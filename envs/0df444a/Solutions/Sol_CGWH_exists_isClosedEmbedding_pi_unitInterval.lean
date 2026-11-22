-- Prove2me | solution 1 for CGWH.exists_isClosedEmbedding_pi_unitInterval
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T16:58:23.587625+00:00
-- url     : https://prove2.me/submissions/e018b2e8-3f00-4cc2-811c-96dfb47505aa

import Mathlib

open Topology TopologicalSpace

set_option autoImplicit false

universe u v


theorem solution
    {K : Type u} {ι : Type v} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    (h : Cardinal.lift.{v} (Cardinal.mk C(K, ℂ)) ≤ Cardinal.lift.{u} (Cardinal.mk ι)) :
    ∃ φ : K → (ι → unitInterval), IsClosedEmbedding φ := by
  -- `C(K, [0,1])` injects into `C(K, ℂ)`, hence into `ι`
  have inj : Function.Injective (fun a : C(K, unitInterval) =>
      (⟨fun x => ((a x : ℝ) : ℂ), by fun_prop⟩ : C(K, ℂ))) := by
    intro a b hab
    ext x
    have := congrArg (fun f : C(K, ℂ) => f x) hab
    simpa using this
  have h' : Cardinal.lift.{v} (Cardinal.mk C(K, unitInterval)) ≤
      Cardinal.lift.{u} (Cardinal.mk ι) :=
    (Cardinal.lift_le.2 (Cardinal.mk_le_of_injective inj)).trans h
  obtain ⟨j⟩ := Cardinal.lift_mk_le'.1 h'
  classical
  -- coordinate `i = j a` of `φ x` is `a x`; the other coordinates are `0`
  let φ : K → ι → unitInterval :=
    fun x i => if hi : ∃ a, j a = i then (Classical.choose hi) x else 0
  have hφ : Continuous φ := by
    refine continuous_pi fun i => ?_
    by_cases hi : ∃ a, j a = i
    · simp only [φ, dif_pos hi]; exact (Classical.choose hi).continuous
    · simp only [φ, dif_neg hi]; exact continuous_const
  have hinj : Function.Injective φ := by
    intro x y hxy
    by_contra hne
    obtain ⟨f, hfx, hfy, hf01⟩ := exists_continuous_zero_one_of_isClosed
      (isClosed_singleton (x := x)) (isClosed_singleton (x := y))
      (by simpa using hne)
    let a : C(K, unitInterval) := ⟨fun z => ⟨f z, hf01 z⟩, f.continuous.subtype_mk _⟩
    have key := congrFun hxy (j a)
    have hi : ∃ b, j b = j a := ⟨a, rfl⟩
    have hch : Classical.choose hi = a := j.injective (Classical.choose_spec hi)
    simp only [φ, dif_pos hi, hch] at key
    have key2 : f x = f y := congrArg Subtype.val key
    rw [hfx rfl, hfy rfl] at key2
    simp at key2
  -- a continuous injection from a compact space to a Hausdorff space is a closed embedding
  exact ⟨φ, hφ.isClosedEmbedding hinj⟩
