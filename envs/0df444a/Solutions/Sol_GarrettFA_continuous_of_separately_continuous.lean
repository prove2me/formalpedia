-- Prove2me | solution 1 for GarrettFA.continuous_of_separately_continuous
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T17:20:33.924249+00:00
-- url     : https://prove2.me/submissions/31a60554-4082-4af8-a467-5935d2cf40d5

import Mathlib
import Definitions.Def_GarrettFA_IsFrechetSpace
import Theorems.Thm_GarrettFA_banach_steinhaus

open Topology Set Filter

theorem solution {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [AddCommGroup X] [Module 𝕜 X] [Module ℝ X]
    [IsScalarTower ℝ 𝕜 X] [UniformSpace X] [IsUniformAddGroup X] [ContinuousSMul 𝕜 X] [T2Space X]
    {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y] [Module ℝ Y]
    [IsScalarTower ℝ 𝕜 Y] [UniformSpace Y] [IsUniformAddGroup Y] [ContinuousSMul 𝕜 Y] [T2Space Y]
    {Z : Type*} [AddCommGroup Z] [Module 𝕜 Z] [Module ℝ Z]
    [IsScalarTower ℝ 𝕜 Z] [UniformSpace Z] [IsUniformAddGroup Z] [ContinuousSMul 𝕜 Z] [T2Space Z]
    (hX : GarrettFA.IsFrechetSpace 𝕜 X) (hY : GarrettFA.IsFrechetSpace 𝕜 Y)
    (hZ : GarrettFA.IsFrechetSpace 𝕜 Z)
    (β : X →ₗ[𝕜] Y →ₗ[𝕜] Z) (h₁ : ∀ x : X, Continuous (β x))
    (h₂ : ∀ y : Y, Continuous (fun x : X => β x y)) :
    Continuous (fun p : X × Y => β p.1 p.2) := by
  have hXm : TopologicalSpace.MetrizableSpace X := hX.2.1
  have hYm : TopologicalSpace.MetrizableSpace Y := hY.2.1
  have hZl : LocallyConvexSpace ℝ Z := hZ.1
  rw [continuous_iff_seqContinuous]
  intro u p hu
  have hx : Tendsto (fun n => (u n).1) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hu
  have hy : Tendsto (fun n => (u n).2) atTop (𝓝 p.2) := (continuous_snd.tendsto p).comp hu
  let L : ℕ → X →L[𝕜] Z := fun n => ⟨β.flip ((u n).2), h₂ _⟩
  have hL : ∀ n x, L n x = β x (u n).2 := fun n x => rfl
  set E := Set.range L with hE
  have hbdd : ∀ x : X, Bornology.IsVonNBounded 𝕜 ((fun T : X →L[𝕜] Z => T x) '' E) := by
    intro x
    have ht : Tendsto (fun n => β x (u n).2) atTop (𝓝 (β x p.2)) :=
      ((h₁ x).tendsto _).comp hy
    have := ht.isVonNBounded_range 𝕜
    convert this using 1
    ext z
    simp [hE, hL]
  have hequi := GarrettFA.banach_steinhaus (Or.inl hX) E hbdd
  have hxs : Tendsto (fun n => (u n).1 - p.1) atTop (𝓝 0) := by
    simpa using hx.sub_const p.1
  have h1 : Tendsto (fun n => β ((u n).1 - p.1) (u n).2) atTop (𝓝 0) := by
    intro U hU
    obtain ⟨N, hN, hNU⟩ := hequi U hU
    have hev : ∀ᶠ n in atTop, (u n).1 - p.1 ∈ N := hxs hN
    rw [Filter.mem_map]
    filter_upwards [hev] with n hn
    exact hNU (L n) ⟨L n, ⟨n, rfl⟩, rfl⟩ hn
  have hys : Tendsto (fun n => (u n).2 - p.2) atTop (𝓝 0) := by
    simpa using hy.sub_const p.2
  have h2 : Tendsto (fun n => β p.1 ((u n).2 - p.2)) atTop (𝓝 0) := by
    have h0 : Tendsto (β p.1) (𝓝 0) (𝓝 0) := by simpa using (h₁ p.1).tendsto 0
    exact h0.comp hys
  have h3 := (tendsto_const_nhds (x := β p.1 p.2)).add (h1.add h2)
  rw [add_zero, add_zero] at h3
  refine h3.congr fun n => ?_
  simp only [map_sub, LinearMap.sub_apply]
  abel
