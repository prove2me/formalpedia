-- Prove2me | solution 1 for BirkhoffGlobalSection.radial_filling_locally_convex_of_positive_tangential_hessian
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-29T19:36:20.270116+00:00
-- url     : https://prove2.me/submissions/8b12f344-615f-4fe4-ac27-c413c366b1fa

import Theorems.Thm_BirkhoffGlobalSection_radial_filling_locally_convex_at_each_point
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic.Linarith

open BirkhoffGlobalSection
open scoped Topology

private def radialFilling (S : Set Phase) : Set Phase :=
  {y : Phase | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y = t • s}

private theorem radialFilling_isClosed_isPreconnected (S : Set Phase)
    (hS : IsCompact S) :
    IsClosed (radialFilling S) ∧ IsPreconnected (radialFilling S) := by
  let f : Phase × ℝ → Phase := fun p => p.2 • p.1
  have hf : Continuous f := continuous_snd.smul continuous_fst
  have himg : f '' (S ×ˢ Set.Icc (0 : ℝ) 1) = radialFilling S := by
    ext y
    constructor
    · rintro ⟨⟨s, t⟩, ⟨hs, ht⟩, rfl⟩
      exact ⟨s, hs, t, ht.1, ht.2, rfl⟩
    · rintro ⟨s, hs, t, ht0, ht1, rfl⟩
      exact ⟨(s, t), ⟨hs, ⟨ht0, ht1⟩⟩, rfl⟩
  have hcompact : IsCompact (radialFilling S) := by
    rw [← himg]
    exact (hS.prod isCompact_Icc).image hf
  have hstar : StarConvex ℝ (0 : Phase) (radialFilling S) := by
    intro y hy a b ha hb hab
    obtain ⟨s, hs, t, ht0, ht1, rfl⟩ := hy
    refine ⟨s, hs, b * t, mul_nonneg hb ht0, ?_, ?_⟩
    · calc
        b * t ≤ b * 1 := mul_le_mul_of_nonneg_left ht1 hb
        _ = b := mul_one b
        _ ≤ 1 := by linarith
    · simp [smul_smul]
  constructor
  · exact hcompact.isClosed
  · rcases (radialFilling S).eq_empty_or_nonempty with he | hne
    · simpa [he] using isPreconnected_empty
    · exact (hstar.isPathConnected (hstar.mem hne)).isConnected.isPreconnected

theorem solution (F : Phase → ℝ) (S : Set Phase)
    (hS : IsCompact S)
    (hF0 : ∀ s ∈ S, F s = 0)
    (hreg : ∀ s ∈ S, fderiv ℝ F s ≠ 0)
    (hTH : HasPositiveTangentialHessianOn F S)
    (hray : ∀ x ∈ unitThreeSphere, ∃ r : ℝ, 0 < r ∧ (fun i : Fin 4 => r * x i) ∈ S)
    (huniq : ∀ x ∈ unitThreeSphere, ∀ r t : ℝ, 0 < r → 0 < t →
      (fun i : Fin 4 => r * x i) ∈ S → (fun i : Fin 4 => t * x i) ∈ S → r = t)
    (hneg : ∀ x ∈ unitThreeSphere, ∀ R : ℝ, 0 < R → (fun i : Fin 4 => R * x i) ∈ S →
      ∀ r : ℝ, 0 ≤ r → r < R → F (fun i : Fin 4 => r * x i) < 0) :
    let K : Set Phase :=
      {y : Phase | ∃ s ∈ S, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ y = t • s}
    IsClosed K ∧ IsPreconnected K ∧
      ∀ x ∈ K, ∃ U : Set Phase, U ∈ 𝓝 x ∧ Convex ℝ (K ∩ U) := by
  change IsClosed (radialFilling S) ∧ IsPreconnected (radialFilling S) ∧
    ∀ x ∈ radialFilling S, ∃ U : Set Phase, U ∈ 𝓝 x ∧ Convex ℝ (radialFilling S ∩ U)
  have htop := radialFilling_isClosed_isPreconnected S hS
  have hlocal := radial_filling_locally_convex_at_each_point
    F S hS hF0 hreg hTH hray huniq hneg
  exact ⟨htop.1, htop.2, hlocal⟩
