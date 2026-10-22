-- Prove2me | solution 1 for BirkhoffGlobalSection.left_component_radial_projection_continuous
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-24T22:35:16.68242+00:00
-- url     : https://prove2.me/submissions/92703d4c-3a38-4bbb-bbbe-b7c7ecb2f6b1

import Definitions.Def_BirkhoffGlobalSection
import Mathlib.Tactic

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ f : LeftEnergyState μ c → {x : Phase // x ∈ unitThreeSphere},
      Continuous f ∧
        ∀ s, (f s : Phase) =
          fun i => (s : Phase) i /
            Real.sqrt (zNormSq (s : Phase) + wNormSq (s : Phase)) := by
  -- the component avoids the origin
  have hpos : ∀ s : LeftEnergyState μ c, 0 < zNormSq (s : Phase) + wNormSq (s : Phase) := by
    intro s
    have hH : leviCivitaHamiltonian μ c (s : Phase) = 0 :=
      (connectedComponentIn_subset _ _ s.2).1
    by_contra hle
    push_neg at hle
    set x : Phase := (s : Phase)
    have h0 : x 0 = 0 := by unfold zNormSq wNormSq at hle; nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)]
    have h1 : x 1 = 0 := by unfold zNormSq wNormSq at hle; nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)]
    have h2 : x 2 = 0 := by unfold zNormSq wNormSq at hle; nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)]
    have h3 : x 3 = 0 := by unfold zNormSq wNormSq at hle; nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 3)]
    unfold leviCivitaHamiltonian zNormSq wNormSq secondCollisionDistanceSq at hH
    rw [h0, h1, h2, h3] at hH
    norm_num at hH
    linarith
  have hN : ∀ s : Phase, zNormSq s + wNormSq s = s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 + s 3 ^ 2 := by
    intro s; unfold zNormSq wNormSq; ring
  have hcont : Continuous (fun s : LeftEnergyState μ c =>
      (fun i => (s : Phase) i / Real.sqrt (zNormSq (s : Phase) + wNormSq (s : Phase)) : Phase)) := by
    apply continuous_pi
    intro i
    apply Continuous.div
    · exact (continuous_apply i).comp continuous_subtype_val
    · have : Continuous (fun x : Phase => zNormSq x + wNormSq x) := by
        unfold zNormSq wNormSq; fun_prop
      exact Real.continuous_sqrt.comp (this.comp continuous_subtype_val)
    · intro s; exact (Real.sqrt_pos.2 (hpos s)).ne'
  refine ⟨fun s => ⟨fun i => (s : Phase) i /
      Real.sqrt (zNormSq (s : Phase) + wNormSq (s : Phase)), ?_⟩, ?_, fun s => rfl⟩
  · have hp := hpos s
    have hsq := Real.sq_sqrt hp.le
    have hne := (Real.sqrt_pos.2 hp).ne'
    show zNormSq _ + wNormSq _ = 1
    generalize Real.sqrt (zNormSq (s : Phase) + wNormSq (s : Phase)) = t at hsq hne ⊢
    have e : zNormSq (fun i => (s : Phase) i / t) + wNormSq (fun i => (s : Phase) i / t) =
        (zNormSq (s : Phase) + wNormSq (s : Phase)) / t ^ 2 := by
      unfold zNormSq wNormSq; field_simp
    rw [e, ← hsq, div_self (pow_ne_zero 2 hne)]
  · exact hcont.subtype_mk _
