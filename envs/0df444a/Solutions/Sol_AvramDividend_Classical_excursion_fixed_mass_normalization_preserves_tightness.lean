-- Prove2me | solution 1 for AvramDividend.Classical.excursion_fixed_mass_normalization_preserves_tightness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:07:08.419935+00:00
-- url     : https://prove2.me/submissions/356471f3-6393-49a5-a696-18ef3df8e2ce

import Mathlib.MeasureTheory.Measure.Prokhorov
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology

/-!
Normalising a family of finite measures of common positive mass
multiplies each compact-complement mass by the same finite factor.
Uniform tightness is therefore preserved.
-/
theorem solution
    (ν : ℕ → FiniteMeasure ℝ) (c : NNReal) (hc : 0 < c)
    (hmass : ∀ n : ℕ, (ν n).mass = c)
    (hnz : ∀ n : ℕ, ν n ≠ 0)
    (htight : IsTightMeasureSet
      (Set.range (fun n : ℕ => (ν n : Measure ℝ)))) :
    IsTightMeasureSet
      (Set.range (fun n : ℕ => ((ν n).normalize : Measure ℝ))) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight ⊢
  intro ε hε
  have hcpos : (0 : ENNReal) < (c : ENNReal) := by exact_mod_cast hc
  have hc0 : (c : ENNReal) ≠ 0 := ne_of_gt hcpos
  have hcTop : (c : ENNReal) ≠ ⊤ := by simp
  have hδ : 0 < ε * (c : ENNReal) :=
    ENNReal.mul_pos (ne_of_gt hε) (ne_of_gt hcpos)
  obtain ⟨K, hK, hbound⟩ := htight (ε * (c : ENNReal)) hδ
  refine ⟨K, hK, ?_⟩
  intro m hm
  obtain ⟨n, rfl⟩ := hm
  have hb : (ν n : Measure ℝ) Kᶜ ≤ ε * (c : ENNReal) :=
    hbound (ν n : Measure ℝ) ⟨n, rfl⟩
  calc
    ((ν n).normalize : Measure ℝ) Kᶜ =
        ((c⁻¹ : NNReal) : ENNReal) * (ν n : Measure ℝ) Kᶜ := by
      rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero (ν n) (hnz n)]
      simp only [Measure.smul_apply, hmass n]
      rfl
    _ ≤ ((c⁻¹ : NNReal) : ENNReal) * (ε * (c : ENNReal)) :=
      mul_le_mul' le_rfl hb
    _ = ε := by
      rw [ENNReal.coe_inv (ne_of_gt hc)]
      calc
        (c : ENNReal)⁻¹ * (ε * (c : ENNReal)) =
            ((c : ENNReal)⁻¹ * (c : ENNReal)) * ε := by ac_rfl
        _ = ε := by rw [ENNReal.inv_mul_cancel hc0 hcTop, one_mul]
