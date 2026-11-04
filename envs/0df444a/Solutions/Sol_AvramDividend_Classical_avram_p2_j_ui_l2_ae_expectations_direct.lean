-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_l2_ae_expectations_direct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:44:12.168186+00:00
-- url     : https://prove2.me/submissions/ff458415-46e9-4e09-ace5-5542a826227a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal

/-! An independent source-only proof of the L²-to-expectation Vitali principle. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ) (B : ℝ≥0)
    (hm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hB : ∀ n, eLpNorm (Y n) 2 P ≤ (B : ENNReal))
    (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (nhds (∫ ω, Z ω ∂P)) := by
  have h2 : ∀ n, MemLp (Y n) 2 P := by
    intro n
    exact ⟨hm n, lt_of_le_of_lt (hB n) (by simp)⟩
  have h1 : ∀ n, MemLp (Y n) 1 P := by
    intro n
    exact (h2 n).mono_exponent (by norm_num)
  have hBound1 : ∀ n, eLpNorm (Y n) 1 P ≤ (B : ENNReal) := by
    intro n
    exact (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (hm n)).trans (hB n)
  have hLocal : ∀ n (s : Set Ω),
      eLpNorm (Y n) 1 (P.restrict s) ≤
        (B : ENNReal) * (P s) ^ (1 / 2 : ℝ) := by
    intro n s
    have h2s : MemLp (Y n) 2 (P.restrict s) := (h2 n).restrict s
    have hcs :=
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (μ := P.restrict s) (p := 1) (q := 2)
        (by norm_num) h2s.aestronglyMeasurable
    have hnorm : eLpNorm (Y n) 2 (P.restrict s) ≤ (B : ENNReal) :=
      (eLpNorm_mono_measure (Y n) (Measure.restrict_le_self)).trans (hB n)
    have hcs' : eLpNorm (Y n) 1 (P.restrict s) ≤
        eLpNorm (Y n) 2 (P.restrict s) * (P s) ^ (1 / 2 : ℝ) := by
      convert hcs using 1 <;> norm_num
    exact hcs'.trans (by gcongr <;> exact hnorm)
  have hUnif : UnifIntegrable Y 1 P := by
    intro ε hε
    have hEps : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
    obtain ⟨c, hc, hmul⟩ :=
      ENNReal.exists_nnreal_pos_mul_lt
        (a := (B : ENNReal)) (b := ENNReal.ofReal ε)
        (by simp) (ne_of_gt hEps)
    have hcoe : ENNReal.ofReal ((c : ℝ) ^ 2) = (c : ENNReal) ^ 2 := by
      simp
    have hpow :
        (ENNReal.ofReal ((c : ℝ) ^ 2)) ^ (1 / 2 : ℝ) = (c : ENNReal) := by
      rw [hcoe]
      simpa [ENNReal.rpow_two] using
        (ENNReal.rpow_mul (c : ENNReal) 2 (1 / 2 : ℝ)).symm
    refine ⟨(c : ℝ) ^ 2, by positivity, ?_⟩
    intro n s hs hμ
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
    calc
      eLpNorm (Y n) 1 (P.restrict s) ≤
          (B : ENNReal) * (P s) ^ (1 / 2 : ℝ) := hLocal n s
      _ ≤ (B : ENNReal) *
          (ENNReal.ofReal ((c : ℝ) ^ 2)) ^ (1 / 2 : ℝ) := by
          gcongr <;> exact hμ
      _ = (B : ENNReal) * (c : ENNReal) := by rw [hpow]
      _ ≤ ENNReal.ofReal ε := by rw [mul_comm]; exact le_of_lt hmul
  have hUI : UniformIntegrable Y 1 P := ⟨hm, hUnif, ⟨B, hBound1⟩⟩
  have hZ : Integrable Z P := hUI.integrable_of_ae_tendsto hae
  have hZLp : MemLp Z 1 P := memLp_one_iff_integrable.mpr hZ
  have hLp : Tendsto (fun n => eLpNorm (Y n - Z) 1 P) atTop (nhds 0) :=
    tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
      hm hZLp hUI.unifIntegrable hae
  have hY : ∀ n, Integrable (Y n) P :=
    fun n => memLp_one_iff_integrable.mp (h1 n)
  exact ⟨hZ, tendsto_integral_of_L1' Z hZ.aestronglyMeasurable
    (Filter.Eventually.of_forall hY) hLp⟩
