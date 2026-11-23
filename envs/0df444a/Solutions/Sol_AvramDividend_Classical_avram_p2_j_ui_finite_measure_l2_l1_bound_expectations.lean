-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_finite_measure_l2_l1_bound_expectations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:04:58.363951+00:00
-- url     : https://prove2.me/submissions/069508ad-333f-47f7-bfaf-1a8b4185db24

import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal

/-! On finite measures, bounded L2 and L1 norms give Vitali mean convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (B D : ℝ≥0)
    (hm : ∀ n, AEStronglyMeasurable (Y n) μ)
    (h2 : ∀ n, eLpNorm (Y n) 2 μ ≤ (B : ENNReal))
    (h1 : ∀ n, eLpNorm (Y n) 1 μ ≤ (D : ENNReal))
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z μ ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂μ) atTop
        (nhds (∫ ω, Z ω ∂μ)) := by
  have hMem2 : ∀ n, MemLp (Y n) 2 μ := by
    intro n
    exact ⟨hm n, lt_of_le_of_lt (h2 n) (by simp)⟩
  have hLocal : ∀ n (s : Set Ω),
      eLpNorm (Y n) 1 (μ.restrict s) ≤
        (B : ENNReal) * (μ s) ^ (1 / 2 : ℝ) := by
    intro n s
    have h2s : MemLp (Y n) 2 (μ.restrict s) := (hMem2 n).restrict s
    have hcs :=
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (μ := μ.restrict s) (p := 1) (q := 2)
        (by norm_num) h2s.aestronglyMeasurable
    have hnorm : eLpNorm (Y n) 2 (μ.restrict s) ≤ (B : ENNReal) :=
      (eLpNorm_mono_measure (Y n) (Measure.restrict_le_self)).trans (h2 n)
    have hcs' : eLpNorm (Y n) 1 (μ.restrict s) ≤
        eLpNorm (Y n) 2 (μ.restrict s) * (μ s) ^ (1 / 2 : ℝ) := by
      convert hcs using 1 <;> norm_num
    exact hcs'.trans (by gcongr <;> exact hnorm)
  have hunif : UnifIntegrable Y 1 μ := by
    intro ε hε
    have hEps : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
    obtain ⟨c, hc, hmul⟩ :=
      ENNReal.exists_nnreal_pos_mul_lt
        (a := (B : ENNReal)) (b := ENNReal.ofReal ε)
        (by simp) (ne_of_gt hEps)
    have hcoe : ENNReal.ofReal ((c : ℝ) ^ 2) = (c : ENNReal) ^ 2 := by simp
    have hpow :
        (ENNReal.ofReal ((c : ℝ) ^ 2)) ^ (1 / 2 : ℝ) = (c : ENNReal) := by
      rw [hcoe]
      simpa [ENNReal.rpow_two] using
        (ENNReal.rpow_mul (c : ENNReal) 2 (1 / 2 : ℝ)).symm
    refine ⟨(c : ℝ) ^ 2, by positivity, ?_⟩
    intro n s hs hμ
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
    calc
      eLpNorm (Y n) 1 (μ.restrict s) ≤
          (B : ENNReal) * (μ s) ^ (1 / 2 : ℝ) := hLocal n s
      _ ≤ (B : ENNReal) *
          (ENNReal.ofReal ((c : ℝ) ^ 2)) ^ (1 / 2 : ℝ) := by
          gcongr <;> exact hμ
      _ = (B : ENNReal) * (c : ENNReal) := by rw [hpow]
      _ ≤ ENNReal.ofReal ε := by rw [mul_comm]; exact le_of_lt hmul
  have hUI : UniformIntegrable Y 1 μ := ⟨hm, hunif, ⟨D, h1⟩⟩
  have hZ : Integrable Z μ := hUI.integrable_of_ae_tendsto hae
  have hZLp : MemLp Z 1 μ := memLp_one_iff_integrable.mpr hZ
  have hLp : Tendsto (fun n => eLpNorm (Y n - Z) 1 μ) atTop (nhds 0) :=
    tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
      hm hZLp hUI.unifIntegrable hae
  have hY : ∀ n, Integrable (Y n) μ :=
    fun n => memLp_one_iff_integrable.mp (hUI.memLp n)
  exact ⟨hZ, tendsto_integral_of_L1' Z hZ.aestronglyMeasurable
    (Filter.Eventually.of_forall hY) hLp⟩
