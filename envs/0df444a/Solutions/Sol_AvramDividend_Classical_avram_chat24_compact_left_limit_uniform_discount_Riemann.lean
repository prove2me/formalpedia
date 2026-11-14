-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_compact_left_limit_uniform_discount_Riemann
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:50:20.947838+00:00
-- url     : https://prove2.me/submissions/423fccfa-5298-4099-b7db-3817a3807f85

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_avram_chat24_uniform_step_quadrature_core
import Theorems.Thm_avram_chat24_physical_discount_cell_integral_core
import Theorems.Thm_avram_chat24_physical_clock_zero_atom_core
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (F Y : ℝ≥0 → ℝ) (a b q T : ℝ) (hT : 0 ≤ T) (hq : 0 ≤ q)
    (B : ℝ≥0) (hB : 0 < B) (hBT : B ≤ (⟨T, hT⟩ : ℝ≥0))
    (hband : ∀ s : ℝ≥0, s ≤ B → F s ∈ Icc a b)
    (hpre : ∀ t : ℝ≥0, 0 < t → t ≤ B →
      Y t ∈ Icc a b ∧ Tendsto F (𝓝[<] t) (nhds (Y t)))
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc a b)) :
    let μ : Measure ℝ≥0 := (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    let A : ℝ≥0 → ℝ := fun t =>
      if (t : ℝ≥0∞) ≤ (B : ℝ≥0∞) ∧ Y t ∈ Icc a b then
        Real.exp (-(q * (t : ℝ))) * (-(q * w (Y t))) else 0
    Integrable A μ ∧
      Tendsto (fun n : ℕ =>
        let u : ℕ → ℝ≥0 := fun i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
        ∑ i ∈ Finset.range (n + 1),
          (Real.exp (-(q * (u (i + 1) : ℝ))) -
            Real.exp (-(q * (u i : ℝ)))) * w (F (u i)))
        atTop (nhds (∫ t, A t ∂μ))  := by
  classical
  intro μ A
  letI : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  let k : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ))) * (-q)
  let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
  have hk : Continuous k := by dsimp [k]; fun_prop
  have hkb (t : ℝ≥0) : ‖k t‖ ≤ q := by
    have he : Real.exp (-(q * (t : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hq t.property))
    have he0 := (Real.exp_pos (-(q * (t : ℝ)))).le
    change |Real.exp (-(q * (t : ℝ))) * (-q)| ≤ q
    rw [abs_mul, abs_of_nonneg he0, abs_neg, abs_of_nonneg hq]
    exact mul_le_of_le_one_left hq he
  have hcell (s t : ℝ≥0) (hst : s ≤ t) (htB : t ≤ B) :
      (∫ r in Ioc s t, k r ∂μ) = E t - E s := by
    have htT : (t : ℝ) ≤ T := by exact_mod_cast htB.trans hBT
    exact avram_chat24_physical_discount_cell_integral_core q T hT s t hst htT
  have hA : (fun t : ℝ≥0 => if t ≤ B ∧ Y t ∈ Icc a b then k t * w (Y t) else 0) = A := by
    funext t
    simp only [A, k, ENNReal.coe_le_coe, mul_assoc, neg_mul]
  have h := avram_chat24_uniform_step_quadrature_core μ (avram_chat24_physical_clock_zero_atom_core T)
    F Y a b B hB hband hpre w hw k E hk.measurable q hq hkb hcell
  dsimp only at h
  rw [hA] at h
  simpa only [E] using h
end
