-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_public_original_cell_real_discount_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T00:16:00.99121+00:00
-- url     : https://prove2.me/submissions/a5ed688f-9676-4741-a2ba-ac05b302eb4c

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_full_stieltjes_uniform_width_mesh_discount_error
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (a b : ℝ≥0) (hab : a ≤ b)
    (δ : ℝ) (hδ : 0 ≤ δ) (hwidth : (b : ℝ) - (a : ℝ) ≤ δ)
    (S : Set ℝ)
    (hMask :
      (∫⁻ r in S ∩ Ioc (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)).toReal =
      (∫⁻ r in Ioc (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)).toReal) :
    let cash : ℝ :=
      (∫⁻ r in S ∩ Ioc (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)).toReal
    let E : ℝ := Real.exp (-(q * (b : ℝ)))
    let inc : ℝ := rightLimit D b ω - rightLimit D a ω
    0 ≤ cash - E * inc ∧ cash - E * inc ≤ q * δ * inc := by
  dsimp
  have hMono :=
    avram_wave3_03_dividendStrategy_rightLimit_monotone D hD ω
  have hInc : 0 ≤ rightLimit D b ω - rightLimit D a ω :=
    sub_nonneg.mpr (hMono hab)
  have hMass :
      dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) =
        ENNReal.ofReal (rightLimit D b ω - rightLimit D a ω) :=
    dividendMeasure_Ioc_rightLimit D hD ω a b
  have hQ :=
    avram_p4_d_dividend_original_full_stieltjes_uniform_width_mesh_discount_error
      D hD ω q δ hq hδ ({0} : Finset ℕ)
      (fun _ => a) (fun _ => b)
      (by simpa using hab) (by simpa using hwidth)
  simp only [Finset.sum_singleton] at hQ
  have hWfin :
      ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) *
        dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) ≠ ⊤ := by
    rw [hMass]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    exact ENNReal.ofReal_ne_top
  have hEfin :
      ENNReal.ofReal (q * δ) *
        dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) ≠ ⊤ := by
    rw [hMass]
    rw [← ENNReal.ofReal_mul (mul_nonneg hq hδ)]
    exact ENNReal.ofReal_ne_top
  have hBfin :
      (ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) *
          dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) +
        ENNReal.ofReal (q * δ) *
          dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ))) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hWfin, hEfin⟩
  have hIfin :
      (∫⁻ r in Ioc (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)) ≠ ⊤ :=
    ne_top_of_le_ne_top hBfin hQ.2
  have hLo := ENNReal.toReal_mono hIfin hQ.1
  have hHi := ENNReal.toReal_mono hBfin hQ.2
  rw [ENNReal.toReal_add hWfin hEfin] at hHi
  rw [hMass] at hLo hHi
  have hW :
      (ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) *
        ENNReal.ofReal (rightLimit D b ω -
          rightLimit D a ω)).toReal =
      Real.exp (-(q * (b : ℝ))) *
        (rightLimit D b ω - rightLimit D a ω) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    exact ENNReal.toReal_ofReal (mul_nonneg (Real.exp_nonneg _) hInc)
  have hE :
      (ENNReal.ofReal (q * δ) *
        ENNReal.ofReal (rightLimit D b ω - rightLimit D a ω)).toReal =
      (q * δ) * (rightLimit D b ω - rightLimit D a ω) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg hq hδ)]
    exact ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg hq hδ) hInc)
  rw [hW] at hLo hHi
  rw [hE] at hHi
  rw [hMask]
  constructor
  · exact sub_nonneg.mpr hLo
  · linarith
