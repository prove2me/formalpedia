-- Prove2me | solution 1 for AvramDividend.Classical.avram_ripple_original_finitecap_fullcell_Hessian_cross_abs_L1_public
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T19:01:14.505192+00:00
-- url     : https://prove2.me/submissions/19e2b718-b92c-4c6b-a9e7-7953f4655870

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ripple_original_strict_floor_masked_Hessian_fullcell_public_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_fullcell_Hessian_cross_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_original_finitecap_physical_Hessian_cross_L1
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω) (j : ℕ) :
    let B : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (Finset.range m).sum (fun i =>
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let R : ℝ := X.X (s + Δ) ω - X.X s ω
        let Z : ℝ := R - (Δ : ℝ) * X.c
        let b : ℝ := C.toReal *
          (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
        if s < ρ ω ∧ s + Δ ≤ ρ ω then
          Real.exp (-(q * (s : ℝ))) *
            (if x + X.X s ω - rightLimit D s ω ≤ b
             then iteratedDeriv 2 w
               (x + X.X s ω - rightLimit D s ω) else 0) / 2 *
              (R ^ 2 - Z ^ 2)
        else 0)
    Tendsto (fun m => ∫ ω, |B m ω| ∂P)
      atTop (nhds (0 : ℝ)) := by
  have hCpos : 0 < C.toReal := by
    exact (ENNReal.toReal_pos_iff).mpr
      ⟨hC, lt_top_iff_ne_top.mpr hFiniteCap⟩
  let b : ℝ := C.toReal *
    (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  have hfracpos :
      0 < (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) := by
    positivity
  have hfraclt :
      (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ)) < 1 := by
    have hj : (j + 1 : ℕ) < j + 2 := by omega
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < ((j + 2 : ℕ) : ℝ))).mpr
    simpa only [one_mul] using
      (show (((j + 1 : ℕ) : ℝ) < ((j + 2 : ℕ) : ℝ)) by exact_mod_cast hj)
  have hbpos : 0 < b := mul_pos hCpos hfracpos
  have hbcap : b < C.toReal := by
    simpa only [b, mul_one] using
      (mul_lt_mul_of_pos_left hfraclt hCpos)
  have hdomain :
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} =
        Ioo (0 : ℝ) C.toReal := by
    ext y
    constructor
    · rintro ⟨hy, hycap⟩
      exact ⟨hy,
        (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy) hFiniteCap).mp hycap⟩
    · rintro ⟨hy, hycap⟩
      exact ⟨hy,
        (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy) hFiniteCap).mpr hycap⟩
  have hws : ContDiffOn ℝ 2 w (Ioo (0 : ℝ) C.toReal) := by
    rw [← hdomain]
    exact hw
  obtain ⟨K, hK, hcoef⟩ :=
    avram_ripple_original_strict_floor_masked_Hessian_fullcell_public_bound
      X x D hD.1.1 ρ δ b C.toReal q
      hδ hbpos hbcap (le_of_lt hq) w hws hFloor
  have hBound :
      ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : ℕ) (ω : Ω) (i : ℕ),
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        i < m → s < ρ ω → s + Δ ≤ ρ ω →
          |Real.exp (-(q * (s : ℝ))) *
            (if x + X.X s ω - rightLimit D s ω ≤ b
             then iteratedDeriv 2 w (x + X.X s ω - rightLimit D s ω)
             else 0)| ≤ K := by
    refine ⟨K, hK, ?_⟩
    intro m ω i
    exact hcoef n m i ω
  have hBInt :=
    avram_ga_original_finitecap_fullcell_Hessian_cross_integrable
      X hX hν q hq w C hC hFiniteCap hw
      x D hD n hn ρ hρstop δ hδ hFloor j
  have hLimit :=
    avram_ga_original_finitecap_physical_Hessian_cross_L1
      X hν n ρ hρstop x D w b q hBound hBInt
  simpa only [b] using hLimit
