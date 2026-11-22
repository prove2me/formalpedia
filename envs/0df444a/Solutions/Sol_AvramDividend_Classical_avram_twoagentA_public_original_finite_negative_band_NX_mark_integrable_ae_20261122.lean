-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_public_original_finite_negative_band_NX_mark_integrable_ae_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:13:44.905164+00:00
-- url     : https://prove2.me/submissions/70782521-16d6-420c-a4f4-ebec91145ce0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_shared_original_finite_negative_band_facts
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_negative_Borel_marked_Poisson_interval_Campbell_exact
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_count_ae_finite
import Theorems.Thm_AvramDividend_Classical_avram_twoagentA_public_original_bounded_physical_rectangle_mark_integrable_20261122
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ :=
      Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    ∀ᵐ ω ∂P,
      NX ω (Ioc 0 T ×ˢ B) < ⊤ ∧
      IntegrableOn (fun p : ℝ≥0 × ℝ => p.2)
        (Ioc 0 T ×ˢ B) (NX ω) := by
  classical
  let B : Set ℝ :=
    Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  obtain ⟨hB, hNeg, hν⟩ :=
    avram_twoagentA_shared_original_finite_negative_band_facts X n m
  have hCampbell :=
    avram_b24_original_negative_Borel_marked_Poisson_interval_Campbell_exact
      X 0 T (by positivity) B hB hNeg
  have hAE : ∀ᵐ ω ∂P, NX ω (Ioc 0 T ×ˢ B) < ⊤ := by
    apply avram_p2_e_compensator_finite_nu_count_ae_finite
      X 0 T (by positivity) B hB hν
    simpa only [tsub_zero] using hCampbell
  have ha : -1 ≤ -(1 / ((n : ℝ) + 1)) := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    have hInv : 1 / ((n : ℝ) + 1) ≤ 1 := by
      apply (div_le_iff₀ hpos).mpr
      linarith
    linarith
  have hb : -(1 / ((m : ℝ) + 1)) ≤ 0 :=
    neg_nonpos.mpr (by positivity)
  filter_upwards [hAE] with ω hFin
  exact ⟨hFin,
    avram_twoagentA_public_original_bounded_physical_rectangle_mark_integrable_20261122
      (NX ω) T _ _ ha hb hFin⟩
