-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_discounted_postPayment_zero_stieltjes_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:46:28.561658+00:00
-- url     : https://prove2.me/submissions/5676c468-1dfb-4158-8696-2d6f2eec5260

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_postPayment_Ioc_atom_accounting

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- A post-payment BV path is already right-continuous at time zero;
    its own Stieltjes singleton therefore carries no initial dividend. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (v : ℝ → ℝ) (L : NNReal) (hv : LipschitzWith L v) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      let g : ℝ≥0 → ℝ := fun t =>
        Real.exp (-q * (t : ℝ)) *
          v (x + X.X (min t T) ω - rightLimit D (min t T) ω)
      ∃ hg : BoundedVariationOn g Set.univ,
        hg.vectorMeasure ({0} : Set ℝ≥0) = 0 := by
  filter_upwards [
    avram_wave3_03_bv_discounted_postPayment_Ioc_atom_accounting
      X hX hBV x D hD q hq v L hv
  ] with ω hω
  intro T
  rcases hω T with ⟨hg, -⟩
  let u : ℝ≥0 → ℝ := fun s => x + X.X s ω - rightLimit D s ω
  have hu : ContinuousAt u 0 := by
    simpa [u, continuousWithinAt_univ] using
      (postPaymentReserve_cadlag_adapted X x D hD).1 ω 0
  have hmin : ContinuousAt (fun t : ℝ≥0 => min t T) 0 :=
    (continuous_id.min continuous_const).continuousAt
  have hcomp : ContinuousAt (fun t : ℝ≥0 => u (min t T)) 0 := by
    simpa only [Function.comp_def] using
      (ContinuousAt.comp_of_eq hu hmin
        (by simp : min (0 : ℝ≥0) T = 0))
  have hpath : ContinuousAt (fun t : ℝ≥0 => v (u (min t T))) 0 := by
    have hvcont : ContinuousAt v ((fun t : ℝ≥0 => u (min t T)) 0) :=
      hv.continuous.continuousAt
    exact (ContinuousAt.comp
      (f := fun t : ℝ≥0 => u (min t T)) (g := v) hvcont hcomp :
      ContinuousAt (v ∘ (fun t : ℝ≥0 => u (min t T))) 0)
  have hdisc : ContinuousAt (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ))) 0 := by
    fun_prop
  have hgcont : ContinuousWithinAt
      (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ)) * v (u (min t T)))
      (Ici (0 : ℝ≥0)) 0 :=
    (hdisc.mul hpath).continuousWithinAt
  have hleft : Function.leftLim
      (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ)) * v (u (min t T))) 0 =
      Real.exp (-q * ((0 : ℝ≥0) : ℝ)) * v (u (min (0 : ℝ≥0) T)) :=
    leftLim_eq_of_isBot
      (f := fun t : ℝ≥0 => Real.exp (-q * (t : ℝ)) * v (u (min t T)))
      (isBot_bot : IsBot (0 : ℝ≥0))
  refine ⟨hg, ?_⟩
  calc
    hg.vectorMeasure ({0} : Set ℝ≥0) =
        Function.rightLim (fun t : ℝ≥0 =>
          Real.exp (-q * (t : ℝ)) * v (u (min t T))) 0 -
        Function.leftLim (fun t : ℝ≥0 =>
          Real.exp (-q * (t : ℝ)) * v (u (min t T))) 0 := by
            simpa [u] using (hg.vectorMeasure_singleton (a := (0 : ℝ≥0)))
    _ = 0 := by
      rw [hgcont.rightLim_eq, hleft]
      exact sub_self _
