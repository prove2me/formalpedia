-- Prove2me | solution 1 for AvramDividend.Classical.chat03_discounted_scale_terminal_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:42:12.872964+00:00
-- url     : https://prove2.me/submissions/6fd51f7d-7425-438d-97bb-8da8a70a7c7f

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open AvramDividend.Classical
open scoped NNReal

/-!
Chat 03: the remaining stopped scale value after deterministic horizon N
decays at least as exp(-q N) times the barrier scale value, provided reserve
stays inside [0,a]. This is the pathwise terminal-residual bound, not a
continuous-time stopping or q-scale martingale identity.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (a y : ℝ) (hy : 0 ≤ y) (hya : y ≤ a)
    (N t : ℝ≥0) (hNt : N ≤ t) :
    Real.exp (-(q * (t : ℝ))) * W y ≤
      Real.exp (-(q * (N : ℝ))) * W a := by
  have ha : 0 ≤ a := le_trans hy hya
  have hWy : 0 ≤ W y := hW.2.1 y hy
  have hWle : W y ≤ W a :=
    hW.2.2.2.1 (Set.mem_Ici.mpr hy)
      (Set.mem_Ici.mpr ha) hya
  have hNt_real : (N : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast hNt
  have hqt : q * (N : ℝ) ≤ q * (t : ℝ) :=
    mul_le_mul_of_nonneg_left hNt_real hq.le
  have he : Real.exp (-(q * (t : ℝ))) ≤
      Real.exp (-(q * (N : ℝ))) :=
    Real.exp_le_exp.mpr (neg_le_neg hqt)
  calc
    Real.exp (-(q * (t : ℝ))) * W y ≤
        Real.exp (-(q * (N : ℝ))) * W y :=
      mul_le_mul_of_nonneg_right he hWy
    _ ≤ Real.exp (-(q * (N : ℝ))) * W a :=
      mul_le_mul_of_nonneg_left hWle (Real.exp_nonneg _)