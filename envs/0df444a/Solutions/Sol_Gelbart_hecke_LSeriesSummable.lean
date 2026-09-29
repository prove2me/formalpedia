-- Prove2me | solution 1 for Gelbart.hecke_LSeriesSummable
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T23:36:18.73956+00:00
-- url     : https://prove2.me/submissions/9b3a5802-c5f8-4e99-b74d-c91b161c5f2b

import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Definitions.Def_Gelbart_hecke_series

namespace Gelbart

theorem hecke_LSeriesSummable
    (a : ℕ → ℂ) (c : ℝ) (hc : 0 < c) (hgrowth : HeckeCoeffGrowth a c)
    {s : ℂ} (hs : c + 1 < s.re) :
    LSeriesSummable a s := by
  apply LSeriesSummable_of_le_const_mul_rpow hs
  obtain ⟨K, hK⟩ := hgrowth
  refine ⟨K, fun n hn => ?_⟩
  simpa only [add_sub_cancel_right] using hK n (Nat.one_le_iff_ne_zero.mpr hn)

end Gelbart

theorem solution
    (a : ℕ → ℂ) (c : ℝ) (hc : 0 < c) (hgrowth : Gelbart.HeckeCoeffGrowth a c)
    {s : ℂ} (hs : c + 1 < s.re) :
    LSeriesSummable a s :=
  Gelbart.hecke_LSeriesSummable a c hc hgrowth hs

#print axioms Gelbart.hecke_LSeriesSummable
#print axioms solution
