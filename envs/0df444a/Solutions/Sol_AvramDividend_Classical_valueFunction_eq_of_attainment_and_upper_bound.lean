-- Prove2me | solution 1 for AvramDividend.Classical.valueFunction_eq_of_attainment_and_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:56:47.463665+00:00
-- url     : https://prove2.me/submissions/11554f09-0c62-49c6-88ae-2c0b8a7c5999

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Omega : Type*} [mOmega : MeasurableSpace Omega] {P : Measure Omega}
    {F : Filtration NNReal mOmega}
    (X : SpectrallyNegativeLevy P F) (q x : Real)
    (B : ENNReal) (D : NNReal -> Omega -> Real)
    (hD : IsAdmissible X x D)
    (hvalue : dividendValue X q x D = B)
    (hupper : valueFunction X q x <= B) :
    valueFunction X q x = B := by
  apply le_antisymm hupper
  have hle : dividendValue X q x D <= valueFunction X q x := by
    unfold valueFunction
    exact le_iSup_of_le D (le_iSup_of_le hD le_rfl)
  simpa only [hvalue] using hle
