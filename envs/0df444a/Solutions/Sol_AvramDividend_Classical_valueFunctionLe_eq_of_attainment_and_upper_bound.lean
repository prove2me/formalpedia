-- Prove2me | solution 1 for AvramDividend.Classical.valueFunctionLe_eq_of_attainment_and_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T10:56:30.848583+00:00
-- url     : https://prove2.me/submissions/a571d88f-49f9-42c4-a3fc-eaca34dd0350

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
    (C B : ENNReal) (D : NNReal -> Omega -> Real)
    (hD : IsAdmissibleLe X x C D)
    (hvalue : dividendValue X q x D = B)
    (hupper : valueFunctionLe X q C x <= B) :
    valueFunctionLe X q C x = B := by
  apply le_antisymm hupper
  have hle : dividendValue X q x D <= valueFunctionLe X q C x := by
    unfold valueFunctionLe
    exact le_iSup_of_le D (le_iSup_of_le hD le_rfl)
  simpa only [hvalue] using hle
