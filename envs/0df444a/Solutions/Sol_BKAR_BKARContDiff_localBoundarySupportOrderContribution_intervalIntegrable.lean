-- Prove2me | solution 1 for BKAR.BKARContDiff.localBoundarySupportOrderContribution_intervalIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:37:16.417817+00:00
-- url     : https://prove2.me/submissions/766d1f72-884d-4f2a-8575-bfc1131b326a

import Definitions.Def_BKAR_CubePartition_Smoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Theorems.Thm_BKAR_BKARContDiff_localBoundarySupportOrderContribution_continuous

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}
namespace BKAR.BKARContDiff
theorem _root_.solution
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (I : ForestIndex V) (order : List (Edge V)) (a b : ℝ) :
    IntervalIntegrable
      (fun top : ℝ =>
        Forest.localBoundarySupportOrderContribution choices F pref prefixTs
          top I order ρ)
      MeasureTheory.volume a b :=
  (hρ.localBoundarySupportOrderContribution_continuous choices F pref prefixTs
    hpref hprefixTs I order).intervalIntegrable a b
end BKAR.BKARContDiff
