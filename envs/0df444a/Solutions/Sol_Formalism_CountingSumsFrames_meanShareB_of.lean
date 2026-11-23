-- Prove2me | solution 1 for Formalism.CountingSumsFrames.meanShareB_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:57:09.415792+00:00
-- url     : https://prove2.me/submissions/7ec5bd4b-38ef-43aa-b1d3-e61ab7d2c2db

import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SegmentBoundThreeHolds
import Theorems.Thm_Formalism_CountingSumsFrames_mean_share_abs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution (h : DigitVectorsCount) : MeanShareB := by
  intro s m P I R _ bad rk Mlo Mhi eps K hP hI heps hK hbad hMlo hMhi hrk hsum
  classical
  convert mean_share_abs (Fintype.piFinset fun _ : Fin (s+1) => I) DigitCompat (∏ i, P i ^ m)
    (Finset.prod_pos fun i _ => pow_pos (hP i) m)
    (fun aa _ => by convert h s m P aa hP) bad rk Mlo Mhi eps K
    (Fintype.piFinset_nonempty.mpr fun _ => hI) heps hK hbad hMlo hMhi hrk (by convert hsum)
end Formalism.CountingSumsFrames
