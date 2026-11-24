-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_bS_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:52:44.503808+00:00
-- url     : https://prove2.me/submissions/5fbbbab6-2251-4ac8-ad3a-2566d1024213

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_MemSpanStandardIffProjZero
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationMaximalQuotient
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_standardBasis_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Module
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hS : SBasis) {nu mu : Fin n → ℤ} (hnu : Dominant nu) (h : nu = mu) (I : {I : TIdx nu // StdT I}) :
    ((qb_bS hS hnu h I : ↥(SMu mu)) : GLCoord ℤ n) = brk nu I.1 := by
  subst h
  exact standardBasis_coe hS nu hnu I
end Formalism.InvariantFactorPaths.ColumnFamilies
