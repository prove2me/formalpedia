-- Prove2me | solution 1 for Formalism.REAL.HWDiag_Amat_upper
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:12:47.615795+00:00
-- url     : https://prove2.me/submissions/8cd21a7b-cebb-4731-b3cb-3db37c3c00c9

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HWDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (l : Fin n → ℂ) : (Amat l).IsUpperTriangular := by
  intro i j hij
  have h : j < i := hij
  simp [Amat, h.ne', not_lt.mpr h.le]
end Formalism.REAL
