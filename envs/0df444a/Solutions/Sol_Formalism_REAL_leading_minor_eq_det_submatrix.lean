-- Prove2me | solution 1 for Formalism.REAL.leading_minor_eq_det_submatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:34:58.158258+00:00
-- url     : https://prove2.me/submissions/4a5a27b8-4cc5-46a2-a0c4-0288487286d4

import Definitions.Def_Formalism_RealPlaceAnalysis_LminorPos
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_LeadingMinorEqDetSubmatrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (x : Matrix (Fin n) (Fin n) ℂ) (i : Fin (n + 1)) :
    lminor x i = (x.submatrix (Fin.castLE (Nat.lt_succ_iff.mp i.isLt))
      (Fin.castLE (Nat.lt_succ_iff.mp i.isLt))).det := rfl
end Formalism.REAL
