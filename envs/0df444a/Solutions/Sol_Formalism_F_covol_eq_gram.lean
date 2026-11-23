-- Prove2me | solution 1 for Formalism.F.covol_eq_gram
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:25:08.082845+00:00
-- url     : https://prove2.me/submissions/a346c100-9bcc-4ef5-b6b0-d8088c18324f

import Definitions.Def_Formalism_LatticeSlopes_Statement
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_CovolEqGram
import Theorems.Thm_Formalism_F_det_gram_basis_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.F
namespace Formalism.F
theorem _root_.solution : CovolEqGram := by
  intro E _ _ _ L hL ι _ _ b
  unfold covol
  rw [dif_pos hL]
  congr 1
  exact det_gram_basis_eq L (Module.finBasis ℤ L) b
end Formalism.F
