-- Prove2me | solution 1 for Formalism.REAL.sign_extendLast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:59:11.125802+00:00
-- url     : https://prove2.me/submissions/b3f52a5a-c6a9-43cf-ba44-1109b3a221ff

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet

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
theorem _root_.solution {m : ℕ} (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (extendLast τ) = Equiv.Perm.sign τ := by
  rw [extendLast, Equiv.Perm.sign_trans_trans_symm]
  exact Equiv.optionCongr_sign τ
end Formalism.REAL
