-- Prove2me | solution 1 for Formalism.REAL.extendLast_castSucc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:29.900815+00:00
-- url     : https://prove2.me/submissions/9882f222-c79d-4dec-86ea-a56eabfe7981

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
theorem _root_.solution {m : ℕ} (τ : Equiv.Perm (Fin m)) (k : Fin m) :
    extendLast τ k.castSucc = (τ k).castSucc := by
  simp [extendLast, finSuccEquivLast_castSucc, finSuccEquivLast_symm_some]
end Formalism.REAL
