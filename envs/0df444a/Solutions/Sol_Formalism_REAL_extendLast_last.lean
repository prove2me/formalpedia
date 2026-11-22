-- Prove2me | solution 1 for Formalism.REAL.extendLast_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:01.624023+00:00
-- url     : https://prove2.me/submissions/c770d72a-f743-4580-82d4-29af23bfd0d4

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
theorem _root_.solution {m : ℕ} (τ : Equiv.Perm (Fin m)) : extendLast τ (Fin.last m) = Fin.last m := by
  simp [extendLast, finSuccEquivLast_last, finSuccEquivLast_symm_none]
end Formalism.REAL
