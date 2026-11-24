-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW.erase_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:36:36.255217+00:00
-- url     : https://prove2.me/submissions/c2904649-4641-4cff-8ef1-6d0c0ff660c6

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAPRTWNeAlgSt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IrreducibleCapelliModules
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreKLExistsOfAlg
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJAPRTWNeAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA Formalism.FourierDecayAlt.P.CutMP.JA.SSn Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
theorem _root_.solution {n : ℕ} (p : Fin n → ℂ) (hp : Function.Injective p) (i : Fin n) :
    ∏ j ∈ Finset.univ.erase i, (-p i + p j) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro j hj h
  exact Finset.ne_of_mem_erase hj (hp (by linear_combination h))
end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW
