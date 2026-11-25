-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TheSecStab.emb_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:37:47.528599+00:00
-- url     : https://prove2.me/submissions/03f5fad0-efd3-4694-9f44-d8bc48b9f123

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSection
import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutGCoreCut
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheSectionStab

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TheSecStab
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TwoByOneBlock Formalism.FourierDecayAlt.P.TheSec
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.TheSecStab
theorem _root_.solution {μ μ' : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (h : embWb k r μ = embWb k r μ') : μ = μ' := by
  ext a b
  have ha : a.val ≤ k := Nat.lt_succ_iff.mp a.isLt
  have hb : b.val ≤ k := Nat.lt_succ_iff.mp b.isLt
  have e := congrFun (congrFun h ⟨r + a.val, by omega⟩) ⟨r + b.val, by omega⟩
  simpa [embWb, ha, hb] using e
end Formalism.FourierDecayAlt.P.TheSecStab
