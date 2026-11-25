-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TheSecStab.zero_ne_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:13:50.012709+00:00
-- url     : https://prove2.me/submissions/2e8ada8a-638f-47a0-9896-8b799873cd94

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
variable {k : ℕ}
namespace Formalism.FourierDecayAlt.P.TheSecStab
theorem _root_.solution (hk : 1 ≤ k) : (0 : Fin (k + 1)) ≠ Fin.last k := by
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_zero, Fin.val_last] at h'
  omega
end Formalism.FourierDecayAlt.P.TheSecStab
