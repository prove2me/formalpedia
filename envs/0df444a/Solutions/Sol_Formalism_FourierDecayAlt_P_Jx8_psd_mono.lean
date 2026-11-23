-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.psd_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:21.995775+00:00
-- url     : https://prove2.me/submissions/e563ba45-5b9b-4e39-a3b1-948f7d64b861

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8
variable {α : Type}
namespace Formalism.FourierDecayAlt.P.Jx8
theorem _root_.solution {F G : Finset α} (h : F ⊆ G) {k : α → α → ℂ} (hk : TB.PSDOn G k) : TB.PSDOn F k := by
  unfold TB.PSDOn at *
  exact hk.submatrix (fun x : F => (⟨x.1, h x.2⟩ : G))
end Formalism.FourierDecayAlt.P.Jx8
