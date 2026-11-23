-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.t_OutsideSysOk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:03.789054+00:00
-- url     : https://prove2.me/submissions/5990e22d-0e3e-43ea-8d92-f43713eafc08

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_t_OutsideOk

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
namespace Formalism.FourierDecayAlt.P.Jx8
theorem _root_.solution : OutsideSysOk := by
  intro E α _ N L L' F h1 h2 h3
  obtain ⟨o1, o2, o3⟩ := t_OutsideOk E α L F
  exact ⟨h1, h2, fun t t' htt h _ h' _ => o1 t t' htt, o2, h3, o3⟩
end Formalism.FourierDecayAlt.P.Jx8
