-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.psd_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:42:36.876276+00:00
-- url     : https://prove2.me/submissions/97eb0097-fe09-417e-902b-b1baa0159899

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
variable {α : Type} {F : Finset α}
namespace Formalism.FourierDecayAlt.P.Jx8
theorem _root_.solution {k k' : α → α → ℂ} (h : ∀ x ∈ F, ∀ y ∈ F, k x y = k' x y) (hk : TB.PSDOn F k) :
    TB.PSDOn F k' := by
  unfold TB.PSDOn at *
  have : (Matrix.of fun x y : F => k' x y) = Matrix.of fun x y : F => k x y := by
    ext x y; exact (h x x.2 y y.2).symm
  rw [this]; exact hk
end Formalism.FourierDecayAlt.P.Jx8
