-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DensitySumsAndDomination.psd_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:49.403581+00:00
-- url     : https://prove2.me/submissions/f7dc04ac-aa9b-41b3-95aa-bb9ab6a1ff15

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DensitySumsAndDomination

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexInnerProductSpace ComplexOrder ComplexConjugate
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DensitySumsAndDomination
namespace Formalism.FourierDecayAlt.P.DensitySumsAndDomination
theorem _root_.solution {α : Type} {Y : Finset α} {k k' : α → α → ℂ}
    (h : ∀ x ∈ Y, ∀ y ∈ Y, k x y = k' x y) (hk : TB.PSDOn Y k) : TB.PSDOn Y k' := by
  unfold TB.PSDOn at *
  have e : (Matrix.of fun x y : Y => k x y) = Matrix.of fun x y : Y => k' x y := by
    ext x y
    simp only [Matrix.of_apply]
    exact h x x.2 y y.2
  rwa [← e]
end Formalism.FourierDecayAlt.P.DensitySumsAndDomination
