-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.psd_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:29.533294+00:00
-- url     : https://prove2.me/submissions/863cc975-401e-4377-ab4f-b167a54638c9

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
variable {α : Type}
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
theorem _root_.solution {P : Finset α} {k k' : α → α → ℂ} (h : ∀ x ∈ P, ∀ y ∈ P, k x y = k' x y)
    (hk : PSDOn P k) : PSDOn P k' := by
  unfold TA.PSDOn at hk ⊢
  refine ⟨fun x hx y hy => ?_, fun a => ?_⟩
  · rw [← h x hx y hy, ← h y hy x hx]
    exact hk.1 x hx y hy
  · have e : ∑ x ∈ P, ∑ y ∈ P, conj (a x) * k' x y * a y =
        ∑ x ∈ P, ∑ y ∈ P, conj (a x) * k x y * a y :=
      Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by rw [h x hx y hy]
    rw [e]
    exact hk.2 a
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
