-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.psd_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:15:31.690812+00:00
-- url     : https://prove2.me/submissions/1e3ca4c6-444f-4057-9581-ae812c819786

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
theorem _root_.solution {P : Finset α} {k k' : α → α → ℂ} (hk : PSDOn P k) (hk' : PSDOn P k') :
    PSDOn P (fun x y => k x y + k' x y) := by
  unfold TA.PSDOn at hk hk' ⊢
  refine ⟨fun x hx y hy => ?_, fun a => ?_⟩
  · simp only [hk.1 x hx y hy, hk'.1 x hx y hy, map_add]
  · have e : ∑ x ∈ P, ∑ y ∈ P, conj (a x) * (k x y + k' x y) * a y =
        (∑ x ∈ P, ∑ y ∈ P, conj (a x) * k x y * a y) +
          ∑ x ∈ P, ∑ y ∈ P, conj (a x) * k' x y * a y := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [e, Complex.add_re]
    exact add_nonneg (hk.2 a) (hk'.2 a)
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
