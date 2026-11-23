-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.LW.prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:26:55.882165+00:00
-- url     : https://prove2.me/submissions/e67b5596-bbd1-4d1d-9935-3a5b121db93b

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_LW_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_LW_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ} {m : ℕ} {c : K}
namespace Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
namespace LW
theorem _root_.solution {ι : Type} (s : Finset ι) {f : ι → (Fin m → K) → K} (hf : ∀ i, LW R c (f i)) :
    LW R c (fun v => ∏ i ∈ s, f i v) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LW.const (R := R) (c := c) (m := m) R.one_mem
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a).mul ih
end LW
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
