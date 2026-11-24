-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx2.Tri.hsVec_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:19:49.888513+00:00
-- url     : https://prove2.me/submissions/67a358d2-9c06-40de-8029-62b671cf127d

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Tri_hsVec_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_TBBx2_Tri_hsVec_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2 Formalism.FourierDecayAlt.P.TBBx2.Tri
open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB
open scoped ENNReal
noncomputable section
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.TBBx2.Tri
theorem _root_.solution {n : ℕ} (A : Fin n → Wq →L[ℂ] Wp) (s : Finset (Fin n)) :
    B.hsVec (∑ i ∈ s, A i) = ∑ i ∈ s, B.hsVec (A i) := by
  induction s using Finset.induction_on with
  | empty => simp [hsVec_zero]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hsVec_add, ih]
end Formalism.FourierDecayAlt.P.TBBx2.Tri
