-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.rdV_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:21:20.539064+00:00
-- url     : https://prove2.me/submissions/5556ff10-93ac-4dca-8914-6658998a1120

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_CapelliWordSumExpansion_loc_hasDerivAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
theorem _root_.solution {ι : Type*} (L : List ι) (c : ι → ℂ) (h : ι → Mat k r → E) {g X : Mat k r}
    (hg : g ∈ GV k r) (hX : inLie k r X) (hL : ∀ i ∈ L, Loc 1 (h i) g) :
    RdV X (fun x => (L.map fun i => c i • h i x).sum) g = (L.map fun i => c i • RdV X (h i) g).sum := by
  have key : HasDerivAt (fun t : ℝ => (L.map fun i => c i • h i (g * NormedSpace.exp ((t : ℂ) • X))).sum)
      ((L.map fun i => c i • RdV X (h i) g).sum) 0 := by
    induction L with
    | nil => simpa using hasDerivAt_const (0 : ℝ) (0 : E)
    | cons i L ih =>
      simp only [List.map_cons, List.sum_cons]
      exact ((loc_hasDerivAt le_rfl (hL i (by simp)) hg hX).const_smul (c i)).add
        (ih (fun j hj => hL j (by simp [hj])))
  exact key.deriv
end Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
