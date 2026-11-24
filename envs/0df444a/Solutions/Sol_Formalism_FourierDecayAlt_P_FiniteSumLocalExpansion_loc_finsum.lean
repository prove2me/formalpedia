-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.loc_finsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:53:50.870806+00:00
-- url     : https://prove2.me/submissions/28e9772f-29f1-4eb6-bd2a-1aee6c898a6f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteSumLocalExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_loc_of_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_loc_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_loc_add
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabGlW_loc_add


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5 Formalism.FourierDecayAlt.P.CapelliWordSumExpansion Formalism.FourierDecayAlt.P.LieDecompositionLocal
  Formalism.FourierDecayAlt.P.FourTermExpansion
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
theorem _root_.solution {ι : Type*} (s : Finset ι) (c : ι → ℂ) (Φ : ι → Mat k r → E) {m : ℕ∞} {g : Mat k r}
    (h : ∀ i ∈ s, Loc m (Φ i) g) : Loc m (fun z => ∑ i ∈ s, c i • Φ i z) g := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    exact loc_of_eq (by funext z; simp) (loc_zero m g)
  · intro j s hj ih h
    exact loc_of_eq (by funext z; rw [Finset.sum_insert hj, add_comm])
      (loc_add (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) (h j (Finset.mem_insert_self j s)) (c j))
end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
