-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.top_finsum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:11:16.868034+00:00
-- url     : https://prove2.me/submissions/42cb9cdd-4444-4754-b2c6-a6c7140e4228

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteSumLocalExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_loc_finsum
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_EZ_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_FourTermExpansion_top_lin
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_FourTermExpansion_top_apply___a095e6ea583d


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
theorem _root_.solution (M : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Mat k r) {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (Φ : ι → Mat k r → E) {g : Mat k r} (hg : g ∈ GV k r) (h : ∀ i ∈ s, Loc 1 (Φ i) g)
    (v : ℂ) (a b : Fin (2 * r + k + 1)) :
    Top (FourTermExpansion.LT M) v a b (fun z => ∑ i ∈ s, c i • Φ i z) g = ∑ i ∈ s, c i • Top (FourTermExpansion.LT M) v a b (Φ i) g := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp [FourTermExpansion.top_apply'', FourTermExpansion.EZ_zero]
  · intro j s hj ih h
    have hs : ∀ i ∈ s, Loc 1 (Φ i) g := fun i hi => h i (Finset.mem_insert_of_mem hi)
    calc Top (FourTermExpansion.LT M) v a b (fun z => ∑ i ∈ insert j s, c i • Φ i z) g
        = Top (FourTermExpansion.LT M) v a b (fun z => (∑ i ∈ s, c i • Φ i z) + c j • Φ j z) g := by
          congr 1; funext z; rw [Finset.sum_insert hj, add_comm]
      _ = Top (FourTermExpansion.LT M) v a b (fun z => ∑ i ∈ s, c i • Φ i z) g + c j • Top (FourTermExpansion.LT M) v a b (Φ j) g :=
          FourTermExpansion.top_lin M (loc_finsum s c Φ hs) (h j (Finset.mem_insert_self j s)) hg (c j) v a b
      _ = _ := by rw [ih hs, Finset.sum_insert hj, add_comm]
end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
