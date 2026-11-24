-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion.conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:28:26.172396+00:00
-- url     : https://prove2.me/submissions/81e4c979-4659-4f6a-a61d-e2b5133aabcf

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourTermExpansion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CvRhoOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfCVUnderIntOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOrbitSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FiniteSumLocalExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_gv_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_FiniteSumLocalExpansion_Mc_expand
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_LieDecompositionLocal_EZ_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
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
theorem _root_.solution (y : Mat k r) (hy : y ∈ GV k r) {Ψ : Mat k r → E} {g : Mat k r} (hΨ : Loc 1 Ψ g)
    (hg : g ∈ GV k r) (v : ℂ) (a b : Fin (2 * r + k + 1)) :
    Top (FourTermExpansion.LT (Mc y)) v a b Ψ g = ∑ ab : Fin (2 * r + k + 1) × Fin (2 * r + k + 1),
      ((y⁻¹) ab.1 a * y b ab.2) • Top (FourTermExpansion.LT (Msg k r)) v ab.1 ab.2 Ψ g := by
  have hsum : ∑ ab : Fin (2 * r + k + 1) × Fin (2 * r + k + 1),
      ((y⁻¹) ab.1 a * y b ab.2) • (if ab.1 = ab.2 then v • Ψ g else 0) = if a = b then v • Ψ g else 0 := by
    have h1 : ∀ ab : Fin (2 * r + k + 1) × Fin (2 * r + k + 1),
        ((y⁻¹) ab.1 a * y b ab.2) • (if ab.1 = ab.2 then v • Ψ g else (0 : E)) =
          (if ab.1 = ab.2 then (y⁻¹) ab.1 a * y b ab.2 else 0) • (v • Ψ g) := fun ab => by
      split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun ab _ => h1 ab), ← Finset.sum_smul]
    have h2 : ∑ ab : Fin (2 * r + k + 1) × Fin (2 * r + k + 1),
        (if ab.1 = ab.2 then (y⁻¹) ab.1 a * y b ab.2 else 0) = if a = b then 1 else 0 := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      have := congrFun (congrFun (gv_inv hy).1 b) a
      rw [Matrix.mul_apply] at this
      rw [Finset.sum_congr rfl (fun p _ => mul_comm _ _), this, Matrix.one_apply]
      simp only [eq_comm]
    rw [h2]
    split_ifs <;> simp
  rw [FourTermExpansion.top_apply'' (Mc y), Mc_expand y a b, EZ_sum hΨ hg]
  simp only [FourTermExpansion.top_apply'', smul_add, Finset.sum_add_distrib, hsum]
end Formalism.FourierDecayAlt.P.FiniteSumLocalExpansion
