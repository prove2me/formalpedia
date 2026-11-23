-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.coefIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:38:42.658157+00:00
-- url     : https://prove2.me/submissions/b7ba3886-8992-4fab-88f6-ae9b7355d74b

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_weighted_L2_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_weighted_L2_const_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_coefficient_L2
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_dS_poly
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_meas_th

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution : CoefIntegrable := by
  intro B S σ _ hM hW h4 h4' ε hε Y hY p
  obtain ⟨c, hc⟩ := h4 Y hY
  have hth : ∀ ω, 0 ≤ th ε σ (B.G ω) := fun ω =>
    Real.rpow_nonneg (div_nonneg (B.G_pos ω).le (by have := B.G_pos ω; linarith)) _
  have hd : ∀ ω k, 0 ≤ S.d Y ω k := fun ω k => (hW.2 Y hY ω k).le
  have hk : ∀ k, WeightedL2 B (fun ω => th ε σ (B.G ω) * S.d Y ω k) (fun ω => S.ds Y p ω k) := by
    intro k
    have hco := coefficient_L2 B 1 (S.r + 1) (fun ω => th ε σ (B.G ω) * S.d Y ω k) (fun y ω => S.gs Y (y 0) ω k)
      (fun κ ω => c (κ 0 : ℕ) ω k) (fun _ => Set.univ) (fun ω => mul_nonneg (hth ω) (hd ω k))
      (fun _ => Set.infinite_univ)
      (by
        intro y ω
        show conjS B (S.g Y) S.X (y 0) ω k = _
        rw [hc (y 0) ω k]
        rw [← (Equiv.funUnique (Fin 1) (Fin (S.r + 1 + 1))).symm.sum_comp]
        rw [← Fin.sum_univ_eq_sum_range (fun q => ((y 0 : ℝ) : ℂ) ^ q * c q ω k)]
        apply Finset.sum_congr rfl
        intro i _
        simp [Equiv.funUnique])
      (by
        intro y _
        refine ⟨((hM.2.2 Y hY).2 (y 0) k).aestronglyMeasurable, ?_⟩
        refine Integrable.mono' ((h4' ε hε).1 Y hY (y 0)) ?_ (Filter.Eventually.of_forall ?_)
        · exact (((meas_th B ε σ).mul ((hM.2.2 Y hY).1 k)).mul
            (((hM.2.2 Y hY).2 (y 0) k).norm.pow_const 2)).aestronglyMeasurable
        · intro ω
          rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (hth ω) (hd ω k)) (by positivity)), mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (hth ω)
          unfold LE.sq
          exact Finset.single_le_sum (f := fun k => S.d Y ω k * ‖S.gs Y (y 0) ω k‖ ^ 2)
            (fun k _ => mul_nonneg (hd ω k) (by positivity)) (Finset.mem_univ k))
    have hds : (fun ω => S.ds Y p ω k) =
        fun ω => (p.factorial : ℂ) * (if p < S.r + 1 + 1 then c p ω k else 0) := by
      funext ω
      exact dS_poly B (S.g Y) S.X (S.r + 1) c hc p ω k
    rw [hds]
    apply weighted_L2_const_mul
    by_cases hp : p < S.r + 1 + 1
    · simp only [if_pos hp]
      exact hco (fun _ => ⟨p, hp⟩)
    · simp only [if_neg hp]
      exact weighted_L2_zero B _
  have he : (fun ω => th ε σ (B.G ω) * LE.sq B (S.d Y) (S.ds Y p) ω) =
      fun ω => ∑ k, (th ε σ (B.G ω) * S.d Y ω k) * ‖S.ds Y p ω k‖ ^ 2 := by
    funext ω; unfold LE.sq; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  rw [he]
  exact integrable_finset_sum _ (fun k _ => (hk k).2)
end Formalism.FourierDecayAlt.P.LEx2
