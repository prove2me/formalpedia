-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBJ.Frz.contDiff_Psc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:34:00.61799+00:00
-- url     : https://prove2.me/submissions/139b6128-3762-46e1-b398-319f3d04dfdf

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockTwoDiagonalZeroSize
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_supp_bounds
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_inv_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_y_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_contDiff_gI

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBJ Formalism.FourierDecayAlt.P.PBJ.Frz
open MeasureTheory Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
open scoped Convolution
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.FourierDecayAlt.P.PBJ.Frz
theorem _root_.solution [CompleteSpace V] (β c : ℂ) {p : ℕ} {Ψ : G.Mat (p + 1) → V} (hΨ : KCls Ψ) (hc : c ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (Psc β c Ψ) := by
  obtain ⟨R, δ, hR, hδ, hb⟩ := supp_bounds hΨ
  obtain ⟨M, hM0, hM⟩ := inv_bound p R (δ / ‖c‖) (div_pos hδ (norm_pos_iff.2 hc))
  set k : Set (AB p) := Metric.closedBall 0 (p * R * M) with hkdef
  have hk : IsCompact k := isCompact_closedBall _ _
  set g : G.Mat p → AB p → V := fun H y => gI β c Ψ H (-y) with hgdef
  have hgs : ∀ H y, H ∈ (Set.univ : Set (G.Mat p)) → y ∉ k → g H y = 0 := by
    intro H y _ hy
    by_contra hne
    apply hy
    have := y_bound hR hδ hc hb hM0 hM hne
    rw [norm_neg] at this
    simpa [hkdef, Metric.mem_closedBall, dist_zero_right] using this
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry g) (Set.univ ×ˢ Set.univ) := by
    have h := (contDiff_gI β c hΨ).comp (contDiff_fst.prodMk contDiff_snd.neg)
    exact h.contDiffOn
  have hconv := contDiffOn_convolution_right_with_param (μ := (volume : Measure (AB p)))
    (f := fun _ : AB p => (1 : ℝ)) (ContinuousLinearMap.lsmul ℝ ℝ) isOpen_univ hk hgs
    (locallyIntegrable_const 1) hg
  rw [Set.univ_prod_univ, contDiffOn_univ] at hconv
  have hc2 := hconv.comp (contDiff_id.prodMk (contDiff_const (c := (0 : AB p))))
  have e : ((fun q : G.Mat p × AB p => ((fun _ : AB p => (1 : ℝ)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g q.1) q.2) ∘
      fun H : G.Mat p => (id H, (0 : AB p))) = Psc β c Ψ := by
    funext H
    simp only [Function.comp, id]
    rw [convolution_def]
    unfold Psc
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hgdef, zero_sub, neg_neg, ContinuousLinearMap.lsmul_apply, one_smul]
  rw [e] at hc2
  exact hc2
end Formalism.FourierDecayAlt.P.PBJ.Frz
