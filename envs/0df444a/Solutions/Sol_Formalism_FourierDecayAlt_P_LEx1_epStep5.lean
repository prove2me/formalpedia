-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.epStep5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:27:26.756061+00:00
-- url     : https://prove2.me/submissions/cbf92b8a-7845-417b-bfe9-065c5cf7c67c

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_pr_mulF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution : EpStep5 := by
  intro B X c hMeas hBeta
  obtain ⟨hmu, hmC, hmd, hmS⟩ := hMeas
  obtain ⟨hIu, hIh⟩ := hBeta
  unfold EP.beta
  simp_rw [pr_mulF]
  have hmpr : Measurable fun ω => pr B (fun _ _ => (1:ℝ)) (X.Cw X.u) X.u ω := by
    unfold pr
    refine Finset.measurable_sum _ fun a _ => ?_
    exact (measurable_const.mul (hmC a)).mul (Complex.continuous_conj.measurable.comp (hmu a))
  have hbd : ∀ ω, ‖pr B (fun _ _ => (1:ℝ)) (X.Cw X.u) X.u ω‖ ≤
      LE.sq B (fun _ _ => 1) (X.Cw X.u) ω + LE.sq B (fun _ _ => 1) X.u ω := by
    intro ω
    unfold pr LE.sq
    rw [← Finset.sum_add_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    simp only [Complex.ofReal_one, one_mul, norm_mul, RCLike.norm_conj]
    nlinarith [sq_nonneg (‖X.Cw X.u ω a‖ - ‖X.u ω a‖), norm_nonneg (X.Cw X.u ω a), norm_nonneg (X.u ω a)]
  refine tendsto_integral_filter_of_dominated_convergence
    (fun ω => LE.sq B (fun _ _ => 1) (X.Cw X.u) ω + LE.sq B (fun _ _ => 1) X.u ω) ?_ ?_ (hIh.add hIu) ?_
  · refine Eventually.of_forall fun ε => ?_
    refine Measurable.aestronglyMeasurable (Measurable.mul ?_ hmpr)
    refine Complex.measurable_ofReal.comp ?_
    unfold Cut.sc
    exact ((c.smooth.continuous.measurable.comp (B.G_meas.div_const ε)).pow_const 2)
  · refine Eventually.of_forall fun ε => Eventually.of_forall fun ω => ?_
    rw [norm_mul]
    have h1 : ‖((c.sc ε 2 (B.G ω) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      unfold Cut.sc
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_one₀ (c.nonneg _) (c.le_one _)
    calc _ ≤ 1 * ‖pr B (fun _ _ => (1:ℝ)) (X.Cw X.u) X.u ω‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact hbd ω
  · refine Eventually.of_forall fun ω => ?_
    refine tendsto_const_nhds.congr' ?_
    have : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Set.Ioo 0 (B.G ω) := Ioo_mem_nhdsGT (B.G_pos ω)
    filter_upwards [this] with ε hε
    have h1 : 1 ≤ B.G ω / ε := by rw [le_div_iff₀ hε.1]; linarith [hε.2]
    simp [Cut.sc, c.one _ h1]
end Formalism.FourierDecayAlt.P.LEx1
