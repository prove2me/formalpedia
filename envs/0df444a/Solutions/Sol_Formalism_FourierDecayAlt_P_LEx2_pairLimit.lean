-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.pairLimit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:10.39556+00:00
-- url     : https://prove2.me/submissions/e37b2b21-0eb9-4486-a0a2-12a3151c1db1

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_meas_sq
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LEx2_sq_nonneg__b7974ad0744f
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_int_pr
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_norm_int_pr_le

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
theorem _root_.solution : PairLimit := by
  intro B A _ wt v v' f f' hpos hmw hmv hmv' hmf hmf' hIv hIv' hIf hIf' hT hT'
  set V : ℝ := ∫ ω, LE.sq B wt v ω ∂B.μ
  set V' : ℝ := ∫ ω, LE.sq B wt v' ω ∂B.μ
  have hV : 0 ≤ V := integral_nonneg fun ω => sq_nonneg' B wt hpos _ ω
  have hV' : 0 ≤ V' := integral_nonneg fun ω => sq_nonneg' B wt hpos _ ω
  have hIsub : ∀ (g w : Fn B A), (∀ a, Measurable fun ω => g ω a) → (∀ a, Measurable fun ω => w ω a) →
      Integrable (LE.sq B wt g) B.μ → Integrable (LE.sq B wt w) B.μ →
      Integrable (LE.sq B wt (fun ω a => g ω a - w ω a)) B.μ := by
    intro g w hg hw hIg hIw
    refine Integrable.mono' ((hIg.const_mul 2).add (hIw.const_mul 2))
      (meas_sq B wt _ hmw fun a => (hg a).sub (hw a)).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg' B wt hpos _ ω)]
    simp only [LE.sq, Pi.add_apply, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun a _ => ?_
    have h1 : ‖g ω a - w ω a‖ ≤ ‖g ω a‖ + ‖w ω a‖ := norm_sub_le _ _
    have h2 : ‖g ω a - w ω a‖ ^ 2 ≤ 2 * ‖g ω a‖ ^ 2 + 2 * ‖w ω a‖ ^ 2 := by
      nlinarith [norm_nonneg (g ω a - w ω a), sq_nonneg (‖g ω a‖ - ‖w ω a‖), norm_nonneg (g ω a), norm_nonneg (w ω a)]
    nlinarith [hpos ω a]
  rw [Metric.tendsto_nhds]
  intro η hη
  set δ : ℝ := η / (V + V' + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have hsum : Tendsto (fun ε : ℝ => ((∫ ω, LE.sq B wt (fun ω a => f ε ω a - v ω a) ω ∂B.μ) +
      ∫ ω, LE.sq B wt (fun ω a => f' ε ω a - v' ω a) ω ∂B.μ) * (1 / 2 + 1 / (2 * δ))) (𝓝[>] 0) (𝓝 0) := by
    have := (hT.add hT').mul_const (1 / 2 + 1 / (2 * δ))
    simpa using this
  have hev := (tendsto_order.mp hsum).2 (η / 2) (by positivity)
  filter_upwards [hev, self_mem_nhdsWithin] with ε hε hpos'
  have hε0 : 0 < ε := hpos'
  set a1 : Fn B A := fun ω a => f ε ω a - v ω a
  set a2 : Fn B A := fun ω a => f' ε ω a - v' ω a
  have hI1 : Integrable (LE.sq B wt a1) B.μ := hIsub _ _ (fun a => hmf ε a hε0) hmv (hIf ε hε0) hIv
  have hI2 : Integrable (LE.sq B wt a2) B.μ := hIsub _ _ (fun a => hmf' ε a hε0) hmv' (hIf' ε hε0) hIv'
  have hm1 : ∀ a, Measurable fun ω => a1 ω a := fun a => (hmf ε a hε0).sub (hmv a)
  have hm2 : ∀ a, Measurable fun ω => a2 ω a := fun a => (hmf' ε a hε0).sub (hmv' a)
  have hdec : ∀ ω, pr B wt (f ε) (f' ε) ω - pr B wt v v' ω =
      pr B wt a1 a2 ω + pr B wt a1 v' ω + pr B wt v a2 ω := by
    intro ω
    simp only [pr, a1, a2, map_sub]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have i1 := int_pr B wt hpos a1 a2 hmw hm1 hm2 hI1 hI2
  have i2 := int_pr B wt hpos a1 v' hmw hm1 hmv' hI1 hIv'
  have i3 := int_pr B wt hpos v a2 hmw hmv hm2 hIv hI2
  have i4 := int_pr B wt hpos (f ε) (f' ε) hmw (fun a => hmf ε a hε0) (fun a => hmf' ε a hε0) (hIf ε hε0) (hIf' ε hε0)
  have i5 := int_pr B wt hpos v v' hmw hmv hmv' hIv hIv'
  rw [dist_eq_norm, ← integral_sub i4 i5]
  simp_rw [hdec]
  have h12 : Integrable (fun ω => pr B wt a1 a2 ω + pr B wt a1 v' ω) B.μ := i1.add i2
  rw [integral_add h12 i3, integral_add i1 i2]
  have b1 := norm_int_pr_le B wt hpos a1 a2 hI1 hI2 1 one_pos
  have b2 := norm_int_pr_le B wt hpos a1 v' hI1 hIv' δ hδ
  have b3 := norm_int_pr_le B wt hpos v a2 hIv hI2 (1/δ) (by positivity)
  have hδV : δ * (V + V') < η := by
    rw [hδdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  set E1 : ℝ := ∫ ω, LE.sq B wt a1 ω ∂B.μ
  set E2 : ℝ := ∫ ω, LE.sq B wt a2 ω ∂B.μ
  have e3 : V / (1/δ) = δ * V := by field_simp
  have e4 : (E1 + E2) * (1 / 2 + 1 / (2 * δ)) = (E1 / 1 + 1 * E2) / 2 + E1 / δ / 2 + 1 / δ * E2 / 2 := by
    field_simp; ring
  calc _ ≤ ‖∫ ω, pr B wt a1 a2 ω ∂B.μ‖ + ‖∫ ω, pr B wt a1 v' ω ∂B.μ‖ + ‖∫ ω, pr B wt v a2 ω ∂B.μ‖ :=
        norm_add₃_le
    _ ≤ (E1 / 1 + 1 * E2) / 2 + (E1 / δ + δ * V') / 2 + (V / (1/δ) + 1/δ * E2) / 2 := by
        gcongr
    _ = (E1 + E2) * (1 / 2 + 1 / (2 * δ)) + δ * (V + V') / 2 := by rw [e4, e3]; ring
    _ < η := by linarith
end Formalism.FourierDecayAlt.P.LEx2
