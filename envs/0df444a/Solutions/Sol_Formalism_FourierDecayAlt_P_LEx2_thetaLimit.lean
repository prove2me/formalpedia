-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.thetaLimit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:35:14.273341+00:00
-- url     : https://prove2.me/submissions/f8e2260b-ce55-445b-b1b6-c443c4ca2fc7

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_thetaForm
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_Fk_iter_lim

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
theorem _root_.solution : ThetaLimit := by
  intro σ p x hx
  have hlog : Tendsto (fun ε : ℝ => Real.log x - Real.log ε) (𝓝[>] 0) atTop := by
    have := Real.tendsto_log_nhdsGT_zero
    have h2 : Tendsto (fun ε : ℝ => -Real.log ε) (𝓝[>] 0) atTop := tendsto_neg_atBot_atTop.comp this
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_left _ (Real.log x) h2
  have h := (Fk_iter_lim p 0 σ).comp hlog
  simp only [and_true] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : 0 < ε := hε
  unfold ld
  have : (fun u : ℝ => th ε σ (Real.exp u)) = fun u : ℝ => Fk 0 σ (u - Real.log ε) := by
    funext u
    rw [thetaForm ε σ hε0 u]
    unfold Fk
    have : Real.exp (-(u - Real.log ε)) = ε * Real.exp (-u) := by
      rw [neg_sub, Real.exp_sub, Real.exp_log hε0, Real.exp_neg]; ring
    rw [this]; simp
  rw [this, iteratedDeriv_comp_sub_const]
  rfl
end Formalism.FourierDecayAlt.P.LEx2
