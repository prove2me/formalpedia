-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2b2.PfN.L_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:02:39.002979+00:00
-- url     : https://prove2.me/submissions/adcbd00b-2923-4745-a03c-fe04055441d6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_WeightedSumIntegralFormula
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_NoExceptionalOfNoRealZero
import Theorems.Thm_Formalism_HermitianLattices_GL2b2_PfN_tt_bound
import Theorems.Thm_Formalism_HermitianLattices_GL2b2_PfN_summable_u
import Theorems.Thm_Formalism_HermitianLattices_GL2b2_PfN_tt_differentiable
import Theorems.Thm_Formalism_HermitianLattices_GL2b2_PfN_series_eq
import Theorems.Thm_Formalism_HermitianLattices_GL2b2_PfN_chi_eight_ne_one
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply



set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2b2
open Formalism.HermitianLattices.GL2b2.PfN
open Complex
namespace Formalism.HermitianLattices.GL2b2.PfN
theorem _root_.solution (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) :
    DirichletCharacter.LFunction ZeroFreeRegionGL2.chi8 (σ : ℂ) = ∑' k, tt k (σ : ℂ) := by
  let U : Set ℂ := {s | σ / 2 < s.re} ∩ Metric.ball 0 3
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hUc : Convex ℝ U := (convex_halfSpace_re_gt _).inter (convex_ball _ _)
  have hG : DifferentiableOn ℂ (fun s => ∑' k, tt k s) U := by
    apply differentiableOn_tsum_of_summable_norm (summable_u (σ / 2) 3 (by linarith))
      (fun k => (tt_differentiable k).differentiableOn) hUo
    intro k w hw
    exact tt_bound k w (σ / 2) 3 (by linarith) hw.1.le (mem_ball_zero_iff.1 hw.2).le
  have hL : DifferentiableOn ℂ (DirichletCharacter.LFunction ZeroFreeRegionGL2.chi8) U :=
    (DirichletCharacter.differentiable_LFunction chi_eight_ne_one).differentiableOn
  have h2U : (2 : ℂ) ∈ U := ⟨by simp; linarith, by simp; norm_num⟩
  have hσU : (σ : ℂ) ∈ U := ⟨by simp; linarith, by simp [abs_of_pos h0]; linarith⟩
  have hev : DirichletCharacter.LFunction ZeroFreeRegionGL2.chi8 =ᶠ[nhds (2 : ℂ)] (fun s => ∑' k, tt k s) := by
    have : {s : ℂ | 1 < s.re} ∈ nhds (2 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [this] with s hs using series_eq s hs
  exact (hL.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hG.analyticOnNhd hUo)
    hUc.isPreconnected h2U hev hσU
end Formalism.HermitianLattices.GL2b2.PfN
