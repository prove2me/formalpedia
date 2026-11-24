-- Prove2me | solution 1 for Formalism.ZF.perron_continuous_Fy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:42:19.710402+00:00
-- url     : https://prove2.me/submissions/19610cca-1261-4d8e-b7e0-9ef48d7a3c86

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution {y : ℝ} (hy : 0 < y) {σ₀ : ℝ} (hσ : 1 < σ₀) :
    Continuous (fun t : ℝ => Fy y ((σ₀ : ℂ) + t * I)) := by
  have hU : ∀ t : ℝ, 1 < ((σ₀ : ℂ) + t * I).re := fun t => by simpa using hσ
  have hzd : DifferentiableOn ℂ riemannZeta {s : ℂ | 1 < s.re} := fun s hs =>
    (differentiableAt_riemannZeta (fun h => by rw [h] at hs; simp at hs)).differentiableWithinAt
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hderiv : ContinuousOn (deriv riemannZeta) {s : ℂ | 1 < s.re} :=
    ((hzd.analyticOnNhd hopen).deriv).continuousOn
  have hline : Continuous (fun t : ℝ => (σ₀ : ℂ) + t * I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  unfold Fy
  refine Continuous.div (Continuous.mul (Continuous.neg (Continuous.div ?_ ?_ ?_)) ?_) ?_ ?_
  · exact hderiv.comp_continuous hline hU
  · exact hzd.continuousOn.comp_continuous hline hU
  · intro t
    exact riemannZeta_ne_zero_of_one_lt_re (hU t)
  · exact hline.const_cpow (Or.inl (by exact_mod_cast hy.ne'))
  · exact hline.mul (hline.sub continuous_const)
  · intro t
    have h1 := hU t
    refine mul_ne_zero ?_ ?_
    · intro h
      rw [h] at h1
      norm_num at h1
    · intro h
      rw [sub_eq_zero] at h
      rw [h] at h1
      simp at h1
end Formalism.ZF
