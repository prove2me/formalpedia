-- Prove2me | solution 1 for Formalism.riemannZetaOne_ne_zero_of_integrable_mellin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:50:58.919104+00:00
-- url     : https://prove2.me/submissions/ad18310a-94e9-468d-84d6-36fd9daff00e

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_OfRealNeOfRealOfLt
import Definitions.Def_Formalism_ZetaNonvanishing_LandauEq
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_ZetaNonvanishing_MellinElem
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_LogDerivZeroFree
import Definitions.Def_Formalism_ZetaNonvanishing_MellinDeriv
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaLandau
import Theorems.Thm_Formalism_AZ_eq
import Theorems.Thm_Formalism_differentiable_AZ
import Theorems.Thm_Formalism_measurable_HZ
import Theorems.Thm_Formalism_mellin_HZ
import Theorems.Thm_Formalism_ne_one_of_one_lt_re
import Theorems.Thm_Formalism_ne_zero_of_lt_re
import Theorems.Thm_Formalism_riemannZetaOne_ne_zero_of_one_le_re
import Theorems.Thm_Formalism_sub_ne_zero_of_lt_re


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
open ArithmeticFunction
namespace Formalism
theorem _root_.solution (h1 : MellinDeriv) (h3 : MellinSgen) (h5 : MellinElem)
    (h11 : LogDerivZeroFree) {ε C θ : ℝ} (hε : ε * ε = 1) (hθ1 : θ < 1)
    (hH : ∀ x : ℝ, 1 ≤ x → 0 ≤ HZ ε C θ x)
    (hInt : ∀ σ : ℝ, θ < σ → IntegrableOn (fun x : ℝ => HZ ε C θ x * x ^ (-σ - 1)) (Ioi 1)) :
    ∀ s : ℂ, θ < s.re → riemannZeta₁ s ≠ 0 := by
  set U : Set ℂ := {s | θ < s.re} with hU_def
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hId : DifferentiableOn ℂ (IZ ε C θ) U := by
    intro s hs
    have hD := h1 (fun x => ((HZ ε C θ x : ℝ) : ℂ)) θ
      (Complex.measurable_ofReal.comp (measurable_HZ h3 ε C θ)).aestronglyMeasurable
      (fun σ hσ => (hInt σ hσ).congr_fun (fun x hx => by
        simp only [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hH x (le_of_lt (mem_Ioi.mp hx)))])
        measurableSet_Ioi) s hs
    exact hD.differentiableAt.differentiableWithinAt
  have hZd : Differentiable ℂ riemannZeta₁ := differentiable_riemannZeta₁
  have hAd := differentiable_AZ
  have hf1 : DifferentiableOn ℂ
      (fun s => s * (s - 1) * riemannZeta₁ s * (IZ ε C θ s - C / (s - θ))) U := by
    intro s hs
    have hsθ : s - (θ : ℂ) ≠ 0 := sub_ne_zero_of_lt_re hs
    have hIs := (hId s hs).differentiableAt (hUopen.mem_nhds hs)
    have hEs := hZd s
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := exact hsθ)
  have hEq : EqOn (fun s => s * (s - 1) * riemannZeta₁ s * (IZ ε C θ s - C / (s - θ)))
      (fun s => (ε : ℂ) * AZ s) U := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (hf1.analyticOnNhd hUopen)
      ((hAd.const_mul (ε : ℂ)).differentiableOn.analyticOnNhd hUopen)
      (convex_halfSpace_re_gt θ).isPreconnected (z₀ := 2)
      (show θ < (2:ℂ).re by simp; linarith) ?_
    have h2mem : (2:ℂ) ∈ {s : ℂ | 1 < s.re} := by simp
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds h2mem] with z hz
    have hz' : 1 < z.re := hz
    have hZ := riemannZetaOne_ne_zero_of_one_le_re hz'.le
    have hs1' : z - 1 ≠ 0 := sub_ne_zero.mpr (ne_one_of_one_lt_re hz')
    have hs0 : z ≠ 0 := ne_zero_of_lt_re zero_le_one hz'
    have hsθ : z - θ ≠ 0 := sub_ne_zero_of_lt_re (a := θ) (by linarith)
    rw [mellin_HZ h3 h5 hθ1 hz', AZ_eq hZ]
    field_simp
    ring
  set q : ℂ → ℂ := fun s => linZ s - (ε : ℂ) * (s * (s - 1) * (IZ ε C θ s - C / (s - θ)))
    with hq_def
  have hqd : DifferentiableOn ℂ q U := by
    intro s hs
    have hsθ : s - (θ : ℂ) ≠ 0 := sub_ne_zero_of_lt_re hs
    have hIs := (hId s hs).differentiableAt (hUopen.mem_nhds hs)
    apply DifferentiableAt.differentiableWithinAt
    simp only [hq_def, linZ]
    fun_prop (disch := exact hsθ)
  have hid : ∀ s ∈ U, deriv riemannZeta₁ s = q s * riemannZeta₁ s := by
    intro s hs
    have he := hEq hs
    simp only at he
    unfold AZ at he
    have hεc : (ε : ℂ) * ε = 1 := by exact_mod_cast hε
    simp only [hq_def]
    linear_combination (ε : ℂ) * he - (deriv riemannZeta₁ s - linZ s * riemannZeta₁ s) * hεc
  intro s hs
  exact h11 riemannZeta₁ q U hUopen hZd ⟨1, by simp⟩ hqd hid s hs
end Formalism
