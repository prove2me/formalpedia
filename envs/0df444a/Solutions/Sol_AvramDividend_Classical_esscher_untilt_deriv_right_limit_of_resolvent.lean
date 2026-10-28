-- Prove2me | solution 1 for AvramDividend.Classical.esscher_untilt_deriv_right_limit_of_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T10:56:03.271994+00:00
-- url     : https://prove2.me/submissions/d6e137e4-0080-4624-8cd7-4b937144e11d

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical Set Filter
open scoped Topology
theorem solution
    (W V g : ℝ → ℝ) (φ s : ℝ)
    (hW : ∀ x : ℝ, 0 < x → W x = Real.exp (φ * x) * V x)
    (hVlim : Tendsto V (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hgcont : ContinuousOn g (Ici (0 : ℝ)))
    (hgzero : g 0 = s)
    (hVderiv : ∀ x : ℝ, 0 < x → HasDerivAt V (g x) x) :
    Tendsto (deriv W) (𝓝[>] (0 : ℝ)) (𝓝 s) := by
  have hd : ∀ x : ℝ, 0 < x →
      deriv W x = (Real.exp (φ * x) * φ) * V x + Real.exp (φ * x) * g x := by
    intro x hx
    have h1 : HasDerivAt (fun z => Real.exp (φ * z)) (Real.exp (φ * x) * φ) x := by
      simpa using ((hasDerivAt_id x).const_mul φ).exp
    have h2 := h1.mul (hVderiv x hx)
    refine (h2.congr_of_eventuallyEq ?_).deriv
    filter_upwards [Ioi_mem_nhds hx] with z hz
    exact hW z hz
  have hexp : Tendsto (fun x => Real.exp (φ * x)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have : Continuous (fun x : ℝ => Real.exp (φ * x)) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hg : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 s) := by
    rw [← hgzero]
    exact ((hgcont 0 (le_refl (0:ℝ))).mono Ioi_subset_Ici_self).tendsto
  have := ((hexp.mul_const φ).mul hVlim).add (hexp.mul hg)
  simp only [mul_zero, one_mul, zero_add] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (hd x hx).symm
