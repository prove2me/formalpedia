-- Prove2me | solution 1 for ContWeatherall.contDiff_parametric_intervalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-18T21:08:45.506984+00:00
-- url     : https://prove2.me/submissions/67bcaea9-2cee-4a24-8454-3f4aa8c16de6

import Mathlib

open scoped ContDiff Interval

universe u v

namespace ContWeatherall

/-- Smoothness of parametric interval integrals. -/
theorem cpi_main {H : Type u} {G : Type v} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {f : H → ℝ → G} (hf : ContDiff ℝ ∞ (Function.uncurry f)) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x => ∫ t in a..b, f x t) := by
  suffices key : ∀ n : ℕ, ∀ {G : Type (max u v)} [NormedAddCommGroup G] [NormedSpace ℝ G]
      [CompleteSpace G] (f : H → ℝ → G), ContDiff ℝ ∞ (Function.uncurry f) →
      ContDiff ℝ n (fun x => ∫ t in a..b, f x t) by
    let e : ULift.{u} G ≃L[ℝ] G := ContinuousLinearEquiv.ulift
    let g : H → ℝ → ULift.{u} G := fun x t => e.symm (f x t)
    have hg : ContDiff ℝ ∞ (Function.uncurry g) := e.symm.contDiff.comp hf
    have heq : (fun x => ∫ t in a..b, f x t) = fun x => e (∫ t in a..b, g x t) := by
      funext x
      have hint : IntervalIntegrable (g x) MeasureTheory.volume a b :=
        (hg.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
      have h := e.toContinuousLinearMap.intervalIntegral_comp_comm hint
      calc _ = ∫ t in a..b, e.toContinuousLinearMap (g x t) := by simp [g]
        _ = _ := h
    rw [heq]
    exact e.contDiff.comp (contDiff_infty.2 fun n => key n g hg)
  intro n
  induction n with
  | zero =>
    intro G _ _ _ f hf
    exact contDiff_zero.2
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf.continuous a b)
  | succ n ih =>
    intro G _ _ _ f hf
    set f' : H → ℝ → H →L[ℝ] G := fun x t => fderiv ℝ (fun y => f y t) x with hf'def
    have hf' : ContDiff ℝ ∞ (Function.uncurry f') := by
      have := ContDiff.fderiv (f := fun (p : H × ℝ) (y : H) => f y p.2) (g := fun p => p.1)
        (m := ∞) (n := ∞)
        (hf.comp (contDiff_snd.prodMk (contDiff_snd.comp contDiff_fst)))
        contDiff_fst (by simp)
      exact this
    have hdiff : ∀ x t, HasFDerivAt (fun y => f y t) (f' x t) x := by
      intro x t
      have : ContDiff ℝ ∞ (fun y => f y t) :=
        hf.comp (contDiff_id.prodMk contDiff_const)
      exact (this.differentiable (by simp) x).hasFDerivAt
    have hcont : ∀ x, Continuous (f x) := fun x =>
      hf.continuous.comp (continuous_const.prodMk continuous_id)
    have hcont' : ∀ x, Continuous (f' x) := fun x =>
      hf'.continuous.comp (continuous_const.prodMk continuous_id)
    have : ContDiff ℝ ((n : ℕ∞) + 1) (fun x => ∫ t in a..b, f x t) := by
      refine contDiff_succ_iff_hasFDerivAt.2 ⟨fun x => ∫ t in a..b, f' x t, ih f' hf', ?_⟩
      intro x₀
      obtain ⟨C, hC⟩ := (isCompact_uIcc (a := a) (b := b)).exists_bound_of_continuousOn
        (hcont' x₀).continuousOn
      have hev : ∀ᶠ x in nhds x₀, ∀ t ∈ Set.uIcc a b, ‖f' x t‖ < C + 1 := by
        refine (isCompact_uIcc (a := a) (b := b)).eventually_forall_of_forall_eventually ?_
        intro t ht
        have hc : Continuous fun z : H × ℝ => ‖f' z.1 z.2‖ := hf'.continuous.norm
        exact hc.continuousAt.eventually_lt continuousAt_const
          (by simpa using (hC t ht).trans_lt (lt_add_one C))
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le'' (bound := fun _ => C + 1)
        hev (Filter.Eventually.of_forall fun x => (hcont x).aestronglyMeasurable)
        ((hcont x₀).intervalIntegrable _ _) (hcont' x₀).aestronglyMeasurable ?_
        intervalIntegrable_const ?_
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc fun t ht x hx => ?_
        exact (hx t (Set.uIoc_subset_uIcc ht)).le
      · exact Filter.Eventually.of_forall fun t x _ => hdiff x t
    exact_mod_cast this

end ContWeatherall

theorem solution {H G : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {f : H → ℝ → G} (hf : ContDiff ℝ ∞ (Function.uncurry f)) (a b : ℝ) :
    ContDiff ℝ ∞ (fun x => ∫ t in a..b, f x t) :=
  ContWeatherall.cpi_main hf a b
