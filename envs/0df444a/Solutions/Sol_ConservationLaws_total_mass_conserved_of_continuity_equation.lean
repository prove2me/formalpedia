-- Prove2me | solution 1 for ConservationLaws.total_mass_conserved_of_continuity_equation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T23:00:47.498982+00:00
-- url     : https://prove2.me/submissions/3cfba153-b3ce-41ef-8258-9f3c4e5f6e9c

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Operations
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped Topology
private theorem mass_time_integral_derivative {n : ℕ} (ρ : ℝ → EuclideanSpace ℝ (Fin n) → ℝ) (hρ : ContDiff ℝ 1 (fun p : ℝ × EuclideanSpace ℝ (Fin n) => ρ p.1 p.2)) (R : ℝ) (hs : ∀ t x, R < ‖x‖ → ρ t x = 0) (t₀ : ℝ) : HasDerivAt (fun t => ∫ x, ρ t x) (∫ x, deriv (fun s => ρ s x) t₀) t₀ := by
  classical
  let Φ : ℝ × EuclideanSpace ℝ (Fin n) → ℝ := fun p => ρ p.1 p.2
  let v : ℝ × EuclideanSpace ℝ (Fin n) := (1, 0)
  have hslice (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : HasDerivAt (fun s => ρ s x) (fderiv ℝ Φ (t, x) v) t := by
    have hh : HasFDerivAt Φ (fderiv ℝ Φ (t, x)) (t, x) :=
      (hρ.differentiable_one (t, x)).hasFDerivAt
    have hh' : HasDerivAt (fun s : ℝ => ((s, x) : ℝ × EuclideanSpace ℝ (Fin n))) v t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
    exact hh.comp_hasDerivAt t hh'
  have hkey (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
      deriv (fun s => ρ s x) t = fderiv ℝ Φ (t, x) v :=
    (hslice t x).deriv
  have hdcont : Continuous (fun p => fderiv ℝ Φ p v) :=
    (hρ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  let K : Set (EuclideanSpace ℝ (Fin n)) :=
    Metric.closedBall 0 (max R 0)
  have hK : IsCompact K := isCompact_closedBall _ _
  have houtside (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ K) : R < ‖x‖ := by
    have hnot : ¬ ‖x‖ ≤ max R 0 := by
      intro hle
      apply hx
      simpa [K, Metric.mem_closedBall, dist_zero_right] using hle
    exact lt_of_le_of_lt (le_max_left R 0) (lt_of_not_ge hnot)
  have hdzero (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ K) : fderiv ℝ Φ (t, x) v = 0 := by
    rw [← hkey]
    have he : (fun s => ρ s x) = (fun _ => 0) := by
      funext s
      exact hs s x (houtside x hx)
    simp [he]
  have hΦcont (t : ℝ) : Continuous (ρ t) := by
    have hmap : Continuous (fun x : EuclideanSpace ℝ (Fin n) => (t, x)) :=
      continuous_const.prodMk continuous_id
    simpa [Φ, Function.comp_def] using hρ.continuous.comp hmap
  have hdcontslice (t : ℝ) :
      Continuous (fun x : EuclideanSpace ℝ (Fin n) => fderiv ℝ Φ (t, x) v) :=
    hdcont.comp (continuous_const.prodMk continuous_id)
  have hρcompact (t : ℝ) : HasCompactSupport (ρ t) := by
    apply HasCompactSupport.intro hK
    intro x hx; exact hs t x (houtside x hx)
  have hintegrable (t : ℝ) : MeasureTheory.Integrable (ρ t) :=
    (hΦcont t).integrable_of_hasCompactSupport (hρcompact t)
  let I : Set ℝ := Set.Icc (t₀ - 1) (t₀ + 1)
  have hI : I ∈ 𝓝 t₀ := by
    change Set.Icc (t₀ - 1) (t₀ + 1) ∈ 𝓝 t₀
    exact Icc_mem_nhds (by linarith) (by linarith)
  have hIK : IsCompact (I ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨C, hC⟩ := (hIK.image hdcont).isBounded.exists_norm_le
  have hbound : ∀ᵐ x ∂MeasureTheory.volume, ∀ t ∈ I, ‖fderiv ℝ Φ (t, x) v‖ ≤ K.indicator (fun _ => C) x := by
    apply Filter.Eventually.of_forall
    intro x t ht
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      exact hC _ ⟨(t, x), ⟨ht, hx⟩, rfl⟩
    · rw [Set.indicator_of_notMem hx, hdzero t x hx]
      simp
  have hboundint : MeasureTheory.Integrable (K.indicator (fun _ => C)) (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) := by
    exact (MeasureTheory.integrable_indicator_iff hK.measurableSet).mpr
      (MeasureTheory.integrableOn_const (hK.measure_lt_top).ne)
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (F := fun t x => ρ t x)
    (F' := fun t x => fderiv ℝ Φ (t, x) v)
    (s := I) (x₀ := t₀) (bound := K.indicator (fun _ => C))
    hI (Filter.Eventually.of_forall fun t => (hΦcont t).aestronglyMeasurable)
    (hintegrable t₀) (hdcontslice t₀).aestronglyMeasurable
    hbound hboundint
    (Filter.Eventually.of_forall fun x t _ => hslice t x)
  have hEq : (fun x : EuclideanSpace ℝ (Fin n) =>
      fderiv ℝ Φ (t₀, x) v) = (fun x => deriv (fun s => ρ s x) t₀) :=
    funext (fun x => (hkey t₀ x).symm)
  simpa only [hEq] using hres.2
private theorem mass_integral_directional_derivative_zero {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (v : EuclideanSpace ℝ (Fin n)) : (∫ x, fderiv ℝ f x v) = 0 := by
  have hd : MeasureTheory.Integrable (fun x => fderiv ℝ f x v) :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v)
  have hi : MeasureTheory.Integrable f := hf.continuous.integrable_of_hasCompactSupport hc
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun _ : EuclideanSpace ℝ (Fin n) => (1 : ℝ)) (g := f)
    (v := v) (μ := MeasureTheory.volume)
    (by simp) (by simpa using hd) (by simpa using hi)
    (fun _ _ => differentiableAt_const _)
    (fun x _ => (hf.differentiable one_ne_zero) x)
  simpa using hh
theorem solution {n : ℕ} (ρ : ℝ → EuclideanSpace ℝ (Fin n) → ℝ) (u : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hρ : ContDiff ℝ 1 (fun p : ℝ × EuclideanSpace ℝ (Fin n) => ρ p.1 p.2)) (hu : ContDiff ℝ 1 (fun p : ℝ × EuclideanSpace ℝ (Fin n) => u p.1 p.2)) (hsupp : ∃ R : ℝ, ∀ t x, R < ‖x‖ → ρ t x = 0) (hcont : ∀ t x, deriv (fun s => ρ s x) t + ∑ k : Fin n, fderiv ℝ (fun y => ρ t y * u t y k) x (EuclideanSpace.single k 1) = 0) : ∀ t s, ∫ x, ρ t x = ∫ x, ρ s x := by
  classical
  obtain ⟨R, hR⟩ := hsupp
  have hcompact (q : ℝ) : HasCompactSupport (ρ q) := by
    refine HasCompactSupport.intro
      (K := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (max R 0))
      (ProperSpace.isCompact_closedBall _ _) ?_
    intro y hy
    apply hR q y
    have hn : ¬ ‖y‖ ≤ max R 0 := by
      intro hn
      apply hy
      simpa [Metric.mem_closedBall, dist_zero_right] using hn
    exact lt_of_le_of_lt (le_max_left R 0) (lt_of_not_ge hn)
  have hmap (q : ℝ) :
      ContDiff ℝ 1 (fun y : EuclideanSpace ℝ (Fin n) => (q, y)) :=
    contDiff_const.prodMk contDiff_id
  have hρslice (q : ℝ) : ContDiff ℝ 1 (ρ q) := by
    simpa only [Function.comp_def] using hρ.comp (hmap q)
  have huslice (q : ℝ) : ContDiff ℝ 1 (u q) := by
    simpa only [Function.comp_def] using hu.comp (hmap q)
  have hflux_smooth (q : ℝ) (k : Fin n) : ContDiff ℝ 1 (fun y => ρ q y * u q y k) := by
    have hproj : ContDiff ℝ 1 (fun y : EuclideanSpace ℝ (Fin n) => (u q y) k) := by
      have hh : ContDiff ℝ 1 ((fun z : EuclideanSpace ℝ (Fin n) => z k) ∘ u q) :=
        (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp (huslice q)
      simpa only [Function.comp_def] using hh
    exact (hρslice q).mul hproj
  have hflux_compact (q : ℝ) (k : Fin n) :
      HasCompactSupport (fun y => ρ q y * u q y k) := by
    change HasCompactSupport ((ρ q) * fun y => u q y k)
    exact (hcompact q).mul_right
  have hflux_zero (q : ℝ) (k : Fin n) : (∫ y, fderiv ℝ (fun z => ρ q z * u q z k) y (EuclideanSpace.single k 1)) = 0 := by
    exact mass_integral_directional_derivative_zero
      (fun y => ρ q y * u q y k) (hflux_smooth q k)
      (hflux_compact q k) (EuclideanSpace.single k 1)
  have hflux_deriv_integrable (q : ℝ) (k : Fin n) : MeasureTheory.Integrable (fun y => fderiv ℝ (fun z => ρ q z * u q z k) y (EuclideanSpace.single k 1)) :=
    (((hflux_smooth q k).continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport ((hflux_compact q k).fderiv_apply ℝ (EuclideanSpace.single k 1))
  have hdivergence_zero (q : ℝ) : (∫ y, ∑ k : Fin n, fderiv ℝ (fun z => ρ q z * u q z k) y (EuclideanSpace.single k 1)) = 0 := by
    rw [MeasureTheory.integral_finsetSum _ (fun k _ => hflux_deriv_integrable q k)]
    simp only [hflux_zero, Finset.sum_const_zero]
  have htotal_time_deriv_zero (q : ℝ) : (∫ y, deriv (fun p => ρ p y) q) = 0 := by
    have hh (y : EuclideanSpace ℝ (Fin n)) : deriv (fun p => ρ p y) q = -(∑ k : Fin n, fderiv ℝ (fun z => ρ q z * u q z k) y (EuclideanSpace.single k 1)) := by
      linarith [hcont q y]
    simp_rw [hh]
    rw [MeasureTheory.integral_neg, hdivergence_zero]
    simp
  have hd (q : ℝ) : HasDerivAt (fun z => ∫ x, ρ z x) 0 q := by
    have hh := mass_time_integral_derivative ρ hρ R hR q
    simpa only [htotal_time_deriv_zero q] using hh
  intro t s; exact is_const_of_deriv_eq_zero
    (fun q => (hd q).differentiableAt) (fun q => (hd q).deriv) t s
