-- Prove2me | solution 1 for DynMomentum.ShortHorizon.eq_A13_A2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-27T03:04:40.050273+00:00
-- url     : https://prove2.me/submissions/2382dd10-feda-4eee-81db-bf17e35aa85b

import Mathlib
import Definitions.Def_DynMomentum_ShortHorizon_Model

open DynMomentum.ShortHorizon in
theorem solution (P : Params) (hP : P.Standing) (T : ℝ) (hT0 : 0 ≤ T) (hTτ : T ≤ P.τ)
    (s : ℝ → ℝ) (hs : ContinuousOn s (Set.Icc (-P.τ) 0)) (A1 : ℝ → ℝ)
    (hA1 : ∀ u ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt A1 (rhs1 P (A1 u)) (Set.Icc 0 T) u) :
    let A2 : ℝ → ℝ := fun t => ∫ u in t..T,
      Real.exp (∫ v in t..u, (P.σ ^ 2 * A1 v + P.α / (P.γ * P.τ)))
        * (((P.r - P.σ ^ 2 / 2) * (1 - P.α / P.γ) + (1 - P.α) * P.μ / P.γ
              - P.α / (P.γ * P.τ) * s (u - P.τ)) * A1 u
          + (1 - P.γ) / P.γ ^ 2 * (P.α / (P.σ ^ 2 * P.τ))
              * ((1 - P.α) * P.μ - P.α * (P.r - P.σ ^ 2 / 2) - P.α / P.τ * s (u - P.τ)))
    (∀ t ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt A2 (rhs2 P s t (A1 t) (A2 t)) (Set.Icc 0 T) t) ∧
      A2 T = 0 := by
  intro A2
  obtain ⟨hα0, hα1, hσ, hτ, hγ⟩ := hP
  have hτ0 : -P.τ ≤ 0 := by linarith
  have hA1c : ContinuousOn A1 (Set.Icc 0 T) := fun u hu => (hA1 u hu).continuousWithinAt
  set a : ℝ → ℝ := Set.IccExtend hT0 (fun x : Set.Icc (0 : ℝ) T => A1 x) with ha
  have hac : Continuous a := continuous_IccExtend_iff.mpr hA1c.restrict
  have haeq : ∀ v ∈ Set.Icc (0 : ℝ) T, a v = A1 v := fun v hv => Set.IccExtend_of_mem _ _ hv
  set sb : ℝ → ℝ := Set.IccExtend hτ0 (fun x : Set.Icc (-P.τ) 0 => s x) with hsb
  have hsbc : Continuous sb := continuous_IccExtend_iff.mpr hs.restrict
  have hsbeq : ∀ u ∈ Set.Icc (0 : ℝ) T, sb (u - P.τ) = s (u - P.τ) := fun u hu =>
    Set.IccExtend_of_mem _ _ ⟨by linarith [hu.1], by linarith [hu.2]⟩
  set g : ℝ → ℝ := fun v => P.σ ^ 2 * a v + P.α / (P.γ * P.τ) with hg
  set h : ℝ → ℝ := fun u => ((P.r - P.σ ^ 2 / 2) * (1 - P.α / P.γ) + (1 - P.α) * P.μ / P.γ
              - P.α / (P.γ * P.τ) * sb (u - P.τ)) * a u
          + (1 - P.γ) / P.γ ^ 2 * (P.α / (P.σ ^ 2 * P.τ))
              * ((1 - P.α) * P.μ - P.α * (P.r - P.σ ^ 2 / 2) - P.α / P.τ * sb (u - P.τ)) with hh
  have hgc : Continuous g := by simp only [hg]; fun_prop
  have hhc : Continuous h := by simp only [hh]; fun_prop
  set B : ℝ → ℝ := fun t => ∫ u in t..T, Real.exp (∫ v in t..u, g v) * h u with hB
  have hAB : ∀ t ∈ Set.Icc (0 : ℝ) T, A2 t = B t := by
    intro t ht
    simp only [A2, hB]
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hu' : u ∈ Set.Icc (0 : ℝ) T := by
      rw [Set.uIcc_of_le ht.2] at hu
      exact ⟨le_trans ht.1 hu.1, hu.2⟩
    have hin : ∫ v in t..u, (P.σ ^ 2 * A1 v + P.α / (P.γ * P.τ)) = ∫ v in t..u, g v := by
      refine intervalIntegral.integral_congr fun v hv => ?_
      have hv' : v ∈ Set.Icc (0 : ℝ) T := by
        rcases le_total t u with h1 | h1
        · rw [Set.uIcc_of_le h1] at hv; exact ⟨le_trans ht.1 hv.1, le_trans hv.2 hu'.2⟩
        · rw [Set.uIcc_of_ge h1] at hv; exact ⟨le_trans hu'.1 hv.1, le_trans hv.2 ht.2⟩
      simp only [hg, haeq v hv']
    simp only [hin, hh, haeq u hu', hsbeq u hu']
  set G : ℝ → ℝ := fun t => ∫ v in (0 : ℝ)..t, g v with hG
  have hGd : ∀ t, HasDerivAt G (g t) t := fun t =>
    (hgc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hGc : Continuous G := continuous_iff_continuousAt.mpr fun t => (hGd t).continuousAt
  set k : ℝ → ℝ := fun u => Real.exp (G u) * h u with hk
  have hkc : Continuous k := by simp only [hk]; fun_prop
  have hBe : ∀ t, B t = Real.exp (-G t) * ∫ u in t..T, k u := by
    intro t
    simp only [hB, hk]
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    have : ∫ v in t..u, g v = G u - G t := by
      simp only [hG]
      exact (intervalIntegral.integral_interval_sub_left (hgc.intervalIntegrable 0 u)
        (hgc.intervalIntegrable 0 t)).symm
    rw [this, sub_eq_neg_add, Real.exp_add]
    ring
  have hKd : ∀ t, HasDerivAt (fun t => ∫ u in t..T, k u) (-k t) t := by
    intro t
    have h1 := (hkc.integral_hasStrictDerivAt T t).hasDerivAt.neg
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
    show ∫ u in x..T, k u = -∫ u in T..x, k u
    rw [intervalIntegral.integral_symm]
  have hBd : ∀ t, HasDerivAt B (-(g t) * B t - h t) t := by
    intro t
    have hE : HasDerivAt (fun t => Real.exp (-G t)) (Real.exp (-G t) * (-(g t))) t :=
      ((hGd t).neg).exp
    have := hE.mul (hKd t)
    have hfun : B = fun t => Real.exp (-G t) * ∫ u in t..T, k u := funext hBe
    rw [hfun]
    refine this.congr_deriv ?_
    simp only [hk]
    have : Real.exp (-G t) * Real.exp (G t) = 1 := by rw [← Real.exp_add]; simp
    linear_combination (-(h t)) * this
  refine ⟨fun t ht => ?_, ?_⟩
  · have hd := (hBd t).hasDerivWithinAt (s := Set.Icc 0 T)
    have hval : rhs2 P s t (A1 t) (A2 t) = -(g t) * B t - h t := by
      unfold rhs2
      simp only [hg, hh, haeq t ht, hsbeq t ht, hAB t ht]
      ring
    rw [hval]
    exact hd.congr_of_mem (fun x hx => hAB x hx) ht
  · simp [A2]
