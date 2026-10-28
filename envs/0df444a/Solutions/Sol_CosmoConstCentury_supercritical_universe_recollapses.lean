-- Prove2me | solution 1 for CosmoConstCentury.supercritical_universe_recollapses
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T11:49:37.615499+00:00
-- url     : https://prove2.me/submissions/67f553bd-14ef-4026-b7c4-9327b27813b6

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology
open CosmoConstCentury

namespace S214CC

lemma anti (t₀ : ℝ) (f f' : ℝ → ℝ) (hf : ∀ t, t₀ ≤ t → HasDerivAt f (f' t) t)
    (hneg : ∀ t, t₀ ≤ t → f' t ≤ 0) : AntitoneOn f (Set.Ici t₀) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici t₀)
  · exact fun t ht => (hf t ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    exact (hf t (le_of_lt ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    rw [(hf t (le_of_lt ht)).deriv]
    exact hneg t (le_of_lt ht)

end S214CC

theorem solution (G c k t₀ : ℝ) (hG : 0 < G) (hc : 0 < c)
    (R ρ : ℝ → ℝ) (hsuper : criticalDensity G (hubbleParam R t₀) < ρ t₀) :
    ¬ IsFriedmannSolution G c 0 k (Set.Ici t₀) R ρ := by
  intro hF
  have hpos : ∀ t, t₀ ≤ t → 0 < R t := fun t ht => (hF t ht).1
  have hcd : ∀ t, t₀ ≤ t → ContDiffAt ℝ 2 R t := fun t ht => (hF t ht).2.1
  have e15 := (hF t₀ (Set.mem_Ici.mpr le_rfl)).2.2.1
  have e16 : ∀ t, t₀ ≤ t → deriv R t ^ 2 / R t ^ 2 + 2 * deriv (deriv R) t / R t +
      k * c ^ 2 / R t ^ 2 - 0 = 0 := fun t ht => (hF t ht).2.2.2
  have hdR : ∀ t, t₀ ≤ t → HasDerivAt R (deriv R t) t := fun t ht =>
    ((hcd t ht).differentiableAt (by norm_num)).hasDerivAt
  have hdR' : ∀ t, t₀ ≤ t → HasDerivAt (deriv R) (deriv (deriv R) t) t := by
    intro t ht
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ R) t := (hcd t ht).fderiv_right (m := 1) (by norm_num)
    have h2 : ContDiffAt ℝ 1 (fun x => fderiv ℝ R x 1) t := h1.clm_apply contDiffAt_const
    exact (h2.differentiableAt (by norm_num)).hasDerivAt
  have ode : ∀ t, t₀ ≤ t →
      deriv R t ^ 2 + 2 * R t * deriv (deriv R) t + k * c ^ 2 = 0 := by
    intro t ht
    have h := e16 t ht
    have hR := (hpos t ht).ne'
    field_simp at h
    linarith
  have hk : 0 < k := by
    have hR := hpos t₀ le_rfl
    have hκ : einsteinKappa G c * c ^ 2 = 8 * Real.pi * G := by
      unfold einsteinKappa; field_simp
    rw [hκ] at e15
    unfold criticalDensity hubbleParam at hsuper
    have hπG : 0 < 8 * Real.pi * G := by positivity
    rw [div_lt_iff₀ hπG] at hsuper
    have : 3 * k * c ^ 2 / R t₀ ^ 2 > 0 := by
      have h3 : 3 * (deriv R t₀ / R t₀) ^ 2 = 3 * deriv R t₀ ^ 2 / R t₀ ^ 2 := by
        field_simp
      nlinarith
    have hc2 : 0 < c ^ 2 := by positivity
    by_contra hk
    push Not at hk
    have : 3 * k * c ^ 2 / R t₀ ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)
    linarith
  set a := k * c ^ 2 with ha
  have ha0 : 0 < a := by positivity
  set E : ℝ → ℝ := fun t => R t * deriv R t ^ 2 + a * R t with hE
  have hEanti : AntitoneOn E (Set.Ici t₀) := by
    refine S214CC.anti t₀ E (fun t => deriv R t * (deriv R t ^ 2 + 2 * R t *
      deriv (deriv R) t + a)) (fun t ht => ?_) (fun t ht => by rw [ode t ht, mul_zero])
    have h := ((hdR t ht).mul ((hdR' t ht).pow 2)).add ((hdR t ht).const_mul a)
    exact h.congr_deriv (by simp only [Pi.pow_apply]; push_cast; ring)
  set M := E t₀ / a with hM
  have hRle : ∀ t, t₀ ≤ t → R t ≤ M := by
    intro t ht
    have h := hEanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    simp only [hE] at h
    rw [hM, le_div_iff₀ ha0]
    have : 0 ≤ R t * deriv R t ^ 2 := mul_nonneg (hpos t ht).le (sq_nonneg _)
    simp only [hE]; nlinarith
  have hM0 : 0 < M := lt_of_lt_of_le (hpos t₀ le_rfl) (hRle t₀ le_rfl)
  set b := a / (2 * M) with hb
  have hb0 : 0 < b := by positivity
  have hR'' : ∀ t, t₀ ≤ t → deriv (deriv R) t ≤ -b := by
    intro t ht
    have hR := hpos t ht
    have h := ode t ht
    have h1 : 2 * R t * deriv (deriv R) t ≤ -a := by nlinarith [sq_nonneg (deriv R t)]
    have h2 : b * (2 * R t) ≤ a := by
      rw [hb, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [hRle t ht]
    nlinarith
  have hg : AntitoneOn (fun t => deriv R t + b * t) (Set.Ici t₀) :=
    S214CC.anti t₀ _ (fun t => deriv (deriv R) t + b) (fun t ht => (hdR' t ht).add
      ((hasDerivAt_id t).const_mul b |>.congr_deriv (by ring)))
      (fun t ht => by linarith [hR'' t ht])
  have hh : AntitoneOn (fun t => R t - deriv R t₀ * t + b * (t - t₀) ^ 2 / 2) (Set.Ici t₀) := by
    refine S214CC.anti t₀ _ (fun t => (deriv R t + b * t) - (deriv R t₀ + b * t₀))
      (fun t ht => ?_) (fun t ht => ?_)
    · have h1 := (hdR t ht).sub ((hasDerivAt_id t).const_mul (deriv R t₀))
      have h2 := (((hasDerivAt_id t).sub_const t₀).pow 2).const_mul b |>.div_const 2
      exact (h1.add h2).congr_deriv (by simp only [id]; push_cast; ring)
    · have := hg (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
      simp only at this; linarith
  set T := 2 * (R t₀ + |deriv R t₀|) / b + 1 with hT
  have hT1 : 1 ≤ T := by
    have : 0 ≤ 2 * (R t₀ + |deriv R t₀|) / b := by
      apply div_nonneg _ hb0.le
      have := hpos t₀ le_rfl; positivity
    linarith
  have hTb : 2 * (R t₀ + |deriv R t₀|) ≤ b * T := by
    have e : b * (2 * (R t₀ + |deriv R t₀|) / b) = 2 * (R t₀ + |deriv R t₀|) := by
      field_simp
    rw [hT, mul_add b, e, mul_one]; linarith
  have key := hh (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (by linarith : t₀ ≤ t₀ + T))
    (by linarith)
  simp only [sub_self] at key
  have hRT := hpos (t₀ + T) (by linarith)
  have habs : -|deriv R t₀| ≤ deriv R t₀ := neg_abs_le _
  have habs2 : deriv R t₀ ≤ |deriv R t₀| := le_abs_self _
  have hR0 := hpos t₀ le_rfl
  nlinarith [mul_le_mul_of_nonneg_left hTb (by linarith : (0:ℝ) ≤ T)]
