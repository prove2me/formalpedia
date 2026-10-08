-- Prove2me | solution 1 for CosmoConstCentury.einstein_de_sitter_age
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:42:43.846534+00:00
-- url     : https://prove2.me/submissions/34a9d611-7a44-4967-8acd-398ad4f01d59

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology

open Filter Topology CosmoConstCentury in
theorem solution (G c : ℝ) (R ρ : ℝ → ℝ)
    (hsol : IsFriedmannSolution G c 0 0 (Set.Ioi 0) R ρ)
    (hexp : ∀ t > 0, 0 < deriv R t) (hbang : Tendsto R (𝓝[>] 0) (𝓝 0)) :
    ∀ t > 0, t = 2 / (3 * hubbleParam R t) := by
  have hpos : ∀ t > (0:ℝ), 0 < R t := fun t ht => (hsol t ht).1
  have hd1 : ∀ t > (0:ℝ), DifferentiableAt ℝ R t := fun t ht =>
    ((hsol t ht).2.1).differentiableAt (by norm_num)
  have hd2 : ∀ t > (0:ℝ), DifferentiableAt ℝ (deriv R) t := fun t ht =>
    (((hsol t ht).2.1).derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : ∀ t > (0:ℝ), deriv R t ^ 2 + 2 * R t * deriv (deriv R) t = 0 := by
    intro t ht
    have h := (hsol t ht).2.2.2
    have hr := (hpos t ht).ne'
    field_simp at h
    linear_combination h
  have hsqd : ∀ t > (0:ℝ), HasDerivAt (fun s => Real.sqrt (R s))
      (deriv R t / (2 * Real.sqrt (R t))) t := fun t ht =>
    (hd1 t ht).hasDerivAt.sqrt (hpos t ht).ne'
  let w : ℝ → ℝ := fun t => Real.sqrt (R t) * deriv R t
  have hwd : ∀ t > (0:ℝ), HasDerivAt w ((deriv R t / (2 * Real.sqrt (R t))) * deriv R t
      + Real.sqrt (R t) * deriv (deriv R) t) t := fun t ht =>
    (hsqd t ht).mul (hd2 t ht).hasDerivAt
  have hw0 : ∀ t > (0:ℝ), deriv w t = 0 := by
    intro t ht
    rw [(hwd t ht).deriv]
    have hs : 0 < Real.sqrt (R t) := Real.sqrt_pos.2 (hpos t ht)
    have hsq : Real.sqrt (R t) ^ 2 = R t := Real.sq_sqrt (hpos t ht).le
    field_simp
    linear_combination heq t ht + 2 * deriv (deriv R) t * hsq
  have hwc : ∀ t > (0:ℝ), w t = w 1 := by
    intro t ht
    exact isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0:ℝ)).isPreconnected
      (fun s hs => (hwd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => hw0 s hs) ht (by norm_num : (1:ℝ) ∈ Set.Ioi 0)
  obtain ⟨a, ha⟩ : ∃ a, a = w 1 := ⟨_, rfl⟩
  have hwc' : ∀ t > (0:ℝ), Real.sqrt (R t) * deriv R t = a := fun t ht => by
    rw [ha]; exact hwc t ht
  let g : ℝ → ℝ := fun t => R t * Real.sqrt (R t) - 3 / 2 * a * t
  have hgd : ∀ t > (0:ℝ), HasDerivAt g (deriv R t * Real.sqrt (R t)
      + R t * (deriv R t / (2 * Real.sqrt (R t))) - 3 / 2 * a) t := by
    intro t ht
    have h := ((hd1 t ht).hasDerivAt.mul (hsqd t ht)).sub
      ((hasDerivAt_id t).const_mul (3 / 2 * a))
    exact h.congr_deriv (by ring)
  have hg0 : ∀ t > (0:ℝ), deriv g t = 0 := by
    intro t ht
    rw [(hgd t ht).deriv]
    have hs : 0 < Real.sqrt (R t) := Real.sqrt_pos.2 (hpos t ht)
    have hsq : Real.sqrt (R t) ^ 2 = R t := Real.sq_sqrt (hpos t ht).le
    have hwt : Real.sqrt (R t) * deriv R t = a := hwc' t ht
    field_simp
    linear_combination -(deriv R t) * hsq + 3 * Real.sqrt (R t) * hwt
  have hgc : ∀ t > (0:ℝ), ∀ s > (0:ℝ), g s = g t := by
    intro t ht s hs
    exact isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0:ℝ)).isPreconnected
      (fun s hs => (hgd s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => hg0 s hs) hs ht
  have hlim : Tendsto g (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun s => Real.sqrt (R s)) (𝓝[>] 0) (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp hbang
      simpa [Function.comp_def] using this
    have h2 : Tendsto (fun s : ℝ => 3 / 2 * a * s) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun s : ℝ => 3 / 2 * a * s) (𝓝 0) (𝓝 (3 / 2 * a * 0)) :=
        ((continuous_const.mul continuous_id).tendsto 0)
      simpa using tendsto_nhdsWithin_of_tendsto_nhds this
    have := (hbang.mul h1).sub h2
    simpa using this
  intro t ht
  have hgt : g t = 0 := by
    have hc : Tendsto g (𝓝[>] 0) (𝓝 (g t)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (hgc t ht s hs).symm
    exact tendsto_nhds_unique hc hlim
  have hs : 0 < Real.sqrt (R t) := Real.sqrt_pos.2 (hpos t ht)
  have hwt : Real.sqrt (R t) * deriv R t = a := hwc' t ht
  have hr := hpos t ht
  have hd := hexp t ht
  have key : R t = 3 / 2 * deriv R t * t := by
    have : Real.sqrt (R t) * (R t - 3 / 2 * deriv R t * t) = 0 := by
      have hg : R t * Real.sqrt (R t) - 3 / 2 * a * t = 0 := hgt
      rw [← hwt] at hg
      linear_combination hg
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hs.ne'
    · linarith
  unfold hubbleParam
  rw [key]
  field_simp
