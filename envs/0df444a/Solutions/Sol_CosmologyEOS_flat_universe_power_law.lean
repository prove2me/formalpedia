-- Prove2me | solution 1 for CosmologyEOS.flat_universe_power_law
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:28:21.427135+00:00
-- url     : https://prove2.me/submissions/2fb9d350-fd6c-4f7f-978b-081d9fde5cad

import Mathlib
import Definitions.Def_CosmologyEOS_Defs

open Real Filter Topology
open CosmologyEOS

namespace LUCore

theorem scale_core (I : Set ℝ) (hI : IsOpen I) (hIc : IsPreconnected I) (a ε : ℝ → ℝ) (k : ℝ)
    (ha : ∀ t ∈ I, DifferentiableAt ℝ a t) (hε : ∀ t ∈ I, DifferentiableAt ℝ ε t)
    (hpos : ∀ t ∈ I, 0 < a t)
    (hode : ∀ t ∈ I, deriv ε t = -k * (deriv a t / a t) * ε t) :
    ∀ s ∈ I, ∀ t ∈ I, ε t * a t ^ k = ε s * a s ^ k := by
  have hd : ∀ t ∈ I, HasDerivAt (fun t => ε t * a t ^ k) 0 t := by
    intro t ht
    have h1 : HasDerivAt (fun t => ε t * a t ^ k)
        (deriv ε t * a t ^ k + ε t * (deriv a t * k * a t ^ (k - 1))) t :=
      (hε t ht).hasDerivAt.mul ((ha t ht).hasDerivAt.rpow_const (p := k)
        (Or.inl (hpos t ht).ne'))
    refine h1.congr_deriv ?_
    rw [hode t ht, Real.rpow_sub_one (hpos t ht).ne']
    have := (hpos t ht).ne'
    field_simp
    ring
  intro s hs t ht
  exact hI.is_const_of_deriv_eq_zero hIc (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hd x hx).deriv) ht hs

end LUCore

theorem solution (G w : ℝ) (hG : 0 < G) (hw : -1 < w) (a ε p : ℝ → ℝ)
    (ha_diff : ∀ t > 0, DifferentiableAt ℝ a t)
    (hε_diff : ∀ t > 0, DifferentiableAt ℝ ε t)
    (ha_pos : ∀ t > 0, 0 < a t)
    (heos : ∀ t > 0, p t = w * ε t)
    (hfluid : ∀ t > 0, FluidEquation a ε p t)
    (hfried : ∀ t > 0, FlatFriedmannEquation G a ε t)
    (hbang : Tendsto a (𝓝[>] 0) (𝓝 0)) :
    ∃ C > 0, ∀ t > 0, a t = C * t ^ (2 / (3 * (1 + w))) := by
  set n := 3 * (1 + w) with hn
  have hnpos : 0 < n := by rw [hn]; linarith
  set m := n / 2 with hm
  have hmpos : 0 < m := by rw [hm]; linarith
  have hK := LUCore.scale_core (Set.Ioi 0) isOpen_Ioi isPreconnected_Ioi a ε n
    ha_diff hε_diff ha_pos (fun t ht => by rw [hfluid t ht, heos t ht]; ring)
  set B : ℝ → ℝ := fun t => a t ^ m with hB
  have hBd : ∀ t > 0, HasDerivAt B (deriv a t * m * a t ^ (m - 1)) t := fun t ht =>
    (ha_diff t ht).hasDerivAt.rpow_const (Or.inl (ha_pos t ht).ne')
  set g : ℝ → ℝ := fun t => deriv a t * m * a t ^ (m - 1) with hg
  have hgsq : ∀ t > 0, g t ^ 2 = m ^ 2 * (8 * π * G / 3) * (ε 1 * a 1 ^ n) := by
    intro t ht
    have hat := ha_pos t ht
    rw [← hK 1 (by norm_num : (1:ℝ) ∈ Set.Ioi 0) t ht]
    have hf := hfried t ht
    unfold FlatFriedmannEquation at hf
    have e1 : a t ^ (m - 1) = a t ^ m / a t := Real.rpow_sub_one hat.ne' m
    have e2 : a t ^ n = a t ^ m * a t ^ m := by
      rw [← Real.rpow_add hat]; congr 1; rw [hm]; ring
    simp only [hg]
    rw [e1, e2]
    have : g t = m * a t ^ m * (deriv a t / a t) := by
      simp only [hg]; rw [e1]; field_simp
    calc (deriv a t * m * (a t ^ m / a t)) ^ 2 = m ^ 2 * (a t ^ m) ^ 2 * (deriv a t / a t) ^ 2 := by
          field_simp
      _ = _ := by rw [hf]; ring
  set s := g 1 with hs
  have hconst : ∀ t > 0, g t = s := by
    intro t ht
    have h2 : g t ^ 2 = s ^ 2 := by rw [hs, hgsq t ht, hgsq 1 (by norm_num)]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
    · exact h
    · by_cases hs0 : s = 0
      · rw [h, hs0, neg_zero]
      exfalso
      have hoc : Set.OrdConnected (deriv B '' Set.Ioi 0) :=
        Set.OrdConnected.image_deriv Set.ordConnected_Ioi
          (fun x hx => (hBd x hx).differentiableAt)
      have hm1 : g t ∈ deriv B '' Set.Ioi 0 := ⟨t, ht, (hBd t ht).deriv⟩
      have hm2 : s ∈ deriv B '' Set.Ioi 0 := ⟨1, by norm_num, (hBd 1 (by norm_num)).deriv⟩
      have h0 : (0:ℝ) ∈ Set.uIcc (g t) s := by
        rw [h, Set.mem_uIcc]
        rcases lt_or_gt_of_ne hs0 with hh | hh
        · right; constructor <;> linarith
        · left; constructor <;> linarith
      obtain ⟨u, hu, hu0⟩ := hoc.uIcc_subset hm1 hm2 h0
      rw [(hBd u hu).deriv] at hu0
      have h3 := hgsq u hu
      have h4 := hgsq 1 (by norm_num)
      simp only [hg] at h3
      rw [hu0] at h3
      apply hs0
      have : s ^ 2 = 0 := by rw [hs, h4, ← h3]; ring
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  have hlin : ∀ t > 0, B t - s * t = B 1 - s * 1 := by
    intro t ht
    have hd : ∀ x ∈ Set.Ioi (0:ℝ), HasDerivAt (fun t => B t - s * t) (g x - s * 1) x :=
      fun x hx => (hBd x hx).sub ((hasDerivAt_id x).const_mul s)
    exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
      (fun x hx => by simp only [Pi.zero_apply]; rw [(hd x hx).deriv, hconst x hx]; ring)
      ht (by norm_num : (1:ℝ) ∈ Set.Ioi 0)
  set D := B 1 - s * 1 with hD
  have hD0 : D = 0 := by
    have t1 : Tendsto B (𝓝[>] 0) (𝓝 0) := by
      have := hbang.rpow_const (p := m) (Or.inr hmpos.le)
      rwa [Real.zero_rpow hmpos.ne'] at this
    have t2 : Tendsto B (𝓝[>] 0) (𝓝 (s * 0 + D)) := by
      have : Tendsto (fun t : ℝ => s * t + D) (𝓝[>] 0) (𝓝 (s * 0 + D)) :=
        ((continuous_const.mul continuous_id).add continuous_const).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
      apply this.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      have := hlin t ht
      linarith
    have := tendsto_nhds_unique t1 t2
    linarith
  have hBt : ∀ t > 0, B t = s * t := fun t ht => by have := hlin t ht; linarith
  have hspos : 0 < s := by
    have := hBt 1 (by norm_num)
    have : 0 < B 1 := Real.rpow_pos_of_pos (ha_pos 1 (by norm_num)) _
    linarith
  refine ⟨s ^ m⁻¹, Real.rpow_pos_of_pos hspos _, fun t ht => ?_⟩
  have e : (2 / (3 * (1 + w))) = m⁻¹ := by rw [hm, hn]; field_simp
  rw [e, ← Real.mul_rpow hspos.le (le_of_lt ht), ← hBt t ht, hB]
  exact (Real.rpow_rpow_inv (ha_pos t ht).le hmpos.ne').symm
