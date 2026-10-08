-- Prove2me | solution 1 for CosmoConstCentury.einstein_newtonian_limit_bounded_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:37:36.308745+00:00
-- url     : https://prove2.me/submissions/8a05ca3c-9cba-4588-8e0c-80f4fbdd7fa0

import Mathlib
import Definitions.Def_CosmoConstCentury_Defs

open Filter Topology

namespace P00f50d29

open CosmoConstCentury

lemma laplacian3_neg (φ : EuclideanSpace ℝ (Fin 3) → ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    laplacian3 (fun y => -φ y) x = -laplacian3 φ x := by
  have h1 : ∀ i : Fin 3, (fun y => fderiv ℝ (fun y => -φ y) y (EuclideanSpace.single i 1))
      = fun y => -(fderiv ℝ φ y (EuclideanSpace.single i 1)) := by
    intro i; funext y; rw [fderiv_fun_neg]; rfl
  simp only [laplacian3, h1]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_fun_neg]; rfl

lemma second_dir_le (φ : EuclideanSpace ℝ (Fin 3) → ℝ) (hφ : ContDiff ℝ 2 φ) (η : ℝ) (hη : 0 < η)
    (x : EuclideanSpace ℝ (Fin 3))
    (hmax : ∀ y, φ y - η * ‖y‖ ^ 2 ≤ φ x - η * ‖x‖ ^ 2)
    (e : EuclideanSpace ℝ (Fin 3)) (he : ‖e‖ = 1) :
    fderiv ℝ (fun y => fderiv ℝ φ y e) x e ≤ 4 * η := by
  by_contra hcon
  push Not at hcon
  have hd1 : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hC1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  have hd2 : Differentiable ℝ (fun y => fderiv ℝ φ y e) :=
    (hC1.clm_apply contDiff_const).differentiable (by norm_num)
  set a : ℝ := inner ℝ x e with ha
  let g : ℝ → ℝ := fun t => φ (x + t • e) - η * (2 * a * t + t ^ 2) - η * t ^ 2
  have hline : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • e) e t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const e).const_add x
  have hg' : ∀ t, HasDerivAt g (fderiv ℝ φ (x + t • e) e - η * (2 * a + 2 * t) - 2 * η * t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => φ (x + t • e)) (fderiv ℝ φ (x + t • e) e) t :=
      (hd1 (x + t • e)).hasFDerivAt.comp_hasDerivAt t (hline t)
    have h2 : HasDerivAt (fun t : ℝ => η * (2 * a * t + t ^ 2)) (η * (2 * a + 2 * t)) t := by
      have := (((hasDerivAt_id t).const_mul (2 * a)).add (hasDerivAt_pow 2 t)).const_mul η
      exact this.congr_deriv (by norm_num <;> ring)
    have h3 : HasDerivAt (fun t : ℝ => η * t ^ 2) (2 * η * t) t := by
      have := (hasDerivAt_pow 2 t).const_mul η
      exact this.congr_deriv (by norm_num <;> ring)
    exact (h1.sub h2).sub h3
  have hderiv : deriv g = fun t => fderiv ℝ φ (x + t • e) e - η * (2 * a + 2 * t) - 2 * η * t := by
    funext t; exact (hg' t).deriv
  have hg'' : HasDerivAt (deriv g) (fderiv ℝ (fun y => fderiv ℝ φ y e) x e - 4 * η) 0 := by
    rw [hderiv]
    have h1 := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (0:ℝ) (hd2 (x + (0:ℝ) • e)).hasFDerivAt (hline 0)
    simp only [zero_smul, add_zero, Function.comp_def] at h1
    have h2 : HasDerivAt (fun t : ℝ => η * (2 * a + 2 * t)) (η * 2) 0 := by
      have := (((hasDerivAt_id (0:ℝ)).const_mul 2).const_add (2 * a)).const_mul η
      exact this.congr_deriv (by norm_num <;> ring)
    have h3 : HasDerivAt (fun t : ℝ => 2 * η * t) (2 * η) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).const_mul (2 * η)
    exact ((h1.sub h2).sub h3).congr_deriv (by ring)
  -- g t ≤ g 0 - η t^2
  have hbound : ∀ t : ℝ, g t ≤ g 0 - η * t ^ 2 := by
    intro t
    have hm := hmax (x + t • e)
    have hn : ‖x + t • e‖ ^ 2 = ‖x‖ ^ 2 + 2 * a * t + t ^ 2 := by
      rw [norm_add_sq_real, norm_smul, he, real_inner_smul_right, ha]
      simp; ring
    simp only [g, zero_smul, add_zero, mul_zero, zero_pow two_ne_zero]
    rw [hn] at hm
    nlinarith
  have hmaxg : IsLocalMax g 0 := Filter.Eventually.of_forall fun t => by
    have := hbound t; nlinarith [sq_nonneg t]
  have hd0 : deriv g 0 = 0 := hmaxg.deriv_eq_zero
  have hmin : IsLocalMin g 0 :=
    isLocalMin_of_deriv_deriv_pos (by rw [hg''.deriv]; linarith) hd0 (hg' 0).continuousAt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hmin
  have ht : dist (ε / 2) (0:ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith
  have h1 := hball ht
  have h2 := hbound (ε / 2)
  have : 0 < η * (ε / 2) ^ 2 := by positivity
  linarith

lemma key (φ : EuclideanSpace ℝ (Fin 3) → ℝ) (hφ : ContDiff ℝ 2 φ) (M : ℝ)
    (hM : ∀ x, φ x ≤ M) (k : ℝ) (hk : 0 < k) (hΔ : ∀ x, laplacian3 φ x = k) : False := by
  set η : ℝ := k / 24 with hηdef
  have hη : 0 < η := by positivity
  have hcont : Continuous fun y : EuclideanSpace ℝ (Fin 3) => φ y - η * ‖y‖ ^ 2 :=
    hφ.continuous.sub (continuous_const.mul (continuous_norm.pow 2))
  have hlim : Tendsto (fun y : EuclideanSpace ℝ (Fin 3) => φ y - η * ‖y‖ ^ 2)
      (cocompact _) atBot := by
    have h1 : Tendsto (fun y : EuclideanSpace ℝ (Fin 3) => M - η * ‖y‖ ^ 2) (cocompact _) atBot := by
      have := ((tendsto_pow_atTop (two_ne_zero)).comp (tendsto_norm_cocompact_atTop (E := EuclideanSpace ℝ (Fin 3)))).const_mul_atTop hη
      have := tendsto_atBot_add_const_left _ M (tendsto_neg_atTop_atBot.comp this)
      refine this.congr fun y => ?_
      simp [Function.comp]; ring
    refine tendsto_atBot_mono (fun y => ?_) h1
    have := hM y; linarith
  obtain ⟨x, hx⟩ := hcont.exists_forall_ge hlim
  have hle : ∀ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1) ≤ 4 * η := fun i =>
    second_dir_le φ hφ η hη x hx _ (by simp)
  have hsum : laplacian3 φ x ≤ ∑ _i : Fin 3, 4 * η := Finset.sum_le_sum fun i _ => hle i
  rw [hΔ x] at hsum
  simp at hsum
  linarith

end P00f50d29

open CosmoConstCentury in
theorem solution (G c Λ ρ : ℝ) :
    (∃ φ : EuclideanSpace ℝ (Fin 3) → ℝ, ContDiff ℝ 2 φ ∧ (∃ M : ℝ, ∀ x, |φ x| ≤ M) ∧
      ∀ x, laplacian3 φ x + c ^ 2 * Λ = 4 * Real.pi * G * ρ) ↔
    c ^ 2 * Λ = 4 * Real.pi * G * ρ := by
  constructor
  · rintro ⟨φ, hφ, ⟨M, hM⟩, hΔ⟩
    set k := 4 * Real.pi * G * ρ - c ^ 2 * Λ with hk
    have hΔ' : ∀ x, CosmoConstCentury.laplacian3 φ x = k := fun x => by
      have := hΔ x; linarith
    rcases lt_trichotomy k 0 with h | h | h
    · exfalso
      refine P00f50d29.key (fun y => -φ y) hφ.neg M (fun x => ?_) (-k) (by linarith) (fun x => ?_)
      · have := (abs_le.mp (hM x)).1; linarith
      · rw [P00f50d29.laplacian3_neg, hΔ' x]
    · linarith
    · exact (P00f50d29.key φ hφ M (fun x => (abs_le.mp (hM x)).2) k h hΔ').elim
  · intro h
    refine ⟨fun _ => 0, contDiff_const, ⟨0, fun x => by simp⟩, fun x => ?_⟩
    simp [CosmoConstCentury.laplacian3, h]
