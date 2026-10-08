-- Prove2me | solution 1 for BeckTeboulleMD.EMDA.theorem_4_1_a
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T07:43:45.327032+00:00
-- url     : https://prove2.me/submissions/5ad0c843-dbe7-4daa-a13f-3e9a42cf018c

import Mathlib
import Definitions.Def_BeckTeboulleMD_EMDA_Setting

set_option autoImplicit false

namespace P800dbdb5

open Filter Topology BeckTeboulleMD.EMDA

lemma slope_nonneg (F : ℝ → ℝ) (d : ℝ) (hF : HasDerivAt F d 0)
    (hpos : ∀ s : ℝ, 0 < s → s < 1 → F 0 ≤ F s) : 0 ≤ d := by
  have h := hF.tendsto_slope_zero_right
  apply ge_of_tendsto h
  have : Set.Ioo (0:ℝ) 1 ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT one_pos
  filter_upwards [this] with s hs
  simp only [zero_add, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.2 hs.1.le) (sub_nonneg.2 (hpos s hs.1 hs.2))

lemma line_deriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : E → ℝ) (m v : E) (h : DifferentiableAt ℝ ψ m) :
    HasDerivAt (fun s : ℝ => ψ (m + s • v)) (fderiv ℝ ψ m v) 0 := by
  have h1 : HasDerivAt (fun s : ℝ => m + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add m
  have h2 : HasFDerivAt ψ (fderiv ℝ ψ m) (m + (0:ℝ) • v) := by simpa using h.hasFDerivAt
  exact h2.comp_hasDerivAt (0:ℝ) h1

lemma bregman_lb {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (ψ : E → ℝ) (σ : ℝ) (hψ : StrongConvexOn X σ ψ)
    (x y : E) (hx : x ∈ X) (hy : y ∈ X) (hd : DifferentiableAt ℝ ψ x) :
    σ / 2 * ‖y - x‖ ^ 2 ≤ bregman ψ y x := by
  set c : ℝ := σ / 2 * ‖x - y‖ ^ 2 with hc
  set A : ℝ := ψ y - ψ x - c with hA
  let F : ℝ → ℝ := fun s => ψ x + s * A + s ^ 2 * c - ψ (x + s • (y - x))
  have hF : HasDerivAt F (A + 0 - fderiv ℝ ψ x (y - x)) 0 := by
    have e1 : HasDerivAt (fun s : ℝ => s * A) A 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).mul_const A
    have e2 : HasDerivAt (fun s : ℝ => s ^ 2 * c) 0 0 := by
      simpa using (hasDerivAt_pow 2 (0:ℝ)).mul_const c
    have := (((e1.const_add (ψ x)).add e2).sub (line_deriv ψ x (y - x) hd))
    exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by
      simp only [F, Pi.add_apply, Pi.sub_apply])
  have hpos : ∀ s : ℝ, 0 < s → s < 1 → F 0 ≤ F s := by
    intro s hs0 hs1
    have key := hψ.2 hx hy (show (0:ℝ) ≤ 1 - s by linarith) hs0.le (show 1 - s + s = 1 by ring)
    have hpt : (1 - s) • x + s • y = x + s • (y - x) := by module
    rw [hpt] at key
    simp only [smul_eq_mul] at key
    simp only [F, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, zero_smul, add_zero]
    rw [hA]
    nlinarith [key]
  have := slope_nonneg F _ hF hpos
  unfold bregman
  rw [norm_sub_rev]
  linarith

lemma first_order {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (ψ : E → ℝ) (l : E →L[ℝ] ℝ) (tk : ℝ)
    (xk m u : E) (hm : m ∈ X) (hu : u ∈ X) (hdm : DifferentiableAt ℝ ψ m)
    (hmin : ∀ w ∈ X, l m + (1 / tk) * bregman ψ m xk ≤ l w + (1 / tk) * bregman ψ w xk) :
    0 ≤ l (u - m) + (1 / tk) * (fderiv ℝ ψ m (u - m) - fderiv ℝ ψ xk (u - m)) := by
  set v := u - m with hv
  let F : ℝ → ℝ := fun s => l m + s * l v + (1 / tk) * (ψ (m + s • v) - ψ xk
      - fderiv ℝ ψ xk (m - xk) - s * fderiv ℝ ψ xk v)
  have hFeq : ∀ s : ℝ, F s = l (m + s • v) + (1 / tk) * bregman ψ (m + s • v) xk := by
    intro s
    simp only [F, bregman, map_add, map_sub, map_smul, smul_eq_mul]
    ring
  have hF : HasDerivAt F (l v + (1 / tk) * (fderiv ℝ ψ m v - fderiv ℝ ψ xk v)) 0 := by
    have e1 : HasDerivAt (fun s : ℝ => s * l v) (l v) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).mul_const (l v)
    have e3 : HasDerivAt (fun s : ℝ => s * fderiv ℝ ψ xk v) (fderiv ℝ ψ xk v) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).mul_const (fderiv ℝ ψ xk v)
    have e2 := ((((line_deriv ψ m v hdm).sub_const (ψ xk)).sub_const
      (fderiv ℝ ψ xk (m - xk))).sub e3).const_mul (1 / tk)
    have := (e1.const_add (l m)).add e2
    exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => by
      simp only [F, Pi.add_apply, Pi.sub_apply])
  have hpos : ∀ s : ℝ, 0 < s → s < 1 → F 0 ≤ F s := by
    intro s hs0 hs1
    rw [hFeq, hFeq, zero_smul, add_zero]
    have hmem : m + s • v ∈ X := hXconv.add_smul_sub_mem hm hu ⟨hs0.le, hs1.le⟩
    exact hmin _ hmem
  exact slope_nonneg F _ hF hpos

end P800dbdb5

open BeckTeboulleMD.EMDA in
theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXc : IsClosed X) (hXconv : Convex ℝ X)
    (f : E → ℝ) (hf : ConvexOn ℝ X f)
    (Lf : ℝ) (hLip : ∀ x ∈ X, ∀ y ∈ X, |f x - f y| ≤ Lf * ‖x - y‖)
    (xstar : E) (hxstar : xstar ∈ X) (hmin : ∀ y ∈ X, f xstar ≤ f y)
    (g : E → E →L[ℝ] ℝ) (hg : ∀ x ∈ X, ∀ y ∈ X, f x + g x (y - x) ≤ f y)
    (ψ : E → ℝ) (σ : ℝ) (hσ : 0 < σ) (hψ : StrongConvexOn X σ ψ)
    (t : ℕ → ℝ) (x : ℕ → E) (hrun : IsSANPRun X ψ g t x) :
    ∀ k, 1 ≤ k → ∃ s ∈ Finset.Icc 1 k, f (x s) - f xstar
      ≤ (bregman ψ xstar (x 1)
          + 1 / (2 * σ) * ∑ s ∈ Finset.Icc 1 k, t s ^ 2 * ‖g (x s)‖ ^ 2)
        / ∑ s ∈ Finset.Icc 1 k, t s := by
  -- one step
  have step : ∀ k, 1 ≤ k → t k * (f (x k) - f xstar) ≤
      bregman ψ xstar (x k) - bregman ψ xstar (x (k + 1))
        + 1 / (2 * σ) * (t k ^ 2 * ‖g (x k)‖ ^ 2) := by
    intro k hk
    obtain ⟨htk, hxk, hdk, hmk⟩ := hrun k hk
    obtain ⟨_, hxk1, hdk1, _⟩ := hrun (k + 1) (by omega)
    have hA := hg (x k) hxk xstar hxstar
    have hB := P800dbdb5.first_order X hXconv ψ (g (x k)) (t k) (x k) (x (k + 1)) xstar
      hxk1 hxstar hdk1 hmk
    have hD := P800dbdb5.bregman_lb X ψ σ hψ (x k) (x (k + 1)) hxk hxk1 hdk
    have hE : g (x k) (x k - x (k + 1)) ≤ ‖g (x k)‖ * ‖x k - x (k + 1)‖ :=
      le_trans (le_abs_self _) ((g (x k)).le_opNorm _)
    -- three point identity
    have h3 : bregman ψ xstar (x k) - bregman ψ xstar (x (k + 1)) - bregman ψ (x (k + 1)) (x k)
        = fderiv ℝ ψ (x (k + 1)) (xstar - x (k + 1)) - fderiv ℝ ψ (x k) (xstar - x (k + 1)) := by
      unfold bregman
      simp only [map_sub]
      ring
    have hlin1 : g (x k) (xstar - x k) = g (x k) (xstar - x (k + 1)) - g (x k) (x k - x (k + 1)) := by
      rw [← map_sub]; congr 1; abel
    have hnorm : ‖x k - x (k + 1)‖ = ‖x (k + 1) - x k‖ := norm_sub_rev _ _
    set d := ‖x (k + 1) - x k‖
    set G := ‖g (x k)‖
    set a := g (x k) (xstar - x (k + 1))
    set b := g (x k) (x k - x (k + 1))
    have hB' : 0 ≤ t k * a + (fderiv ℝ ψ (x (k + 1)) (xstar - x (k + 1))
        - fderiv ℝ ψ (x k) (xstar - x (k + 1))) := by
      have := mul_nonneg htk.le hB
      rw [mul_add, ← mul_assoc, mul_one_div_cancel htk.ne', one_mul] at this
      exact this
    rw [hnorm] at hE
    have hquad : t k * G * d - σ / 2 * d ^ 2 ≤ 1 / (2 * σ) * (t k ^ 2 * G ^ 2) := by
      rw [show 1 / (2 * σ) * (t k ^ 2 * G ^ 2) = (t k * G) ^ 2 / (2 * σ) by ring,
        le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (σ * d - t k * G)]
    have hbE : t k * b ≤ t k * G * d := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hE htk.le
    have h1 : t k * (f (x k) - f xstar) ≤ t k * b - t k * a := by
      have := mul_le_mul_of_nonneg_left (show f (x k) - f xstar ≤ b - a by linarith) htk.le
      linarith
    linarith [h3, hD, hB', hquad, hbE]
  -- telescoped sum
  have tele : ∀ k, 1 ≤ k → ∑ s ∈ Finset.Icc 1 k, t s * (f (x s) - f xstar) ≤
      bregman ψ xstar (x 1) - bregman ψ xstar (x (k + 1))
        + 1 / (2 * σ) * ∑ s ∈ Finset.Icc 1 k, t s ^ 2 * ‖g (x s)‖ ^ 2 := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => simpa using step 1 le_rfl
    | succ n hn ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
      have := step (n + 1) (by omega)
      rw [mul_add]
      linarith
  intro k hk
  have hne : (Finset.Icc 1 k).Nonempty := ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hk⟩⟩
  obtain ⟨s, hs, hsmin⟩ := Finset.exists_min_image (Finset.Icc 1 k)
    (fun s => f (x s) - f xstar) hne
  refine ⟨s, hs, ?_⟩
  have htpos : ∀ j ∈ Finset.Icc 1 k, 0 < t j := fun j hj =>
    (hrun j (Finset.mem_Icc.1 hj).1).1
  have hT : 0 < ∑ j ∈ Finset.Icc 1 k, t j := Finset.sum_pos htpos hne
  rw [le_div_iff₀ hT, Finset.mul_sum]
  have hlow : ∑ j ∈ Finset.Icc 1 k, (f (x s) - f xstar) * t j ≤
      ∑ j ∈ Finset.Icc 1 k, t j * (f (x j) - f xstar) := by
    apply Finset.sum_le_sum
    intro j hj
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hsmin j hj) (htpos j hj).le
  have hk1 := (hrun (k + 1) (by omega))
  have hBnn := P800dbdb5.bregman_lb X ψ σ hψ (x (k + 1)) xstar hk1.2.1 hxstar hk1.2.2.1
  have : 0 ≤ σ / 2 * ‖xstar - x (k + 1)‖ ^ 2 := by positivity
  linarith [tele k hk]
