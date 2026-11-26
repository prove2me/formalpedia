-- Prove2me | solution 1 for GRH.dirichlet_low_height_nonzero_of_nonnegative_real_prefixes
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T15:05:12.006927+00:00
-- url     : https://prove2.me/submissions/6ead394f-a69e-4e40-8c6f-2f23ac6e0cda

import Theorems.Thm_GRH_dirichlet_rectangle_tail_and_derivative_bounds
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Complex Set GRH.DirichletGrid

private lemma weighted_lower {f : ℕ → ℝ} (hf : f 0 = 1)
    (hp : ∀ n, 0 ≤ ∑ k ∈ Finset.range n, f k) {x : ℝ} (hx : (1/2:ℝ) ≤ x)
    (N : ℕ) (hN : 0 < N) :
    1/4 ≤ ∑ k ∈ Finset.range N, f k * ((k:ℝ)+1)^(-x) := by
  let w (k : ℕ) := ((k:ℝ)+1)^(-x)
  let A (n : ℕ) := ∑ k ∈ Finset.range n, f k
  let B (n : ℕ) := ∑ k ∈ Finset.range n, f k * w k
  have dec (k : ℕ) : w (k+1) ≤ w k := by
    unfold w
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
    push_cast
    linarith
  have inv (k : ℕ) : w 0-w 1 ≤ B (k+1) - A (k+1)*w (k+1) := by
    induction k with
    | zero => simp [A,B,hf]
    | succ k ih =>
      have Ar : A (k+2) = A (k+1) + f (k+1) := Finset.sum_range_succ _ _
      have Br : B (k+2) = B (k+1) + f (k+1)*w (k+1) := Finset.sum_range_succ _ _
      have pos : 0 ≤ A (k+2) := hp _
      have step := mul_nonneg pos (sub_nonneg.mpr (dec (k+1)))
      change _ ≤ B (k+2) - A (k+2)*w (k+2)
      rw [Ar] at step
      rw [Br,Ar]
      nlinarith
  have htwo : (2:ℝ)^(-x) ≤ 3/4 := by
    have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (show -x ≤ -(1/2:ℝ) by linarith)
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) (1/2:ℝ), ← Real.sqrt_eq_rpow] at hpow
    apply hpow.trans
    rw [← one_div, div_le_iff₀ (Real.sqrt_pos.2 (by norm_num))]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg (2:ℝ)]
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  have h := inv k
  have add := mul_nonneg (hp (k+1)) (show 0 ≤ w (k+1) by unfold w; positivity)
  change 0 ≤ A (k+1) * w (k+1) at add
  have w0 : w 0 = 1 := by simp [w]
  have w1 : w 1 = (2:ℝ)^(-x) := by norm_num [w]
  rw [w0,w1] at h
  change _ ≤ B (k+1)
  linarith

private lemma sample_lower {q : ℕ} (χ : DirichletCharacter ℂ q)
    (hp : ∀ n : ℕ, 0 ≤ ∑ k ∈ Finset.range n, (χ ((k+1:ℕ) : ZMod q)).re)
    {x : ℝ} (hx : (1/2:ℝ) ≤ x) {m : ℕ} (hm : 0 < m) : 1/4 ≤ ‖sample χ m (x:ℂ)‖ := by
  let f (k : ℕ) := (χ ((k+1:ℕ) : ZMod q)).re
  have h := weighted_lower (f:=f) (by simp [f]) hp hx (m^2) (pow_pos hm _)
  apply le_trans _ (Complex.re_le_norm (sample χ m (x:ℂ)))
  unfold sample
  rw [Complex.re_sum]
  have ic : Finset.Icc 1 (m^2) = Finset.Ico 1 (m^2+1) := by ext k; simp
  rw [ic, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel] 
  apply h.trans_eq
  apply Finset.sum_congr rfl
  intro k _
  have e : ((1+k:ℕ):ℂ)^(-(x:ℂ)) = (((k:ℝ)+1)^(-x) : ℝ) := by
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    rw [add_comm]
  rw [e]
  simp [f, Nat.add_comm, Complex.mul_re]

/-- Nonnegative real prefix sums give a quantitative neighborhood of the real interval. -/
theorem solution (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hp : ∀ n : ℕ, 0 ≤ ∑ k ∈ Finset.range n, (χ ((k+1:ℕ) : ZMod q)).re)
    (z : ℂ) (ha : (1/2:ℝ) ≤ z.re) (hb : z.re ≤ 1) (ht : |z.im| ≤ 1/(256*(q:ℝ))) :
    χ.LFunction z ≠ 0 := by
  have hq : (0:ℝ) < q := by exact_mod_cast NeZero.pos q
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  let x : ℂ := (z.re:ℂ)
  have hx : x ∈ reProdIm (Icc (1/2:ℝ) 1) (Icc (-0) 0) := by
    exact ⟨⟨ha,hb⟩,by simp [x]⟩
  let m := 96*q
  have hm : 0 < m := Nat.mul_pos (by decide) (NeZero.pos q)
  have he := (GRH.dirichlet_rectangle_tail_and_derivative_bounds q χ hχ le_rfl le_rfl
    (le_refl 0) hm hx).1
  have herr : tailBudget q 0 / (m:ℝ) = 1/16 := by
    unfold tailBudget m
    push_cast
    field_simp
    ring
  rw [herr] at he
  have hs : 1/4 ≤ ‖sample χ m x‖ := sample_lower χ hp ha hm
  have tri := norm_add_le (sample χ m x - χ.LFunction x) (χ.LFunction x)
  rw [sub_add_cancel, norm_sub_rev (sample χ m x)] at tri
  have hlower : 3/16 ≤ ‖χ.LFunction x‖ := by linarith
  let K := reProdIm (Icc (1/2:ℝ) 1) (Icc (-(1/2:ℝ)) (1/2))
  have inx : x ∈ K := ⟨⟨ha,hb⟩,by norm_num [x]⟩
  have inz : z ∈ K := ⟨⟨ha,hb⟩,abs_le.mp (ht.trans ((div_le_iff₀ (by positivity)).2 (by linarith)))⟩
  have cv : Convex ℝ K := ((convex_Icc (1/2:ℝ) 1).linear_preimage Complex.reLm).inter
    ((convex_Icc (-(1/2:ℝ)) (1/2)).linear_preimage Complex.imLm)
  have var : ‖χ.LFunction z - χ.LFunction x‖ ≤ slopeBudget q (1/2) * ‖z-x‖ :=
    cv.norm_image_sub_le_of_norm_deriv_le (fun w _ => χ.differentiableAt_LFunction w (.inr hχ))
      (fun w hw => (GRH.dirichlet_rectangle_tail_and_derivative_bounds q χ hχ le_rfl le_rfl
        (by norm_num) (m:=1) Nat.zero_lt_one hw).2) inx inz
  have dist : ‖z-x‖ ≤ |z.im| := by simpa [x] using Complex.norm_le_abs_re_add_abs_im (z-x)
  rw [show slopeBudget q (1/2) = 40*q by unfold slopeBudget; ring] at var
  have upper := mul_le_mul_of_nonneg_left (dist.trans ht) (show 0 ≤ 40*(q:ℝ) by positivity)
  have value : 40*(q:ℝ)*(1/(256*q)) = 5/32 := by field_simp; ring
  rw [value] at upper
  intro zero
  rw [zero,zero_sub,norm_neg] at var
  linarith
