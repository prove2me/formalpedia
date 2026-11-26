-- Prove2me | solution 1 for GRH.dirichlet_abel_bound_of_prefix_envelope
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T17:27:16.722722+00:00
-- url     : https://prove2.me/submissions/4adda2c4-f449-4b81-91a6-95c8c765681d

import Theorems.Thm_GRH_dirichlet_abel_disk_from_centered_prefixes
import Theorems.Thm_GlobalTheory_DirichletTail_norm_cpow_sub_le
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Complex

private lemma prefix_expansion (a w : ℕ → ℂ) (h1 : w 0=1) (M : ℕ) :
    (∑ k ∈ Finset.range M,a k*w k) + (1-∑ k ∈ Finset.range M,a k)*w M - 1 =
      ∑ k ∈ Finset.range M, ((∑ j ∈ Finset.range (k+1),a j)-1)*(w k-w (k+1)) := by
  induction M with
  | zero => simp [h1]
  | succ M ih =>
    rw [Finset.sum_range_succ (f:=fun k => ((∑ j ∈ Finset.range (k+1),a j)-1)*(w k-w (k+1)))]
    rw [← ih]
    simp only [Finset.sum_range_succ]
    ring

/-- Abel summation with a separate bound for every centered prefix and a uniform tail. -/
theorem solution (Q M : ℕ) [NeZero Q] (ψ : DirichletCharacter ℂ Q) (hp : ψ ≠ 1)
    (s : ℂ) (x K R : ℝ) (B : ℕ → ℝ) (hx : 0 < x) (hxs : x ≤ s.re) (hK : ‖s‖/x ≤ K)
    (hR0 : 0 ≤ R) (hB0 : ∀ n, 0 ≤ B n)
    (hB : ∀ n : ℕ, ‖(∑ k ∈ Finset.range n,ψ ((k+1:ℕ):ZMod Q))-1‖ ≤ B n)
    (hR : ∀ n, B n ≤ R) :
    ‖ψ.LFunction s-1‖ ≤ K*((∑ k ∈ Finset.range M,B (k+1)*
      (((k:ℝ)+1)^(-x)-((k:ℝ)+2)^(-x)))+R*((M:ℝ)+1)^(-x)) := by
  let A (k : ℕ) := ψ ((k+1:ℕ):ZMod Q)
  let w (k : ℕ) := ((k+1:ℕ):ℂ)^(-s)
  let u (k : ℕ) := ((k:ℝ)+1)^(-x)
  let P := (∑ k ∈ Finset.range M,A k*w k)+(1-∑ k ∈ Finset.range M,A k)*w M
  have sx := hx.trans_le hxs
  have kpos := (div_nonneg (norm_nonneg s) hx.le).trans hK
  have disk (n : ℕ) : ‖(∑ k ∈ Finset.range n,A k)-1‖ ≤ B n := hB n
  have tail := GRH.dirichlet_abel_disk_from_centered_prefixes Q ψ hp M 1 R hR0
    (fun n _ => (disk n).trans (hR n)) s sx
  change ‖ψ.LFunction s-P‖ ≤ _ at tail
  have rat := (div_le_div_of_nonneg_left (norm_nonneg s) hx hxs).trans hK
  have mono := Real.rpow_le_rpow_of_exponent_le
    (show 1 ≤ (M:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) M]) (neg_le_neg hxs)
  have tail' : ‖ψ.LFunction s-P‖ ≤ (R:ℝ)*K*u M := tail.trans
    (mul_le_mul (mul_le_mul_of_nonneg_left rat (by positivity)) mono (by positivity)
      (mul_nonneg (by positivity) kpos))
  have diff (k : ℕ) : ‖w k-w (k+1)‖ ≤ K*(u k-u (k+1)) := by
    have he := GlobalTheory.DirichletTail.norm_cpow_sub_le (s:=s) (a:=(k:ℝ)+1)
      (b:=(k:ℝ)+1+1) (δ:=x) (by linarith [Nat.cast_nonneg (α:=ℝ) k]) (by linarith) hx hxs
    have variation : ‖w k-w (k+1)‖ ≤ (‖s‖/x)*(u k-u (k+1)) := by
      simpa [w,u] using he
    apply variation.trans (mul_le_mul_of_nonneg_right hK _)
    apply sub_nonneg.mpr
    dsimp [u]
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (neg_nonpos.mpr hx.le)
    push_cast
    linarith
  have finite : ‖P-1‖ ≤ K * ∑ k ∈ Finset.range M,B (k+1)*(u k-u (k+1)) := by
    dsimp only [P]
    rw [prefix_expansion A w (by simp [w]),Finset.mul_sum]
    apply (norm_sum_le _ _).trans (Finset.sum_le_sum _)
    intro k _
    rw [norm_mul]
    have h := mul_le_mul (disk (k+1)) (diff k) (norm_nonneg _) (hB0 (k+1))
    linarith only [h]
  have tri := norm_sub_le_norm_sub_add_norm_sub (ψ.LFunction s) P 1
  apply tri.trans
  have e (k : ℕ) : u (k+1)=((k:ℝ)+2)^(-x) := by simp [u]; ring_nf
  simp only [e] at finite
  dsimp only [u] at finite tail'
  linarith only [finite,tail']

