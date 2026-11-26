-- Prove2me | solution 1 for GRH.dirichlet_one_disk_of_period_variation
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T15:35:55.188261+00:00
-- url     : https://prove2.me/submissions/81103ffc-3ae1-4478-ab46-72223e24d39b

import Theorems.Thm_GRH_dirichlet_abel_disk_from_centered_prefixes
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Complex

private lemma period_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (n : ℕ) :
    ∑ i ∈ Finset.range q, χ ((n+i+1:ℕ) : ZMod q) = 0 := by
  have reindex (f : ZMod q → ℂ) :
      ∑ i ∈ Finset.range q, f (i : ZMod q) = ∑ b : ZMod q, f b := by
    refine Finset.sum_nbij' (i := fun j => ((j : ℕ) : ZMod q)) (j := fun b => b.val)
      (fun _ _ => Finset.mem_univ _) (fun b _ => Finset.mem_range.mpr (ZMod.val_lt b))
      (fun _ hj => ZMod.val_natCast_of_lt (Finset.mem_range.mp hj))
      (fun b _ => ZMod.natCast_rightInverse b) (fun _ _ => rfl)
  calc _ = ∑ i ∈ Finset.range q, (fun b : ZMod q => χ ((n+1:ℕ)+b)) i := by
          apply Finset.sum_congr rfl
          intro i _
          push_cast
          congr 1
          abel
       _ = ∑ b : ZMod q, χ ((n+1:ℕ)+b) := reindex (fun b : ZMod q => χ ((n+1:ℕ)+b))
       _ = ∑ b : ZMod q, χ b := Fintype.sum_equiv (Equiv.addLeft ((n+1:ℕ) : ZMod q)) _ _ (fun _ => rfl)
       _ = 0 := MulChar.sum_eq_zero_of_ne_one hχ

private lemma period_disk {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (t : ℕ) (V : ℝ) (ht : t ≤ q)
    (hl : (∑ k ∈ Finset.range t, ‖χ ((k+1:ℕ):ZMod q)‖) ≤ V)
    (hr : (∑ k ∈ Finset.Ico t q, ‖χ ((k+1:ℕ):ZMod q)‖) ≤ V) :
    ∃ c : ℂ, ∀ n : ℕ, ‖(∑ k ∈ Finset.range n, χ ((k+1:ℕ):ZMod q))-c‖ ≤ V/2 := by
  let a (k : ℕ) := χ ((k+1:ℕ):ZMod q)
  let A (n : ℕ) := ∑ k ∈ Finset.range n, a k
  let S (n : ℕ) := ∑ k ∈ Finset.range n, ‖a k‖
  have zero : A q=0 := by simpa [A,a] using period_zero χ hχ 0
  have shift (n : ℕ) : A (n+q)=A n := by
    dsimp [A,a]
    rw [Finset.sum_range_add,period_zero χ hχ,add_zero]
  have dist {i j : ℕ} (hij : i ≤ j) : ‖A j - A i‖ ≤ S j - S i := by
    have e : A i+(∑ k ∈ Finset.Ico i j,a k)=A j := Finset.sum_range_add_sum_Ico _ hij
    have f : S i+(∑ k ∈ Finset.Ico i j,‖a k‖)=S j := Finset.sum_range_add_sum_Ico _ hij
    rw [← e,← f,add_sub_cancel_left,add_sub_cancel_left]
    exact norm_sum_le _ _
  have size (n : ℕ) : ‖A n‖ ≤ S n := norm_sum_le _ _
  have back : S q-S t ≤ V := by
    have e : S t+(∑ k ∈ Finset.Ico t q,‖a k‖)=S q := Finset.sum_range_add_sum_Ico _ ht
    rw [← e,add_sub_cancel_left]
    exact hr
  have one_period (n : ℕ) (hn : n ≤ q) : ‖A n-A t/2‖ ≤ V/2 := by
    rw [show A n-A t/2 = (A n+(A n-A t))/2 by ring,norm_div]
    norm_num only [Complex.norm_ofNat]
    apply div_le_div_of_nonneg_right _ (by norm_num)
    have tri := norm_add_le (A n) (A n-A t)
    by_cases h : n ≤ t
    · have e := dist h
      rw [norm_sub_rev] at e
      change S t ≤ V at hl
      linarith [size n]
    · have e := dist hn
      rw [zero,zero_sub,norm_neg] at e
      linarith [dist (le_of_lt (lt_of_not_ge h))]
  refine ⟨A t/2, fun n => ?_⟩
  change ‖A n - _‖ ≤ _
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ q
    · exact one_period n hn
    · have e : n-q+q=n := Nat.sub_add_cancel (by omega)
      have hrec := ih (n-q) (Nat.sub_lt (by omega) (NeZero.pos q))
      rw [← e,shift]
      exact hrec

/-- The two arcs of a complete character period enclose all prefixes in
a disk. An initial stretch of zero coefficients then controls L(s)-1. -/
theorem solution (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (t M : ℕ) (V : ℝ) (ht : t ≤ q) (hM : 0 < M)
    (hl : (∑ k ∈ Finset.range t, ‖χ ((k+1:ℕ):ZMod q)‖) ≤ V)
    (hr : (∑ k ∈ Finset.Ico t q, ‖χ ((k+1:ℕ):ZMod q)‖) ≤ V)
    (hzero : ∀ k : ℕ, 0 < k → k < M → χ ((k+1:ℕ):ZMod q) = 0)
    (s : ℂ) (hs : 0 < s.re) :
    ‖χ.LFunction s - 1‖ ≤ (V/2)*(1+‖s‖/s.re)*((M:ℝ)+1)^(-s.re) := by
  obtain ⟨c,hc⟩ := period_disk χ hχ t V ht hl hr
  have hV : 0 ≤ V := (Finset.sum_nonneg (fun k _ => norm_nonneg _)).trans hl
  have initial (v : ℕ → ℂ) (hv : v 0 = 1) :
      (∑ k ∈ Finset.range M, χ ((k+1:ℕ):ZMod q)*v k) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp [hv]
    · intro k hk hne
      rw [hzero k (Nat.pos_of_ne_zero hne) (Finset.mem_range.mp hk),zero_mul]
    · intro h
      exact (h (Finset.mem_range.mpr hM)).elim
  have A := initial (fun _ => 1) rfl
  simp only [mul_one] at A
  have P := initial (fun k => ((k+1:ℕ):ℂ)^(-s)) (by simp)
  have e := GRH.dirichlet_abel_disk_from_centered_prefixes q χ hχ M c (V/2)
    (by positivity) (fun n _ => hc n) s hs
  rw [A,P] at e
  have csize := hc M
  rw [A,norm_sub_rev] at csize
  have w : ‖((M+1:ℕ):ℂ)^(-s)‖=((M:ℝ)+1)^(-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.succ_pos _),neg_re]
    norm_cast
  have tri := dist_triangle (χ.LFunction s) (1+(c-1)*((M+1:ℕ):ℂ)^(-s)) 1
  simp only [dist_eq_norm] at tri
  rw [add_sub_cancel_left,norm_mul,w] at tri
  have bound := mul_le_mul_of_nonneg_right csize
    (show 0 ≤ ((M:ℝ)+1)^(-s.re) by positivity)
  linarith only [tri,e,bound]
