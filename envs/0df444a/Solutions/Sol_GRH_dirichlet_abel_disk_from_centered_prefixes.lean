-- Prove2me | solution 1 for GRH.dirichlet_abel_disk_from_centered_prefixes
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T15:34:42.028262+00:00
-- url     : https://prove2.me/submissions/2664bf5d-7131-4ba5-bf10-1fa84be7f170

import Theorems.Thm_GlobalTheory_DirichletTail_norm_cpow_sub_le
import Theorems.Thm_GlobalTheory_DirichletTail_norm_LFunction_sub_sum_le
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Complex Filter Topology

private lemma finite_disk (a w : ℕ → ℂ) (u : ℕ → ℝ) (K R : ℝ) (hK : 1 ≤ K) (hR : 0 ≤ R)
    (hu : ∀ n, 0 ≤ u n) (hnorm : ∀ n, ‖w n‖ = u n)
    (hdiff : ∀ n, ‖w n-w (n+1)‖ ≤ K*(u n-u (n+1))) (M : ℕ) (c : ℂ)
    (hdisk : ∀ n, M ≤ n → ‖(∑ k ∈ Finset.range n, a k)-c‖ ≤ R) {N : ℕ} (hN : M ≤ N) :
    ‖(∑ k ∈ Finset.range N, a k*w k) -
      ((∑ k ∈ Finset.range M, a k*w k) + (c - ∑ k ∈ Finset.range M, a k)*w M)‖ ≤ R*K*u M := by
  let A (n : ℕ) := ∑ k ∈ Finset.range n, a k
  let P (n : ℕ) := ∑ k ∈ Finset.range n, a k*w k
  let B := P M + (c-A M)*w M
  let E (n : ℕ) := P n-B-(A n-c)*w n
  have step (n : ℕ) : E (n+1) = E n + (A (n+1)-c)*(w n-w (n+1)) := by
    dsimp only [E, P, A]
    rw [Finset.sum_range_succ,Finset.sum_range_succ]
    ring
  have inv (n : ℕ) (hn : M ≤ n) : ‖E n‖ ≤ R*K*(u M-u n) := by
    induction n,hn using Nat.le_induction with
    | base =>
      have e : E M = 0 := by dsimp only [E,B]; ring
      simp [e]
    | succ n hn ih =>
      rw [step]
      apply (norm_add_le _ _).trans
      rw [norm_mul]
      have ht := mul_le_mul (hdisk (n+1) (by omega)) (hdiff n)
        (norm_nonneg _) hR
      change ‖A (n+1)-c‖ * _ ≤ _ at ht
      linarith only [ih,ht]
  have e : P N-B = E N+(A N-c)*w N := by dsimp only [E]; ring
  change ‖P N-B‖ ≤ _
  rw [e]
  apply (norm_add_le _ _).trans
  rw [norm_mul,hnorm]
  have b := mul_le_mul_of_nonneg_right (hdisk N hN) (hu N)
  change ‖A N-c‖*_ ≤ _ at b
  nlinarith only [inv N hN,b,mul_nonneg (mul_nonneg hR (sub_nonneg.mpr hK)) (hu N)]

/-- A disk enclosing the coefficient prefixes gives an explicit error for
the Dirichlet polynomial with its complex boundary correction. -/
theorem solution (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (M : ℕ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hdisk : ∀ n : ℕ, M ≤ n → ‖(∑ k ∈ Finset.range n, χ ((k+1:ℕ):ZMod q)) - c‖ ≤ R)
    (s : ℂ) (hs : 0 < s.re) :
    ‖χ.LFunction s - ((∑ k ∈ Finset.range M, χ ((k+1:ℕ):ZMod q) * ((k+1:ℕ):ℂ)^(-s)) +
       (c - ∑ k ∈ Finset.range M, χ ((k+1:ℕ):ZMod q)) * ((M+1:ℕ):ℂ)^(-s))‖
      ≤ R*(‖s‖/s.re)*((M:ℝ)+1)^(-s.re) := by
  let a (k : ℕ) := χ ((k+1:ℕ):ZMod q)
  let w (k : ℕ) := ((k+1:ℕ):ℂ)^(-s)
  let u (k : ℕ) := ((k:ℝ)+1)^(-s.re)
  let K := ‖s‖/s.re
  let B := (∑ k ∈ Finset.range M, a k*w k) + (c-∑ k ∈ Finset.range M, a k)*w M
  have hK : 1 ≤ K := (one_le_div hs).2 (re_le_norm s)
  have hn (k : ℕ) : ‖w k‖ = u k := by
    dsimp only [w,u]
    rw [Complex.norm_natCast_cpow_of_pos (Nat.succ_pos _), neg_re]
    norm_cast
  have diff (k : ℕ) : ‖w k-w (k+1)‖ ≤ K*(u k-u (k+1)) := by
    have h := GlobalTheory.DirichletTail.norm_cpow_sub_le (s:=s) (a:=(k:ℝ)+1)
      (b:=(k:ℝ)+1+1) (δ:=s.re) (by linarith [Nat.cast_nonneg (α:=ℝ) k]) (by linarith) hs le_rfl
    simpa [w,u,K] using h
  have finite (n : ℕ) (h : M ≤ n) : ‖(∑ k ∈ Finset.range n, a k*w k)-B‖ ≤ R*K*u M :=
    finite_disk a w u K R hK hR (fun n => by dsimp [u]; positivity) hn diff M c hdisk h
  let T := 2*(q:ℝ)*(1+‖s‖/s.re)
  have lim : Tendsto (fun n : ℕ => T*(n:ℝ)^(-s.re)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds (x:=T)).mul
      ((tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop)
  change ‖χ.LFunction s-B‖ ≤ R*K*u M
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (show
    Tendsto (fun n : ℕ => T*(n:ℝ)^(-s.re)+R*K*u M) atTop (𝓝 (R*K*u M)) by
    simpa using lim.add_const (R*K*u M))
  filter_upwards [eventually_ge_atTop (max M 1)] with n hN
  have e := GlobalTheory.DirichletTail.norm_LFunction_sub_sum_le q χ hχ s hs n ((le_max_right ..).trans hN)
  have ic : Finset.Icc 1 n = Finset.Ico 1 (n+1) := by ext k; simp
  rw [ic,Finset.sum_Ico_eq_sum_range,Nat.add_sub_cancel] at e
  have e' : ‖χ.LFunction s - ∑ k ∈ Finset.range n, a k*w k‖ ≤ T*(n:ℝ)^(-s.re) := by
    simpa only [a,w,T,Nat.add_comm 1] using e
  have tri := dist_triangle (χ.LFunction s) (∑ k ∈ Finset.range n, a k*w k) B
  simp only [dist_eq_norm] at tri
  exact tri.trans (add_le_add e' (finite n ((le_max_left ..).trans hN)))
