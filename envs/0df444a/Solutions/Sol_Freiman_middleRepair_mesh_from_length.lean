-- Prove2me | solution 1 for Freiman.middleRepair_mesh_from_length
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T22:51:48.542998+00:00
-- url     : https://prove2.me/submissions/54667f1c-02d5-406a-be31-c29158bd80e5

import Definitions.Def_Freiman_middleRepair
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.MetricSpace.Pseudo.Defs

open Freiman

private theorem widths_compare (c : MiddleCore) (hc : middleRegular c)
    (hr : middleRatio c < (5 : ℝ)) :
    middleWidth c.left ≤ 5 * middleWidth c.right ∧
      middleWidth c.right ≤ 5 * middleWidth c.left := by
  unfold middleRatio middleNormalized at hr
  split_ifs at hr with h
  · have h' := (div_lt_iff₀ hc.2.2.2).mp hr
    exact ⟨le_of_lt h', by linarith [hc.2.2.1]⟩
  · have h' := (div_lt_iff₀ hc.2.2.1).mp hr
    exact ⟨by linarith [hc.2.2.2], le_of_lt h'⟩

theorem solution :
    (∀ w : List ℕ+, middleWidth w ≤ (middleBeta-middleAlpha)/(Nat.fib (w.length+1):ℝ)^2) →
    (∀ c : MiddleCore, middleRegular c → middleRepairGood c → middleRatio c < (5:ℝ)) →
    ∀ (c : MiddleCore) (t : ℝ) (p : ℕ→MiddleCore), middleRepairPath c t p →
      (∀ n : ℕ, n+c.left.length+c.right.length ≤ (p n).left.length+(p n).right.length) →
      Filter.Tendsto (fun n : ℕ => middleWidth (p n).left+middleWidth (p n).right) Filter.atTop (nhds 0) := by
  intro fibbound ratio c t p hp hlength
  have hB : 0 ≤ middleBeta - middleAlpha := by
    have hs : 3 < Real.sqrt 21 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
    unfold middleBeta middleAlpha
    linarith
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (max (5 : ℝ) (6 * (middleBeta-middleAlpha) / ε))
  have hNfive : (5 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hNbound : 6 * (middleBeta-middleAlpha) / ε < (N : ℝ) :=
    lt_of_le_of_lt (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hNnat : 5 ≤ N := by exact_mod_cast (le_of_lt hNfive)
  have hsmall : 6 * ((middleBeta-middleAlpha) / (N : ℝ)) < ε := by
    have hcross := (div_lt_iff₀ hε).mp hNbound
    have hdiv := (div_lt_iff₀ hNpos).mpr (show 6 * (middleBeta-middleAlpha) < ε * N by linarith)
    simpa only [mul_div_assoc] using hdiv
  have long (w : List ℕ+) (hlen : N ≤ w.length) :
      middleWidth w ≤ (middleBeta-middleAlpha) / (N : ℝ) := by
    have hfib : N ≤ Nat.fib (w.length+1) :=
      le_trans (by omega : N ≤ w.length+1) (Nat.le_fib_self (by omega))
    have hfibR : (N : ℝ) ≤ (Nat.fib (w.length+1) : ℝ) := by exact_mod_cast hfib
    have hden : (N : ℝ) ≤ (Nat.fib (w.length+1) : ℝ)^2 := by nlinarith
    exact (fibbound w).trans (div_le_div_of_nonneg_left hB hNpos hden)
  refine ⟨2*N, ?_⟩
  intro n hn
  have hc := (hp.2 n).1
  have hg := (hp.2 n).2.1
  have hcomp := widths_compare (p n) hc (ratio _ hc hg)
  have hsum := hlength n
  have hlarge : N ≤ (p n).left.length ∨ N ≤ (p n).right.length := by omega
  have hbound : middleWidth (p n).left + middleWidth (p n).right ≤
      6 * ((middleBeta-middleAlpha) / (N : ℝ)) := by
    rcases hlarge with hl | hr
    · have hw := long (p n).left hl
      linarith [hcomp.2]
    · have hw := long (p n).right hr
      linarith [hcomp.1]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith [hc.2.2.1, hc.2.2.2])]
  exact hbound.trans_lt hsmall

#print axioms solution
