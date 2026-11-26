-- Prove2me | solution 3 for GRH.signed_square_block_moebius_means_below_boundary
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T11:11:24.683743+00:00
-- url     : https://prove2.me/submissions/45f6cab0-bc08-46b7-b9e8-8b59ead54ddb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_centered_moebius_bound_iff_square_mertens_residual
import Theorems.Thm_GRH_moebius_square_mertens_harmonic_residual_below_boundary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset GRH
open scoped BigOperators

theorem solution (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a)
    (σ : ℝ) (hhalf : 1/2 < σ) (hcap : σ ≤ 0.8749570698) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℕ,
      |(∑ j ∈ range (2*u+1), centeredMoebiusBilinear q a (u^2+j))/((2*u+1:ℕ):ℝ)| ≤
        C*((u:ℝ)^2+1)^σ := by
  obtain ⟨D,hD,h⟩ := (centered_moebius_bound_iff_square_mertens_residual q a σ hhalf.le).2
    (moebius_square_mertens_harmonic_residual_below_boundary q a ha σ hhalf hcap)
  refine ⟨D*(2:ℝ)^σ, by positivity, fun u => ?_⟩
  let m := 2*u+1
  let X := ((u:ℝ)^2+1)^σ
  have hm : 0 < (m:ℝ) := by dsimp [m]; positivity
  have hjbound (j : ℕ) (hj : j ∈ range m) :
      |centeredMoebiusBilinear q a (u^2+j)| ≤ (D*(2:ℝ)^σ)*X := by
    have hjn : j ≤ 2*u := by simpa only [m,mem_range,Nat.lt_succ_iff] using hj
    have hjr : (j:ℝ) ≤ 2*(u:ℝ) := by exact_mod_cast hjn
    have hbase : ((u^2+j:ℕ):ℝ)+1 ≤ 2*((u:ℝ)^2+1) := by
      push_cast
      nlinarith [sq_nonneg ((u:ℝ)-1)]
    have hscale := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ ((u^2+j:ℕ):ℝ)+1)
      hbase (show 0 ≤ σ by linarith)
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity)] at hscale
    calc
      _ ≤ D * (((u^2+j:ℕ):ℝ)+1)^σ := h (u^2+j)
      _ ≤ D * ((2:ℝ)^σ*X) := mul_le_mul_of_nonneg_left hscale hD
      _ = _ := (mul_assoc _ _ _).symm
  change |(∑ j ∈ range m, centeredMoebiusBilinear q a (u^2+j))/(m:ℝ)| ≤ D*(2:ℝ)^σ*X
  rw [abs_div,abs_of_pos hm]
  apply (div_le_iff₀ hm).2
  calc
    _ ≤ ∑ j ∈ range m, |centeredMoebiusBilinear q a (u^2+j)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ range m, (D*(2:ℝ)^σ)*X := sum_le_sum hjbound
    _ = _ := by simp only [sum_const,card_range,nsmul_eq_mul]; ring
