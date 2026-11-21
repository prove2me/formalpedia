-- Prove2me | solution 1 for GRH.centered_moebius_progression_bilinear_power_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T02:25:57.841983+00:00
-- url     : https://prove2.me/submissions/99883307-4022-4e5c-958c-d7c3b5edd759
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_GRH_MoebiusBilinear
import Theorems.Thm_GRH_centered_moebius_square_block_control
import Theorems.Thm_GRH_signed_square_block_moebius_means_below_boundary
import Mathlib
open GRH Finset

theorem solution (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |centeredMoebiusBilinear q a N| ≤ C * ((N : ℝ) + 1) ^ σ := by
  obtain ⟨⟨K,hK,hm⟩,hu⟩ := centered_moebius_square_block_control q a ha
  by_cases hσ : 0.8749570698 < σ
  · exact hu σ hσ hone
  obtain ⟨C,hC,h⟩ := signed_square_block_moebius_means_below_boundary q a ha σ hhalf (le_of_not_gt hσ)
  refine ⟨2*K+C,by positivity,fun N => ?_⟩
  let u := N.sqrt
  let A := (∑ j ∈ range (2*u+1),centeredMoebiusBilinear q a (u^2+j))/((2*u+1:ℕ):ℝ)
  let X := ((N:ℝ)+1)^σ
  have hsr : (u:ℝ)^2 ≤ N := by exact_mod_cast Nat.sqrt_le' N
  have hx : (u:ℝ) ≤ X := by
    calc _ ≤ Real.sqrt ((N:ℝ)+1) := (Real.le_sqrt (by positivity) (by positivity)).2 (by linarith)
         _ = ((N:ℝ)+1)^(1/2:ℝ) := Real.sqrt_eq_rpow _
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by simp) hhalf.le
  have h1 : 1 ≤ X := Real.one_le_rpow (by simp) (by linarith)
  have hx' : ((u:ℝ)^2+1)^σ ≤ X := Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
  have h3 : |centeredMoebiusBilinear q a N| ≤ |centeredMoebiusBilinear q a N-A|+|A| := by
    simpa only [sub_add_cancel] using (abs_add_le (centeredMoebiusBilinear q a N-A) A)
  apply h3.trans
  calc _ ≤ K*((u:ℝ)+1)+C*((u:ℝ)^2+1)^σ := add_le_add (hm N) (h u)
       _ ≤ K*(X+X)+C*X := add_le_add (mul_le_mul_of_nonneg_left (add_le_add hx h1) hK) (mul_le_mul_of_nonneg_left hx' hC)
       _ = _ := by dsimp [X];ring
