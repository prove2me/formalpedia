-- Prove2me | solution 1 for GRH.character_weighted_moment_abel_inequality
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T17:44:16.980748+00:00
-- url     : https://prove2.me/submissions/01bd9d95-08d7-49a8-8a17-03889c1ba996

import Theorems.Thm_GRH_character_moment_centered_convolution_bound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open GRH.CharacterMoment

/-- A single convolution row controlling a weighted sum of squared character
prefixes gives a bound for their weighted absolute values. -/
theorem solution (q : ℕ) (χ : DirichletCharacter ℂ q) (I U : Finset ℕ)
    (iv T w t h : ℕ → ℕ) (z : ℕ → ℂ) (L c : ℕ) (rs : List (Array ℕ))
    (perm : Permutes q U iv) (hz : ∑ a ∈ U, χ (a:ZMod q)=0)
    (hr : Rows q U iv T rs) (hl : ∀ i ∈ I, t i*h i=L)
    (he : ((∑ i ∈ I, (w i*h i:ℕ)*‖z i‖^2 : ℝ):ℂ) =
      ∑ a ∈ U, (T a:ℂ)*χ (a:ZMod q)) :
    (L:ℝ)^(2^rs.length)*(∑ i ∈ I,(w i:ℝ)*‖z i‖)^(2*2^rs.length) ≤
      ((∑ i ∈ I,w i*t i : ℕ):ℝ)^(2^rs.length)*(deviation U (lastRow T rs) c:ℝ) := by
  let A := ∑ i ∈ I,(w i:ℝ)*‖z i‖
  let H : ℝ := ∑ i ∈ I, ((w i*t i:ℕ):ℝ)
  let E := ∑ i ∈ I, ((w i*h i:ℕ):ℝ)*‖z i‖^2
  have hnonneg : 0≤H := Finset.sum_nonneg (fun _ _ => by positivity)
  have enonneg : 0≤E := Finset.sum_nonneg (fun _ _ => by positivity)
  have cs : (Real.sqrt L*A)^2 ≤ H*E := by
    dsimp only [A,H,E]
    rw [Finset.mul_sum]
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun _ _ => by positivity)
      (fun _ _ => by positivity)
    intro i hi
    simp only [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _),Nat.cast_mul]
    have e : (t i:ℝ)*(h i:ℝ)=L := by exact_mod_cast hl i hi
    rw [← e]
    exact le_of_eq (by ring)
  rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg _)] at cs
  have f := GRH.character_moment_centered_convolution_bound q χ U iv T rs c perm hz hr
  rw [← he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg enonneg] at f
  let m := 2^rs.length
  change (L:ℝ)^m * A^(2*m) ≤ _ 
  rw [pow_mul,← mul_pow,Nat.cast_sum]
  change ((L:ℝ)*A^2)^m ≤ H^m*(deviation U (lastRow T rs) c:ℝ)
  apply (pow_le_pow_left₀ (by positivity) cs m).trans
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_left f (pow_nonneg hnonneg _)
