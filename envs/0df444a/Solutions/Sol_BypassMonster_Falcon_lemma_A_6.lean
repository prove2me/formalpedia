-- Prove2me | solution 1 for BypassMonster.Falcon.lemma_A_6
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:54:47.200648+00:00
-- url     : https://prove2.me/submissions/95e4d610-8009-4344-b052-ae5bc660a04e

import Mathlib
import Definitions.Def_BypassMonster_Falcon_Model
import Definitions.Def_BypassMonster_Falcon_Analysis

open MeasureTheory

namespace Aux_Falcon_A6
open BypassMonster.Falcon

lemma pt {K : ℕ} [NeZero K] (γ : ℝ) (hγ : 0 ≤ γ) (amax : (Fin K → ℝ) → Fin K)
    (hamax : ∀ (g : Fin K → ℝ) (a : Fin K), g a ≤ g (amax g)) (g : Fin K → ℝ) (a : Fin K) :
    1 / igw γ amax g a ≤ (K : ℝ) + γ * (g (amax g) - g a) := by
  have hK : (1 : ℝ) ≤ K := by exact_mod_cast NeZero.one_le
  have hD : ∀ b, (K : ℝ) ≤ (K : ℝ) + γ * (g (amax g) - g b) := by
    intro b
    have := hamax g b
    have : 0 ≤ γ * (g (amax g) - g b) := mul_nonneg hγ (by linarith)
    linarith
  unfold igw
  by_cases ha : a = amax g
  · rw [if_pos ha, ha, sub_self, mul_zero, add_zero]
    have hterm : ∀ b ∈ Finset.univ.erase (amax g),
        1 / ((K : ℝ) + γ * (g (amax g) - g b)) ≤ 1 / (K : ℝ) := by
      intro b _
      exact one_div_le_one_div_of_le (by linarith) (hD b)
    have hsum := Finset.sum_le_card_nsmul _ _ _ hterm
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hsum
    have hcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
      rw [Nat.cast_sub NeZero.one_le]; simp
    rw [hcast] at hsum
    have hp : 1 / (K : ℝ) ≤
        1 - ∑ b ∈ Finset.univ.erase (amax g), 1 / ((K : ℝ) + γ * (g (amax g) - g b)) := by
      have : ((K : ℝ) - 1) * (1 / (K : ℝ)) = 1 - 1 / (K : ℝ) := by
        field_simp
      linarith
    have hKpos : (0 : ℝ) < K := by linarith
    have hppos : 0 < 1 - ∑ b ∈ Finset.univ.erase (amax g),
        1 / ((K : ℝ) + γ * (g (amax g) - g b)) :=
      lt_of_lt_of_le (by positivity) hp
    exact (one_div_le hppos hKpos).mpr hp
  · rw [if_neg ha, one_div_one_div]

end Aux_Falcon_A6

open BypassMonster.Falcon in
theorem solution
    {X : Type*} [Fintype X] [MeasurableSpace X] [DiscreteMeasurableSpace X]
    {K : ℕ} [NeZero K]
    (DX : Measure X) [IsProbabilityMeasure DX]
    (A : Params X K) (hamax : ∀ (g : Fin K → ℝ) (a : Fin K), g a ≤ g (A.amax g))
    (m : ℕ) (hm : 1 ≤ m) (ω : Params.Omega X K) (π : X → Fin K) :
    V DX (A.pm m ω) π ≤ (K : ℝ) + A.gamma m * A.RegHat DX m ω π := by
  have hγ : 0 ≤ A.gamma m := by
    unfold Params.gamma
    split_ifs
    · norm_num
    · exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  have hRHS : (K : ℝ) + A.gamma m * A.RegHat DX m ω π =
      ∫ x, ((K : ℝ) + A.gamma m * (A.fhat m ω x (A.amax (A.fhat m ω x)) - A.fhat m ω x (π x))) ∂DX := by
    rw [integral_add (integrable_const _) Integrable.of_finite, integral_const, probReal_univ,
      one_smul, integral_const_mul, integral_sub Integrable.of_finite Integrable.of_finite]
    rfl
  rw [hRHS]
  unfold V
  apply integral_mono Integrable.of_finite Integrable.of_finite
  intro x
  exact Aux_Falcon_A6.pt (A.gamma m) hγ A.amax hamax (A.fhat m ω x) (π x)
