-- Prove2me | solution 1 for F3SubsetSum.theorem_4_20
-- status  : ACCEPTED   (prove)
-- author  : @Robin Kothari
-- created : 2026-11-14T04:22:21.65891+00:00
-- url     : https://prove2.me/submissions/2b36da0a-a290-414a-860a-05718ce56f50

import Theorems.Thm_F3SubsetSum_corollary_4_18
import Theorems.Thm_F3SubsetSum_theorem_4_19
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open F3SubsetSum
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option linter.all false

namespace RankLowerProof

private lemma three_term_bound (D a₀ a₁ a : ℕ) (hD : 3 ≤ D)
    (h₀₁ : (a₀ : ℝ) ^ (1 - 1 / (D : ℝ)) ≤ a₁)
    (h₁₂ : (a₁ : ℝ) ^ (1 - 1 / ((D : ℝ) - 1)) ≤ a) :
    (((a₀ : ℝ) + a₁ + a) / 3) ^ (1 - 2 / (D : ℝ)) ≤ a := by
  let d : ℝ := D
  let s := 1 - 2 / d
  let u := 1 - 1 / d
  let v := 1 - 1 / (d - 1)
  have hd : (3 : ℝ) ≤ d := by dsimp [d]; exact_mod_cast hD
  have hd0 : 0 < d := by linarith
  have hd1 : 0 < d - 1 := by linarith
  have hs : 0 < s := by dsimp [s]; rw [sub_pos, div_lt_one hd0]; linarith
  have hv : 0 < v := by dsimp [v]; rw [sub_pos, div_lt_one hd1]; linarith
  have hs1 : s ≤ 1 := by dsimp [s]; have := div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hd0.le; linarith
  have hsv : s ≤ v := by
    have hh : 1 / (d - 1) ≤ 2 / d := (div_le_div_iff₀ hd1 hd0).mpr (by linarith)
    dsimp [s, v]; linarith
  have huv : u * v = s := by
    dsimp [u, v, s]
    field_simp
    ring
  have h₀ : (a₀ : ℝ) ^ s ≤ a := by
    calc
      _ = ((a₀ : ℝ) ^ u) ^ v := by rw [← Real.rpow_mul (Nat.cast_nonneg _), huv]
      _ ≤ (a₁ : ℝ) ^ v := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) h₀₁ hv.le
      _ ≤ _ := h₁₂
  have h₁ : (a₁ : ℝ) ^ s ≤ a := by
    by_cases ha₁ : a₁ = 0
    · subst a₁; simp only [Nat.cast_zero, Real.zero_rpow hs.ne']; exact Nat.cast_nonneg a
    · exact (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ha₁) hsv).trans h₁₂
  have ha : (a : ℝ) ^ s ≤ a := by
    by_cases hz : a = 0
    · subst a; simp only [Nat.cast_zero, Real.zero_rpow hs.ne', le_refl]
    · exact Real.rpow_le_self_of_one_le (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz) hs1
  have hbase : 0 ≤ ((a₀ : ℝ) + a₁ + a) / 3 := by positivity
  have hmax : ((a₀ : ℝ) + a₁ + a) / 3 ≤ max (a₀ : ℝ) (max (a₁ : ℝ) a) := by
    have h0 := le_max_left (a₀ : ℝ) (max (a₁ : ℝ) a)
    have h1 := (le_max_left (a₁ : ℝ) a).trans (le_max_right (a₀ : ℝ) (max (a₁ : ℝ) a))
    have h2 := (le_max_right (a₁ : ℝ) a).trans (le_max_right (a₀ : ℝ) (max (a₁ : ℝ) a))
    linarith
  calc
    _ ≤ (max (a₀ : ℝ) (max (a₁ : ℝ) a)) ^ s := Real.rpow_le_rpow hbase hmax hs.le
    _ = max ((a₀ : ℝ) ^ s) (max ((a₁ : ℝ) ^ s) ((a : ℝ) ^ s)) := by
      rw [Real.rpow_max (Nat.cast_nonneg _) (le_max_of_le_left (Nat.cast_nonneg _)) hs.le,
        Real.rpow_max (Nat.cast_nonneg _) (Nat.cast_nonneg _) hs.le]
    _ ≤ _ := max_le h₀ (max_le h₁ ha)

end RankLowerProof

theorem solution (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) (n D : ℕ) (hD : 3 ≤ D)
    (W : Submodule (AlgebraicClosure (ZMod q))
      (Module.Dual (AlgebraicClosure (ZMod q)) (Rd (AlgebraicClosure (ZMod q)) n q D)))
    (hW : W ≠ ⊥) :
    ((Module.finrank (AlgebraicClosure (ZMod q)) W : ℝ) / 3) ^ (1 - 2 / (D : ℝ)) ≤
      symbolicRank (AlgebraicClosure (ZMod q)) n q D W := by

  classical
  obtain ⟨A, hvalid, hdim, hrank, hshadow⟩ := corollary_4_18 q hq n D (by omega) W hW
  let c := min (q - 1) D
  let a := ∑ d ∈ Finset.Icc 2 c, (A d).card
  have hc : 2 ≤ c := by dsimp [c]; omega
  have hdecomp : Module.finrank (AlgebraicClosure (ZMod q)) W =
      (A 0).card + (A 1).card + a := by
    rw [hdim]
    have he : Finset.range (c + 1) = insert 0 (insert 1 (Finset.Icc 2 c)) := by
      ext d
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    change (∑ d ∈ Finset.range (c + 1), (A d).card) = _
    rw [he, Finset.sum_insert (by simp), Finset.sum_insert (by simp)]
    omega
  have h₀₁ : ((A 0).card : ℝ) ^ (1 - 1 / (D : ℝ)) ≤ (A 1).card := by
    have ht := theorem_4_19 n D (by omega) (A 0) (by
      intro α hα
      simpa using (hvalid 0 (by dsimp [c] at hc; omega) α hα).2)
    exact ht.trans (by exact_mod_cast Finset.card_le_card (hshadow 0 (by dsimp [c] at hc; omega)))
  have h₂a : (A 2).card ≤ a := Finset.single_le_sum (fun d _ => Nat.zero_le (A d).card)
    (Finset.mem_Icc.mpr ⟨le_rfl, hc⟩)
  have h₁₂ : ((A 1).card : ℝ) ^ (1 - 1 / ((D : ℝ) - 1)) ≤ a := by
    have ht := theorem_4_19 n (D - 1) (by omega) (A 1) (by
      intro α hα
      exact (hvalid 1 (by dsimp [c] at hc; omega) α hα).2)
    have hcast : ((D - 1 : ℕ) : ℝ) = (D : ℝ) - 1 := by rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [hcast] at ht
    exact ht.trans (by exact_mod_cast (Finset.card_le_card (hshadow 1 (by dsimp [c] at hc; omega))).trans h₂a)
  have hb := RankLowerProof.three_term_bound D (A 0).card (A 1).card a hD h₀₁ h₁₂
  have hcast : (Module.finrank (AlgebraicClosure (ZMod q)) W : ℝ) =
      ((A 0).card : ℝ) + (A 1).card + a := by exact_mod_cast hdecomp
  rw [← hcast] at hb
  exact hb.trans (by exact_mod_cast hrank)

#print axioms solution
