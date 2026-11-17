-- Prove2me | solution 1 for DetANN.HPIM.hpim_tree_correct
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-16T06:45:51.792369+00:00
-- url     : https://prove2.me/submissions/1ab46da1-3b2a-4ddc-9aba-816356cb6f50

import Mathlib
import Definitions.Def_DetANN_HPIMTree
import Theorems.Thm_DetANN_HPIM_hpimNode_correct
import Theorems.Thm_DetANN_HPIM_hpimTree_cost

/-!
# The HPIM tree is a `(1+δ)`-ANN structure, from the node correctness and the cost bound
-/

namespace DetANN.HPIM

lemma alpha_le (N : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    alphaOf N δ (Nat.clog 2 N) ≤ 1 + δ := by
  set h := Nat.clog 2 N
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg _
  set x := 1 / lamOf N δ with hx
  have hxv : x = δ / (4 * ((h : ℝ) + 1)) := by
    rw [hx]; unfold lamOf; simp only [h]; field_simp
  have hx0 : 0 ≤ x := by rw [hxv]; positivity
  -- (1 + x)^h ≤ exp(x h) ≤ exp(δ/4)
  have h1 : (1 + x) ^ h ≤ Real.exp (δ / 4) := by
    calc (1 + x) ^ h ≤ Real.exp x ^ h := by
          gcongr; linarith [Real.add_one_le_exp x]
      _ = Real.exp (h * x) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (δ / 4) := by
          apply Real.exp_le_exp.2
          rw [hxv, mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  -- exp(y) ≤ 1 + y + y² for y = δ/4 ≤ 1/8
  set y := δ / 4 with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y ≤ 1 / 8 := by rw [hy]; linarith
  have h2 : Real.exp y ≤ 1 + y + y ^ 2 := by
    have := Real.abs_exp_sub_one_sub_id_le (x := y) (by rw [abs_of_nonneg hy0]; linarith)
    linarith [le_abs_self (Real.exp y - 1 - y)]
  unfold alphaOf
  rw [← hx]
  calc (1 + x) ^ h * (1 + y) ^ 2 ≤ (1 + y + y ^ 2) * (1 + y) ^ 2 := by
        gcongr; exact h1.trans h2
    _ ≤ 1 + 4 * y := by
        have e2 : y ^ 2 ≤ y / 8 := by nlinarith
        have e3 : y ^ 3 ≤ y / 64 := by nlinarith
        have e4 : y ^ 4 ≤ y / 512 := by nlinarith
        nlinarith
    _ = 1 + δ := by rw [hy]; ring

/-- **M**, from M6, the factor arithmetic and the cost bound. -/
theorem hpim_tree_correct_aux :
    ∃ C₁ : ℕ, ∀ (m N : ℕ), 1 ≤ m → 1 ≤ N →
      ∀ Y : Fin N → EuclideanSpace ℝ (Fin m), Function.Injective Y →
        ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ q : EuclideanSpace ℝ (Fin m),
          (∃ k : Fin N, (hpimTree Y δ).search q = k ∧ ∀ j : Fin N, ‖q - Y k‖ ≤ (1 + δ) * ‖q - Y j‖) ∧
          ((hpimTree Y δ).cost q : ℝ) ≤ C₁ * m * Real.log (N / δ) ^ 2 := by
  obtain ⟨C₁, hC⟩ := hpimTree_cost
  refine ⟨C₁, fun m N hm hN Y hY δ hδ hδ' q => ⟨?_, hC m N hm hN Y hY δ hδ hδ' q⟩⟩
  have hfuel : Nat.clog 2 (Finset.univ : Finset (Fin N)).card < N + 1 := by
    rw [Finset.card_univ, Fintype.card_fin]
    have := Nat.clog_le_of_le_pow (b := 2) (x := N) (y := N) N.lt_two_pow_self.le
    omega
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨k, -, hks, hkb⟩ := hpimNode_correct Y δ hm hY hδ hδ' (N + 1) Finset.univ hne hfuel q
  refine ⟨k, hks, fun j => ?_⟩
  have hα := alpha_le N δ hδ hδ'
  rw [Finset.card_univ, Fintype.card_fin] at hkb
  exact (hkb j (Finset.mem_univ _)).trans (mul_le_mul_of_nonneg_right hα (norm_nonneg _))

end DetANN.HPIM

open DetANN.HPIM in
theorem solution :
    ∃ C₁ : ℕ, ∀ (m N : ℕ), 1 ≤ m → 1 ≤ N →
      ∀ Y : Fin N → EuclideanSpace ℝ (Fin m), Function.Injective Y →
        ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ q : EuclideanSpace ℝ (Fin m),
          (∃ k : Fin N, (hpimTree Y δ).search q = k ∧ ∀ j : Fin N, ‖q - Y k‖ ≤ (1 + δ) * ‖q - Y j‖) ∧
          ((hpimTree Y δ).cost q : ℝ) ≤ C₁ * m * Real.log (N / δ) ^ 2 :=
  hpim_tree_correct_aux
