-- Prove2me | solution 1 for CoCoNet.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T03:35:34.319828+00:00
-- url     : https://prove2.me/submissions/47ff9a2a-8c5a-4191-bb52-a6115ed31846

import Mathlib
import Definitions.Def_CoCoNet_IsAdmissible
import Definitions.Def_CoCoNet_bankrupt
import Definitions.Def_CoCoNet_converting
import Definitions.Def_CoCoNet_healthy
import Definitions.Def_CoCoNet_IsEquilibrium
import Definitions.Def_CoCoNet_Phi

namespace Aux_CoCoNet_l1
open CoCoNet Matrix

theorem sum_restrict {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (F : Finset (Fin n))
    (v : Fin n → ℝ) (i : Fin n) :
    ∑ j, W i j * restrictTo F v j = ∑ j ∈ F, W i j * v j := by
  simp only [restrictTo, mul_ite, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

theorem Phi_apply {n : ℕ} (m : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (l c s : Fin n → ℝ)
    (i : Fin n) :
    Phi m W l c s i = s i + restrictTo (bankrupt s) m i * s i
      + restrictTo (converting l s) m i * s i + restrictTo (healthy l s) c i
      - ∑ j ∈ converting l s, W i j * m j * s j - ∑ j ∈ healthy l s, W i j * c j := by
  have h1 : ((1 - W) * Matrix.diagonal (restrictTo (converting l s) m)) *ᵥ s =
      (1 - W) *ᵥ (Matrix.diagonal (restrictTo (converting l s) m) *ᵥ s) :=
    (Matrix.mulVec_mulVec _ _ _).symm
  unfold Phi Lmat
  rw [Matrix.add_mulVec, Matrix.add_mulVec, h1, Matrix.sub_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, Matrix.one_mulVec, Matrix.one_mulVec]
  simp only [Pi.add_apply, Pi.sub_apply, Matrix.mulVec_diagonal]
  have e1 : (W *ᵥ (Matrix.diagonal (restrictTo (converting l s) m) *ᵥ s)) i =
      ∑ j ∈ converting l s, W i j * (m j * s j) := by
    rw [Matrix.mulVec, dotProduct]
    simp only [Matrix.mulVec_diagonal]
    rw [← sum_restrict W (converting l s) (fun j => m j * s j) i]
    apply Finset.sum_congr rfl
    intro j _
    simp only [restrictTo]
    split_ifs <;> ring
  have e2 : (W *ᵥ restrictTo (healthy l s) c) i = ∑ j ∈ healthy l s, W i j * c j := by
    rw [Matrix.mulVec, dotProduct, sum_restrict]
  have e1' : ∑ j ∈ converting l s, W i j * (m j * s j) = ∑ j ∈ converting l s, W i j * m j * s j :=
    Finset.sum_congr rfl (fun j _ => by ring)
  rw [e1, e2, e1']
  ring

end Aux_CoCoNet_l1

open CoCoNet Aux_CoCoNet_l1 in
theorem solution {n : ℕ} (m : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (l c : Fin n → ℝ)
    (hadm : IsAdmissible m W) (hl : 0 ≤ l) (s : Fin n → ℝ) :
    (∃! P : Finset (Fin n) × Finset (Fin n) × Finset (Fin n),
        ∃ a : Fin n → ℝ, IsEquilibrium m W l c a s P.1 P.2.1 P.2.2) ∧
    ∀ (a : Fin n → ℝ) (B C H : Finset (Fin n)),
      IsEquilibrium m W l c a s B C H ↔
        (B = bankrupt s ∧ C = converting l s ∧ H = healthy l s ∧ a = Phi m W l c s) := by
  have mB : ∀ i, i ∈ bankrupt s ↔ s i < 0 := fun i => by simp [bankrupt]
  have mC : ∀ i, i ∈ converting l s ↔ 0 ≤ s i ∧ s i ≤ l i := fun i => by simp [converting]
  have mH : ∀ i, i ∈ healthy l s ↔ l i < s i := fun i => by simp [healthy]
  have hli : ∀ i, 0 ≤ l i := fun i => hl i
  have rB : ∀ (v : Fin n → ℝ) i, restrictTo (bankrupt s) v i = if s i < 0 then v i else 0 := by
    intro v i; simp only [restrictTo, mB]
  have rC : ∀ (v : Fin n → ℝ) i, restrictTo (converting l s) v i =
      if 0 ≤ s i ∧ s i ≤ l i then v i else 0 := by
    intro v i; simp only [restrictTo, mC]
  have rH : ∀ (v : Fin n → ℝ) i, restrictTo (healthy l s) v i = if l i < s i then v i else 0 := by
    intro v i; simp only [restrictTo, mH]
  have key : ∀ a : Fin n → ℝ, ∀ B C H : Finset (Fin n),
      IsEquilibrium m W l c a s B C H ↔
        (B = bankrupt s ∧ C = converting l s ∧ H = healthy l s ∧ a = Phi m W l c s) := by
    intro a B C H
    constructor
    · intro E
      refine ⟨E.B_eq, E.C_eq, E.H_eq, ?_⟩
      funext i
      rw [Phi_apply, rB, rC, rH, ← E.C_eq, ← E.H_eq]
      rcases lt_or_ge (s i) 0 with h1 | h1
      · have hi : i ∈ B ∪ C := by rw [E.B_eq]; simp [mB, h1]
        have := E.eq1 i hi
        rw [if_pos h1, if_neg (by intro h; linarith [h.1]), if_neg (by intro h; linarith [hli i])]
        linarith
      · rcases le_or_gt (s i) (l i) with h2 | h2
        · have hi : i ∈ B ∪ C := by rw [E.C_eq]; simp [mC, h1, h2]
          have := E.eq1 i hi
          rw [if_neg (by linarith), if_pos ⟨h1, h2⟩, if_neg (by linarith)]
          linarith
        · have hi : i ∈ H := by rw [E.H_eq]; simp [mH, h2]
          have := E.eq2 i hi
          rw [if_neg (by linarith), if_neg (by intro h; linarith [h.2]), if_pos h2]
          linarith
    · rintro ⟨hB, hC, hH, ha⟩
      subst hB hC hH ha
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
      · rw [Finset.disjoint_left]; intro i h1 h2; rw [mB] at h1; rw [mC] at h2; linarith [h2.1]
      · rw [Finset.disjoint_left]; intro i h1 h2; rw [mB] at h1; rw [mH] at h2; linarith [hli i]
      · rw [Finset.disjoint_left]; intro i h1 h2; rw [mC] at h1; rw [mH] at h2; linarith [h1.2]
      · ext i
        simp only [Finset.mem_union, mB, mC, mH, Finset.mem_univ, iff_true]
        rcases lt_or_ge (s i) 0 with h1 | h1
        · left; left; exact h1
        · rcases le_or_gt (s i) (l i) with h2 | h2
          · left; right; exact ⟨h1, h2⟩
          · right; exact h2
      · intro i hi
        rw [Phi_apply, rB, rC, rH]
        rw [Finset.mem_union, mB, mC] at hi
        rcases hi with h1 | h1
        · rw [if_pos h1, if_neg (by intro h; linarith [h.1]), if_neg (by intro h; linarith [hli i])]
          ring
        · rw [if_neg (by linarith [h1.1]), if_pos h1, if_neg (by intro h; linarith [h1.2])]
          ring
      · intro i hi
        rw [mH] at hi
        rw [Phi_apply, rB, rC, rH, if_neg (by linarith [hli i]),
          if_neg (by intro h; linarith [h.2]), if_pos hi]
        ring
  refine ⟨⟨(bankrupt s, converting l s, healthy l s), ⟨Phi m W l c s,
    (key _ _ _ _).mpr ⟨rfl, rfl, rfl, rfl⟩⟩, ?_⟩, key⟩
  rintro ⟨B, C, H⟩ ⟨a, E⟩
  obtain ⟨h1, h2, h3, -⟩ := (key _ _ _ _).mp E
  simp only at h1 h2 h3
  rw [h1, h2, h3]
