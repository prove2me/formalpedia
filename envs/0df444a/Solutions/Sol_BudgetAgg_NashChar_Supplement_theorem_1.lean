-- Prove2me | solution 1 for BudgetAgg.NashChar.Supplement.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:13:10.596835+00:00
-- url     : https://prove2.me/submissions/cb6a0241-2925-4a2c-9402-0bbafba16413

import Mathlib
import Definitions.Def_BudgetAgg_NashChar_Setting
import Definitions.Def_BudgetAgg_NashChar_Supplement_LpModel

open BudgetAgg
open BudgetAgg.NashChar
open BudgetAgg.NashChar.Supplement

open BudgetAgg.NashChar

/-- Theorem 1, p. 11: with `ℓ1` preferences, `m ≥ 3`, `n ≥ 3`, no mechanism is
efficient, strategyproof and proportional. -/
theorem solution {n m : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) (f : Mechanism n m) :
    ¬ (IsEfficientMech l1Util f ∧ IsStrategyproofFor l1Util f ∧ IsProportional f) := by
      rintro ⟨hE, hSP, hPr⟩
      obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 1 / (n : ℝ) := ⟨_, rfl⟩
      have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
      have ht0 : 0 < t := by rw [ht]; positivity
      have ht3 : 3 * t ≤ 1 := by
        rw [ht, mul_one_div, div_le_one (by linarith)]; exact hnR
      have mk : ∀ (a b c : Fin m), a ≠ b → a ≠ c → b ≠ c → ∀ x y z : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ z →
          x + y + z = 1 → ∃ p : stdSimplex ℝ (Fin m), ∀ j, p.1 j =
            (if j = a then x else 0) + (if j = b then y else 0) + (if j = c then z else 0) := by
        intro a b c hab hac hbc x y z hx hy hz hs
        refine ⟨⟨fun j => (if j = a then x else 0) + (if j = b then y else 0) +
          (if j = c then z else 0), ?_, ?_⟩, fun j => rfl⟩
        · intro j
          dsimp only
          split_ifs <;> linarith
        · simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          linarith
      have hd : ∀ (a b c : Fin m), a ≠ b → a ≠ c → b ≠ c → ∀ p q : stdSimplex ℝ (Fin m),
          (∀ j, j ≠ a → j ≠ b → j ≠ c → p.1 j = 0) →
          l1Util p q = -(|p.1 a - q.1 a| + |p.1 b - q.1 b| + |p.1 c - q.1 c| +
            (1 - q.1 a - q.1 b - q.1 c)) := by
        intro a b c hab hac hbc p q hp
        have hq : ∑ j, q.1 j = 1 := q.2.2
        have h1 : ∑ j, (|p.1 j - q.1 j| - q.1 j) =
            ∑ j ∈ ({a, b, c} : Finset (Fin m)), (|p.1 j - q.1 j| - q.1 j) := by
          symm
          apply Finset.sum_subset (Finset.subset_univ _)
          intro j _ hj
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
          rw [hp j hj.1 hj.2.1 hj.2.2, zero_sub, abs_neg, abs_of_nonneg (q.2.1 j), sub_self]
        rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
          Finset.sum_singleton] at h1
        rw [Finset.sum_sub_distrib, hq] at h1
        unfold l1Util
        linarith
      have hle3 : ∀ (a b c : Fin m), a ≠ b → a ≠ c → b ≠ c → ∀ q : stdSimplex ℝ (Fin m),
          q.1 a + q.1 b + q.1 c ≤ 1 := by
        intro a b c hab hac hbc q
        have h := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.subset_univ ({a, b, c} : Finset (Fin m))) (fun j _ _ => q.2.1 j)
        rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
          Finset.sum_singleton, q.2.2] at h
        linarith
      obtain ⟨b, hbdef⟩ : ∃ x : Fin m, x = ⟨1, by omega⟩ := ⟨_, rfl⟩
      obtain ⟨a0, ha0⟩ : ∃ x : Fin m, x = ⟨0, by omega⟩ := ⟨_, rfl⟩
      obtain ⟨c0, hc0⟩ : ∃ x : Fin m, x = ⟨2, by omega⟩ := ⟨_, rfl⟩
      have h0b : a0 ≠ b := by rw [ha0, hbdef]; simp [Fin.ext_iff]
      have h2b : c0 ≠ b := by rw [hc0, hbdef]; simp [Fin.ext_iff]
      have h02 : a0 ≠ c0 := by rw [ha0, hc0]; simp [Fin.ext_iff]
      have hb0 : b ≠ a0 := h0b.symm
      have hb2 : b ≠ c0 := h2b.symm
      have h20 : c0 ≠ a0 := h02.symm
      obtain ⟨A, hA⟩ : ∃ x : Fin n, x = ⟨0, by omega⟩ := ⟨_, rfl⟩
      obtain ⟨Z, hZ⟩ : ∃ x : Fin n, x = ⟨n - 1, by omega⟩ := ⟨_, rfl⟩
      obtain ⟨B, hB⟩ : ∃ x : Fin n, x = ⟨1, by omega⟩ := ⟨_, rfl⟩
      have hAZ : A ≠ Z := by rw [hA, hZ]; simp [Fin.ext_iff]; omega
      have hBA : B ≠ A := by rw [hA, hB]; simp [Fin.ext_iff]
      have hBZ : B ≠ Z := by rw [hB, hZ]; simp [Fin.ext_iff]; omega
      obtain ⟨pA5, hpA5⟩ := mk a0 b c0 h0b h02 hb2 (3*t/2) (1 - 3*t/2) 0 (by linarith) (by linarith)
        le_rfl (by ring)
      obtain ⟨pZ5, hpZ5⟩ := mk a0 b c0 h0b h02 hb2 0 (1 - 3*t/2) (3*t/2) le_rfl (by linarith)
        (by linarith) (by ring)
      obtain ⟨δa, hδa⟩ := mk a0 b c0 h0b h02 hb2 1 0 0 (by norm_num) le_rfl le_rfl (by norm_num)
      obtain ⟨δb, hδb⟩ := mk a0 b c0 h0b h02 hb2 0 1 0 le_rfl (by norm_num) le_rfl (by norm_num)
      obtain ⟨δc, hδc⟩ := mk a0 b c0 h0b h02 hb2 0 0 1 le_rfl le_rfl (by norm_num) (by norm_num)
      obtain ⟨P5, hP5⟩ : ∃ P : Profile n m,
          P = fun i => if i = A then pA5 else if i = Z then pZ5 else δb := ⟨_, rfl⟩
      have hP5A : P5 A = pA5 := by rw [hP5]; simp
      have hP5Z : P5 Z = pZ5 := by rw [hP5]; simp [hAZ.symm]
      have hP5O : ∀ i, i ≠ A → i ≠ Z → P5 i = δb := by intro i h1 h2; rw [hP5]; simp [h1, h2]
      have hδbv : ∀ j, δb.1 j = if j = b then 1 else 0 := by intro j; rw [hδb]; simp
      have vpA5 : ∀ j, j ≠ a0 → j ≠ b → j ≠ c0 → pA5.1 j = 0 := by
        intro j h1 h2 h3; rw [hpA5]; simp [h1, h2, h3]
      have vpZ5 : ∀ j, j ≠ a0 → j ≠ b → j ≠ c0 → pZ5.1 j = 0 := by
        intro j h1 h2 h3; rw [hpZ5]; simp [h1, h2, h3]
      have vP5 : ∀ i j, j ≠ a0 → j ≠ b → j ≠ c0 → (P5 i).1 j = 0 := by
        intro i j h1 h2 h3
        by_cases hiA : i = A
        · rw [hiA, hP5A]; exact vpA5 j h1 h2 h3
        by_cases hiZ : i = Z
        · rw [hiZ, hP5Z]; exact vpZ5 j h1 h2 h3
        rw [hP5O i hiA hiZ, hδbv]; simp [h2]
      have k1A : ∀ j, (Function.update P5 Z δc A).1 j =
          (if j = a0 then 3*t/2 else 0) + (if j = b then 1 - 3*t/2 else 0) := by
        intro j; rw [Function.update_of_ne hAZ, hP5A, hpA5]; simp
      have k1Z : ∀ j, (Function.update P5 Z δc Z).1 j = if j = c0 then 1 else 0 := by
        intro j; rw [Function.update_self, hδc]; simp
      have k1O : ∀ i, i ≠ A → i ≠ Z → ∀ j, (Function.update P5 Z δc i).1 j = if j = b then 1 else 0 := by
        intro i h1 h2 j; rw [Function.update_of_ne h2, hP5O i h1 h2, hδbv]
      have k6A : ∀ j, (Function.update P5 A δa Z).1 j =
          (if j = c0 then 3*t/2 else 0) + (if j = b then 1 - 3*t/2 else 0) := by
        intro j; rw [Function.update_of_ne hAZ.symm, hP5Z, hpZ5]; simp only [ite_self, zero_add]; ring
      have k6Z : ∀ j, (Function.update P5 A δa A).1 j = if j = a0 then 1 else 0 := by
        intro j; rw [Function.update_self, hδa]; simp
      have k6O : ∀ i, i ≠ Z → i ≠ A → ∀ j, (Function.update P5 A δa i).1 j = if j = b then 1 else 0 := by
        intro i h1 h2 j; rw [Function.update_of_ne h2, hP5O i h2 h1, hδbv]
      have hB5 : ∀ j, (P5 B).1 j = if j = b then 1 else 0 := by rw [hP5O B hBA hBZ]; exact hδbv
      have hA5a : pA5.1 a0 = 3*t/2 := by rw [hpA5]; simp [h0b, h02]
      have hA5b : pA5.1 b = 1 - 3*t/2 := by rw [hpA5]; simp [hb0, hb2]
      have hA5c : pA5.1 c0 = 0 := by rw [hpA5]; simp [h20, h2b]
      have hZ5a : pZ5.1 a0 = 0 := by rw [hpZ5]; simp [h0b, h02]
      have hZ5b : pZ5.1 b = 1 - 3*t/2 := by rw [hpZ5]; simp [hb0, hb2]
      have hZ5c : pZ5.1 c0 = 3*t/2 := by rw [hpZ5]; simp [h20, h2b]
      have H_e : ∀ (a c : Fin m), a ≠ b → c ≠ b → a ≠ c → ∀ (Q : Profile n m) (B : Fin n),
          (∀ i j, j ≠ a → j ≠ b → j ≠ c → (Q i).1 j = 0) →
          (∀ j, (Q B).1 j = if j = b then 1 else 0) →
          (f Q).1 a + (f Q).1 b + (f Q).1 c = 1 := by
        clear ha0 hc0 h0b h2b h02 hb0 hb2 h20 hA hZ hB hAZ hBA hBZ hpA5 hpZ5 hδa hδb hδc hP5A hP5Z hP5O hδbv vpA5 vpZ5 vP5 k1A k1Z k1O k6A k6Z k6O hB5 hA5a hA5b hA5c hZ5a hZ5b hZ5c hP5 P5 pA5 pZ5 δa δb δc A Z B a0 c0
        intro a c hab hcb hac Q B hQ hB
        have hbc : b ≠ c := hcb.symm
        have hle := hle3 a b c hab hac hbc (f Q)
        by_contra hne
        have hlt : (f Q).1 a + (f Q).1 b + (f Q).1 c < 1 := lt_of_le_of_ne hle hne
        have qa0 := (f Q).2.1 a
        have qb0 := (f Q).2.1 b
        have qc0 := (f Q).2.1 c
        obtain ⟨q', hq'⟩ := mk a b c hab hac hbc ((f Q).1 a) (1 - (f Q).1 a - (f Q).1 c) ((f Q).1 c)
          qa0 (by linarith) qc0 (by ring)
        have e1 : q'.1 a = (f Q).1 a := by rw [hq']; simp [hab, hac]
        have e2 : q'.1 b = 1 - (f Q).1 a - (f Q).1 c := by rw [hq']; simp [hab.symm, hbc]
        have e3 : q'.1 c = (f Q).1 c := by rw [hq']; simp [hac.symm, hbc.symm]
        apply hE Q
        refine ⟨q', fun i => ?_, B, ?_⟩
        · rw [hd a b c hab hac hbc (Q i) (f Q) (hQ i), hd a b c hab hac hbc (Q i) q' (hQ i), e1, e2, e3]
          have : |(Q i).1 b - (1 - (f Q).1 a - (f Q).1 c)| ≤ |(Q i).1 b - (f Q).1 b| +
              (1 - (f Q).1 a - (f Q).1 b - (f Q).1 c) :=
            abs_le.mpr ⟨by linarith [neg_abs_le ((Q i).1 b - (f Q).1 b)],
              by linarith [le_abs_self ((Q i).1 b - (f Q).1 b)]⟩
          linarith
        · have hBa : (Q B).1 a = 0 := by rw [hB]; simp [hab]
          have hBb : (Q B).1 b = 1 := by rw [hB]; simp
          have hBc : (Q B).1 c = 0 := by rw [hB]; simp [hcb]
          rw [hd a b c hab hac hbc (Q B) (f Q) (hQ B), hd a b c hab hac hbc (Q B) q' (hQ B), e1, e2, e3,
            hBa, hBb, hBc]
          rw [abs_of_nonpos (by linarith : (0:ℝ) - (f Q).1 a ≤ 0),
            abs_of_nonpos (by linarith : (0:ℝ) - (f Q).1 c ≤ 0),
            abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - (f Q).1 b),
            abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - (1 - (f Q).1 a - (f Q).1 c))]
          linarith
      have H_tr : ∀ (a c : Fin m), a ≠ b → c ≠ b → a ≠ c → ∀ (Q : Profile n m) (B : Fin n),
          (∀ i j, j ≠ a → j ≠ b → j ≠ c → (Q i).1 j = 0) →
          (∀ j, (Q B).1 j = if j = b then 1 else 0) →
          ∀ ε : ℝ, 0 < ε → ε ≤ (f Q).1 a →
          (∀ i, (Q i).1 a = 0 ∨ (f Q).1 b + ε ≤ (Q i).1 b) → False := by
        clear ha0 hc0 h0b h2b h02 hb0 hb2 h20 hA hZ hB hAZ hBA hBZ hpA5 hpZ5 hδa hδb hδc hP5A hP5Z hP5O hδbv vpA5 vpZ5 vP5 k1A k1Z k1O k6A k6Z k6O hB5 hA5a hA5b hA5c hZ5a hZ5b hZ5c hP5 P5 pA5 pZ5 δa δb δc A Z B a0 c0
        intro a c hab hcb hac Q B hQ hB ε hε hεa hi
        have hbc : b ≠ c := hcb.symm
        have hs := H_e a c hab hcb hac Q B hQ hB
        have qa0 := (f Q).2.1 a
        have qb0 := (f Q).2.1 b
        have qc0 := (f Q).2.1 c
        obtain ⟨q', hq'⟩ := mk a b c hab hac hbc ((f Q).1 a - ε) ((f Q).1 b + ε) ((f Q).1 c)
          (by linarith) (by linarith) qc0 (by linarith)
        have e1 : q'.1 a = (f Q).1 a - ε := by rw [hq']; simp [hab, hac]
        have e2 : q'.1 b = (f Q).1 b + ε := by rw [hq']; simp [hab.symm, hbc]
        have e3 : q'.1 c = (f Q).1 c := by rw [hq']; simp [hac.symm, hbc.symm]
        apply hE Q
        refine ⟨q', fun i => ?_, B, ?_⟩
        · rw [hd a b c hab hac hbc (Q i) (f Q) (hQ i), hd a b c hab hac hbc (Q i) q' (hQ i), e1, e2, e3]
          rcases hi i with h | h
          · rw [h]
            have : |(Q i).1 b - ((f Q).1 b + ε)| ≤ |(Q i).1 b - (f Q).1 b| + ε :=
              abs_le.mpr ⟨by linarith [neg_abs_le ((Q i).1 b - (f Q).1 b)],
                by linarith [le_abs_self ((Q i).1 b - (f Q).1 b)]⟩
            rw [abs_of_nonpos (by linarith : (0:ℝ) - ((f Q).1 a - ε) ≤ 0),
              abs_of_nonpos (by linarith : (0:ℝ) - (f Q).1 a ≤ 0)]
            linarith
          · have : |(Q i).1 a - ((f Q).1 a - ε)| ≤ |(Q i).1 a - (f Q).1 a| + ε :=
              abs_le.mpr ⟨by linarith [neg_abs_le ((Q i).1 a - (f Q).1 a)],
                by linarith [le_abs_self ((Q i).1 a - (f Q).1 a)]⟩
            rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ (Q i).1 b - ((f Q).1 b + ε)),
              abs_of_nonneg (by linarith : (0:ℝ) ≤ (Q i).1 b - (f Q).1 b)]
            linarith
        · have hBa : (Q B).1 a = 0 := by rw [hB]; simp [hab]
          have hBb : (Q B).1 b = 1 := by rw [hB]; simp
          have hBc : (Q B).1 c = 0 := by rw [hB]; simp [hcb]
          rw [hd a b c hab hac hbc (Q B) (f Q) (hQ B), hd a b c hab hac hbc (Q B) q' (hQ B), e1, e2, e3,
            hBa, hBb, hBc]
          rw [abs_of_nonpos (by linarith : (0:ℝ) - (f Q).1 a ≤ 0),
            abs_of_nonpos (by linarith : (0:ℝ) - ((f Q).1 a - ε) ≤ 0),
            abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - (f Q).1 b),
            abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - ((f Q).1 b + ε))]
          linarith
      have key : ∀ (a c : Fin m) (A Z : Fin n), a ≠ b → c ≠ b → a ≠ c → A ≠ Z →
          ∀ (P : Profile n m),
          (∀ j, (P A).1 j = (if j = a then 3*t/2 else 0) + (if j = b then 1 - 3*t/2 else 0)) →
          (∀ j, (P Z).1 j = if j = c then 1 else 0) →
          (∀ i, i ≠ A → i ≠ Z → ∀ j, (P i).1 j = if j = b then 1 else 0) →
          (f P).1 a = t/2 ∧ (f P).1 b = 1 - 3*t/2 ∧ (f P).1 c = t := by
        clear ha0 hc0 h0b h2b h02 hb0 hb2 h20 hA hZ hB hAZ hBA hBZ hpA5 hpZ5 hδa hδb hδc hP5A hP5Z hP5O hδbv vpA5 vpZ5 vP5 k1A k1Z k1O k6A k6Z k6O hB5 hA5a hA5b hA5c hZ5a hZ5b hZ5c hP5 P5 pA5 pZ5 δa δb δc A Z B a0 c0
        intro a c A Z hab hcb hac hAZ P hPA hPZ hPO
        have hbc : b ≠ c := hcb.symm
        have hba : b ≠ a := hab.symm
        have hca : c ≠ a := hac.symm
        obtain ⟨B, hBA, hBZ⟩ : ∃ B : Fin n, B ≠ A ∧ B ≠ Z := by
          by_contra hcon
          push Not at hcon
          have h0 := hcon ⟨0, by omega⟩
          have h1 := hcon ⟨1, by omega⟩
          have h2 := hcon ⟨2, by omega⟩
          simp only [ne_eq, Fin.ext_iff] at h0 h1 h2
          omega
        have hvanP : ∀ i j, j ≠ a → j ≠ b → j ≠ c → (P i).1 j = 0 := by
          intro i j hja hjb hjc
          by_cases hiA : i = A
          · subst hiA; rw [hPA]; simp [hja, hjb]
          by_cases hiZ : i = Z
          · subst hiZ; rw [hPZ]; simp [hjc]
          rw [hPO i hiA hiZ]; simp [hjb]
        have hPa0 : ∀ i, i ≠ A → (P i).1 a = 0 := by
          intro i hiA
          by_cases hiZ : i = Z
          · subst hiZ; rw [hPZ]; simp [hac]
          rw [hPO i hiA hiZ]; simp [hab]
        have hBP : ∀ j, (P B).1 j = if j = b then 1 else 0 := hPO B hBA hBZ
        have hPAa : (P A).1 a = 3*t/2 := by rw [hPA]; simp [hab]
        have hPAb : (P A).1 b = 1 - 3*t/2 := by rw [hPA]; simp [hab.symm]
        have hPAc : (P A).1 c = 0 := by rw [hPA]; simp [hac.symm, hbc.symm]
        obtain ⟨δa, hδa⟩ := mk a b c hab hac hbc 1 0 0 (by norm_num) le_rfl le_rfl (by norm_num)
        obtain ⟨δb, hδb⟩ := mk a b c hab hac hbc 0 1 0 le_rfl (by norm_num) le_rfl (by norm_num)
        obtain ⟨p3, hp3⟩ := mk a b c hab hac hbc (3*t/4) (1 - 3*t/4) 0 (by linarith) (by linarith)
          le_rfl (by ring)
        have vδa : ∀ j, j ≠ a → j ≠ b → j ≠ c → δa.1 j = 0 := by
          intro j h1 h2 h3; rw [hδa]; simp [h1, h2, h3]
        have vδb : ∀ j, j ≠ a → j ≠ b → j ≠ c → δb.1 j = 0 := by
          intro j h1 h2 h3; rw [hδb]; simp [h1, h2, h3]
        have vp3 : ∀ j, j ≠ a → j ≠ b → j ≠ c → p3.1 j = 0 := by
          intro j h1 h2 h3; rw [hp3]; simp [h1, h2, h3]
        have hvanU : ∀ p' : stdSimplex ℝ (Fin m), (∀ j, j ≠ a → j ≠ b → j ≠ c → p'.1 j = 0) →
            ∀ i j, j ≠ a → j ≠ b → j ≠ c → (Function.update P A p' i).1 j = 0 := by
          intro p' hp' i j hja hjb hjc
          by_cases hiA : i = A
          · subst hiA; rw [Function.update_self]; exact hp' j hja hjb hjc
          rw [Function.update_of_ne hiA]; exact hvanP i j hja hjb hjc
        have hBU : ∀ p' : stdSimplex ℝ (Fin m), ∀ j,
            (Function.update P A p' B).1 j = if j = b then 1 else 0 := by
          intro p' j; rw [Function.update_of_ne hBA]; exact hPO B hBA hBZ j
        have hda := hd a b c hab hac hbc
        have E2 := H_e a c hab hcb hac _ B (hvanU δa vδa) (hBU δa)
        have E4 := H_e a c hab hcb hac _ B (hvanU δb vδb) (hBU δb)
        have hs3 := H_e a c hab hcb hac _ B (hvanU p3 vp3) (hBU p3)
        have hs1 := H_e a c hab hcb hac P B hvanP hBP
        have T1 := H_tr a c hab hcb hac P B hvanP hBP
        have T3 := H_tr a c hab hcb hac _ B (hvanU p3 vp3) (hBU p3)
        clear H_e H_tr mk hd hle3 hvanU hBU
        -- the outcome at P
        have x10 := (f P).2.1 a
        have y10 := (f P).2.1 b
        have z10 := (f P).2.1 c
        -- Profile 2
        have hSM2 : IsSingleMinded (Function.update P A δa) := by
          intro i j
          by_cases hiA : i = A
          · rw [hiA, Function.update_self, hδa]; split_ifs <;> norm_num
          rw [Function.update_of_ne hiA]
          by_cases hiZ : i = Z
          · rw [hiZ, hPZ]; split_ifs <;> norm_num
          rw [hPO i hiA hiZ]; split_ifs <;> norm_num
        have hq2a : (f (Function.update P A δa)).1 a = t := by
          rw [hPr _ hSM2 a]
          have : ∀ i, (Function.update P A δa i).1 a = if i = A then 1 else 0 := by
            intro i
            by_cases hiA : i = A
            · rw [hiA, Function.update_self, hδa]; simp [hab, hac]
            rw [Function.update_of_ne hiA, if_neg hiA, hPa0 i hiA]
          simp [this, ht]
        have hq2c : (f (Function.update P A δa)).1 c = t := by
          rw [hPr _ hSM2 c]
          have : ∀ i, (Function.update P A δa i).1 c = if i = Z then 1 else 0 := by
            intro i
            by_cases hiA : i = A
            · rw [hiA, Function.update_self, hδa]; simp [hac.symm, hbc.symm, hAZ]
            rw [Function.update_of_ne hiA]
            by_cases hiZ : i = Z
            · rw [hiZ, hPZ]; simp
            rw [hPO i hiA hiZ, if_neg hiZ]; simp [hbc.symm]
          simp [this, ht]
        have hq2b : (f (Function.update P A δa)).1 b = 1 - 2*t := by
          have := E2
          linarith
        -- (9)
        have h9 := hSP A P (Function.update P A δa) (fun j hj => Function.update_of_ne hj _ _)
        rw [hda (P A) _ (hvanP A), hda (P A) _ (hvanP A), hPAa, hPAb, hPAc, hq2a, hq2b, hq2c] at h9
        have hx1lo : t/2 ≤ (f P).1 a := by
          linarith [abs_of_nonneg (show (0:ℝ) ≤ 3*t/2 - t by linarith),
            abs_of_nonneg (show (0:ℝ) ≤ 1 - 3*t/2 - (1 - 2*t) by linarith),
            abs_of_nonpos (show (0:ℝ) - t ≤ 0 by linarith),
            le_abs_self (3*t/2 - (f P).1 a), neg_abs_le (3*t/2 - (f P).1 a),
            le_abs_self (1 - 3*t/2 - (f P).1 b), neg_abs_le (1 - 3*t/2 - (f P).1 b),
            le_abs_self (0 - (f P).1 c), neg_abs_le (0 - (f P).1 c)]
        -- (10)
        have h10 := hSP A (Function.update P A δa) P (fun j hj => (Function.update_of_ne hj _ _).symm)
        have hδaa : δa.1 a = 1 := by rw [hδa]; simp [hab, hac]
        have hδab : δa.1 b = 0 := by rw [hδa]; simp [hba, hca, hcb]
        have hδac : δa.1 c = 0 := by rw [hδa]; simp [hba, hca, hcb]
        rw [Function.update_self, hda δa _ vδa, hda δa _ vδa, hδaa, hδab, hδac, hq2a, hq2b, hq2c] at h10
        have hx1hi : (f P).1 a ≤ t := by
          linarith [abs_of_nonneg (show (0:ℝ) ≤ 1 - t by linarith),
            abs_of_nonpos (show (0:ℝ) - (1 - 2*t) ≤ 0 by linarith),
            abs_of_nonpos (show (0:ℝ) - t ≤ 0 by linarith),
            abs_of_nonneg (show (0:ℝ) ≤ 1 - (f P).1 a by linarith),
            abs_of_nonpos (show (0:ℝ) - (f P).1 b ≤ 0 by linarith),
            abs_of_nonpos (show (0:ℝ) - (f P).1 c ≤ 0 by linarith)]
        -- efficiency at P
        have hy1lo : 1 - 3*t/2 ≤ (f P).1 b := by
          by_contra hlt
          push Not at hlt
          apply T1 (min ((f P).1 a) (1 - 3*t/2 - (f P).1 b))
            (lt_min (by linarith) (by linarith)) (min_le_left _ _)
          intro i
          by_cases hiA : i = A
          · right; rw [hiA, hPAb]; linarith [min_le_right ((f P).1 a) (1 - 3*t/2 - (f P).1 b)]
          · left; exact hPa0 i hiA
        clear h9 h10 T1 hq2a hq2b hq2c hSM2 E2
        -- Profile 4
        have hSM4 : IsSingleMinded (Function.update P A δb) := by
          intro i j
          by_cases hiA : i = A
          · rw [hiA, Function.update_self, hδb]; split_ifs <;> norm_num
          rw [Function.update_of_ne hiA]
          by_cases hiZ : i = Z
          · rw [hiZ, hPZ]; split_ifs <;> norm_num
          rw [hPO i hiA hiZ]; split_ifs <;> norm_num
        have hq4a : (f (Function.update P A δb)).1 a = 0 := by
          rw [hPr _ hSM4 a]
          have : ∀ i, (Function.update P A δb i).1 a = 0 := by
            intro i
            by_cases hiA : i = A
            · rw [hiA, Function.update_self, hδb]; simp [hab, hac]
            rw [Function.update_of_ne hiA, hPa0 i hiA]
          simp [this]
        have hq4c : (f (Function.update P A δb)).1 c = t := by
          rw [hPr _ hSM4 c]
          have : ∀ i, (Function.update P A δb i).1 c = if i = Z then 1 else 0 := by
            intro i
            by_cases hiA : i = A
            · rw [hiA, Function.update_self, hδb]; simp [hac.symm, hbc.symm, hAZ]
            rw [Function.update_of_ne hiA]
            by_cases hiZ : i = Z
            · rw [hiZ, hPZ]; simp
            rw [hPO i hiA hiZ, if_neg hiZ]; simp [hbc.symm]
          simp [this, ht]
        have hq4b : (f (Function.update P A δb)).1 b = 1 - t := by
          have := E4
          linarith
        -- Profile 3
        have hp3a : p3.1 a = 3*t/4 := by rw [hp3]; simp [hab]
        have hp3b : p3.1 b = 1 - 3*t/4 := by rw [hp3]; simp [hab.symm]
        have hp3c : p3.1 c = 0 := by rw [hp3]; simp [hba, hca, hcb]
        have hδba : δb.1 a = 0 := by rw [hδb]; simp [hab]
        have hδbb : δb.1 b = 1 := by rw [hδb]; simp [hab.symm]
        have hδbc : δb.1 c = 0 := by rw [hδb]; simp [hba, hca, hcb]
        have x30 := (f (Function.update P A p3)).2.1 a
        have y30 := (f (Function.update P A p3)).2.1 b
        have z30 := (f (Function.update P A p3)).2.1 c
        have h11 := hSP A (Function.update P A p3) (Function.update P A δb) (fun j hj => by
          rw [Function.update_of_ne hj, Function.update_of_ne hj])
        rw [Function.update_self, hda p3 _ vp3, hda p3 _ vp3, hp3a, hp3b, hp3c, hq4a, hq4b, hq4c] at h11
        have hz3 : (f (Function.update P A p3)).1 c ≤ t := by
          linarith [abs_of_nonneg (show (0:ℝ) ≤ 3*t/4 - 0 by linarith),
            abs_of_nonneg (show (0:ℝ) ≤ 1 - 3*t/4 - (1 - t) by linarith),
            abs_of_nonpos (show (0:ℝ) - t ≤ 0 by linarith),
            le_abs_self (3*t/4 - (f (Function.update P A p3)).1 a),
            le_abs_self (1 - 3*t/4 - (f (Function.update P A p3)).1 b),
            neg_abs_le (0 - (f (Function.update P A p3)).1 c)]
        have h12 := hSP A (Function.update P A δb) (Function.update P A p3) (fun j hj => by
          rw [Function.update_of_ne hj, Function.update_of_ne hj])
        rw [Function.update_self, hda δb _ vδb, hda δb _ vδb, hδba, hδbb, hδbc, hq4a, hq4b, hq4c] at h12
        have hy3 : (f (Function.update P A p3)).1 b ≤ 1 - t := by
          linarith [abs_of_nonpos (show (0:ℝ) - 0 ≤ 0 by linarith),
            abs_of_nonneg (show (0:ℝ) ≤ 1 - (1 - t) by linarith),
            abs_of_nonpos (show (0:ℝ) - t ≤ 0 by linarith),
            abs_of_nonpos (show (0:ℝ) - (f (Function.update P A p3)).1 a ≤ 0 by linarith),
            abs_of_nonneg (show (0:ℝ) ≤ 1 - (f (Function.update P A p3)).1 b by linarith),
            abs_of_nonpos (show (0:ℝ) - (f (Function.update P A p3)).1 c ≤ 0 by linarith)]
        have hx3 : (f (Function.update P A p3)).1 a = 0 := by
          by_contra hne
          have hpos : 0 < (f (Function.update P A p3)).1 a := lt_of_le_of_ne x30 (Ne.symm hne)
          apply T3
            (min ((f (Function.update P A p3)).1 a) (1 - 3*t/4 - (f (Function.update P A p3)).1 b))
            (lt_min hpos (by linarith)) (min_le_left _ _)
          intro i
          by_cases hiA : i = A
          · right; rw [hiA, Function.update_self, hp3b]
            linarith [min_le_right ((f (Function.update P A p3)).1 a)
              (1 - 3*t/4 - (f (Function.update P A p3)).1 b)]
          · left; rw [Function.update_of_ne hiA]; exact hPa0 i hiA
        clear h11 h12 T3 E4 hSM4 hq4a hq4b hq4c hPr hE
        have hy3' : (f (Function.update P A p3)).1 b = 1 - t := by linarith
        have hz3' : (f (Function.update P A p3)).1 c = t := by linarith
        -- (13)
        have h13 := hSP A (Function.update P A p3) P (fun j hj => (Function.update_of_ne hj _ _).symm)
        rw [Function.update_self, hda p3 _ vp3, hda p3 _ vp3, hp3a, hp3b, hp3c, hx3, hy3', hz3'] at h13
        have hc1 : |(0:ℝ) - (f P).1 c| = (f P).1 c := by
          rw [abs_of_nonpos (by linarith)]; ring
        have hk1 : |3*t/4 - 0| + |1 - 3*t/4 - (1 - t)| + |(0:ℝ) - t| = 2 * t := by
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
          ring
        have hfin : (f P).1 a = t/2 ∧ (f P).1 b = 1 - 3*t/2 := by
          rcases le_total 0 (3*t/4 - (f P).1 a) with h1 | h1 <;>
          rcases le_total 0 (1 - 3*t/4 - (f P).1 b) with h2 | h2
          · rw [abs_of_nonneg h1, abs_of_nonneg h2] at h13
            constructor <;> linarith
          · rw [abs_of_nonneg h1, abs_of_nonpos h2] at h13
            exfalso; linarith
          · rw [abs_of_nonpos h1, abs_of_nonneg h2] at h13
            exfalso; linarith
          · rw [abs_of_nonpos h1, abs_of_nonpos h2] at h13
            exfalso; linarith
        exact ⟨hfin.1, hfin.2, by linarith⟩
      have k1 := key a0 c0 A Z h0b h2b h02 hAZ (Function.update P5 Z δc) k1A k1Z k1O
      have k6 := key c0 a0 Z A h2b h0b h02.symm hAZ.symm (Function.update P5 A δa) k6A k6Z k6O
      have hs5 := H_e a0 c0 h0b h2b h02 P5 B vP5 hB5
      clear key H_tr H_e mk hle3 k1A k1Z k1O k6A k6Z k6O hB5 vP5 hP5O hP5 hδbv hδa hδb hδc
      have x50 := (f P5).2.1 a0
      have y50 := (f P5).2.1 b
      have z50 := (f P5).2.1 c0
      have hd0 := hd a0 b c0 h0b h02 hb2
      clear hd
      have s1 := hSP A P5 (Function.update P5 A δa) (fun j hj => Function.update_of_ne hj _ _)
      rw [hP5A, hd0 pA5 _ vpA5, hd0 pA5 _ vpA5, hA5a, hA5b, hA5c, k6.1, k6.2.1, k6.2.2] at s1
      have s2 := hSP Z P5 (Function.update P5 Z δc) (fun j hj => Function.update_of_ne hj _ _)
      rw [hP5Z, hd0 pZ5 _ vpZ5, hd0 pZ5 _ vpZ5, hZ5a, hZ5b, hZ5c, k1.1, k1.2.1, k1.2.2] at s2
      have u1 : (f P5).1 c0 ≤ t/2 := by
        linarith only [s1, hs5, ht0, x50, y50, z50,
          abs_of_nonneg (show (0:ℝ) ≤ 3*t/2 - t by linarith only [ht0]),
          abs_of_nonneg (show (0:ℝ) ≤ 1 - 3*t/2 - (1 - 3*t/2) by linarith only [ht0]),
          abs_of_nonpos (show (0:ℝ) - t/2 ≤ 0 by linarith only [ht0]),
          le_abs_self (3*t/2 - (f P5).1 a0), le_abs_self (1 - 3*t/2 - (f P5).1 b),
          neg_abs_le (0 - (f P5).1 c0)]
      have u2 : t ≤ (f P5).1 c0 := by
        linarith only [s2, hs5, ht0, x50, y50, z50,
          abs_of_nonpos (show (0:ℝ) - t/2 ≤ 0 by linarith only [ht0]),
          abs_of_nonneg (show (0:ℝ) ≤ 1 - 3*t/2 - (1 - 3*t/2) by linarith only [ht0]),
          abs_of_nonneg (show (0:ℝ) ≤ 3*t/2 - t by linarith only [ht0]),
          neg_abs_le (0 - (f P5).1 a0), neg_abs_le (1 - 3*t/2 - (f P5).1 b),
          le_abs_self (3*t/2 - (f P5).1 c0)]
      linarith only [u1, u2, ht0]
