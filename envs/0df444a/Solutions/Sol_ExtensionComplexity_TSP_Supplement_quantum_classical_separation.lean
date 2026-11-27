-- Prove2me | solution 1 for ExtensionComplexity.TSP.Supplement.quantum_classical_separation
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:23:16.237001+00:00
-- url     : https://prove2.me/submissions/b4fe8464-cc49-4c03-96b0-822e8891a498

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_Supplement_OneWayProtocol
import Definitions.Def_ExtensionComplexity_TSP_Supplement_ClassicalProtocol

open ExtensionComplexity
open ExtensionComplexity.TSP
open ExtensionComplexity.TSP.Supplement

/-- Theorem 18, p. 17:19: rows and columns are indexed by `n`-bit strings (`2^n × 2^n`); a
`k`-qubit message is a state of dimension `2^k` (p. 17:16). The `O(1)` and `Ω(n)` constants are
uniform in `n`; the classical clause quantifies over every private-coin protocol. -/
theorem solution :
    ∃ C₁ : ℝ, ∃ C₂ : ℝ, 0 < C₂ ∧ ∃ N : ℕ, ∀ n : ℕ, 1 ≤ n →
      ∃ M : Matrix (Fin n → Bool) (Fin n → Bool) ℝ, (∀ a b, 0 ≤ M a b) ∧
        (∃ k : ℕ, (k : ℝ) ≤ Real.logb 2 n + C₁ ∧
          ∃ P : OneWayProtocol (Fin n → Bool) (Fin n → Bool) (2 ^ k), P.Computes M) ∧
        (N ≤ n → ∀ P : ClassicalProtocol (Fin n → Bool) (Fin n → Bool),
          P.Computes M → C₂ * n ≤ P.cost) := by
            classical
            have hsplit : ∀ (m : ℕ) (f : (Fin (m+1) → Bool) → ℕ),
                ∑ x, f x = ∑ α : Bool, ∑ x' : Fin m → Bool, f (Fin.cons α x') := by
              intro m f
              rw [← Fintype.sum_prod_type']
              exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => Bool)) _ _ (fun x => rfl)).symm
            obtain ⟨ip, hip⟩ : ∃ ip : ∀ m : ℕ, (Fin m → Bool) → (Fin m → Bool) → ℕ,
                ∀ m a b, ip m a b = ∑ k, if (a k && b k) then 1 else 0 := ⟨_, fun _ _ _ => rfl⟩
            have hipc : ∀ m (α β : Bool) (a b : Fin m → Bool),
                ip (m+1) (Fin.cons α a) (Fin.cons β b) = (if (α && β) then 1 else 0) + ip m a b := by
              intro m α β a b
              rw [hip, hip, Fin.sum_univ_succ]
              simp
            have KW : ∀ m (A B : (Fin m → Bool) → Prop), (∀ a b, A a → B b → ip m a b ≠ 1) →
                ∑ a, ∑ b, (if A a ∧ B b ∧ ip m a b = 0 then 1 else 0) ≤ 2 ^ m := by
              intro m
              induction m with
              | zero =>
                intro A B _
                calc _ ≤ ∑ a : Fin 0 → Bool, ∑ b : Fin 0 → Bool, 1 :=
                      Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => by split_ifs <;> omega
                  _ = 2 ^ 0 := by simp
              | succ m ih =>
                intro A B hAB
                calc _ = ∑ a' : Fin m → Bool, ∑ b' : Fin m → Bool,
                      ((if A (Fin.cons true a') ∧ B (Fin.cons true b') ∧
                          ip (m+1) (Fin.cons true a') (Fin.cons true b') = 0 then 1 else 0) +
                       (if A (Fin.cons true a') ∧ B (Fin.cons false b') ∧
                          ip (m+1) (Fin.cons true a') (Fin.cons false b') = 0 then 1 else 0) +
                       (if A (Fin.cons false a') ∧ B (Fin.cons true b') ∧
                          ip (m+1) (Fin.cons false a') (Fin.cons true b') = 0 then 1 else 0) +
                       (if A (Fin.cons false a') ∧ B (Fin.cons false b') ∧
                          ip (m+1) (Fin.cons false a') (Fin.cons false b') = 0 then 1 else 0)) := by
                      simp only [hsplit (m := m), Fintype.sum_bool, Finset.sum_add_distrib]
                      ring
                  _ ≤ ∑ a' : Fin m → Bool, ∑ b' : Fin m → Bool,
                      ((if (A (Fin.cons false a') ∨ A (Fin.cons true a')) ∧ B (Fin.cons false b') ∧
                          ip m a' b' = 0 then 1 else 0) +
                       (if A (Fin.cons false a') ∧ (B (Fin.cons false b') ∨ B (Fin.cons true b')) ∧
                          ip m a' b' = 0 then 1 else 0)) := by
                      refine Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ => ?_
                      have hc := hAB (Fin.cons true a') (Fin.cons true b')
                      simp only [hipc] at hc ⊢
                      by_cases h1 : A (Fin.cons true a') <;> by_cases h0 : A (Fin.cons false a') <;>
                        by_cases g1 : B (Fin.cons true b') <;> by_cases g0 : B (Fin.cons false b') <;>
                        by_cases hd : ip m a' b' = 0 <;> simp [h1, h0, g1, g0, hd] at hc ⊢
                  _ = ∑ a' : Fin m → Bool, ∑ b' : Fin m → Bool,
                      (if (A (Fin.cons false a') ∨ A (Fin.cons true a')) ∧ B (Fin.cons false b') ∧
                          ip m a' b' = 0 then 1 else 0) +
                      ∑ a' : Fin m → Bool, ∑ b' : Fin m → Bool,
                       (if A (Fin.cons false a') ∧ (B (Fin.cons false b') ∨ B (Fin.cons true b')) ∧
                          ip m a' b' = 0 then 1 else 0) := by
                      simp only [Finset.sum_add_distrib]
                  _ ≤ 2 ^ m + 2 ^ m := by
                      apply add_le_add
                      · have h := ih (fun a' => A (Fin.cons false a') ∨ A (Fin.cons true a'))
                          (fun b' => B (Fin.cons false b')) (by
                            intro a b ha hb
                            have := hipc m true false a b
                            have := hipc m false false a b
                            rcases ha with ha | ha
                            · have := hAB _ _ ha hb; simp_all
                            · have := hAB _ _ ha hb; simp_all)
                        refine le_trans (le_of_eq ?_) h
                        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
                        split_ifs <;> rfl
                      · have h := ih (fun a' => A (Fin.cons false a'))
                          (fun b' => B (Fin.cons false b') ∨ B (Fin.cons true b')) (by
                            intro a b ha hb
                            have := hipc m false true a b
                            have := hipc m false false a b
                            rcases hb with hb | hb
                            · have := hAB _ _ ha hb; simp_all
                            · have := hAB _ _ ha hb; simp_all)
                        refine le_trans (le_of_eq ?_) h
                        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
                        split_ifs <;> rfl
                  _ = 2 ^ (m+1) := by ring
            have count : ∀ m, ∑ a : Fin m → Bool, ∑ b : Fin m → Bool,
                (if ip m a b = 0 then 1 else 0) = 3 ^ m := by
              intro m
              induction m with
              | zero => simp [hip]
              | succ m ih =>
                have e1 : ∀ x : ℕ, (if 1 + x = 0 then 1 else 0 : ℕ) = 0 := by intro x; simp
                have e0 : ∀ x : ℕ, (if 0 + x = 0 then 1 else 0 : ℕ) = if x = 0 then 1 else 0 := by
                  intro x; simp
                simp only [hsplit (m := m), Fintype.sum_bool, Finset.sum_add_distrib, hipc]
                simp only [Bool.and_true, Bool.and_false, if_true, Bool.false_eq_true, if_false, e1, e0,
                  Finset.sum_const_zero, ih]
                ring
            refine ⟨1, 1/2, by norm_num, 0, fun n hn => ?_⟩
            have hnn : ∀ P : ClassicalProtocol (Fin n → Bool) (Fin n → Bool), ∀ a b,
                0 ≤ P.expectedOutput a b := by
              intro P
              induction P with
              | aliceOutputs f hf => intro a b; exact hf a
              | bobOutputs g hg => intro a b; exact hg b
              | aliceSends p hp c0 c1 ih0 ih1 =>
                intro a b
                exact add_nonneg (mul_nonneg (sub_nonneg.2 (hp a).2) (ih0 a b)) (mul_nonneg (hp a).1 (ih1 a b))
              | bobSends q hq c0 c1 ih0 ih1 =>
                intro a b
                exact add_nonneg (mul_nonneg (sub_nonneg.2 (hq b).2) (ih0 a b)) (mul_nonneg (hq b).1 (ih1 a b))
            have hmix : ∀ p e0 e1 : ℝ, 0 ≤ p → p ≤ 1 → 0 ≤ e0 → 0 ≤ e1 → 0 < (1 - p) * e0 + p * e1 →
                (p < 1 ∧ 0 < e0) ∨ (0 < p ∧ 0 < e1) := by
              intro p e0 e1 h0 h1 he0 he1 hpos
              by_contra hc
              push_neg at hc
              rcases h1.lt_or_eq with h1' | h1'
              · have := hc.1 h1'
                have he0' : e0 = 0 := le_antisymm this he0
                rcases h0.lt_or_eq with h0' | h0'
                · have := hc.2 h0'
                  have : e1 = 0 := le_antisymm this he1
                  subst_vars; simp at hpos
                · subst_vars; simp at hpos
              · rcases h0.lt_or_eq with h0' | h0'
                · have := hc.2 h0'
                  have : e1 = 0 := le_antisymm this he1
                  subst_vars; simp at hpos
                · rw [← h0'] at h1'; norm_num at h1'
            have hite : ∀ (P Q : Prop) {_ : Decidable P} {_ : Decidable Q}, (P → Q) →
                (if P then (1:ℕ) else 0) ≤ (if Q then 1 else 0) := by
              intro P Q _ _ h; split_ifs with h1 h2 <;> first | omega | exact absurd (h h1) h2
            have hite2 : ∀ (P Q R : Prop) {_ : Decidable P} {_ : Decidable Q} {_ : Decidable R}, (P → Q ∨ R) →
                (if P then (1:ℕ) else 0) ≤ (if Q then 1 else 0) + (if R then 1 else 0) := by
              intro P Q R _ _ _ h
              by_cases h1 : P
              · rcases h h1 with h2 | h2 <;> simp [h1, h2]
              · simp [h1]
            have hsc : ∀ (P Q : (Fin n → Bool) → (Fin n → Bool) → Prop) {_ : ∀ a b, Decidable (P a b)}
                {_ : ∀ a b, Decidable (Q a b)}, (∀ a b, P a b ↔ Q a b) →
                ∑ a, ∑ b, (if P a b then (1:ℕ) else 0) = ∑ a, ∑ b, (if Q a b then (1:ℕ) else 0) := by
              intro P Q _ _ h
              refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
              by_cases h1 : P a b
              · rw [if_pos h1, if_pos ((h a b).1 h1)]
              · rw [if_neg h1, if_neg (fun h2 => h1 ((h a b).2 h2))]
            have hprot : ∀ P : ClassicalProtocol (Fin n → Bool) (Fin n → Bool),
                ∀ A B : (Fin n → Bool) → Prop,
                (∀ a b, A a → B b → 0 < P.expectedOutput a b → ip n a b ≠ 1) →
                ∑ a, ∑ b, (if A a ∧ B b ∧ 0 < P.expectedOutput a b ∧ ip n a b = 0 then 1 else 0)
                  ≤ 2 ^ P.cost * 2 ^ n := by
              intro P
              induction P with
              | aliceOutputs f hf =>
                intro A B h
                simp only [ClassicalProtocol.expectedOutput, ClassicalProtocol.cost, pow_zero, one_mul]
                have h2 := KW n (fun a => A a ∧ 0 < f a) B (fun a b ha hb => h a b ha.1 hb ha.2)
                refine le_trans (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_) h2
                exact hite _ _ fun H1 => ⟨⟨H1.1, H1.2.2.1⟩, H1.2.1, H1.2.2.2⟩
              | bobOutputs g hg =>
                intro A B h
                simp only [ClassicalProtocol.expectedOutput, ClassicalProtocol.cost, pow_zero, one_mul]
                have h2 := KW n A (fun b => B b ∧ 0 < g b) (fun a b ha hb => h a b ha hb.1 hb.2)
                refine le_trans (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_) h2
                exact hite _ _ fun H1 => ⟨H1.1, ⟨H1.2.1, H1.2.2.1⟩, H1.2.2.2⟩
              | aliceSends p hp c0 c1 ih0 ih1 =>
                intro A B h
                have h0 := ih0 (fun a => A a ∧ p a < 1) B (by
                  intro a b ha hb he
                  apply h a b ha.1 hb
                  simp only [ClassicalProtocol.expectedOutput]
                  have := mul_pos (sub_pos.2 ha.2) he
                  have := mul_nonneg (hp a).1 (hnn c1 a b)
                  linarith)
                have h1 := ih1 (fun a => A a ∧ 0 < p a) B (by
                  intro a b ha hb he
                  apply h a b ha.1 hb
                  simp only [ClassicalProtocol.expectedOutput]
                  have := mul_pos ha.2 he
                  have := mul_nonneg (sub_nonneg.2 (hp a).2) (hnn c0 a b)
                  linarith)
                have hc0 : 2 ^ c0.cost ≤ 2 ^ (max c0.cost c1.cost) := Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
                have hc1 : 2 ^ c1.cost ≤ 2 ^ (max c0.cost c1.cost) := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
                calc _ ≤ ∑ a, ∑ b, ((if (A a ∧ p a < 1) ∧ B b ∧ 0 < c0.expectedOutput a b ∧ ip n a b = 0 then 1 else 0)
                      + (if (A a ∧ 0 < p a) ∧ B b ∧ 0 < c1.expectedOutput a b ∧ ip n a b = 0 then 1 else 0)) := by
                      refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
                      simp only [ClassicalProtocol.expectedOutput]
                      refine hite2 _ _ _ fun H1 => ?_
                      rcases hmix _ _ _ (hp a).1 (hp a).2 (hnn c0 a b) (hnn c1 a b) H1.2.2.1 with H | H
                      · exact Or.inl ⟨⟨H1.1, H.1⟩, H1.2.1, H.2, H1.2.2.2⟩
                      · exact Or.inr ⟨⟨H1.1, H.1⟩, H1.2.1, H.2, H1.2.2.2⟩
                  _ ≤ _ := by
                      simp only [Finset.sum_add_distrib]
                      exact add_le_add ((hsc _ _ fun _ _ => Iff.rfl).trans_le h0)
                        ((hsc _ _ fun _ _ => Iff.rfl).trans_le h1)
                  _ ≤ 2 ^ (ClassicalProtocol.aliceSends p hp c0 c1).cost * 2 ^ n := by
                      simp only [ClassicalProtocol.cost, pow_succ]
                      have := Nat.mul_le_mul_right (2 ^ n) hc0
                      have := Nat.mul_le_mul_right (2 ^ n) hc1
                      linarith
              | bobSends q hq c0 c1 ih0 ih1 =>
                intro A B h
                have h0 := ih0 A (fun b => B b ∧ q b < 1) (by
                  intro a b ha hb he
                  apply h a b ha hb.1
                  simp only [ClassicalProtocol.expectedOutput]
                  have := mul_pos (sub_pos.2 hb.2) he
                  have := mul_nonneg (hq b).1 (hnn c1 a b)
                  linarith)
                have h1 := ih1 A (fun b => B b ∧ 0 < q b) (by
                  intro a b ha hb he
                  apply h a b ha hb.1
                  simp only [ClassicalProtocol.expectedOutput]
                  have := mul_pos hb.2 he
                  have := mul_nonneg (sub_nonneg.2 (hq b).2) (hnn c0 a b)
                  linarith)
                have hc0 : 2 ^ c0.cost ≤ 2 ^ (max c0.cost c1.cost) := Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
                have hc1 : 2 ^ c1.cost ≤ 2 ^ (max c0.cost c1.cost) := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
                calc _ ≤ ∑ a, ∑ b, ((if A a ∧ (B b ∧ q b < 1) ∧ 0 < c0.expectedOutput a b ∧ ip n a b = 0 then 1 else 0)
                      + (if A a ∧ (B b ∧ 0 < q b) ∧ 0 < c1.expectedOutput a b ∧ ip n a b = 0 then 1 else 0)) := by
                      refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
                      simp only [ClassicalProtocol.expectedOutput]
                      refine hite2 _ _ _ fun H1 => ?_
                      rcases hmix _ _ _ (hq b).1 (hq b).2 (hnn c0 a b) (hnn c1 a b) H1.2.2.1 with H | H
                      · exact Or.inl ⟨H1.1, ⟨H1.2.1, H.1⟩, H.2, H1.2.2.2⟩
                      · exact Or.inr ⟨H1.1, ⟨H1.2.1, H.1⟩, H.2, H1.2.2.2⟩
                  _ ≤ _ := by
                      simp only [Finset.sum_add_distrib]
                      exact add_le_add ((hsc _ _ fun _ _ => Iff.rfl).trans_le h0)
                        ((hsc _ _ fun _ _ => Iff.rfl).trans_le h1)
                  _ ≤ 2 ^ (ClassicalProtocol.bobSends q hq c0 c1).cost * 2 ^ n := by
                      simp only [ClassicalProtocol.cost, pow_succ]
                      have := Nat.mul_le_mul_right (2 ^ n) hc0
                      have := Nat.mul_le_mul_right (2 ^ n) hc1
                      linarith
            -- final arithmetic
            have harith : ∀ c : ℕ, 3 ^ n ≤ 2 ^ c * 2 ^ n → (1/2 : ℝ) * n ≤ c := by
              intro c hc
              by_contra hlt
              push_neg at hlt
              have h2 : 2 * c + 1 ≤ n := by
                have : (2 * c : ℝ) < n := by linarith
                exact_mod_cast this
              have h3 : 9 ^ n ≤ 4 ^ c * 4 ^ n := by
                have := Nat.mul_le_mul hc hc
                calc 9 ^ n = 3 ^ n * 3 ^ n := by rw [← mul_pow]; norm_num
                  _ ≤ _ := this
                  _ = 4 ^ c * 4 ^ n := by
                    rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; ring
              have h4 : 4 ^ c * 2 ≤ 2 ^ n := by
                calc 4 ^ c * 2 = 2 ^ (2 * c + 1) := by rw [pow_succ, pow_mul]; norm_num
                  _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2
              have h5 : 2 * 9 ^ n ≤ 8 ^ n := by
                calc 2 * 9 ^ n ≤ 2 * (4 ^ c * 4 ^ n) := by omega
                  _ = (4 ^ c * 2) * 4 ^ n := by ring
                  _ ≤ 2 ^ n * 4 ^ n := Nat.mul_le_mul_right _ h4
                  _ = 8 ^ n := by rw [← mul_pow]; norm_num
              have h6 : 8 ^ n ≤ 9 ^ n := Nat.pow_le_pow_left (by norm_num) n
              have h7 : 0 < 9 ^ n := by positivity
              omega
            obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, (k:ℝ) ≤ Real.logb 2 n + 1 ∧ n + 1 ≤ 2 ^ k := by
              refine ⟨Nat.log 2 n + 1, ?_, Nat.lt_pow_succ_log_self (by norm_num) n⟩
              have := Real.natLog_le_logb n 2
              push_cast at this ⊢
              linarith
            have hk0 : 0 < 2 ^ k := by positivity
            obtain ⟨χ, hχ⟩ : ∃ χ : (Fin n → Bool) → ℕ → ℝ, ∀ a l,
                χ a l = if h : l < n then (if a ⟨l, h⟩ then 1 else 0) else 0 := ⟨_, fun _ _ => rfl⟩
            obtain ⟨U, hU⟩ : ∃ U : (Fin n → Bool) → ℕ → ℝ, ∀ a l,
                U a l = if l = 0 then 1 else χ a (l - 1) := ⟨_, fun _ _ => rfl⟩
            obtain ⟨V, hV⟩ : ∃ V : (Fin n → Bool) → ℕ → ℝ, ∀ a l,
                V a l = if l = 0 then 1 else -χ a (l - 1) := ⟨_, fun _ _ => rfl⟩
            obtain ⟨u, hu⟩ : ∃ u : (Fin n → Bool) → Fin (2 ^ k) → ℝ, ∀ a l, u a l = U a l :=
              ⟨_, fun _ _ => rfl⟩
            obtain ⟨v, hv⟩ : ∃ v : (Fin n → Bool) → Fin (2 ^ k) → ℝ, ∀ a l, v a l = V a l :=
              ⟨_, fun _ _ => rfl⟩
            have hipR : ∀ a b, (ip n a b : ℝ) = ∑ l ∈ Finset.range n, χ a l * χ b l := by
              intro a b
              rw [hip, Nat.cast_sum, ← Fin.sum_univ_eq_sum_range (fun l => χ a l * χ b l) n]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [hχ, hχ, dif_pos i.2, dif_pos i.2]
              simp only [Fin.eta]
              by_cases ha : a i <;> by_cases hb : b i <;> simp [ha, hb]
            have hUV : ∀ a b, v b ⬝ᵥ u a = 1 - (ip n a b : ℝ) := by
              intro a b
              have e1 : v b ⬝ᵥ u a = ∑ l : Fin (2 ^ k), V b l * U a l := by
                simp only [dotProduct, hu, hv]
              rw [e1, Fin.sum_univ_eq_sum_range (fun l => V b l * U a l) (2 ^ k)]
              have hsub : Finset.range (n+1) ⊆ Finset.range (2 ^ k) := Finset.range_subset_range.2 hk2
              rw [← Finset.sum_subset hsub (fun l hl hl' => ?_)]
              · rw [Finset.sum_range_succ', hipR]
                have e2 : ∀ l, V b (l + 1) * U a (l + 1) = -(χ a l * χ b l) := by
                  intro l
                  rw [hV, hU, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel]
                  ring
                simp only [e2, Finset.sum_neg_distrib]
                rw [hU, hV, if_pos rfl, if_pos rfl]
                ring
              · simp only [Finset.mem_range, not_lt] at hl'
                rw [hU, if_neg (by omega), hχ, dif_neg (by omega), mul_zero]
            have hV1 : ∀ b l, v b l * v b l ≤ 1 := by
              intro b l
              rw [hv, hV, hχ]
              split_ifs <;> norm_num
            have hc : ∀ a, 1 ≤ u a ⬝ᵥ u a := by
              intro a
              calc (1:ℝ) = u a ⟨0, hk0⟩ * u a ⟨0, hk0⟩ := by rw [hu, hU]; simp
                _ ≤ ∑ l, u a l * u a l :=
                    Finset.single_le_sum (f := fun l => u a l * u a l) (fun i _ => mul_self_nonneg _)
                      (Finset.mem_univ _)
            have hvv : ∀ b, v b ⬝ᵥ v b ≤ (2 ^ k : ℝ) := by
              intro b
              calc v b ⬝ᵥ v b = ∑ l, v b l * v b l := rfl
                _ ≤ ∑ _l : Fin (2 ^ k), (1:ℝ) := Finset.sum_le_sum fun l _ => hV1 b l
                _ = 2 ^ k := by simp
            have hstar : ∀ w : Fin (2 ^ k) → ℝ, star w = w := fun w => star_trivial w
            have hvmv : ∀ (w x : Fin (2 ^ k) → ℝ), Matrix.mulVec (Matrix.vecMulVec w w) x = (w ⬝ᵥ x) • w := by
              intro w x
              rw [Matrix.vecMulVec_mulVec, op_smul_eq_smul]
            have hρpsd : ∀ a, ((u a ⬝ᵥ u a)⁻¹ • Matrix.vecMulVec (u a) (u a)).PosSemidef := by
              intro a
              have h := Matrix.posSemidef_vecMulVec_self_star (u a)
              rw [hstar] at h
              exact h.smul (inv_nonneg.2 (le_trans zero_le_one (hc a)))
            have hρtr : ∀ a, ((u a ⬝ᵥ u a)⁻¹ • Matrix.vecMulVec (u a) (u a)).trace = 1 := by
              intro a
              rw [Matrix.trace_smul, Matrix.trace_vecMulVec, smul_eq_mul]
              exact inv_mul_cancel₀ (ne_of_gt (lt_of_lt_of_le zero_lt_one (hc a)))
            have hE0 : ∀ b, (((2 ^ k : ℝ))⁻¹ • Matrix.vecMulVec (v b) (v b)).PosSemidef := by
              intro b
              have h := Matrix.posSemidef_vecMulVec_self_star (v b)
              rw [hstar] at h
              exact h.smul (inv_nonneg.2 (by positivity))
            have hE1 : ∀ b, (1 - ((2 ^ k : ℝ))⁻¹ • Matrix.vecMulVec (v b) (v b)).PosSemidef := by
              intro b
              refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (Matrix.isHermitian_one.sub (hE0 b).isHermitian) ?_
              intro x
              rw [hstar, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hvmv, dotProduct_sub, dotProduct_smul,
                dotProduct_smul, smul_eq_mul, smul_eq_mul]
              have hcs : (v b ⬝ᵥ x) ^ 2 ≤ (v b ⬝ᵥ v b) * (x ⬝ᵥ x) := by
                have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (v b) x
                rw [show v b ⬝ᵥ v b = ∑ i, v b i ^ 2 by simp [dotProduct, sq],
                  show x ⬝ᵥ x = ∑ i, x i ^ 2 by simp [dotProduct, sq]]
                exact this
              have hxx : 0 ≤ x ⬝ᵥ x := by
                simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
              have hR : (0:ℝ) < 2 ^ k := by positivity
              have h2 : (v b ⬝ᵥ x) ^ 2 ≤ 2 ^ k * (x ⬝ᵥ x) :=
                le_trans hcs (mul_le_mul_of_nonneg_right (hvv b) hxx)
              rw [dotProduct_comm x (v b)]
              have : ((2:ℝ) ^ k)⁻¹ * ((v b ⬝ᵥ x) * (v b ⬝ᵥ x)) ≤ x ⬝ᵥ x := by
                rw [inv_mul_le_iff₀ hR, ← sq]; exact h2
              linarith
            obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin n → Bool) (Fin n → Bool) ℝ, ∀ a b,
                M a b = ((2:ℝ) ^ k)⁻¹ * (u a ⬝ᵥ u a)⁻¹ * (v b ⬝ᵥ u a) ^ 2 := ⟨_, fun _ _ => rfl⟩
            have hM0 : ∀ a b, 0 ≤ M a b := by
              intro a b
              rw [hM]
              have := le_trans zero_le_one (hc a)
              positivity
            have hMpos : ∀ a b, ip n a b = 0 → 0 < M a b := by
              intro a b h
              rw [hM, hUV, h]
              have := lt_of_lt_of_le zero_lt_one (hc a)
              norm_num
              positivity
            have hMz : ∀ a b, ip n a b = 1 → M a b = 0 := by
              intro a b h
              rw [hM, hUV, h]
              norm_num
            refine ⟨M, hM0, ⟨k, hk1, ⟨{
                alice := fun a => ⟨_, hρpsd a, hρtr a⟩
                bob := fun b => ⟨2, ![1, 0], ![((2 ^ k : ℝ))⁻¹ • Matrix.vecMulVec (v b) (v b),
                  1 - ((2 ^ k : ℝ))⁻¹ • Matrix.vecMulVec (v b) (v b)], ?_, ?_⟩
                label_nonnegative := ?_ }, ?_⟩⟩, ?_⟩
            · intro o
              fin_cases o
              · exact hE0 b
              · exact hE1 b
            · rw [Fin.sum_univ_two]
              simp
            · intro j o
              fin_cases o <;> simp
            · intro a b
              simp only [LabelledPOVM.expectation, LabelledPOVM.probability, Fin.sum_univ_two]
              simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, zero_mul, add_zero]
              rw [hM, smul_mul_assoc, mul_smul_comm, Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_smul, Matrix.trace_smul,
                Matrix.trace_vecMulVec, dotProduct_smul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
              ring
            · intro _ P hP
              have h := hprot P (fun _ => True) (fun _ => True) (by
                intro a b _ _ hpos h1
                rw [hP a b, hMz a b h1] at hpos
                exact lt_irrefl _ hpos)
              apply harith
              rw [← count n]
              refine le_trans (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
                hite _ _ ?_) h
              intro h0
              exact ⟨trivial, trivial, by rw [hP a b]; exact hMpos a b h0, h0⟩
