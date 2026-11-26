-- Prove2me | solution 1 for Erdos287.consecutive_omissions_from_multi_premise_residue_rules
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T07:07:02.935023+00:00
-- url     : https://prove2.me/submissions/e05cfbc4-ba26-4ae6-9cbc-daa446d12e61

import Mathlib
import Theorems.Thm_Erdos287_nonempty_prime_layer_has_large_cofactor_numerator

open Finset

set_option autoImplicit false

/-- A rule may use several established positions at once. A contradictory
trace in both branches certifies a pair of consecutive omissions. -/
theorem solution (D H R : Finset ℕ) (m M C : ℕ)
    (hD : D ⊆ Finset.Icc m M) (hpos : ∀ n ∈ D, 0 < n)
    (hdiv : ∀ n ∈ D, n ∣ C) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hH : Disjoint D H) (hR : R ⊆ D)
    (rule : Finset (ℕ × Bool) → (ℕ × Bool) → Prop)
    (hRules : ∀ A b, rule A b →
      (b.2 = true ∧
        ((b.1 - 1, false) ∈ A ∧ m < b.1 ∧ b.1 ≤ M ∨
         (b.1 + 1, false) ∈ A ∧ m ≤ b.1 ∧ b.1 + 1 ≤ M)) ∨
      (b.2 = true ∧ b.1 ∈ R) ∨ (b.2 = false ∧ b.1 ∈ H) ∨
      ∃ S : Finset ℕ, b.1 ∈ S ∧ (∀ a ∈ A, a.1 ∈ S) ∧
        ((∃ q : ℕ, q ∣ C ∧
          (∀ n ∈ Finset.Icc m M, ¬ q ∣ C / n → n ∈ S) ∧
          (∀ T ⊆ S, q ∣ (∑ n ∈ T, C / n) →
            (∀ a ∈ A, a.1 ∈ T ↔ a.2 = true) → (b.1 ∈ T ↔ b.2 = true))) ∨
         (∃ p e : ℕ, p.Prime ∧ 1 ≤ e ∧
          (∀ n ∈ Finset.Icc m M, n ∉ H → padicValNat p n ≤ e ∧
            (n ∈ S ↔ padicValNat p n = e)) ∧
          (∀ T ⊆ S, (¬ T.Nonempty ∨ p ≤ T.card * (M / p ^ e) ^ (T.card - 1)) →
            (∀ a ∈ A, a.1 ∈ T ↔ a.2 = true) → (b.1 ∈ T ↔ b.2 = true)))))
    (hProof : ∃ root : ℕ, ∀ b : Bool, ∃ T : Finset (ℕ × Bool),
      Relation.ReflTransGen
        (fun X Y => ∃ A a, rule A a ∧ A ⊆ X ∧ Y = insert a X)
        {(root, b)} T ∧
      ∃ n, (n, true) ∈ T ∧ (n, false) ∈ T) :
    ∃ n, m ≤ n ∧ n + 1 ≤ M ∧ n ∉ D ∧ n + 1 ∉ D := by
  by_contra hg
  have hnxt (n : ℕ) (hl : m ≤ n) (hr : n + 1 ≤ M) (hn : n ∉ D) : n + 1 ∈ D := by
    by_contra hh
    exact hg ⟨n, hl, hr, hn, hh⟩
  have hnum : (∑ n ∈ D, C / n) = C := by
    have hscale : (C : ℚ) * (∑ n ∈ D, (1 : ℚ) / n) = ((∑ n ∈ D, C / n : ℕ) : ℚ) := by
      rw [mul_sum, Nat.cast_sum]
      refine sum_congr rfl fun n hn => ?_
      rw [mul_one_div]
      apply (div_eq_iff (Nat.cast_ne_zero.mpr (hpos n hn).ne')).mpr
      exact_mod_cast (Nat.div_mul_cancel (hdiv n hn)).symm
    rw [hsum, mul_one] at hscale
    exact_mod_cast hscale.symm
  have havoid (n : ℕ) (hn : n ∈ D) : n ∉ H := fun hh => disjoint_left.mp hH hn hh
  let holds (a : ℕ × Bool) := (a.1 ∈ D ↔ a.2 = true)
  have hstep (A : Finset (ℕ × Bool)) (b : ℕ × Bool) (hb : rule A b) :
      (∀ a ∈ A, holds a) → holds b := by
    intro ha
    rcases hRules A b hb with h | h | h | h
    · obtain ⟨hb₁, hpair⟩ := h
      have hk : b.1 ∈ D := by
        rcases hpair with ⟨hmem, hlo, hhi⟩ | ⟨hmem, hlo, hhi⟩
        · have he : b.1 - 1 + 1 = b.1 := by omega
          have hn : b.1 - 1 ∉ D := fun h => Bool.false_ne_true ((ha _ hmem).mp h)
          have hs := hnxt (b.1 - 1) (by omega) (he.symm ▸ hhi) hn
          simpa only [he] using hs
        · by_contra hnot
          have hn := hnxt b.1 hlo hhi hnot
          exact Bool.false_ne_true ((ha _ hmem).mp hn)
      exact ⟨fun _ => hb₁, fun _ => hk⟩
    · exact ⟨fun _ => h.1, fun _ => hR h.2⟩
    · have hn : b.1 ∉ D := fun hn => havoid _ hn h.2
      exact ⟨fun hh => (hn hh).elim, fun hh => (Bool.false_ne_true (h.1 ▸ hh)).elim⟩
    · obtain ⟨S, hbS, haS, hkind⟩ := h
      let T := D ∩ S
      have haT (a : ℕ × Bool) (haA : a ∈ A) : a.1 ∈ T ↔ a.2 = true := by
        simpa only [T, mem_inter, haS a haA, and_true] using ha a haA
      have hbT : b.1 ∈ T ↔ b.2 = true := by
        rcases hkind with ⟨q, hq, hsupport, hcert⟩ | ⟨p, e, hp, he, hsupport, hcert⟩
        · have hout : q ∣ ∑ n ∈ D \ S, C / n := by
            refine dvd_sum fun n hn => ?_
            obtain ⟨hnD, hnS⟩ := mem_sdiff.mp hn
            by_contra hh
            exact hnS (hsupport n (hD hnD) hh)
          have hdiff : D \ T = D \ S := by
            ext n
            simp only [T, mem_sdiff, mem_inter]
            tauto
          have hsplit := sum_sdiff (f := fun n => C / n) (inter_subset_left : T ⊆ D)
          rw [hdiff, hnum] at hsplit
          have hT : q ∣ ∑ n ∈ T, C / n := by
            have hh := congrArg (fun x : ℕ => x - ∑ n ∈ D \ S, C / n) hsplit
            have heq : (∑ n ∈ T, C / n) = C - ∑ n ∈ D \ S, C / n := by
              simpa only [T, Nat.add_sub_cancel_left] using hh
            rw [heq]
            exact Nat.dvd_sub hq hout
          exact hcert T inter_subset_right hT haT
        · have hmax (n : ℕ) (hn : n ∈ D) := (hsupport n (hD hn) (havoid n hn)).1
          have hlayer : D.filter (fun n => padicValNat p n = e) = T := by
            ext n
            simp only [T, mem_filter, mem_inter]
            exact ⟨fun ⟨hd, h⟩ => ⟨hd, (hsupport n (hD hd) (havoid n hd)).2.mpr h⟩,
              fun ⟨hd, h⟩ => ⟨hd, (hsupport n (hD hd) (havoid n hd)).2.mp h⟩⟩
          have hT : ¬ T.Nonempty ∨ p ≤ T.card * (M / p ^ e) ^ (T.card - 1) := by
            by_cases ht : T.Nonempty
            · have ht' : (D.filter (fun n => padicValNat p n = e)).Nonempty := hlayer.symm ▸ ht
              have h := Erdos287.nonempty_prime_layer_has_large_cofactor_numerator D M p e hp he
                (fun n hn => ⟨hpos n hn, (mem_Icc.mp (hD hn)).2⟩) hmax hsum ht'
              dsimp only at h
              exact Or.inr (by simpa only [hlayer] using h.2.1.trans h.2.2)
            · exact Or.inl ht
          exact hcert T inter_subset_right hT haT
      simpa only [holds, T, mem_inter, hbS, and_true] using hbT
  have htrace {X Y : Finset (ℕ × Bool)} (h : Relation.ReflTransGen
      (fun U V => ∃ A a, rule A a ∧ A ⊆ U ∧ V = insert a U) X Y) :
      (∀ a ∈ X, holds a) → ∀ a ∈ Y, holds a := by
    induction h with
    | refl => exact id
    | tail _ hxy ih =>
      intro hX a ha
      obtain ⟨A, b, hR, hsub, rfl⟩ := hxy
      rcases mem_insert.mp ha with hab | ha
      · rw [hab]
        exact hstep A b hR (fun x hx => ih hX x (hsub hx))
      · exact ih hX a ha
  obtain ⟨root, hroot⟩ := hProof
  let b := decide (root ∈ D)
  obtain ⟨T, hT, n, hn, hn'⟩ := hroot b
  have hstart : ∀ a ∈ ({(root, b)} : Finset (ℕ × Bool)), holds a := by
    intro a ha
    rw [mem_singleton.mp ha]
    simp [holds, b]
  have hp := htrace hT hstart
  exact Bool.false_ne_true ((hp _ hn').mp ((hp _ hn).mpr rfl))

