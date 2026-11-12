-- Prove2me | solution 1 for CallCountPOPBR.lemma_2_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T20:16:09.946036+00:00
-- url     : https://prove2.me/submissions/ad633a3a-d9f5-40ed-8dad-c0855f776378

import Definitions.Def_CallCountPOPBR_Instance_IsValid
import Definitions.Def_CallCountPOPBR_IsAdmissibleRule
import Definitions.Def_CallCountPOPBR_IsCompletion
import Definitions.Def_CallCountPOPBR_Eval

set_option autoImplicit false

open CallCountPOPBR in
theorem solution (I : Instance) (rule : ℕ → ℕ × ℕ) (C : ℕ → ℕ)
    (hI : I.IsValid) (hrule : IsAdmissibleRule I.d I.p rule) (hC : IsCompletion I rule C) :
    (∀ n, n ≤ I.N → Odd (C n)) ∧
    (∀ n, n < I.d → Eval C n = 1) ∧
    (∀ n, I.d ≤ n → n ≤ I.N →
      Eval C n = Eval C (n - (rule (n % I.p)).1) + Eval C (n - (rule (n % I.p)).2)) ∧
    (I.p = I.N + 1 → ∀ n n', n ≤ I.N → n' ≤ I.N → n % I.p = n' % I.p → n = n') ∧
    (I.p = I.N + 1 → ∀ pairs : ℕ → ℕ × ℕ, ∃ rule' : ℕ → ℕ × ℕ,
      ∀ n, n ≤ I.N → rule' (n % I.p) = pairs n) ∧
    (I.p = I.N + 1 → I.N ≤ 2 * I.d - 1 → ∀ n, I.d ≤ n → n ≤ I.N →
      n - I.d < I.d ∧ (Finset.Icc 1 I.d).image (fun o => n - o) = Finset.Ico (n - I.d) n) := by
  obtain ⟨_, hd1, hdN, hp1, hpN, _⟩ := hI
  obtain ⟨hC0, hCrec, _⟩ := hC
  have hodd : ∀ n, n ≤ I.N → Odd (C n) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih hn
    by_cases hnd : n < I.d
    · rw [hC0 n hnd]
      exact odd_one
    · push_neg at hnd
      have hp : n % I.p < I.p := Nat.mod_lt _ (by omega)
      obtain ⟨ha1, hab, hbd⟩ := hrule _ hp
      rw [hCrec n hnd hn]
      obtain ⟨i, hi⟩ := ih (n - (rule (n % I.p)).1) (by omega) (by omega)
      obtain ⟨j, hj⟩ := ih (n - (rule (n % I.p)).2) (by omega) (by omega)
      exact ⟨i + j + 1, by omega⟩
  refine ⟨hodd, ?_, ?_, ?_, ?_, ?_⟩
  · intro n hn
    simp [Eval, hC0 n hn]
  · intro n hnd hn
    have hp : n % I.p < I.p := Nat.mod_lt _ (by omega)
    obtain ⟨ha1, hab, hbd⟩ := hrule _ hp
    obtain ⟨i, hi⟩ := hodd (n - (rule (n % I.p)).1) (by omega)
    obtain ⟨j, hj⟩ := hodd (n - (rule (n % I.p)).2) (by omega)
    simp only [Eval]
    rw [hCrec n hnd hn, hi, hj]
    omega
  · intro hpe n n' hn hn' hmod
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
    exact hmod
  · intro hpe pairs
    refine ⟨pairs, fun n hn => ?_⟩
    rw [Nat.mod_eq_of_lt (by omega)]
  · intro hpe hN n hnd hn
    refine ⟨by omega, ?_⟩
    ext x
    simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_Ico]
    constructor
    · rintro ⟨o, ⟨h1, h2⟩, rfl⟩
      omega
    · rintro ⟨h1, h2⟩
      exact ⟨n - x, ⟨by omega, by omega⟩, by omega⟩
