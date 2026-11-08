-- Prove2me | solution 1 for CallCountPOPBR.theorem_2_2_growth_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:12:29.700287+00:00
-- url     : https://prove2.me/submissions/b75a17d9-f569-49a9-8800-6ec6acf058a1

import Definitions.Def_CallCountPOPBR_Instance_IsValid
import Definitions.Def_CallCountPOPBR_IsAdmissibleRule
import Definitions.Def_CallCountPOPBR_IsCompletion

set_option autoImplicit false

open CallCountPOPBR in
theorem solution (I : Instance) (rule : ℕ → ℕ × ℕ) (C : ℕ → ℕ)
    (hI : I.IsValid) (hrule : IsAdmissibleRule I.d I.p rule) (hC : IsCompletion I rule C) :
    ∀ n, n ≤ I.N → C n ≤ 2 ^ (n + 1) - 1 := by
  obtain ⟨_, hd1, hdN, hp1, _, _⟩ := hI
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hpow : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    by_cases hnd : n < I.d
    · rw [hC.1 n hnd, pow_succ]
      omega
    · push_neg at hnd
      rw [hC.2.1 n hnd hn]
      have hr := hrule (n % I.p) (Nat.mod_lt _ (by omega))
      obtain ⟨ha1, hab, hbd⟩ := hr
      have h1 := ih (n - (rule (n % I.p)).1) (by omega) (by omega)
      have h2 := ih (n - (rule (n % I.p)).2) (by omega) (by omega)
      have e1 : 2 ^ (n - (rule (n % I.p)).1 + 1) ≤ 2 ^ n :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have e2 : 2 ^ (n - (rule (n % I.p)).2 + 1) ≤ 2 ^ n :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ]
      omega
