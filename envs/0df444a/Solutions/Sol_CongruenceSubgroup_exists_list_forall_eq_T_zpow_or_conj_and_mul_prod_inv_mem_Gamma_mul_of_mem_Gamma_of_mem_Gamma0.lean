-- Prove2me | solution 1 for CongruenceSubgroup.exists_list_forall_eq_T_zpow_or_conj_and_mul_prod_inv_mem_Gamma_mul_of_mem_Gamma_of_mem_Gamma0
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/87eeb754-90b1-508e-aea8-c7ca7074fed6

import Mathlib
import Theorems.Thm_Matrix_SpecialLinearGroup_exists_map_eq_and_map_eq_of_coprime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CongruenceSubgroup_exists_list_forall_eq_T_zpow_or_conj_and_mul_prod_inv_mem_Gamma_mul_of_mem_Gamma_of_mem_Gamma0

set_option autoImplicit false

open scoped MatrixGroups

theorem solution
    (q : ℕ) [Fact q.Prime] (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) (M' : ℕ) [NeZero M'] (hℓM' : ¬ ℓ ∣ M') :

    (∃ w : SL(2, ℤ), w ∈ CongruenceSubgroup.Gamma q ∧ w ∈ CongruenceSubgroup.Gamma0 M' ∧
      ((w 0 0 : ℤ) : ZMod ℓ) = 0 ∧ ((w 0 1 : ℤ) : ZMod ℓ) = -1 ∧
      ((w 1 0 : ℤ) : ZMod ℓ) = 1 ∧ ((w 1 1 : ℤ) : ZMod ℓ) = 0) ∧

    (∀ w : SL(2, ℤ), w ∈ CongruenceSubgroup.Gamma q → w ∈ CongruenceSubgroup.Gamma0 M' →
      ((w 0 0 : ℤ) : ZMod ℓ) = 0 → ((w 0 1 : ℤ) : ZMod ℓ) = -1 →
      ((w 1 0 : ℤ) : ZMod ℓ) = 1 → ((w 1 1 : ℤ) : ZMod ℓ) = 0 →
      ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q → γ ∈ CongruenceSubgroup.Gamma0 M' →
        ∃ l : List (SL(2, ℤ)),
          (∀ e ∈ l, ∃ s : ℤ, (q : ℤ) ∣ s ∧ (e = ModularGroup.T ^ s ∨ e = w * ModularGroup.T ^ s * w⁻¹)) ∧
          γ * (l.prod)⁻¹ ∈ CongruenceSubgroup.Gamma (q * ℓ) ∧
          l.prod ∈ CongruenceSubgroup.Gamma0 M') := by
  classical
  have hqp : q.Prime := Fact.out
  have hℓp : ℓ.Prime := Fact.out
  haveI : NeZero ℓ := ⟨hℓp.ne_zero⟩
  haveI : NeZero q := ⟨hqp.ne_zero⟩
  have hqℓ : Nat.Coprime q ℓ := (Nat.coprime_primes hqp hℓp).mpr (Ne.symm hℓq)
  have hM'ℓ : Nat.Coprime M' ℓ := (Nat.Prime.coprime_iff_not_dvd hℓp).mpr hℓM' |>.symm
  have hcop : Nat.Coprime (q * M') ℓ := Nat.Coprime.mul hqℓ hM'ℓ

  have descend : ∀ {n m : ℕ}, m ∣ n → ∀ {x c : ℤ}, (x : ZMod n) = (c : ZMod n) → (x : ZMod m) = (c : ZMod m) := by
    intro n m h x c hx
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hx ⊢
    exact dvd_trans (Int.natCast_dvd_natCast.mpr h) hx

  have red : ∀ (N : ℕ) (g : SL(2, ℤ)) (i j : Fin 2),
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) g) i j) = ((g i j : ℤ) : ZMod N) := by
    intro N g i j; rfl

  have hT : ∀ s : ℤ, ((ModularGroup.T ^ s) 0 0 : ℤ) = 1 ∧ ((ModularGroup.T ^ s) 0 1 : ℤ) = s ∧
      ((ModularGroup.T ^ s) 1 0 : ℤ) = 0 ∧ ((ModularGroup.T ^ s) 1 1 : ℤ) = 1 := by
    intro s
    have h := ModularGroup.coe_T_zpow s
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      · show (ModularGroup.T ^ s).1 _ _ = _
        rw [h]; simp
  have hT0 : ∀ s : ℤ, ModularGroup.T ^ s ∈ CongruenceSubgroup.Gamma0 M' := by
    intro s; rw [CongruenceSubgroup.Gamma0_mem]; rw [(hT s).2.2.1]; simp
  have hTq : ∀ s : ℤ, (q : ℤ) ∣ s → ModularGroup.T ^ s ∈ CongruenceSubgroup.Gamma q := by
    intro s hs; simpa using CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (q : ℤ) s hs

  have hlift : ∀ t : ℤ, ∃ s : ℤ, (q : ℤ) ∣ s ∧ (s : ZMod ℓ) = (t : ZMod ℓ) := by
    intro t
    obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr hqℓ : IsCoprime (q : ℤ) (ℓ : ℤ))
    refine ⟨t * u * q, ⟨t * u, by ring⟩, ?_⟩
    have : t * u * (q : ℤ) = t - t * v * ℓ := by
      have := congrArg (fun z => t * z) huv
      linear_combination this
    rw [this]; push_cast; simp [ZMod.natCast_self]

  obtain ⟨w, hw1, hw2⟩ := Matrix.SpecialLinearGroup.exists_map_eq_and_map_eq_of_coprime (q * M') ℓ hcop 1
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ)) ModularGroup.S)
  have hw1e : ∀ i j : Fin 2, ((w i j : ℤ) : ZMod (q * M')) = (((1 : SL(2, ℤ)) i j : ℤ) : ZMod (q * M')) := by
    intro i j
    have h0 : (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (q * M'))) w) i j =
        (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (q * M'))) 1) i j := by rw [hw1, map_one]
    rwa [red, red] at h0
  have hw2e : ∀ i j : Fin 2, ((w i j : ℤ) : ZMod ℓ) = ((ModularGroup.S i j : ℤ) : ZMod ℓ) := by
    intro i j
    have h0 : (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ)) w) i j =
        (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ)) ModularGroup.S) i j := by rw [hw2]
    rwa [red, red] at h0
  have one00 : ((1 : SL(2, ℤ)) 0 0 : ℤ) = 1 := rfl
  have one01 : ((1 : SL(2, ℤ)) 0 1 : ℤ) = 0 := rfl
  have one10 : ((1 : SL(2, ℤ)) 1 0 : ℤ) = 0 := rfl
  have one11 : ((1 : SL(2, ℤ)) 1 1 : ℤ) = 1 := rfl
  have S00 : (ModularGroup.S 0 0 : ℤ) = 0 := rfl
  have S01 : (ModularGroup.S 0 1 : ℤ) = -1 := rfl
  have S10 : (ModularGroup.S 1 0 : ℤ) = 1 := rfl
  have S11 : (ModularGroup.S 1 1 : ℤ) = 0 := rfl
  have hwq : w ∈ CongruenceSubgroup.Gamma q := by
    rw [CongruenceSubgroup.Gamma_mem]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := descend (dvd_mul_right q M') (hw1e 0 0); rw [one00] at this; exact_mod_cast this
    · have := descend (dvd_mul_right q M') (hw1e 0 1); rw [one01] at this; exact_mod_cast this
    · have := descend (dvd_mul_right q M') (hw1e 1 0); rw [one10] at this; exact_mod_cast this
    · have := descend (dvd_mul_right q M') (hw1e 1 1); rw [one11] at this; exact_mod_cast this
  have hw0 : w ∈ CongruenceSubgroup.Gamma0 M' := by
    rw [CongruenceSubgroup.Gamma0_mem]
    have := descend (dvd_mul_left M' q) (hw1e 1 0); rw [one10] at this; exact_mod_cast this
  have hw00 : ((w 0 0 : ℤ) : ZMod ℓ) = 0 := by have := hw2e 0 0; rw [S00] at this; exact_mod_cast this
  have hw01 : ((w 0 1 : ℤ) : ZMod ℓ) = -1 := by have := hw2e 0 1; rw [S01] at this; exact_mod_cast this
  have hw10 : ((w 1 0 : ℤ) : ZMod ℓ) = 1 := by have := hw2e 1 0; rw [S10] at this; exact_mod_cast this
  have hw11 : ((w 1 1 : ℤ) : ZMod ℓ) = 0 := by have := hw2e 1 1; rw [S11] at this; exact_mod_cast this
  refine ⟨⟨w, hwq, hw0, hw00, hw01, hw10, hw11⟩, ?_⟩

  intro w' hw'q hw'0 hw'00 hw'01 hw'10 hw'11 γ hγq hγ0

  let red' : SL(2, ℤ) →* SL(2, ZMod ℓ) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod ℓ))
  have hker : ∀ g : SL(2, ℤ), g ∈ CongruenceSubgroup.Gamma ℓ ↔ red' g = 1 := fun g => Iff.rfl

  have hw'S : red' w' = red' ModularGroup.S := by
    apply Matrix.SpecialLinearGroup.ext
    simp only [Fin.forall_fin_two]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [red, red, hw'00, S00]; simp
    · rw [red, red, hw'01, S01]; simp
    · rw [red, red, hw'10, S10]; simp
    · rw [red, red, hw'11, S11]; simp

  have hTmod : ∀ s t : ℤ, (s : ZMod ℓ) = (t : ZMod ℓ) → red' (ModularGroup.T ^ s) = red' (ModularGroup.T ^ t) := by
    intro s t hst
    have hdvd : (ℓ : ℤ) ∣ (s - t) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hst
      have := hst
      rwa [← neg_sub, dvd_neg] at this
    have hmem : ModularGroup.T ^ (s - t) ∈ CongruenceSubgroup.Gamma ℓ := by
      simpa using CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (ℓ : ℤ) (s - t) hdvd
    have h1 : red' (ModularGroup.T ^ (s - t)) = 1 := (hker _).mp hmem
    have : ModularGroup.T ^ s = ModularGroup.T ^ (s - t) * ModularGroup.T ^ t := by
      rw [← zpow_add, sub_add_cancel]
    rw [this, map_mul, h1, one_mul]

  let Allowed : SL(2, ℤ) → Prop := fun e => ∃ s : ℤ, (q : ℤ) ∣ s ∧ (e = ModularGroup.T ^ s ∨ e = w' * ModularGroup.T ^ s * w'⁻¹)
  have hAll0 : ∀ e, Allowed e → e ∈ CongruenceSubgroup.Gamma0 M' := by
    rintro e ⟨s, hs, rfl | rfl⟩
    · exact hT0 s
    · exact mul_mem (mul_mem hw'0 (hT0 s)) (inv_mem hw'0)
  have hAllq : ∀ e, Allowed e → e ∈ CongruenceSubgroup.Gamma q := by
    rintro e ⟨s, hs, rfl | rfl⟩
    · exact hTq s hs
    · exact mul_mem (mul_mem hw'q (hTq s hs)) (inv_mem hw'q)
  have hAllinv : ∀ e, Allowed e → Allowed e⁻¹ := by
    rintro e ⟨s, hs, rfl | rfl⟩
    · exact ⟨-s, by simpa using hs, Or.inl (by rw [zpow_neg])⟩
    · exact ⟨-s, by simpa using hs, Or.inr (by rw [mul_inv_rev, mul_inv_rev, inv_inv, zpow_neg, mul_assoc])⟩
  have hprod0 : ∀ l : List (SL(2, ℤ)), (∀ e ∈ l, Allowed e) → l.prod ∈ CongruenceSubgroup.Gamma0 M' := by
    intro l hl
    exact Subgroup.list_prod_mem _ (fun e he => hAll0 e (hl e he))
  have hprodq : ∀ l : List (SL(2, ℤ)), (∀ e ∈ l, Allowed e) → l.prod ∈ CongruenceSubgroup.Gamma q := by
    intro l hl
    exact Subgroup.list_prod_mem _ (fun e he => hAllq e (hl e he))

  have key : ∀ g : SL(2, ℤ), ∃ l : List (SL(2, ℤ)), (∀ e ∈ l, Allowed e) ∧ red' l.prod = red' g := by
    intro g
    have hg : g ∈ Subgroup.closure ({ModularGroup.S, ModularGroup.T} : Set (SL(2, ℤ))) := by
      rw [SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top g
    refine Subgroup.closure_induction (p := fun g _ => ∃ l : List (SL(2, ℤ)), (∀ e ∈ l, Allowed e) ∧ red' l.prod = red' g)
      ?_ ?_ ?_ ?_ hg
    ·
      intro x hx
      rcases hx with rfl | rfl
      ·
        obtain ⟨s, hsq, hs⟩ := hlift (-1)
        refine ⟨[ModularGroup.T ^ s, w' * ModularGroup.T ^ s * w'⁻¹, ModularGroup.T ^ s], ?_, ?_⟩
        · intro e he
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
          rcases he with rfl | rfl | rfl
          · exact ⟨s, hsq, Or.inl rfl⟩
          · exact ⟨s, hsq, Or.inr rfl⟩
          · exact ⟨s, hsq, Or.inl rfl⟩
        · have hrel : ModularGroup.S = ModularGroup.T ^ (-1 : ℤ) * (ModularGroup.S * ModularGroup.T ^ (-1 : ℤ) * ModularGroup.S⁻¹) * ModularGroup.T ^ (-1 : ℤ) := by
            rw [zpow_neg, zpow_one]
            ext i j
            fin_cases i <;> fin_cases j <;> rfl
          have hTs : red' (ModularGroup.T ^ s) = red' (ModularGroup.T ^ (-1 : ℤ)) := hTmod s (-1) (by simpa using hs)
          simp only [List.prod_cons, List.prod_nil, mul_one, map_mul, map_inv, hw'S, hTs]
          conv_rhs => rw [hrel]
          simp only [map_mul, map_inv, mul_assoc]
      ·
        obtain ⟨s, hsq, hs⟩ := hlift 1
        refine ⟨[ModularGroup.T ^ s], ?_, ?_⟩
        · intro e he
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
          subst he
          exact ⟨s, hsq, Or.inl rfl⟩
        · simp only [List.prod_cons, List.prod_nil, mul_one]
          rw [hTmod s 1 (by simpa using hs), zpow_one]
    · exact ⟨[], fun e he => by simp at he, by simp⟩
    · intro x y _ _ ⟨l₁, hl₁, h₁⟩ ⟨l₂, hl₂, h₂⟩
      refine ⟨l₁ ++ l₂, ?_, ?_⟩
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact hl₁ e he
        · exact hl₂ e he
      · rw [List.prod_append, map_mul, map_mul, h₁, h₂]
    · intro x _ ⟨l, hl, h⟩
      refine ⟨(l.map fun e => e⁻¹).reverse, ?_, ?_⟩
      · intro e he
        rw [List.mem_reverse, List.mem_map] at he
        obtain ⟨e', he', rfl⟩ := he
        exact hAllinv e' (hl e' he')
      · rw [← List.prod_inv_reverse, map_inv, map_inv, h]
  obtain ⟨l, hl, hred⟩ := key γ
  refine ⟨l, hl, ?_, hprod0 l hl⟩

  have h1 : γ * (l.prod)⁻¹ ∈ CongruenceSubgroup.Gamma ℓ := by
    rw [hker, map_mul, map_inv, ← hred, mul_inv_cancel]
  have h2 : γ * (l.prod)⁻¹ ∈ CongruenceSubgroup.Gamma q := mul_mem hγq (inv_mem (hprodq l hl))

  rw [CongruenceSubgroup.Gamma_mem] at h1 h2 ⊢
  have hcopZ : IsCoprime (q : ℤ) (ℓ : ℤ) := Nat.isCoprime_iff_coprime.mpr hqℓ
  have crt : ∀ (x c : ℤ), ((x : ZMod q) = (c : ZMod q)) → ((x : ZMod ℓ) = (c : ZMod ℓ)) →
      ((x : ZMod (q * ℓ)) = (c : ZMod (q * ℓ))) := by
    intro x c h1 h2
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h1 h2
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    exact hcopZ.mul_dvd h1 h2
  obtain ⟨a1, a2, a3, a4⟩ := h2
  obtain ⟨b1, b2, b3, b4⟩ := h1
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := crt _ 1 (by simpa using a1) (by simpa using b1); simpa using this
  · have := crt _ 0 (by simpa using a2) (by simpa using b2); simpa using this
  · have := crt _ 0 (by simpa using a3) (by simpa using b3); simpa using this
  · have := crt _ 1 (by simpa using a4) (by simpa using b4); simpa using this

end S_CongruenceSubgroup_exists_list_forall_eq_T_zpow_or_conj_and_mul_prod_inv_mem_Gamma_mul_of_mem_Gamma_of_mem_Gamma0
end P2MW
export P2MW.S_CongruenceSubgroup_exists_list_forall_eq_T_zpow_or_conj_and_mul_prod_inv_mem_Gamma_mul_of_mem_Gamma_of_mem_Gamma0 (solution)
