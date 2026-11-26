-- Prove2me | solution 1 for GRH.dirichlet_character_conjugate_representatives
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T18:45:52.157444+00:00
-- url     : https://prove2.me/submissions/c0ace489-c6b3-4028-8772-ee0b846e7b18

import Definitions.Def_GRH_DyadicCharacterGrid
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Tactic.Linarith

open GRH.DyadicCharacterGrid Complex
open scoped ComplexConjugate

private lemma inverse_im {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (j : ℕ) :
    (χ⁻¹ (j:ZMod q)).im = -(χ (j:ZMod q)).im := by
  rw [← MulChar.star_apply'];rfl

private lemma real_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (∀ j : ℕ,j<q → (χ (j:ZMod q)).im=0) ↔ χ=χ⁻¹ := by
  constructor
  · intro h
    apply DFunLike.ext
    intro a
    have hr := h a.val (ZMod.val_lt a)
    rw [ZMod.natCast_zmod_val] at hr
    rw [← MulChar.star_apply']
    apply Complex.ext
    · rfl
    · change (χ a).im= -(χ a).im
      linarith
  · intro h j _
    have e := inverse_im χ j
    rw [← h] at e
    linarith

/-- The first nonreal residue selects one character from each inverse pair.
Both members are selected exactly when the character equals its inverse. -/
theorem solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    (Oriented χ ∨ Oriented χ⁻¹) ∧ ((Oriented χ ∧ Oriented χ⁻¹) ↔ χ=χ⁻¹) := by
  classical
  by_cases hreal : ∀ j : ℕ,j<q → (χ (j:ZMod q)).im=0
  · have hs := (real_iff χ).1 hreal
    have good : Oriented χ := Or.inl hreal
    exact ⟨Or.inl good,⟨fun _ => hs,fun _ => ⟨good,hs ▸ good⟩⟩⟩
  · push Not at hreal
    let n := Nat.find hreal
    have hn : n<q ∧ (χ (n:ZMod q)).im≠0 := Nat.find_spec hreal
    have prior (j : ℕ) (hj : j<n) : (χ (j:ZMod q)).im=0 := by
      by_contra e
      exact Nat.find_min hreal hj ⟨hj.trans hn.1,e⟩
    have priorInv (j : ℕ) (hj : j<n) : (χ⁻¹ (j:ZMod q)).im=0 := by
      rw [inverse_im,prior j hj,neg_zero]
    have atFirst {ψ : DirichletCharacter ℂ q} (hnz : (ψ (n:ZMod q)).im≠0)
        (before : ∀ j<n,(ψ (j:ZMod q)).im=0) (ho : Oriented ψ) : 0<(ψ (n:ZMod q)).im := by
      rcases ho with h|⟨k,_,hk,hkpre⟩
      · exact (hnz (h n hn.1)).elim
      · rcases lt_trichotomy k n with hl|rfl|hg
        · exact (hk.ne' (before k hl)).elim
        · exact hk
        · exact (hnz (hkpre n hg)).elim
    have hninv : (χ⁻¹ (n:ZMod q)).im≠0 := by rw [inverse_im];exact neg_ne_zero.mpr hn.2
    constructor
    · rcases lt_or_gt_of_ne hn.2 with h|h
      · exact Or.inr (Or.inr ⟨n,hn.1,by rw [inverse_im];linarith,priorInv⟩)
      · exact Or.inl (Or.inr ⟨n,hn.1,h,prior⟩)
    · constructor
      · intro ⟨hp,hn'⟩
        have p := atFirst hn.2 prior hp
        have m := atFirst hninv priorInv hn'
        rw [inverse_im] at m
        linarith
      · intro heq
        exact (hn.2 ((real_iff χ).2 heq n hn.1)).elim
