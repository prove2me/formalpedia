-- Prove2me | solution 1 for DGPNash.Gadget.lemma53_comparator
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T11:48:51.339576+00:00
-- url     : https://prove2.me/submissions/691eaae3-adb9-4840-8f08-42c17fe8c56e

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_Gadget_EpsNash
import Definitions.Def_DGPNash_Gadget_AffectsGraph
import Definitions.Def_DGPNash_Gadget_AddMulGame
import Definitions.Def_DGPNash_Gadget_BasicGadgets

set_option autoImplicit false

namespace Dbc2b259

open DGPNash.Gadget

def e : (CompRole → Fin 2) ≃ Fin 2 × Fin 2 × Fin 2 where
  toFun s := (s .a, s .b, s .d)
  invFun p := fun r => match r with
    | .a => p.1
    | .b => p.2.1
    | .d => p.2.2
  left_inv s := by funext r; cases r <;> rfl
  right_inv p := rfl

lemma univ_eq : (Finset.univ : Finset CompRole) = {CompRole.a, CompRole.b, CompRole.d} := by
  ext x; cases x <;> simp

lemma sum_eq (f : (CompRole → Fin 2) → ℝ) :
    ∑ s, f s = ∑ x : Fin 2, ∑ y : Fin 2, ∑ z : Fin 2, f (e.symm (x, y, z)) := by
  rw [← Fintype.sum_equiv e.symm (fun p => f (e.symm p)) f (fun _ => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]

lemma prod_eq (f : CompRole → ℝ) : ∏ i, f i = f .a * (f .b * f .d) := by
  rw [univ_eq, Finset.prod_insert (by decide), Finset.prod_pair (by decide)]

lemma eapp_a (x y z : Fin 2) : e.symm (x, y, z) .a = x := rfl
lemma eapp_b (x y z : Fin 2) : e.symm (x, y, z) .b = y := rfl
lemma eapp_d (x y z : Fin 2) : e.symm (x, y, z) .d = z := rfl

lemma pp (u : CompRole → (CompRole → Fin 2) → ℝ) (τ : CompRole → Fin 2 → ℝ) (i : CompRole) :
    AGT.expectedPayoff (S := fun _ => Fin 2) u τ i =
      ∑ x : Fin 2, ∑ y : Fin 2, ∑ z : Fin 2,
        τ .a x * (τ .b y * τ .d z) * u i (e.symm (x, y, z)) := by
  unfold AGT.expectedPayoff AGT.profileProb
  rw [sum_eq]
  simp only [prod_eq, eapp_a, eapp_b, eapp_d]

lemma pay_d_0 (σ : CompRole → Fin 2 → ℝ) (hb : σ .b 0 + σ .b 1 = 1) :
    DGPNash.NashMap.purePayoff (S := fun _ => Fin 2) compPayoff σ .d 0 = σ .a 1 := by
  unfold DGPNash.NashMap.purePayoff
  rw [pp]
  simp [Fin.sum_univ_two, compPayoff, ind, eapp_a, eapp_b, eapp_d, Function.update]
  linear_combination σ .a 1 * hb

lemma pay_d_1 (σ : CompRole → Fin 2 → ℝ) (ha : σ .a 0 + σ .a 1 = 1) :
    DGPNash.NashMap.purePayoff (S := fun _ => Fin 2) compPayoff σ .d 1 = σ .b 1 := by
  unfold DGPNash.NashMap.purePayoff
  rw [pp]
  simp [Fin.sum_univ_two, compPayoff, ind, eapp_a, eapp_b, eapp_d, Function.update]
  linear_combination σ .b 1 * ha

theorem main :
    ¬ Affects (S := fun _ => Fin 2) compPayoff .d .a ∧
    ¬ Affects (S := fun _ => Fin 2) compPayoff .d .b ∧
    ∀ (ε : ℝ), 0 ≤ ε → ε < 1 → ∀ σ : CompRole → Fin 2 → ℝ,
      IsEpsNash (S := fun _ => Fin 2) compPayoff ε σ →
      (σ .a 1 < σ .b 1 - ε → σ .d 1 = 1) ∧ (σ .a 1 > σ .b 1 + ε → σ .d 1 = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, s, x, y, h⟩
    exact h (by simp [compPayoff])
  · rintro ⟨_, s, x, y, h⟩
    exact h (by simp [compPayoff])
  · intro ε _ _ σ hσ
    obtain ⟨hmix, hws⟩ := hσ
    obtain ⟨_, has⟩ := hmix .a
    obtain ⟨_, hbs⟩ := hmix .b
    obtain ⟨_, hds⟩ := hmix .d
    simp only [Fin.sum_univ_two] at has hbs hds
    have H01 := hws .d 0 1
    have H10 := hws .d 1 0
    rw [pay_d_0 σ hbs, pay_d_1 σ has] at H01 H10
    constructor
    · intro h
      have : σ .d 0 = 0 := H10 (by linarith)
      linarith
    · intro h
      exact H01 (by linarith)

end Dbc2b259

open DGPNash.Gadget in
theorem solution :
    ¬ Affects (S := fun _ => Fin 2) compPayoff .d .a ∧
    ¬ Affects (S := fun _ => Fin 2) compPayoff .d .b ∧
    ∀ (ε : ℝ), 0 ≤ ε → ε < 1 → ∀ σ : CompRole → Fin 2 → ℝ,
      IsEpsNash (S := fun _ => Fin 2) compPayoff ε σ →
      (σ .a 1 < σ .b 1 - ε → σ .d 1 = 1) ∧ (σ .a 1 > σ .b 1 + ε → σ .d 1 = 0) := by
  exact Dbc2b259.main
