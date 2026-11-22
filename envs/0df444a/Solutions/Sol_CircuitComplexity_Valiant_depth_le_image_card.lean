-- Prove2me | solution 1 for CircuitComplexity.Valiant.depth_le_image_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T10:13:01.455829+00:00
-- url     : https://prove2.me/submissions/eee60e95-19f3-4ddc-8245-ce4192cb0058

module
public import Definitions.Def_LeanPool_CircuitComplexity_Digraph_Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Batteries.Data.Nat.Bitwise.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_Valiant
section
@[expose] public section
namespace Digraph
end Digraph
namespace CircuitComplexity.Valiant
open Digraph
variable {V : Type*} [Fintype V]
section LegalLabelHelpers
variable {V : Type*}
private lemma legal_label_add_le
    {G : Digraph V} {ℓ : V → ℕ} (hℓ : IsLegalLabeling G ℓ)
    {m : ℕ} {p : Fin m → V} (hp : G.IsDirectedPath p) :
    ∀ k a (h₁ : a < m) (h₂ : a + k < m),
      ℓ (p ⟨a, h₁⟩) + k ≤ ℓ (p ⟨a + k, h₂⟩) := by
  intro k
  induction k with
  | zero =>
    simp_all
  | succ k ih =>
    intro a h₁ h₂
    have hak : a + k < m := by omega
    have ihk := ih a h₁ hak
    have stepl : ℓ (p ⟨a + k, hak⟩) < ℓ (p ⟨a + k + 1, h₂⟩) :=
      hℓ _ _ (hp ⟨a + k, hak⟩ h₂)
    change ℓ (p ⟨a, h₁⟩) + (k + 1) ≤ ℓ (p ⟨a + k + 1, h₂⟩)
    omega
private lemma legal_label_strictMono
    {G : Digraph V} {ℓ : V → ℕ} (hℓ : IsLegalLabeling G ℓ)
    {m : ℕ} {p : Fin m → V} (hp : G.IsDirectedPath p) :
    StrictMono (fun i : Fin m => ℓ (p i)) := by
  intro i j hij
  have hile : i.val < j.val := hij
  have hjm : j.val < m := j.isLt
  have hd : i.val + (j.val - i.val) < m := by omega
  have key := legal_label_add_le hℓ hp (j.val - i.val) i.val i.isLt hd
  have e2 : (⟨i.val + (j.val - i.val), hd⟩ : Fin m) = j :=
    Fin.ext (show i.val + (j.val - i.val) = j.val by omega)
  rw [show (⟨i.val, i.isLt⟩ : Fin m) = i from rfl, e2] at key
  change ℓ (p i) < ℓ (p j)
  omega
end LegalLabelHelpers
variable [DecidableEq V]
end CircuitComplexity.Valiant
end
end

set_option autoImplicit true
@[expose] public section
public section
open CircuitComplexity CircuitComplexity.Valiant
open Digraph
variable {V : Type*} [Fintype V]
namespace CircuitComplexity.Valiant
theorem _root_.solution (G : Digraph V)
    {ℓ : V → ℕ} (hℓ : IsLegalLabeling G ℓ) :
    G.depth ≤ (Finset.univ.image ℓ).card := by
  unfold Digraph.depth
  apply csSup_le
  · exact ⟨0, fun (i : Fin 0) => i.elim0, fun i _ => i.elim0⟩
  · rintro m ⟨p, hp⟩
    have hinj : Function.Injective (fun i : Fin m => ℓ (p i)) :=
      (legal_label_strictMono hℓ hp).injective
    have hsubset :
        (Finset.univ : Finset (Fin m)).image (fun i => ℓ (p i)) ⊆
          Finset.univ.image ℓ := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx ⊢
      obtain ⟨i, hi⟩ := hx
      exact ⟨p i, hi⟩
    have hcard :
        ((Finset.univ : Finset (Fin m)).image (fun i => ℓ (p i))).card = m := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    exact hcard ▸ Finset.card_le_card hsubset
end CircuitComplexity.Valiant
