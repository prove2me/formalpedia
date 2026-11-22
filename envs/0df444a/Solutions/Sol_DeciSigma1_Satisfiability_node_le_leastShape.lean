-- Prove2me | solution 1 for DeciSigma1.Satisfiability.node_le_leastShape
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:33:31.59303+00:00
-- url     : https://prove2.me/submissions/84177f24-25ae-4c87-974b-026c8ffd7a2d

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
public import Theorems.Thm_DeciSigma1_Satisfiability_LowerLabel_cons_fLe
public import Theorems.Thm_DeciSigma1_Satisfiability_LowerLabel_decompose
public import Theorems.Thm_DeciSigma1_Satisfiability_UpperLabel_decompose
public import Theorems.Thm_DeciSigma1_Satisfiability_f_le_shapeLabel
public import Theorems.Thm_DeciSigma1_Satisfiability_shapeLabel_mono
public import Theorems.Thm_DeciSigma1_Satisfiability_leastShape_label_eq

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}
namespace DeciSigma1.Satisfiability
theorem _root_.solution {a : Fin n → V} {x : V} (hl : LitT.fLe a x ∈ Γ) :
    Semantics.Tree.node (leastShape Γ ∘ a) ≤ leastShape Γ x := by
  intro π c d hc hd
  rw [leastShape_label_eq hd]
  cases π with
  | nil =>
    have he : c = .f := (Option.some.inj hc).symm
    subst c
    exact f_le_shapeLabel ⟨a, x, hl, .nil (.refl x)⟩
  | cons i π =>
    have hc' : (leastShape Γ (a i)).fn π = some c := hc
    rw [leastShape_label_eq hc']
    have hp : LowerAt Γ [i] (a i) x := .cons hl (.refl x) (.nil (.refl _))
    exact shapeLabel_mono (fun h => h.cons_fLe hl i)
      (fun _ h => UpperLabel.decompose (π := [i]) h hp)
end DeciSigma1.Satisfiability
