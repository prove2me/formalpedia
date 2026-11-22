-- Prove2me | solution 1 for DeciSigma1.Satisfiability.leastShape_le_node
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:33:27.038802+00:00
-- url     : https://prove2.me/submissions/23a5872b-412e-4860-a96a-5872767a49a6

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Closure
public import Definitions.Def_LeanPool_DeciSigma1_Satisfiability_Shape
public import Theorems.Thm_DeciSigma1_Satisfiability_LowerLabel_decompose
public import Theorems.Thm_DeciSigma1_Satisfiability_UpperLabel_decompose
public import Theorems.Thm_DeciSigma1_Satisfiability_UpperLabel_cons_leF
public import Theorems.Thm_DeciSigma1_Satisfiability_shapeLabel_le_f
public import Theorems.Thm_DeciSigma1_Satisfiability_shapeLabel_mono
public import Theorems.Thm_DeciSigma1_Satisfiability_leastShape_label_eq

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Satisfiability
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ} {V : Type*} {Γ : List (LitT n V)}
namespace DeciSigma1.Satisfiability
theorem _root_.solution {x : V} {b : Fin n → V} (hl : LitT.leF x b ∈ Γ) :
    leastShape Γ x ≤ Semantics.Tree.node (leastShape Γ ∘ b) := by
  intro π c d hc hd
  rw [leastShape_label_eq hc]
  cases π with
  | nil =>
    have he : d = .f := (Option.some.inj hd).symm
    subst d
    exact shapeLabel_le_f ⟨x, b, hl, .nil (.refl x)⟩
  | cons i π =>
    have hd' : (leastShape Γ (b i)).fn π = some d := hd
    rw [leastShape_label_eq hd']
    have hp : UpperAt Γ [i] x (b i) := .cons (.refl x) hl (.nil (.refl _))
    exact shapeLabel_mono (fun h => LowerLabel.decompose (π := [i]) h hp)
      (fun _ h => h.cons_leF hl i)
end DeciSigma1.Satisfiability
