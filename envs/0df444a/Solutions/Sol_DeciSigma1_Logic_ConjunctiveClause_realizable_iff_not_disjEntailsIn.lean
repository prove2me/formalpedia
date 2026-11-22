-- Prove2me | solution 1 for DeciSigma1.Logic.ConjunctiveClause.realizable_iff_not_disjEntailsIn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:59:27.796236+00:00
-- url     : https://prove2.me/submissions/c61c55cd-5806-4c76-936d-a7fbeaf7bec2

module
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Syntax
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Definitions.Def_LeanPool_DeciSigma1_Logic_Flatten
public import Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_holds_append
public import Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_mem_terms
public import Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_extend_closed
public import Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_extend_name
public import Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_holds_constraints_extend
public import Theorems.Thm_DeciSigma1_Logic_ConjunctiveClause_eq_eval_of_holds_constraints
attribute [local simp] DeciSigma1.Logic.ConjunctiveClause.holds_append

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Logic
variable {T : Type → Type} {D V : Type} {I : Interpretation T D}
open DeciSigma1.Logic.ConjunctiveClause
variable (F : Flattening I) {m : ℕ} (c : ConjunctiveClause T (Fin m))
variable [DecidableEq (T (Fin m))]
namespace DeciSigma1.Logic.ConjunctiveClause
theorem _root_.solution {C : D → Prop} (hC : I.TermClosed C) :
    (∃ ρ : Fin m → D, (∀ v, C (ρ v)) ∧ c.Holds I ρ) ↔
      ¬ F.DisjEntailsIn C (c.constraints F) (c.queries F) := by
  simp only [Flattening.DisjEntailsIn, not_forall, not_exists]
  constructor
  · rintro ⟨ρ, hCρ, hρ⟩
    refine ⟨c.extend F ρ, c.extend_closed F hC hCρ, c.holds_constraints_extend F hρ, ?_⟩
    intro i
    have h := c.mem_terms F (p := c.negative[i]) (Or.inr (List.getElem_mem i.isLt))
    change ¬ I.le (c.extend F ρ (c.name F c.negative[i].1))
      (c.extend F ρ (c.name F c.negative[i].2))
    rw [c.extend_name F ρ h.1, c.extend_name F ρ h.2]
    exact hρ.2 _ (List.getElem_mem i.isLt)
  · rintro ⟨σ, hCσ, hσ, hq⟩
    refine ⟨σ ∘ .inl, fun v => hCσ _, ?_, ?_⟩
    · intro p hp
      have h := c.mem_terms F (Or.inl hp)
      have hl := hσ _ (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
      rwa [F.holds_leLit, c.eq_eval_of_holds_constraints F hσ h.1,
        c.eq_eval_of_holds_constraints F hσ h.2] at hl
    · intro p hp
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
      have h := c.mem_terms F (Or.inr (List.getElem_mem hi))
      have hl : ¬ I.le (σ (c.name F c.negative[i].1)) (σ (c.name F c.negative[i].2)) :=
        hq ⟨i, hi⟩
      rwa [c.eq_eval_of_holds_constraints F hσ h.1,
        c.eq_eval_of_holds_constraints F hσ h.2] at hl
end DeciSigma1.Logic.ConjunctiveClause
