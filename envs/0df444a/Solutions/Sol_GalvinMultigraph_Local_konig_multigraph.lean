-- Prove2me | solution 1 for GalvinMultigraph.Local.konig_multigraph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:16:38.157784+00:00
-- url     : https://prove2.me/submissions/756dcd16-c212-46cd-818f-1c819160617c

module
public import Definitions.Def_GalvinMultigraph_Local_Stable
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Set
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Definitions.Def_GalvinMultigraph_Local_Konig
public import Theorems.Thm_GalvinMultigraph_Local_saturated_matching

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
open GalvinMultigraph GalvinMultigraph.Local
variable {U R E : Type*} [Fintype U] [Fintype R] [Fintype E]
  [DecidableEq U] [DecidableEq R] [DecidableEq E]
namespace GalvinMultigraph.Local
theorem _root_.solution (left : E → U) (right : E → R) (S : Finset E) (Δ : ℕ)
    (hL : ∀ u, degLOn left S u ≤ Δ) (hR : ∀ r, degROn right S r ≤ Δ) :
    ∃ φ : E → ℕ, (∀ e ∈ S, φ e < Δ) ∧
      ∀ e ∈ S, ∀ f ∈ S, e ≠ f → (left e = left f ∨ right e = right f) → φ e ≠ φ f := by
  classical
  induction Δ generalizing S with
  | zero =>
    have hS : S = ∅ := by
      by_contra hcon
      obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hcon
      have : 1 ≤ degLOn left S (left e) :=
        Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩⟩
      have := hL (left e)
      omega
    subst hS
    exact ⟨fun _ => 0, by simp, by simp⟩
  | succ Δ ih =>
    obtain ⟨M, hMS, hM, hLsat, hRsat⟩ := saturated_matching left right S (Δ + 1) (by omega) hL hR
    have hmono : ∀ (u : U), degLOn left (S \ M) u ≤ degLOn left S u := by
      intro u
      exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)
    have hmonoR : ∀ (r : R), degROn right (S \ M) r ≤ degROn right S r := by
      intro r
      exact Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)
    have hL' : ∀ u, degLOn left (S \ M) u ≤ Δ := by
      intro u
      by_cases hu : degLOn left S u = Δ + 1
      · obtain ⟨e, heM, heu⟩ := hLsat u hu
        have hss : (S \ M).filter (fun x => left x = u) ⊂ S.filter (fun x => left x = u) := by
          refine Finset.ssubset_iff_of_subset (Finset.filter_subset_filter _ Finset.sdiff_subset)
            |>.2 ⟨e, Finset.mem_filter.mpr ⟨hMS heM, heu⟩, ?_⟩
          simp [Finset.mem_filter, Finset.mem_sdiff, heM]
        have := Finset.card_lt_card hss
        unfold degLOn at hu ⊢
        omega
      · have := hL u; have := hmono u; omega
    have hR' : ∀ r, degROn right (S \ M) r ≤ Δ := by
      intro r
      by_cases hr : degROn right S r = Δ + 1
      · obtain ⟨e, heM, her⟩ := hRsat r hr
        have hss : (S \ M).filter (fun x => right x = r) ⊂ S.filter (fun x => right x = r) := by
          refine Finset.ssubset_iff_of_subset (Finset.filter_subset_filter _ Finset.sdiff_subset)
            |>.2 ⟨e, Finset.mem_filter.mpr ⟨hMS heM, her⟩, ?_⟩
          simp [Finset.mem_filter, Finset.mem_sdiff, heM]
        have := Finset.card_lt_card hss
        unfold degROn at hr ⊢
        omega
      · have := hR r; have := hmonoR r; omega
    obtain ⟨φ', hφ'lt, hφ'⟩ := ih (S \ M) hL' hR'
    refine ⟨fun e => if e ∈ M then Δ else φ' e, ?_, ?_⟩
    · intro e he
      by_cases heM : e ∈ M
      · simp [heM]
      · have := hφ'lt e (Finset.mem_sdiff.mpr ⟨he, heM⟩)
        simp [heM]
        omega
    · intro e he f hf hne hadj
      by_cases heM : e ∈ M <;> by_cases hfM : f ∈ M
      · exfalso
        rcases hadj with h | h
        · exact (hM e heM f hfM hne).1 h
        · exact (hM e heM f hfM hne).2 h
      · have := hφ'lt f (Finset.mem_sdiff.mpr ⟨hf, hfM⟩)
        simp only [heM, hfM, ite_true, ite_false]
        omega
      · have := hφ'lt e (Finset.mem_sdiff.mpr ⟨he, heM⟩)
        simp only [heM, hfM, ite_true, ite_false]
        omega
      · simp only [heM, hfM, ite_false]
        exact hφ' e (Finset.mem_sdiff.mpr ⟨he, heM⟩) f (Finset.mem_sdiff.mpr ⟨hf, hfM⟩) hne hadj
end GalvinMultigraph.Local
