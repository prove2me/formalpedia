-- Prove2me | solution 1 for GalvinMultigraph.Local.merge_matchings
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:56:46.927847+00:00
-- url     : https://prove2.me/submissions/229842d0-17e4-478f-84e5-8750ec30f960

module
public import Definitions.Def_GalvinMultigraph_Local_Stable
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Set
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Definitions.Def_GalvinMultigraph_Local_Konig
public import Theorems.Thm_GalvinMultigraph_Local_stable_matching_multi


set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
open GalvinMultigraph GalvinMultigraph.Local
variable {U R E : Type*} [Fintype U] [Fintype R] [Fintype E]
  [DecidableEq U] [DecidableEq R] [DecidableEq E]
omit [Fintype U] [Fintype R]
namespace GalvinMultigraph.Local
theorem _root_.solution (left : E → U) (right : E → R) (S ML MR : Finset E)
    (hMLS : ML ⊆ S) (hMRS : MR ⊆ S)
    (hML : IsMatchingOn left right ML) (hMR : IsMatchingOn left right MR) :
    ∃ M : Finset E, M ⊆ S ∧ IsMatchingOn left right M ∧
      (∀ u, (∃ e ∈ ML, left e = u) → ∃ e ∈ M, left e = u) ∧
      (∀ r, (∃ e ∈ MR, right e = r) → ∃ e ∈ M, right e = r) := by
  classical
  -- Left vertices prefer the edges of `MR`, right vertices prefer the edges of `ML`; a stable
  -- matching for these preferences must cover every vertex covered by the corresponding matching.
  set n : ℕ := Fintype.card E with hn
  set idx : E → ℕ := fun e => ((Fintype.equivFin E) e : ℕ) with hidx
  have hidxlt : ∀ e, idx e < n := fun e => (Fintype.equivFin E e).isLt
  have hidxinj : Function.Injective idx := by
    intro e f h
    exact (Fintype.equivFin E).injective (Fin.ext h)
  set pu : E → ℕ := fun e => (if e ∈ ML then 0 else n) + idx e with hpu
  set pr : E → ℕ := fun e => (if e ∈ MR then 0 else n) + idx e with hpr
  have hpuinj : ∀ e f, pu e = pu f → e = f := by
    intro e f h
    by_cases he : e ∈ ML <;> by_cases hf : f ∈ ML <;>
      simp only [hpu, he, hf, ite_true, ite_false] at h <;>
      first
        | exact hidxinj (by omega)
        | (exfalso; have := hidxlt e; have := hidxlt f; omega)
  have hprinj : ∀ e f, pr e = pr f → e = f := by
    intro e f h
    by_cases he : e ∈ MR <;> by_cases hf : f ∈ MR <;>
      simp only [hpr, he, hf, ite_true, ite_false] at h <;>
      first
        | exact hidxinj (by omega)
        | (exfalso; have := hidxlt e; have := hidxlt f; omega)
  obtain ⟨M, hMsub, hMmatch, hMstab⟩ :=
    stable_matching_multi left right pu pr (fun e f _ h => hpuinj e f h)
      (fun e f _ h => hprinj e f h) (ML ∪ MR)
  refine ⟨M, hMsub.trans (Finset.union_subset hMLS hMRS), hMmatch, ?_, ?_⟩
  · rintro u ⟨e, heML, rfl⟩
    by_cases heM : e ∈ M
    · exact ⟨e, heM, rfl⟩
    · rcases hMstab e (Finset.mem_union_left _ heML) heM with ⟨f, hfM, hfl, _⟩ | ⟨f, hfM, hfr, hfp⟩
      · exact ⟨f, hfM, hfl⟩
      · exfalso
        have hfne : f ≠ e := fun h => heM (h ▸ hfM)
        rcases Finset.mem_union.mp (hMsub hfM) with hfML | hfMR
        · exact (hML f hfML e heML hfne).2 hfr
        · have hfnotML : f ∉ ML := fun h => (hML f h e heML hfne).2 hfr
          have hlt : pr e < pr f := hfp
          have h1 : pr f = idx f := by simp [hpr, hfMR]
          have heMR : e ∈ MR := by
            by_contra hcon
            have : pr e = n + idx e := by simp [hpr, hcon]
            have := hidxlt f
            omega
          exact hfne (hMR f hfMR e heMR hfne |>.2 hfr |>.elim)
  · rintro r ⟨e, heMR, rfl⟩
    by_cases heM : e ∈ M
    · exact ⟨e, heM, rfl⟩
    · rcases hMstab e (Finset.mem_union_right _ heMR) heM with ⟨f, hfM, hfl, hfp⟩ | ⟨f, hfM, hfr, _⟩
      · exfalso
        have hfne : f ≠ e := fun h => heM (h ▸ hfM)
        rcases Finset.mem_union.mp (hMsub hfM) with hfML | hfMR
        · have h1 : pu f = idx f := by simp [hpu, hfML]
          have heML : e ∈ ML := by
            by_contra hcon
            have : pu e = n + idx e := by simp [hpu, hcon]
            have := hidxlt f
            omega
          exact (hML f hfML e heML hfne).1 hfl
        · exact (hMR f hfMR e heMR hfne).1 hfl
      · exact ⟨f, hfM, hfr⟩
end GalvinMultigraph.Local
