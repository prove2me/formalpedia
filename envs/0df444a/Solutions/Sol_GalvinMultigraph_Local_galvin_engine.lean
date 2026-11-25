-- Prove2me | solution 1 for GalvinMultigraph.Local.galvin_engine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:00:39.934325+00:00
-- url     : https://prove2.me/submissions/789db631-c9c7-4f0a-8b27-573e888b2a6d

module
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Set
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_GalvinMultigraph_Local_Kernel
public import Definitions.Def_GalvinMultigraph_Local_Ranks
public import Definitions.Def_GalvinMultigraph_Local_Main
public import Theorems.Thm_GalvinMultigraph_Local_kernel_coloring
public import Theorems.Thm_GalvinMultigraph_Local_stable_matching_multi


set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
open GalvinMultigraph GalvinMultigraph.Local
variable {U R E : Type*} [Fintype U] [Fintype R] [Fintype E] [DecidableEq U] [DecidableEq R]
    [DecidableEq E]
omit [Fintype U] [Fintype R]
namespace GalvinMultigraph.Local
theorem _root_.solution (left : E → U) (right : E → R) (ru rv : E → ℕ)
    (hru : ∀ e f, left e = left f → ru e = ru f → e = f)
    (hrv : ∀ e f, right e = right f → rv e = rv f → e = f)
    (L : E → Finset ℕ)
    (hL : ∀ e, (Finset.univ.filter fun f =>
        (left e = left f ∧ ru e < ru f) ∨ (right e = right f ∧ rv f < rv e)).card < (L e).card) :
    ∃ φ : E → ℕ, (∀ e, φ e ∈ L e) ∧
      ∀ e f, e ≠ f → (left e = left f ∨ right e = right f) → φ e ≠ φ f := by
  classical
  set A : E → E → Prop := fun e f =>
    (left e = left f ∧ ru e < ru f) ∨ (right e = right f ∧ rv f < rv e) with hAdef
  have hirr : ∀ e, ¬ A e e := by intro e; simp [hAdef]
  -- Kernels of the Galvin orientation are exactly stable matchings.
  have hker : ∀ S : Finset E, ∃ K, IsKernelOn A S K := by
    intro S
    set C : ℕ := Finset.univ.sup rv with hC
    have hle : ∀ e, rv e ≤ C := fun e => Finset.le_sup (Finset.mem_univ e)
    obtain ⟨M, hMsub, hMmatch, hMstab⟩ :=
      stable_matching_multi left right ru (fun e => C - rv e) hru
        (by
          intro e f hrr hpp
          have hpp' : C - rv e = C - rv f := hpp
          exact hrv e f hrr (by have := hle e; have := hle f; omega)) S
    refine ⟨M, hMsub, ?_, ?_⟩
    · intro x hx y hy hxy
      rcases eq_or_ne x y with rfl | hne
      · exact hirr x hxy
      · obtain ⟨hl, hr⟩ := hMmatch x hx y hy hne
        rcases hxy with ⟨h, _⟩ | ⟨h, _⟩
        · exact hl h
        · exact hr h
    · intro x hxS hxK
      rcases hMstab x hxS hxK with ⟨f, hfM, hfl, hfp⟩ | ⟨f, hfM, hfr, hfp⟩
      · exact ⟨f, hfM, Or.inl ⟨hfl.symm, hfp⟩⟩
      · refine ⟨f, hfM, Or.inr ⟨hfr.symm, ?_⟩⟩
        have := hle x; have := hle f; omega
  obtain ⟨φ, hφmem, hφ⟩ := kernel_coloring A hirr hker L (fun e => hL e)
  refine ⟨φ, hφmem, ?_⟩
  intro e f hef hadj
  rcases hadj with hl | hr
  · rcases lt_trichotomy (ru e) (ru f) with h | h | h
    · exact hφ e f (Or.inl ⟨hl, h⟩)
    · exact absurd (hru e f hl h) hef
    · exact (hφ f e (Or.inl ⟨hl.symm, h⟩)).symm
  · rcases lt_trichotomy (rv e) (rv f) with h | h | h
    · exact (hφ f e (Or.inr ⟨hr.symm, h⟩)).symm
    · exact absurd (hrv e f hr h) hef
    · exact hφ e f (Or.inr ⟨hr, h⟩)
end GalvinMultigraph.Local
