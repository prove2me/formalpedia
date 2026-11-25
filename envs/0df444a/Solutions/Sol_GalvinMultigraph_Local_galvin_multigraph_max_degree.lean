-- Prove2me | solution 1 for GalvinMultigraph.Local.galvin_multigraph_max_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:18:30.291715+00:00
-- url     : https://prove2.me/submissions/7f2116f8-88d3-4df7-805b-7807bd39a41f

module
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Set
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_GalvinMultigraph_Local_Kernel
public import Definitions.Def_GalvinMultigraph_Local_Ranks
public import Definitions.Def_GalvinMultigraph_Local_Main
public import Theorems.Thm_GalvinMultigraph_Local_galvin_engine
public import Theorems.Thm_GalvinMultigraph_Local_konig_multigraph


set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
open GalvinMultigraph GalvinMultigraph.Local
variable {U R E : Type*} [Fintype U] [Fintype R] [Fintype E] [DecidableEq U] [DecidableEq R]
    [DecidableEq E]
namespace GalvinMultigraph.Local
theorem _root_.solution (left : E → U) (right : E → R) (Δ : ℕ)
    (hdegU : ∀ u, degL left u ≤ Δ) (hdegR : ∀ r, degR right r ≤ Δ)
    (L : E → Finset ℕ) (hL : ∀ e, Δ ≤ (L e).card) :
    ∃ φ : E → ℕ, (∀ e, φ e ∈ L e) ∧
      ∀ e f, e ≠ f → (left e = left f ∨ right e = right f) → φ e ≠ φ f := by
  classical
  rcases Nat.eq_zero_or_pos Δ with rfl | hΔ
  · -- With `Δ = 0` the multigraph has no edges at all.
    have hempty : ∀ e : E, False := by
      intro e
      have h1 : 1 ≤ degL left (left e) := by
        refine Finset.card_pos.mpr ⟨e, ?_⟩
        simp
      have := hdegU (left e); omega
    exact ⟨fun _ => 0, fun e => (hempty e).elim, fun e => (hempty e).elim⟩
  · obtain ⟨φ0, hφ0lt, hφ0⟩ :=
      konig_multigraph left right Finset.univ Δ (fun u => hdegU u) (fun r => hdegR r)
    have hφ0lt' : ∀ e, φ0 e < Δ := fun e => hφ0lt e (Finset.mem_univ e)
    have hproper : ∀ e f, e ≠ f → (left e = left f ∨ right e = right f) → φ0 e ≠ φ0 f :=
      fun e f h h' => hφ0 e (Finset.mem_univ e) f (Finset.mem_univ f) h h'
    refine galvin_engine left right φ0 φ0 ?_ ?_ L ?_
    · intro e f hlf hcol
      by_contra hne
      exact hproper e f hne (Or.inl hlf) hcol
    · intro e f hrf hcol
      by_contra hne
      exact hproper e f hne (Or.inr hrf) hcol
    · intro e
      have hA : (Finset.univ.filter fun f => left e = left f ∧ φ0 e < φ0 f).card ≤ Δ - 1 - φ0 e :=
          by
        have hinj : Set.InjOn φ0 ↑(Finset.univ.filter fun f => left e = left f ∧ φ0 e < φ0 f) := by
          intro x hx y hy hxy
          simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
          by_contra hne
          exact hproper x y hne (Or.inl (hx.2.1.symm.trans hy.2.1)) hxy
        have hsub : (Finset.univ.filter fun f => left e = left f ∧ φ0 e < φ0 f).image φ0 ⊆
            Finset.Icc (φ0 e + 1) (Δ - 1) := by
          intro c hc
          simp only [Finset.mem_image, Finset.mem_filter] at hc
          obtain ⟨f, hf, rfl⟩ := hc
          have := hφ0lt' f
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        calc (Finset.univ.filter fun f => left e = left f ∧ φ0 e < φ0 f).card
              = ((Finset.univ.filter fun f => left e = left f ∧ φ0 e < φ0 f).image φ0).card :=
              (Finset.card_image_of_injOn hinj).symm
          _ ≤ (Finset.Icc (φ0 e + 1) (Δ - 1)).card := Finset.card_le_card hsub
          _ = Δ - 1 - φ0 e := by rw [Nat.card_Icc]; omega
      have hB : (Finset.univ.filter fun f => right e = right f ∧ φ0 f < φ0 e).card ≤ φ0 e := by
        have hinj : Set.InjOn φ0 ↑(Finset.univ.filter fun f => right e = right f ∧ φ0 f < φ0 e) :=
            by
          intro x hx y hy hxy
          simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
          by_contra hne
          exact hproper x y hne (Or.inr (hx.2.1.symm.trans hy.2.1)) hxy
        have hsub : (Finset.univ.filter fun f => right e = right f ∧ φ0 f < φ0 e).image φ0 ⊆
            Finset.range (φ0 e) := by
          intro c hc
          simp only [Finset.mem_image, Finset.mem_filter] at hc
          obtain ⟨f, hf, rfl⟩ := hc
          exact Finset.mem_range.mpr hf.2.2
        calc (Finset.univ.filter fun f => right e = right f ∧ φ0 f < φ0 e).card
              = ((Finset.univ.filter fun f => right e = right f ∧ φ0 f < φ0 e).image φ0).card :=
              (Finset.card_image_of_injOn hinj).symm
          _ ≤ (Finset.range (φ0 e)).card := Finset.card_le_card hsub
          _ = φ0 e := Finset.card_range _
      have hsplit : (Finset.univ.filter fun f =>
          (left e = left f ∧ φ0 e < φ0 f) ∨ (right e = right f ∧ φ0 f < φ0 e)).card ≤
          (Finset.univ.filter fun f => left e = left f ∧ φ0 e < φ0 f).card +
            (Finset.univ.filter fun f => right e = right f ∧ φ0 f < φ0 e).card := by
        rw [Finset.filter_or]
        exact Finset.card_union_le _ _
      have hlt := hφ0lt' e
      have hLe := hL e
      omega
end GalvinMultigraph.Local
