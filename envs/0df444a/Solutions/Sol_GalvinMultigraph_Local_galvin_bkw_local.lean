-- Prove2me | solution 1 for GalvinMultigraph.Local.galvin_bkw_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:19:02.352796+00:00
-- url     : https://prove2.me/submissions/a54afd1b-3a38-4b51-84d5-5d8a58ef2fd4

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
public import Theorems.Thm_GalvinMultigraph_Local_ranks_exist


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
theorem _root_.solution (left : E → U) (right : E → R)
    (L : E → Finset ℕ) (hL : ∀ e, max (degL left (left e)) (degR right (right e)) ≤ (L e).card) :
    ∃ φ : E → ℕ, (∀ e, φ e ∈ L e) ∧
      ∀ e f, e ≠ f → (left e = left f ∨ right e = right f) → φ e ≠ φ f := by
  classical
  -- The local slack of an edge: how much its right degree exceeds its left degree.
  set c : E → ℕ := fun e =>
    max (degL left (left e)) (degR right (right e)) - degL left (left e) with hc
  have hdegL : ∀ u, degLOn left Finset.univ u = degL left u := fun _ => rfl
  have hdegR : ∀ v, degROn right Finset.univ v = degR right v := fun _ => rfl
  have hmaxL : ∀ e : E, degL left (left e) ≤ max (degL left (left e)) (degR right (right e)) :=
    fun e => le_max_left _ _
  have hmaxR : ∀ e : E, degR right (right e) ≤ max (degL left (left e)) (degR right (right e)) :=
    fun e => le_max_right _ _
  obtain ⟨pL, pR, hbL, hbR, hiL, hiR, hcle⟩ :=
    ranks_exist left right c Finset.univ (fun _ => 0) (fun _ => 0)
      (fun e _ => Nat.zero_le _)
      (by
        intro e _
        have h1 := hmaxL e
        have h2 := hmaxR e
        simp only [hdegL, hdegR, hc, Nat.zero_add]
        omega)
  refine galvin_engine left right pL pR (fun e f hlf hval => hiL e (Finset.mem_univ e) f
      (Finset.mem_univ f) hlf hval)
    (fun e f hrf hval => hiR e (Finset.mem_univ e) f (Finset.mem_univ f) hrf hval) L ?_
  intro e
  have hbLe := hbL e (Finset.mem_univ e)
  have hbRe := hbR e (Finset.mem_univ e)
  rw [hdegL] at hbLe
  rw [hdegR] at hbRe
  -- The edges above `e` at its left endpoint.
  have hA : (Finset.univ.filter fun f => left e = left f ∧ pL e < pL f).card
      ≤ degL left (left e) - 1 - pL e := by
    have hinj : Set.InjOn pL ↑(Finset.univ.filter fun f => left e = left f ∧ pL e < pL f) := by
      intro x hx y hy hxy
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
      exact hiL x (Finset.mem_univ x) y (Finset.mem_univ y) (hx.2.1.symm.trans hy.2.1) hxy
    have hsub : (Finset.univ.filter fun f => left e = left f ∧ pL e < pL f).image pL ⊆
        Finset.Ico (pL e + 1) (degL left (left e)) := by
      intro k hk
      simp only [Finset.mem_image, Finset.mem_filter] at hk
      obtain ⟨f, hf, rfl⟩ := hk
      have := hbL f (Finset.mem_univ f)
      rw [hdegL, ← hf.2.1] at this
      obtain ⟨_, hup⟩ := this
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    calc (Finset.univ.filter fun f => left e = left f ∧ pL e < pL f).card
          = ((Finset.univ.filter fun f => left e = left f ∧ pL e < pL f).image pL).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.Ico (pL e + 1) (degL left (left e))).card := Finset.card_le_card hsub
      _ = degL left (left e) - 1 - pL e := by rw [Nat.card_Ico]; omega
  -- The edges below `e` at its right endpoint.
  have hB : (Finset.univ.filter fun f => right e = right f ∧ pR f < pR e).card ≤ pR e := by
    have hinj : Set.InjOn pR ↑(Finset.univ.filter fun f => right e = right f ∧ pR f < pR e) := by
      intro x hx y hy hxy
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx hy
      exact hiR x (Finset.mem_univ x) y (Finset.mem_univ y) (hx.2.1.symm.trans hy.2.1) hxy
    have hsub : (Finset.univ.filter fun f => right e = right f ∧ pR f < pR e).image pR ⊆
        Finset.range (pR e) := by
      intro k hk
      simp only [Finset.mem_image, Finset.mem_filter] at hk
      obtain ⟨f, hf, rfl⟩ := hk
      exact Finset.mem_range.mpr hf.2.2
    calc (Finset.univ.filter fun f => right e = right f ∧ pR f < pR e).card
          = ((Finset.univ.filter fun f => right e = right f ∧ pR f < pR e).image pR).card :=
          (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range (pR e)).card := Finset.card_le_card hsub
      _ = pR e := Finset.card_range _
  have hsplit : (Finset.univ.filter fun f =>
      (left e = left f ∧ pL e < pL f) ∨ (right e = right f ∧ pR f < pR e)).card ≤
      (Finset.univ.filter fun f => left e = left f ∧ pL e < pL f).card +
        (Finset.univ.filter fun f => right e = right f ∧ pR f < pR e).card := by
    rw [Finset.filter_or]
    exact Finset.card_union_le _ _
  have hcl := hcle e (Finset.mem_univ e)
  have hLe := hL e
  have h1 := hmaxL e
  have h2 := hmaxR e
  have hcval : c e = max (degL left (left e)) (degR right (right e)) - degL left (left e) := rfl
  omega
end GalvinMultigraph.Local
