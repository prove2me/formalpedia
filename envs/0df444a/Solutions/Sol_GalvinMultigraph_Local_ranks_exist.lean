-- Prove2me | solution 1 for GalvinMultigraph.Local.ranks_exist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:11:51.028691+00:00
-- url     : https://prove2.me/submissions/b476699e-3fa0-44f3-9d9c-fc632d255167

module
public import Definitions.Def_GalvinMultigraph_Local_Konig
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Choose
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Set
public import Definitions.Def_GalvinMultigraph_Local_Ranks
public import Theorems.Thm_GalvinMultigraph_Local_degLOn_le_of_subset
public import Theorems.Thm_GalvinMultigraph_Local_degROn_le_of_subset
public import Theorems.Thm_GalvinMultigraph_Local_degLOn_sdiff_covered
public import Theorems.Thm_GalvinMultigraph_Local_degROn_sdiff_covered
public import Theorems.Thm_GalvinMultigraph_Local_degLOn_sdiff_uncovered
public import Theorems.Thm_GalvinMultigraph_Local_degROn_sdiff_uncovered
public import Theorems.Thm_GalvinMultigraph_Local_degLOn_pos
public import Theorems.Thm_GalvinMultigraph_Local_degROn_pos
public import Theorems.Thm_GalvinMultigraph_Local_matching_dichotomy

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false
open GalvinMultigraph GalvinMultigraph.Local
variable {U R E : Type*} [Fintype U] [Fintype R] [Fintype E]
  [DecidableEq U] [DecidableEq R] [DecidableEq E]
omit [Fintype R] [Fintype E]
namespace GalvinMultigraph.Local
theorem _root_.solution (left : E → U) (right : E → R) (c : E → ℕ) (S : Finset E) :
    ∀ aL : U → ℕ, ∀ aR : R → ℕ,
    (∀ e ∈ S, aR (right e) ≤ aL (left e) + c e) →
    (∀ e ∈ S, aR (right e) + degROn right S (right e)
        ≤ aL (left e) + degLOn left S (left e) + c e) →
    ∃ pL pR : E → ℕ,
      (∀ e ∈ S, aL (left e) ≤ pL e ∧ pL e < aL (left e) + degLOn left S (left e)) ∧
      (∀ e ∈ S, aR (right e) ≤ pR e ∧ pR e < aR (right e) + degROn right S (right e)) ∧
      (∀ e ∈ S, ∀ f ∈ S, left e = left f → pL e = pL f → e = f) ∧
      (∀ e ∈ S, ∀ f ∈ S, right e = right f → pR e = pR f → e = f) ∧
      (∀ e ∈ S, pR e ≤ pL e + c e) := by
  classical
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro aL aR h1 h2
    rcases S.eq_empty_or_nonempty with rfl | hS
    · exact ⟨fun _ => 0, fun _ => 0, by simp, by simp, by simp, by simp, by simp⟩
    obtain ⟨M, hMS, hMne, hM, hcase⟩ := matching_dichotomy left right S hS
    obtain ⟨m0, hm0⟩ := hMne
    have hssub : S \ M ⊂ S := by
      refine Finset.ssubset_iff_of_subset Finset.sdiff_subset |>.2 ⟨m0, hMS hm0, ?_⟩
      simp [Finset.mem_sdiff, hm0]
    -- degree bookkeeping
    have hdL1 : ∀ m ∈ M, degLOn left S (left m) = degLOn left (S \ M) (left m) + 1 :=
      fun m hm => degLOn_sdiff_covered left right S M hM hMS hm
    have hdR1 : ∀ m ∈ M, degROn right S (right m) = degROn right (S \ M) (right m) + 1 :=
      fun m hm => degROn_sdiff_covered left right S M hM hMS hm
    have hdL0 : ∀ u, (∀ m ∈ M, left m ≠ u) → degLOn left (S \ M) u = degLOn left S u :=
      fun u h => degLOn_sdiff_uncovered left S M u h
    have hdR0 : ∀ v, (∀ m ∈ M, right m ≠ v) → degROn right (S \ M) v = degROn right S v :=
      fun v h => degROn_sdiff_uncovered right S M v h
    have hdLle : ∀ u, degLOn left (S \ M) u ≤ degLOn left S u :=
      fun u => degLOn_le_of_subset left Finset.sdiff_subset u
    have hdRle : ∀ v, degROn right (S \ M) v ≤ degROn right S v :=
      fun v => degROn_le_of_subset right Finset.sdiff_subset v
    -- the covered-degree identities in the form used repeatedly below
    have hdLcov : ∀ u, (∃ m ∈ M, left m = u) →
        degLOn left S u = degLOn left (S \ M) u + 1 := by
      rintro u ⟨m, hm, rfl⟩; exact hdL1 m hm
    have hdRcov : ∀ v, (∃ m ∈ M, right m = v) →
        degROn right S v = degROn right (S \ M) v + 1 := by
      rintro v ⟨m, hm, rfl⟩; exact hdR1 m hm
    rcases hcase with hA | hB
    · -- Case A: `M` covers every left vertex; place it at the bottom of both orders.
      set aL' : U → ℕ := fun u => aL u + (if (∃ m ∈ M, left m = u) then 1 else 0) with haL'
      set aR' : R → ℕ := fun v => aR v + (if (∃ m ∈ M, right m = v) then 1 else 0) with haR'
      have hcovL : ∀ e ∈ S \ M, (∃ m ∈ M, left m = left e) := by
        intro e he
        exact hA e (Finset.mem_sdiff.mp he).1
      have h1' : ∀ e ∈ S \ M, aR' (right e) ≤ aL' (left e) + c e := by
        intro e he
        have hx : (∃ m ∈ M, left m = left e) := hcovL e he
        have := h1 e (Finset.mem_sdiff.mp he).1
        simp only [haL', haR', hx, ite_true]
        split <;> omega
      have h2' : ∀ e ∈ S \ M, aR' (right e) + degROn right (S \ M) (right e)
          ≤ aL' (left e) + degLOn left (S \ M) (left e) + c e := by
        intro e he
        have hx : (∃ m ∈ M, left m = left e) := hcovL e he
        have hxd := hdLcov (left e) hx
        have hb := h2 e (Finset.mem_sdiff.mp he).1
        simp only [haL', haR', hx, ite_true]
        by_cases hy : (∃ m ∈ M, right m = right e)
        · have hyd := hdRcov (right e) hy
          simp only [hy, ite_true]
          omega
        · have hyd := hdR0 (right e) (by push Not at hy; intro m hm; exact hy m hm)
          simp only [hy, ite_false]
          omega
      obtain ⟨pL', pR', hbL', hbR', hiL', hiR', hc'⟩ := ih (S \ M) hssub aL' aR' h1' h2'
      refine ⟨fun e => if e ∈ M then aL (left e) else pL' e,
              fun e => if e ∈ M then aR (right e) else pR' e, ?_, ?_, ?_, ?_, ?_⟩
      · intro e he
        by_cases hem : e ∈ M
        · simp only [hem, ite_true]
          have := degLOn_pos left he
          omega
        · have heS : e ∈ S \ M := Finset.mem_sdiff.mpr ⟨he, hem⟩
          have hx : (∃ m ∈ M, left m = left e) := hcovL e heS
          have hxd := hdLcov (left e) hx
          have := hbL' e heS
          simp only [hem, ite_false, haL', hx, ite_true] at this ⊢
          omega
      · intro e he
        by_cases hem : e ∈ M
        · simp only [hem, ite_true]
          have := degROn_pos right he
          omega
        · have heS : e ∈ S \ M := Finset.mem_sdiff.mpr ⟨he, hem⟩
          have hb := hbR' e heS
          simp only [hem, ite_false]
          by_cases hy : (∃ m ∈ M, right m = right e)
          · have hyd := hdRcov (right e) hy
            simp only [haR', hy, ite_true] at hb
            omega
          · have hyd := hdR0 (right e) (by push Not at hy; intro m hm; exact hy m hm)
            simp only [haR', hy, ite_false] at hb
            omega
      · intro e he f hf hlef hval
        by_cases hem : e ∈ M <;> by_cases hfm : f ∈ M
        · by_contra hne
          exact (hM e hem f hfm hne).1 hlef
        · exfalso
          have hfS : f ∈ S \ M := Finset.mem_sdiff.mpr ⟨hf, hfm⟩
          have hx : (∃ m ∈ M, left m = left f) := hcovL f hfS
          have hb := (hbL' f hfS).1
          simp only [hem, ite_true, hfm, ite_false] at hval
          simp only [haL', hx, ite_true] at hb
          rw [hlef] at hval
          omega
        · exfalso
          have heS : e ∈ S \ M := Finset.mem_sdiff.mpr ⟨he, hem⟩
          have hx : (∃ m ∈ M, left m = left e) := hcovL e heS
          have hb := (hbL' e heS).1
          simp only [hem, ite_false, hfm, ite_true] at hval
          simp only [haL', hx, ite_true] at hb
          rw [← hlef] at hval
          omega
        · simp only [hem, ite_false, hfm, ite_false] at hval
          exact hiL' e (Finset.mem_sdiff.mpr ⟨he, hem⟩) f (Finset.mem_sdiff.mpr ⟨hf, hfm⟩) hlef hval
      · intro e he f hf hlef hval
        by_cases hem : e ∈ M <;> by_cases hfm : f ∈ M
        · by_contra hne
          exact (hM e hem f hfm hne).2 hlef
        · exfalso
          have hfS : f ∈ S \ M := Finset.mem_sdiff.mpr ⟨hf, hfm⟩
          have hy : (∃ m ∈ M, right m = right f) := ⟨e, hem, hlef⟩
          have hb := (hbR' f hfS).1
          simp only [hem, ite_true, hfm, ite_false] at hval
          simp only [haR', hy, ite_true] at hb
          rw [hlef] at hval
          omega
        · exfalso
          have heS : e ∈ S \ M := Finset.mem_sdiff.mpr ⟨he, hem⟩
          have hy : (∃ m ∈ M, right m = right e) := ⟨f, hfm, hlef.symm⟩
          have hb := (hbR' e heS).1
          simp only [hem, ite_false, hfm, ite_true] at hval
          simp only [haR', hy, ite_true] at hb
          rw [← hlef] at hval
          omega
        · simp only [hem, ite_false, hfm, ite_false] at hval
          exact hiR' e (Finset.mem_sdiff.mpr ⟨he, hem⟩) f (Finset.mem_sdiff.mpr ⟨hf, hfm⟩) hlef hval
      · intro e he
        by_cases hem : e ∈ M
        · simp only [hem, ite_true]
          exact h1 e he
        · simp only [hem, ite_false]
          exact hc' e (Finset.mem_sdiff.mpr ⟨he, hem⟩)
    · -- Case B: neighbours of covered left vertices are covered; place `M` at the top.
      have h1' : ∀ e ∈ S \ M, aR (right e) ≤ aL (left e) + c e :=
        fun e he => h1 e (Finset.mem_sdiff.mp he).1
      have h2' : ∀ e ∈ S \ M, aR (right e) + degROn right (S \ M) (right e)
          ≤ aL (left e) + degLOn left (S \ M) (left e) + c e := by
        intro e he
        have heS := (Finset.mem_sdiff.mp he).1
        have hb := h2 e heS
        by_cases hx : (∃ m ∈ M, left m = left e)
        · have hy := hB e heS hx
          have hxd := hdLcov (left e) hx
          have hyd := hdRcov (right e) hy
          omega
        · have hxd := hdL0 (left e) (by push Not at hx; intro m hm; exact hx m hm)
          have hyd := hdRle (right e)
          omega
      obtain ⟨pL', pR', hbL', hbR', hiL', hiR', hc'⟩ := ih (S \ M) hssub aL aR h1' h2'
      refine ⟨fun e => if e ∈ M then aL (left e) + degLOn left S (left e) - 1 else pL' e,
              fun e => if e ∈ M then aR (right e) + degROn right S (right e) - 1 else pR' e,
              ?_, ?_, ?_, ?_, ?_⟩
      · intro e he
        by_cases hem : e ∈ M
        · simp only [hem, ite_true]
          have := degLOn_pos left he
          omega
        · have := hbL' e (Finset.mem_sdiff.mpr ⟨he, hem⟩)
          have hle := hdLle (left e)
          simp only [hem, ite_false]
          omega
      · intro e he
        by_cases hem : e ∈ M
        · simp only [hem, ite_true]
          have := degROn_pos right he
          omega
        · have := hbR' e (Finset.mem_sdiff.mpr ⟨he, hem⟩)
          have hle := hdRle (right e)
          simp only [hem, ite_false]
          omega
      · intro e he f hf hlef hval
        by_cases hem : e ∈ M <;> by_cases hfm : f ∈ M
        · by_contra hne
          exact (hM e hem f hfm hne).1 hlef
        · exfalso
          have hfS : f ∈ S \ M := Finset.mem_sdiff.mpr ⟨hf, hfm⟩
          have hx : (∃ m ∈ M, left m = left f) := ⟨e, hem, hlef⟩
          have hxd := hdLcov (left f) hx
          have := (hbL' f hfS).2
          simp only [hem, ite_true, hfm, ite_false] at hval
          rw [hlef] at hval
          omega
        · exfalso
          have heS : e ∈ S \ M := Finset.mem_sdiff.mpr ⟨he, hem⟩
          have hx : (∃ m ∈ M, left m = left e) := ⟨f, hfm, hlef.symm⟩
          have hxd := hdLcov (left e) hx
          have := (hbL' e heS).2
          simp only [hem, ite_false, hfm, ite_true] at hval
          rw [← hlef] at hval
          omega
        · simp only [hem, ite_false, hfm, ite_false] at hval
          exact hiL' e (Finset.mem_sdiff.mpr ⟨he, hem⟩) f (Finset.mem_sdiff.mpr ⟨hf, hfm⟩) hlef hval
      · intro e he f hf hlef hval
        by_cases hem : e ∈ M <;> by_cases hfm : f ∈ M
        · by_contra hne
          exact (hM e hem f hfm hne).2 hlef
        · exfalso
          have hfS : f ∈ S \ M := Finset.mem_sdiff.mpr ⟨hf, hfm⟩
          have hy : (∃ m ∈ M, right m = right f) := ⟨e, hem, hlef⟩
          have hyd := hdRcov (right f) hy
          have := (hbR' f hfS).2
          simp only [hem, ite_true, hfm, ite_false] at hval
          rw [hlef] at hval
          omega
        · exfalso
          have heS : e ∈ S \ M := Finset.mem_sdiff.mpr ⟨he, hem⟩
          have hy : (∃ m ∈ M, right m = right e) := ⟨f, hfm, hlef.symm⟩
          have hyd := hdRcov (right e) hy
          have := (hbR' e heS).2
          simp only [hem, ite_false, hfm, ite_true] at hval
          rw [← hlef] at hval
          omega
        · simp only [hem, ite_false, hfm, ite_false] at hval
          exact hiR' e (Finset.mem_sdiff.mpr ⟨he, hem⟩) f (Finset.mem_sdiff.mpr ⟨hf, hfm⟩) hlef hval
      · intro e he
        by_cases hem : e ∈ M
        · simp only [hem, ite_true]
          have hb := h2 e he
          have := degLOn_pos left he
          have := degROn_pos right he
          omega
        · simp only [hem, ite_false]
          exact hc' e (Finset.mem_sdiff.mpr ⟨he, hem⟩)
end GalvinMultigraph.Local
