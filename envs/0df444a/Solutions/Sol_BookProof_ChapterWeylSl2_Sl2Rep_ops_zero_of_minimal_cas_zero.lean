-- Prove2me | solution 1 for BookProof.ChapterWeylSl2.Sl2Rep.ops_zero_of_minimal_cas_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T15:06:20.620196+00:00
-- url     : https://prove2.me/submissions/149e27bb-ec4d-472b-ad56-e481d4384410

-- Generated from ChapterWeylSl2.lean — theorem BookProof.ChapterWeylSl2.Sl2Rep.ops_zero_of_minimal_cas_zero
import Mathlib
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_exists_highestWeight
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_highestWeight_nat
import Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_cas_highestWeight
import Definitions.Def_ChapterWeylSl2
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterGleasonPureMixed
open BookProof.ChapterDoubleSlit
open BookProof.ChapterGleasonPureMixed
open BookProof.ChapterWeylSl2
open BookProof.ChapterWeylSl2



universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable (R : Sl2Rep V)
variable {R}
variable {R : Sl2Rep V}
open BookProof.ChapterWeylSl2.Sl2Rep in
theorem solution [FiniteDimensional ℂ V] {W : Submodule ℂ V}
    (hW : R.IsInv W) (hne : W ≠ ⊥) (hmin : ∀ U ≤ W, R.IsInv U → U = ⊥ ∨ U = W)
    (hcas : ∀ x ∈ W, R.cas x = 0) : ∀ x ∈ W, R.E x = 0 ∧ R.F x = 0 ∧ R.H x = 0 := by 
  classical
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨w, lam, hw0, hEw, hHw⟩ := BookProof.ChapterWeylSl2.Sl2Rep.exists_highestWeight (R.restr W hW)
  have hE : R.E (w : V) = 0 := by
    have := congrArg Subtype.val hEw
    simpa [BookProof.ChapterWeylSl2.Sl2Rep.restr, LinearMap.restrict_coe_apply] using this
  have hH : R.H (w : V) = lam • (w : V) := by
    have := congrArg Subtype.val hHw
    simpa [BookProof.ChapterWeylSl2.Sl2Rep.restr, LinearMap.restrict_coe_apply] using this
  have hw0' : (w : V) ≠ 0 := by
    intro h; apply hw0; exact Subtype.ext h
  obtain ⟨m, hm, hF⟩ := BookProof.ChapterWeylSl2.Sl2Rep.highestWeight_nat hw0' hE hH
  have hc := BookProof.ChapterWeylSl2.Sl2Rep.cas_highestWeight hE hH
  rw [hcas w w.2] at hc
  have h0 : lam ^ 2 + 2 * lam = 0 := by
    by_contra h
    exact hw0' ((smul_eq_zero.mp hc.symm).resolve_left h)
  rw [hm] at h0
  have hm0 : m = 0 := by
    have : ((m ^ 2 + 2 * m : ℕ) : ℂ) = 0 := by push_cast; exact h0
    have : m ^ 2 + 2 * m = 0 := by exact_mod_cast this
    nlinarith
  subst hm0
  have hF' : R.F (w : V) = 0 := by simpa using hF
  have hH' : R.H (w : V) = 0 := by rw [hH, hm]; simp
  set U := Submodule.span ℂ {(w : V)} with hUdef
  have hU : R.IsInv U := by
    refine ⟨?_, ?_, ?_⟩ <;>
    · intro x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      simp [hE, hF', hH']
  have hUW : U ≤ W := by
    rw [hUdef, Submodule.span_le, Set.singleton_subset_iff]; exact w.2
  rcases hmin U hUW hU with h | h
  · exfalso
    have : (w : V) ∈ U := Submodule.mem_span_singleton_self _
    rw [h, Submodule.mem_bot] at this
    exact hw0' this
  · intro x hx
    rw [← h] at hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    simp [hE, hF', hH']
