-- Prove2me | solution 1 for ContWeatherall.full_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:37:53.288642+00:00
-- url     : https://prove2.me/submissions/9518cfe8-f285-4bc9-bb5b-1f567d38ad51

import Mathlib
import Definitions.Def_ContWeatherall_defs

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff
open ContWeatherall
/-- If some potential exists, `A ↦ dA` is full iff `H¹ = 0`. -/


theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (P : (E → E [⋀^Fin 2]→L[ℝ] F) → Prop) [Nonempty (Pot P)] :
    (fieldStrength P).Full ↔ H1Vanishes E F := by
  obtain ⟨A0⟩ := ‹Nonempty (Pot P)›
  have hd : ∀ {w : E → E [⋀^Fin 1]→L[ℝ] F}, ContDiff ℝ ∞ w → Differentiable ℝ w :=
    fun h => h.differentiable (by simp)
  constructor
  · intro hfull w hw hdw
    have hsum : extDeriv (A0.pot + w) = extDeriv A0.pot := by
      funext x
      rw [extDeriv_add (hd A0.smooth x) (hd hw x), hdw]
      simp
    let A' : Pot P := ⟨A0.pot + w, A0.smooth.add hw, by rw [hsum]; exact A0.field_eq⟩
    have heq : (fieldStrength P).obj A0 = (fieldStrength P).obj A' := by
      show Discrete.mk _ = Discrete.mk _
      congr 1
      exact Subtype.ext hsum.symm
    obtain ⟨f, -⟩ := hfull.map_surjective (eqToHom heq)
    refine ⟨f.chi, f.smooth, ?_⟩
    have := f.eq
    exact add_left_cancel this
  · intro hH
    refine ⟨fun {A A'} φ => ?_⟩
    have h := Discrete.eq_of_hom φ
    have hAA : extDeriv A.pot = extDeriv A'.pot := congrArg Subtype.val h
    have hw : ContDiff ℝ ∞ (A'.pot - A.pot) := A'.smooth.sub A.smooth
    have hdw : extDeriv (A'.pot - A.pot) = 0 := by
      funext x
      have e1 : A'.pot = A.pot + (A'.pot - A.pot) := by abel
      have e2 := congrFun hAA x
      rw [e1, extDeriv_add (hd A.smooth x) (hd hw x)] at e2
      have e3 : extDeriv A.pot x + 0 = extDeriv A.pot x + extDeriv (A'.pot - A.pot) x := by
        rw [add_zero]; exact e2
      exact (add_left_cancel e3).symm
    obtain ⟨χ, hχ, hgχ⟩ := hH _ hw hdw
    refine ⟨(⟨χ, hχ, by rw [hgχ]; abel⟩ : GaugeHom A A'), Subsingleton.elim _ _⟩


