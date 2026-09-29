-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianCanonical.crd_numOp
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:45:07.70661+00:00
-- url     : https://prove2.me/submissions/db52e0d4-e344-495d-9e5a-5422a2439bef

-- Generated from ChapterNavierStokesLagrangianCanonical.lean — theorem BookProof.NavierStokesFlow.LagrangianCanonical.crd_numOp
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianCanonical
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato  BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.ThreeComponent
set_option autoImplicit false

theorem solution (i : Fin 3) (x : lpFiniteModes Vel) :
    crd (numOp i x) = fun β => ((β i : ℝ) : ℂ) * crd x β := by
  funext β
  change (Real.sqrt (β i) : ℂ) * ((Real.sqrt (((lower i β) i : ℝ) + 1) : ℂ) * crd x (raise i (lower i β))) = _
  by_cases hzero : β i = 0
  · simp [hzero]
  · have hp : 1 ≤ β i := Nat.one_le_iff_ne_zero.mpr hzero
    rw [raise_lower i hp, lower_self]
    have ht : ((β i - 1 : ℕ) : ℝ) + 1 = (β i : ℝ) := by
      rw [Nat.cast_sub hp]
      norm_num
    rw [ht]
    have hr : (Real.sqrt (β i) : ℂ) * (Real.sqrt (β i) : ℂ) = (β i : ℂ) := by
      norm_cast
      exact Real.mul_self_sqrt (by positivity)
    rw [← mul_assoc, hr]
    norm_cast

#print axioms solution
