-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianCanonical.ann_comp_cre_eq
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:53:29.403917+00:00
-- url     : https://prove2.me/submissions/f4dcd071-6b0c-4345-985d-5afb84fae31a

-- Generated from ChapterNavierStokesLagrangianCanonical.lean — theorem BookProof.NavierStokesFlow.LagrangianCanonical.ann_comp_cre_eq
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianCanonical
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato  BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.ThreeComponent
set_option autoImplicit false
private theorem parent_crd_numOp (i : Fin 3) (x : lpFiniteModes Vel) :
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


theorem solution (i : Fin 3) :
    (ann i).comp (cre i) = (cre i).comp (ann i) + LinearMap.id := by
  classical
  ext x β
  change crd (ann i (cre i x)) β = crd (numOp i x) β + crd x β
  rw [parent_crd_numOp]
  change (Real.sqrt ((β i : ℝ) + 1) : ℂ) *
      ((Real.sqrt ((raise i β) i) : ℂ) * crd x (lower i (raise i β))) = _
  have hl : lower i (raise i β) = β := by
    funext j
    by_cases hj : j = i
    · subst j
      rw [lower_self, raise_self]
      omega
    · rw [lower_of_ne hj, raise_of_ne hj]
  rw [hl, raise_self]
  push_cast
  rw [← mul_assoc, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  push_cast
  ring

#print axioms solution
