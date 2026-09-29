-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianCanonical.numOp_coreState
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:53:30.213072+00:00
-- url     : https://prove2.me/submissions/052d97f6-8e52-44bc-90b9-0fff1f42b48b

-- Generated from ChapterNavierStokesLagrangianCanonical.lean — theorem BookProof.NavierStokesFlow.LagrangianCanonical.numOp_coreState
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianCanonical
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianCanonical
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato  BookProof.NavierStokesFlow.LagrangianKatoRellich
open BookProof.NavierStokesFlow.CanonicalVector BookProof.NavierStokesFlow.ThreeComponent














variable (nu : ℝ)
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


theorem solution (i : Fin 3) (β : Vel) :
    numOp i (coreState β) = ((β i : ℝ) : ℂ) • coreState β := by
  classical
  refine Subtype.ext (lp.ext (funext fun γ => ?_))
  change crd (numOp i (coreState β)) γ = (((β i : ℝ) : ℂ) * crd (coreState β) γ)
  rw [parent_crd_numOp]
  by_cases hg : γ = β
  · subst γ
    rfl
  · simp [crd, coreState, lp.single_apply, Pi.single_apply, hg, Ne.symm hg]

#print axioms solution
