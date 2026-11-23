-- Prove2me | solution 1 for CompanionTheory.D.Inhab.exp_entry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:13:53.570247+00:00
-- url     : https://prove2.me/submissions/c2422fed-ee8d-47c2-a673-7a14709d494c

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_ExpEntry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Inhab
namespace CompanionTheory.D.Inhab
theorem _root_.solution (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (i j : Fin N) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) (X i j) 0 := by
  let _ := Matrix.linftyOpNormedRing (n := Fin N) (α := ℂ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := Fin N) (α := ℂ)
  have : CompleteSpace (Matrix (Fin N) (Fin N) ℂ) := FiniteDimensional.complete ℝ _
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L0 : Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let L : Matrix (Fin N) (Fin N) ℂ →L[ℝ] ℂ := LinearMap.toContinuousLinearMap L0
  have h2 := L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  have e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) = L ∘ fun u : ℝ => NormedSpace.exp (u • X) := by
    funext t
    simp only [Function.comp_apply, Complex.coe_smul]
    rfl
  rw [e]
  exact h2
end CompanionTheory.D.Inhab
