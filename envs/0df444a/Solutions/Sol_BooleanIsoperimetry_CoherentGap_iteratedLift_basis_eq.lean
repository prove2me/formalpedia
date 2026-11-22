-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.iteratedLift_basis_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:48.432691+00:00
-- url     : https://prove2.me/submissions/290404f2-6fc8-47f5-b8ba-57135d2f88aa

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_lift_sub
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_basis
attribute [local simp] BooleanIsoperimetry.CoherentGap.realDot_basis



set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution {n : ℕ} (coordinate : Fin n) :
    ∀ {steps : ℕ} (hsteps : 0 < steps),
      iteratedLift (basis coordinate) steps =
        basis (⟨coordinate.val + steps, by omega⟩ : Fin (n + steps)) -
          basis (⟨steps - 1, by omega⟩ : Fin (n + steps))
  | 0, hsteps => by omega
  | 1, _ => by
      change lift (basis coordinate) =
        basis (⟨coordinate.val + 1, by omega⟩ : Fin (n + 1)) -
          basis (⟨1 - 1, by omega⟩ : Fin (n + 1))
      rw [lift_basis]
      have hpositive :
          coordinate.succ =
            (⟨coordinate.val + 1, by omega⟩ : Fin (n + 1)) := by
        apply Fin.ext
        simp
      have hnegative :
          (0 : Fin (n + 1)) =
            (⟨1 - 1, by omega⟩ : Fin (n + 1)) := by
        apply Fin.ext
        simp
      rw [hpositive, hnegative]
  | steps + 2, _ => by
      have inductionHypothesis :=
        solution coordinate (steps := steps + 1) (by omega)
      rw [iteratedLift, inductionHypothesis, lift_sub, lift_basis, lift_basis]
      have hpositive :
          (⟨coordinate.val + (steps + 1), by omega⟩ :
              Fin (n + (steps + 1))).succ =
            (⟨coordinate.val + (steps + 2), by omega⟩ :
              Fin (n + (steps + 2))) := by
        apply Fin.ext
        simp
        omega
      have hnegative :
          (⟨steps + 1 - 1, by omega⟩ :
              Fin (n + (steps + 1))).succ =
            (⟨steps + 2 - 1, by omega⟩ :
              Fin (n + (steps + 2))) := by
        apply Fin.ext
        simp
      rw [hpositive, hnegative]
      abel
end BooleanIsoperimetry.CoherentGap
