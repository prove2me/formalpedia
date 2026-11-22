-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.coordinate_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:28:16.706514+00:00
-- url     : https://prove2.me/submissions/42f5ad64-d48d-45e0-9f9a-9124db4888cb

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_Certificate_length_eq_dot_target
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_aggregate
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_realDot_basis
attribute [local simp] BooleanIsoperimetry.CoherentGap.realDot_basis

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution {n : ℕ} {weights : Relation n}
    {coordinate : Fin n} (certificate : Certificate weights (basis coordinate))
    (candidate : Fin n → ℝ)
    (hgap : ∀ relation, IsLiftableUnit weights relation →
      1 ≤ realDot relation candidate) :
    (weights coordinate : ℝ) ≤ candidate coordinate := by
  have hsumGeneral : ∀ relations : List (Relation n),
      (∀ relation ∈ relations, IsLiftableUnit weights relation) →
        (relations.length : ℝ) ≤
          (relations.map fun relation => realDot relation candidate).sum := by
    intro relations
    induction relations with
    | nil =>
        intro
        simp
    | cons relation relations inductionHypothesis =>
        intro hvalid
        have hhead := hgap relation (hvalid relation List.mem_cons_self)
        have htail :
            ∀ tailRelation ∈ relations,
              IsLiftableUnit weights tailRelation := by
          intro tailRelation htailRelation
          exact hvalid tailRelation (List.mem_cons_of_mem relation htailRelation)
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons,
          List.sum_cons]
        simpa [add_comm] using add_le_add hhead (inductionHypothesis htail)
  have hsum := hsumGeneral certificate.relations certificate.valid
  have hlength :
      (certificate.relations.length : ℝ) = (weights coordinate : ℝ) := by
    exact_mod_cast certificate.length_eq_dot_target.trans (dot_basis coordinate weights)
  rw [hlength] at hsum
  calc
    (weights coordinate : ℝ) ≤
        (certificate.relations.map fun relation =>
          realDot relation candidate).sum := hsum
    _ = realDot (aggregate certificate.relations) candidate :=
      (realDot_aggregate certificate.relations candidate).symm
    _ = realDot (basis coordinate) candidate :=
      congrArg (fun relation => realDot relation candidate) certificate.target_eq
    _ = candidate coordinate := realDot_basis coordinate candidate
end BooleanIsoperimetry.CoherentGap
