-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.Certificate.length_eq_dot_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:27:27.221178+00:00
-- url     : https://prove2.me/submissions/6ecdf2ba-2360-4220-ac4a-eabfb94137c9

module
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_dot_aggregate

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
namespace Certificate
theorem _root_.solution {n : ℕ} {weights target : Relation n}
    (certificate : Certificate weights target) :
    (certificate.relations.length : ℤ) = dot target weights := by
  have hmass : ∀ relations : List (Relation n),
      (∀ relation ∈ relations, IsLiftableUnit weights relation) →
        (relations.map fun relation => dot relation weights).sum =
          (relations.length : ℤ) := by
    intro relations
    induction relations with
    | nil =>
        intro
        simp
    | cons relation relations inductionHypothesis =>
        intro hvalid
        have hunit := (hvalid relation List.mem_cons_self).2.1
        have htail :
            ∀ tailRelation ∈ relations,
              IsLiftableUnit weights tailRelation := by
          intro tailRelation htailRelation
          exact hvalid tailRelation (List.mem_cons_of_mem relation htailRelation)
        simp only [List.map_cons, List.sum_cons, hunit, List.length_cons,
          Nat.cast_add, Nat.cast_one]
        simpa [add_comm] using inductionHypothesis htail
  have hcertificateMass := hmass certificate.relations certificate.valid
  calc
    (certificate.relations.length : ℤ) =
        (certificate.relations.map fun relation => dot relation weights).sum :=
      hcertificateMass.symm
    _ = dot (aggregate certificate.relations) weights :=
      (dot_aggregate certificate.relations weights).symm
    _ = dot target weights := congrArg (fun relation => dot relation weights)
      certificate.target_eq
end Certificate
end BooleanIsoperimetry.CoherentGap
