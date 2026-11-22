-- Prove2me | solution 1 for BooleanIsoperimetry.CoherentGap.principal_corrections_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:30:43.451799+00:00
-- url     : https://prove2.me/submissions/7db9f28b-81fb-4a15-9e94-8500736eb163

module
public import Definitions.Def_LeanPool_BooleanIsoperimetry_CoherentGap
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_BooleanIsoperimetry_ConwayGuyCoherentGap
public import Theorems.Thm_BooleanIsoperimetry_CoherentGap_corrections_target_sum

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open BooleanIsoperimetry BooleanIsoperimetry.CoherentGap
namespace BooleanIsoperimetry.CoherentGap
theorem _root_.solution (offset : ℕ) :
    principal offset +
        ((corrections offset).map Correction.target).sum =
      basis 0 := by
  rw [principal, corrections_target_sum, Finset.sum_sub_distrib]
  have hpositive := guide_pos (dimension := offset + 2) (by omega)
  have hguide :
      guide (offset + 2) = (guide (offset + 2) - 1) + 1 := by
    omega
  let equivalence :
      Fin ((guide (offset + 2) - 1) + 1) ≃
        Fin (guide (offset + 2)) :=
    Fin.castOrderIso hguide.symm
  have hpartition :
      (∑ index : Fin (guide (offset + 2)),
          basis (positiveIndex offset index)) =
        basis 0 +
          ∑ index : Fin (guide (offset + 2) - 1),
            basis (⟨index.val + 1, by
              have hdeep := correction_deep_bound (dimension := offset + 2)
                (index := index.val) (by omega) index.isLt
              omega⟩ : Fin (offset + 2)) := by
    rw [← equivalence.sum_comp]
    rw [Fin.sum_univ_succ]
    congr 1
  rw [hpartition]
  abel
end BooleanIsoperimetry.CoherentGap
