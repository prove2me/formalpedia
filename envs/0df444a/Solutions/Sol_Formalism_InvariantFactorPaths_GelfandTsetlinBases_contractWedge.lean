-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.contractWedge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:48:30.648871+00:00
-- url     : https://prove2.me/submissions/0ef0c130-31ad-4d12-82eb-6a779c9c02d3

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_sg_insert
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_sg_erase
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_sgR_mul_self

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
variable {R : Type*} [CommRing R] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
theorem _root_.solution : ContractWedge := by
  intro R _ n K X Y
  funext I
  simp only [contrF, wedgeF, Pi.sub_apply]
  have hsgi : ∀ m, m ∉ I → sg (insert m I) m = sg I m := fun m hm => by
    rw [sg_insert hm]; simp
  have hsge : ∀ m', m' ∈ I → sg (I.erase m') m' = sg I m' := fun m' hm' => by
    rw [sg_erase hm']; simp
  have hL : ∀ m ∈ Iᶜ, ∑ m' ∈ insert m I, ((sg (insert m I) m' : ℤ) : R) * K ((insert m I).erase m') * X m' =
      ((sg I m : ℤ) : R) * K I * X m +
        ∑ m' ∈ I, ((sg (insert m I) m' : ℤ) : R) * K ((insert m I).erase m') * X m' := by
    intro m hm
    rw [Finset.mem_compl] at hm
    rw [Finset.sum_insert hm, Finset.erase_insert hm, hsgi m hm]
  have hR : ∀ m' ∈ I, ∑ m ∈ (I.erase m')ᶜ, ((sg (I.erase m') m : ℤ) : R) * Y m * K (insert m (I.erase m')) =
      ((sg I m' : ℤ) : R) * Y m' * K I +
        ∑ m ∈ Iᶜ, ((sg (I.erase m') m : ℤ) : R) * Y m * K (insert m (I.erase m')) := by
    intro m' hm'
    rw [Finset.compl_erase, Finset.sum_insert (by simpa using hm'), Finset.insert_erase hm', hsge m' hm']
  have hcross : ∀ m ∈ Iᶜ, ∀ m' ∈ I,
      ((sg I m : ℤ) : R) * Y m * (((sg (insert m I) m' : ℤ) : R) * K ((insert m I).erase m') * X m') =
        -(((sg I m' : ℤ) : R) * (((sg (I.erase m') m : ℤ) : R) * Y m * K (insert m (I.erase m'))) * X m') := by
    intro m hm m' hm'
    rw [Finset.mem_compl] at hm
    have hne : m ≠ m' := fun h => hm (h ▸ hm')
    rw [sg_insert hm, sg_erase hm', Finset.erase_insert_of_ne hne]
    rcases lt_or_gt_of_ne hne with h | h
    · simp [h, not_lt.mpr h.le]
      ring
    · simp [h, not_lt.mpr h.le]
      ring
  have d1 : ∀ m, ((sg I m : ℤ) : R) * Y m * (((sg I m : ℤ) : R) * K I * X m) = X m * Y m * K I := by
    intro m
    linear_combination (Y m * K I * X m) * sgR_mul_self (R := R) I m
  have d2 : ∀ m, ((sg I m : ℤ) : R) * (((sg I m : ℤ) : R) * Y m * K I) * X m = X m * Y m * K I := by
    intro m
    linear_combination (Y m * K I * X m) * sgR_mul_self (R := R) I m
  conv_lhs => rw [Finset.sum_congr rfl (fun m hm => by rw [hL m hm])]
  have hRs : ∑ m' ∈ I, ((sg I m' : ℤ) : R) *
      (∑ m ∈ (I.erase m')ᶜ, ((sg (I.erase m') m : ℤ) : R) * Y m * K (insert m (I.erase m'))) * X m' =
      ∑ m' ∈ I, ((sg I m' : ℤ) : R) * (((sg I m' : ℤ) : R) * Y m' * K I +
        ∑ m ∈ Iᶜ, ((sg (I.erase m') m : ℤ) : R) * Y m * K (insert m (I.erase m'))) * X m' :=
    Finset.sum_congr rfl (fun m' hm' => by rw [hR m' hm'])
  rw [hRs]
  simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl (fun m' hm' => hcross m hm m' hm')),
    Finset.sum_congr rfl (fun m _ => d1 m), Finset.sum_congr rfl (fun m _ => d2 m)]
  simp only [Finset.sum_neg_distrib]
  conv_lhs => rw [Finset.sum_comm]
  rw [← Finset.sum_add_sum_compl I (fun a => X a * Y a * K I)]
  ring
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
