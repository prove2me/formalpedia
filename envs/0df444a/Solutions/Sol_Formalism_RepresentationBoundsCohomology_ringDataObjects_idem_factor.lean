-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.idem_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:00:22.867652+00:00
-- url     : https://prove2.me/submissions/0e306ef1-c194-4c2d-af52-22e3e864d8f8

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_Normal
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RightIdealImageOfSurjective
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdemFactor
import Theorems.Thm_Formalism_RepresentationBoundsCohomology_ringDataObjects_idem_normal_form


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution {K : Type} [Field K] {d : Type} [Fintype d] [DecidableEq d] (e : Matrix d d K)
    (he : e * e = e) : ∃ (S : Type) (_ : Fintype S) (_ : DecidableEq S) (U : Matrix d S K)
      (W : Matrix S d K), U * W = e ∧ W * U = 1 := by
  obtain ⟨P, Q, dd, hdd, hPQ, hQP, rfl⟩ := idem_normal_form e he
  let J : Matrix d {a // dd a = 1} K := Matrix.of fun a i => if a = i.1 then 1 else 0
  have hJJ : J.transpose * J = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.of_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have h' : i.1 ≠ j.1 := fun e => hij (Subtype.ext e)
      simp [hij, h', Ne.symm h']
  have hJD : J * J.transpose = Matrix.diagonal dd := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, J, Matrix.of_apply]
    by_cases ha : dd a = 1
    · rw [Finset.sum_eq_single ⟨a, ha⟩]
      · by_cases hab : a = b
        · subst hab; simp [ha]
        · simp [Matrix.diagonal_apply_ne _ hab, Ne.symm hab]
      · intro i _ hi
        have : a ≠ i.1 := fun e => hi (Subtype.ext e.symm)
        simp [this]
      · intro h; exact absurd (mem_univ _) h
    · have h0 : dd a = 0 := (hdd a).resolve_right ha
      rw [Finset.sum_eq_zero fun i _ => by
        have : a ≠ i.1 := fun e => ha (e ▸ i.2)
        simp [this]]
      by_cases hab : a = b
      · subst hab; simp [h0]
      · simp [Matrix.diagonal_apply_ne _ hab]
  refine ⟨{a // dd a = 1}, inferInstance, inferInstance, P * J, J.transpose * Q, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc J, hJD, ← Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQP, Matrix.one_mul, hJJ]
end Formalism.RepresentationBoundsCohomology.ringDataObjects
