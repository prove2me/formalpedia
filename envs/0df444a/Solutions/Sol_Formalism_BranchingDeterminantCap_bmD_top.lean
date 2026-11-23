-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmD_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:46.285905+00:00
-- url     : https://prove2.me/submissions/7aba12de-a684-44ca-a623-1db3d1244585

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_ndF_eq
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_omg_add
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_omg_sub
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_omg_single
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_zcomp_bmE
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_zcomp_bmZ
import Theorems.Thm_Formalism_BranchingDeterminantCap_bmD_zero_of_gt
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} (G : BP R n) (β : Fin n → ℤ)
    (hmax : ∀ β', zcomp R n β' G ≠ 0 → omg β' ≤ omg β) (l j : Fin n) (hj : j.val = l.val + 1) (k : ℕ) :
    (∀ β', omg β + (k : ℤ) < omg β' → zcomp R n β' ((ndF R (n + 1) n l j)^[k] G) = 0) ∧
      omg (β + k • (Pi.single j 1 - Pi.single l 1)) = omg β + (k : ℤ) ∧
      zcomp R n (β + k • (Pi.single j 1 - Pi.single l 1)) ((ndF R (n + 1) n l j)^[k] G) =
        (bmZ R n j l)^[k] (zcomp R n β G) := by
  have hδ : omg (Pi.single j 1 - Pi.single l 1 : Fin n → ℤ) = 1 := by
    rw [bmD_omg_sub, bmD_omg_single, bmD_omg_single, hj]
    push_cast; ring
  induction k with
  | zero =>
    refine ⟨fun β' h => ?_, by simp, by simp⟩
    rw [Function.iterate_zero, id]
    exact bmD_zero_of_gt G β hmax β' (by simpa using h)
  | succ k ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    have hexp : ∀ β', zcomp R n β' ((ndF R (n + 1) n l j)^[k + 1] G) =
        bmE R n j l (zcomp R n β' ((ndF R (n + 1) n l j)^[k] G)) +
          bmZ R n j l (zcomp R n (β' - (Pi.single j 1 - Pi.single l 1))
            ((ndF R (n + 1) n l j)^[k] G)) := by
      intro β'
      rw [Function.iterate_succ_apply', bm_ndF_eq, Derivation.add_apply, map_add, bmD_zcomp_bmE,
        bmD_zcomp_bmZ]
    have h2 : omg (β + (k + 1) • (Pi.single j 1 - Pi.single l 1)) = omg β + ((k + 1 : ℕ) : ℤ) := by
      rw [succ_nsmul, ← add_assoc, bmD_omg_add, ih2, hδ]
      push_cast; ring
    refine ⟨fun β' h => ?_, h2, ?_⟩
    · rw [hexp, ih1 β' (by push_cast at h; linarith), ih1 _ (by
        rw [bmD_omg_sub, hδ]; push_cast at h; linarith), map_zero, map_zero, add_zero]
    · rw [hexp, ih1 _ (by rw [h2]; push_cast; linarith), map_zero, zero_add,
        Function.iterate_succ_apply', ← ih3]
      congr 2
      rw [succ_nsmul, ← add_assoc, add_sub_cancel_right]
end Formalism.BranchingDeterminantCap
