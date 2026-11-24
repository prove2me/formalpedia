-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.pow_eq_of_signed_minors_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:21.344606+00:00
-- url     : https://prove2.me/submissions/61f787e1-d182-4eb2-95b3-97f4215c81f8

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_E5sign_intCast_ne_zero
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_signed_minor_split

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {F : Type} [Field F] {p : ℕ} (s : Fin p → ℕ) (t t0 : Fin p → F)
    (h0 : ∀ a, t0 a ≠ 0) (h : ∀ a, IndexedMinorEntry s t a = IndexedMinorEntry s t0 a) :
    ∀ a, t a ^ s a = t0 a ^ s a := by
  intro a
  induction a using WellFoundedLT.induction with
  | _ a ih =>
    have h1 := h a
    rw [signed_minor_split, signed_minor_split] at h1
    have h2 : (∏ a' ∈ univ.filter (fun a' : Fin p => a' < a), ((ParitySign (s a') : ℤ) : F) * t a' ^ s a') =
        ∏ a' ∈ univ.filter (fun a' : Fin p => a' < a), ((ParitySign (s a') : ℤ) : F) * t0 a' ^ s a' := by
      apply Finset.prod_congr rfl
      intro x hx
      rw [ih x (by simpa using hx)]
    rw [h2] at h1
    have h3 : (∏ a' ∈ univ.filter (fun a' : Fin p => a' < a), ((ParitySign (s a') : ℤ) : F) * t0 a' ^ s a') ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun x _ => mul_ne_zero (E5sign_intCast_ne_zero _) (pow_ne_zero _ (h0 x))
    exact mul_left_cancel₀ (E5sign_intCast_ne_zero _) (mul_left_cancel₀ h3 h1)
end Formalism.HermitianLatticeCounting.P
