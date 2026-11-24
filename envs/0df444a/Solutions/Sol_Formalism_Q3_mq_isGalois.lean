-- Prove2me | solution 1 for Formalism.Q3.mq_isGalois
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:12:38.348362+00:00
-- url     : https://prove2.me/submissions/be179cc7-4566-4c84-91da-4ea64ffbb84f

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_MQGalois
import Theorems.Thm_Formalism_Q3_mq_algAdjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.Q3
variable {k : ℕ} {E : Type} [Field E] [NumberField E] {a : Fin k → ℤ} {α : Fin k → E}
namespace Formalism.Q3
theorem _root_.solution (h : IsMQ a α) : IsGalois ℚ E := by
  classical
  set p : ℚ[X] := ∏ i, (X ^ 2 - C ((a i : ℚ))) with hp
  have hmon : p.Monic := monic_prod_of_monic _ _ (fun i _ => monic_X_pow_sub_C _ two_ne_zero)
  have hroot : ∀ i, α i ∈ p.rootSet E := by
    intro i
    rw [mem_rootSet]
    refine ⟨hmon.ne_zero, ?_⟩
    rw [hp, map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [h.1 i]
  have hsplit : (p.map (algebraMap ℚ E)).Splits := by
    rw [hp, Polynomial.map_prod]
    apply Splits.prod
    intro i _
    have hfac : (X ^ 2 - C ((a i : ℚ))).map (algebraMap ℚ E) = (X - C (α i)) * (X - C (-α i)) := by
      have hc : (C ((a i : ℚ))).map (algebraMap ℚ E) = C (α i) ^ 2 := by
        rw [Polynomial.map_C, map_intCast, ← h.1 i, C_pow]
      rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, hc, C_neg]
      ring
    rw [hfac]
    exact (Splits.X_sub_C _).mul (Splits.X_sub_C _)
  haveI : p.IsSplittingField ℚ E := by
    refine Polynomial.IsSplittingField.mk hsplit ?_
    rw [eq_top_iff, ← mq_algAdjoin h]
    exact Algebra.adjoin_mono (by rintro _ ⟨i, rfl⟩; exact hroot i)
  haveI : Normal ℚ E := Normal.of_isSplittingField p
  exact IsGalois.mk
end Formalism.Q3
