-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.fact_add_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:21:26.346372+00:00
-- url     : https://prove2.me/submissions/736a2202-e7c1-4da8-bfc8-256326b3fd3d

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vN_mul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vN_prod
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vN_choose_le
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_ne_zero
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_add_eq
import Theorems.Thm_Formalism_MainNotions_PlaneGram_natLog_le_term
import Theorems.Thm_Formalism_MainNotions_PlaneGram_two_le_p
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fact_lower

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ))
variable {v} {p : ℕ} [CharZero K]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (hD : DVRHyp v p) {L : Type} [Fintype L] {r : ℕ}
    {α α' : L × Fin r →₀ ℕ} {d : L → ℕ} (h : ∀ i, ldeg (α + α') i = d i) :
    vN v (∏ i, (d i).factorial) - 2 * kapL p r d ≤ vN v (fact α) + vN v (fact α') := by
  have hf := fact_add_eq α α'
  have hne : ∏ x, (α x + α' x).choose (α' x) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun x _ => (Nat.choose_pos (by omega)).ne'
  have hv : vN v (fact (α + α')) =
      vN v (∏ x, (α x + α' x).choose (α' x)) + vN v (fact α) + vN v (fact α') := by
    rw [hf, vN_mul hD (mul_ne_zero hne (fact_ne_zero α)) (fact_ne_zero α'),
      vN_mul hD hne (fact_ne_zero α)]
  have hl := fact_lower hD h
  have hc : vN v (∏ x, (α x + α' x).choose (α' x)) ≤ kapL p r d := by
    rw [vN_prod hD _ _ (fun x _ => (Nat.choose_pos (by omega)).ne'), Fintype.sum_prod_type]
    unfold kapL
    apply Finset.sum_le_sum
    intro i _
    have hb : ∀ a : Fin r, α (i, a) + α' (i, a) ≤ d i := by
      intro a
      rw [← h i]
      unfold ldeg
      have := Finset.single_le_sum (f := fun b : Fin r => (α + α') (i, b))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
      simpa using this
    calc ∑ a : Fin r, vN v ((α (i, a) + α' (i, a)).choose (α' (i, a)))
        ≤ ∑ _a : Fin r, (Nat.log p (d i) : ℝ) := by
          apply Finset.sum_le_sum
          intro a _
          refine (vN_choose_le hD _ _).trans ?_
          exact_mod_cast Nat.log_mono_right (hb a)
      _ = (r : ℝ) * (Nat.log p (d i) : ℝ) := by simp
      _ ≤ _ := natLog_le_term (two_le_p hD) r (d i)
  linarith
end Formalism.MainNotions.PlaneGram
