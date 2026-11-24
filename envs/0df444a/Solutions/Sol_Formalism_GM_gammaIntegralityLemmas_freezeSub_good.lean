-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.freezeSub_good
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:28.318546+00:00
-- url     : https://prove2.me/submissions/23b91583-bf2d-4cf5-90e9-1940f6ef425e

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IVP_sum
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_sum
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_sub
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_AllMono_X_mul_X
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_sub
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_IsIntP_sum
import Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas__v_add_9b2e3af02dc8
import Theorems.Thm_P2M_Formalism_GM_gammaIntegralityLemmas__v_single_a5388cd8d2f0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {N r : ℕ}
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (LL : Letters (N + 1)) (ρ : Fin r) (hW : LL.vec (Fin.last N) = true)
    (i : Fin (N + 1)) (c : Fin r) :
    AllMono (p := p) (GoodQ ρ) (dv i) (freezeSub p LL ρ (i, c)) := by
  have hne : ∀ (a : Fin (N + 1)), (Fin.last (N + 1) : Fin (N + 1 + 1)) ≠ Fin.castSucc a :=
    fun a h => Fin.castSucc_ne_last a h.symm
  simp only [freezeSub]
  split_ifs with hv hc hc
  · subst hc
    apply AllMono.sum
    intro c' _
    apply AllMono.X_mul_X
    refine ⟨by rw [δv_add, δv_single, δv_single]; rfl, ?_⟩
    simp only [Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq]
    by_cases h1 : c' = c <;> by_cases h2 : i = Fin.last N <;> simp [h1, h2, hne, Fin.castSucc_ne_last]
  · apply AllMono.X_mul_X
    refine ⟨by rw [δv_add, δv_single, δv_single, dv]; exact add_comm _ _, ?_⟩
    simp only [Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq]
    simp [hne, Ne.symm hc]
    try (split_ifs <;> omega)
  · subst hc
    apply AllMono.X_mul_X
    refine ⟨by rw [δv_add, δv_single, δv_single, dv]; exact add_comm _ _, ?_⟩
    simp only [Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq]
    by_cases h2 : i = Fin.last N <;> simp [h2, hne, Fin.castSucc_ne_last]
  · have hi : i ≠ Fin.last N := by rintro rfl; simp [hW] at hv
    apply AllMono.sub
    · apply AllMono.X_mul_X
      refine ⟨by rw [δv_add, δv_single, δv_single, dv]; exact add_comm _ _, ?_⟩
      simp only [Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq]
      simp [hne, Ne.symm hc]
      split_ifs <;> omega
    · apply AllMono.X_mul_X
      refine ⟨by rw [δv_add, δv_single, δv_single]; rfl, ?_⟩
      simp only [Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq]
      simp [hne, hi, Ne.symm hc, Fin.castSucc_ne_last]
end Formalism.GM.gammaIntegralityLemmas
