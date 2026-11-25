-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.pderiv_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:06:52.195468+00:00
-- url     : https://prove2.me/submissions/67b73602-3280-4f25-b2ae-11dd076287c5

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_hasSubst_of_ordGE
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_subst
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ordGE_pderiv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_pderiv_subst_coe
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWtG_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_HasWt_mul
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mul


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
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type*} [Field C] {σ τ : Type*}
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution [Fintype σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s)) (b : τ)
    (H : MvPowerSeries σ C) :
    pderiv C b (subst a H) = ∑ w, pderiv C b (a w) * subst a (pderiv C w H) := by
  have hs := hasSubst_of_ordGE ha
  ext e
  obtain ⟨p, hp⟩ : ∃ p : MvPolynomial σ C, p = truncTotal (e.degree + 2) H := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : MvPowerSeries σ C, R = H - (p : MvPowerSeries σ C) := ⟨_, rfl⟩
  have hRo : OrdGE (e.degree + 2) R := by
    intro d hd
    rw [hR, map_sub, MvPolynomial.coeff_coe, hp, coeff_truncTotal _ hd, sub_self]
  have hH : H = (p : MvPowerSeries σ C) + R := by rw [hR]; ring
  have hL : coeff e (pderiv C b (subst a R)) = 0 :=
    ordGE_pderiv (n := e.degree + 1) (ordGE_subst ha hRo) b e (by omega)
  have hRr : coeff e (∑ w, pderiv C b (a w) * subst a (pderiv C w R)) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun w _ => ?_
    have h1 : OrdGE (0 + (e.degree + 1)) (pderiv C b (a w) * subst a (pderiv C w R)) :=
      Formalism.BaseCaseIdentities.OrdGE.mul (ordGE_zero _) (ordGE_subst ha (ordGE_pderiv (n := e.degree + 1) hRo w))
    exact h1 e (by omega)
  have hsum : ∑ w, pderiv C b (a w) * subst a (pderiv C w H) =
      (∑ w, pderiv C b (a w) * subst a (pderiv C w (p : MvPowerSeries σ C))) +
        ∑ w, pderiv C b (a w) * subst a (pderiv C w R) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hH, map_add, subst_add hs, mul_add]
  rw [hsum, map_add, hRr, add_zero, ← pderiv_subst_coe hs, hH, subst_add hs, map_add, map_add, hL,
    add_zero]
end Formalism.L2.FormalSeriesBounds
