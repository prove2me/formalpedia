-- Prove2me | solution 1 for Formalism.L2.Pj.unramBridge_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:18:53.244398+00:00
-- url     : https://prove2.me/submissions/b353e509-fb28-4dd4-8165-13aa9ec58dab

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open Formalism Formalism.L2 Formalism.L2.Pj
attribute [local instance] FractionRing.liftAlgebra
namespace Formalism.L2.Pj
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] [IsCMField K],
    (∀ P : Ideal (𝓞 K), P.IsMaximal → ∃ θ : 𝓞 K,
      θ - RingOfIntegers.mapRingEquiv (IsCMField.complexConj K : K ≃+* K) θ ∉ P) →
    Algebra.Unramified (𝓞 (maximalRealSubfield K)) (𝓞 K) := by
  intro K _ _ _ hθ
  set F := maximalRealSubfield K with hF
  have hsep : Algebra.IsSeparable (FractionRing (𝓞 F)) (FractionRing (𝓞 K)) := by
    refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv (𝓞 F) F).symm.toRingEquiv
          (FractionRing.algEquiv (𝓞 K) K).symm.toRingEquiv ?_
    ext _
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv (𝓞 F) F).symm
      (FractionRing.algEquiv (𝓞 K) K).symm _
  rw [Algebra.unramified_iff_forall]
  rintro ⟨Q, hQ⟩
  change Algebra.IsUnramifiedAt (𝓞 F) Q
  rcases eq_or_ne Q ⊥ with rfl | hne
  · exact Algebra.isUnramifiedAt_bot
  have hmax : Q.IsMaximal := hQ.isMaximal hne
  obtain ⟨θ, hθP⟩ := hθ Q hmax
  set θ' := RingOfIntegers.mapRingEquiv (IsCMField.complexConj K : K ≃+* K) θ with hθ'
  have hσ : θ' = IsCMField.ringOfIntegersComplexConj K θ := RingOfIntegers.ext rfl
  have hne' : θ - θ' ≠ 0 := fun h => hθP (h ▸ Ideal.zero_mem _)

  have hnotF : (θ : K) ∉ F := by
    intro hm
    apply hne'
    rw [sub_eq_zero, hσ]
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj]
    exact ((IsCMField.complexConj_eq_self_iff K _).mpr hm).symm

  have hfin : Module.finrank F K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F K
  have hint : IsIntegral F (θ : K) := Algebra.IsIntegral.isIntegral _
  have hadj : Algebra.adjoin F {algebraMap (𝓞 K) K θ} = ⊤ := by
    have : IsSimpleOrder (IntermediateField F K) :=
      IntermediateField.isSimpleOrder_of_finrank_prime F K (hfin ▸ Nat.prime_two)
    rcases eq_bot_or_eq_top (IntermediateField.adjoin F {(θ : K)}) with h | h
    · exfalso
      rw [IntermediateField.adjoin_simple_eq_bot_iff, IntermediateField.mem_bot] at h
      obtain ⟨y, hy⟩ := h
      exact hnotF (hy ▸ y.2)
    · rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
      change (IntermediateField.adjoin F {(θ : K)}).toSubalgebra = ⊤
      rw [h, IntermediateField.top_toSubalgebra]
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 F) F K θ hadj

  set f := minpoly (𝓞 F) θ with hf
  have hθint : IsIntegral (𝓞 F) θ := Algebra.IsIntegral.isIntegral _
  have hmonic : f.Monic := minpoly.monic hθint
  have hdeg : f.natDegree ≤ 2 := by
    have h1 : f = minpoly (𝓞 F) (algebraMap (𝓞 K) K θ) :=
      (minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective (𝓞 K) K) θ).symm
    have h2 := minpoly.isIntegrallyClosed_eq_field_fractions' F
      (IsIntegral.algebraMap hθint : IsIntegral (𝓞 F) (algebraMap (𝓞 K) K θ))
    have h3 : (minpoly F (algebraMap (𝓞 K) K θ)).natDegree ≤ 2 :=
      hfin ▸ minpoly.natDegree_le _
    rw [h2, Polynomial.natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective _ _)] at h3
    rw [h1]; exact h3
  set fK := f.map (algebraMap (𝓞 F) (𝓞 K)) with hfK
  have hKmonic : fK.Monic := hmonic.map _
  have hKdeg : fK.natDegree ≤ 2 := by
    rw [hfK, hmonic.natDegree_map]; exact hdeg
  have hr1 : fK.IsRoot θ := by
    rw [IsRoot, hfK, eval_map, ← aeval_def]; exact minpoly.aeval _ _
  have hr2 : fK.IsRoot θ' := by
    rw [IsRoot, hfK, eval_map, ← aeval_def, hσ]
    rw [show IsCMField.ringOfIntegersComplexConj K θ = (IsCMField.ringOfIntegersComplexConj K).toAlgHom θ from rfl,
      Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  set g := fK /ₘ (X - C θ) with hg
  have hfg : (X - C θ) * g = fK := (mul_divByMonic_eq_iff_isRoot).mpr hr1
  have hg2 : g.IsRoot θ' := by
    have := hr2
    rw [← hfg, IsRoot, eval_mul] at this
    rcases mul_eq_zero.mp this with h | h
    · exfalso; apply hne'; simp at h; rw [sub_eq_zero] at h ⊢; exact h.symm
    · exact h
  set h := g /ₘ (X - C θ') with hh
  have hgh : (X - C θ') * h = g := (mul_divByMonic_eq_iff_isRoot).mpr hg2
  have hfac : fK = (X - C θ) * ((X - C θ') * h) := by rw [hgh, hfg]
  have hhmonic : h.Monic := by
    have hm2 : ((X - C θ) * (X - C θ')).Monic := (monic_X_sub_C θ).mul (monic_X_sub_C θ')
    rw [hfac, ← mul_assoc] at hKmonic
    exact hm2.of_mul_monic_left hKmonic
  have hh1 : h = 1 := by
    rw [← hhmonic.natDegree_eq_zero]
    have := hKdeg
    rw [hfac, natDegree_mul (X_sub_C_ne_zero θ) (mul_ne_zero (X_sub_C_ne_zero θ') hhmonic.ne_zero),
      natDegree_mul (X_sub_C_ne_zero θ') hhmonic.ne_zero, natDegree_X_sub_C, natDegree_X_sub_C] at this
    omega
  have hval : aeval θ (derivative f) = θ - θ' := by
    rw [aeval_def, ← eval_map, ← derivative_map, ← hfK, hfac, hh1]
    simp [derivative_mul]
  rw [← not_dvd_differentIdeal_iff, Ideal.dvd_iff_le]
  intro hle
  exact hθP (hle (hval ▸ hmem))
end Formalism.L2.Pj
