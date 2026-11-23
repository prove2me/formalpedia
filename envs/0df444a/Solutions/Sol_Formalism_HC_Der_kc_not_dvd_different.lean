-- Prove2me | solution 1 for Formalism.HC.Der.kc_not_dvd_different
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:17.954803+00:00
-- url     : https://prove2.me/submissions/431f14df-6ff8-476b-9f4c-5a69637e6b4f

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_KcPair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HC Formalism.HC.Der
open NumberField Ideal
attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
namespace Formalism.HC.Der
theorem _root_.solution (M E : Type) [Field M] [NumberField M] [Field E] [NumberField E] [Algebra M E] [IsGalois M E]
    (P : Ideal (𝓞 E)) [P.IsPrime]
    (h : P ≠ ⊥ → ∀ σ : E ≃ₐ[M] E, (∀ x : 𝓞 E, σ • x - x ∈ P) → σ = 1) : ¬ P ∣ differentIdeal (𝓞 M) (𝓞 E) := by
  by_cases hP : P = ⊥
  · subst hP
    intro hdvd
    apply differentIdeal_ne_bot (A := 𝓞 M) (B := 𝓞 E)
    rw [← Ideal.zero_eq_bot] at hdvd ⊢
    exact zero_dvd_iff.mp hdvd
  · have hp0 : P.under (𝓞 M) ≠ ⊥ := fun h0 => hP (Ideal.eq_bot_of_comap_eq_bot h0)
    haveI hmax : (P.under (𝓞 M)).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hp0
    haveI hfin : Finite (P.under (𝓞 M)).ResidueField := by
      haveI : Finite ((𝓞 M) ⧸ P.under (𝓞 M)) := Ideal.finiteQuotientOfFreeOfNeBot _ hp0
      exact Finite.of_surjective _
        (Ideal.bijective_algebraMap_quotient_residueField (P.under (𝓞 M))).2
    rw [not_dvd_differentIdeal_iff, Algebra.isUnramifiedAt_iff_of_isDedekindDomain,
      ← Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 M)) P (E ≃ₐ[M] E),
      ← Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[M] E) (P.under (𝓞 M)) P,
      Subgroup.card_eq_one, Subgroup.eq_bot_iff_forall]
    intro σ hσ
    exact h hP σ hσ
end Formalism.HC.Der
