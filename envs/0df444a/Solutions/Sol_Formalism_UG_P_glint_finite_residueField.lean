-- Prove2me | solution 1 for Formalism.UG.P.glint_finite_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:04:19.952477+00:00
-- url     : https://prove2.me/submissions/66c01bba-4a45-49eb-bd93-b485d8a8bca1

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Lemmata_NearbyExistence_ExistsNear
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Theorems.Thm_Formalism_UG_P_glint_exists_approx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace Formalism.UG.P
theorem _root_.solution :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) := by
  let φ : 𝓞 F →+* IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
    (IsLocalRing.residue _).comp (algebraMap (𝓞 F) (v.adicCompletionIntegers F))
  have hmem : ∀ y : v.adicCompletionIntegers F, Valued.v (y : v.adicCompletion F) < 1 →
      y ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := fun y hy =>
    (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰))).2 hy
  have hker : ∀ r ∈ v.asIdeal, φ r = 0 := by
    intro r hr
    simp only [φ, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
    apply hmem
    rw [algebraMap_adicCompletionIntegers_apply, adicCompletion.valued_coe (K := F) (v := v),
      valuation_of_algebraMap]
    exact (intValuation_lt_one_iff_mem v r).2 hr
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨r, hr⟩ := glint_exists_approx v x
    refine ⟨r, ?_⟩
    simp only [φ, RingHom.comp_apply]
    show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
    rw [Ideal.Quotient.eq]
    apply hmem
    have e : ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) r - x : v.adicCompletionIntegers F) :
        v.adicCompletion F) = -((x : v.adicCompletion F) - algebraMap (𝓞 F) (v.adicCompletion F) r) := by
      rw [AddSubgroupClass.coe_sub, neg_sub, algebraMap_adicCompletionIntegers_apply,
        IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), algebraMap_adicCompletion]
      rfl
    rw [e, Valuation.map_neg]
    exact hr
  have := v.isMaximal
  have hs : Function.Surjective (Ideal.Quotient.lift v.asIdeal φ hker) :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hsurj
  exact Finite.of_surjective _ hs
end Formalism.UG.P
