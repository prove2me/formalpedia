-- Prove2me | solution 1 for Formalism.MainNotions.BridgeLevelGenB.dense_mod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:22:32.744716+00:00
-- url     : https://prove2.me/submissions/e281fbb6-ef3f-4aeb-8249-be41c9ed443a

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnimodularity_CartierFrobeniusFormLocal
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_BridgeLevelGenB
import Theorems.Thm_Formalism_MainNotions_BridgeLevelGenB_val_int
import Theorems.Thm_Formalism_MainNotions_BridgeLevelGenB_exists_int_close

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLevelGenB
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Topology Formalism.MainNotions.S
open scoped TensorProduct
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.MainNotions.BridgeLevelGenB
theorem _root_.solution (g : ℕ) (hg : 1 ≤ g) (y : FiniteAdeleRing (𝓞 F) F) (hy : y ∈ Formalism.UG.intAd F) :
    ∃ s : 𝓞 F, ∃ c ∈ Formalism.UG.intAd F,
      y = algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F s) + (g : FiniteAdeleRing (𝓞 F) F) * c := by
  classical
  set gO : 𝓞 F := (g : 𝓞 F) with hgO
  have hg0 : gO ≠ 0 := by rw [hgO]; exact Nat.cast_ne_zero.2 (by omega)
  have hI : Ideal.span {gO} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hg0
  set T := (Ideal.finite_factors hI).toFinset with hT
  have hyv : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v (y v) ≤ 1 :=
    fun v => (mem_adicCompletionIntegers (𝓞 F) F v).1 (hy v)
  choose a ha using fun v : HeightOneSpectrum (𝓞 F) => exists_int_close v (y v) (hyv v) hg0
  set k : HeightOneSpectrum (𝓞 F) → ℕ :=
    fun v => (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {gO})).factors with hk
  obtain ⟨s, hs⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T) (fun v => v.asIdeal) k
    (fun v _ => v.prime) (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => a v.1)
  have hval : ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s)) ≤ v.intValuation gO := by
    intro v
    by_cases hv : v ∈ T
    · have h1 := hs v hv
      have h2 : v.intValuation (s - a v) ≤ v.intValuation gO := by
        rw [intValuation_if_neg v hg0]
        exact (intValuation_le_pow_iff_mem v _ _).2 h1
      have h3 : Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (a v)) -
          algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s)) ≤ v.intValuation gO := by
        rw [← map_sub, ← map_sub, val_int, ← Valuation.map_neg, neg_sub]
        exact h2
      calc Valued.v (y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s))
          = Valued.v ((y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (a v))) +
              (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (a v)) -
                algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s))) := by ring_nf
        _ ≤ max _ _ := Valuation.map_add _ _ _
        _ ≤ _ := max_le (ha v).le h3
    · have hgv : gO ∉ v.asIdeal := by
        intro hm
        apply hv
        rw [hT, Set.Finite.mem_toFinset]
        show v.asIdeal ∣ Ideal.span {gO}
        rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
        exact hm
      have h1 : v.intValuation gO = 1 :=
        le_antisymm (intValuation_le_one v gO) (not_lt.1 fun h => hgv ((intValuation_lt_one_iff_mem v gO).1 h))
      rw [h1]
      calc Valued.v (y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s))
          ≤ max (Valued.v (y v)) (Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s))) :=
            Valuation.map_sub _ _ _
        _ ≤ 1 := max_le (hyv v) (by rw [val_int]; exact intValuation_le_one v s)
  have hgF : algebraMap (𝓞 F) F gO ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)]; exact hg0
  refine ⟨s, algebraMap F _ (algebraMap (𝓞 F) F gO)⁻¹ *
    (y - algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F s)), ?_, ?_⟩
  · intro v
    show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F gO)⁻¹ *
      (y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s)) ∈ _
    rw [mem_adicCompletionIntegers, map_mul, map_inv₀, map_inv₀, val_int]
    have hne : v.intValuation gO ≠ 0 := intValuation_ne_zero v gO hg0
    calc (v.intValuation gO)⁻¹ * Valued.v (y v - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s))
        ≤ (v.intValuation gO)⁻¹ * v.intValuation gO := by gcongr; exact hval v
      _ = 1 := inv_mul_cancel₀ hne
  · have e : (g : FiniteAdeleRing (𝓞 F) F) = algebraMap F _ (algebraMap (𝓞 F) F gO) := by
      rw [hgO, map_natCast, map_natCast]
    rw [e, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hgF, map_one, one_mul]
    ring
end Formalism.MainNotions.BridgeLevelGenB
