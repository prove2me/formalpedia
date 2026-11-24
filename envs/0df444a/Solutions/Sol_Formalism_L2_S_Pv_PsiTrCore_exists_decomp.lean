-- Prove2me | solution 1 for Formalism.L2.S.Pv.PsiTrCore.exists_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:37:41.935212+00:00
-- url     : https://prove2.me/submissions/91cdbae4-a40d-40e4-8b1c-dc2d832184ce

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_TraceIntegralEstimates_PsiTrCoreApprox
import Theorems.Thm_Formalism_L2_S_Pv_PsiTrCore_valued_algebraMap_int
import Theorems.Thm_Formalism_L2_S_Pv_PsiTrCore_exists_approx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Formalism Formalism.L2 Formalism.L2.S Formalism.L2.S.Pv Formalism.L2.S.Pv.PsiTrCore
variable {F : Type} [Field F] [NumberField F]
namespace Formalism.L2.S.Pv.PsiTrCore
theorem _root_.solution (a : FiniteAdeleRing (𝓞 F) F) (ha : ∀ v, a v ∈ v.adicCompletionIntegers F)
    (n : 𝓞 F) (hn : n ≠ 0) :
    ∃ b : 𝓞 F, ∃ c : FiniteAdeleRing (𝓞 F) F, (∀ v, c v ∈ v.adicCompletionIntegers F) ∧
      a = algebraMap F (FiniteAdeleRing (𝓞 F) F) (b : F) +
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (n : F) * c := by
  obtain ⟨b, hb⟩ := exists_approx a ha n hn
  have hnF : (n : F) ≠ 0 := by
    have := (IsFractionRing.injective (𝓞 F) F).ne hn
    rwa [map_zero] at this
  have hA : ∀ (k : F) (v : HeightOneSpectrum (𝓞 F)),
      (algebraMap F (FiniteAdeleRing (𝓞 F) F) k) v = algebraMap F (v.adicCompletion F) k :=
    fun k v ↦ rfl
  refine ⟨b, algebraMap F (FiniteAdeleRing (𝓞 F) F) ((n : F)⁻¹) *
    (a - algebraMap F (FiniteAdeleRing (𝓞 F) F) (b : F)), fun v ↦ ?_, ?_⟩
  · rw [mem_adicCompletionIntegers]
    change Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) ((n : F)⁻¹)) v *
      (a v - (algebraMap F (FiniteAdeleRing (𝓞 F) F) (b : F)) v)) ≤ 1
    rw [hA, hA, map_mul, map_inv₀, map_inv₀, valued_algebraMap_int]
    have hne : v.intValuation n ≠ 0 := by
      rw [intValuation_if_neg v hn]; exact WithZero.exp_ne_zero
    calc (v.intValuation n)⁻¹ * Valued.v (a v - algebraMap F (v.adicCompletion F) (b : F))
        ≤ (v.intValuation n)⁻¹ * v.intValuation n := by
          have hbv := hb v
          gcongr
      _ = 1 := inv_mul_cancel₀ hne
  · rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hnF, map_one, one_mul]
    ring
end Formalism.L2.S.Pv.PsiTrCore
