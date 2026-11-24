-- Prove2me | solution 1 for Formalism.NG.IdempotentCriticalLength.smul_eq_zero_iff_crit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:33:25.812576+00:00
-- url     : https://prove2.me/submissions/e960510a-48be-4bee-9c53-dd567c18152b

import Definitions.Def_Formalism_CharacterColumnKernels_StatCompMultSimple
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthEpsImgEqAdd
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_RightMulEpsAlgebraMap
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_SmulEqZeroIffCrit
import Theorems.Thm_Formalism_NG_IdempotentCriticalLength_jac_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdempotentCriticalLength
variable {O Λ : Type*} [CommRing O] [IsLocalRing O] [Ring Λ] [Algebra O Λ]
namespace Formalism.NG.IdempotentCriticalLength
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module Λ V] [IsSimpleModule Λ V]
    {ε : Λ} (hii : ∀ x : Λ, ∃ c : O, ε * x * ε - algebraMap O Λ c * ε ∈ Ring.jacobson Λ)
    (hiii : ∀ c ∈ IsLocalRing.maximalIdeal O, algebraMap O Λ c ∈ Ring.jacobson Λ)
    {v : V} (hv0 : v ≠ 0) (hv : ε • v = v) (x : Λ) :
    x • v = 0 ↔ Crit O ε x := by
  have e2 : ∀ c : O, (algebraMap O Λ c * ε) • v = algebraMap O Λ c • v := by
    intro c; rw [mul_smul, hv]
  constructor
  · intro hx y c hc
    have h1 := jac_smul hc v
    have e1 : (ε * (y * x) * ε) • v = 0 := by
      rw [mul_smul, hv, mul_smul, mul_smul, hx, smul_zero, smul_zero]
    rw [sub_smul, e1, e2, zero_sub, neg_eq_zero] at h1
    by_contra hcm
    have hu : IsUnit c := by
      by_contra hu'
      exact hcm hu'
    exact hv0 (((hu.map (algebraMap O Λ)).smul_eq_zero).mp h1)
  · intro hc
    by_contra hx
    obtain ⟨y, hy⟩ := (IsSimpleModule.toSpanSingleton_surjective Λ hx) v
    rw [LinearMap.toSpanSingleton_apply] at hy
    obtain ⟨c, hc'⟩ := hii (y * x)
    have h1 := jac_smul hc' v
    have e1 : (ε * (y * x) * ε) • v = v := by
      rw [mul_smul, hv, mul_smul, mul_smul, hy, hv]
    rw [sub_smul, e1, e2, sub_eq_zero, jac_smul (hiii c (hc y c hc')) v] at h1
    exact hv0 h1
end Formalism.NG.IdempotentCriticalLength
