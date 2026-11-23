-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x3.sum_over_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:32:50.474833+00:00
-- url     : https://prove2.me/submissions/88e8c63f-ac6e-4dc2-828e-0065fbddb1a8

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_psiBar_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_finsum_char
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_chC_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_chC_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x3
variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ)
variable {R ψ}
variable {C : Type} [AddCommGroup C] [Module R C]
open Classical
namespace Formalism.FourierDecayAlt.P.A5x3
theorem _root_.solution (h : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) [Finite C]
    (μ : C →ₗ[R] KR R) :
    ∑ᶠ c : C, psiKR R ψ (μ c) = if μ = 0 then (Nat.card C : ℂ) else 0 := by
  split_ifs with hμ
  · apply (finsum_char (chC h μ)).1
    intro g
    rw [hμ, chC_apply, LinearMap.zero_apply, ← psiBar_apply h, AddChar.map_zero_eq_one]
  · apply (finsum_char (chC h μ)).2
    by_contra hcon
    push Not at hcon
    apply hμ
    apply chC_injective h
    ext c
    rw [hcon c, chC_apply, LinearMap.zero_apply, ← psiBar_apply h, AddChar.map_zero_eq_one]
end Formalism.FourierDecayAlt.P.A5x3
