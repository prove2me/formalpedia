-- Prove2me | solution 1 for Formalism.DimensionVariation.CB.const_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:37.374801+00:00
-- url     : https://prove2.me/submissions/802be54b-5f73-438b-a270-d7b8ad1df0b1

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementCB
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_PerEmbeddingCoupledBound
import Theorems.Thm_Formalism_DimensionVariation_CB_card_sigma_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues (fnorm chainFun chainMat)
open Formalism.DimensionVariation.CB
namespace Formalism.DimensionVariation.CB
theorem _root_.solution {AA AA' : Type} [Fintype AA] [Fintype AA'] (Cl : AA → Type) (Cl' : AA' → Type)
    [∀ a, Fintype (Cl a)] [∀ b, Fintype (Cl' b)] (h h' t : ℝ) (ht : 0 ≤ t)
    (hh : ∀ a, (Fintype.card (Cl a) : ℝ) ≤ h) (hh' : ∀ b, (Fintype.card (Cl' b) : ℝ) ≤ h') :
    ((Fintype.card (Σ a, Cl a) : ℝ) * (Fintype.card (Σ b, Cl' b) : ℝ)) * t ≤
      cbSq (Fintype.card AA) (Fintype.card AA') h h' t := by
  have h1 := card_sigma_le Cl h hh
  have h2 := card_sigma_le Cl' h' hh'
  have h3 : ((Fintype.card (Σ a, Cl a) : ℝ) * (Fintype.card (Σ b, Cl' b) : ℝ)) ≤
      ((Fintype.card AA : ℝ) * h) * ((Fintype.card AA' : ℝ) * h') :=
    mul_le_mul h1 h2 (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) h1)
  have h4 := mul_le_mul_of_nonneg_right h3 ht
  unfold cbSq
  calc _ ≤ _ := h4
    _ = _ := by ring
end Formalism.DimensionVariation.CB
