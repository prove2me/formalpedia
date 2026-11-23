-- Prove2me | solution 1 for Formalism.DimensionVariation.CB.cbSq_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:00.693072+00:00
-- url     : https://prove2.me/submissions/b40f809f-30a9-4b55-ac54-34f702dbe0a1

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementCB
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_PerEmbeddingCoupledBound
import Theorems.Thm_Formalism_DimensionVariation_CB_const_le

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
    0 ≤ cbSq (Fintype.card AA) (Fintype.card AA') h h' t :=
  le_trans (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) ht)
    (const_le Cl Cl' h h' t ht hh hh')
end Formalism.DimensionVariation.CB
