-- Prove2me | solution 1 for Formalism.DimensionVariation.lift_sharp_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:50.091455+00:00
-- url     : https://prove2.me/submissions/747aafa3-b584-45bd-8418-6608125ba6e7

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementCB
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_PerEmbeddingCoupledBound
import Theorems.Thm_Formalism_DimensionVariation_CB_const_le
import Theorems.Thm_Formalism_DimensionVariation_liftOperatorBound


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
open CB
namespace Formalism.DimensionVariation
theorem _root_.solution : LiftSharpBound := by
  intro Pl ι AA AA' _ _ _ _ Cl Cl' _ _ A B _ _ _ _ _ r ν n s Th c Rc lam Om S γ γ' ε h h'
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hγ hγ' hε hh hh'
  refine (liftOperatorBound Pl ι (Σ a, Cl a) (Σ b, Cl' b) A B r ν n s Th c Rc lam Om S γ γ' ε
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 hγ hγ' hε).trans (const_le Cl Cl' h h' _ ?_ hh hh')
  have : ∀ τ, 0 < (Om τ)⁻¹ ^ n τ *
      (Real.exp 1 * (2 * (n τ : ℝ) + 2) ^ (2 * Fintype.card ι) * Real.exp (∑ i, ph (ν τ i))) := by
    intro τ
    have := h10 τ
    positivity
  have hP := Finset.prod_pos (fun τ (_ : τ ∈ Finset.univ) => this τ)
  positivity
end Formalism.DimensionVariation
