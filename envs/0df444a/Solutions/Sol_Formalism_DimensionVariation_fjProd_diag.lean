-- Prove2me | solution 1 for Formalism.DimensionVariation.fjProd_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:59.437811+00:00
-- url     : https://prove2.me/submissions/2605e229-ad68-43f8-a0eb-a745390f71fc

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet
import Theorems.Thm_Formalism_DimensionVariation_fjW_diag
import Theorems.Thm_Formalism_DimensionVariation_fjProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory Filter Topology
open scoped ComplexConjugate Real Nat
noncomputable section
open Formalism Formalism.DimensionVariation
namespace Formalism.DimensionVariation
theorem _root_.solution {κ : Type} [Fintype κ] (e : κ → ℕ) :
    ∫ u : κ → ℂ, mono u e * mono (cj u) e * (Real.exp (-(nsq u)) : ℂ) =
      (π : ℂ) ^ Fintype.card κ * (mfact e : ℂ) := by
  simp_rw [fjProd]
  rw [show (∫ u : κ → ℂ, ∏ x, fjW (e x) (e x) (u x)) =
      ∏ x, ∫ z : ℂ, fjW (e x) (e x) z from
    integral_fintype_prod_volume_eq_prod (fun x (z : ℂ) => fjW (e x) (e x) z)]
  simp_rw [fjW_diag]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, mfact,
    Nat.cast_prod]
end Formalism.DimensionVariation
