-- Prove2me | solution 1 for Formalism.L2.Indef.specDet_rect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:12:44.906261+00:00
-- url     : https://prove2.me/submissions/a46df0f4-442e-4f74-a5f5-2cdcccc623d2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Theorems.Thm_Formalism_L2_Indef_dim_of_bij
import Theorems.Thm_Formalism_L2_Indef_isUnit_det_of_bij

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.Indef
theorem _root_.solution (hS : SpecDet) (v : InfinitePlace K) {D dQ : ℕ}
    (XQ : InfinitePlace K → Matrix (Fin dQ) (Fin dQ) ℂ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ)
    (hXQ : ∀ u, IsUnit (XQ u).det) (hXE : ∀ u, IsUnit (XE u).det)
    (ι : Matrix (Fin D) (Fin dQ) K) (hι : Function.Bijective ι.mulVec)
    (J : Type) [Fintype J] (dZ dW : J → ℕ)
    (XT : ∀ j, InfinitePlace K → Matrix (Fin (dZ j)) (Fin (dZ j)) ℂ)
    (XW : ∀ j, InfinitePlace K → Matrix (Fin (dW j)) (Fin (dW j)) ℂ)
    (hXT : ∀ j u, IsUnit (XT j u).det) (hXW : ∀ j u, IsUnit (XW j u).det)
    (θ : ∀ j, Matrix (Fin (dW j)) (Fin (dZ j)) K) (hθ : ∀ j, Function.Bijective (θ j).mulVec)
    (Ix : Type) [Fintype Ix] (Qp : Ix → Submodule K (Fin dQ → K))
    (Tq : ∀ j, Ix → Submodule K (Fin (dZ j) → K))
    (h1 : iSupIndep Qp) (h2 : (⨆ p, Qp p) = ⊤) (h3 : ∀ j, iSupIndep (Tq j)) (h4 : ∀ j, (⨆ p, Tq j p) = ⊤)
    (h5 : ∀ j p, finrank K (Qp p) = finrank K (Tq j p)) (s : ℝ) (lam : J → Ix → ℝ)
    (h6 : ∀ p, IsScalarOn XQ XE v ι (Qp p) (s * ∏ j, lam j p))
    (h7 : ∀ j p, IsScalarOn (XT j) (XW j) v (θ j) (Tq j p) (lam j p)) :
    detRatio XQ XE ι v = s ^ D * ∏ j, detRatio (XT j) (XW j) (θ j) v := by
  obtain rfl : dQ = D := dim_of_bij ι hι
  have hd : dZ = dW := funext fun j => dim_of_bij (θ j) (hθ j)
  subst hd
  exact hS K v _ XQ XE hXQ hXE ι (isUnit_det_of_bij ι hι) J _ XT XW hXT hXW θ
    (fun j => isUnit_det_of_bij (θ j) (hθ j)) Ix Qp Tq h1 h2 h3 h4 h5 s lam h6 h7
end Formalism.L2.Indef
