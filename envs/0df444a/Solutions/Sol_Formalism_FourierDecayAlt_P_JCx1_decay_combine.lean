-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JCx1.decay.combine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:49:49.161152+00:00
-- url     : https://prove2.me/submissions/00265fcb-6fb4-4d33-b7ba-7e4277d50d60

import Definitions.Def_Formalism_HermitianCurvature_StatementJC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockEstimatesSumForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelSizesJointMean
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TheoremPIntegralOfPlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_B1_decay
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism.FourierDecayAlt
open Finset Formalism.FourierDecayAlt
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JCx1 Formalism.FourierDecayAlt.P.JCx1.decay
open Formalism.FourierDecayAlt.TB
open scoped ComplexOrder
attribute [local instance] Classical.propDecidable
variable {E W : Type} [Field E] (D : Data E W)
namespace Formalism.FourierDecayAlt.P.JCx1.decay
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (K : ℕ) (abelian₂ x a : ι → ℝ) (N M : ℝ)
    (A : Finset ι) (hA : ∀ v, v ∈ A ↔ x v < a v)
    (hL : ∀ v, 0 ≤ abelian₂ v) (hLx : ∀ v, abelian₂ v ≤ x v) (ha : ∀ v, 0 < a v) (hM : 0 ≤ M)
    (h : (∏ v ∈ A, a v ^ K) * N ≤ (∏ v ∈ A, abelian₂ v ^ K) * M) :
    N ≤ (∏ v, min 1 ((x v / a v) ^ K)) * M := by
  have hpt : ∀ v, min 1 ((x v / a v) ^ K) = if v ∈ A then (x v / a v) ^ K else 1 := by
    intro v
    have hxv : 0 ≤ x v := (hL v).trans (hLx v)
    split_ifs with hv
    · exact min_eq_right (pow_le_one₀ (div_nonneg hxv (ha v).le) ((div_le_one (ha v)).2 ((hA v).1 hv).le))
    · exact min_eq_left (one_le_pow₀ ((one_le_div (ha v)).2 (not_lt.1 fun h => hv ((hA v).2 h))))
  have hprod : (∏ v, min 1 ((x v / a v) ^ K)) = ∏ v ∈ A, (x v / a v) ^ K := by
    rw [Finset.prod_congr rfl fun v _ => hpt v, Finset.prod_ite_mem, Finset.univ_inter]
  rw [hprod]
  have hPa : 0 < ∏ v ∈ A, a v ^ K := Finset.prod_pos fun v _ => pow_pos (ha v) K
  have hq : (∏ v ∈ A, (x v / a v) ^ K) = (∏ v ∈ A, x v ^ K) / ∏ v ∈ A, a v ^ K := by
    rw [← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun v _ => div_pow _ _ _
  have hLx' : (∏ v ∈ A, abelian₂ v ^ K) ≤ ∏ v ∈ A, x v ^ K :=
    Finset.prod_le_prod (fun v _ => pow_nonneg (hL v) K) fun v _ => pow_le_pow_left₀ (hL v) (hLx v) K
  rw [hq, div_mul_eq_mul_div, le_div_iff₀ hPa]
  calc N * ∏ v ∈ A, a v ^ K = (∏ v ∈ A, a v ^ K) * N := mul_comm _ _
    _ ≤ (∏ v ∈ A, abelian₂ v ^ K) * M := h
    _ ≤ (∏ v ∈ A, x v ^ K) * M := mul_le_mul_of_nonneg_right hLx' hM
end Formalism.FourierDecayAlt.P.JCx1.decay
