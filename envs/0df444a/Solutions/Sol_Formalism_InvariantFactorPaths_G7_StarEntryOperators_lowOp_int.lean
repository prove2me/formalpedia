-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.StarEntryOperators.lowOp_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:48:38.802169+00:00
-- url     : https://prove2.me/submissions/4c2d514c-b96f-461f-b4c6-c969ba6a97c3

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementE
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NormLeOfDvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral jetPair mfact opInt)
open Formalism.GrowthSums (gamP rhoP)
open Formalism.InvariantFactorPaths.G7.StarEntryOperators
namespace Formalism.InvariantFactorPaths.G7.StarEntryOperators
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] {ν r0 r1 C : ℕ} (l : Fin C → ℕ)
    (sf : Fin C → ZMod (2 * ν)) (T : ∀ c, Fin (l c) → Fin r0 → K) (I : ∀ c, Fin (l c) → Fin r1)
    (hT : ∀ c i a, ‖T c i a‖ ≤ 1) : ∀ n, ‖MvPolynomial.coeff n (lowOp l sf T I)‖ ≤ 1 := by
  have h : lowOp l sf T I ∈ opInt K (ZV ν r0 r1) := by
    unfold lowOp minorAt
    refine Subring.prod_mem _ fun c _ => ?_
    rw [Matrix.det_apply]
    refine Subring.sum_mem _ fun π _ => ?_
    rw [Units.smul_def]
    refine zsmul_mem ?_ _
    refine Subring.prod_mem _ fun r _ => ?_
    rw [Matrix.of_apply]
    refine Subring.sum_mem _ fun a _ => ?_
    intro κ
    classical
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, norm_mul]
    refine mul_le_one₀ (hT _ _ _) (norm_nonneg _) ?_
    split_ifs <;> simp
  exact h
end Formalism.InvariantFactorPaths.G7.StarEntryOperators
