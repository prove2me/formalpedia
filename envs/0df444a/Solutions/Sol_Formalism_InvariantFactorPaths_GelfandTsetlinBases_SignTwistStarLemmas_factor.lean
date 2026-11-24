-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:49:29.394944+00:00
-- url     : https://prove2.me/submissions/b832b62d-2abc-4470-baee-6db9550b02ba

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_jacobi_gen
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_minorF_genMat
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_SignTwistStarLemmas_canIdx_compl
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_colHeight_le
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_genMat_det_ne


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
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open SignTwistStarLemmas
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
variable {k : Type} [Field k] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
theorem _root_.solution (μ : Fin n → ℤ) {I : ℤ → Finset (Fin n)} (hI : IsIndex μ I) (c : ℤ) :
    minorF (if 1 ≤ c then genMat k n else ((genMat k n)⁻¹).transpose) (canIdx μ c) (I c) =
      algebraMap k (GenField k n) ((sgnU k μ I c : kˣ) : k) *
        (if 1 ≤ c then 1 else ((genMat k n).det)⁻¹) *
        algebraMap (MvPolynomial (Fin n × Fin n) k) (GenField k n)
          (minorF (genX k n) (initSeg n (hatIdx I c).card) (hatIdx I c)) := by
  have hIc := hI c
  by_cases hc : 1 ≤ c
  · simp only [if_pos hc, sgnU, hatIdx] at hIc ⊢
    rw [minorF_genMat, hIc]
    simp [canIdx, initSeg, hc]
  · simp only [if_neg hc, sgnU, hatIdx] at hIc ⊢
    have hle := Paths.colHeight_le μ c
    have hcard : (I c)ᶜ.card = colHeight μ c := by
      rw [Finset.card_compl, hIc, Fintype.card_fin]; omega
    have j := jacobi_gen (genU k n) (canIdx μ c) (I c)
    change (genMat k n).det * minorF ((genMat k n)⁻¹).transpose _ _ = _ * minorF (genMat k n) _ _ at j
    have hd := genMat_det_ne k n
    apply mul_left_cancel₀ hd
    rw [j, canIdx_compl μ hc, hcard, minorF_genMat]
    have e : algebraMap k (GenField k n)
        (((-1 : kˣ) ^ (epsN (initSeg n (colHeight μ c)) + epsN (I c)ᶜ) : kˣ) : k) =
        (-1) ^ (epsN (initSeg n (colHeight μ c)) + epsN (I c)ᶜ) := by simp
    rw [e]
    field_simp
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
