-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.deg_fractional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:35:21.801704+00:00
-- url     : https://prove2.me/submissions/6f52d0c9-d336-4a08-ae51-1785948e1be3

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_absNorm_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_ht_fractional
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_ht_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_idealSmul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LLcv
open Formalism.HN Formalism.HermitianLatticesTheory Formalism.LFunctionChainParameters.slopeLatticeData
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K
namespace Formalism.LFunctionChainParameters.LLcv
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {N : Submodule (𝓞 K) V} (hN : N.FG) {I : FI} (hI : I ≠ 0) :
    deg (realize b X) (idealSmul (I : Submodule (𝓞 K) K) N) = deg (realize b X) N -
      (rkK N : ℝ) * Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by
  have h := ht_fractional b X hX hN hI
  have hp := ht_pos b X hX hN
  unfold ht at h hp
  rw [rkK_idealSmul hI] at h
  set c : ℝ := (2 : ℝ) ^ (nPl K * rkK N) * |(NumberField.discr K : ℝ)| ^ (-(rkK N : ℝ) / 2)
    with hc
  have hD : 0 < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hc0 : 0 < c := by positivity
  have hcov : 0 < Formalism.F.covol (zl (realize b X) N) := by
    by_contra hneg
    have : c * Formalism.F.covol (zl (realize b X) N) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hc0.le (not_lt.1 hneg)
    linarith
  have h2 : Formalism.F.covol (zl (realize b X) (idealSmul (I : Submodule (𝓞 K) K) N)) =
      Formalism.F.covol (zl (realize b X) N) * ((FractionalIdeal.absNorm I : ℚ) : ℝ) ^ rkK N := by
    apply mul_left_cancel₀ hc0.ne'
    rw [h]; ring
  unfold deg Formalism.F.deg
  rw [h2, Real.log_mul hcov.ne' (pow_ne_zero _ (absNorm_pos hI).ne'), Real.log_pow]
  ring
end Formalism.LFunctionChainParameters.LLcv
