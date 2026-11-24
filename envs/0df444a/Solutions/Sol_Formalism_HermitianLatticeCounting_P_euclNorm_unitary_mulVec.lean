-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.euclNorm_unitary_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:15:50.242825+00:00
-- url     : https://prove2.me/submissions/8451fa40-b6fe-4507-9c0f-b5bf6fb5d305

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Formalism_LogSumExpBounds_IsoTransfer
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_unitary_leftG
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_euclNorm_nonneg
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_euclNorm_sq_eq_star_dotProduct
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_Final_h2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {k : Matrix ι ι ℂ} (hk : k ∈ Matrix.unitaryGroup ι ℂ)
    (v : ι → ℂ) : n2G (k *ᵥ v) = n2G v := by
  have h : ((n2G (k *ᵥ v) ^ 2 : ℝ) : ℂ) = ((n2G v ^ 2 : ℝ) : ℂ) := by
    rw [euclNorm_sq_eq_star_dotProduct, euclNorm_sq_eq_star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, unitary_leftG hk, Matrix.one_mulVec]
  have h2 : n2G (k *ᵥ v) ^ 2 = n2G v ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (euclNorm_nonneg _) (euclNorm_nonneg _)).mp h2
end Formalism.HermitianLatticeCounting.P
