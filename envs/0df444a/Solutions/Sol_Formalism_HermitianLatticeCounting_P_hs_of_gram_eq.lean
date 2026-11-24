-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.hs_of_gram_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:14:08.295399+00:00
-- url     : https://prove2.me/submissions/6279d749-172a-493f-afbf-50cb8e362478

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PowFinrankEqZeroOfTracePow
import Definitions.Def_Formalism_LogSumExpBounds_IsoTransfer
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Transference
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExtensionInterSubspace
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hs_nonneg
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_hs_sq_trace
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
theorem _root_.solution {N : ℕ} {Y Z : Matrix (Fin N) (Fin N) ℂ}
    (h : (Yᴴ * Y).trace = (Zᴴ * Z).trace) : hs Y = hs Z := by
  rw [← hs_sq_trace, ← hs_sq_trace] at h
  have h2 : hs Y ^ 2 = hs Z ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (hs_nonneg _) (hs_nonneg _)).mp h2
end Formalism.HermitianLatticeCounting.P
