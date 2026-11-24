-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.shortIndependentVectorsOfDualMinimum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:56:30.655822+00:00
-- url     : https://prove2.me/submissions/592ba121-ea1b-48af-ae67-a74025317b0a

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ExistsNeZeroNormLeRankDivOfDualMinimum
import Definitions.Def_Formalism_LatticeSlopes_CovolAntiSameRank
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_SaturationProperties
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DegQuot
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_ShortIndependentVectorsOfDualMinimum
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_exists_short_linearIndependent_of_dualMinimum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace Formalism.NormUnitaryCountingLemmas
theorem _root_.solution : ShortIndependentVectorsOfDualMinimum := by
  intro E _ _ _ M hMd hspan l hl hdual
  haveI := hMd
  obtain ⟨b, hbM, hbli, hbn, -⟩ := exists_short_linearIndependent_of_dualMinimum M hspan hl hdual (finrank ℝ E) le_rfl
  refine ⟨b, hbM, hbli, fun i => ?_⟩
  have hn0 : (0 : ℝ) < (finrank ℝ E : ℝ) := by exact_mod_cast Fin.pos i
  have h1 : ‖b i‖ ≤ Real.sqrt (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) / l) := by
    have h2 := hbn i
    have h3 : 0 ≤ Real.sqrt (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) / l) := by positivity
    have h4 : (Real.sqrt (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) / l)) ^ 2 =
        (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) / l) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hn0.le]
    nlinarith [norm_nonneg (b i)]
  have h5 : (finrank ℝ E : ℝ) ^ ((3 : ℝ) / 2) = (finrank ℝ E : ℝ) * Real.sqrt (finrank ℝ E : ℝ) := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hn0, Real.rpow_one, Real.sqrt_eq_rpow]
  rw [h5]
  calc ‖b i‖ ≤ Real.sqrt (finrank ℝ E : ℝ) * ((finrank ℝ E : ℝ) / l) := h1
    _ = (finrank ℝ E : ℝ) * Real.sqrt (finrank ℝ E : ℝ) / l := by ring
end Formalism.NormUnitaryCountingLemmas
