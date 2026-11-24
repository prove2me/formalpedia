-- Prove2me | solution 1 for Formalism.L2.Th1.C.lGSubgroup_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:23:15.731706+00:00
-- url     : https://prove2.me/submissions/75810b39-6315-4b92-9cb4-142c731c0ee5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_one
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_mul
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_intMv_of_mul_eq_one
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_constantCoeff_mvExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open IntegralMvPolynomialLemmas
namespace Formalism.L2.Th1.C
theorem _root_.solution (hE : MvExpLaws) : LGSubgroup := by
  intro K _ _ R σ
  obtain ⟨h0, -, hadd, -⟩ := hE K σ
  refine ⟨⟨map_zero _, ?_⟩, ?_, ?_⟩
  · rw [h0]; exact intMv_one
  · intro f g hf hg
    refine ⟨by rw [map_add, hf.1, hg.1, add_zero], ?_⟩
    rw [hadd f g hf.1 hg.1]
    exact intMv_mul hf.2 hg.2
  · intro f hf
    have hn : MvPowerSeries.constantCoeff (-f) = 0 := by rw [map_neg, hf.1, neg_zero]
    refine ⟨hn, intMv_of_mul_eq_one hf.2 (constantCoeff_mvExp hf.1) ?_⟩
    rw [← hadd f (-f) hf.1 hn, add_neg_cancel, h0]
end Formalism.L2.Th1.C
