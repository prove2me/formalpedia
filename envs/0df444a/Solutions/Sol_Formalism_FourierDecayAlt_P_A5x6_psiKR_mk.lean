-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x6.psiKR_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:41.248645+00:00
-- url     : https://prove2.me/submissions/24b6edcd-eb8f-4cf5-8647-5db26316611e

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MulInvBlockDiagApplySameBlock
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A5x6
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x6
theorem _root_.solution (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (a : K) :
    psiKR R ψ (Submodule.Quotient.mk a : KR R) = ψ a := by
  unfold psiKR
  set b := Quotient.out (Submodule.Quotient.mk a : KR R) with hb
  have h1 : b - a ∈ R := by
    rw [← mem_rangeR R, ← Submodule.Quotient.eq]
    exact Quotient.out_eq _
  calc ψ b = ψ (a + (b - a)) := by congr 1; abel
    _ = ψ a := by rw [AddChar.map_add_eq_mul, hψ _ h1, mul_one]
end Formalism.FourierDecayAlt.P.A5x6
