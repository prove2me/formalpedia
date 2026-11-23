-- Prove2me | solution 1 for Formalism.MainNotions.TestSideWords.TwistedFiltration.G2.mem_of_X_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:56:49.689127+00:00
-- url     : https://prove2.me/submissions/12350c8f-e0a5-425b-b2fc-e67129bf733f

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_SumCCMulSumOfMulEqOne
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_TwistedSubstitution_TwistedMonomialFiltration_MaxTwistDegreePderivLeAddOne
import Theorems.Thm_Formalism_MainNotions_TestSideWords_TwistedFiltration_G1_flt_lift_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.TestSideWords Formalism.MainNotions.TestSideWords.TwistedFiltration Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
variable {R : Type*} [CommRing R] {ι : Type} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
theorem _root_.solution {e t : ℤ} (v : ι × Fin n) (P : MvPolynomial (ι × Fin n) (GLLaurent R n))
    (h : X v * P ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t) : P ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F t := by
  rw [laurentCoeffFiltration, flt_lift_mem] at h ⊢
  intro m
  have hm := h (Finsupp.single v 1 + m)
  rw [coeff_X_mul] at hm
  simpa using hm
end Formalism.MainNotions.TestSideWords.TwistedFiltration.G2
