-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x4.sum_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:36:41.929519+00:00
-- url     : https://prove2.me/submissions/2c9c4399-633c-45cc-9392-3d2fc8d1516b

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationInvarianceEverySetting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x4
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x4
theorem _root_.solution (k r' : ℕ) (F : Fin (2 * (1 + r') + k + 1) → ℂ)
    (h : ∀ p, ¬ (1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) → F p = 0) :
    ∑ p, F p = ∑ j, F (levPos k 1 r' j) := by
  symm
  apply Finset.sum_of_injOn (levPos k 1 r')
  · intro a _ b _ hab
    have := congrArg Fin.val hab
    simp only [levPos] at this
    exact Fin.ext (by omega)
  · intro a _; exact Finset.mem_coe.2 (Finset.mem_univ _)
  · intro p _ hp
    apply h
    intro hc
    apply hp
    refine ⟨⟨p.val - 1, by omega⟩, Finset.mem_coe.2 (Finset.mem_univ _), ?_⟩
    apply Fin.ext
    simp only [levPos]
    omega
  · intro _ _; rfl
end Formalism.FourierDecayAlt.P.B2x4
