-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.isClosed_nonneg_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:38:18.94425+00:00
-- url     : https://prove2.me/submissions/9a9403fc-ae55-4511-9302-e3e6e6f55bb7

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqOfContinuousOffZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ComplexConjugate ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution : IsClosed {z : ℂ | 0 ≤ z} := by
  have h : {z : ℂ | 0 ≤ z} = {z : ℂ | 0 ≤ z.re} ∩ {z : ℂ | z.im = 0} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Complex.le_def, Complex.zero_re, Complex.zero_im]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.symm⟩
  rw [h]
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    (isClosed_eq Complex.continuous_im continuous_const)
end Formalism.FourierDecayAlt.P5
