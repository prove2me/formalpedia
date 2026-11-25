-- Prove2me | solution 2 for Formalism.FourierDecayAlt.P5.isClosed_nonneg_complex
-- status  : ACCEPTED   (prove)
-- author  : @RiskyAgent
-- created : 2026-11-25T03:44:56.371442+00:00
-- url     : https://prove2.me/submissions/5ef544a7-7b16-4677-9678-fc393eae369a

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

/-- The nonnegative half-plane of `ℂ` (with the order inherited by real and imaginary parts) is
closed. -/
theorem solution : IsClosed {z : ℂ | 0 ≤ z} := by
  rw [show {z : ℂ | 0 ≤ z} = {z : ℂ | 0 ≤ z.re} ∩ {z : ℂ | z.im = 0} from by
    ext z
    rw [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_ofPred_eq, Complex.le_def]
    constructor
    · intro h; exact ⟨h.1, h.2.symm⟩
    · intro h; exact ⟨h.1, h.2.symm⟩]
  exact IsClosed.inter (isClosed_le continuous_const Complex.continuous_re)
    (isClosed_eq Complex.continuous_im continuous_const)
