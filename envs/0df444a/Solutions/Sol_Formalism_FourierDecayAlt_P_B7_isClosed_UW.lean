-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.isClosed_UW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:43:53.163731+00:00
-- url     : https://prove2.me/submissions/64e117fd-72e8-47ea-b1f7-4a557ba60d9f

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_isClosed_GV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) : IsClosed {x : Mt k r | Matrix.of x ∈ UWset k r z} := by
  have hmv : ∀ v : Fin (2 * r + k + 1) → ℂ, IsClosed {x : Mt k r | Matrix.of x *ᵥ v = v} := fun v =>
    isClosed_eq (by first | fun_prop | exact continuous_id.matrix_mulVec continuous_const) continuous_const
  have e : {x : Mt k r | Matrix.of x ∈ UWset k r z} = {x : Mt k r | Matrix.of x ∈ GV k r} ∩
      ((⋂ a : Fin r, ({x : Mt k r | Matrix.of x *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩
        {x : Mt k r | Matrix.of x *ᵥ bvec (esI k r a) = bvec (esI k r a)})) ∩ {x : Mt k r | Matrix.of x *ᵥ z = z}) := by
    ext x
    simp only [UWset, GV, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    try tauto
  rw [e]
  exact isClosed_GV.inter ((isClosed_iInter fun a => (hmv _).inter (hmv _)).inter (hmv z))
end Formalism.FourierDecayAlt.P.B7
