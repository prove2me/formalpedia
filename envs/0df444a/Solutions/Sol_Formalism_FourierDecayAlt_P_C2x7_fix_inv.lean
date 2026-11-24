-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x7.fix_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:15:43.908746+00:00
-- url     : https://prove2.me/submissions/c806aa08-f710-4ce8-b046-175af34d9f92

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x7
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x7
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {g : B.Mat k r} (hg : g ∈ C2.FixSet k r z) :
    g⁻¹ ∈ C2.FixSet k r z := by
  have hu : IsUnit g.det := WeylGroupFacts.isUnit_of_uh hg.1
  refine ⟨WeylGroupFacts.uh_inv hg.1, fun a => ?_⟩
  calc g⁻¹ *ᵥ fvec k r z a = g⁻¹ *ᵥ (g *ᵥ fvec k r z a) := by rw [hg.2 a]
    _ = fvec k r z a := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
end Formalism.FourierDecayAlt.P.C2x7
