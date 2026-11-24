-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qb1.ckOn_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:24:58.327158+00:00
-- url     : https://prove2.me/submissions/d88251a6-d835-46e0-ab01-6c7c2c491e35

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CasimirEigenvalueCoefficients

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qb1
variable {k r : ℕ} {Vs : Type} [NormedAddCommGroup Vs] [NormedSpace ℂ Vs]
namespace Formalism.FourierDecayAlt.P.Qb1
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {f : Mx k r → E} (s : ℂ)
    (h : CkOn m (GV k r) f) : CkOn m (GV k r) (fun g => s • f g) := by
  intro g₀ hg₀
  obtain ⟨U, F, a, b, c, d⟩ := h g₀ hg₀
  refine ⟨U, fun g => s • F g, a, b, ?_, ?_⟩
  · exact c.const_smul s
  · intro g hg hgG
    show s • f g = s • F g
    rw [d g hg hgG]
end Formalism.FourierDecayAlt.P.Qb1
