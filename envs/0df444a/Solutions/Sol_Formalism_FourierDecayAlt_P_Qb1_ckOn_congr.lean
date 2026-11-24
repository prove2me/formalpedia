-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qb1.ckOn_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:24:57.288937+00:00
-- url     : https://prove2.me/submissions/b1bd497c-c796-42b2-b91a-21f745a97b71

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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ∞} {f f' : Mx k r → E}
    (he : ∀ g ∈ GV k r, f g = f' g) (h : CkOn m (GV k r) f) : CkOn m (GV k r) f' := by
  intro g₀ hg₀
  obtain ⟨U, F, a, b, c, d⟩ := h g₀ hg₀
  exact ⟨U, F, a, b, c, fun g hg hgG => (he g hgG).symm.trans (d g hg hgG)⟩
end Formalism.FourierDecayAlt.P.Qb1
