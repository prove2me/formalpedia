-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qb1.ckOn_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:24:56.461915+00:00
-- url     : https://prove2.me/submissions/3862278d-f0d0-4ecb-82b3-d583c9b57353

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CasimirEigenvalueCoefficients
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_LL_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_add


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
    (h : CkOn m (GV k r) f) (h' : CkOn m (GV k r) f') : CkOn m (GV k r) (fun g => f g + f' g) := by
  intro g₀ hg₀
  obtain ⟨U, F, a, b, c, d⟩ := h g₀ hg₀
  obtain ⟨U', F', a', b', c', d'⟩ := h' g₀ hg₀
  refine ⟨U ∩ U', fun g => F g + F' g, a.inter a', ⟨b, b'⟩, ?_, ?_⟩
  · exact (c.mono Set.inter_subset_left).add (c'.mono Set.inter_subset_right)
  · intro g hg hgG
    show f g + f' g = F g + F' g
    rw [d g hg.1 hgG, d' g hg.2 hgG]
end Formalism.FourierDecayAlt.P.Qb1
