-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:33:47.620737+00:00
-- url     : https://prove2.me/submissions/357762da-f5a4-4dd8-b657-39e8c58e4078

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordIntegralScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordKeyIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveOrbitOpen
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveOrbitOpen_dmin_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_PositiveOrbitOpen_gf_cont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PositiveOrbitOpen
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
omit [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.PositiveOrbitOpen
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (Q.OmPlus k r z z') := by
  rw [isOpen_iff_mem_nhds]
  intro g hg
  have h1 : ∀ᶠ x in 𝓝 g, ∀ l : Fin (r + 2), l.val ≤ r → Dmin k r z z' x l ≠ 0 := by
    refine Filter.eventually_all.2 fun l => ?_
    by_cases hl : l.val ≤ r
    · filter_upwards [(dmin_cont z z' l).continuousAt.eventually_ne (hg.1 l hl)] with x hx
      exact fun _ => hx
    · exact Filter.Eventually.of_forall fun x h => absurd h hl
  have h2 : ∀ᶠ x in 𝓝 g, 0 < Gf k r z z' x := continuousAt_const.eventually_lt (gf_cont z z').continuousAt hg.2
  filter_upwards [h1, h2] with x hx1 hx2
  exact ⟨hx1, hx2⟩
end Formalism.FourierDecayAlt.P.PositiveOrbitOpen
