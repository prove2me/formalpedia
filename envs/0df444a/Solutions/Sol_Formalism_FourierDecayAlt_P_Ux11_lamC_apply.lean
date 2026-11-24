-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux11.lamC_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:27:09.563809+00:00
-- url     : https://prove2.me/submissions/c3a02868-4e88-43f2-a124-a9ff093d4879

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakToStrongSmoothnessReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux11
variable {k ρ mm : ℕ} {E V : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V]
  [NormedSpace ℂ V] {a : ℝ} {S : Set (B.Mat k ρ)}
namespace Formalism.FourierDecayAlt.P.Ux11
theorem _root_.solution (M : U.CCModel k ρ E a mm S V) (t : Idx k ρ mm) (w : V) :
    lamC M t w = ((B.gN t.1.2.2 ^ a : ℝ) : ℂ) • B.dLR t.1.1 t.1.2.1 (M.ev w) t.1.2.2 := rfl
end Formalism.FourierDecayAlt.P.Ux11
