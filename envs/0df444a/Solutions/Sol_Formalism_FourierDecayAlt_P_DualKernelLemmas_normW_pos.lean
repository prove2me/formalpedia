-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DualKernelLemmas.normW_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:09:38.133375+00:00
-- url     : https://prove2.me/submissions/4fc445be-99b8-4a8b-ac62-dcc97c1a4fe9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PartialFlipCommuteDiagScalarOfFree
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualKernelLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DualKernelLemmas
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities
open scoped Matrix
namespace Formalism.FourierDecayAlt.P.DualKernelLemmas
theorem _root_.solution {S : Type} (nn : ℝ → ℝ) (w : List (Letter ℂ S)) (h : ∀ l ∈ w, 0 < nn l.pt.re) :
    0 < normW nn w := by
  unfold normW
  apply List.prod_pos
  intro x hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  exact h l hl
end Formalism.FourierDecayAlt.P.DualKernelLemmas
