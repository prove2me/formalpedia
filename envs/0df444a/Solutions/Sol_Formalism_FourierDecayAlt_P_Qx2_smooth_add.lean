-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx2.smooth_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:19:31.186961+00:00
-- url     : https://prove2.me/submissions/2b45b94b-11d5-4fec-8dfd-4270b788d4f4

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta

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
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.Qx2
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.Qx2
theorem _root_.solution {f f₂ : Mx k r → E} (hf : SmoothLev k r i D f) (hf₂ : SmoothLev k r i D f₂) :
    SmoothLev k r i D (fun x => f x + f₂ x) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g₀ hg₀
  obtain ⟨U₂, F₂, hU₂, hgU₂, hF₂, he₂⟩ := hf₂ g₀ hg₀
  refine ⟨U ∩ U₂, fun x => F x + F₂ x, hU.inter hU₂, ⟨hgU, hgU₂⟩,
    (hF.mono Set.inter_subset_left).add (hF₂.mono Set.inter_subset_right), fun g hg hgG => ?_⟩
  simp only [he g hg.1 hgG, he₂ g hg.2 hgG]
end Formalism.FourierDecayAlt.P.Qx2
