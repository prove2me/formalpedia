-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OperatorRepresentations.smooth_coef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:14:27.81469+00:00
-- url     : https://prove2.me/submissions/86ea1cfc-73e3-4fbb-b14a-b190eba543f2

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.OperatorRepresentations
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.OperatorRepresentations
theorem _root_.solution {c : Mx k r → ℂ} {f : Mx k r → E} (hc : SmoothLev k r i D c) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (fun g => c g • f g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hc g₀ hg₀
  obtain ⟨U₂, F₂, hU₂, hgU₂, hF₂, he₂⟩ := hf g₀ hg₀
  refine ⟨U ∩ U₂, fun x => F x • F₂ x, hU.inter hU₂, ⟨hgU, hgU₂⟩,
    (hF.mono Set.inter_subset_left).smul (hF₂.mono Set.inter_subset_right), ?_⟩
  intro x hx hxG
  show c x • f x = F x • F₂ x
  rw [he x hx.1 hxG, he₂ x hx.2 hxG]
end Formalism.FourierDecayAlt.P.OperatorRepresentations
