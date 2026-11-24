-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.OperatorRepresentations.Rep.bridge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:53:48.914594+00:00
-- url     : https://prove2.me/submissions/398d0744-0a75-46e4-bdb9-d3691bb44787

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_smooth_congr

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
namespace Rep
theorem _root_.solution (hD : IsOpen D) {X : Module.End ℂ (SV k r i D E)} {T L : (Mx k r → E) → Mx k r → E}
    (hX : Rep X T) (hL : ∀ f, ∀ g ∈ Glev k r i ∩ D, L f g = T f g) (f : Mx k r → E) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (L f) ∧ ∀ g ∈ Glev k r i ∩ D, L f g = (X (Qr.mkV hD f hf)).1 g :=
  ⟨smooth_congr hD (hX.1.sm f hf) (hL f), fun g hg => by rw [hX.mkV hD hf hg, hL f g hg]⟩
end Rep
end Formalism.FourierDecayAlt.P.OperatorRepresentations
