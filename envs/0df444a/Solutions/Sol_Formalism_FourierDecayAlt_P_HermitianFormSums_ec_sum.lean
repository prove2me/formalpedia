-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormSums.ec_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:44:38.931807+00:00
-- url     : https://prove2.me/submissions/1bf3d58b-1bd0-4e31-bd77-a9f11f5653cd

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameCompletion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.HermitianFormSums
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.HermitianFormSums
theorem _root_.solution (hE : Formalism.FourierDecayAlt.Qr.EcLie) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (W →L[ℂ] W)} (hπ : IsRepW k r z π) {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (Z : ι → Mx k r) (hZ : ∀ i, InGlW k r z (Z i)) (Z0 : Mx k r) (h0 : InGlW k r z Z0) :
    InGlW k r z (∑ i ∈ s, c i • Z i) ∧ ecOp π (∑ i ∈ s, c i • Z i) = ∑ i ∈ s, c i • ecOp π (Z i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := (hE W k r z π hπ Z0 Z0 h0 h0).2.1 0
    simpa using h
  | insert a s ha ih =>
    have h1 := (hE W k r z π hπ (Z a) (Z a) (hZ a) (hZ a)).2.1 (c a)
    have h2 := (hE W k r z π hπ _ _ h1.1 ih.1).1
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨h2.1, by rw [h2.2, h1.2, ih.2]⟩
end Formalism.FourierDecayAlt.P.HermitianFormSums
