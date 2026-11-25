-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliTwoByTwo.capelli_two_eval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:59:34.066494+00:00
-- url     : https://prove2.me/submissions/f503e3bb-0d90-42c6-8e8a-4725fc7195fd

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliTwoByTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_good_ybv
import Theorems.Thm_Formalism_FourierDecayAlt_P_OperatorRepresentations_good_yv


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
open Formalism.FourierDecayAlt.P.CapelliTwoByTwo
variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
namespace Formalism.FourierDecayAlt.P.CapelliTwoByTwo
theorem _root_.solution (hD : IsOpen D) (z : Fin (2 * r + k + 1) → ℂ) (u : ℂ) (x ξ : Fin (mdim k r i) → ℂ)
    (ψ : SV k r i D E) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    (ch2 (EV k r i D E) u (yV k r z i D E) x (etaV k r z i D E) ξ ψ).1 g =
      (chat2A (EV k r i D E) u (yv k r z i g) x (ybv k r z i g) ξ ψ).1 g := by
  have hy : ∀ (c : Fin (mdim k r i)) (φ : SV k r i D E),
      ((yV k r z i D E c) φ).1 g = yv k r z i g c • φ.1 g := by
    intro c φ
    unfold yV opV
    rw [dif_pos ⟨hD, OperatorRepresentations.good_yv z c⟩]
    show cutF k r i D (mulF _ φ.1) g = _
    rw [cutF_of_mem hg]
    rfl
  have hη : ∀ (c : Fin (mdim k r i)) (φ : SV k r i D E),
      ((etaV k r z i D E c) φ).1 g = ybv k r z i g c • φ.1 g := by
    intro c φ
    unfold etaV opV
    rw [dif_pos ⟨hD, OperatorRepresentations.good_ybv z c⟩]
    show cutF k r i D (mulF _ φ.1) g = _
    rw [cutF_of_mem hg]
    rfl
  unfold ch2 chat2A
  simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ =>
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
  split_ifs
  · simp only [LinearMap.smul_apply, Module.End.mul_apply, LinearMap.sub_apply, Submodule.coe_smul,
      Submodule.coe_sub, Pi.smul_apply, Pi.sub_apply, hy, hη]
    module
  · rfl
end Formalism.FourierDecayAlt.P.CapelliTwoByTwo
