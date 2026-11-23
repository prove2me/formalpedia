-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x4.card_isoSet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:41.206308+00:00
-- url     : https://prove2.me/submissions/bfc14cca-f512-4b1c-9b4e-74c5dabb1d14

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val



set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x4
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.A5x4
theorem _root_.solution {n : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R)
    (φ0 : coker R Z ≃ₗ[R] C) (hφ0 : φ0 ∈ isoSet R Z C e lam) :
    Nat.card (isoSet R Z C e lam) = Nat.card (autSet R C e lam) := by
  refine Nat.card_congr ⟨fun φ => ⟨φ0.symm.trans φ.1, ?_⟩, fun σ => ⟨φ0.trans σ.1, ?_⟩, ?_, ?_⟩
  · refine ⟨?_, fun c => ?_⟩
    · have : φ0.symm e = eZ R Z := by rw [← hφ0.1]; simp
      simp [this, φ.2.1]
    · obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (φ0.symm c)
      have h3 : φ0 (Submodule.Quotient.mk v) = c := by rw [hv]; simp
      simp only [LinearEquiv.trans_apply]
      rw [← hv, φ.2.2 v, ← hφ0.2 v, h3]
  · refine ⟨?_, fun v => ?_⟩
    · simp [hφ0.1, σ.2.1]
    · simp only [LinearEquiv.trans_apply]
      rw [σ.2.2, hφ0.2]
  · intro φ; ext x; simp
  · intro σ; ext x; simp
end Formalism.FourierDecayAlt.P.A5x4
