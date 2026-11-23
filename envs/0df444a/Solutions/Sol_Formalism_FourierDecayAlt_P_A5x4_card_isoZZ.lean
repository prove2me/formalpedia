-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x4.card_isoZZ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:58.514387+00:00
-- url     : https://prove2.me/submissions/163b8915-46bf-40f8-a2db-e3a25d97c2ed

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
theorem _root_.solution {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K)
    (Z' : Matrix (Fin n') (Fin n') K)
    (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R)
    (φ0 : coker R Z ≃ₗ[R] C) (hφ0 : φ0 ∈ isoSet R Z C e lam) :
    Nat.card (isoSet R Z' C e lam) = Nat.card (isoZZ R Z Z') := by
  refine Nat.card_congr ⟨fun ρ => ⟨φ0.trans ρ.1.symm, ?_⟩, fun φ => ⟨φ.1.symm.trans φ0, ?_⟩, ?_, ?_⟩
  · refine ⟨?_, fun v v' hv => ?_⟩
    · simp only [LinearEquiv.trans_apply, hφ0.1]
      exact (LinearEquiv.symm_apply_eq _).2 ρ.2.1.symm
    · simp only [LinearEquiv.trans_apply] at hv
      have h4 : φ0 (Submodule.Quotient.mk v) = ρ.1 (Submodule.Quotient.mk v') := by
        rw [← hv]; simp
      rw [← ρ.2.2 v', ← h4, hφ0.2]
  · refine ⟨?_, fun v' => ?_⟩
    · have : φ.1.symm (eZ R Z') = eZ R Z := by rw [← φ.2.1]; simp
      simp [this, hφ0.1]
    · obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (φ.1.symm (Submodule.Quotient.mk v'))
      have h3 : φ.1 (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' := by rw [hv]; simp
      simp only [LinearEquiv.trans_apply]
      rw [← hv, hφ0.2 v, φ.2.2 v v' h3]
  · intro ρ; ext x; simp
  · intro φ; ext x; simp
end Formalism.FourierDecayAlt.P.A5x4
