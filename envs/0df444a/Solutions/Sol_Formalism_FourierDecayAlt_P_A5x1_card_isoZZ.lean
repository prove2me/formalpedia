-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x1.card_isoZZ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:44:06.498878+00:00
-- url     : https://prove2.me/submissions/84475372-0341-48ea-bec0-da3b7a16aa1e

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TripleForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x1
namespace Formalism.FourierDecayAlt.P.A5x1
theorem _root_.solution {K : Type} [CommRing K] (R : Subring K) {n n' : ℕ} (Z : Matrix (Fin n) (Fin n) K)
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
end Formalism.FourierDecayAlt.P.A5x1
