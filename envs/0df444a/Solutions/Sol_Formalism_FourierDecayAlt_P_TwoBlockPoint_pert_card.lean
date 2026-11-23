-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.pert_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:16.609339+00:00
-- url     : https://prove2.me/submissions/44061940-1cf8-4e7f-b352-a0e4fe51fc98

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_fib
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_gl_coe
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mem_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_right_eq
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
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoBlockPoint
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution {N n' : ℕ} (Z' : Matrix (Fin n') (Fin n') K) (Z Z₁ : Matrix (Fin N) (Fin N) K)
    (h1 : latZ R Z = latZ R Z₁) (h2 : ∀ v, lamLin R Z₁ v = lamLin R Z v) :
    Nat.card (isoZZ R Z₁ Z') = Nat.card (isoZZ R Z Z') := by
  let ψ : coker R Z ≃ₗ[R] coker R Z₁ := Submodule.quotEquivOfEq _ _ h1
  have hψe : ψ (eZ R Z) = eZ R Z₁ := rfl
  have hψm : ∀ v : Fin N → R, ψ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := fun v => rfl
  let e : (coker R Z₁ ≃ₗ[R] coker R Z') ≃ (coker R Z ≃ₗ[R] coker R Z') :=
    ⟨fun φ => ψ.trans φ, fun φ => ψ.symm.trans φ, fun φ => by ext x; simp, fun φ => by ext x; simp⟩
  refine Nat.card_congr (e.subtypeEquiv fun φ => ?_)
  simp only [isoZZ, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1', h2'⟩
    refine ⟨?_, fun v v' hv => ?_⟩
    · show φ (ψ (eZ R Z)) = eZ R Z'
      rw [hψe, h1']
    · have hv' : φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' := by
        rw [← hψm v]
        exact hv
      rw [h2' v v' hv', h2]
  · rintro ⟨h1', h2'⟩
    refine ⟨?_, fun v v' hv => ?_⟩
    · rw [← hψe]
      exact h1'
    · have hv' : (e φ) (Submodule.Quotient.mk v) = Submodule.Quotient.mk v' := by
        show φ (ψ (Submodule.Quotient.mk v)) = _
        rw [hψm v]
        exact hv
      rw [h2' v v' hv', h2]
end Formalism.FourierDecayAlt.P.TwoBlockPoint
