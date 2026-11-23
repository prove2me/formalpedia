-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.isoInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:59:54.760496+00:00
-- url     : https://prove2.me/submissions/021725d3-41d1-4e92-ace0-3c938791f442

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_liftR_map
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_cokEquiv_mk
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_cokEquiv_eZ
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_lamLin_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures
namespace Formalism.DoubleCosetMeasures.P
theorem _root_.solution : IsoInv := by
  intro K _ R n a b Z ha hb hai hbi C _ _ e lam
  obtain ⟨A, rfl⟩ : ∃ A : Matrix (Fin n) (Fin n) R, A.map R.subtype = a :=
    ⟨liftR R a hai, liftR_map R a hai⟩
  obtain ⟨B, rfl⟩ : ∃ B : Matrix (Fin n) (Fin n) R, B.map R.subtype = b :=
    ⟨liftR R b hbi, liftR_map R b hbi⟩
  have hA : (A.map R.subtype).det = 1 := by
    rw [Matrix.det_of_lowerTriangular _ ha.1]
    exact Finset.prod_eq_one (fun i _ => ha.2 i)
  have hB : (B.map R.subtype).det = 1 := by
    rw [Matrix.det_of_upperTriangular hb.1]
    exact Finset.prod_eq_one (fun i _ => hb.2 i)
  have hAA : A * A⁻¹ = 1 :=
    Matrix.mul_nonsing_inv A (by rw [det_lift_eq_one R A hA]; exact isUnit_one)
  refine Nat.card_congr (Equiv.subtypeEquiv
    { toFun := fun φ => (cokEquiv R A B Z hA hB).trans φ
      invFun := fun ψ => (cokEquiv R A B Z hA hB).symm.trans ψ
      left_inv := fun φ => by
        ext x
        rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      right_inv := fun ψ => by
        ext x
        rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] } ?_)
  intro φ
  simp only [isoSet, Set.mem_setOf_eq, Equiv.coe_fn_mk]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun v => ?_⟩
    · show φ (cokEquiv R A B Z hA hB (eZ R Z)) = e
      rw [cokEquiv_eZ R A B Z hA hB ha]
      exact h1
    · show lam (φ (cokEquiv R A B Z hA hB (Submodule.Quotient.mk v))) = lamLin R Z v
      rw [cokEquiv_mk, h2, lamLin_mul R A B Z hA hb]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun v => ?_⟩
    · rw [← cokEquiv_eZ R A B Z hA hB ha]
      exact h1
    · have h3 := h2 (A⁻¹ *ᵥ v)
      change lam (φ (cokEquiv R A B Z hA hB (Submodule.Quotient.mk (A⁻¹ *ᵥ v)))) = _ at h3
      rw [cokEquiv_mk, Matrix.mulVec_mulVec, hAA, Matrix.one_mulVec] at h3
      rw [h3, ← lamLin_mul R A B Z hA hb (A⁻¹ *ᵥ v), Matrix.mulVec_mulVec, hAA,
        Matrix.one_mulVec]
end Formalism.DoubleCosetMeasures.P
