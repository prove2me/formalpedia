-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.KernelScalingBack.Kp_block
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:48.919389+00:00
-- url     : https://prove2.me/submissions/8c793604-277b-414e-b87b-6bd09f73bccf

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_Kp_scale
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_inv_entry
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_dg_ge
import Theorems.Thm_Formalism_FourierDecayAlt_P_KernelScalingBack_dg_lt
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_det_orbZ
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_inverse_last_column_formula
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
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.KernelScalingBack
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.KernelScalingBack
theorem _root_.solution (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (h : Point K) (s : ℕ) (hs : 1 ≤ s)
    (z k : Kˣ) (hk : (k : K) ∈ R) (hki : ((k⁻¹ : Kˣ) : K) ∈ R)
    (h1 : (((k⁻¹ : Kˣ) : K) - 1) *
      Ring.inverse (pt (addBlock h s z).1 (addBlock h s z).2).det ∈ R)
    (h2 : ((k : K) - 1) * (z : K) *
      Ring.inverse (pt (addBlock h s z).1 (addBlock h s z).2).det ∈ R) (w' : Point K) :
    Kp R ψ (addBlock h s (z * k)) w' = Kp R ψ (addBlock h s z) w' := by
  have e : addBlock h s (z * k) = ((h.1 ++ [s], Function.update h.2 h.1.length z *
      Function.update (1 : ℕ → Kˣ) h.1.length k) : Point K) := by
    unfold addBlock
    congr 1
    funext b
    by_cases hb : b = h.1.length
    · subst hb; simp
    · simp [Function.update_of_ne hb]
  have hsum : (h.1 ++ [s]).sum = h.1.sum + s := by simp
  have hlast : h.1.sum + s - 1 < (h.1 ++ [s]).sum := by omega
  rw [e]
  show _ = Kp R ψ ((h.1 ++ [s], Function.update h.2 h.1.length z) : Point K) w'
  refine Kp_scale R _ _ _ ψ hψ ?_ ?_ ?_ w'
  · intro b
    by_cases hb : b = h.1.length
    · subst hb; simp [hk, hki]
    · simp [Function.update_of_ne hb, R.one_mem]
  · intro p hZ j b hj
    rw [dg_ge h.1 s k j (by omega)]
    apply inv_entry R hZ
    rw [A5x5.det_orbZ]
    exact h1
  · intro p hZ j hj
    by_cases c1 : j.val + 1 < h.1.sum
    · rw [dg_lt h.1 s k j (by omega), dg_lt h.1 s k ⟨j.val + 1, hj⟩ c1]
      simp [R.zero_mem]
    · by_cases c2 : h.1.sum ≤ j.val
      · rw [dg_ge h.1 s k j c2, dg_ge h.1 s k ⟨j.val + 1, hj⟩ (by simp; omega)]
        simp [R.zero_mem]
      · rw [dg_lt h.1 s k j (by omega), dg_ge h.1 s k ⟨j.val + 1, hj⟩ (by simp; omega)]
        have hL := (Formalism.FourierDecayAlt.P.inverse_last_column_formula K h s z hs
          ((p.1 : GL (Fin (h.1 ++ [s]).sum) K) : Matrix (Fin (h.1 ++ [s]).sum) (Fin (h.1 ++ [s]).sum) K)
          ((p.2 : GL (Fin (h.1 ++ [s]).sum) K) : Matrix (Fin (h.1 ++ [s]).sum) (Fin (h.1 ++ [s]).sum) K)
          p.1.2.1 p.2.2 j ⟨h.1.sum + s - 1, hlast⟩ ⟨j.val + 1, hj⟩
          (by show h.1.sum + s - 1 + 1 = (h.1 ++ [s]).sum; omega)
          (by show j.val + 1 = h.1.sum; omega)).1
        have hZ' := inv_entry R hZ (x := ((k : K) - 1) * (z : K))
          (by rw [A5x5.det_orbZ]; exact h2) j ⟨h.1.sum + s - 1, hlast⟩
        have e3 : (orbZ ((h.1 ++ [s], Function.update h.2 h.1.length z) : Point K) p)⁻¹ j
            ⟨h.1.sum + s - 1, hlast⟩ = ((z⁻¹ : Kˣ) : K) *
            ((p.2 : GL (Fin (h.1 ++ [s]).sum) K) :
              Matrix (Fin (h.1 ++ [s]).sum) (Fin (h.1 ++ [s]).sum) K)⁻¹ j ⟨j.val + 1, hj⟩ := hL
        rw [e3] at hZ'
        rw [Subgroup.coe_inv, Matrix.coe_units_inv]
        have e4 : ((k : K) - 1) * (z : K) * (((z⁻¹ : Kˣ) : K) *
            ((p.2 : GL (Fin (h.1 ++ [s]).sum) K) :
              Matrix (Fin (h.1 ++ [s]).sum) (Fin (h.1 ++ [s]).sum) K)⁻¹ j ⟨j.val + 1, hj⟩) =
            ((((1 : Kˣ)⁻¹ : Kˣ) : K) * (k : K) - 1) *
            ((p.2 : GL (Fin (h.1 ++ [s]).sum) K) :
              Matrix (Fin (h.1 ++ [s]).sum) (Fin (h.1 ++ [s]).sum) K)⁻¹ j ⟨j.val + 1, hj⟩ := by
          have hz : (z : K) * ((z⁻¹ : Kˣ) : K) = 1 := Units.mul_inv z
          simp only [inv_one, Units.val_one, one_mul]
          linear_combination ((k : K) - 1) * ((p.2 : GL (Fin (h.1 ++ [s]).sum) K) :
              Matrix (Fin (h.1 ++ [s]).sum) (Fin (h.1 ++ [s]).sum) K)⁻¹ j ⟨j.val + 1, hj⟩ * hz
        rw [← e4]
        exact hZ'
end Formalism.FourierDecayAlt.P.KernelScalingBack
