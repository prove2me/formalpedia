-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.PhiH_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:59:54.265018+00:00
-- url     : https://prove2.me/submissions/4501c7d0-7d3b-4081-9a85-9276f70edfa2

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_mem_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_outM_clsM
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_cls_bij
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_Tsum_translate
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_Tsum_conj
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_PhiH_eq_Tsum
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
variable {a s : ℕ}
variable {N : ℕ}
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution (ψ : AddChar K ℂ) (hψ : ∀ r ∈ R, ψ r = 1) (h : Point K) {n' : ℕ}
    (Z' : Matrix (Fin n') (Fin n') K) (s : ℕ) (Z a b : Matrix (Fin s) (Fin s) K)
    (ha : IsLowUni a) (hai : IsInt R a) (hb : IsUpUni b) (hbi : IsInt R b) :
    PhiH R ψ h Z' s (a * Z * b) = PhiH R ψ h Z' s Z := by
  have hda : a.det = 1 := isLowUni_det K ha
  have hdb : b.det = 1 := isUpUni_det K hb
  have hua : IsUnit a.det := by rw [hda]; exact isUnit_one
  have hub : IsUnit b.det := by rw [hdb]; exact isUnit_one
  have hadj : ∀ {c : Matrix (Fin s) (Fin s) K}, IsInt R c → IsInt R c.adjugate := by
    intro c hc
    have e : c = R.subtype.mapMatrix (Matrix.of fun i j => (⟨c i j, hc i j⟩ : R)) := by
      ext i j
      rfl
    rw [e, ← RingHom.map_adjugate]
    intro i j
    exact ((Matrix.adjugate (Matrix.of fun i j => (⟨c i j, hc i j⟩ : R))) i j).2
  have hinvI : ∀ {c : Matrix (Fin s) (Fin s) K}, IsInt R c → c.det = 1 → IsInt R c⁻¹ := by
    intro c hc hd
    rw [Matrix.inv_def, hd, Ring.inverse_one, one_smul]
    exact hadj hc
  have hF := cls_bij R (ι := Fin s) (κ := Fin h.1.sum) (fun U => a * U) (fun U => a⁻¹ * U)
    (fun U V => Matrix.mul_add _ _ _) (fun U V => Matrix.mul_add _ _ _)
    (fun V hV => mem_mul R hai hV) (fun V hV => mem_mul R (hinvI hai hda) hV)
    (fun U => by
      show a⁻¹ * (a * U) = U
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul a hua, Matrix.one_mul])
    (fun U => by
      show a * (a⁻¹ * U) = U
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv a hua, Matrix.one_mul])
  have hG := cls_bij R (ι := Fin h.1.sum) (κ := Fin s) (fun U => U * b) (fun U => U * b⁻¹)
    (fun U V => Matrix.add_mul _ _ _) (fun U V => Matrix.add_mul _ _ _)
    (fun V hV => mem_mul R hV hbi) (fun V hV => mem_mul R hV (hinvI hbi hdb))
    (fun U => by
      show U * b * b⁻¹ = U
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv b hub, Matrix.mul_one])
    (fun U => by
      show U * b⁻¹ * b = U
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul b hub, Matrix.mul_one])
  rw [PhiH_eq_Tsum, PhiH_eq_Tsum,
    ← finsum_comp_equiv ((Equiv.refl (Cos R h)).prodCongr
      ((Equiv.ofBijective _ hF).prodCongr (Equiv.ofBijective _ hG)))]
  refine finsum_congr fun τ => ?_
  simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.refl_apply,
    Equiv.ofBijective_apply]
  rw [Tsum_translate R ψ hψ Z' _ (a * outM R τ.2.1) _ (outM R τ.2.2 * b) _ _ (outM_clsM R _)
      (outM_clsM R _),
    Tsum_conj R ψ Z' _ _ _ _ a b ha hai hb hbi]
end Formalism.FourierDecayAlt.P.TwoBlockPoint
