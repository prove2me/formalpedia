-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.Fz_perturb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:44.234847+00:00
-- url     : https://prove2.me/submissions/64330b21-14b3-4821-8608-a6e0575b53c9

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_pert_unit
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_pert_latZ
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_pert_lamLin
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoBlockPoint_pert_card
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_isInt_adjugate
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_isInt_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x6_det_mem
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
theorem _root_.solution (ϖ : K) (hϖ : ϖ ∈ R) (hu : ∀ r ∈ R, ∃ y ∈ R, (1 + ϖ * r) * y = 1) {N n' : ℕ}
    (Z' : Matrix (Fin n') (Fin n') K) (Z P : Matrix (Fin N) (Fin N) K) (hd : IsUnit Z.det)
    (hPi : IsInt R P) (hP : ∀ i j, ∃ r ∈ R, P i j = Z.det ^ 2 * (ϖ * r)) :
    Fz R Z' (Z + P) = Fz R Z' Z := by
  unfold Fz
  by_cases hZ : IsInt R Z
  swap
  · rw [if_neg hZ, if_neg]
    intro h
    apply hZ
    intro i j
    have := R.sub_mem (h i j) (hPi i j)
    simpa using this
  have hZP : IsInt R (Z + P) := fun i j => R.add_mem (hZ i j) (hPi i j)
  rw [if_pos hZ, if_pos hZP]
  congr 1

  choose p hpR hp using hP
  set d : K := Z.det with hdef
  have hdR : d ∈ R := A5x6.det_mem R Z hZ
  obtain ⟨di, hdi⟩ : ∃ di : K, d * di = 1 := ⟨_, Ring.mul_inverse_cancel d hd⟩
  have hinv : Ring.inverse d = di := by
    have := Ring.mul_inverse_cancel d hd
    calc Ring.inverse d = Ring.inverse d * (d * di) := by rw [hdi, mul_one]
      _ = (d * Ring.inverse d) * di := by ring
      _ = di := by rw [this, one_mul]
  let P₀ : Matrix (Fin N) (Fin N) K := Matrix.of p
  have hP₀ : IsInt R P₀ := fun i j => hpR i j
  have hPeq : P = (d ^ 2 * ϖ) • P₀ := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, P₀, Matrix.of_apply]
    rw [hp i j]; ring
  have hadj : IsInt R Z.adjugate := Formalism.DoubleCosetMeasures.P.isInt_adjugate R hZ
  let M' : Matrix (Fin N) (Fin N) K := Z.adjugate * (d • P₀)
  have hM' : IsInt R M' :=
    Formalism.DoubleCosetMeasures.P.isInt_mul R hadj (fun i j => by
      simp only [Matrix.smul_apply, smul_eq_mul]; exact R.mul_mem hdR (hP₀ i j))
  let ϖR : R := ⟨ϖ, hϖ⟩
  let MR : Matrix (Fin N) (Fin N) R := Formalism.DoubleCosetMeasures.P.liftR R M' hM'
  let g : Matrix (Fin N) (Fin N) R := 1 + ϖR • MR
  have huR : ∀ r : R, IsUnit (1 + ϖR * r) := by
    intro r
    obtain ⟨y, hy, e⟩ := hu r r.2
    exact IsUnit.of_mul_eq_one (⟨y, hy⟩ : R) (Subtype.ext e)
  have hgdet : IsUnit g.det := pert_unit R ϖR huR MR
  have hgg : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hgdet
  have hgmap : g.map R.subtype = 1 + ϖ • M' := by
    ext i j
    simp only [g, MR, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Formalism.DoubleCosetMeasures.P.liftR, ϖR]
    by_cases hij : i = j <;> simp [hij]
  have hZadj : Z * Z.adjugate = d • (1 : Matrix (Fin N) (Fin N) K) := Matrix.mul_adjugate Z
  have hZg : Z * g.map R.subtype = Z + P := by
    rw [hgmap, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, hZadj, hPeq]
    congr 1
    rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, smul_smul]
    congr 1; ring
  let δ : Matrix (Fin N) (Fin N) K := (g⁻¹).map R.subtype
  have hδ : IsInt R δ := fun i j => (g⁻¹ i j).2
  have hgδ : (1 + ϖ • M') * δ = 1 := by
    rw [← hgmap, ← Matrix.map_mul, hgg, Matrix.map_one _ (map_zero _) (map_one _)]
  let W : Matrix (Fin N) (Fin N) K := ϖ • (Z.adjugate * P₀ * δ * Z.adjugate)
  have hW : IsInt R W := fun i j => by
    simp only [W, Matrix.smul_apply, smul_eq_mul]
    exact R.mul_mem hϖ (Formalism.DoubleCosetMeasures.P.isInt_mul R (Formalism.DoubleCosetMeasures.P.isInt_mul R
      (Formalism.DoubleCosetMeasures.P.isInt_mul R hadj hP₀) hδ) hadj i j)
  have hZi : Z⁻¹ = di • Z.adjugate := by rw [Matrix.inv_def, ← hdef, hinv]
  have hinvZP : (Z + P)⁻¹ = Z⁻¹ - W := by
    have e1 : (Z + P)⁻¹ = δ * Z⁻¹ := by
      apply Matrix.inv_eq_right_inv
      rw [← hZg, hgmap, Matrix.mul_assoc, ← Matrix.mul_assoc _ δ, hgδ, Matrix.one_mul,
        Matrix.mul_nonsing_inv Z hd]
    have e2 : δ = 1 - (ϖ • M') * δ := by
      rw [eq_sub_iff_add_eq, ← hgδ, Matrix.add_mul, Matrix.one_mul]
    rw [e1]
    conv_lhs => rw [e2]
    rw [Matrix.sub_mul, Matrix.one_mul]
    congr 1
    rw [hZi]
    simp only [M', W, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
    congr 1
    linear_combination ϖ * hdi
  refine pert_card R Z' Z (Z + P) ?_ (pert_lamLin R Z (Z + P) W hW hinvZP)
  rw [← hZg]
  exact (pert_latZ R Z g g⁻¹ hgg).symm
end Formalism.FourierDecayAlt.P.TwoBlockPoint
