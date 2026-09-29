-- Prove2me | solution 1 for CuspForm.traceLin_of_coe_eq_slash_heckeDiagMatrix
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/a5527046-4a81-5252-b69d-db74d7faa3e1

import Definitions.Def_CuspForm_AtkinLehnerOperator
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix

set_option Elab.async false

set_option autoImplicit false

open UpperHalfPlane CongruenceSubgroup
p2m_open_scoped "ModularForm P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.ModularForm MatrixGroups"

noncomputable section

namespace ModularForm
p2m_export "ModularForm" "IsGLPos.coe_smul coe_smul slash_apply ext add_apply smul_apply atkinLehnerLin coe_atkinLehnerLin_apply AtkinLehnerDatum AtkinLehnerDatum.alGL alSlash alSlash_def heckeMatrix heckeDiagMatrix val_heckeMatrix val_heckeDiagMatrix heckeU heckeT heckeU_def heckeT_eq_heckeU_add heckeTLin coe_heckeTLin_apply"
p2m_open "ModularForm"

variable {M q : ℕ}

def scalarGL (hq : 0 < q) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℝ), 0; 0, (q : ℝ)] (by
    rw [Matrix.det_fin_two_of]
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    simpa using mul_ne_zero hq' hq')

@[scoped simp] lemma scalarGL_coe (hq : 0 < q) :
    (scalarGL hq : Matrix (Fin 2) (Fin 2) ℝ) = !![(q : ℝ), 0; 0, (q : ℝ)] := rfl

lemma det_scalarGL (hq : 0 < q) : ((scalarGL hq).det : ℝ) = (q : ℝ) ^ 2 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, scalarGL_coe, Matrix.det_fin_two_of]; ring

lemma det_scalarGL_pos (hq : 0 < q) : 0 < ((scalarGL hq).det : ℝ) := by
  rw [det_scalarGL]
  positivity

lemma slash_scalarGL (k : ℤ) (hq : 0 < q) (f : ℍ → ℂ) :
    f ∣[k] scalarGL hq = ((q : ℂ) ^ (k - 2)) • f := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  ext τ
  rw [ModularForm.slash_apply, Pi.smul_apply, smul_eq_mul]

  have hσ : σ (scalarGL hq) (f (scalarGL hq • τ)) = f (scalarGL hq • τ) := by
    rw [UpperHalfPlane.σ, if_pos (det_scalarGL_pos hq)]; rfl

  have hdenom : denom (scalarGL hq) ↑τ = (q : ℝ) := by
    simp only [UpperHalfPlane.denom, scalarGL_coe]
    simp

  have hsmul : scalarGL hq • τ = τ := by
    apply UpperHalfPlane.ext
    rw [coe_smul_of_det_pos (det_scalarGL_pos hq)]
    simp only [num, denom, scalarGL_coe]
    have hqC' : ((q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    simp
    field_simp
  rw [hσ, hsmul, det_scalarGL, hdenom, abs_of_pos (by positivity : (0 : ℝ) < (q : ℝ) ^ 2)]
  have h1 : (((q : ℝ) ^ 2 : ℝ) : ℂ) = (q : ℂ) ^ (2 : ℕ) := by push_cast; ring
  have h2 : (((q : ℝ) : ℝ) : ℂ) = (q : ℂ) := by push_cast; ring
  rw [h1, h2, ← zpow_natCast ((q : ℂ)) 2, ← zpow_mul, mul_assoc, ← zpow_add₀ hqC]
  rw [show (2 : ℕ) * (k - 1) + -k = k - 2 by push_cast; ring]
  ring

end ModularForm
p2m_reactivate "P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.ModularForm"

namespace ModularForm
p2m_export "ModularForm" "IsGLPos.coe_smul coe_smul slash_apply ext add_apply smul_apply atkinLehnerLin coe_atkinLehnerLin_apply AtkinLehnerDatum AtkinLehnerDatum.alGL alSlash alSlash_def heckeMatrix heckeDiagMatrix val_heckeMatrix val_heckeDiagMatrix heckeU heckeT heckeU_def heckeT_eq_heckeU_add heckeTLin coe_heckeTLin_apply"
namespace AtkinLehnerDatum
p2m_export "ModularForm.AtkinLehnerDatum" "q_pos mat alGL alGL_coe b bezout R a"
p2m_open "ModularForm.AtkinLehnerDatum ModularForm"

p2m_open "ModularForm P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.ModularForm Matrix"

variable {M q : ℕ} (W : AtkinLehnerDatum M q)

private def _root_.ModularForm.AtkinLehnerDatum.lowerLeftSL : SL(2, ℤ) :=
  ⟨!![W.a, W.b; (W.R : ℤ), (q : ℤ)], by
    rw [Matrix.det_fin_two_of]; linear_combination W.bezout⟩

p2m_export "ModularForm.AtkinLehnerDatum" "lowerLeftSL"
@[scoped simp] lemma lowerLeftSL_coe :
    (W.lowerLeftSL : Matrix (Fin 2) (Fin 2) ℤ) = !![W.a, W.b; (W.R : ℤ), (q : ℤ)] := rfl

private lemma _root_.ModularForm.AtkinLehnerDatum.lowerLeftSL_mem : W.lowerLeftSL ∈ Gamma0 W.R := by
  rw [Gamma0_mem]
  show (((W.lowerLeftSL : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod W.R) = 0
  simp

p2m_export "ModularForm.AtkinLehnerDatum" "lowerLeftSL_mem"

private theorem _root_.ModularForm.AtkinLehnerDatum.mat_eq_lowerLeftSL_mul_diagMat :
    W.mat = (W.lowerLeftSL : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1] := by
  rw [mat, lowerLeftSL_coe, Matrix.mul_fin_two]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

p2m_export "ModularForm.AtkinLehnerDatum" "mat_eq_lowerLeftSL_mul_diagMat"

private def _root_.ModularForm.AtkinLehnerDatum.bqALUnitSL : SL(2, ℤ) :=
  ⟨!![(q : ℤ) * W.a, W.b; (W.R : ℤ), 1], by
    rw [Matrix.det_fin_two_of]; linear_combination W.bezout⟩

p2m_export "ModularForm.AtkinLehnerDatum" "bqALUnitSL"
@[scoped simp] lemma bqALUnitSL_coe :
    (W.bqALUnitSL : Matrix (Fin 2) (Fin 2) ℤ) = !![(q : ℤ) * W.a, W.b; (W.R : ℤ), 1] := rfl

private lemma _root_.ModularForm.AtkinLehnerDatum.bqALUnitSL_mem : W.bqALUnitSL ∈ Gamma0 W.R := by
  rw [Gamma0_mem]
  show (((W.bqALUnitSL : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod W.R) = 0
  simp

p2m_export "ModularForm.AtkinLehnerDatum" "bqALUnitSL_mem"

private theorem _root_.ModularForm.AtkinLehnerDatum.diagMat_mul_mat :
    !![(q : ℤ), 0; 0, 1] * W.mat
      = !![(q : ℤ), 0; 0, (q : ℤ)] * (W.bqALUnitSL : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [mat, bqALUnitSL_coe, Matrix.mul_fin_two, Matrix.mul_fin_two]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp

p2m_export "ModularForm.AtkinLehnerDatum" "diagMat_mul_mat"

def translationSL (j : ℤ) : SL(2, ℤ) :=
  ⟨!![1, j; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp] lemma translationSL_coe (j : ℤ) :
    (translationSL j : Matrix (Fin 2) (Fin 2) ℤ) = !![1, j; 0, 1] := rfl

lemma translationSL_mem (j : ℤ) (N : ℕ) : translationSL j ∈ Gamma0 N := by
  rw [Gamma0_mem]
  show (((translationSL j : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0
  simp

theorem diagMat_mul_heckeRep (j : ℤ) :
    (!![(q : ℤ), 0; 0, 1] * !![1, j; 0, (q : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ)
      = !![(q : ℤ), 0; 0, (q : ℤ)] * (translationSL j : Matrix (Fin 2) (Fin 2) ℤ) := by
  rw [translationSL_coe, Matrix.mul_fin_two, Matrix.mul_fin_two]
  refine Matrix.ext fun i j' => ?_
  fin_cases i <;> fin_cases j' <;> simp

private lemma glLift_of_intMatrixEq {A B C D : Matrix (Fin 2) (Fin 2) ℤ}
    (h : A * B = C * D) :
    (A.map (algebraMap ℤ ℝ)) * (B.map (algebraMap ℤ ℝ))
      = (C.map (algebraMap ℤ ℝ)) * (D.map (algebraMap ℤ ℝ)) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
    ← RingHom.mapMatrix_apply, ← map_mul, ← map_mul, h]

private lemma mapGL_coe_eq' (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

private lemma heckeDiagMatrix_coe_eq (hq : q ≠ 0) :
    ((heckeDiagMatrix q : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := by
  rw [val_heckeDiagMatrix hq]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

private lemma heckeMatrix_coe_eq (hq : q ≠ 0) (j : ℕ) :
    ((heckeMatrix q j : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (!![1, (j : ℤ); 0, (q : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := by
  rw [val_heckeMatrix hq]
  refine Matrix.ext fun i j' => ?_
  fin_cases i <;> fin_cases j' <;> simp [Matrix.map_apply]

private lemma scalarGL_coe_eq (hq : 0 < q) :
    ((scalarGL hq : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (!![(q : ℤ), 0; 0, (q : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := by
  rw [scalarGL_coe]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

variable [NeZero M]

private lemma _root_.ModularForm.AtkinLehnerDatum.alGL_eq_lowerLeftSL_mul_heckeDiagMatrix :
    W.alGL = Matrix.SpecialLinearGroup.mapGL ℝ W.lowerLeftSL * heckeDiagMatrix q := by
  have hq : q ≠ 0 := W.q_pos.ne'
  apply Units.ext
  rw [Units.val_mul, alGL_coe, mapGL_coe_eq', heckeDiagMatrix_coe_eq hq,
    ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← map_mul,
    ← W.mat_eq_lowerLeftSL_mul_diagMat]

p2m_export "ModularForm.AtkinLehnerDatum" "alGL_eq_lowerLeftSL_mul_heckeDiagMatrix"

private lemma _root_.ModularForm.AtkinLehnerDatum.heckeDiagMatrix_mul_alGL :
    heckeDiagMatrix q * W.alGL
      = scalarGL W.q_pos * Matrix.SpecialLinearGroup.mapGL ℝ W.bqALUnitSL := by
  have hq : q ≠ 0 := W.q_pos.ne'
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, alGL_coe, heckeDiagMatrix_coe_eq hq, scalarGL_coe_eq,
    mapGL_coe_eq']
  exact glLift_of_intMatrixEq W.diagMat_mul_mat

p2m_export "ModularForm.AtkinLehnerDatum" "heckeDiagMatrix_mul_alGL"

private lemma _root_.ModularForm.AtkinLehnerDatum.heckeDiagMatrix_mul_heckeMatrix (j : ℕ) :
    heckeDiagMatrix q * heckeMatrix q j
      = scalarGL W.q_pos * Matrix.SpecialLinearGroup.mapGL ℝ (translationSL (j : ℤ)) := by
  have hq : q ≠ 0 := W.q_pos.ne'
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, heckeDiagMatrix_coe_eq hq, heckeMatrix_coe_eq hq,
    scalarGL_coe_eq, mapGL_coe_eq']
  exact glLift_of_intMatrixEq (diagMat_mul_heckeRep (j : ℤ))

p2m_export "ModularForm.AtkinLehnerDatum" "heckeDiagMatrix_mul_heckeMatrix"
end ModularForm.AtkinLehnerDatum
p2m_reactivate "P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.ModularForm P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.ModularForm.AtkinLehnerDatum"
p2m_reactivate "P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.ModularForm"

namespace ModularForm
p2m_export "ModularForm" "IsGLPos.coe_smul coe_smul slash_apply ext add_apply smul_apply atkinLehnerLin coe_atkinLehnerLin_apply AtkinLehnerDatum AtkinLehnerDatum.alGL alSlash alSlash_def heckeMatrix heckeDiagMatrix val_heckeMatrix val_heckeDiagMatrix heckeU heckeT heckeU_def heckeT_eq_heckeU_add heckeTLin coe_heckeTLin_apply"
p2m_open "ModularForm"

variable {M q : ℕ} (W : AtkinLehnerDatum M q) [NeZero M]

p2m_open "ModularForm.AtkinLehnerDatum P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.ModularForm.AtkinLehnerDatum"

lemma alSlash_eq_slash_heckeDiagMatrix_of_lowerLevel (k : ℤ) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 W.R : Subgroup (GL (Fin 2) ℝ)), SlashAction.map k γ f = f) :
    alSlash W k f = f ∣[k] heckeDiagMatrix q := by
  rw [alSlash_def, W.alGL_eq_lowerLeftSL_mul_heckeDiagMatrix, SlashAction.slash_mul]
  congr 1
  exact hf _ (Subgroup.mem_map.mpr ⟨W.lowerLeftSL, W.lowerLeftSL_mem, rfl⟩)

lemma alSlash_slash_heckeDiagMatrix_of_lowerLevel {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 W.R : Subgroup (GL (Fin 2) ℝ)), SlashAction.map (2 : ℤ) γ f = f) :
    alSlash W 2 (f ∣[(2 : ℤ)] heckeDiagMatrix q) = f := by
  rw [alSlash_def, ← SlashAction.slash_mul, W.heckeDiagMatrix_mul_alGL, SlashAction.slash_mul,
    slash_scalarGL]
  simp only [show ((2 : ℤ) - 2) = 0 by ring, zpow_zero, one_smul]
  exact hf _ (Subgroup.mem_map.mpr ⟨W.bqALUnitSL, W.bqALUnitSL_mem, rfl⟩)

lemma heckeU_slash_heckeDiagMatrix_of_lowerLevel {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 W.R : Subgroup (GL (Fin 2) ℝ)), SlashAction.map (2 : ℤ) γ f = f) :
    heckeU (2 : ℤ) q (f ∣[(2 : ℤ)] heckeDiagMatrix q) = (q : ℂ) • f := by
  rw [heckeU_def]
  have hterm : ∀ j ∈ Finset.range q,
      (f ∣[(2 : ℤ)] heckeDiagMatrix q) ∣[(2 : ℤ)] heckeMatrix q j = f := by
    intro j _
    rw [← SlashAction.slash_mul, W.heckeDiagMatrix_mul_heckeMatrix j, SlashAction.slash_mul,
      slash_scalarGL]
    simp only [show ((2 : ℤ) - 2) = 0 by ring, zpow_zero, one_smul]
    exact hf _ (Subgroup.mem_map.mpr ⟨translationSL (j : ℤ), translationSL_mem _ _, rfl⟩)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℂ]

theorem traceSlashClosed_of_lowerLevel {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 W.R : Subgroup (GL (Fin 2) ℝ)), SlashAction.map (2 : ℤ) γ f = f) :
    f + heckeU (2 : ℤ) q (alSlash W 2 f) = ((q : ℂ) + 1) • f := by
  rw [alSlash_eq_slash_heckeDiagMatrix_of_lowerLevel W 2 hf,
    heckeU_slash_heckeDiagMatrix_of_lowerLevel W hf]
  ext τ
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem traceSlashClosed_slash_heckeDiagMatrix_of_lowerLevel {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 W.R : Subgroup (GL (Fin 2) ℝ)), SlashAction.map (2 : ℤ) γ f = f) :
    (f ∣[(2 : ℤ)] heckeDiagMatrix q) + heckeU (2 : ℤ) q (alSlash W 2 (f ∣[(2 : ℤ)] heckeDiagMatrix q))
      = heckeT (2 : ℤ) q f := by
  rw [alSlash_slash_heckeDiagMatrix_of_lowerLevel W hf, heckeT_eq_heckeU_add, add_comm]

end ModularForm
p2m_reactivate "P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.ModularForm P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.ModularForm.AtkinLehnerDatum"

namespace ModularForm
p2m_export "ModularForm" "IsGLPos.coe_smul coe_smul slash_apply ext add_apply smul_apply atkinLehnerLin coe_atkinLehnerLin_apply AtkinLehnerDatum AtkinLehnerDatum.alGL alSlash alSlash_def heckeMatrix heckeDiagMatrix val_heckeMatrix val_heckeDiagMatrix heckeU heckeT heckeU_def heckeT_eq_heckeU_add heckeTLin coe_heckeTLin_apply"
p2m_open "ModularForm"

p2m_open "ModularForm.AtkinLehnerDatum P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.ModularForm.AtkinLehnerDatum"

variable {M q : ℕ} (W : AtkinLehnerDatum M q) [NeZero M]

theorem traceSlashClosed_alSlash_of_lowerLevel {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 W.R : Subgroup (GL (Fin 2) ℝ)), SlashAction.map (2 : ℤ) γ f = f) :
    (alSlash W 2 f) + heckeU (2 : ℤ) q (alSlash W 2 (alSlash W 2 f)) = heckeT (2 : ℤ) q f := by
  rw [alSlash_eq_slash_heckeDiagMatrix_of_lowerLevel W 2 hf]
  exact traceSlashClosed_slash_heckeDiagMatrix_of_lowerLevel W hf

theorem traceSlashClosed_alSlash_slash_heckeDiagMatrix_of_lowerLevel {f : ℍ → ℂ}
    (hf : ∀ γ ∈ (Gamma0 W.R : Subgroup (GL (Fin 2) ℝ)), SlashAction.map (2 : ℤ) γ f = f) :
    (alSlash W 2 (f ∣[(2 : ℤ)] heckeDiagMatrix q))
        + heckeU (2 : ℤ) q (alSlash W 2 (alSlash W 2 (f ∣[(2 : ℤ)] heckeDiagMatrix q)))
      = ((q : ℂ) + 1) • f := by
  rw [alSlash_slash_heckeDiagMatrix_of_lowerLevel W hf]
  exact traceSlashClosed_of_lowerLevel W hf

end ModularForm
p2m_reactivate "P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.ModularForm P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.ModularForm.AtkinLehnerDatum"

namespace ModularForm
p2m_export "ModularForm" "IsGLPos.coe_smul coe_smul slash_apply ext add_apply smul_apply atkinLehnerLin coe_atkinLehnerLin_apply AtkinLehnerDatum AtkinLehnerDatum.alGL alSlash alSlash_def heckeMatrix heckeDiagMatrix val_heckeMatrix val_heckeDiagMatrix heckeU heckeT heckeU_def heckeT_eq_heckeU_add heckeTLin coe_heckeTLin_apply"
namespace AtkinLehnerDatum
p2m_export "ModularForm.AtkinLehnerDatum" "q_pos mat alGL alGL_coe b bezout R a"
p2m_open "ModularForm.AtkinLehnerDatum ModularForm"

variable {M q : ℕ} (W : AtkinLehnerDatum M q)

private lemma _root_.ModularForm.AtkinLehnerDatum.not_dvd_R_impl (hq : 1 < q) : ¬ q ∣ W.R := by
  intro ⟨t, ht⟩
  have h : (q : ℤ) ∣ 1 := ⟨W.a - (t : ℤ) * W.b, by
    rw [← W.bezout, ht]; push_cast; ring⟩
  exact absurd (Int.eq_one_of_dvd_one (by exact_mod_cast q.zero_le) h)
    (by exact_mod_cast hq.ne')

p2m_export "ModularForm.AtkinLehnerDatum" "not_dvd_R_impl"
end ModularForm.AtkinLehnerDatum
p2m_reactivate "P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.ModularForm P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.ModularForm.AtkinLehnerDatum"
p2m_reactivate "P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.ModularForm P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.ModularForm.AtkinLehnerDatum"

namespace CuspForm
p2m_export "CuspForm" "IsGLPos.coe_smul smul_apply ext coe_smul add_apply atkinLehnerLin coe_atkinLehnerLin_apply traceLin coe_traceLin_apply heckeTLin coe_heckeTLin_apply"
p2m_open "CuspForm"

p2m_open "ModularForm P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.ModularForm ModularForm.AtkinLehnerDatum P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.ModularForm.AtkinLehnerDatum"

variable {M q : ℕ} (W : ModularForm.AtkinLehnerDatum M q) [NeZero M] (hq : q.Prime)

theorem traceLin_of_coe_eq_impl {f : CuspForm (Gamma0 W.R) 2}
    {g : CuspForm (Gamma0 M) 2} (hg : ⇑g = ⇑f) :
    traceLin W hq g = ((q : ℂ) + 1) • f := by
  refine DFunLike.coe_injective ?_
  simp only [coe_traceLin_apply, hg, CuspForm.IsGLPos.coe_smul]
  exact traceSlashClosed_of_lowerLevel W (SlashInvariantFormClass.slash_action_eq f)

theorem traceLin_of_coe_eq_slash_heckeDiagMatrix_impl {f : CuspForm (Gamma0 W.R) 2}
    {g : CuspForm (Gamma0 M) 2} (hg : ⇑g = (⇑f) ∣[(2 : ℤ)] heckeDiagMatrix q) :
    traceLin W hq g = heckeTLin (2 : ℤ) hq (W.not_dvd_R_impl hq.one_lt) f := by
  refine DFunLike.coe_injective ?_
  simp only [coe_traceLin_apply, hg, coe_heckeTLin_apply]
  exact traceSlashClosed_slash_heckeDiagMatrix_of_lowerLevel W
    (SlashInvariantFormClass.slash_action_eq f)

theorem traceLin_atkinLehnerLin_of_coe_eq_impl {f : CuspForm (Gamma0 W.R) 2}
    {g : CuspForm (Gamma0 M) 2} (hg : ⇑g = ⇑f) :
    traceLin W hq (atkinLehnerLin W 2 g) = heckeTLin (2 : ℤ) hq (W.not_dvd_R_impl hq.one_lt) f := by
  refine DFunLike.coe_injective ?_
  simp only [coe_traceLin_apply, coe_atkinLehnerLin_apply, hg, coe_heckeTLin_apply]
  exact traceSlashClosed_alSlash_of_lowerLevel W (SlashInvariantFormClass.slash_action_eq f)

theorem traceLin_atkinLehnerLin_of_coe_eq_slash_heckeDiagMatrix_impl {f : CuspForm (Gamma0 W.R) 2}
    {g : CuspForm (Gamma0 M) 2} (hg : ⇑g = (⇑f) ∣[(2 : ℤ)] heckeDiagMatrix q) :
    traceLin W hq (atkinLehnerLin W 2 g) = ((q : ℂ) + 1) • f := by
  refine DFunLike.coe_injective ?_
  simp only [coe_traceLin_apply, coe_atkinLehnerLin_apply, hg, CuspForm.IsGLPos.coe_smul]
  exact traceSlashClosed_alSlash_slash_heckeDiagMatrix_of_lowerLevel W
    (SlashInvariantFormClass.slash_action_eq f)

end CuspForm
p2m_reactivate "P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.ModularForm P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.ModularForm.AtkinLehnerDatum"

end
p2m_reactivate "P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.ModularForm P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.ModularForm.AtkinLehnerDatum"

p2m_open "CongruenceSubgroup CuspForm P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix.CuspForm ModularForm.CuspForm"

theorem solution {M q : ℕ} (W : ModularForm.AtkinLehnerDatum M q) [NeZero M]
    (hq : q.Prime) {f : CuspForm (Gamma0 W.R) 2} {g : CuspForm (Gamma0 M) 2}
    (hg : ⇑g = (⇑f) ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix q) :
    traceLin W hq g = heckeTLin (2 : ℤ) hq (W.not_dvd_R_impl hq.one_lt) f :=
  CuspForm.traceLin_of_coe_eq_slash_heckeDiagMatrix_impl W hq hg

#print axioms solution

end S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix
end P2MW
export P2MW.S_CuspForm_traceLin_of_coe_eq_slash_heckeDiagMatrix (solution)
