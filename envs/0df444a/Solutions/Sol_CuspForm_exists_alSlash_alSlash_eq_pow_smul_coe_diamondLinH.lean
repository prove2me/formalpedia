-- Prove2me | solution 1 for CuspForm.exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/54507a29-e479-58a5-a5f2-1a38fc6198a5

import Mathlib
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Theorems.Thm_CuspForm_stableD
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH

set_option autoImplicit false

open Matrix UpperHalfPlane CongruenceSubgroup
p2m_open_scoped "MatrixGroups ModularForm P2MW.S_CuspForm_exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH.ModularForm Manifold"

noncomputable section

namespace ModularForm
p2m_export "ModularForm" "smul_slash slash_apply ext smul_apply AtkinLehnerDatum AtkinLehnerDatum.mat AtkinLehnerDatum.det_mat AtkinLehnerDatum.alGL_coe alSlash"
p2m_open "ModularForm"

namespace W2HAux

p2m_open "ModularForm.AtkinLehnerDatum"

variable {M q : ℕ} (W : AtkinLehnerDatum M q)

lemma mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

lemma map_int_mul_eq (A P : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * P).map (algebraMap ℤ ℝ) = A.map (algebraMap ℤ ℝ) * P.map (algebraMap ℤ ℝ) := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_mul]

variable (q) in

def scalarGL (hq : 0 < q) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℝ), 0; 0, (q : ℝ)] (by
    rw [Matrix.det_fin_two_of]
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    simpa using mul_ne_zero hq' hq')

@[scoped simp] lemma scalarGL_coe (hq : 0 < q) :
    (scalarGL q hq : Matrix (Fin 2) (Fin 2) ℝ) = !![(q : ℝ), 0; 0, (q : ℝ)] := rfl

lemma val_det_scalarGL (hq : 0 < q) : ((scalarGL q hq).det : ℝ) = (q : ℝ) ^ 2 := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, scalarGL_coe, Matrix.det_fin_two_of]
  ring

lemma denom_scalarGL (hq : 0 < q) (z : ℂ) : denom (scalarGL q hq) z = (q : ℝ) := by
  simp [UpperHalfPlane.denom, scalarGL_coe]

lemma num_scalarGL (hq : 0 < q) (z : ℂ) : num (scalarGL q hq) z = (q : ℝ) * z := by
  simp [UpperHalfPlane.num, scalarGL_coe]

lemma det_scalarGL_pos (hq : 0 < q) : 0 < ((scalarGL q hq).det : ℝ) := by
  rw [val_det_scalarGL]
  have : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  positivity

lemma scalarGL_smul (hq : 0 < q) (τ : ℍ) : scalarGL q hq • τ = τ := by
  have hqC : ((q : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by exact_mod_cast hq.ne' : ((q : ℝ)) ≠ 0)
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (det_scalarGL_pos hq), num_scalarGL, denom_scalarGL,
    mul_comm, mul_div_assoc, div_self hqC, mul_one]

lemma slash_scalarGL (k : ℤ) (hq : 0 < q) (f : ℍ → ℂ) :
    f ∣[k] scalarGL q hq = ((q : ℂ) ^ (k - 2)) • f := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  ext τ
  rw [ModularForm.slash_apply, Pi.smul_apply, smul_eq_mul]
  have hσ : σ (scalarGL q hq) (f (scalarGL q hq • τ)) = f (scalarGL q hq • τ) := by
    rw [UpperHalfPlane.σ, if_pos (det_scalarGL_pos hq)]
    rfl
  rw [hσ, scalarGL_smul, val_det_scalarGL, denom_scalarGL,
    abs_of_pos (by positivity : (0 : ℝ) < (q : ℝ) ^ 2)]

  have h1 : (((q : ℝ) ^ 2 : ℝ) : ℂ) = (q : ℂ) ^ (2 : ℕ) := by push_cast; ring
  have h2 : (((q : ℝ) : ℝ) : ℂ) = (q : ℂ) := by push_cast; ring
  rw [h1, h2, ← _root_.zpow_natCast ((q : ℂ)) 2, ← _root_.zpow_mul, mul_assoc, ← zpow_add₀ hqC]
  rw [show (2 : ℕ) * (k - 1) + -k = k - 2 by push_cast; ring]
  ring

variable (W' : AtkinLehnerDatum M q)

def sqUnit₂ : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(q : ℤ) * W'.a * W.a + W'.b * (W.R : ℤ), W'.a * W.b + W'.b;
     (q : ℤ) * ((W'.R : ℤ) * W.a + (W.R : ℤ)), (W'.R : ℤ) * W.b + (q : ℤ)]

theorem mat_mul_mat : W'.mat * W.mat = (q : ℤ) • sqUnit₂ W W' := by
  rw [AtkinLehnerDatum.mat, AtkinLehnerDatum.mat, sqUnit₂, Matrix.mul_fin_two]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem det_sqUnit₂ [NeZero M] : (sqUnit₂ W W').det = 1 := by
  have h := congrArg Matrix.det (mat_mul_mat W W')
  rw [Matrix.det_mul, AtkinLehnerDatum.det_mat, AtkinLehnerDatum.det_mat, Matrix.det_smul, Fintype.card_fin] at h
  have hq : ((q : ℤ)) ^ 2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast W.q_pos.ne')
  have : (q : ℤ) ^ 2 * (sqUnit₂ W W').det = (q : ℤ) ^ 2 * 1 := by rw [mul_one, ← h]; ring
  exact mul_left_cancel₀ hq this

def sqUnit₂SL [NeZero M] : SL(2, ℤ) := ⟨sqUnit₂ W W', det_sqUnit₂ W W'⟩

lemma sqUnit₂SL_coe [NeZero M] : ((sqUnit₂SL W W' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = sqUnit₂ W W' := rfl

lemma sqUnit₂SL_mem [NeZero M] : sqUnit₂SL W W' ∈ Gamma0 M := by
  rw [Gamma0_mem]
  show ((((sqUnit₂ W W') 1 0 : ℤ)) : ZMod M) = 0
  have h : (sqUnit₂ W W') 1 0 = (M : ℤ) * (W.a + 1) := by
    have h1 : (sqUnit₂ W W') 1 0 = (q : ℤ) * ((W'.R : ℤ) * W.a + (W.R : ℤ)) := by rw [sqUnit₂]; simp
    rw [h1, mul_add, ← mul_assoc, ← W'.hM_int, ← W.hM_int]; ring
  rw [h]
  push_cast
  simp

lemma alGL_mul_alGL₂ [NeZero M] :
    W'.alGL * W.alGL = scalarGL q W.q_pos * Matrix.SpecialLinearGroup.mapGL ℝ (sqUnit₂SL W W') := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show (W'.alGL : Matrix (Fin 2) (Fin 2) ℝ) * (W.alGL : Matrix (Fin 2) (Fin 2) ℝ)
      = (scalarGL q W.q_pos : Matrix (Fin 2) (Fin 2) ℝ) *
        ((Matrix.SpecialLinearGroup.mapGL ℝ (sqUnit₂SL W W') : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  rw [AtkinLehnerDatum.alGL_coe, AtkinLehnerDatum.alGL_coe, scalarGL_coe, mapGL_coe_eq, sqUnit₂SL_coe, ← map_int_mul_eq,
    mat_mul_mat]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.natCast_apply]

end W2HAux
p2m_reactivate "P2MW.S_CuspForm_exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH.ModularForm.W2HAux"

end ModularForm
p2m_reactivate "P2MW.S_CuspForm_exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH.ModularForm.W2HAux P2MW.S_CuspForm_exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH.ModularForm"

open _root_.ModularForm _root_.P2MW.S_CuspForm_exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH.ModularForm ModularForm.W2HAux in
theorem solution
    (M : ℕ) [NeZero M] (p : ℕ) [Fact p.Prime] (hpM : p ∣ M) (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W W' : ModularForm.AtkinLehnerDatum M p) (k : ℤ) (f : CuspForm (CohCarrier.GammaH M H) k) :
    ∃ δ : (ZMod M)ˣ, ModularForm.alSlash W k (ModularForm.alSlash W' k ⇑f) =
      ((p : ℂ) ^ (k - 2)) • (⇑(CuspForm.diamondLinH k δ f) : UpperHalfPlane → ℂ) := by
  set u : Gamma0 M := ⟨sqUnit₂SL W W', sqUnit₂SL_mem W W'⟩ with hu
  refine ⟨CohCarrier.gamma0Units M u, ?_⟩
  set d : (ZMod M)ˣ := CohCarrier.gamma0Units M u with hd

  have hmem : (u : SL(2, ℤ)) * ((CuspForm.gammaLift M d : Gamma0 M) : SL(2, ℤ))⁻¹ ∈ CohCarrier.GammaH M H := by
    refine CohCarrier.mem_GammaH_iff.mpr ⟨(Gamma0 M).mul_mem u.2 ((Gamma0 M).inv_mem (CuspForm.gammaLift M d).2), ?_⟩
    have : CohCarrier.gamma0Units M ⟨(u : SL(2, ℤ)) * ((CuspForm.gammaLift M d : Gamma0 M) : SL(2, ℤ))⁻¹,
        (Gamma0 M).mul_mem u.2 ((Gamma0 M).inv_mem (CuspForm.gammaLift M d).2)⟩ =
        CohCarrier.gamma0Units M u * (CohCarrier.gamma0Units M (CuspForm.gammaLift M d))⁻¹ := by
      rw [← map_inv, ← map_mul]; rfl
    rw [this, CuspForm.gamma0Units_gammaLift, ← hd, mul_inv_cancel]
    exact one_mem H
  have hfu : (⇑f : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (sqUnit₂SL W W')) =
      (⇑(CuspForm.diamondLinH k d f) : UpperHalfPlane → ℂ) := by
    rw [CuspForm.coe_diamondLinH_apply k (CuspForm.stableD M H k) d f]
    have hinv := SlashInvariantFormClass.slash_action_eq f
      (Matrix.SpecialLinearGroup.mapGL ℝ ((u : SL(2, ℤ)) * ((CuspForm.gammaLift M d : Gamma0 M) : SL(2, ℤ))⁻¹))
      (Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩)
    calc (⇑f : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (sqUnit₂SL W W'))
        = (⇑f) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ
            (((u : SL(2, ℤ)) * ((CuspForm.gammaLift M d : Gamma0 M) : SL(2, ℤ))⁻¹) *
              ((CuspForm.gammaLift M d : Gamma0 M) : SL(2, ℤ)))) := by
          rw [inv_mul_cancel_right]
      _ = ((⇑f) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ((u : SL(2, ℤ)) * ((CuspForm.gammaLift M d : Gamma0 M) : SL(2, ℤ))⁻¹)))
            ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ((CuspForm.gammaLift M d : Gamma0 M) : SL(2, ℤ))) := by
          rw [map_mul, SlashAction.slash_mul]
      _ = (⇑f) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ ((CuspForm.gammaLift M d : Gamma0 M) : SL(2, ℤ))) := by
          rw [hinv]
  calc alSlash W k (alSlash W' k (⇑f))
      = (⇑f) ∣[k] (W'.alGL * W.alGL) := by
        rw [alSlash, alSlash, SlashAction.slash_mul]
    _ = ((⇑f) ∣[k] scalarGL p W.q_pos) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (sqUnit₂SL W W')) := by
        rw [alGL_mul_alGL₂, SlashAction.slash_mul]
    _ = (((p : ℂ) ^ (k - 2)) • (⇑f : UpperHalfPlane → ℂ)) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (sqUnit₂SL W W')) := by
        rw [slash_scalarGL]
    _ = ((p : ℂ) ^ (k - 2)) • ((⇑f) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (sqUnit₂SL W W'))) := by
        rw [ModularForm.smul_slash]
        congr 1
        rw [UpperHalfPlane.σ, if_pos]
        · rfl
        · simp
    _ = ((p : ℂ) ^ (k - 2)) • (⇑(CuspForm.diamondLinH k d f) : UpperHalfPlane → ℂ) := by rw [hfu]

end
p2m_reactivate "P2MW.S_CuspForm_exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH.ModularForm.W2HAux P2MW.S_CuspForm_exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH.ModularForm"

end S_CuspForm_exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH
end P2MW
export P2MW.S_CuspForm_exists_alSlash_alSlash_eq_pow_smul_coe_diamondLinH (solution)
