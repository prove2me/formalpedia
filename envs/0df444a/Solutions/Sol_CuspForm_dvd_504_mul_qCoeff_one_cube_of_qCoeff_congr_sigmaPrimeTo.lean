-- Prove2me | solution 1 for CuspForm.dvd_504_mul_qCoeff_one_cube_of_qCoeff_congr_sigmaPrimeTo
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/9b7394f9-c5e1-55f9-b9fa-4373ebc69eff

import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Theorems.Thm_CuspForm_exists_modularForm_qCoeff_eq_of_qCoeff_congr_sigmaPrimeTo
import Theorems.Thm_ModularForm_exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke
import Theorems.Thm_ModularForm_levelOne_weight_six_qCoeff_one
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_dvd_504_mul_qCoeff_one_cube_of_qCoeff_congr_sigmaPrimeTo
set_option autoImplicit false
set_option Elab.async false
open ModularCurve
open scoped ModularForm MatrixGroups

namespace S09WFP2

private def datum (p : ℕ) : ModularForm.AtkinLehnerDatum p p := ⟨1, (mul_one p).symm, 0, -1, by simp⟩

private def gamma0Elt (p : ℕ) : SL(2, ℤ) := ⟨!![1, 0; (p : ℤ), 1], by simp [Matrix.det_fin_two_of]⟩

private theorem gamma0Elt_mem (p : ℕ) : gamma0Elt p ∈ CongruenceSubgroup.Gamma0 p := by
  rw [CongruenceSubgroup.Gamma0_mem]
  simp [gamma0Elt]

private noncomputable def fricke (p : ℕ) [NeZero p] : Matrix.GeneralLinearGroup (Fin 2) ℝ :=
  Matrix.SpecialLinearGroup.mapGL ℝ (gamma0Elt p) * (datum p).alGL

private theorem fricke_coe (p : ℕ) [NeZero p] :
    ((fricke p : Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = !![0, -1; (p : ℝ), 0] := by
  rw [fricke, Units.val_mul, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    ModularForm.AtkinLehnerDatum.alGL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gamma0Elt, datum, ModularForm.AtkinLehnerDatum.mat, Matrix.mul_apply, Fin.sum_univ_two]

private theorem abs_det_fricke (p : ℕ) [NeZero p] : |(((fricke p).det : ℝˣ) : ℝ)| = (p : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, fricke_coe, Matrix.det_fin_two_of]
  simp

private theorem slash_fricke (p : ℕ) [NeZero p] {k : ℤ}
    (X : ModularForm (CongruenceSubgroup.Gamma0 p) k) :
    (X : UpperHalfPlane → ℂ) ∣[k] fricke p = ModularForm.alSlash (datum p) k X := by
  rw [fricke, SlashAction.slash_mul,
    SlashInvariantForm.slash_action_eqn X _ (Subgroup.mem_map_of_mem _ (gamma0Elt_mem p))]
  rfl

private theorem one_mem_strictPeriods (p : ℕ) :
    (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 p : Subgroup SL(2, ℤ)) :
      Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples 1

private theorem slash_cube (p : ℕ) [NeZero p] (F G : ModularForm (CongruenceSubgroup.Gamma0 p) 2)
    (hFW : (F : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] fricke p = G)
    (hGW : (G : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] fricke p = F) :
    ((F : UpperHalfPlane → ℂ) * F * G) ∣[((2 : ℤ) + 2) + 2] fricke p
      = (p : ℂ) ^ 2 • ((F : UpperHalfPlane → ℂ) * G * G) := by
  rw [ModularForm.mul_slash, ModularForm.mul_slash, hFW, hGW, abs_det_fricke]
  funext τ
  simp
  ring

private theorem qCoeff_mul {p : ℕ} {a b : ℤ} (A : ModularForm (CongruenceSubgroup.Gamma0 p) a)
    (B : ModularForm (CongruenceSubgroup.Gamma0 p) b) (n : ℕ) :
    ModularFormClass.qCoeff (A.mul B) n
      = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          ModularFormClass.qCoeff A ij.1 * ModularFormClass.qCoeff B ij.2 := by
  unfold ModularFormClass.qCoeff
  rw [ModularForm.qExpansion_mul one_pos (one_mem_strictPeriods p) A B, PowerSeries.coeff_mul]

private theorem qCoeff_neg {p : ℕ} {a : ℤ} (A : ModularForm (CongruenceSubgroup.Gamma0 p) a) (n : ℕ) :
    ModularFormClass.qCoeff (-(A : UpperHalfPlane → ℂ)) n = -ModularFormClass.qCoeff A n := by
  unfold ModularFormClass.qCoeff
  rw [ModularForm.qExpansion_neg one_pos (one_mem_strictPeriods p) A]
  simp

private theorem qCoeff_smul {p : ℕ} {a : ℤ} (c : ℂ) (A : ModularForm (CongruenceSubgroup.Gamma0 p) a)
    (n : ℕ) :
    ModularFormClass.qCoeff (c • (A : UpperHalfPlane → ℂ)) n = c * ModularFormClass.qCoeff A n := by
  unfold ModularFormClass.qCoeff
  rw [ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods p) c A]
  simp

private theorem qCoeff_levelOne_sub_smul {p : ℕ} {k : ℤ} (Y : ModularForm 𝒮ℒ k) (c : ℂ)
    (X : ModularForm (CongruenceSubgroup.Gamma0 p) k) (n : ℕ) :
    ModularFormClass.qCoeff ((Y : UpperHalfPlane → ℂ) - c • (X : UpperHalfPlane → ℂ)) n
      = ModularFormClass.qCoeff Y n - c * ModularFormClass.qCoeff X n := by
  have hY : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (Y : UpperHalfPlane → ℂ)) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero Y one_pos one_mem_strictPeriods_SL
  have hX : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (c • (X : UpperHalfPlane → ℂ))) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero (c • X) one_pos (one_mem_strictPeriods p)
  unfold ModularFormClass.qCoeff
  rw [UpperHalfPlane.qExpansion_sub hY hX, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods p) c X]
  simp

private theorem dvd_antidiagonal_sum (N : ℤ) {a b : ℕ → ℤ} (ha : ∀ i, i ≠ 0 → N ∣ a i)
    (hb : ∀ j, j ≠ 0 → N ∣ b j) {n : ℕ} (hn : n ≠ 0) :
    N ∣ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, a ij.1 * b ij.2 := by
  refine Finset.dvd_sum fun ij hij => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  rcases eq_or_ne ij.1 0 with h1 | h1
  · have h2 : ij.2 ≠ 0 := fun h2 => hn (by rw [← hij, h1, h2])
    exact Dvd.dvd.mul_left (hb _ h2) _
  · exact Dvd.dvd.mul_right (ha _ h1) _

private theorem cast_sum_antidiagonal {a b : ℕ → ℤ} {ca cb : ℕ → ℂ} (ha : ∀ i, (a i : ℂ) = ca i)
    (hb : ∀ j, (b j : ℂ) = cb j) (n : ℕ) :
    ((∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, a ij.1 * b ij.2 : ℤ) : ℂ)
      = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, ca ij.1 * cb ij.2 := by
  push_cast
  exact Finset.sum_congr rfl fun ij _ => by rw [ha, hb]

private theorem exists_coeffs_mul {p : ℕ} (N : ℤ) {a b : ℤ}
    (A : ModularForm (CongruenceSubgroup.Gamma0 p) a) (B : ModularForm (CongruenceSubgroup.Gamma0 p) b)
    {x y : ℕ → ℤ} (hx : ∀ n, (x n : ℂ) = ModularFormClass.qCoeff A n)
    (hy : ∀ n, (y n : ℂ) = ModularFormClass.qCoeff B n)
    (hxd : ∀ n, n ≠ 0 → N ∣ x n) (hyd : ∀ n, n ≠ 0 → N ∣ y n) :
    ∃ z : ℕ → ℤ, (∀ n, (z n : ℂ) = ModularFormClass.qCoeff (A.mul B) n) ∧ z 0 = x 0 * y 0 ∧
      ∀ n, n ≠ 0 → N ∣ z n :=
  ⟨fun n => ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, x ij.1 * y ij.2,
    fun n => by rw [qCoeff_mul]; exact cast_sum_antidiagonal hx hy n,
    by simp,
    fun n hn => dvd_antidiagonal_sum N hxd hyd hn⟩

private theorem negp_ne (p : ℕ) [NeZero p] : -(p : ℝ) ≠ 0 :=
  neg_ne_zero.mpr (by exact_mod_cast NeZero.ne p)

private theorem fricke_mul_fricke (p : ℕ) [NeZero p] :
    fricke p * fricke p
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (-(p : ℝ)) (negp_ne p)) := by
  apply Units.ext
  rw [Units.val_mul, fricke_coe,
    show ((Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (-(p : ℝ)) (negp_ne p)) :
        Matrix.GeneralLinearGroup (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = Matrix.scalar (Fin 2) (-(p : ℝ)) from rfl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar_apply]

private theorem slash_scalar_two (c : ℝˣ) (g : UpperHalfPlane → ℂ) :
    g ∣[(2 : ℤ)] (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = g := by
  ext τ
  have hdet : ((Matrix.GeneralLinearGroup.scalar (Fin 2) c).det.val : ℝ) = (c : ℝ) ^ 2 := by
    rw [Matrix.GeneralLinearGroup.det_scalar]
    simp [Fintype.card_fin]
  have hpos : 0 < ((Matrix.GeneralLinearGroup.scalar (Fin 2) c).det.val : ℝ) := by
    rw [hdet]
    exact pow_two_pos_of_ne_zero c.ne_zero
  have hc : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr c.ne_zero
  rw [ModularForm.slash_apply, UpperHalfPlane.σ, if_pos hpos, hdet,
    UpperHalfPlane.glScalar_smul, UpperHalfPlane.denom_scalar,
    abs_of_nonneg (sq_nonneg (c : ℝ))]
  simp only [ContinuousAlgEquiv.refl_apply]
  have : (((c : ℝ) ^ 2 : ℝ) : ℂ) * ((c : ℝ) : ℂ) ^ (-(2 : ℤ)) = 1 := by
    push_cast
    rw [← zpow_natCast (((c : ℝ) : ℂ)) 2, ← zpow_add₀ hc]
    norm_num
  rw [show (2 : ℤ) - 1 = 1 by norm_num, zpow_one, mul_assoc, this, mul_one]

private theorem exists_fricke_pair (p : ℕ) [NeZero p] (F : ModularForm (CongruenceSubgroup.Gamma0 p) 2) :
    ∃ G : ModularForm (CongruenceSubgroup.Gamma0 p) 2,
      (F : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] fricke p = G ∧ (G : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] fricke p = F := by
  have hFW : (F : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] fricke p = ModularForm.atkinLehnerLin (datum p) 2 F := by
    rw [slash_fricke, ModularForm.coe_atkinLehnerLin_apply]
  refine ⟨ModularForm.atkinLehnerLin (datum p) 2 F, hFW, ?_⟩
  rw [← hFW, ← SlashAction.slash_mul, fricke_mul_fricke, slash_scalar_two]

private theorem heckeU_eq_neg (p : ℕ) [Fact p.Prime] [NeZero p]
    (F G : ModularForm (CongruenceSubgroup.Gamma0 p) 2)
    (hGW : (G : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] fricke p = F) :
    ModularForm.heckeU 2 p (F : UpperHalfPlane → ℂ) = -(G : UpperHalfPlane → ℂ) := by
  obtain ⟨Y₂, hY₂⟩ :=
    ModularForm.exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke p 2 G (fricke p) (fricke_coe p)
  have h0 : Y₂ = 0 := rank_zero_iff_forall_zero.mp ModularForm.levelOne_weight_two_rank_zero Y₂
  rw [h0, ModularForm.coe_zero, hGW] at hY₂
  simp only [sub_self, zpow_zero, one_smul] at hY₂
  exact eq_neg_of_add_eq_zero_right hY₂.symm

private theorem qCoeff_fricke (p : ℕ) (hp0 : p ≠ 0) (F G : ModularForm (CongruenceSubgroup.Gamma0 p) 2)
    (hU : ModularForm.heckeU 2 p (F : UpperHalfPlane → ℂ) = -(G : UpperHalfPlane → ℂ))
    (aF : ℕ → ℤ) (hF : ∀ n : ℕ, (aF n : ℂ) = ModularFormClass.qCoeff F n) (n : ℕ) :
    ((-aF (n * p) : ℤ) : ℂ) = ModularFormClass.qCoeff G n := by
  have h1 := ModularFormClass.qCoeff_heckeU F (one_mem_strictPeriods p) hp0 n
  rw [hU, ModularForm.coeffHeckeU_apply, qCoeff_neg G n] at h1
  push_cast
  rw [hF (n * p), ← h1, neg_neg]

private theorem exists_cube (p : ℕ) (F G : ModularForm (CongruenceSubgroup.Gamma0 p) 2) :
    ∃ K : ModularForm (CongruenceSubgroup.Gamma0 p) 6,
      (K : UpperHalfPlane → ℂ) = (F : UpperHalfPlane → ℂ) * F * G ∧
      ∀ n, ModularFormClass.qCoeff K n = ModularFormClass.qCoeff ((F.mul F).mul G) n :=
  ⟨ModularForm.mcast (by norm_num) ((F.mul F).mul G), rfl, fun _ => rfl⟩

private theorem exists_scaled_cube (p : ℕ) (F G : ModularForm (CongruenceSubgroup.Gamma0 p) 2) :
    ∃ L' : ModularForm (CongruenceSubgroup.Gamma0 p) 6,
      (L' : UpperHalfPlane → ℂ) = (p : ℂ) ^ 2 • ((F : UpperHalfPlane → ℂ) * G * G) ∧
      ∀ n, ModularFormClass.qCoeff L' n = (p : ℂ) ^ 2 * ModularFormClass.qCoeff ((F.mul G).mul G) n := by
  refine ⟨(p : ℂ) ^ 2 • ModularForm.mcast (by norm_num) ((F.mul G).mul G), rfl, fun n => ?_⟩
  exact qCoeff_smul ((p : ℂ) ^ 2) (ModularForm.mcast (by norm_num) ((F.mul G).mul G)) n

private theorem zpow_six_sub_two (p : ℕ) : (p : ℂ) ^ ((6 : ℤ) - 2) = (p : ℂ) ^ 2 * (p : ℂ) ^ 2 := by
  rw [show ((6 : ℤ) - 2) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast]
  ring

private theorem exists_levelOne_six (p : ℕ) [Fact p.Prime] [NeZero p] (hp0 : p ≠ 0)
    (F G : ModularForm (CongruenceSubgroup.Gamma0 p) 2)
    (hFW : (F : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] fricke p = G)
    (hGW : (G : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] fricke p = F) :
    ∃ Y : ModularForm 𝒮ℒ 6, ∀ n : ℕ, ModularFormClass.qCoeff Y n
      = (p : ℂ) ^ 2 * ((p : ℂ) ^ 2 * ModularFormClass.qCoeff ((F.mul F).mul G) n
          + ModularFormClass.qCoeff ((F.mul G).mul G) (n * p)) := by
  obtain ⟨K, hKc, hKq⟩ := exists_cube p F G
  obtain ⟨L', hLc, hLq⟩ := exists_scaled_cube p F G
  have hKW : (K : UpperHalfPlane → ℂ) ∣[(6 : ℤ)] fricke p = L' := by
    rw [hKc, hLc]
    exact slash_cube p F G hFW hGW
  obtain ⟨Y, hY⟩ :=
    ModularForm.exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke p 6 K (fricke p) (fricke_coe p)
  rw [hKW] at hY
  refine ⟨Y, fun n => ?_⟩
  have hH : ModularForm.heckeU 6 p (L' : UpperHalfPlane → ℂ)
      = (Y : UpperHalfPlane → ℂ) - (p : ℂ) ^ ((6 : ℤ) - 2) • (K : UpperHalfPlane → ℂ) := by
    rw [hY]
    abel
  have h1 := ModularFormClass.qCoeff_heckeU L' (one_mem_strictPeriods p) hp0 n
  rw [hH, ModularForm.coeffHeckeU_apply, qCoeff_levelOne_sub_smul, hLq, hKq, zpow_six_sub_two] at h1
  linear_combination h1

private theorem endgame (p : ℕ) (hp0 : p ≠ 0) (N c : ℤ) (Y : ModularForm 𝒮ℒ 6) (bK bL : ℕ → ℤ)
    (hbK0 : bK 0 = c * c * -c) (hbL0 : bL 0 = c * -c * -c)
    (hY0 : ModularFormClass.qCoeff Y 0 = (((p : ℤ) ^ 2 * ((p : ℤ) ^ 2 * bK 0 + bL 0) : ℤ) : ℂ))
    (hY1 : ModularFormClass.qCoeff Y 1 = (((p : ℤ) ^ 2 * ((p : ℤ) ^ 2 * bK 1 + bL p) : ℤ) : ℂ))
    (hdvd : N ∣ (p : ℤ) ^ 2 * bK 1 + bL p) :
    N ∣ 504 * c ^ 3 * ((p : ℤ) ^ 2 - 1) := by
  have h6 := ModularForm.levelOne_weight_six_qCoeff_one Y
  rw [hY1, hY0] at h6
  have h7 : (p : ℤ) ^ 2 * ((p : ℤ) ^ 2 * bK 1 + bL p)
      = -504 * ((p : ℤ) ^ 2 * ((p : ℤ) ^ 2 * bK 0 + bL 0)) := by
    exact_mod_cast h6
  have hp2 : ((p : ℤ)) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hp0)
  have h8 : (p : ℤ) ^ 2 * bK 1 + bL p = -504 * ((p : ℤ) ^ 2 * bK 0 + bL 0) :=
    mul_left_cancel₀ hp2 (by linear_combination h7)
  have hkey : 504 * c ^ 3 * ((p : ℤ) ^ 2 - 1) = (p : ℤ) ^ 2 * bK 1 + bL p := by
    rw [h8, hbK0, hbL0]
    ring
  rw [hkey]
  exact hdvd

end S09WFP2

namespace CuspForm p2m_export "CuspForm" "coe_zero mcast ext atkinLehnerLin coe_atkinLehnerLin_apply exists_modularForm_qCoeff_eq_of_qCoeff_congr_sigmaPrimeTo" end CuspForm
p2m_open_scoped "CuspForm" in
open S09WFP2 in
private theorem CuspForm.dvd_504_mul_qCoeff_one_cube_of_qCoeff_congr_sigmaPrimeTo (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m) (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2) (af : ℕ → ℤ) (haf : ∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n) (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1) : (24 * m : ℤ) ∣ 504 * (af 1) ^ 3 * ((p : ℤ) - 1) ^ 3 * ((p : ℤ) ^ 2 - 1) := by
  have _ := hm
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hp0 : p ≠ 0 := NeZero.ne p
  obtain ⟨F, aF, hF, hF0, hFdvd⟩ :=
    CuspForm.exists_modularForm_qCoeff_eq_of_qCoeff_congr_sigmaPrimeTo p m f af haf hcongr
  obtain ⟨G, hFW, hGW⟩ := exists_fricke_pair p F
  have hU := heckeU_eq_neg p F G hGW

  obtain ⟨bG, hbG, hbG0, hbGdvd⟩ : ∃ b : ℕ → ℤ, (∀ n, (b n : ℂ) = ModularFormClass.qCoeff G n) ∧
      b 0 = -aF 0 ∧ ∀ n, n ≠ 0 → ((24 * m : ℕ) : ℤ) ∣ b n :=
    ⟨fun n => -aF (n * p), qCoeff_fricke p hp0 F G hU aF hF, by simp,
      fun n hn => dvd_neg.mpr (hFdvd _ (mul_ne_zero hn hp0))⟩
  obtain ⟨bFF, hbFF, hbFF0, hbFFdvd⟩ := exists_coeffs_mul ((24 * m : ℕ) : ℤ) F F hF hF hFdvd hFdvd
  obtain ⟨bK, hbK, hbK0, hbKdvd⟩ :=
    exists_coeffs_mul ((24 * m : ℕ) : ℤ) (F.mul F) G hbFF hbG hbFFdvd hbGdvd
  obtain ⟨bFG, hbFG, hbFG0, hbFGdvd⟩ := exists_coeffs_mul ((24 * m : ℕ) : ℤ) F G hF hbG hFdvd hbGdvd
  obtain ⟨bL, hbL, hbL0, hbLdvd⟩ :=
    exists_coeffs_mul ((24 * m : ℕ) : ℤ) (F.mul G) G hbFG hbG hbFGdvd hbGdvd

  obtain ⟨Y, hYn⟩ := exists_levelOne_six p hp0 F G hFW hGW
  have hY0 : ModularFormClass.qCoeff Y 0
      = (((p : ℤ) ^ 2 * ((p : ℤ) ^ 2 * bK 0 + bL 0) : ℤ) : ℂ) := by
    rw [hYn 0, zero_mul, ← hbK 0, ← hbL 0]
    push_cast
    ring
  have hY1 : ModularFormClass.qCoeff Y 1
      = (((p : ℤ) ^ 2 * ((p : ℤ) ^ 2 * bK 1 + bL p) : ℤ) : ℂ) := by
    rw [hYn 1, one_mul, ← hbK 1, ← hbL p]
    push_cast
    ring
  have hdvd : ((24 * m : ℕ) : ℤ) ∣ (p : ℤ) ^ 2 * bK 1 + bL p :=
    dvd_add (Dvd.dvd.mul_left (hbKdvd 1 one_ne_zero) _) (hbLdvd p hp0)
  have hend := endgame p hp0 ((24 * m : ℕ) : ℤ) (aF 0) Y bK bL
    (by rw [hbK0, hbFF0, hbG0]) (by rw [hbL0, hbFG0, hbG0]) hY0 hY1 hdvd
  have hN : ((24 * m : ℕ) : ℤ) = 24 * (m : ℤ) := by push_cast; ring
  have hkey : 504 * (af 1) ^ 3 * ((p : ℤ) - 1) ^ 3 * ((p : ℤ) ^ 2 - 1)
      = 504 * (aF 0) ^ 3 * ((p : ℤ) ^ 2 - 1) := by
    rw [hF0]
    ring
  rw [← hN, hkey]
  exact hend

theorem solution (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m) (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2) (af : ℕ → ℤ) (haf : ∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n) (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1) : (24 * m : ℤ) ∣ 504 * (af 1) ^ 3 * ((p : ℤ) - 1) ^ 3 * ((p : ℤ) ^ 2 - 1) :=
  CuspForm.dvd_504_mul_qCoeff_one_cube_of_qCoeff_congr_sigmaPrimeTo p m hm f af haf hcongr

end S_CuspForm_dvd_504_mul_qCoeff_one_cube_of_qCoeff_congr_sigmaPrimeTo
end P2MW
export P2MW.S_CuspForm_dvd_504_mul_qCoeff_one_cube_of_qCoeff_congr_sigmaPrimeTo (solution)
