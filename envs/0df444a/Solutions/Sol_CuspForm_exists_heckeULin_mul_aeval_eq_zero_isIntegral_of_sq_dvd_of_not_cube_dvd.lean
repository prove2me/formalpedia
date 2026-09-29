-- Prove2me | solution 1 for CuspForm.exists_heckeULin_mul_aeval_eq_zero_isIntegral_of_sq_dvd_of_not_cube_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/ed78cf9b-060a-5d1d-a88e-ee01529e4db1

import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_span_rescaleLin_isNewform_eq_top
import Theorems.Thm_CuspForm_qCoeff_eq_zero_of_isNewform_of_sq_dvd
import Theorems.Thm_CuspForm_qCoeff_sq_eq_one_of_isNewform
import Theorems.Thm_CuspForm_finiteDimensional_Gamma0
import Theorems.Thm_CuspForm_forall_exists_qCoeff_eq_of_isNormalizedEigenform
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Theorems.Thm_CuspForm_qCoeff_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_heckeULin_mul_aeval_eq_zero_isIntegral_of_sq_dvd_of_not_cube_dvd
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree"
p2m_attr_erase "simp" "FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CuspForm.coe_heckeULowerLin_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularForm Polynomial
open scoped MatrixGroups ModularForm

namespace A2alphaOldSpace

theorem hΓ (M : ℕ) [NeZero M] : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 M : Subgroup SL(2, ℤ)) :
    Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp

def qCoeffLin (M n : ℕ) [NeZero M] : CuspForm (CongruenceSubgroup.Gamma0 M) 2 →ₗ[ℂ] ℂ where
  toFun G := ModularFormClass.qCoeff G n
  map_add' f g := by
    show ModularFormClass.qCoeff (⇑(f + g)) n = _
    unfold ModularFormClass.qCoeff
    rw [CuspForm.coe_add, ModularForm.qExpansion_add one_pos (hΓ M) f g, map_add]
  map_smul' c f := by
    show ModularFormClass.qCoeff (⇑(c • f)) n = _
    unfold ModularFormClass.qCoeff
    rw [CuspForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos (hΓ M), _root_.map_smul]
    rfl

theorem qCoeffLin_apply (M n : ℕ) [NeZero M] (G : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    qCoeffLin M n G = ModularFormClass.qCoeff G n := rfl

theorem qCoeff_zero' (M n : ℕ) [NeZero M] :
    ModularFormClass.qCoeff (⇑(0 : CuspForm (CongruenceSubgroup.Gamma0 M) 2)) n = 0 := by
  rw [← qCoeffLin_apply, map_zero]

theorem rescaleLin_apply' {d R M : ℕ} [NeZero M] [NeZero R] (hdRM : d * R ∣ M) (hd : d ≠ 0)
    (f : CuspForm (CongruenceSubgroup.Gamma0 R) 2) (τ : ℍ) :
    FreyPackage.ModMCarrier.rescaleLin hdRM 2 f τ = (d : ℂ) * f (heckeDiagMatrix d • τ) := by
  rw [show FreyPackage.ModMCarrier.rescaleLin hdRM 2 f τ
      = (⇑(FreyPackage.ModMCarrier.rescaleLin hdRM 2 f)) τ from rfl,
    FreyPackage.ModMCarrier.coe_rescaleLin_apply, slash_heckeDiagMatrix_apply 2 hd]
  norm_num

def pad (d : ℕ) (c : ℕ → ℂ) (m : ℕ) : ℂ := if d ∣ m then (d : ℂ) * c (m / d) else 0

theorem qCoeff_rescaleLin {d R M : ℕ} [NeZero M] [NeZero R] (hdRM : d * R ∣ M) (hd : d ≠ 0)
    (f : CuspForm (CongruenceSubgroup.Gamma0 R) 2) (n : ℕ) :
    ModularFormClass.qCoeff (FreyPackage.ModMCarrier.rescaleLin hdRM 2 f) n
      = pad d (ModularFormClass.qCoeff f) n := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hfun : (fun τ : ℍ => f (heckeDiagMatrix d • τ))
      = (d : ℂ)⁻¹ • ⇑(FreyPackage.ModMCarrier.rescaleLin hdRM 2 f) := by
    funext τ
    rw [Pi.smul_apply, smul_eq_mul, rescaleLin_apply' hdRM hd, ← mul_assoc, inv_mul_cancel₀ hdC,
      one_mul]
  have h1 := ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul f (hΓ R) hd n
  rw [hfun] at h1
  have h2 : ModularFormClass.qCoeff ((d : ℂ)⁻¹ • ⇑(FreyPackage.ModMCarrier.rescaleLin hdRM 2 f)) n
      = (d : ℂ)⁻¹ * ModularFormClass.qCoeff (FreyPackage.ModMCarrier.rescaleLin hdRM 2 f) n := by
    unfold ModularFormClass.qCoeff
    rw [ModularForm.qExpansion_smul one_pos (hΓ M), _root_.map_smul, smul_eq_mul]
  rw [h2] at h1
  have h3 := congrArg (fun z : ℂ => (d : ℂ) * z) h1
  rw [← mul_assoc, mul_inv_cancel₀ hdC, one_mul] at h3
  rw [h3]
  unfold pad
  split_ifs <;> simp

theorem qCoeff_heckeULin {M p : ℕ} [NeZero M] (hp : p ≠ 0) (hpM : p ∣ M)
    (F : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.heckeULin 2 hpM F) n = ModularFormClass.qCoeff F (n * p) := by
  rw [CuspForm.coe_heckeULin_apply]
  exact ModularFormClass.qCoeff_heckeU F (hΓ M) hp n

theorem qCoeff_mul_of_not_dvd {R : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 R) 2}
    (hg : g.IsNormalizedEigenform) {q : ℕ} (hq : q.Prime) (hqR : ¬ q ∣ R) (m : ℕ) :
    ModularFormClass.qCoeff g (m * q) = ModularFormClass.qCoeff g q * ModularFormClass.qCoeff g m
      - q * (if q ∣ m then ModularFormClass.qCoeff g (m / q) else 0) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [CuspForm.qCoeff_zero]
  obtain ⟨r, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' q hq.ne_one
  have hcop : ∀ s : ℕ, Nat.Coprime (q ^ s) m' := fun s =>
    (hq.coprime_iff_not_dvd.mpr hm').pow_left s
  rcases r with _ | r
  · rw [pow_zero, one_mul, if_neg hm', mul_zero, sub_zero, mul_comm m' q,
      show q * m' = q ^ 1 * m' by rw [pow_one], hg.qCoeff_mul_of_coprime _ _ (hcop 1), pow_one]
  · have h1 : q ^ (r + 1) * m' * q = q ^ (r + 2) * m' := by ring
    have h2 : q ∣ q ^ (r + 1) * m' := dvd_mul_of_dvd_left (dvd_pow_self q (Nat.succ_ne_zero r)) _
    have h3 : q ^ (r + 1) * m' / q = q ^ r * m' := by
      rw [pow_succ, mul_assoc, mul_comm q, ← mul_assoc, Nat.mul_div_cancel _ hq.pos]
    rw [h1, if_pos h2, h3, hg.qCoeff_mul_of_coprime _ _ (hcop _),
      hg.qCoeff_mul_of_coprime _ _ (hcop _), hg.qCoeff_mul_of_coprime _ _ (hcop _),
      hg.qCoeff_prime_pow_of_not_dvd q r hq hqR]
    ring

theorem qCoeff_mul_of_dvd {R : ℕ} {g : CuspForm (CongruenceSubgroup.Gamma0 R) 2}
    (hg : g.IsNormalizedEigenform) {q : ℕ} (hq : q.Prime) (hqR : q ∣ R) (m : ℕ) :
    ModularFormClass.qCoeff g (m * q) = ModularFormClass.qCoeff g q * ModularFormClass.qCoeff g m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [CuspForm.qCoeff_zero]
  obtain ⟨r, m', hm', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm.ne' q hq.ne_one
  have hcop : ∀ s : ℕ, Nat.Coprime (q ^ s) m' := fun s =>
    (hq.coprime_iff_not_dvd.mpr hm').pow_left s
  rcases r with _ | r
  · rw [pow_zero, one_mul, mul_comm m' q,
      show q * m' = q ^ 1 * m' by rw [pow_one], hg.qCoeff_mul_of_coprime _ _ (hcop 1), pow_one]
  · have h1 : q ^ (r + 1) * m' * q = q ^ (r + 2) * m' := by ring
    rw [h1, hg.qCoeff_mul_of_coprime _ _ (hcop _), hg.qCoeff_mul_of_coprime _ _ (hcop _),
      hg.qCoeff_prime_pow_of_dvd q r hq hqR]
    ring

def L (q : ℕ) {k : ℕ} (w : Fin k → ℂ) (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ j : Fin k, w j * c (n * q ^ (j : ℕ))

theorem pad_mul (d e : ℕ) (c : ℕ → ℂ) : pad (d * e) c = pad d (pad e c) := by
  funext m
  unfold pad
  by_cases hdm : d ∣ m
  · rw [if_pos hdm]
    by_cases hem : e ∣ m / d
    · rw [if_pos hem, if_pos ((Nat.dvd_div_iff_mul_dvd hdm).mp hem), Nat.div_div_eq_div_mul,
        Nat.cast_mul, mul_assoc]
    · rw [if_neg hem, mul_zero, if_neg (fun h => hem ((Nat.dvd_div_iff_mul_dvd hdm).mpr h))]
  · rw [if_neg hdm, if_neg (fun h => hdm (dvd_trans (dvd_mul_right d e) h))]

theorem pad_one (c : ℕ → ℂ) : pad 1 c = c := by
  funext m; simp [pad]

theorem L_pad_of_coprime (q : ℕ) {k : ℕ} (w : Fin k → ℂ) (c : ℕ → ℂ) {d : ℕ}
    (hdq : Nat.Coprime d q) (n : ℕ) :
    L q w (pad d c) n = if d ∣ n then (d : ℂ) * L q w c (n / d) else 0 := by
  unfold L pad
  by_cases hdn : d ∣ n
  · rw [if_pos hdn, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [if_pos (dvd_mul_of_dvd_left hdn _), Nat.div_mul_right_comm hdn]
    ring
  · rw [if_neg hdn]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg (fun h => hdn (((hdq.pow_right _).dvd_mul_right).mp h)), mul_zero]

theorem L_pad_eq_zero_of_coprime (q : ℕ) {k : ℕ} (w : Fin k → ℂ) (c : ℕ → ℂ) {d : ℕ}
    (hdq : Nat.Coprime d q) (h : ∀ n, L q w c (n * q) = 0) (n : ℕ) :
    L q w (pad d c) (n * q) = 0 := by
  rw [L_pad_of_coprime q w c hdq]
  split_ifs with hdn
  · have hdn' : d ∣ n := hdq.dvd_mul_right.mp hdn
    rw [← Nat.div_mul_right_comm hdn' q, h, mul_zero]
  · rfl

theorem L_three (q : ℕ) (x y z : ℂ) (c : ℕ → ℂ) (n : ℕ) :
    L q ![x, y, z] c n = x * c n + y * c (n * q) + z * c (n * q * q) := by
  simp [L, Fin.sum_univ_three, pow_two, mul_assoc]

theorem L_two (q : ℕ) (x y : ℂ) (c : ℕ → ℂ) (n : ℕ) :
    L q ![x, y] c n = x * c n + y * c (n * q) := by
  simp [L, Fin.sum_univ_two]

theorem L_one (q : ℕ) (x : ℂ) (c : ℕ → ℂ) (n : ℕ) : L q ![x] c n = x * c n := by
  simp [L]

theorem towerA {q : ℕ} (hq : q.Prime) (a : ℂ) (b : ℕ → ℂ)
    (H : ∀ m, b (m * q) = a * b m - q * (if q ∣ m then b (m / q) else 0))
    {i : ℕ} (hi : i ≤ 2) (n : ℕ) :
    L q ![(q : ℂ), -a, 1] (pad (q ^ i) b) (n * q) = 0 := by
  have hq0 : 0 < q := hq.pos
  rw [L_three]
  interval_cases i
  · rw [pow_zero, pad_one, H (n * q * q), if_pos (dvd_mul_left q (n * q)),
      Nat.mul_div_cancel _ hq0]
    ring
  · have e1 : pad (q ^ 1) b (n * q) = q * b n := by
      rw [pow_one, pad, if_pos (dvd_mul_left q n), Nat.mul_div_cancel _ hq0]
    have e2 : pad (q ^ 1) b (n * q * q) = q * b (n * q) := by
      rw [pow_one, pad, if_pos (dvd_mul_left q _), Nat.mul_div_cancel _ hq0]
    have e3 : pad (q ^ 1) b (n * q * q * q) = q * b (n * q * q) := by
      rw [pow_one, pad, if_pos (dvd_mul_left q _), Nat.mul_div_cancel _ hq0]
    rw [e1, e2, e3, H (n * q), if_pos (dvd_mul_left q n), Nat.mul_div_cancel _ hq0]
    ring
  · have e1 : pad (q ^ 2) b (n * q) = (q : ℂ) * q * (if q ∣ n then b (n / q) else 0) := by
      unfold pad
      rw [pow_two, Nat.cast_mul]
      by_cases hqn : q ∣ n
      · rw [if_pos (mul_dvd_mul hqn (dvd_refl q)), if_pos hqn,
          Nat.mul_div_mul_right _ _ hq0]
      · rw [if_neg (fun h => hqn ((Nat.mul_dvd_mul_iff_right hq0).mp h)), if_neg hqn, mul_zero]
    have e2 : pad (q ^ 2) b (n * q * q) = (q : ℂ) * q * b n := by
      rw [pad, pow_two, if_pos ⟨n, by ring⟩, mul_assoc, Nat.mul_div_cancel _ (Nat.mul_pos hq0 hq0),
        Nat.cast_mul]
    have e3 : pad (q ^ 2) b (n * q * q * q) = (q : ℂ) * q * b (n * q) := by
      rw [pad, pow_two, if_pos ⟨n * q, by ring⟩, mul_assoc (n * q),
        Nat.mul_div_cancel _ (Nat.mul_pos hq0 hq0), Nat.cast_mul]
    rw [e1, e2, e3, H n]
    ring

theorem towerB {q : ℕ} (hq : q.Prime) (a : ℂ) (b : ℕ → ℂ)
    (H : ∀ m, b (m * q) = a * b m) {i : ℕ} (hi : i ≤ 1) (n : ℕ) :
    L q ![-a, 1] (pad (q ^ i) b) (n * q) = 0 := by
  have hq0 : 0 < q := hq.pos
  rw [L_two]
  interval_cases i
  · rw [pow_zero, pad_one, H (n * q)]
    ring
  · have e1 : pad (q ^ 1) b (n * q) = q * b n := by
      rw [pow_one, pad, if_pos (dvd_mul_left q n), Nat.mul_div_cancel _ hq0]
    have e2 : pad (q ^ 1) b (n * q * q) = q * b (n * q) := by
      rw [pow_one, pad, if_pos (dvd_mul_left q _), Nat.mul_div_cancel _ hq0]
    rw [e1, e2, H n]
    ring

theorem towerC {q : ℕ} (b : ℕ → ℂ) (H : ∀ m, b (m * q) = 0) (n : ℕ) :
    L q ![(1 : ℂ)] (pad (q ^ 0) b) (n * q) = 0 := by
  rw [L_one, pow_zero, pad_one, H n, mul_zero]

def RootsGood (q : ℕ) (P : ℂ[X]) : Prop :=
  ∀ μ : ℂ, P.IsRoot μ → IsIntegral ℤ μ ∧ ∃ ν : ℂ, IsIntegral ℤ ν ∧ μ * ν = q

theorem rootsGood_prod (q : ℕ) {ι : Type*} (s : Finset ι) (P : ι → ℂ[X])
    (h : ∀ i ∈ s, RootsGood q (P i)) : RootsGood q (∏ i ∈ s, P i) := by
  intro μ hμ
  rw [IsRoot.def, eval_prod, Finset.prod_eq_zero_iff] at hμ
  obtain ⟨i, hi, hμi⟩ := hμ
  exact h i hi μ hμi

theorem rootsGood_one (q : ℕ) : RootsGood q (1 : ℂ[X]) := by
  intro μ hμ
  simp at hμ

theorem rootsGood_X_sub_C (q : ℕ) {a : ℂ} (ha : a ^ 2 = 1) : RootsGood q (X - C a) := by
  intro μ hμ
  rw [IsRoot.def, eval_sub, eval_X, eval_C, sub_eq_zero] at hμ
  subst hμ
  have hint : IsIntegral ℤ μ := by
    refine ⟨X ^ 2 - 1, (monic_X_pow 2).sub_of_left (by simp), ?_⟩
    simp [ha]
  refine ⟨hint, μ * q, hint.mul ?_, ?_⟩
  · exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (q : ℤ)))
  · rw [← mul_assoc, ← pow_two, ha, one_mul]

theorem rootsGood_quadratic (q : ℕ) {a : ℂ} (ha : IsIntegral ℤ a) :
    RootsGood q (X ^ 2 - C a * X + C (q : ℂ)) := by
  intro μ hμ
  rw [IsRoot.def, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C, eval_X, eval_C] at hμ

  set A := integralClosure ℤ ℂ
  have haA : a ∈ A := ha
  have hint : IsIntegral ℤ μ := by
    have hA : IsIntegral A μ := by
      let α : A := ⟨a, haA⟩
      refine ⟨X ^ 2 + (C (-α) * X + C ((q : ℕ) : A)), monic_X_pow_add ?_, ?_⟩
      · have h1 : (C (-α) * X).degree ≤ 1 := degree_C_mul_X_le _
        have h2 : (C ((q : ℕ) : A)).degree ≤ 1 := degree_C_le.trans (by norm_num)
        exact ((degree_add_le _ _).trans (max_le h1 h2)).trans_lt (by norm_num)
      · simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C]
        have hα : algebraMap A ℂ α = a := rfl
        rw [map_neg, map_natCast, hα]
        linear_combination hμ
    exact isIntegral_trans μ hA
  refine ⟨hint, a - μ, ha.sub hint, ?_⟩
  linear_combination (-1 : ℂ) * hμ

theorem qCoeff_U_aeval_quadratic {N : ℕ} [NeZero N] {q : ℕ} (hq : q.Prime) (hqN : q ∣ N)
    (a : ℂ) (F : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.heckeULin 2 hqN
        (aeval (CuspForm.heckeULin (N := N) 2 hqN) (X ^ 2 - C a * X + C (q : ℂ)) F)) n
      = L q ![(q : ℂ), -a, 1] (ModularFormClass.qCoeff F) (n * q) := by
  set U := CuspForm.heckeULin (N := N) 2 hqN with hU
  have hev : aeval U (X ^ 2 - C a * X + C (q : ℂ)) F = U (U F) - a • U F + (q : ℂ) • F := by
    simp only [map_add, map_sub, map_mul, aeval_X, aeval_C, LinearMap.add_apply,
      LinearMap.sub_apply, Module.End.mul_apply, Module.algebraMap_end_apply, pow_two]
  rw [hev, map_add, map_sub, map_smul, map_smul, ← qCoeffLin_apply, map_add, map_sub, map_smul,
    map_smul, qCoeffLin_apply, qCoeffLin_apply, qCoeffLin_apply, smul_eq_mul, smul_eq_mul, hU,
    qCoeff_heckeULin hq.ne_zero, qCoeff_heckeULin hq.ne_zero, qCoeff_heckeULin hq.ne_zero,
    qCoeff_heckeULin hq.ne_zero, qCoeff_heckeULin hq.ne_zero, qCoeff_heckeULin hq.ne_zero, L_three]
  ring

theorem qCoeff_U_aeval_linear {N : ℕ} [NeZero N] {q : ℕ} (hq : q.Prime) (hqN : q ∣ N)
    (a : ℂ) (F : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.heckeULin 2 hqN
        (aeval (CuspForm.heckeULin (N := N) 2 hqN) (X - C a) F)) n
      = L q ![-a, 1] (ModularFormClass.qCoeff F) (n * q) := by
  set U := CuspForm.heckeULin (N := N) 2 hqN with hU
  have hev : aeval U (X - C a) F = U F - a • F := by
    simp only [map_sub, aeval_X, aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply]
  rw [hev, map_sub, map_smul, ← qCoeffLin_apply, map_sub, map_smul, qCoeffLin_apply,
    qCoeffLin_apply, smul_eq_mul, hU, qCoeff_heckeULin hq.ne_zero, qCoeff_heckeULin hq.ne_zero,
    qCoeff_heckeULin hq.ne_zero, L_two]
  ring

theorem qCoeff_U_aeval_one {N : ℕ} [NeZero N] {q : ℕ} (hq : q.Prime) (hqN : q ∣ N)
    (F : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.heckeULin 2 hqN
        (aeval (CuspForm.heckeULin (N := N) 2 hqN) (1 : ℂ[X]) F)) n
      = L q ![(1 : ℂ)] (ModularFormClass.qCoeff F) (n * q) := by
  rw [map_one, Module.End.one_apply, qCoeff_heckeULin hq.ne_zero, L_one, one_mul]

theorem exists_poly_generator {N : ℕ} [NeZero N] {q : ℕ} (hq : q.Prime) (hqN : q ∣ N)
    (hcube : ¬ q ^ 3 ∣ N) {R d : ℕ} (hdRM : d * R ∣ N)
    (g : CuspForm (CongruenceSubgroup.Gamma0 R) 2) (hg : g.IsNewform) :
    ∃ P : ℂ[X], RootsGood q P ∧
      CuspForm.heckeULin 2 hqN (aeval (CuspForm.heckeULin (N := N) 2 hqN) P
        (FreyPackage.ModMCarrier.rescaleLin hdRM 2 g)) = 0 := by
  haveI hR : NeZero R :=
    ⟨by rintro rfl; exact NeZero.ne N (Nat.eq_zero_of_zero_dvd (mul_zero d ▸ hdRM))⟩
  have hd : d ≠ 0 := by
    rintro rfl; exact NeZero.ne N (Nat.eq_zero_of_zero_dvd (zero_mul R ▸ hdRM))

  obtain ⟨i, d', hd', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd q hq.ne_one
  have hcop : Nat.Coprime d' q := (hq.coprime_iff_not_dvd.mpr hd').symm

  have hcF : ModularFormClass.qCoeff (FreyPackage.ModMCarrier.rescaleLin hdRM 2 g)
      = pad d' (pad (q ^ i) (ModularFormClass.qCoeff g)) := by
    funext n
    rw [qCoeff_rescaleLin hdRM hd g n, mul_comm (q ^ i) d', pad_mul]

  have hvan : ∀ H : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
      (∀ n, ModularFormClass.qCoeff H n = 0) → H = 0 := fun H hH =>
    ModularFormClass.eq_of_forall_qCoeff_eq (hΓ N) fun n => by rw [hH n, qCoeff_zero' N n]
  by_cases hqR : q ∣ R
  · by_cases hqR2 : q ^ 2 ∣ R
    ·
      have ha0 : ModularFormClass.qCoeff g q = 0 :=
        CuspForm.qCoeff_eq_zero_of_isNewform_of_sq_dvd hg q hq hqR2
      have hi : i = 0 := by
        rcases Nat.eq_zero_or_pos i with h | h
        · exact h
        · exfalso; apply hcube
          obtain ⟨R', rfl⟩ := hqR2
          exact dvd_trans ⟨q ^ (i - 1) * d' * R', by
            rw [show q ^ i = q ^ (i - 1) * q by rw [← pow_succ]; congr 1; omega]; ring⟩ hdRM
      subst hi
      refine ⟨1, rootsGood_one q, hvan _ fun n => ?_⟩
      rw [qCoeff_U_aeval_one hq, hcF]
      refine L_pad_eq_zero_of_coprime q _ _ hcop (fun m => towerC _ (fun m => ?_) m) n
      rw [qCoeff_mul_of_dvd hg.1 hq hqR, ha0, zero_mul]
    ·
      have ha1 : ModularFormClass.qCoeff g q ^ 2 = 1 :=
        CuspForm.qCoeff_sq_eq_one_of_isNewform hg q hq hqR hqR2
      have hi : i ≤ 1 := by
        by_contra h
        apply hcube
        obtain ⟨R', rfl⟩ := hqR
        exact dvd_trans ⟨q ^ (i - 2) * d' * R', by
          rw [show q ^ i = q ^ (i - 2) * q ^ 2 by rw [← pow_add]; congr 1; omega]; ring⟩ hdRM
      refine ⟨X - C (ModularFormClass.qCoeff g q), rootsGood_X_sub_C q ha1, hvan _ fun n => ?_⟩
      rw [qCoeff_U_aeval_linear hq, hcF]
      exact L_pad_eq_zero_of_coprime q _ _ hcop
        (fun m => towerB hq _ _ (fun m => qCoeff_mul_of_dvd hg.1 hq hqR m) hi m) n
  ·
    have hi : i ≤ 2 := by
      by_contra h
      apply hcube
      exact dvd_trans ⟨q ^ (i - 3) * d' * R, by
        rw [show q ^ i = q ^ (i - 3) * q ^ 3 by rw [← pow_add]; congr 1; omega]; ring⟩ hdRM
    obtain ⟨α, hα⟩ := CuspForm.forall_exists_qCoeff_eq_of_isNormalizedEigenform hg.1 q
    have haint : IsIntegral ℤ (ModularFormClass.qCoeff g q) := by rw [← hα]; exact α.2
    refine ⟨X ^ 2 - C (ModularFormClass.qCoeff g q) * X + C (q : ℂ), rootsGood_quadratic q haint,
      hvan _ fun n => ?_⟩
    rw [qCoeff_U_aeval_quadratic hq, hcF]
    exact L_pad_eq_zero_of_coprime q _ _ hcop
      (fun m => towerA hq _ _ (fun m => qCoeff_mul_of_not_dvd hg.1 hq hqR m) hi m) n

theorem heckeULin_mul_aeval {N : ℕ} [NeZero N] {q : ℕ} (hqN : q ∣ N) (A : ℂ[X]) :
    CuspForm.heckeULin 2 hqN * aeval (CuspForm.heckeULin (N := N) 2 hqN) A
      = aeval (CuspForm.heckeULin (N := N) 2 hqN) A * CuspForm.heckeULin 2 hqN := by
  set U := CuspForm.heckeULin (N := N) 2 hqN
  calc U * aeval U A = aeval U X * aeval U A := by rw [aeval_X]
    _ = aeval U (X * A) := (map_mul _ _ _).symm
    _ = aeval U (A * X) := by rw [mul_comm]
    _ = aeval U A * U := by rw [map_mul, aeval_X]

end A2alphaOldSpace

open A2alphaOldSpace in
theorem solution
    (N : ℕ) [NeZero N] (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hsq : q ^ 2 ∣ N) (hcube : ¬ q ^ 3 ∣ N) :
    ∃ Q : Polynomial ℂ,
      (∀ μ : ℂ, Q.IsRoot μ → IsIntegral ℤ μ ∧ ∃ ν : ℂ, IsIntegral ℤ ν ∧ μ * ν = q) ∧
      CuspForm.heckeULin 2 hqN * Polynomial.aeval (CuspForm.heckeULin (N := N) 2 hqN) Q = 0 := by
  classical
  set U := CuspForm.heckeULin (N := N) 2 hqN with hU

  set G : Set (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
    {F | ∃ (R d : ℕ) (hdRM : d * R ∣ N) (g : CuspForm (CongruenceSubgroup.Gamma0 R) 2),
      CuspForm.IsNewform g ∧ F = FreyPackage.ModMCarrier.rescaleLin hdRM 2 g} with hG
  have hspan : Submodule.span ℂ G = ⊤ := CuspForm.span_rescaleLin_isNewform_eq_top N
  haveI := CuspForm.finiteDimensional_Gamma0 N 2
  have hfg : (Submodule.span ℂ G).FG := by rw [hspan]; exact Module.Finite.fg_top
  obtain ⟨s, hsG, hs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset G).mp hfg

  have key : ∀ F ∈ G, ∃ P : ℂ[X], RootsGood q P ∧ U (aeval U P F) = 0 := by
    rintro F ⟨R, d, hdRM, g, hg, rfl⟩
    exact exists_poly_generator hq hqN hcube hdRM g hg
  choose! P hP using key
  refine ⟨∏ F ∈ s, P F, rootsGood_prod q s P (fun F hF => (hP F (hsG hF)).1), ?_⟩
  apply LinearMap.ext
  intro v
  have hv : v ∈ Submodule.span ℂ (↑s : Set (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) := by
    rw [← hs, hspan]; exact Submodule.mem_top
  suffices h : Submodule.span ℂ (↑s : Set (CuspForm (CongruenceSubgroup.Gamma0 N) 2))
      ≤ LinearMap.ker (U * aeval U (∏ F ∈ s, P F)) by
    rw [LinearMap.zero_apply]; exact LinearMap.mem_ker.mp (h hv)
  rw [Submodule.span_le]
  intro F hF
  rw [SetLike.mem_coe, LinearMap.mem_ker, ← Finset.prod_erase_mul s P (Finset.mem_coe.mp hF),
    map_mul, ← mul_assoc, heckeULin_mul_aeval hqN, mul_assoc, Module.End.mul_apply,
    Module.End.mul_apply, (hP F (hsG hF)).2, map_zero]

end

end S_CuspForm_exists_heckeULin_mul_aeval_eq_zero_isIntegral_of_sq_dvd_of_not_cube_dvd
end P2MW
export P2MW.S_CuspForm_exists_heckeULin_mul_aeval_eq_zero_isIntegral_of_sq_dvd_of_not_cube_dvd (solution)
