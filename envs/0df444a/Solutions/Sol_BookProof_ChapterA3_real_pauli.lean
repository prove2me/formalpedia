-- Prove2me | solution 1 for BookProof.ChapterA3.real_pauli
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:03:43.891871+00:00
-- url     : https://prove2.me/submissions/e55c127d-1ce9-45ed-8572-c5d60714881a

-- Generated from ChapterA3b.lean — solution of BookProof.ChapterA3.real_pauli
import Mathlib
import Definitions.Def_ChapterA3b
import Theorems.Thm_BookProof_ChapterA3_isCliffordC_toC
import Theorems.Thm_BookProof_ChapterA3_toC_mul
import Theorems.Thm_BookProof_ChapterA3_toC_det
import Theorems.Thm_BookProof_ChapterA3_toC_conj
import Theorems.Thm_BookProof_ChapterA3_exists_real_of_conj_fixed
import Theorems.Thm_BookProof_ChapterA3_toC_injective
import Theorems.Thm_BookProof_ChapterA3_toC_inv
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution (hpf : PauliFundamental)
    (α β : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ)
    (hα : IsCliffordR α) (hβ : IsCliffordR β) :
    ∃ S : Matrix (Fin 4) (Fin 4) ℝ, |S.det| = 1 ∧ (∀ μ, β μ = S * α μ * S⁻¹) ∧
    (∀ S' : Matrix (Fin 4) (Fin 4) ℝ, |S'.det| = 1 → (∀ μ, β μ = S' * α μ * S'⁻¹) →
      S' = S ∨ S' = -S) := by

  -- Let `Aμ := toC (α μ)`, `Bμ := toC (β μ)`, complex Clifford sets by `isCliffordC_toC`.
  set A : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := fun μ => toC (α μ)
  set B : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := fun μ => toC (β μ);
  -- By the Pauli fundamental theorem, there exists a complex matrix T such that B μ = T * A μ * T⁻¹
  -- for all μ.
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin 4) (Fin 4) ℂ, IsUnit T.det ∧ ∀ μ, B μ = T * A μ * T⁻¹ := by
    exact hpf A B ( isCliffordC_toC hα ) ( isCliffordC_toC hβ ) |>.1;
  -- Let `Tc := T.map (starRingEnd ℂ)`. Apply `.map (starRingEnd ℂ)` to the intertwining relation;
  -- using `toC_conj` (α,β real) and that entrywise conjugation is a ring hom commuting with inverse
  -- (`(T⁻¹).map conj = (T.map conj)⁻¹`, provable via `Matrix.inv_eq_left_inv` + `← Matrix.map_mul`
  -- + `Matrix.nonsing_inv_mul`), get `∀ μ, toC (β μ) = Tc * toC (α μ) * Tc⁻¹`. Also `IsUnit Tc.det`
  -- since `Tc.det = conj T.det`.
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c ≠ 0 ∧ T.map (starRingEnd ℂ) = c • T := by
    apply (hpf A B (isCliffordC_toC hα) (isCliffordC_toC hβ)).2 T (T.map (starRingEnd ℂ)) hT.1 (by
    convert hT.1.map ( starRingEnd ℂ ) using 1;
    simp [ Matrix.det_apply' ]) (by
    exact hT.2) (by
    intro μ
    have hTc : B μ = (T.map (starRingEnd ℂ)) * A μ * (T.map (starRingEnd ℂ))⁻¹ := by
      have hTc_eq : (T.map (starRingEnd ℂ)) * A μ * (T.map (starRingEnd ℂ))⁻¹ = (T * A μ * T⁻¹).map
          (starRingEnd ℂ) := by
        have hTc_eq : (T.map (starRingEnd ℂ))⁻¹ = (T⁻¹).map (starRingEnd ℂ) := by
          rw [ Matrix.inv_eq_left_inv ];
          rw [ ← Matrix.map_mul ];
          ext i j ; by_cases hi : i = j <;> aesop;
        simp only [hTc_eq, Matrix.map_mul];
        exact congr_arg₂ _ ( congr_arg₂ _ rfl ( by ext i j; exact (by
        exact Eq.symm ( by exact (by
          have := toC_conj (α μ);
          exact (by
          exact congr_fun ( congr_fun this i ) j)) )) ) ) rfl
      rw [ hTc_eq, ← hT.2 μ, toC_conj ];
    exact hTc);
  -- Let `r : ℝ := ‖T.det‖ ^ (-1/4 : ℝ)` (positive, `T.det ≠ 0`), `w := Complex.exp ((c.arg/2:ℝ) •
  -- I)` with `w^2 = c`, `‖w‖ = 1`, `conj w = w⁻¹`. Let `a := (r:ℂ) * w`, `S0 := a • T` (note `a ≠
  -- 0`).
  obtain ⟨r, w, a, S0, hr, hw, ha, hS0⟩ : ∃ r : ℝ,    ∃ w : ℂ,    ∃ a : ℂ,    ∃ S0 : Matrix (Fin 4)
      (Fin 4) ℂ,    r > 0 ∧ w^2 = c ∧ ‖w‖ = 1 ∧ a = r * w ∧ S0 = a • T ∧ S0.map (starRingEnd ℂ) = S0
          ∧ ‖S0.det‖ = 1 := by
    -- Let `r : ℝ := ‖T.det‖ ^ (-1/4 : ℝ)` (positive, `T.det ≠ 0`), `w := Complex.exp ((c.arg/2:ℝ) •
    -- I)` with `w^2 = c`, `‖w‖ = 1`, `conj w = w⁻¹`. Let `a := (r:ℂ) * w`, `S0 := a • T` (note `a ≠
    -- 0`), and verify the properties.
    obtain ⟨r, hr⟩ : ∃ r : ℝ, r > 0 ∧ r^4 = 1 / ‖T.det‖ := by
      exact ⟨ ( 1 / ‖T.det‖ ) ^ ( 1/4 : ℝ ), Real.rpow_pos_of_pos ( one_div_pos.mpr (
          norm_pos_iff.mpr ( show T.det ≠ 0 from hT.1.ne_zero ) ) ) _,
              by rw [ ← Real.rpow_natCast, ← Real.rpow_mul ( one_div_nonneg.mpr ( norm_nonneg _ ) )
                  ] ; norm_num ⟩
    obtain ⟨w, hw⟩ : ∃ w : ℂ, w^2 = c ∧ ‖w‖ = 1 := by
      have hw : ‖c‖ = 1 := by
        have h_det : Matrix.det (T.map (starRingEnd ℂ)) = starRingEnd ℂ (Matrix.det T) := by
          simp [ Matrix.det_apply' ];
        replace h_det := congr_arg Norm.norm h_det ; simp_all [ pow_eq_one_iff_of_nonneg ];
      exact ⟨ c ^ ( 1 / 2 : ℂ ), by rw [ ← Complex.cpow_nat_mul ] ; norm_num,
                                    by rw [ Complex.norm_cpow_of_ne_zero hc.1 ] ; norm_num [ hw ] ⟩
    use r, w, r * w, (r * w) • T;
    simp_all only [isUnit_iff_ne_zero, ne_eq, gt_iff_lt, one_div, det_smul_of_tower,
        Fintype.card_fin, mul_pow, smul_eq_mul, Complex.norm_mul, norm_pow, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hr.1, one_pow, mul_one, norm_eq_zero, not_false_eq_true,
                inv_mul_cancel₀, and_true, true_and];
    ext i j; simp only [mul_comm, map_apply, Matrix.smul_apply, smul_eq_mul, mul_left_comm, map_mul, Complex.conj_ofReal] ;
    replace hc := congr_fun ( congr_fun hc.2 i ) j;      simp_all only [mul_assoc, map_apply,
                                                           Matrix.smul_apply,
                                                           smul_eq_mul,
                                                           mul_comm,
                                                           mul_left_comm] ;
    rw [ ← hw.1 ] ; ring;
    rw [ show w ^ 2 = w * w by ring, mul_assoc ] ; rw [ show ( starRingEnd ℂ ) w = w⁻¹ from ?_ ] ;
                               focus (ring);
    · grind;
    · rw [ Complex.inv_def, Complex.normSq_eq_norm_sq ] ; aesop;
  -- By `exists_real_of_conj_fixed` get real `S` with `toC S = S0`.
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin 4) (Fin 4) ℝ, toC S = S0 := by
    exact exists_real_of_conj_fixed hS0.2.2.1;
  refine ⟨ S, ?_, ?_, ?_ ⟩;
  · convert hS0.2.2.2 using 1;
    rw [ ← hS, toC_det ] ; norm_cast;
  · intro μ
    have h_inter : B μ = S0 * A μ * S0⁻¹ := by
      simp_all [ Matrix.inv_def ];
      simp [ Matrix.adjugate_smul, smul_smul, mul_assoc, mul_comm ];
      simp [ show (w * r) ^ 4 = (w * r) ^ 3 * (w * r) by ring, mul_assoc,
        mul_left_comm, hr.ne', show w ≠ 0 from by aesop_cat ];
      simp [ mul_left_comm ( w : ℂ ), hr.ne', show w ≠ 0 from by aesop_cat ];
    refine toC_injective ?_;
    convert h_inter using 1;
    rw [ ← hS, toC_mul, toC_mul, toC_inv ];
  · intro S' hS' hS'_eq
    obtain ⟨d, hd⟩ : ∃ d : ℂ, d ≠ 0 ∧ toC S' = d • toC S := by
      have h_conj : ∀ μ, toC (β μ) = toC S' * toC (α μ) * (toC S')⁻¹ := by
        intro μ; rw [ hS'_eq μ ] ; simp [ toC_mul, toC_inv ] ;
      have := hpf A B ( isCliffordC_toC hα ) ( isCliffordC_toC hβ );
      apply this.right;
      · simp_all ;
        exact ⟨ hr.ne', by rintro rfl; norm_num at ha ⟩;
      · rw [ toC_det ];
        exact isUnit_iff_ne_zero.mpr ( by aesop_cat );
      · intro μ; specialize hT; have := hT.2 μ; simp_all [ Matrix.mul_assoc ] ;
        simp [ Matrix.inv_def, Matrix.smul_eq_diagonal_mul ];
        simp [ ← mul_assoc, ← Matrix.smul_eq_diagonal_mul, Matrix.adjugate_smul ];
        simp [ ← smul_assoc, ← mul_assoc, 
           ];
        field_simp;
        rw [show (r * w / (T.det * r * w)) = (1 / T.det) by
          rw [div_eq_div_iff] <;> ring <;> norm_num [hr.ne', show w ≠ 0 from by aesop_cat,
            hT.1]];
      · exact h_conj;
    -- Since `toC S' = d • toC S`, we have `S' = d • S`.
    have hS'_eq_dS : S' = d.re • S := by
      ext i j; simp only [ne_eq, toC] at hd; (
      replace hd := congr_fun ( congr_fun hd.2 i ) j; simp_all [ Complex.ext_iff ] ;);
    have h_det_S : |S.det| = 1 := by
      have h_det_S : ‖(toC S).det‖ = 1 := by
        grind;
      convert h_det_S using 1;
      norm_num [ toC_det ];
    simp_all only [isUnit_iff_ne_zero, ne_eq, gt_iff_lt, det_smul_of_tower, Fintype.card_fin,
        smul_eq_mul, abs_mul, abs_pow, mul_one, Algebra.smul_mul_assoc];
    rcases eq_or_eq_neg_of_abs_eq
      (show |d.re| = 1 by
        rw [pow_eq_one_iff_of_nonneg (abs_nonneg _)] at hS' <;> aesop) with h | h <;>
      aesop
