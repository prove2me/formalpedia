-- Prove2me | solution 1 for BookProof.ChapterA3.lambda_surjective
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T06:00:05.712178+00:00
-- url     : https://prove2.me/submissions/29fb66d5-c057-441f-ab91-270dc8ef72ef

import Mathlib
import Definitions.Def_ChapterA3c
open BookProof.ChapterA3 Matrix
open scoped ComplexConjugate
set_option maxHeartbeats 0

private theorem isCliffordC_toC {A : Fin 4 → Matrix (Fin 4) (Fin 4) ℝ} (hA : IsCliffordR A) :
    IsCliffordC (fun μ => toC (A μ)) := by
  intro μ ν; specialize hA μ ν; simp_all only [neg_mul, neg_smul, ← ext_iff, Matrix.add_apply, mul_apply,
      Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul] ;
  convert hA using 3;
  simp [ ← Complex.ofReal_inj, minkowski, minkowskiR, toC ];
  simp [ Matrix.one_apply ];
  split_ifs <;> norm_num

/-
Complexification is a ring homomorphism on `4×4` matrices: it preserves
products.
-/
private theorem toC_mul (M N : Matrix (Fin 4) (Fin 4) ℝ) : toC (M * N) = toC M * toC N := by
  ext i j; simp [ toC, Matrix.mul_apply ] ;

/-
Complexification preserves the identity.
-/
private theorem toC_one : toC (1 : Matrix (Fin 4) (Fin 4) ℝ) = 1 := by
  ext i j; by_cases hij : i = j <;> simp [ hij, toC ] ;
  simp [ hij, Matrix.one_apply ]

/-
The determinant of a complexified matrix is the cast of the determinant.
-/
private theorem toC_det (M : Matrix (Fin 4) (Fin 4) ℝ) : (toC M).det = (M.det : ℂ) := by
  unfold toC; simp [ Matrix.det_apply' ] ;

/-
Entrywise conjugation fixes a complexified real matrix.
-/
private theorem toC_conj (M : Matrix (Fin 4) (Fin 4) ℝ) :
    (toC M).map (starRingEnd ℂ) = toC M := by
  ext i j; simp [toC]

/-
A complex matrix fixed by entrywise conjugation is the complexification of a
real matrix.
-/
private theorem exists_real_of_conj_fixed {N : Matrix (Fin 4) (Fin 4) ℂ}
    (hN : N.map (starRingEnd ℂ) = N) : ∃ M : Matrix (Fin 4) (Fin 4) ℝ, toC M = N := by
  use Matrix.of (fun i j => (N i j).re);
  ext i j; simp only [toC, map_apply, of_apply];
  replace hN := congr_fun ( congr_fun hN i ) j; simp_all [ Complex.ext_iff ] ;
  grobner

/-
Complexification is injective.
-/
private theorem toC_injective : Function.Injective toC := by
  intro M N h;
  ext i j; have := congr_fun ( congr_fun h i ) j; simp_all [ Complex.ext_iff, toC ] ;

/-
Complexification commutes with the matrix inverse.
-/
private theorem toC_inv (M : Matrix (Fin 4) (Fin 4) ℝ) : toC M⁻¹ = (toC M)⁻¹ := by
  by_cases h : IsUnit ( Matrix.det M ) <;> simp_all only [isUnit_iff_ne_zero, ne_eq, inv_def,
      Ring.inverse_eq_inv', Decidable.not_not, not_true_eq_false, not_false_eq_true,
          Ring.inverse_non_unit, zero_smul];
  · ext i j ; simp only [toC, map_apply, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul,
      Complex.ofReal_inv];
    simp only [det_apply', Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast,
      Complex.ofReal_prod, adjugate_apply, map_apply, mul_eq_mul_left_iff, inv_eq_zero];
    simp only [updateRow_apply, Pi.single_apply, map_apply];
    exact Or.inl ( Finset.sum_congr rfl fun _ _ => by congr; ext; aesop );
  · simp_all [ toC, Matrix.det_apply' ];
    norm_cast at * ; aesop

/-
**Prop 37 (real Pauli theorem).**  Two real Clifford sets `α^μ`, `β^μ` are
related by a real matrix `S` with `|det S| = 1`, `β^μ = S α^μ S⁻¹`, unique up to
sign.
-/
set_option maxHeartbeats 2000000 in
-- the proof below is a large finite computation; the default heartbeat budget
-- is not enough to elaborate it
private theorem real_pauli (hpf : PauliFundamental)
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
    ext i j; simp only [mul_comm, map_apply, Matrix.smul_apply, smul_eq_mul, mul_left_comm, map_mul,
        Complex.conj_ofReal] ;
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


private theorem mgammaR_clifford : IsCliffordR mgammaR := by
  intro μ ν
  ext i j
  fin_cases μ <;> fin_cases ν <;> fin_cases i <;> fin_cases j <;>
    norm_num [mgammaR, mgammaZ, minkowskiR, minkowskiZ, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.smul_apply, Matrix.add_apply, RingHom.mapMatrix_apply,
      Matrix.one_apply]

private theorem hasLambda_unique {S Λ Λ' : Matrix (Fin 4) (Fin 4) ℝ}
    (h : HasLambda S Λ) (h' : HasLambda S Λ') : Λ = Λ' := by
  ext μ ν
  have he := (h μ).symm.trans (h' μ)
  have h00 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 0) he
  have h01 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 1) he
  have h02 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 0 2) he
  have h20 := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M 2 0) he
  simp [Fin.sum_univ_four, mgammaR, mgammaZ, RingHom.mapMatrix_apply,
    Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply] at h00 h01 h02 h20
  fin_cases ν
  · change Λ μ 0 = Λ' μ 0
    linarith
  · exact h00
  · change Λ μ 2 = Λ' μ 2
    linarith
  · exact h01

private theorem hasLambda_LambdaOf (S : Matrix (Fin 4) (Fin 4) ℝ)
    (h : ∃ Λ, HasLambda S Λ) : HasLambda S (LambdaOf S) := by
  classical
  simpa only [LambdaOf, dif_pos h] using h.choose_spec

private theorem cliffordR_lorentz_comb (Λ : Matrix (Fin 4) (Fin 4) ℝ) (hΛ : Λ ∈ LorentzO) :
    IsCliffordR (fun μ => ∑ ν, Λ μ ν • mgammaR ν) := by
  intro μ ν;
  -- By definition of matrix multiplication and the properties of the Majorana matrices, we can
  -- expand the products.
  have h_expand : (∑ α, Λ μ α • mgammaR α) * (∑ β, Λ ν β • mgammaR β) +
      (∑ β, Λ ν β • mgammaR β) * (∑ α, Λ μ α • mgammaR α) =
      ∑ α, ∑ β, (Λ μ α * Λ ν β) • (mgammaR α * mgammaR β + mgammaR β * mgammaR α) := by
        simp only [Finset.mul_sum _ _ _, mul_smul_comm, Finset.sum_mul, smul_mul_assoc, smul_add];
        simp only [Finset.smul_sum, smul_smul, mul_comm, Finset.sum_add_distrib];
        rw [ Finset.sum_comm ];
  -- By definition of matrix multiplication and the properties of the Majorana matrices, we can
  -- simplify the expression.
  have h_simplify : ∑ α, ∑ β, (Λ μ α * Λ ν β) • (mgammaR α * mgammaR β + mgammaR β * mgammaR α) =
      ∑ α, ∑ β, (Λ μ α * Λ ν β) • ((-2 * minkowskiR α β) • 1) := by
        exact Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj =>
            by rw [ mgammaR_clifford i j ] ;
  -- By definition of matrix multiplication and the properties of the Minkowski metric, we can
  -- simplify the expression.
  have h_final : ∑ α, ∑ β, (Λ μ α * Λ ν β) • (-2 * minkowskiR α β) • (1 : Matrix (Fin 4) (Fin 4) ℝ)
      =
      (-2 * (Λ * minkowskiMat * Λᵀ) μ ν) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
        simp only [neg_mul, neg_smul, smul_neg, Finset.sum_neg_distrib, mul_apply, transpose_apply,
            Finset.sum_mul, mul_assoc, Finset.mul_sum _ _ _, mul_left_comm, mul_neg, neg_inj];
        simp only [minkowskiMat, of_apply, mul_comm, mul_left_comm, Finset.sum_smul];
        exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _
            => by simp [ mul_assoc, smul_smul ] );
  exact h_expand.trans <| h_simplify.trans <| h_final.trans <| by rw [ hΛ ] ; rfl;

theorem solution (hpf : PauliFundamental)
    (Λ : Matrix (Fin 4) (Fin 4) ℝ) (hΛ : Λ ∈ LorentzO) :
    ∃ S : Matrix (Fin 4) (Fin 4) ℝ, IsPin S ∧ LambdaOf S = Λ := by
  have := @cliffordR_lorentz_comb Λ hΛ;
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin 4) (Fin 4) ℝ,    |S.det| = 1 ∧ (∀ μ, mgammaR μ = S * (∑ ν, Λ μ
      ν • mgammaR ν) * S⁻¹) := by
    have := @real_pauli hpf ( fun μ => ∑ ν, Λ μ ν • mgammaR ν ) mgammaR this mgammaR_clifford;
    exact ⟨ this.choose, this.choose_spec.1, this.choose_spec.2.1 ⟩;
  refine ⟨ S, ⟨ ?_, hS.1, ?_ ⟩, ?_ ⟩;
  · exact isUnit_iff_ne_zero.mpr ( by intro h; norm_num [ h ] at hS );
  · use Λ;
    intro μ;
    rw [ hS.2 μ ];
    simp [ ← mul_assoc, show S.det ≠ 0 from by intro h; simp [ h ] at hS ];
  · apply hasLambda_unique;
    focus (apply hasLambda_LambdaOf);
    · use Λ;
      intro μ;
      rw [ hS.2 μ ];
      simp [ ← mul_assoc, show S.det ≠ 0 from by intro h; simp [ h ] at hS ];
    · intro μ;
      rw [ hS.2 μ ];
      simp [ ← mul_assoc, show S.det ≠ 0 from by intro h; norm_num [ h ] at hS ]


#print axioms solution
