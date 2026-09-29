-- Prove2me | solution 1 for BookProof.GaussCoreQuadBounds.gaussInt_self
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T16:31:22.829641+00:00
-- url     : https://prove2.me/submissions/9d2bdc92-cb21-4d35-826b-a396ac0fb5e6

import Mathlib
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterQgHermiteOscillatorEsa
open MeasureTheory Complex MvPolynomial Finset
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine
noncomputable section
namespace BookProof.QgHermiteFriedrichs
variable {d : ℕ}

@[simp] theorem cpoly_add (p q : MvPolynomial (Fin d) ℂ) :
    cpoly (p + q) = cpoly p + cpoly q := by
  simp [cpoly]

@[simp] theorem cpoly_mul (p q : MvPolynomial (Fin d) ℂ) :
    cpoly (p * q) = cpoly p * cpoly q := by
  simp [cpoly]

@[simp] theorem cpoly_X (j : Fin d) : cpoly (X j : MvPolynomial (Fin d) ℂ) = X j := by
  simp [cpoly]

@[simp] theorem cpoly_C (a : ℂ) :
    cpoly (C a : MvPolynomial (Fin d) ℂ) = C (starRingEnd ℂ a) := by
  simp [cpoly]

theorem cpoly_pderiv (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    cpoly (pderiv j p) = pderiv j (cpoly p) := pderiv_map.symm

theorem conj_polyEval (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p)
      = MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (cpoly p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [cpoly]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp only [cpoly] at hp ⊢; simp [hp]

theorem conj_pgFun (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    (starRingEnd ℂ) (pgFun p x) = pgFun (cpoly p) x := by
  simp only [pgFun, map_mul, Complex.conj_ofReal, conj_polyEval]

@[simp] theorem cpoly_sub (p q : MvPolynomial (Fin d) ℂ) :
    cpoly (p - q) = cpoly p - cpoly q := by
  simp [cpoly]

@[simp] theorem cpoly_neg (p : MvPolynomial (Fin d) ℂ) : cpoly (-p) = -cpoly p := by
  simp [cpoly]

theorem cpoly_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin d) ℂ) :
    cpoly (∑ i ∈ s, f i) = ∑ i ∈ s, cpoly (f i) :=
  map_sum (MvPolynomial.map (starRingEnd ℂ)) f s

theorem cpoly_coreD (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    cpoly (coreD j p) = coreD j (cpoly p) := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by norm_num [Complex.ext_iff]
  unfold coreD
  rw [cpoly_sub, cpoly_pderiv, cpoly_mul, cpoly_mul, cpoly_X, cpoly_C, hhalf]

theorem inner_pgLp_pgLp (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp p) (pgLp q) : ℂ) = gaussInt (cpoly p * q) := by
  rw [inner_pgLp, gaussInt]
  refine integral_congr_ae ?_
  filter_upwards [pgLp_coeFn q] with x hx
  rw [hx, conj_pgFun]
  simp only [pgFun, map_mul, gaussWD_eq_sq]
  push_cast
  ring

theorem gaussInt_sub (r s : MvPolynomial (Fin d) ℂ) :
    gaussInt (r - s) = gaussInt r - gaussInt s := by
  have h : r - s = r + (-1 : ℂ) • s := by module
  rw [h, gaussInt_add, gaussInt_smul]
  ring

theorem gaussInt_neg (r : MvPolynomial (Fin d) ℂ) : gaussInt (-r) = -gaussInt r := by
  have h : -r = (-1 : ℂ) • r := by module
  rw [h, gaussInt_smul]
  ring

theorem gaussInt_coreD_raw (j : Fin d) (a b : MvPolynomial (Fin d) ℂ) :
    gaussInt (coreD j a * b) = -gaussInt (a * coreD j b) := by
  have hC2 : (C (1 / 2 : ℂ) : MvPolynomial (Fin d) ℂ) * 2 = 1 := by
    have h2 : ((2 : MvPolynomial (Fin d) ℂ)) = C (2 : ℂ) :=
      (MvPolynomial.ext _ _ (congrFun rfl)).symm
    rw [h2, ← C_mul]
    norm_num
  have hsum : coreD j a * b + a * coreD j b = pderiv j (a * b) - X j * (a * b) := by
    simp only [coreD, pderiv_mul, sub_mul, mul_sub]
    linear_combination (-(X j * a * b)) * hC2
  have h0 : gaussInt (coreD j a * b + a * coreD j b) = 0 := by
    rw [hsum, gaussInt_sub, gaussInt_pderiv, sub_self]
  rw [gaussInt_add] at h0
  linear_combination h0

theorem gaussInt_coreD (j : Fin d) (p q : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly (coreD j p) * q) = -gaussInt (cpoly p * coreD j q) := by
  rw [cpoly_coreD, gaussInt_coreD_raw]

theorem cpoly_kinPoly (p : MvPolynomial (Fin d) ℂ) :
    cpoly (kinPoly p) = kinPoly (cpoly p) := by
  simp only [kinPoly, cpoly_neg, cpoly_sum, cpoly_coreD]

theorem gaussInt_kinPoly (p q : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly p * kinPoly q) = ∑ j : Fin d, gaussInt (cpoly (coreD j p) * coreD j q) := by
  have hmul : cpoly p * kinPoly q = -∑ j : Fin d, cpoly p * coreD j (coreD j q) := by
    simp only [kinPoly, Finset.mul_sum, mul_neg]
  rw [hmul, gaussInt_neg, gaussInt_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gaussInt_coreD j p (coreD j q)]

theorem gaussInt_kinPoly_left (p q : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly (kinPoly p) * q) = ∑ j : Fin d, gaussInt (cpoly (coreD j p) * coreD j q) := by
  have hmul : cpoly (kinPoly p) * q = -∑ j : Fin d, coreD j (coreD j (cpoly p)) * q := by
    rw [cpoly_kinPoly]
    simp only [kinPoly, Finset.sum_mul, neg_mul]
  rw [hmul, gaussInt_neg, gaussInt_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gaussInt_coreD_raw j (coreD j (cpoly p)) q, cpoly_coreD, neg_neg]

variable (W : Vd d → ℝ)

theorem potLp_coeFn (hWc : Continuous W) (hWb : ExpBounded W) (p : MvPolynomial (Fin d) ℂ) :
    (potLp W hWc hWb p : Vd d → ℂ) =ᵐ[volume] fun x => ((W x : ℝ) : ℂ) * pgFun p x :=
  (memLp_mul_pgFun_of_expBounded hWc hWb p).coeFn_toLp

theorem coreEquiv_apply (p : MvPolynomial (Fin d) ℂ) :
    ((coreEquiv p : polyGaussCore (d := d)) : L2d d) = pgLp p := rfl

theorem coreEquiv_symm_pgLp (p : MvPolynomial (Fin d) ℂ) :
    coreEquiv.symm ⟨pgLp p, pgLp_mem_core p⟩ = p := by
  apply coreEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  exact Subtype.ext rfl

theorem hamCore_pgLp (hWc : Continuous W) (hWb : ExpBounded W) (p : MvPolynomial (Fin d) ℂ) :
    hamCore W hWc hWb ⟨pgLp p, pgLp_mem_core p⟩ = hamPoly W hWc hWb p := by
  simp only [hamCore, LinearMap.comp_apply, LinearEquiv.coe_coe, coreEquiv_symm_pgLp]
  rfl
end BookProof.QgHermiteFriedrichs
namespace BookProof.QgHermiteOscillator
variable {d : ℕ}
theorem eval_harmPoly (x : Vd d) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (harmPoly (d := d)) = ((harmW x : ℝ) : ℂ) := by
  have hnorm : ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := norm_sq_eq_sum x
  unfold harmPoly harmW
  rw [map_sum, hnorm]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp
  ring

theorem potLp_harmW (p : MvPolynomial (Fin d) ℂ) :
    potLp harmW continuous_harmW expBounded_harmW p = pgLp (harmPoly * p) := by
  unfold potLp pgLp
  refine MemLp.toLp_congr _ _ ?_
  filter_upwards with x
  simp only [pgFun, map_mul, eval_harmPoly]
  ring

theorem harmCore_pgLp (p : MvPolynomial (Fin d) ℂ) :
    harmCore ⟨pgLp p, pgLp_mem_core p⟩ = pgLp (kinPoly p + harmPoly * p) := by
  unfold harmCore
  rw [hamCore_pgLp]
  unfold hamPoly
  rw [potLp_harmW]
  exact (map_add (pgMap (d := d)) (kinPoly p) (harmPoly * p)).symm
end BookProof.QgHermiteOscillator
namespace TargetQuadraticSupport
variable {d : ℕ}
theorem pderiv_harmPoly (j : Fin d) :
    pderiv j (harmPoly (d := d)) = C (1 / 2 : ℂ) * X j := by
  have hC : (C (1 / 4 : ℂ) : MvPolynomial (Fin d) ℂ) * 2 = C (1 / 2 : ℂ) := by
    have h2 : ((2 : MvPolynomial (Fin d) ℂ)) = C (2 : ℂ) :=
      (MvPolynomial.ext _ _ (congrFun rfl)).symm
    rw [h2, ← C_mul]
    norm_num
  unfold harmPoly
  rw [map_sum, Finset.sum_eq_single j]
  · rw [pderiv_C_mul, pow_two, pderiv_mul, pderiv_X_self]
    linear_combination (X j : MvPolynomial (Fin d) ℂ) * hC
  · intro k _ hk
    rw [pderiv_C_mul, pow_two, pderiv_mul, pderiv_X_of_ne hk]
    ring
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem coreD_harmPoly_mul (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    coreD j (harmPoly * p) = C (1 / 2 : ℂ) * (X j * p) + harmPoly * coreD j p := by
  unfold coreD
  rw [pderiv_mul, pderiv_harmPoly]
  ring

theorem coreD_X_mul (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    coreD j (X j * p) = p + X j * coreD j p := by
  unfold coreD
  rw [pderiv_mul, pderiv_X_self]
  ring

theorem cpoly_add (p q : MvPolynomial (Fin d) ℂ) : cpoly (p + q) = cpoly p + cpoly q := by
  simp [cpoly]

theorem cpoly_harmPoly : cpoly (harmPoly (d := d)) = harmPoly := by
  have hq : (starRingEnd ℂ) (1 / 4 : ℂ) = 1 / 4 := by norm_num [Complex.ext_iff]
  unfold harmPoly
  rw [cpoly_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_two, cpoly_mul, cpoly_mul, cpoly_C, cpoly_X, hq]

theorem gaussInt_cross (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly (coreD j p) * (X j * p)) + gaussInt (cpoly p * (X j * coreD j p))
      = -gaussInt (cpoly p * p) := by
  rw [gaussInt_coreD j p (X j * p), coreD_X_mul, mul_add, gaussInt_add]
  ring

theorem gaussInt_self (r : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly r * r) = ((‖pgLp r‖ ^ 2 : ℝ) : ℂ) := by
  rw [← inner_pgLp_pgLp, inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
  norm_cast

theorem gaussInt_harm_self (q : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly q * (harmPoly * q))
      = (((∑ k : Fin d, ‖pgLp (X k * q)‖ ^ 2) / 4 : ℝ) : ℂ) := by
  have hsum : cpoly q * (harmPoly * q)
      = ∑ k : Fin d, (1 / 4 : ℂ) • (cpoly (X k * q) * (X k * q)) := by
    unfold harmPoly
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cpoly_mul, cpoly_X, smul_eq_C_mul]
    ring
  have hterm : ∀ k : Fin d, gaussInt ((1 / 4 : ℂ) • (cpoly (X k * q) * (X k * q)))
      = ((‖pgLp (X k * q)‖ ^ 2 / 4 : ℝ) : ℂ) := by
    intro k
    rw [gaussInt_smul, gaussInt_self]
    push_cast
    ring
  rw [hsum, gaussInt_sum]
  simp only [hterm]
  rw [← Complex.ofReal_sum, Finset.sum_div]

theorem gaussInt_anticommutator (p : MvPolynomial (Fin d) ℂ) :
    gaussInt (cpoly (kinPoly p) * (harmPoly * p))
        + gaussInt (cpoly (harmPoly * p) * kinPoly p)
      = 2 * (∑ j : Fin d, gaussInt (cpoly (coreD j p) * (harmPoly * coreD j p)))
        - ((d : ℂ) / 2) * gaussInt (cpoly p * p) := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by norm_num [Complex.ext_iff]
  have hT1 : ∀ j : Fin d, gaussInt (cpoly (coreD j p) * coreD j (harmPoly * p))
      = (1 / 2 : ℂ) * gaussInt (cpoly (coreD j p) * (X j * p))
        + gaussInt (cpoly (coreD j p) * (harmPoly * coreD j p)) := by
    intro j
    rw [coreD_harmPoly_mul, mul_add, gaussInt_add]
    congr 1
    have hsm : cpoly (coreD j p) * (C (1 / 2 : ℂ) * (X j * p))
        = (1 / 2 : ℂ) • (cpoly (coreD j p) * (X j * p)) := by
      rw [smul_eq_C_mul]; ring
    rw [hsm, gaussInt_smul]
  have hT2 : ∀ j : Fin d, gaussInt (cpoly (coreD j (harmPoly * p)) * coreD j p)
      = (1 / 2 : ℂ) * gaussInt (cpoly p * (X j * coreD j p))
        + gaussInt (cpoly (coreD j p) * (harmPoly * coreD j p)) := by
    intro j
    rw [coreD_harmPoly_mul, cpoly_add]
    simp only [cpoly_mul, cpoly_C, cpoly_X, cpoly_harmPoly, hhalf]
    rw [add_mul, gaussInt_add]
    congr 1
    · have hsm : C (1 / 2 : ℂ) * (X j * cpoly p) * coreD j p
          = (1 / 2 : ℂ) • (cpoly p * (X j * coreD j p)) := by
        rw [smul_eq_C_mul]; ring
      rw [hsm, gaussInt_smul]
    · congr 1
      ring
  rw [gaussInt_kinPoly_left p (harmPoly * p), gaussInt_kinPoly (harmPoly * p) p]
  simp only [hT1, hT2]
  rw [← Finset.sum_add_distrib]
  have hstep : ∀ j : Fin d,
      ((1 / 2 : ℂ) * gaussInt (cpoly (coreD j p) * (X j * p))
          + gaussInt (cpoly (coreD j p) * (harmPoly * coreD j p)))
        + ((1 / 2 : ℂ) * gaussInt (cpoly p * (X j * coreD j p))
          + gaussInt (cpoly (coreD j p) * (harmPoly * coreD j p)))
      = 2 * gaussInt (cpoly (coreD j p) * (harmPoly * coreD j p))
        - (1 / 2 : ℂ) * gaussInt (cpoly p * p) := by
    intro j
    have h := gaussInt_cross j p
    linear_combination (1 / 2 : ℂ) * h
  simp only [hstep]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

theorem two_re_inner_kin_harm_ge (p : MvPolynomial (Fin d) ℂ) :
    -((d : ℝ) / 2) * ‖pgLp p‖ ^ 2
      ≤ 2 * (inner ℂ (pgLp (kinPoly p)) (pgLp (harmPoly * p)) : ℂ).re := by
  set A : ℂ := (inner ℂ (pgLp (kinPoly p)) (pgLp (harmPoly * p)) : ℂ) with hAdef
  set R : ℝ := ∑ j : Fin d, (∑ k : Fin d, ‖pgLp (X k * coreD j p)‖ ^ 2) / 4 with hRdef
  have hR : 0 ≤ R := by
    rw [hRdef]; positivity
  have hA : A = gaussInt (cpoly (kinPoly p) * (harmPoly * p)) := inner_pgLp_pgLp _ _
  have hB : (inner ℂ (pgLp (harmPoly * p)) (pgLp (kinPoly p)) : ℂ)
      = gaussInt (cpoly (harmPoly * p) * kinPoly p) := inner_pgLp_pgLp _ _
  have hconj : gaussInt (cpoly (harmPoly * p) * kinPoly p) = (starRingEnd ℂ) A := by
    rw [← hB, hAdef, inner_conj_symm]
  have key := gaussInt_anticommutator p
  rw [← hA, hconj, Complex.add_conj, gaussInt_self] at key
  simp only [gaussInt_harm_self] at key
  have hcast :
      (2 : ℂ) * (∑ j : Fin d, (((∑ k : Fin d, ‖pgLp (X k * coreD j p)‖ ^ 2) / 4 : ℝ) : ℂ))
        - ((d : ℂ) / 2) * ((‖pgLp p‖ ^ 2 : ℝ) : ℂ)
      = (((2 * R - (d : ℝ) / 2 * ‖pgLp p‖ ^ 2 : ℝ)) : ℂ) := by
    rw [hRdef]
    push_cast
    ring
  rw [hcast] at key
  have hreal : 2 * A.re = 2 * R - (d : ℝ) / 2 * ‖pgLp p‖ ^ 2 := by exact_mod_cast key
  linarith

theorem norm_sq_harmPoly_mul_le (p : MvPolynomial (Fin d) ℂ) :
    ‖pgLp (harmPoly * p)‖ ^ 2
      ≤ ‖pgLp (kinPoly p + harmPoly * p)‖ ^ 2 + ((d : ℝ) / 2) * ‖pgLp p‖ ^ 2 := by
  have hadd : pgLp (kinPoly p + harmPoly * p) = pgLp (kinPoly p) + pgLp (harmPoly * p) := by
    rw [← pgMap_apply, ← pgMap_apply, ← pgMap_apply, map_add]
  have hre : RCLike.re (inner ℂ (pgLp (kinPoly p)) (pgLp (harmPoly * p)) : ℂ)
      = (inner ℂ (pgLp (kinPoly p)) (pgLp (harmPoly * p)) : ℂ).re := rfl
  rw [hadd, norm_add_sq (𝕜 := ℂ), hre]
  have h := two_re_inner_kin_harm_ge p
  nlinarith [sq_nonneg ‖pgLp (kinPoly p)‖]

theorem norm_harmPoly_mul_le (p : MvPolynomial (Fin d) ℂ) :
    ‖pgLp (harmPoly * p)‖
      ≤ ‖pgLp (kinPoly p + harmPoly * p)‖ + Real.sqrt ((d : ℝ) / 2) * ‖pgLp p‖ := by
  have hs : Real.sqrt ((d : ℝ) / 2) ^ 2 = (d : ℝ) / 2 :=
    Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ Real.sqrt ((d : ℝ) / 2) := Real.sqrt_nonneg _
  have h := norm_sq_harmPoly_mul_le p
  nlinarith [norm_nonneg (pgLp (harmPoly * p)), norm_nonneg (pgLp (kinPoly p + harmPoly * p)),
    norm_nonneg (pgLp p), mul_nonneg hs0 (norm_nonneg (pgLp p))]
end TargetQuadraticSupport
namespace BookProof.GaussCoreQuadBounds
variable {D : ℕ}
theorem pderiv_comm_poly (j k : Fin D) (p : MvPolynomial (Fin D) ℂ) :
    pderiv j (pderiv k p) = pderiv k (pderiv j p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [pderiv_mul, MvPolynomial.pderiv_X, Pi.single_apply, map_add, hp]
      split_ifs with h1 h2 h2 <;> (simp; try ring)

theorem gaussInt_re (r : MvPolynomial (Fin D) ℂ) :
    (gaussInt r).re
      = ∫ x : Vd D, (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) r).re * gaussWD x := by
  rw [gaussInt, ← Complex.reCLM_apply,
    ← ContinuousLinearMap.integral_comp_comm _ (integrable_gwFun r)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [Complex.mul_re]

theorem gaussInt_re_mono {r s : MvPolynomial (Fin D) ℂ}
    (h : ∀ x : Vd D, (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) r).re
      ≤ (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) s).re) :
    (gaussInt r).re ≤ (gaussInt s).re := by
  have hint : ∀ t : MvPolynomial (Fin D) ℂ, MeasureTheory.Integrable
      (fun x : Vd D => (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) t).re * gaussWD x) := by
    intro t
    refine ((integrable_gwFun t).re).congr (Filter.Eventually.of_forall fun x => ?_)
    simp
  rw [gaussInt_re, gaussInt_re]
  refine MeasureTheory.integral_mono (hint r) (hint s) fun x => ?_
  have hw : (0 : ℝ) ≤ gaussWD x := le_of_lt (Real.exp_pos _)
  exact mul_le_mul_of_nonneg_right (h x) hw

theorem norm_pgLp_sq (q : MvPolynomial (Fin D) ℂ) :
    ‖pgLp q‖ ^ 2 = (gaussInt (cpoly q * q)).re := by
  rw [← inner_pgLp_pgLp q q]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) (pgLp q)).symm

theorem coreD_comm (j k : Fin D) (p : MvPolynomial (Fin D) ℂ) :
    coreD j (coreD k p) = coreD k (coreD j p) := by
  simp only [coreD, map_sub, pderiv_mul, pderiv_C, pderiv_X, mul_sub]
  rw [pderiv_comm_poly j k p]
  simp only [Pi.single_apply]
  by_cases hjk : j = k
  · subst hjk; ring
  · rw [if_neg hjk, if_neg (Ne.symm hjk)]
    ring

theorem coreD_mul (j : Fin D) (f p : MvPolynomial (Fin D) ℂ) :
    coreD j (f * p) = pderiv j f * p + f * coreD j p := by
  simp only [coreD, pderiv_mul, mul_sub]
  ring

theorem coreD_sq_mul (j : Fin D) (f p : MvPolynomial (Fin D) ℂ) :
    coreD j (coreD j (f * p))
      = pderiv j (pderiv j f) * p + (2 : ℂ) • (pderiv j f * coreD j p)
        + f * coreD j (coreD j p) := by
  rw [coreD_mul, coreD_add, coreD_mul, coreD_mul, two_smul]
  ring

theorem coreD_X_comm (j : Fin D) (p : MvPolynomial (Fin D) ℂ) :
    coreD j (X j * p) - X j * coreD j p = p := by
  rw [coreD_mul, pderiv_X_self]
  ring

theorem quadForm_harm_eq (p : MvPolynomial (Fin D) ℂ) :
    quadForm harmCore ⟨pgLp p, pgLp_mem_core p⟩
      = ∑ j : Fin D, (‖pgLp (coreD j p)‖ ^ 2 + ‖pgLp (X j * p)‖ ^ 2 / 4) := by
  have hharm : cpoly p * (harmPoly * p)
      = ∑ j : Fin D, ((1 / 4 : ℂ)) • (cpoly (X j * p) * (X j * p)) := by
    rw [harmPoly, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cpoly_mul, cpoly_X, MvPolynomial.smul_eq_C_mul]
    ring
  have hkey : gaussInt (cpoly p * (kinPoly p + harmPoly * p))
      = (∑ j : Fin D, gaussInt (cpoly (coreD j p) * coreD j p))
        + ∑ j : Fin D, (1 / 4 : ℂ) * gaussInt (cpoly (X j * p) * (X j * p)) := by
    rw [mul_add, gaussInt_add, gaussInt_kinPoly, hharm, gaussInt_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ => gaussInt_smul _ _
  rw [quadForm, harmCore_pgLp, inner_pgLp_pgLp]
  change (gaussInt (cpoly p * (kinPoly p + harmPoly * p))).re = _
  rw [hkey]
  rw [Complex.add_re, Complex.re_sum, Complex.re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [norm_pgLp_sq, norm_pgLp_sq]
  simp [Complex.mul_re]
  ring

theorem quadForm_harm_nonneg (p : MvPolynomial (Fin D) ℂ) :
    0 ≤ quadForm harmCore ⟨pgLp p, pgLp_mem_core p⟩ := by
  rw [quadForm_harm_eq]
  positivity

theorem norm_sq_le_quadForm_harm (p : MvPolynomial (Fin D) ℂ) :
    ((D : ℝ) / 2) * ‖pgLp p‖ ^ 2 ≤ quadForm harmCore ⟨pgLp p, pgLp_mem_core p⟩ := by
  have hstep : ∀ j : Fin D, ‖pgLp p‖ ^ 2 / 2
      ≤ ‖pgLp (coreD j p)‖ ^ 2 + ‖pgLp (X j * p)‖ ^ 2 / 4 := by
    intro j
    have hid : cpoly p * p
        = cpoly p * coreD j (X j * p) - cpoly (X j * p) * coreD j p := by
      have h := coreD_X_comm j p
      have hc : cpoly (X j * p) = X j * cpoly p := by rw [cpoly_mul, cpoly_X]
      rw [hc]
      calc cpoly p * p = cpoly p * (coreD j (X j * p) - X j * coreD j p) := by rw [h]
        _ = cpoly p * coreD j (X j * p) - X j * cpoly p * coreD j p := by ring
    have h1 : gaussInt (cpoly p * coreD j (X j * p))
        = -(inner ℂ (pgLp (coreD j p)) (pgLp (X j * p)) : ℂ) := by
      rw [inner_pgLp_pgLp, gaussInt_coreD j p (X j * p), neg_neg]
    have h2 : gaussInt (cpoly (X j * p) * coreD j p)
        = (inner ℂ (pgLp (X j * p)) (pgLp (coreD j p)) : ℂ) := (inner_pgLp_pgLp _ _).symm
    have hns : ‖pgLp p‖ ^ 2
        = -2 * (inner ℂ (pgLp (coreD j p)) (pgLp (X j * p)) : ℂ).re := by
      rw [norm_pgLp_sq, hid, gaussInt_sub, h1, h2]
      have hswap : (inner ℂ (pgLp (X j * p)) (pgLp (coreD j p)) : ℂ).re
          = (inner ℂ (pgLp (coreD j p)) (pgLp (X j * p)) : ℂ).re := by
        rw [← inner_conj_symm (𝕜 := ℂ) (pgLp (coreD j p)) (pgLp (X j * p)), Complex.conj_re]
      rw [Complex.sub_re, Complex.neg_re, hswap]
      ring
    have hcs : |(inner ℂ (pgLp (coreD j p)) (pgLp (X j * p)) : ℂ).re|
        ≤ ‖pgLp (coreD j p)‖ * ‖pgLp (X j * p)‖ :=
      le_trans (Complex.abs_re_le_norm _) (by
        simpa using norm_inner_le_norm (𝕜 := ℂ) (pgLp (coreD j p)) (pgLp (X j * p)))
    have habs := abs_le.mp hcs
    nlinarith [sq_nonneg (‖pgLp (coreD j p)‖ - ‖pgLp (X j * p)‖ / 2),
      norm_nonneg (pgLp (coreD j p)), norm_nonneg (pgLp (X j * p))]
  rw [quadForm_harm_eq]
  have hsum : ∑ _j : Fin D, ‖pgLp p‖ ^ 2 / 2
      ≤ ∑ j : Fin D, (‖pgLp (coreD j p)‖ ^ 2 + ‖pgLp (X j * p)‖ ^ 2 / 4) :=
    Finset.sum_le_sum fun j _ => hstep j
  have hconst : ∑ _j : Fin D, ‖pgLp p‖ ^ 2 / 2 = ((D : ℝ) / 2) * ‖pgLp p‖ ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [← hconst]
  exact hsum

theorem re_inner_symm (a b : L2d D) :
    (inner ℂ a b : ℂ).re = (inner ℂ b a : ℂ).re := by
  rw [← inner_conj_symm (𝕜 := ℂ) a b, Complex.conj_re]

theorem inner_harmP_re (p : MvPolynomial (Fin D) ℂ) :
    (inner ℂ (pgLp (harmP p)) (pgLp p) : ℂ).re
      = quadForm harmCore ⟨pgLp p, pgLp_mem_core p⟩ := by
  have h : quadForm harmCore ⟨pgLp p, pgLp_mem_core p⟩
      = (inner ℂ (pgLp p) (pgLp (harmP p)) : ℂ).re := by
    rw [quadForm, harmCore_pgLp]
    rfl
  rw [h, re_inner_symm]

theorem shiftNorm_sq (p : MvPolynomial (Fin D) ℂ) :
    shiftNorm p ^ 2 = ‖pgLp (harmP p)‖ ^ 2
      + 2 * quadForm harmCore ⟨pgLp p, pgLp_mem_core p⟩ + ‖pgLp p‖ ^ 2 := by
  rw [shiftNorm, norm_add_sq (𝕜 := ℂ)]
  simp only [RCLike.re_to_complex]
  rw [inner_harmP_re]

theorem shiftNorm_nonneg (p : MvPolynomial (Fin D) ℂ) : 0 ≤ shiftNorm p := norm_nonneg _

theorem norm_pgLp_le_shiftNorm (p : MvPolynomial (Fin D) ℂ) : ‖pgLp p‖ ≤ shiftNorm p := by
  have hsq := shiftNorm_sq p
  have hq := quadForm_harm_nonneg p
  nlinarith [norm_nonneg (pgLp p), shiftNorm_nonneg p, sq_nonneg (‖pgLp (harmP p)‖),
    norm_nonneg (pgLp (harmP p))]

theorem norm_harmP_le_shiftNorm (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (harmP p)‖ ≤ shiftNorm p := by
  have hsq := shiftNorm_sq p
  have hq := quadForm_harm_nonneg p
  nlinarith [norm_nonneg (pgLp p), shiftNorm_nonneg p, norm_nonneg (pgLp (harmP p))]

theorem dim_mul_norm_le_shiftNorm (p : MvPolynomial (Fin D) ℂ) :
    ((D : ℝ) / 2 + 1) * ‖pgLp p‖ ≤ shiftNorm p := by
  have hlow := norm_sq_le_quadForm_harm p
  have hcs : (inner ℂ (pgLp p) (pgLp (harmP p) + pgLp p) : ℂ).re
      ≤ ‖pgLp p‖ * shiftNorm p := by
    refine le_trans (Complex.re_le_norm _) ?_
    simpa [shiftNorm] using norm_inner_le_norm (𝕜 := ℂ) (pgLp p) (pgLp (harmP p) + pgLp p)
  have hexp : (inner ℂ (pgLp p) (pgLp (harmP p) + pgLp p) : ℂ).re
      = quadForm harmCore ⟨pgLp p, pgLp_mem_core p⟩ + ‖pgLp p‖ ^ 2 := by
    rw [inner_add_right, Complex.add_re, re_inner_symm (pgLp p) (pgLp (harmP p)),
      inner_harmP_re]
    congr 1
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (pgLp p)
  rcases eq_or_lt_of_le (norm_nonneg (pgLp p)) with h0 | h0
  · rw [← h0]
    simpa using shiftNorm_nonneg p
  · have hkey : ((D : ℝ) / 2 + 1) * ‖pgLp p‖ ^ 2 ≤ ‖pgLp p‖ * shiftNorm p := by
      rw [hexp] at hcs
      nlinarith
    exact le_of_mul_le_mul_right (by nlinarith : ((D : ℝ) / 2 + 1) * ‖pgLp p‖ * ‖pgLp p‖
      ≤ shiftNorm p * ‖pgLp p‖) h0

theorem sqrt_dim_mul_norm_le_shiftNorm (p : MvPolynomial (Fin D) ℂ) :
    Real.sqrt ((D : ℝ) / 2) * ‖pgLp p‖ ≤ shiftNorm p := by
  have hsqrt : Real.sqrt ((D : ℝ) / 2) ≤ (D : ℝ) / 2 + 1 := by
    have h1 : ((D : ℝ) / 2 + 1) = Real.sqrt (((D : ℝ) / 2 + 1) ^ 2) :=
      (Real.sqrt_sq (by positivity)).symm
    rw [h1]
    exact Real.sqrt_le_sqrt (by nlinarith [Nat.cast_nonneg (α := ℝ) D])
  refine le_trans (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)) ?_
  exact dim_mul_norm_le_shiftNorm p

theorem norm_harmPoly_mul_le_shiftNorm (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (harmPoly * p)‖ ≤ 2 * shiftNorm p := by
  have h : ‖pgLp (harmPoly * p)‖ ≤ ‖pgLp (kinPoly p + harmPoly * p)‖ + Real.sqrt ((D : ℝ) / 2) * ‖pgLp p‖ := TargetQuadraticSupport.norm_harmPoly_mul_le p
  have h1 : ‖pgLp (kinPoly p + harmPoly * p)‖ ≤ shiftNorm p := norm_harmP_le_shiftNorm p
  have h2 := sqrt_dim_mul_norm_le_shiftNorm p
  linarith

theorem norm_kinPoly_le_shiftNorm (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (kinPoly p)‖ ≤ 3 * shiftNorm p := by
  have hadd : pgLp (kinPoly p + harmPoly * p) = pgLp (kinPoly p) + pgLp (harmPoly * p) := by
    rw [← pgMap_apply, ← pgMap_apply, ← pgMap_apply, map_add]
  have heq : pgLp (kinPoly p) = pgLp (harmP p) - pgLp (harmPoly * p) := by
    rw [harmP, hadd]
    abel
  have h1 : ‖pgLp (harmP p)‖ ≤ shiftNorm p := norm_harmP_le_shiftNorm p
  have h2 : ‖pgLp (harmPoly * p)‖ ≤ 2 * shiftNorm p := norm_harmPoly_mul_le_shiftNorm p
  calc ‖pgLp (kinPoly p)‖ = ‖pgLp (harmP p) - pgLp (harmPoly * p)‖ := by rw [heq]
    _ ≤ ‖pgLp (harmP p)‖ + ‖pgLp (harmPoly * p)‖ := norm_sub_le _ _
    _ ≤ 3 * shiftNorm p := by linarith

theorem gaussInt_self (q : MvPolynomial (Fin D) ℂ) :
    gaussInt (cpoly q * q) = ((‖pgLp q‖ ^ 2 : ℝ) : ℂ) := by
  rw [← inner_pgLp_pgLp q q, inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (pgLp q)]
  norm_cast

theorem cpoly_real_smul (c : ℝ) (q : MvPolynomial (Fin D) ℂ) :
    cpoly (((c : ℝ) : ℂ) • q) = ((c : ℝ) : ℂ) • cpoly q := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, cpoly_mul, cpoly_C,
    Complex.conj_ofReal]

theorem gaussInt_coreD_sq_pair (j k : Fin D) (p : MvPolynomial (Fin D) ℂ) :
    gaussInt (cpoly (coreD j (coreD j p)) * coreD k (coreD k p))
      = ((‖pgLp (coreD k (coreD j p))‖ ^ 2 : ℝ) : ℂ) := by
  have hcomm : coreD j (coreD k (coreD k p)) = coreD k (coreD k (coreD j p)) := by
    rw [coreD_comm j k (coreD k p), coreD_comm j k p]
  have h1 : gaussInt (cpoly (coreD j (coreD j p)) * coreD k (coreD k p))
      = -gaussInt (cpoly (coreD j p) * coreD j (coreD k (coreD k p))) :=
    gaussInt_coreD j (coreD j p) (coreD k (coreD k p))
  have h2 : gaussInt (cpoly (coreD k (coreD j p)) * coreD k (coreD j p))
      = -gaussInt (cpoly (coreD j p) * coreD k (coreD k (coreD j p))) :=
    gaussInt_coreD k (coreD j p) (coreD k (coreD j p))
  rw [h1, hcomm, ← h2, gaussInt_self]

theorem norm_weighted_kin_sq (c : Fin D → ℝ) (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (∑ j : Fin D, ((c j : ℝ) : ℂ) • coreD j (coreD j p))‖ ^ 2
      = ∑ j : Fin D, ∑ k : Fin D, c j * c k * ‖pgLp (coreD k (coreD j p))‖ ^ 2 := by
  have hexp : cpoly (∑ j : Fin D, ((c j : ℝ) : ℂ) • coreD j (coreD j p))
        * (∑ k : Fin D, ((c k : ℝ) : ℂ) • coreD k (coreD k p))
      = ∑ j : Fin D, ∑ k : Fin D, (((c j * c k : ℝ) : ℂ))
          • (cpoly (coreD j (coreD j p)) * coreD k (coreD k p)) := by
    rw [cpoly_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cpoly_real_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [MvPolynomial.smul_eq_C_mul, Complex.ofReal_mul, map_mul]
    ring
  rw [norm_pgLp_sq, hexp, gaussInt_sum]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gaussInt_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [gaussInt_smul, gaussInt_coreD_sq_pair, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem norm_weighted_kin_le {kappa : Fin D → ℝ} {km : ℝ} (hkm : 0 ≤ km)
    (hk : ∀ j, |kappa j| ≤ km) (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (∑ j : Fin D, ((kappa j : ℝ) : ℂ) • coreD j (coreD j p))‖
      ≤ km * ‖pgLp (kinPoly p)‖ := by
  have hkin : ‖pgLp (kinPoly p)‖ ^ 2
      = ∑ j : Fin D, ∑ k : Fin D, ‖pgLp (coreD k (coreD j p))‖ ^ 2 := by
    have h := norm_weighted_kin_sq (fun _ => (1 : ℝ)) p
    have hsum : (∑ j : Fin D, (((1 : ℝ) : ℂ)) • coreD j (coreD j p)) = -kinPoly p := by
      rw [kinPoly, neg_neg]
      exact Finset.sum_congr rfl fun j _ => by simp
    rw [hsum] at h
    have hneg : pgLp (-kinPoly p) = -pgLp (kinPoly p) := by
      rw [← pgMap_apply, ← pgMap_apply, map_neg]
    rw [hneg, norm_neg] at h
    simpa using h
  have hbound : ‖pgLp (∑ j : Fin D, ((kappa j : ℝ) : ℂ) • coreD j (coreD j p))‖ ^ 2
      ≤ (km * ‖pgLp (kinPoly p)‖) ^ 2 := by
    rw [norm_weighted_kin_sq, mul_pow, hkin, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have hjk : kappa j * kappa k ≤ km ^ 2 := by
      have h1 := abs_le.mp (hk j)
      have h2 := abs_le.mp (hk k)
      nlinarith
    exact mul_le_mul_of_nonneg_right hjk (sq_nonneg _)
  have hrhs : 0 ≤ km * ‖pgLp (kinPoly p)‖ := mul_nonneg hkm (norm_nonneg _)
  nlinarith [norm_nonneg (pgLp (∑ j : Fin D, ((kappa j : ℝ) : ℂ) • coreD j (coreD j p)))]
end BookProof.GaussCoreQuadBounds

variable {D : ℕ}
open BookProof.GaussCoreQuadBounds
theorem solution (q : MvPolynomial (Fin D) ℂ) :
    gaussInt (cpoly q * q) = ((‖pgLp q‖ ^ 2 : ℝ) : ℂ) := by
  rw [← inner_pgLp_pgLp q q, inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (pgLp q)]
  norm_cast
#print axioms solution
