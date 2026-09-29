-- Prove2me | solution 2 for BookProof.SqSumFarisLavine.commPoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:25:56.841944+00:00
-- url     : https://prove2.me/submissions/c30350e9-bd0d-4a14-be6f-97820b8f46be

import Mathlib
import Definitions.Def_ChapterSqSumFarisLavine
import Definitions.Def_ChapterQgHermiteOscillatorEsa
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory Complex MvPolynomial Finset
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine
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

namespace BookProof.YangMillsHermite
variable {d : ℕ}
@[simp] theorem mulOp_apply (f p : MvPolynomial (Fin d) ℂ) : mulOp f p = f * p := rfl
theorem momOp_apply (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momOp j p = (-Complex.I) • (pderiv j p - ((1 / 2 : ℝ) : ℂ) • (X j * p)) := rfl
end BookProof.YangMillsHermite
namespace BookProof.GaussCoreQuadBounds
variable {D : ℕ}
theorem eval_cpoly_self_re (q : MvPolynomial (Fin D) ℂ) (x : Vd D) :
    (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (cpoly q * q)).re
      = ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q‖ ^ 2 := by
  rw [map_mul, ← conj_polyEval]
  set z := MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q with hz
  rw [Complex.mul_re]
  simp [Complex.norm_eq_sqrt_sq_add_sq]
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ z.re ^ 2 + z.im ^ 2 by positivity)]

theorem norm_mul_le_of_pointwise {f g : MvPolynomial (Fin D) ℂ} {lam : ℝ} (hlam : 0 ≤ lam)
    (h : ∀ x : Vd D, ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) f‖
      ≤ lam * ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) g‖)
    (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (f * p)‖ ≤ lam * ‖pgLp (g * p)‖ := by
  have hsq : ‖pgLp (f * p)‖ ^ 2 ≤ (lam * ‖pgLp (g * p)‖) ^ 2 := by
    have hmono : (gaussInt (cpoly (f * p) * (f * p))).re
        ≤ (gaussInt ((((lam ^ 2 : ℝ)) : ℂ) • (cpoly (g * p) * (g * p)))).re := by
      refine gaussInt_re_mono fun x => ?_
      have hval : (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
            (MvPolynomial.C (((lam ^ 2 : ℝ) : ℂ)) * (cpoly (g * p) * (g * p)))).re
          = lam ^ 2 * ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (g * p)‖ ^ 2 := by
        rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, Complex.re_ofReal_mul,
          eval_cpoly_self_re]
      rw [eval_cpoly_self_re, MvPolynomial.smul_eq_C_mul, hval]
      have hf := h x
      have hp : (0 : ℝ) ≤ ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖ := norm_nonneg _
      have hg : (0 : ℝ) ≤ ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) g‖ := norm_nonneg _
      have hff : (0 : ℝ) ≤ ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) f‖ := norm_nonneg _
      rw [map_mul, map_mul, norm_mul, norm_mul, mul_pow, mul_pow]
      have : ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) f‖ ^ 2
          ≤ lam ^ 2 * ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) g‖ ^ 2 := by
        nlinarith
      nlinarith [sq_nonneg (‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖)]
    rw [gaussInt_smul, Complex.re_ofReal_mul] at hmono
    rw [norm_pgLp_sq, mul_pow, norm_pgLp_sq]
    exact hmono
  have hrhs : 0 ≤ lam * ‖pgLp (g * p)‖ := mul_nonneg hlam (norm_nonneg _)
  nlinarith [norm_nonneg (pgLp (f * p))]

theorem eval_harmPoly (x : Vd D) : MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (harmPoly (d := D)) = ((BookProof.QgHermiteOscillator.harmW x : ℝ) : ℂ) := BookProof.QgHermiteOscillator.eval_harmPoly x
end BookProof.GaussCoreQuadBounds
end
noncomputable section
open MeasureTheory Complex MvPolynomial Finset
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs BookProof.FarisLavine
open BookProof.QgHermiteOscillator (harmW)
namespace BookProof.SqSumFarisLavine
open BookProof.GaussCoreQuadBounds
variable {D : ℕ} {R : Type*} [Fintype R]
theorem sqSumPoly_apply (kappa : Fin D → ℝ) (v : R → Fin D → ℝ)
    (p : MvPolynomial (Fin D) ℂ) :
    sqSumPoly kappa v p = kinPart kappa p + potPoly v * p := by
  have hmom : ∀ (j : Fin D) (q : MvPolynomial (Fin D) ℂ),
      YangMillsHermite.momOp j q = (-Complex.I) • coreD j q := by
    intro j q
    have hc : coreD j q = pderiv j q - ((1 / 2 : ℝ) : ℂ) • (X j * q) := by
      rw [coreD, MvPolynomial.smul_eq_C_mul]
      norm_num
    rw [YangMillsHermite.momOp_apply, hc]
  have hsq : ∀ j : Fin D, YangMillsHermite.momOp j (YangMillsHermite.momOp j p)
      = -(coreD j (coreD j p)) := by
    intro j
    rw [hmom, hmom, coreD_smul, smul_smul]
    rw [show (-Complex.I) * (-Complex.I) = (-1 : ℂ) by
      rw [neg_mul_neg, Complex.I_mul_I]]
    rw [neg_one_smul]
  have hlhs : sqSumPoly kappa v p
      = ((1 / 2 : ℝ) : ℂ)
        • ((∑ j : Fin D, ((kappa j : ℝ) : ℂ)
              • YangMillsHermite.momOp j (YangMillsHermite.momOp j p))
            + ∑ r : R, linForm (v r) * (linForm (v r) * p)) := by
    simp [sqSumPoly]
  rw [hlhs, kinPart, potPoly, smul_add]
  congr 1
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsq j, smul_smul, smul_neg, ← neg_smul]
    congr 1
    push_cast
    ring
  · rw [Finset.smul_sum, smul_mul_assoc, Finset.sum_mul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [mul_assoc]

theorem eval_linForm (v : Fin D → ℝ) (x : Vd D) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (linForm v) = ((linFun v x : ℝ) : ℂ) := by
  rw [linForm, linFun, map_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Complex.ofReal_mul]

theorem eval_potPoly (v : R → Fin D → ℝ) (x : Vd D) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (potPoly v) = ((potFun v x : ℝ) : ℂ) := by
  rw [potPoly, potFun, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, map_sum,
    Complex.ofReal_mul, Complex.ofReal_sum]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_mul, eval_linForm, ← Complex.ofReal_mul, ← pow_two]

theorem potFun_nonneg (v : R → Fin D → ℝ) (x : Vd D) : 0 ≤ potFun v x := by
  rw [potFun]
  have : (0 : ℝ) ≤ ∑ r : R, (linFun (v r) x) ^ 2 :=
    Finset.sum_nonneg fun r _ => sq_nonneg _
  linarith

theorem norm_potPoly_mul_le {v : R → Fin D → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x : Vd D, potFun v x ≤ B * ‖x‖ ^ 2) (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (potPoly v * p)‖ ≤ 4 * B * ‖pgLp (harmPoly * p)‖ := by
  refine norm_mul_le_of_pointwise (by positivity) (fun x => ?_) p
  rw [eval_potPoly, eval_harmPoly, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (potFun_nonneg v x),
    abs_of_nonneg (show (0 : ℝ) ≤ harmW x by rw [harmW]; positivity), harmW]
  have := hB x
  linarith

theorem norm_sqSumPoly_le {kappa : Fin D → ℝ} {v : R → Fin D → ℝ} {km B : ℝ}
    (hkm : 0 ≤ km) (hk : ∀ j, |kappa j| ≤ km) (hB0 : 0 ≤ B)
    (hB : ∀ x : Vd D, potFun v x ≤ B * ‖x‖ ^ 2) (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (sqSumPoly kappa v p)‖ ≤ (3 / 2 * km + 8 * B) * shiftNorm p := by
  have hsplit : pgLp (sqSumPoly kappa v p)
      = pgLp (kinPart kappa p) + pgLp (potPoly v * p) := by
    rw [sqSumPoly_apply, ← pgMap_apply, ← pgMap_apply, ← pgMap_apply, map_add]
  have hkin : ‖pgLp (kinPart kappa p)‖ ≤ km / 2 * ‖pgLp (kinPoly p)‖ :=
    norm_weighted_kin_le (kappa := fun j => -(kappa j) / 2) (km := km / 2) (by linarith)
      (fun j => by
        have h := abs_le.mp (hk j)
        rw [abs_le]
        constructor <;> linarith [h.1, h.2]) p
  have h1 : ‖pgLp (kinPoly p)‖ ≤ 3 * shiftNorm p := norm_kinPoly_le_shiftNorm p
  have h2 : ‖pgLp (harmPoly * p)‖ ≤ 2 * shiftNorm p := norm_harmPoly_mul_le_shiftNorm p
  have hpot := norm_potPoly_mul_le hB0 hB p
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  nlinarith [norm_nonneg (pgLp (kinPoly p)), norm_nonneg (pgLp (harmPoly * p)),
    shiftNorm_nonneg p]

theorem coreD_sum {ι : Type*} (s : Finset ι) (j : Fin D) (f : ι → MvPolynomial (Fin D) ℂ) :
    coreD j (∑ i ∈ s, f i) = ∑ i ∈ s, coreD j (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coreD]
  | insert a s ha ih => rw [Finset.sum_insert ha, coreD_add, ih, Finset.sum_insert ha]

theorem coreD_neg (j : Fin D) (p : MvPolynomial (Fin D) ℂ) : coreD j (-p) = -coreD j p := by
  rw [show (-p) = (-1 : ℂ) • p by rw [neg_smul, one_smul], coreD_smul, neg_smul, one_smul]

theorem pderiv_linForm (v : Fin D → ℝ) (j : Fin D) :
    pderiv j (linForm v) = C ((v j : ℝ) : ℂ) := by
  rw [linForm, map_sum, Finset.sum_eq_single j]
  · rw [MvPolynomial.smul_eq_C_mul, pderiv_C_mul, pderiv_X_self, mul_one]
  · intro i _ hi
    simp [MvPolynomial.smul_eq_C_mul, pderiv_X, Ne.symm hi]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem C_two_eq : (C (2 : ℂ) : MvPolynomial (Fin D) ℂ) = 2 := by
  rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, MvPolynomial.C_eq_coe_nat]
  norm_num

theorem pderiv_potPoly (v : R → Fin D → ℝ) (k : Fin D) :
    pderiv k (potPoly v) = gradPoly v k := by
  rw [potPoly, MvPolynomial.smul_eq_C_mul, pderiv_C_mul, map_sum, gradPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [pderiv_mul, pderiv_linForm, MvPolynomial.smul_eq_C_mul,
    show (C (((1 : ℝ) / 2 : ℝ) : ℂ) : MvPolynomial (Fin D) ℂ)
        * (C ((v r k : ℝ) : ℂ) * linForm (v r) + linForm (v r) * C ((v r k : ℝ) : ℂ))
      = (C (((1 : ℝ) / 2 : ℝ) : ℂ) * C ((v r k : ℝ) : ℂ) * C (2 : ℂ)) * linForm (v r) by
      rw [C_two_eq]; ring]
  congr 1
  rw [← map_mul, ← map_mul]
  congr 1
  push_cast
  ring

theorem pderiv_gradPoly_self (v : R → Fin D → ℝ) (k : Fin D) :
    pderiv k (gradPoly v k) = C (((∑ r : R, (v r k) ^ 2 : ℝ) : ℂ)) := by
  rw [gradPoly, map_sum, Complex.ofReal_sum, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, pderiv_C_mul, pderiv_linForm, ← map_mul]
  congr 1
  push_cast
  ring

theorem pderiv_harmPoly (j : Fin D) :
    pderiv j (harmPoly (d := D)) = C (1 / 2 : ℂ) * X j := by
  rw [harmPoly, map_sum, Finset.sum_eq_single j]
  · rw [show (X j : MvPolynomial (Fin D) ℂ) ^ 2 = X j * X j by ring, pderiv_C_mul, pderiv_mul,
      pderiv_X_self, one_mul, mul_one,
      show (X j + X j : MvPolynomial (Fin D) ℂ) = C (2 : ℂ) * X j by rw [C_two_eq]; ring,
      ← mul_assoc, ← map_mul]
    norm_num
  · intro i _ hi
    rw [show (X i : MvPolynomial (Fin D) ℂ) ^ 2 = X i * X i by ring, pderiv_C_mul, pderiv_mul,
      pderiv_X]
    simp [Ne.symm hi]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem pderiv_pderiv_harmPoly (j : Fin D) :
    pderiv j (pderiv j (harmPoly (d := D))) = C (1 / 2 : ℂ) := by
  rw [pderiv_harmPoly, pderiv_C_mul, pderiv_X_self, mul_one]

theorem kin_mul_comm (c : Fin D → ℂ) (f p : MvPolynomial (Fin D) ℂ) :
    (∑ j : Fin D, c j • coreD j (coreD j (f * p))) - f * ∑ j : Fin D, c j • coreD j (coreD j p)
      = ∑ j : Fin D, c j • (pderiv j (pderiv j f) * p
          + (2 : ℂ) • (pderiv j f * coreD j p)) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coreD_sq_mul, mul_smul_comm, ← smul_sub]
  congr 1
  abel

theorem kin_kin_comm (c : Fin D → ℂ) (p : MvPolynomial (Fin D) ℂ) :
    (∑ k : Fin D, coreD k (coreD k (∑ j : Fin D, c j • coreD j (coreD j p))))
      = ∑ j : Fin D, c j • coreD j (coreD j (∑ k : Fin D, coreD k (coreD k p))) := by
  have hswap : ∀ (j k : Fin D) (q : MvPolynomial (Fin D) ℂ),
      coreD k (coreD k (coreD j (coreD j q))) = coreD j (coreD j (coreD k (coreD k q))) := by
    intro j k q
    calc coreD k (coreD k (coreD j (coreD j q)))
        = coreD k (coreD j (coreD k (coreD j q))) := by rw [coreD_comm k j (coreD j q)]
      _ = coreD j (coreD k (coreD k (coreD j q))) := coreD_comm k j (coreD k (coreD j q))
      _ = coreD j (coreD k (coreD j (coreD k q))) := by rw [coreD_comm k j q]
      _ = coreD j (coreD j (coreD k (coreD k q))) := by rw [coreD_comm k j (coreD k q)]
  calc (∑ k : Fin D, coreD k (coreD k (∑ j : Fin D, c j • coreD j (coreD j p))))
      = ∑ k : Fin D, ∑ j : Fin D, c j • coreD k (coreD k (coreD j (coreD j p))) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [coreD_sum, coreD_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [coreD_smul, coreD_smul]
    _ = ∑ j : Fin D, ∑ k : Fin D, c j • coreD j (coreD j (coreD k (coreD k p))) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
          rw [hswap j k p]
    _ = ∑ j : Fin D, c j • coreD j (coreD j (∑ k : Fin D, coreD k (coreD k p))) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [coreD_sum, coreD_sum, Finset.smul_sum]

theorem commPoly_eq (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) (p : MvPolynomial (Fin D) ℂ) :
    commPoly kappa v p
      = ((commConst kappa v : ℝ) : ℂ) • p
        + (∑ j : Fin D, ((-(kappa j) / 2 : ℝ) : ℂ) • (X j * coreD j p))
        + (2 : ℂ) • ∑ k : Fin D, gradPoly v k * coreD k p := by
  classical
  set c : Fin D → ℂ := fun j => ((-(kappa j) / 2 : ℝ) : ℂ) with hcdef
  -- the two second-order parts, as functions of a polynomial
  have hKadd : ∀ u w : MvPolynomial (Fin D) ℂ,
      (∑ j : Fin D, c j • coreD j (coreD j (u + w)))
        = (∑ j : Fin D, c j • coreD j (coreD j u))
          + ∑ j : Fin D, c j • coreD j (coreD j w) := by
    intro u w
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [coreD_add, coreD_add, smul_add]
  have hKneg : ∀ u : MvPolynomial (Fin D) ℂ,
      (∑ j : Fin D, c j • coreD j (coreD j (-u)))
        = -∑ j : Fin D, c j • coreD j (coreD j u) := by
    intro u
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [coreD_neg, coreD_neg, smul_neg]
  have hLadd : ∀ u w : MvPolynomial (Fin D) ℂ,
      (∑ k : Fin D, coreD k (coreD k (u + w)))
        = (∑ k : Fin D, coreD k (coreD k u)) + ∑ k : Fin D, coreD k (coreD k w) := by
    intro u w
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [coreD_add, coreD_add]
  -- the harmonic commutator
  have gKW : (∑ j : Fin D, c j • coreD j (coreD j (harmPoly * p)))
        - harmPoly * ∑ j : Fin D, c j • coreD j (coreD j p)
      = (∑ j : Fin D, c j * (1 / 2 : ℂ)) • p
        + ∑ j : Fin D, c j • (X j * coreD j p) := by
    rw [kin_mul_comm c harmPoly p, Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h2mul : (2 : ℂ) • (C (1 / 2 : ℂ) * X j * coreD j p) = X j * coreD j p := by
      rw [MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← mul_assoc, ← map_mul]
      norm_num
    rw [pderiv_pderiv_harmPoly, pderiv_harmPoly, h2mul, smul_add,
      ← MvPolynomial.smul_eq_C_mul, smul_smul]
  -- the potential commutator
  have gLV : (∑ k : Fin D, coreD k (coreD k (potPoly v * p)))
        - potPoly v * ∑ k : Fin D, coreD k (coreD k p)
      = ((∑ k : Fin D, ((∑ r : R, (v r k) ^ 2 : ℝ) : ℂ))) • p
        + (2 : ℂ) • ∑ k : Fin D, gradPoly v k * coreD k p := by
    have h1 := kin_mul_comm (fun _ => (1 : ℂ)) (potPoly v) p
    simp only [one_smul] at h1
    rw [h1, Finset.sum_smul, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pderiv_potPoly, pderiv_gradPoly_self, ← MvPolynomial.smul_eq_C_mul]
  -- the two Laplacians commute
  have gKL := kin_kin_comm c p
  -- assemble
  have hcp : commPoly kappa v p
      = ((∑ j : Fin D, c j • coreD j (coreD j (harmPoly * p)))
          - harmPoly * ∑ j : Fin D, c j • coreD j (coreD j p))
        + ((∑ k : Fin D, coreD k (coreD k (potPoly v * p)))
          - potPoly v * ∑ k : Fin D, coreD k (coreD k p)) := by
    rw [commPoly, sqSumPoly_apply, sqSumPoly_apply, harmP, harmP, kinPoly, kinPoly, kinPart,
      kinPart, hKadd, hKneg, hLadd]
    rw [← gKL]
    ring
  rw [hcp, gKW, gLV]
  have hconst : ((commConst kappa v : ℝ) : ℂ)
      = (∑ j : Fin D, c j * (1 / 2 : ℂ)) + ∑ k : Fin D, ((∑ r : R, (v r k) ^ 2 : ℝ) : ℂ) := by
    rw [commConst, hcdef]
    push_cast
    rw [Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · exact Finset.sum_comm
  rw [hconst, add_smul]
  abel

theorem abs_im_gaussInt_le (q w : MvPolynomial (Fin D) ℂ) :
    |(gaussInt (cpoly q * w)).im| ≤ ‖pgLp q‖ * ‖pgLp w‖ := by
  rw [← inner_pgLp_pgLp]
  exact le_trans (Complex.abs_im_le_norm _) (norm_inner_le_norm (𝕜 := ℂ) _ _)

end BookProof.SqSumFarisLavine

open _root_.BookProof.SqSumFarisLavine

open Finset MvPolynomial
open _root_.BookProof.HermiteProductCore _root_.BookProof.QgHermiteCore _root_.BookProof.QgHermiteFriedrichs
open _root_.BookProof.FarisLavine
open _root_.BookProof.GaussCoreQuadBounds

variable {D : ℕ} {R : Type*} [Fintype R]

theorem solution (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) (p : MvPolynomial (Fin D) ℂ) :
    commPoly kappa v p
      = ((commConst kappa v : ℝ) : ℂ) • p
        + (∑ j : Fin D, ((-(kappa j) / 2 : ℝ) : ℂ) • (X j * coreD j p))
        + (2 : ℂ) • ∑ k : Fin D, gradPoly v k * coreD k p := by
  exact BookProof.SqSumFarisLavine.commPoly_eq kappa v p

#print axioms solution
