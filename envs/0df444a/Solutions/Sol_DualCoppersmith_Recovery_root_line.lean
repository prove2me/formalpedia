-- Prove2me | solution 1 for DualCoppersmith.Recovery.root_line
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T21:30:06.407879+00:00
-- url     : https://prove2.me/submissions/ea157fe4-01e8-4c04-b827-0f454b0acd65

import Mathlib
import Definitions.Def_DualCoppersmith_Recovery_Lattice

section
set_option autoImplicit false

namespace DualCoppersmith.Dev.RootLine

open DualCoppersmith.Recovery LLLFactor.RedBasis

variable (I : Instance) (P : Parameters I)

theorem boundMonomial_pos (j : Fin (dimension I P)) : 0 < boundMonomial I P j := by
  unfold boundMonomial
  exact Finset.prod_pos fun i _ => pow_pos (I.X_pos i) _

theorem boundMonomial_dvd_rho (j : Fin (dimension I P)) : boundMonomial I P j ∣ rho I P :=
  Finset.dvd_lcm (Finset.mem_univ j)

theorem rho_pos : 0 < rho I P := by
  have h : rho I P ≠ 0 := by
    intro h0
    obtain ⟨j, _, hj⟩ := (Finset.lcm_eq_zero_iff.mp h0)
    exact (boundMonomial_pos I P j).ne' hj
  omega

theorem exponent_constantIndex : exponent I P (constantIndex I P) = 0 := by
  ext i
  simp [exponent, constantIndex, multiIndex]

theorem boundMonomial_constantIndex : boundMonomial I P (constantIndex I P) = 1 := by
  simp [boundMonomial, exponent_constantIndex]

theorem monomialRoot_constantIndex (r : Fin I.ell → ℤ) :
    monomialRoot I P r (constantIndex I P) = 1 := by
  simp [monomialRoot, exponent_constantIndex]

theorem diagonalFactor_constantIndex : diagonalFactor I P (constantIndex I P) = rho I P := by
  simp [diagonalFactor, boundMonomial_constantIndex]

theorem rootVector_apply (r : Fin I.ell → ℤ) (j : Fin (dimension I P)) :
    rootVector I P r j = (diagonalFactor I P j : ℝ) * (monomialRoot I P r j : ℝ) := by
  rfl

theorem rootVector_constantIndex (r : Fin I.ell → ℤ) :
    rootVector I P r (constantIndex I P) = (rho I P : ℝ) := by
  rw [rootVector_apply, diagonalFactor_constantIndex, monomialRoot_constantIndex]
  simp

theorem scaledLattice_apply {v : Vec (dimension I P)} (hv : v ∈ scaledLattice I P) :
    ∃ z ∈ integerKernel I P, ∀ j, v j = (diagonalFactor I P j : ℝ) * (z j : ℝ) := by
  obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := hv
  exact ⟨z, hz, fun j => rfl⟩

theorem scaledLattice_constantIndex {v : Vec (dimension I P)} (hv : v ∈ scaledLattice I P) :
    ∃ k : ℤ, v (constantIndex I P) = (rho I P : ℝ) * (k : ℝ) := by
  obtain ⟨z, _, hz⟩ := scaledLattice_apply I P hv
  refine ⟨z (constantIndex I P), ?_⟩
  rw [hz, diagonalFactor_constantIndex]

/-- Every coefficient index of a polynomial with total degree ≤ t is covered. -/
theorem exists_exponent_eq (d : Fin I.ell →₀ ℕ) (hd : (d.sum fun _ e => e) ≤ P.t) :
    ∃ j, exponent I P j = d := by
  have hsum : ∑ i, d i ≤ P.t := by
    rw [Finsupp.sum_fintype] at hd
    · exact hd
    · intro; rfl
  have hle : ∀ i, d i < P.t + 1 := fun i =>
    lt_of_le_of_lt (le_trans (Finset.single_le_sum (f := fun i => d i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) hsum) (Nat.lt_succ_self _)
  refine ⟨monomialOrder I.ell P.t ⟨fun i => ⟨d i, hle i⟩, by simpa using hsum⟩, ?_⟩
  ext i
  simp [exponent, multiIndex]

theorem eval_eq_sum (r : Fin I.ell → ℤ) (f : MvPolynomial (Fin I.ell) ℤ)
    (hf : f.totalDegree ≤ P.t) :
    MvPolynomial.eval r f =
      ∑ j, MvPolynomial.coeff (exponent I P j) f * monomialRoot I P r j := by
  classical
  have hinj : Function.Injective (exponent I P) := by
    intro a b h
    unfold exponent at h
    have h1 : (monomialOrder I.ell P.t).symm a = (monomialOrder I.ell P.t).symm b := by
      apply Subtype.ext
      funext i
      apply Fin.ext
      have := congrArg (fun d : Fin I.ell →₀ ℕ => d i) h
      simpa [multiIndex] using this
    exact (monomialOrder I.ell P.t).symm.injective h1
  rw [MvPolynomial.eval_eq']
  calc ∑ d ∈ f.support, MvPolynomial.coeff d f * ∏ i, r i ^ d i
      = ∑ d ∈ Finset.univ.image (exponent I P), MvPolynomial.coeff d f * ∏ i, r i ^ d i := by
        apply Finset.sum_subset
        · intro d hd
          obtain ⟨j, hj⟩ := exists_exponent_eq I P d
            (le_trans (MvPolynomial.le_totalDegree hd) hf)
          exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
        · intro d _ hd
          rw [MvPolynomial.notMem_support_iff.mp hd]
          simp
    _ = _ := by
        rw [Finset.sum_image fun a _ b _ h => hinj h]
        rfl

theorem monomialRoot_mem_kernel (r : Fin I.ell → ℤ) (hr : IsBoundedRoot I r) :
    monomialRoot I P r ∈ integerKernel I P := by
  intro q
  have hq := q.property
  unfold shiftIndices at hq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
  obtain ⟨h1, hm, _, hdeg⟩ := hq
  have hdeg' : (shift I P q.val).totalDegree ≤ P.t := by
    unfold shift
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    rw [MvPolynomial.totalDegree_C]
    simpa using hdeg
  have key : ∑ j, coefficientMatrix I P q j * monomialRoot I P r j =
      MvPolynomial.eval r (shift I P q.val) := by
    rw [eval_eq_sum I P r _ hdeg']
    rfl
  rw [key]
  unfold shift shiftCore
  simp only [map_mul, MvPolynomial.eval_C, map_prod, map_pow]
  -- p^m ∣ p^(m-|i|) * (monomial) * ∏ F^i
  have hdvd : (I.p : ℤ) ^ (multiplicityDegree I P q.val.1) ∣
      ∏ a, (MvPolynomial.eval r (I.F a)) ^ (q.val.1 a).val := by
    have : ∏ a, ((I.p : ℤ)) ^ (q.val.1 a).val ∣
        ∏ a, (MvPolynomial.eval r (I.F a)) ^ (q.val.1 a).val :=
      Finset.prod_dvd_prod_of_dvd _ _ fun a _ => pow_dvd_pow_of_dvd (hr.2 a) _
    rwa [Finset.prod_pow_eq_pow_sum] at this
  have : (I.p : ℤ) ^ P.m = (I.p : ℤ) ^ (P.m - multiplicityDegree I P q.val.1) *
      (I.p : ℤ) ^ (multiplicityDegree I P q.val.1) := by
    rw [← pow_add]; congr 1; omega
  rw [this]
  exact dvd_trans (mul_dvd_mul_left _ hdvd) (mul_dvd_mul_left _ (dvd_mul_left _ _))

theorem rootVector_mem (r : Fin I.ell → ℤ) (hr : IsBoundedRoot I r) :
    rootVector I P r ∈ scaledLattice I P :=
  ⟨_, ⟨_, monomialRoot_mem_kernel I P r hr, rfl⟩, rfl⟩

theorem abs_monomialRoot_le (r : Fin I.ell → ℤ) (hr : IsBoundedRoot I r)
    (j : Fin (dimension I P)) :
    |monomialRoot I P r j| ≤ (boundMonomial I P j : ℤ) := by
  unfold monomialRoot boundMonomial
  rw [Finset.abs_prod]
  push_cast
  refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun i _ => ?_
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hr.1 i).le _

theorem norm_rootVector_le (r : Fin I.ell → ℤ) (hr : IsBoundedRoot I r) :
    ‖rootVector I P r‖ ≤ (rho I P : ℝ) * Real.sqrt (dimension I P : ℝ) := by
  have hcoord : ∀ j, ‖rootVector I P r j‖ ^ 2 ≤ (rho I P : ℝ) ^ 2 := by
    intro j
    have h1 : |(monomialRoot I P r j : ℝ)| ≤ (boundMonomial I P j : ℝ) := by
      exact_mod_cast abs_monomialRoot_le I P r hr j
    have h2 : ‖rootVector I P r j‖ ≤ (rho I P : ℝ) := by
      rw [rootVector_apply, Real.norm_eq_abs, abs_mul, Nat.abs_cast]
      calc (diagonalFactor I P j : ℝ) * |(monomialRoot I P r j : ℝ)|
          ≤ (diagonalFactor I P j : ℝ) * (boundMonomial I P j : ℝ) :=
            mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
        _ = (rho I P : ℝ) := by
            unfold diagonalFactor
            exact_mod_cast Nat.div_mul_cancel (boundMonomial_dvd_rho I P j)
    exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [EuclideanSpace.norm_eq]
  have hrho : (0 : ℝ) ≤ rho I P := Nat.cast_nonneg _
  calc Real.sqrt (∑ j, ‖rootVector I P r j‖ ^ 2)
      ≤ Real.sqrt ((rho I P : ℝ) ^ 2 * (dimension I P : ℝ)) := by
        apply Real.sqrt_le_sqrt
        calc ∑ j, ‖rootVector I P r j‖ ^ 2 ≤ ∑ _j : Fin (dimension I P), (rho I P : ℝ) ^ 2 :=
              Finset.sum_le_sum fun j _ => hcoord j
          _ = (rho I P : ℝ) ^ 2 * (dimension I P : ℝ) := by
              simp [mul_comm]
    _ = (rho I P : ℝ) * Real.sqrt (dimension I P : ℝ) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hrho]

theorem line_eq (r : Fin I.ell → ℤ) (hr : IsBoundedRoot I r) :
    (scaledLattice I P : Set (Vec (dimension I P))) ∩
      Set.range (fun c : ℝ => c • rootVector I P r) =
      Set.range (fun c : ℤ => c • rootVector I P r) := by
  ext v
  constructor
  · rintro ⟨hv, c, rfl⟩
    obtain ⟨k, hk⟩ := scaledLattice_constantIndex I P hv
    have hρ : (0 : ℝ) < rho I P := by exact_mod_cast rho_pos I P
    simp only [PiLp.smul_apply, smul_eq_mul, rootVector_constantIndex] at hk
    have hc : c = (k : ℝ) := by
      have : (rho I P : ℝ) * c = (rho I P : ℝ) * k := by rw [← hk]; ring
      exact mul_left_cancel₀ hρ.ne' this
    exact ⟨k, by rw [hc]; exact (Int.cast_smul_eq_zsmul ℝ k _).symm⟩
  · rintro ⟨c, rfl⟩
    refine ⟨Submodule.smul_mem _ c (rootVector_mem I P r hr), (c : ℝ), ?_⟩
    exact Int.cast_smul_eq_zsmul ℝ c _

end DualCoppersmith.Dev.RootLine

namespace DualCoppersmith.Recovery

/-- Lemma 3.2, printed p. 8 / PDF p. 9: all three clauses. -/
theorem chk_root_line (I : Instance) (P : Parameters I) (r : Fin I.ell → ℤ)
    (hr : IsBoundedRoot I r) :
    rootVector I P r ∈ scaledLattice I P ∧
    ((scaledLattice I P : Set (LLLFactor.RedBasis.Vec (dimension I P))) ∩
      Set.range (fun c : ℝ => c • rootVector I P r) =
      Set.range (fun c : ℤ => c • rootVector I P r)) ∧
    ‖rootVector I P r‖ ≤ (rho I P : ℝ) * Real.sqrt (dimension I P : ℝ) :=
  ⟨DualCoppersmith.Dev.RootLine.rootVector_mem I P r hr,
   DualCoppersmith.Dev.RootLine.line_eq I P r hr,
   DualCoppersmith.Dev.RootLine.norm_rootVector_le I P r hr⟩

end DualCoppersmith.Recovery

end

theorem solution : type_of% @DualCoppersmith.Recovery.chk_root_line := @DualCoppersmith.Recovery.chk_root_line
