-- Prove2me | solution 1 for BosonicLearn.vacuum_isGaussianState
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T18:22:34.572209+00:00
-- url     : https://prove2.me/submissions/55072cc8-94dd-4948-ac4b-fa4fc880fd0e

import Mathlib
import Definitions.Def_BosonicLearn_IsGaussianState

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize IsDensity IsTraceClass NuclearExpansion)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Support50.P14
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)
open scoped ENNReal Matrix

open BosonicLearn

noncomputable section

/-! ### Rank-one densities with finite support -/

private def finVec {I : Type} [DecidableEq I] (s : Finset I) (g : I → ℂ) : Hilbert I :=
  ∑ i ∈ s, lp.single 2 i (g i)

private lemma finVec_apply {I : Type} [DecidableEq I] (s : Finset I) (g : I → ℂ) (j : I) :
    finVec s g j = if j ∈ s then g j else 0 := by
  unfold finVec
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.single_apply]
  exact Finset.sum_pi_single j (fun i => g i) s

/-- The normalized rank-one matrix of the vector equal to `z` on `s` and `0` elsewhere. -/
private def rankOneMat {I : Type} [DecidableEq I] (s : Finset I) (z : I → ℂ) : Matrix I I ℂ :=
  fun i j => (if i ∈ s then z i else 0) * star (if j ∈ s then z j else 0) *
    (((∑ k ∈ s, ‖z k‖ ^ 2 : ℝ) : ℂ))⁻¹

private lemma rankOneMat_isDensity {I : Type} [DecidableEq I] (s : Finset I) (z : I → ℂ)
    (hN : 0 < ∑ k ∈ s, ‖z k‖ ^ 2) : IsDensity (rankOneMat s z) := by
  set N : ℝ := ∑ k ∈ s, ‖z k‖ ^ 2 with hNdef
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨⟨{
    left := fun n => if n = 0 then ((N : ℂ)⁻¹) • finVec s z else 0
    right := fun n => if n = 0 then finVec s z else 0
    summable := summable_of_ne_finset_zero (s := {0}) fun n hn => by
      have : n ≠ 0 := by simpa using hn
      simp [this]
    coefficients := ?_ }⟩, ?_, ?_⟩
  · intro i j
    rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
    simp only [if_true, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, finVec_apply, rankOneMat]
    ring
  · intro t x
    have key : ∑ i ∈ t, ∑ j ∈ t, star (x i) * rankOneMat s z i j * x j =
        ((‖∑ i ∈ t, star (x i) * (if i ∈ s then z i else 0)‖ ^ 2 * N⁻¹ : ℝ) : ℂ) := by
      set c : ℂ := ∑ i ∈ t, star (x i) * (if i ∈ s then z i else 0) with hc
      have h1 : c * star c = (‖c‖ : ℂ) ^ 2 := by
        rw [Complex.star_def, Complex.mul_conj']
      push_cast
      rw [← h1, hc, star_sum, Finset.sum_mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [rankOneMat, star_mul', star_star]
      ring
    rw [key]
    refine ⟨Complex.ofReal_im _, ?_⟩
    rw [Complex.ofReal_re]
    positivity
  · have hdiag : ∀ i, (rankOneMat s z i i).re = if i ∈ s then ‖z i‖ ^ 2 * N⁻¹ else 0 := by
      intro i
      by_cases hi : i ∈ s
      · simp only [rankOneMat, hi, if_true]
        rw [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_inv,
          ← Complex.ofReal_mul, Complex.ofReal_re]
      · simp [rankOneMat, hi]
    have hsum : HasSum (fun i => (rankOneMat s z i i).re) (∑ i ∈ s, (rankOneMat s z i i).re) :=
      hasSum_sum_of_ne_finset_zero fun i hi => by rw [hdiag, if_neg hi]
    have hval : ∑ i ∈ s, (rankOneMat s z i i).re = 1 := by
      have : ∑ i ∈ s, (rankOneMat s z i i).re = ∑ i ∈ s, ‖z i‖ ^ 2 * N⁻¹ :=
        Finset.sum_congr rfl fun i hi => by rw [hdiag, if_pos hi]
      rw [this, ← Finset.sum_mul, ← hNdef, mul_inv_cancel₀ hN.ne']
    exact ⟨hsum.summable, hsum.tsum_eq.trans hval⟩

/-! ### The vacuum array and its Weyl characteristic function -/

/-- The vacuum coefficient array. -/
private def vac (n : ℕ) : Matrix (Occupation (Fin n)) (Occupation (Fin n)) ℂ :=
  fun u v => if u = 0 ∧ v = 0 then 1 else 0

private lemma vac_isDensity (n : ℕ) : IsDensity (vac n) := by
  have h := rankOneMat_isDensity ({0} : Finset (Occupation (Fin n))) (fun _ => (1 : ℂ)) (by simp)
  have e : rankOneMat ({0} : Finset (Occupation (Fin n))) (fun _ => (1 : ℂ)) = vac n := by
    funext u v
    by_cases hu : u = 0 <;> by_cases hv : v = 0 <;> simp [rankOneMat, vac, hu, hv]
  rwa [e] at h

private lemma inner_tsum {n : ℕ} (ξ : InterleavedQuadrature (Fin n) → ℝ) (u : Occupation (Fin n)) :
    ∑' v, vac n u v * oscillatorWeylKernel ξ v u =
      if u = 0 then oscillatorWeylKernel ξ 0 0 else 0 := by
  by_cases hu : u = 0
  · subst hu
    rw [if_pos rfl, tsum_eq_single 0 (fun v hv => by simp [vac, hv])]
    simp [vac]
  · rw [if_neg hu]
    simp [vac, hu]

private lemma weyl_zero {n : ℕ} (ξ : InterleavedQuadrature (Fin n) → ℝ) :
    oscillatorWeylKernel ξ (0 : Occupation (Fin n)) 0 =
      ((Real.exp (-(∑ j, (ξ (j, 1) ^ 2 + ξ (j, 0) ^ 2)) / 4) : ℝ) : ℂ) := by
  have hD : ∀ z : ℂ, displacementMatrix z 0 0 = ((Real.exp (-Complex.normSq z / 2) : ℝ) : ℂ) := by
    intro z
    simp [displacementMatrix]
  have hz : ∀ j : Fin n, Complex.normSq ((-(ξ (j, 1) : ℂ) + Complex.I * (ξ (j, 0) : ℂ)) /
      (Real.sqrt 2 : ℂ)) = (ξ (j, 1) ^ 2 + ξ (j, 0) ^ 2) / 2 := by
    intro j
    rw [Complex.normSq_div, Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num)]
    congr 1
    simp [Complex.normSq_apply]
    ring
  unfold oscillatorWeylKernel
  simp only [Pi.zero_apply, hD, hz]
  rw [← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

private lemma char_vac {n : ℕ} (ξ : InterleavedQuadrature (Fin n) → ℝ) :
    oscillatorCharacteristic (vac n) ξ =
      ((Real.exp (-(∑ j, (ξ (j, 1) ^ 2 + ξ (j, 0) ^ 2)) / 4) : ℝ) : ℂ) := by
  unfold oscillatorCharacteristic
  simp only [inner_tsum]
  rw [tsum_eq_single 0 (fun u hu => by simp [hu]), if_pos rfl, weyl_zero]

private lemma char_vac_smul {n : ℕ} (ξ : InterleavedQuadrature (Fin n) → ℝ) (t : ℝ) :
    oscillatorCharacteristic (vac n) (t • ξ) =
      ((Real.exp (-(t ^ 2 * ∑ j, (ξ (j, 1) ^ 2 + ξ (j, 0) ^ 2)) / 4) : ℝ) : ℂ) := by
  rw [char_vac]
  have h : (∑ j, ((t • ξ) (j, 1) ^ 2 + (t • ξ) (j, 0) ^ 2)) =
      t ^ 2 * ∑ j, (ξ (j, 1) ^ 2 + ξ (j, 0) ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [h]

/-! ### The statement -/

theorem solution (n : ℕ) :
    ∃ ρ : State (Occupation (Fin n)),
      (∀ u v, ρ.coefficients u v = if u = 0 ∧ v = 0 then 1 else 0) ∧
      IsGaussianState ρ 0 ((1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ)) := by
  refine ⟨⟨vac n, vac_isDensity n⟩, fun u v => rfl, ?_⟩
  unfold IsGaussianState
  show GaussianAt (vac n) _ _
  -- the covariance in interleaved coordinates is the identity
  have hγ : ∀ a b : InterleavedQuadrature (Fin n),
      2 * ((1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))
        (if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1)
        (if b.2 = 0 then Sum.inl b.1 else Sum.inr b.1) = if a = b then 1 else 0 := by
    rintro ⟨j, k⟩ ⟨j', k'⟩
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
    fin_cases k <;> fin_cases k' <;> by_cases hj : j = j' <;> simp [hj]
  have hvar : ∀ ξ : InterleavedQuadrature (Fin n) → ℝ,
      varianceForm (fun a b => 2 * ((1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))
        (if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1)
        (if b.2 = 0 then Sum.inl b.1 else Sum.inr b.1)) ξ = ∑ j, (ξ (j, 1) ^ 2 + ξ (j, 0) ^ 2) := by
    intro ξ
    unfold varianceForm
    simp only [hγ, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fin.sum_univ_two]
    ring
  have hmean : ∀ ξ : InterleavedQuadrature (Fin n) → ℝ,
      meanForm (fun a => (0 : Fin n ⊕ Fin n → ℝ) (if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1)) ξ = 0 := by
    intro ξ
    simp [meanForm]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- finite energy
    have h0 : ∀ u : Occupation (Fin n),
        ENNReal.ofReal (∑ j, (u j : ℝ)) * ENNReal.ofReal (vac n u u).re = 0 := by
      intro u
      by_cases hu : u = 0
      · subst hu
        simp
      · simp [vac, hu]
    unfold photonEnergy
    simp only [h0, tsum_zero]
    exact ENNReal.zero_lt_top
  · -- symmetry
    apply Matrix.ext
    intro a b
    show 2 * ((1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))
        (if b.2 = 0 then Sum.inl b.1 else Sum.inr b.1)
        (if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1) =
      2 * ((1 / 2 : ℝ) • (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ))
        (if a.2 = 0 then Sum.inl a.1 else Sum.inr a.1)
        (if b.2 = 0 then Sum.inl b.1 else Sum.inr b.1)
    rw [hγ b a, hγ a b]
    by_cases h : a = b
    · subst h
      rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
  · -- summability
    intro ξ
    refine ⟨fun u => ?_, ?_⟩
    · exact summable_of_ne_finset_zero (s := {0}) fun v hv => by
        have : v ≠ 0 := by simpa using hv
        simp [vac, this]
    · simp only [inner_tsum]
      exact summable_of_ne_finset_zero (s := {0}) fun u hu => by
        have : u ≠ 0 := by simpa using hu
        simp [this]
  · -- first and second derivatives of the characteristic function
    intro ξ
    set q : ℝ := ∑ j, (ξ (j, 1) ^ 2 + ξ (j, 0) ^ 2) with hq
    have hfun : (fun t : ℝ => oscillatorCharacteristic (vac n) (t • ξ)) =
        fun t : ℝ => ((Real.exp (-(t ^ 2 * q) / 4) : ℝ) : ℂ) := funext fun t => char_vac_smul ξ t
    have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Real.exp (-(t ^ 2 * q) / 4))
        (Real.exp (-(t ^ 2 * q) / 4) * (-(t * q) / 2)) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => -(t ^ 2 * q) / 4) (-(t * q) / 2) t := by
        have h2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by
          simpa using hasDerivAt_pow 2 t
        have h3 := (h2.mul_const q).neg.div_const 4
        have e : -(2 * t * q) / 4 = -(t * q) / 2 := by ring
        rw [e] at h3
        exact h3
      exact (Real.hasDerivAt_exp _).comp t h1
    have hdc : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ((Real.exp (-(t ^ 2 * q) / 4) : ℝ) : ℂ))
        ((Real.exp (-(t ^ 2 * q) / 4) * (-(t * q) / 2) : ℝ) : ℂ) t := fun t => (hd t).ofReal_comp
    have hderiv : deriv (fun t : ℝ => ((Real.exp (-(t ^ 2 * q) / 4) : ℝ) : ℂ)) =
        fun t : ℝ => ((Real.exp (-(t ^ 2 * q) / 4) * (-(t * q) / 2) : ℝ) : ℂ) :=
      funext fun t => (hdc t).deriv
    rw [hfun, hderiv, hmean ξ, hvar ξ]
    constructor
    · have h := hdc 0
      have e : ((Real.exp (-((0 : ℝ) ^ 2 * q) / 4) * (-((0 : ℝ) * q) / 2) : ℝ) : ℂ) =
          Complex.I * ((0 : ℝ) : ℂ) := by simp
      rw [e] at h
      exact h
    · have h3 : HasDerivAt (fun t : ℝ => -(t * q) / 2) (-q / 2) 0 := by
        have h4 := ((hasDerivAt_id (0 : ℝ)).mul_const q).neg.div_const 2
        have e : -(1 * q) / 2 = -q / 2 := by ring
        rw [e] at h4
        exact h4
      have h2 := (hd 0).mul h3
      have e : Real.exp (-((0 : ℝ) ^ 2 * q) / 4) * (-((0 : ℝ) * q) / 2) * (-((0 : ℝ) * q) / 2) +
          Real.exp (-((0 : ℝ) ^ 2 * q) / 4) * (-q / 2) = -q / 2 - (0 : ℝ) ^ 2 := by simp
      rw [e] at h2
      exact h2.ofReal_comp
  · -- the characteristic function
    intro ξ
    rw [char_vac, hmean ξ, hvar ξ]
    simp
