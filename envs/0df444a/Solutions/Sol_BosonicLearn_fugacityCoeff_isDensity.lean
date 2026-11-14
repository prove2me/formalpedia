-- Prove2me | solution 1 for BosonicLearn.fugacityCoeff_isDensity
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T19:30:46.61552+00:00
-- url     : https://prove2.me/submissions/d9e73b08-b1c4-444a-8419-8d3148289a94

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Theorems.Thm_BosonicLearn_gammaFock_basic
import Theorems.Thm_BosonicLearn_gammaFock_mul
import Theorems.Thm_BosonicLearn_gammaFock_posSemidef
import Theorems.Thm_BosonicLearn_gammaFock_trace_psd

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity IsTraceClass NuclearExpansion)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.RealRegisters (Hilbert)
open scoped Matrix ComplexOrder ENNReal

open BosonicLearn

noncomputable section

/-- The photon-number sector `N`: occupation vectors of total `N`. -/
private def sec (n N : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.range (N + 1)).filter (fun w => ∑ i, w i = N)

private lemma mem_sec {n N : ℕ} (w : Fin n → ℕ) : w ∈ sec n N ↔ ∑ i, w i = N := by
  unfold sec
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h => h.2, fun h => ⟨fun k => ?_, h⟩⟩
  rw [Finset.mem_range, ← h]
  have h2 : w k ≤ ∑ i, w i :=
    Finset.single_le_sum (f := fun i => w i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  omega

private lemma gammaFock_mul_sec {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (u v : Fin n → ℕ) :
    gammaFock (A * B) u v = ∑ w ∈ sec n (∑ i, u i), gammaFock A u w * gammaFock B w v :=
  gammaFock_mul A B u v

/-- A positive semidefinite matrix has a Hermitian square root. -/
private lemma exists_hermitian_sqrt {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef) :
    ∃ S : Matrix (Fin n) (Fin n) ℂ, Sᴴ = S ∧ R = S * S := by
  open scoped MatrixOrder in
  refine ⟨CFC.sqrt R, ?_, (CFC.sqrt_mul_sqrt_self R hR.nonneg).symm⟩
  rw [← Matrix.star_eq_conjTranspose]
  exact (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg R)).star_eq

private lemma gammaFock_herm {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (hS : Sᴴ = S)
    (u v : Fin n → ℕ) : gammaFock S u v = star (gammaFock S v u) := by
  have h := (gammaFock_basic S u v).2.1
  rwa [hS] at h

/-- `Γ(S²) = ∑_w |c_w⟩⟨c_w|` with `c_w` the `w`-th column of `Γ(S)`, for Hermitian `S`. -/
private lemma gammaFock_sq {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (hS : Sᴴ = S)
    (u v : Fin n → ℕ) :
    gammaFock (S * S) u v = ∑ w ∈ sec n (∑ i, u i), gammaFock S u w * star (gammaFock S v w) := by
  rw [gammaFock_mul_sec]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [gammaFock_herm S hS w v]

/-! ### Finitely supported vectors of `ℓ²` -/

/-- The vector with coordinates `g i` for `i ∈ F` and `0` elsewhere. -/
private def finVec {n : ℕ} (F : Finset (Fin n → ℕ)) (g : (Fin n → ℕ) → ℂ) : Hilbert (Fin n → ℕ) :=
  ∑ i ∈ F, lp.single 2 i (g i)

private lemma fin_apply {n : ℕ} (F : Finset (Fin n → ℕ)) (g : (Fin n → ℕ) → ℂ) (j : Fin n → ℕ) :
    finVec F g j = if j ∈ F then g j else 0 := by
  unfold finVec
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.single_apply]
  exact Finset.sum_pi_single j (fun i => g i) F

private lemma norm_fin_sq {n : ℕ} (F : Finset (Fin n → ℕ)) (g : (Fin n → ℕ) → ℂ) :
    ‖finVec F g‖ ^ 2 = ∑ i ∈ F, ‖g i‖ ^ 2 := by
  have h := lp.norm_sum_single (p := (2 : ℝ≥0∞)) (E := fun _ : Fin n → ℕ => ℂ) (by norm_num) g F
  simpa [finVec] using h

/-- The `w`-th column of `Γ(S)`, a finitely supported vector. -/
private def col {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℕ) : Hilbert (Fin n → ℕ) :=
  finVec (sec n (∑ i, w i)) (fun u => gammaFock S u w)

private lemma col_apply {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (w u : Fin n → ℕ) :
    col S w u = gammaFock S u w := by
  unfold col
  rw [fin_apply]
  split_ifs with h
  · rfl
  · rw [mem_sec] at h
    exact ((gammaFock_basic S u w).1 h).symm

private lemma norm_col_sq {n : ℕ} (S : Matrix (Fin n) (Fin n) ℂ) (hS : Sᴴ = S) (w : Fin n → ℕ) :
    ‖col S w‖ ^ 2 = (gammaFock (S * S) w w).re := by
  unfold col
  rw [norm_fin_sq, gammaFock_sq S hS, Complex.re_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [gammaFock_herm S hS u w, norm_star, Complex.star_def, Complex.mul_conj,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- A countable rank-one family with summable weights gives a nuclear expansion. -/
private lemma isTraceClass_of_family {I ι : Type} [Countable ι] {X : Matrix I I ℂ}
    (L R : ι → Hilbert I) (hw : Summable fun a => ‖L a‖ * ‖R a‖)
    (hX : ∀ i j, HasSum (fun a => L a i * star (R a j)) (X i j)) : IsTraceClass X := by
  obtain ⟨g, hg⟩ := exists_injective_nat ι
  have key1 : (fun k => ‖Function.extend g L 0 k‖ * ‖Function.extend g R 0 k‖) =
      Function.extend g (fun a => ‖L a‖ * ‖R a‖) 0 := by
    funext k
    by_cases hk : ∃ a, g a = k
    · obtain ⟨a, rfl⟩ := hk
      simp [hg.extend_apply]
    · simp [Function.extend_apply' _ _ _ hk]
  have key2 : ∀ i j, (fun k => (Function.extend g L 0 k) i * star ((Function.extend g R 0 k) j)) =
      Function.extend g (fun a => L a i * star (R a j)) 0 := by
    intro i j
    funext k
    by_cases hk : ∃ a, g a = k
    · obtain ⟨a, rfl⟩ := hk
      simp [hg.extend_apply]
    · simp [Function.extend_apply' _ _ _ hk]
  exact ⟨{ left := Function.extend g L 0
           right := Function.extend g R 0
           summable := by
             rw [key1]
             exact (summable_extend_zero hg).mpr hw
           coefficients := by
             intro i j
             rw [key2 i j, tsum_extend_zero hg]
             exact (hX i j).tsum_eq.symm }⟩

theorem solution {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) (hR : R.PosSemidef)
    (hR1 : (1 - R).PosDef) : IsDensity (fugacityCoeff R) := by
  obtain ⟨hpos, him, htr⟩ := gammaFock_trace_psd R hR hR1
  obtain ⟨r, hr⟩ : ∃ r : ℝ, (1 - R).det = (r : ℂ) :=
    ⟨((1 - R).det).re, Complex.ext (by simp) (by simp [him])⟩
  have hr0 : 0 < r := by
    rw [hr, Complex.ofReal_re] at hpos
    exact hpos
  have hentry : ∀ u v, fugacityCoeff R u v = (r : ℂ) * gammaFock R u v := by
    intro u v
    unfold fugacityCoeff
    rw [Matrix.smul_apply, smul_eq_mul, hr]
  refine ⟨?_, ?_, ?_⟩
  · -- trace class
    obtain ⟨S, hS, hRS⟩ := exists_hermitian_sqrt R hR
    refine isTraceClass_of_family (ι := Fin n → ℕ) (fun w => (r : ℂ) • col S w) (fun w => col S w)
      ?_ ?_
    · have h1 : Summable fun w : Fin n → ℕ => (gammaFock R w w).re :=
        (Complex.hasSum_re htr).summable
      refine (h1.mul_left r).congr fun w => ?_
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hr0.le, mul_assoc, ← pow_two,
        norm_col_sq S hS, ← hRS]
    · intro u v
      have hzero : ∀ w ∉ sec n (∑ i, u i),
          ((r : ℂ) • col S w) u * star (col S w v) = 0 := by
        intro w hw
        rw [mem_sec] at hw
        rw [lp.coeFn_smul, Pi.smul_apply, col_apply, (gammaFock_basic S u w).1 (Ne.symm hw)]
        simp
      have h : HasSum (fun w : Fin n → ℕ => ((r : ℂ) • col S w) u * star (col S w v))
          (∑ w ∈ sec n (∑ i, u i), ((r : ℂ) • col S w) u * star (col S w v)) :=
        hasSum_sum_of_ne_finset_zero hzero
      convert h using 1
      rw [hentry, hRS, gammaFock_sq S hS, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [lp.coeFn_smul, Pi.smul_apply, col_apply, col_apply, smul_eq_mul, mul_assoc]
  · -- positivity
    intro s z
    have hq := gammaFock_posSemidef R hR s z
    have heq : ∑ u ∈ s, ∑ v ∈ s, star (z u) * fugacityCoeff R u v * z v =
        (r : ℂ) * ∑ u ∈ s, ∑ v ∈ s, star (z u) * gammaFock R u v * z v := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [hentry]
      ring
    rw [heq, Complex.im_ofReal_mul, Complex.re_ofReal_mul, hq.1, mul_zero]
    exact ⟨rfl, mul_nonneg hr0.le hq.2⟩
  · -- trace one
    have h1 : HasSum (fun u : Fin n → ℕ => (fugacityCoeff R u u).re) 1 := by
      have h := Complex.hasSum_re (htr.mul_left (r : ℂ))
      rw [hr, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr0.ne'), Complex.one_re] at h
      refine h.congr_fun fun u => ?_
      rw [hentry]
    exact ⟨h1.summable, h1.tsum_eq⟩
