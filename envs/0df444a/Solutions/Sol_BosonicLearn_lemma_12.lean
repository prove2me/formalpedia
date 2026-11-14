-- Prove2me | solution 1 for BosonicLearn.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T20:05:12.192185+00:00
-- url     : https://prove2.me/submissions/7b7edb38-fe86-4ab9-949e-87edff23ab51

import Mathlib
import Definitions.Def_BosonicLearn_fugacityCoeff
import Definitions.Def_BosonicLearn_fugacityFamily
import Definitions.Def_BosonicLearn_Gsupp
import Theorems.Thm_BosonicLearn_fugacityFamily_occupation_split
import Theorems.Thm_BosonicLearn_fugacity_count_pgf
import Theorems.Thm_BosonicLearn_fugacity_count_test
import Theorems.Thm_BosonicLearn_geometric_pgf_threshold
import Theorems.Thm_BosonicLearn_loewner_eigenvalue_pairing

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal Matrix ComplexOrder

open BosonicLearn

noncomputable section

/-- A Hermitian matrix of operator norm at most `c` lies between `-c` and `c` in the Loewner order. -/
private lemma opnorm_form {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (hX : X.IsHermitian) (c : ℝ)
    (h : WHMultiplicativity.schattenNorm ⊤ X ≤ c) :
    (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - X).PosSemidef ∧
      (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) + X).PosSemidef := by
  have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) X‖ ≤ c := by
    simpa [WHMultiplicativity.schattenNorm] using h
  have key : ∀ v : Fin n → ℂ, |(star v ⬝ᵥ (X *ᵥ v)).re| ≤ c * ∑ i, ‖v i‖ ^ 2 := by
    intro v
    set w : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 v with hw
    have h1 : inner ℂ w (Matrix.toEuclideanCLM (𝕜 := ℂ) X w) = star v ⬝ᵥ (X *ᵥ v) := by
      rw [hw, Matrix.toEuclideanCLM_toLp, EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
    have h2 : ‖inner ℂ w (Matrix.toEuclideanCLM (𝕜 := ℂ) X w)‖ ≤ c * ‖w‖ ^ 2 := by
      calc ‖inner ℂ w (Matrix.toEuclideanCLM (𝕜 := ℂ) X w)‖
          ≤ ‖w‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℂ) X w‖ := norm_inner_le_norm _ _
        _ ≤ ‖w‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℂ) X‖ * ‖w‖) :=
            mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
        _ ≤ ‖w‖ * (c * ‖w‖) := mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)) (norm_nonneg _)
        _ = c * ‖w‖ ^ 2 := by ring
    have h3 : ‖w‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
    rw [h1, h3] at h2
    exact (Complex.abs_re_le_norm _).trans h2
  have hsq : ∀ v : Fin n → ℂ, star v ⬝ᵥ v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    simp only [dotProduct, Pi.star_apply]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  have him : ∀ v : Fin n → ℂ, (star v ⬝ᵥ (X *ᵥ v)).im = 0 := fun v =>
    hX.im_star_dotProduct_mulVec_self v
  have hc1 : (((c : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  constructor
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hc1.sub hX) fun v => ?_
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      hsq, Complex.nonneg_iff]
    have hk := abs_le.mp (key v)
    constructor
    · simp only [Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      linarith [hk.2]
    · rw [Complex.sub_im, him v, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_im, sub_zero]
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hc1.add hX) fun v => ?_
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
      hsq, Complex.nonneg_iff]
    have hk := abs_le.mp (key v)
    constructor
    · simp only [Complex.add_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      linarith [hk.1]
    · rw [Complex.add_im, him v, smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_im, add_zero]

/-- The fugacity matrices of the hard family are admissible: `0 ⪯ R_X ≺ 1`. -/
private lemma family_psd (n : ℕ) (ν ξ : ℝ) (hν0 : 0 < ν) (hν1 : ν ≤ 1) (hξ0 : 0 < ξ)
    (hξ1 : ξ < 1 / 32) (X : Herm0 n) (hX : X ∈ Gsupp n) :
    (fugacityFamily ν ξ X).PosSemidef ∧ (1 - fugacityFamily ν ξ X).PosDef := by
  have hXh : (X : Matrix (Fin n) (Fin n) ℂ).IsHermitian := X.2.1
  have hop : WHMultiplicativity.schattenNorm ⊤ (X : Matrix (Fin n) (Fin n) ℂ) ≤ 4 := hX
  obtain ⟨hminus, hplus⟩ := opnorm_form (X : Matrix (Fin n) (Fin n) ℂ) hXh 4 hop
  have h14 : 0 < 1 - 4 * ξ := by linarith
  have h14' : 1 - 4 * ξ ≠ 0 := h14.ne'
  have h1ν : 1 + ν ≠ 0 := by positivity
  set r : ℝ := ν / ((1 - 4 * ξ) * (1 + ν)) with hr
  have hrpos : 0 < r := by positivity
  have hrt : r * (1 - 4 * ξ) = ν / (1 + ν) := by
    rw [hr]
    field_simp
  have hr1 : r * (1 + 4 * ξ) < 1 := by
    rw [hr, div_mul_eq_mul_div, div_lt_one (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hν1 hξ0.le, mul_pos hξ0 hν0]
  have hRdef : fugacityFamily ν ξ X =
      ((r : ℝ) : ℂ) • (1 + ((ξ : ℝ) : ℂ) • (X : Matrix (Fin n) (Fin n) ℂ)) := rfl
  have e1 : fugacityFamily ν ξ X - ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) =
      ((r * ξ : ℝ) : ℂ) • (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        (X : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [hRdef, ← hrt]
    ext a b
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hRν : (fugacityFamily ν ξ X -
      ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
    rw [e1]
    exact hplus.smul (Complex.zero_le_real.mpr (by positivity))
  have hRpsd : (fugacityFamily ν ξ X).PosSemidef := by
    have e : fugacityFamily ν ξ X = (fugacityFamily ν ξ X -
        ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) +
        ((ν / (1 + ν) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
      rw [sub_add_cancel]
    rw [e]
    exact hRν.add (Matrix.PosSemidef.one.smul (Complex.zero_le_real.mpr (by positivity)))
  have e2 : 1 - fugacityFamily ν ξ X =
      ((1 - r * (1 + 4 * ξ) : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) +
        ((r * ξ : ℝ) : ℂ) • (((4 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) -
          (X : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [hRdef]
    ext a b
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring
  have hR1 : (1 - fugacityFamily ν ξ X).PosDef := by
    rw [e2]
    exact (Matrix.PosDef.one.smul (by exact_mod_cast (sub_pos.mpr hr1))).add_posSemidef
      (hminus.smul (Complex.zero_le_real.mpr (by positivity)))
  exact ⟨hRpsd, hR1⟩

/-- Numerical step: `δ ≤ s`. -/
private lemma num_delta_le {c C n ν ξ k δ s2 : ℝ} (hc : 0 < c) (hC : 0 < C) (hn : 0 < n) (hν : 0 < ν)
    (hk0 : 0 ≤ k) (hkn : k ≤ n) (hξα : ξ ≤ Real.sqrt c / C / Real.sqrt (n * ν))
    (hξ0 : 0 < ξ) (hδ0 : 0 < δ) (h1 : δ ≤ C * k * ν * ξ) (h2 : c * k * ν ≤ s2) : δ ^ 2 ≤ s2 := by
  have hnνpos : 0 < n * ν := mul_pos hn hν
  have hsnν : 0 < Real.sqrt (n * ν) := Real.sqrt_pos.mpr hnνpos
  have hξ2 : ξ ^ 2 * (C ^ 2 * (n * ν)) ≤ c := by
    have h4 : ξ * Real.sqrt (n * ν) ≤ Real.sqrt c / C := by
      rwa [le_div_iff₀ hsnν] at hξα
    have h5 : ξ * Real.sqrt (n * ν) * C ≤ Real.sqrt c := by
      rwa [le_div_iff₀ hC] at h4
    have h6 : (ξ * Real.sqrt (n * ν) * C) ^ 2 ≤ Real.sqrt c ^ 2 :=
      pow_le_pow_left₀ (by positivity) h5 2
    rw [Real.sq_sqrt hc.le] at h6
    have h7 : (ξ * Real.sqrt (n * ν) * C) ^ 2 = ξ ^ 2 * (C ^ 2 * (n * ν)) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hnνpos.le]; ring
    rwa [h7] at h6
  have h8 : δ ^ 2 ≤ (C * k * ν * ξ) ^ 2 := pow_le_pow_left₀ hδ0.le h1 2
  have h9 : (C * k * ν * ξ) ^ 2 * n ≤ c * k * ν * n := by
    have e : (C * k * ν * ξ) ^ 2 * n = k ^ 2 * ν * (ξ ^ 2 * (C ^ 2 * (n * ν))) := by ring
    rw [e]
    have h10 : k ^ 2 * ν * (ξ ^ 2 * (C ^ 2 * (n * ν))) ≤ k ^ 2 * ν * c :=
      mul_le_mul_of_nonneg_left hξ2 (by positivity)
    have h11 : k ^ 2 * ν * c ≤ c * k * ν * n := by
      have h12 : k ^ 2 ≤ k * n := by
        rw [sq]; exact mul_le_mul_of_nonneg_left hkn hk0
      have h13 : k ^ 2 * (ν * c) ≤ k * n * (ν * c) :=
        mul_le_mul_of_nonneg_right h12 (by positivity)
      calc k ^ 2 * ν * c = k ^ 2 * (ν * c) := by ring
        _ ≤ k * n * (ν * c) := h13
        _ = c * k * ν * n := by ring
    exact h10.trans h11
  have h12 : (C * k * ν * ξ) ^ 2 ≤ c * k * ν := le_of_mul_le_mul_right h9 hn
  exact h8.trans (h12.trans h2)

/-- Numerical step: the final constant. -/
private lemma num_final {c₁ c C a n ν ξ δ s2 : ℝ} (hc₁ : 0 < c₁) (hc : 0 < c) (hC : 0 < C)
    (ha : 0 < a) (hξ0 : 0 < ξ) (hnνpos : 0 < n * ν) (hs2pos : 0 < s2)
    (hs2le : s2 ≤ (1 + C) * (n * ν)) (hδge : c * a * n * ν * ξ ≤ δ) :
    c₁ * c * a / Real.sqrt (1 + C) * ξ * Real.sqrt (n * ν) ≤ c₁ * δ / Real.sqrt s2 := by
  have hsC : 0 < Real.sqrt (1 + C) := Real.sqrt_pos.mpr (by linarith)
  have hss : Real.sqrt s2 ≤ Real.sqrt (1 + C) * Real.sqrt (n * ν) := by
    rw [← Real.sqrt_mul (by linarith)]
    exact Real.sqrt_le_sqrt hs2le
  have hss0 : 0 < Real.sqrt s2 := Real.sqrt_pos.mpr hs2pos
  rw [le_div_iff₀ hss0]
  have e1 : Real.sqrt (n * ν) * Real.sqrt (n * ν) = n * ν := Real.mul_self_sqrt hnνpos.le
  calc c₁ * c * a / Real.sqrt (1 + C) * ξ * Real.sqrt (n * ν) * Real.sqrt s2
      ≤ c₁ * c * a / Real.sqrt (1 + C) * ξ * Real.sqrt (n * ν) *
          (Real.sqrt (1 + C) * Real.sqrt (n * ν)) :=
        mul_le_mul_of_nonneg_left hss (by positivity)
    _ = c₁ * (c * a * n * ν * ξ) := by
        have : c₁ * c * a / Real.sqrt (1 + C) * ξ * Real.sqrt (n * ν) *
            (Real.sqrt (1 + C) * Real.sqrt (n * ν)) =
            c₁ * c * a * ξ * (Real.sqrt (n * ν) * Real.sqrt (n * ν)) *
              (Real.sqrt (1 + C) / Real.sqrt (1 + C)) := by ring
        rw [this, e1, div_self hsC.ne']
        ring
    _ ≤ c₁ * δ := mul_le_mul_of_nonneg_left hδge hc₁.le

theorem solution :
    ∀ a : ℝ, 0 < a → ∃ Ca : ℝ, 0 < Ca ∧ ∃ αa : ℝ, 0 < αa ∧
      ∀ n : ℕ, 1 ≤ n → ∀ ν : ℝ, 1 / (n : ℝ) ≤ ν → ν ≤ 1 →
      ∀ ξ : ℝ, 0 < ξ → ξ < 1 / 32 → ξ ≤ αa / Real.sqrt (n * ν) →
      ∀ X₁ ∈ Gsupp n, ∀ X₂ ∈ Gsupp n,
        a * n ≤ WHMultiplicativity.schattenNorm 1 ((X₂ - X₁ : Herm0 n) : Matrix (Fin n) (Fin n) ℂ) →
        ENNReal.ofReal (Ca * ξ * Real.sqrt (n * ν)) ≤
          traceSize (fugacityCoeff (fugacityFamily ν ξ X₂) - fugacityCoeff (fugacityFamily ν ξ X₁)) := by
  intro a ha
  obtain ⟨c, hc, C, hC, hsplit⟩ := fugacityFamily_occupation_split
  obtain ⟨c₁, hc₁, hgeo⟩ := geometric_pgf_threshold C hC
  have hsC : 0 < Real.sqrt (1 + C) := Real.sqrt_pos.mpr (by linarith)
  refine ⟨c₁ * c * a / Real.sqrt (1 + C), by positivity, Real.sqrt c / C, by positivity, ?_⟩
  intro n hn ν hνn hν1 ξ hξ0 hξ1 hξα X₁ hX₁ X₂ hX₂ hdist
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hν0 : 0 < ν := lt_of_lt_of_le (by positivity) hνn
  have hnν : 1 ≤ (n : ℝ) * ν := by
    have := mul_le_mul_of_nonneg_left hνn hn'.le
    rwa [mul_one_div_cancel hn'.ne'] at this
  have hnνpos : 0 < (n : ℝ) * ν := by linarith
  have hsnν : 0 < Real.sqrt (n * ν) := Real.sqrt_pos.mpr hnνpos
  obtain ⟨Rp, Rm, hor, U, A, hU, hBm, hBd, hBC, hδlo, hδhi, hTrlo, hTrhi⟩ :=
    hsplit n hn ν hνn hν1 ξ hξ0 hξ1 X₁ hX₁ X₂ hX₂ a ha hdist
  have hfam₁ := family_psd n ν ξ hν0 hν1 hξ0 hξ1 X₁ hX₁
  have hfam₂ := family_psd n ν ξ hν0 hν1 hξ0 hξ1 X₂ hX₂
  have hRp : Rp.PosSemidef ∧ (1 - Rp).PosDef := by
    rcases hor with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]; exact hfam₁
    · rw [h1]; exact hfam₂
  have hRm : Rm.PosSemidef ∧ (1 - Rm).PosDef := by
    rcases hor with ⟨_, h2⟩ | ⟨_, h2⟩
    · rw [h2]; exact hfam₂
    · rw [h2]; exact hfam₁
  set P : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i => if i ∈ A then (1 : ℂ) else 0) with hP
  set Bp : Matrix (Fin n) (Fin n) ℂ := P * (U * (Rp * (1 - Rp)⁻¹) * Uᴴ) * P with hBp
  set Bm : Matrix (Fin n) (Fin n) ℂ := P * (U * (Rm * (1 - Rm)⁻¹) * Uᴴ) * P with hBmdef
  obtain ⟨lp, lm, hlm0, hle, hlpΛ, hdetp, hdetm, htrp, htrm, htrm2⟩ :=
    loewner_eigenvalue_pairing Bm Bp hBm hBd C hBC
  obtain ⟨hpp0, hppgf⟩ := fugacity_count_pgf Rp hRp.1 hRp.2 U hU A
  obtain ⟨hpm0, hpmgf⟩ := fugacity_count_pgf Rm hRm.1 hRm.2 U hU A
  set pp : ℕ → ℝ := fun k => ∑' w : Occupation (Fin n),
    if ∑ i ∈ A, w i = k then (fugacityCoeff (U * Rp * Uᴴ) w w).re else 0 with hpp
  set pm : ℕ → ℝ := fun k => ∑' w : Occupation (Fin n),
    if ∑ i ∈ A, w i = k then (fugacityCoeff (U * Rm * Uᴴ) w w).re else 0 with hpm
  -- generating functions in product form
  have hPGFp : ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      HasSum (fun k => pp k * z ^ k) (∏ i, (1 + lp i * (1 - z))⁻¹) := by
    intro z hz0 hz1
    have h := (hppgf z hz0 hz1).2
    have e : (1 + ((1 - z : ℝ) : ℂ) • Bp).det.re = ∏ i, (1 + lp i * (1 - z)) := by
      rw [hdetp (1 - z), ← Complex.ofReal_prod, Complex.ofReal_re]
      exact Finset.prod_congr rfl fun i _ => by ring
    rw [e, ← Finset.prod_inv_distrib] at h
    exact h
  have hPGFm : ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      HasSum (fun k => pm k * z ^ k) (∏ i, (1 + lm i * (1 - z))⁻¹) := by
    intro z hz0 hz1
    have h := (hpmgf z hz0 hz1).2
    have e : (1 + ((1 - z : ℝ) : ℂ) • Bm).det.re = ∏ i, (1 + lm i * (1 - z)) := by
      rw [hdetm (1 - z), ← Complex.ofReal_prod, Complex.ofReal_re]
      exact Finset.prod_congr rfl fun i _ => by ring
    rw [e, ← Finset.prod_inv_distrib] at h
    exact h
  -- `δ` and `s²` in terms of the traces
  have hδ : ∑ i, (lp i - lm i) = (Bp - Bm).trace.re := by
    rw [Matrix.trace_sub, htrp, htrm, ← Complex.ofReal_sub, Complex.ofReal_re, Finset.sum_sub_distrib]
  have hs2 : ∑ i, lm i * (1 + lm i) = (Bm + Bm * Bm).trace.re := by
    rw [Matrix.trace_add, htrm, htrm2, ← Complex.ofReal_add, Complex.ofReal_re, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have htrBm : ∑ i, lm i = Bm.trace.re := by rw [htrm, Complex.ofReal_re]
  set δ : ℝ := ∑ i, (lp i - lm i) with hδdef
  set s2 : ℝ := 1 + ∑ i, lm i * (1 + lm i) with hs2def
  have hδlo' : c * a * n * ν * ξ ≤ δ := by rw [hδ]; exact hδlo
  have hδhi' : δ ≤ C * A.card * ν * ξ := by rw [hδ]; exact hδhi
  have hδpos : 0 < δ := lt_of_lt_of_le (mul_pos (mul_pos (mul_pos (mul_pos hc ha) hn') hν0) hξ0) hδlo'
  have hcard : (A.card : ℝ) ≤ n := by
    have := Finset.card_le_univ A
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  have hcard0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  have hsum0 : 0 ≤ ∑ i, lm i * (1 + lm i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hlm0 i) (by linarith [hlm0 i])
  have hs2pos : 0 < s2 := by rw [hs2def]; linarith
  -- upper bound on `s²`
  have hs2le : s2 ≤ (1 + C) * (n * ν) := by
    have h1 : s2 ≤ 1 + C * A.card * ν := by rw [hs2def, hs2]; linarith
    have h2 : C * A.card * ν ≤ C * (n * ν) := by
      have h3 := mul_le_mul_of_nonneg_right hcard hν0.le
      have h4 := mul_le_mul_of_nonneg_left h3 hC.le
      calc C * A.card * ν = C * (A.card * ν) := by ring
        _ ≤ C * (n * ν) := h4
    calc s2 ≤ 1 + C * A.card * ν := h1
      _ ≤ n * ν + C * (n * ν) := add_le_add hnν h2
      _ = (1 + C) * (n * ν) := by ring
  -- `δ ≤ s`
  have hlow : c * A.card * ν ≤ s2 := by
    have h3 : ∑ i, lm i ≤ ∑ i, lm i * (1 + lm i) :=
      Finset.sum_le_sum fun i _ => by nlinarith [hlm0 i]
    have h4 : c * A.card * ν ≤ ∑ i, lm i := by rw [htrBm]; exact hTrlo
    rw [hs2def]
    linarith
  have hδs : δ ^ 2 ≤ s2 := num_delta_le hc hC hn' hν0 hcard0 hcard hξα hξ0 hδpos hδhi' hlow
  obtain ⟨τ, hτ⟩ := hgeo n lp lm hlm0 hle hlpΛ pp pm hpp0 hpm0 hPGFp hPGFm hδpos hδs
  -- data processing
  have htest : ENNReal.ofReal |(∑' k, if τ < k then pp k else 0) - ∑' k, if τ < k then pm k else 0| ≤
      traceSize (fugacityCoeff (fugacityFamily ν ξ X₂) - fugacityCoeff (fugacityFamily ν ξ X₁)) := by
    rcases hor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have h := fugacity_count_test Rp Rm hRp.1 hRp.2 hRm.1 hRm.2 U hU A τ
      rw [abs_sub_comm] at h
      rw [h1, h2] at h
      rw [hpp, hpm, h1, h2]
      exact h
    · have h := fugacity_count_test Rm Rp hRm.1 hRm.2 hRp.1 hRp.2 U hU A τ
      rw [h1, h2] at h
      rw [hpp, hpm, h1, h2]
      exact h
  have hfinal := num_final (a := a) hc₁ hc hC ha hξ0 hnνpos hs2pos hs2le hδlo'
  calc ENNReal.ofReal (c₁ * c * a / Real.sqrt (1 + C) * ξ * Real.sqrt (n * ν))
      ≤ ENNReal.ofReal (c₁ * δ / Real.sqrt s2) := ENNReal.ofReal_le_ofReal hfinal
    _ ≤ ENNReal.ofReal |(∑' k, if τ < k then pp k else 0) - ∑' k, if τ < k then pm k else 0| :=
        ENNReal.ofReal_le_ofReal (hτ.trans (le_abs_self _))
    _ ≤ _ := htest
