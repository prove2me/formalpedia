-- Prove2me | solution 1 for DirichletUnitTheorem.regulator_golden_field
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T02:40:16.540123+00:00
-- url     : https://prove2.me/submissions/f57aafeb-bc9e-473f-9f06-e59e8fd8b4da

import Mathlib
open NumberField

lemma golden_real_root (z : ℂ) (hz : z ^ 2 = z + 1) : z.im = 0 := by
  have h1 := congrArg Complex.im hz
  have h2 := congrArg Complex.re hz
  simp only [sq, Complex.mul_im, Complex.mul_re, Complex.add_im, Complex.add_re,
    Complex.one_im, Complex.one_re] at h1 h2
  by_contra h
  have : z.re = 1 / 2 := by
    have : z.im * (2 * z.re - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' h
    · linarith
  nlinarith [sq_nonneg z.im]

lemma golden_alpha_not_rat (K : Type*) [Field K] [NumberField K] (α : K) (hα : α ^ 2 = α + 1)
    (q : ℚ) : algebraMap ℚ K q ≠ α := by
  intro h
  have hq : q ^ 2 = q + 1 := by
    apply (algebraMap ℚ K).injective
    rw [map_pow, map_add, map_one, h, hα]
  have hq' : ((q : ℝ) - Real.goldenRatio) * ((q : ℝ) - Real.goldenConj) = 0 := by
    have : (q : ℝ) ^ 2 = q + 1 := by exact_mod_cast hq
    have h1 := Real.goldenRatio_add_goldenConj
    have h2 := Real.goldenRatio_mul_goldenConj
    linear_combination this - (q : ℝ) * h1 + h2
  rcases mul_eq_zero.mp hq' with h' | h'
  · exact Real.goldenRatio_irrational ⟨q, by linarith⟩
  · exact Real.goldenConj_irrational ⟨q, by linarith⟩

lemma golden_emb_real (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (α : K) (hα : α ^ 2 = α + 1) (σ : K →+* ℂ) (x : K) :
    (σ x).im = 0 := by
  have hli : LinearIndependent ℚ ![(1 : K), α] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero, smul_eq_zero, one_ne_zero, or_false] at hst
      exact ⟨hst, rfl⟩
    · exfalso
      apply golden_alpha_not_rat K α hα (-s / t)
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      rw [div_eq_mul_inv, map_mul, map_neg, map_inv₀]
      have ht' : algebraMap ℚ K t ≠ 0 := by simpa using ht
      field_simp
      linear_combination -hst
  have hspan := hli.span_eq_top_of_card_eq_finrank (by simp [hK])
  have hx : x ∈ Submodule.span ℚ (Set.range ![(1 : K), α]) := by rw [hspan]; trivial
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, Submodule.mem_span_pair] at hx
  obtain ⟨a, b, rfl⟩ := hx
  have hz : (σ α).im = 0 := golden_real_root _ (by rw [← map_pow, hα, map_add, map_one])
  rw [map_add, map_rat_smul, map_rat_smul, map_one]
  simp [Complex.smul_im, hz]

lemma golden_no_int_sq (n : ℤ) (h1 : (4 : ℝ) < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 < 5 ∨
    (0 : ℝ) < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 < 1) : False := by
  have : (4 : ℤ) < n ^ 2 ∧ n ^ 2 < 5 ∨ (0 : ℤ) < n ^ 2 ∧ n ^ 2 < 1 := by
    rcases h1 with ⟨a, b⟩ | ⟨a, b⟩
    · left; exact ⟨by exact_mod_cast a, by exact_mod_cast b⟩
    · right; exact ⟨by exact_mod_cast a, by exact_mod_cast b⟩
  have hsq : n ^ 2 = n * n := sq n
  rcases this with ⟨a, b⟩ | ⟨a, b⟩
  · nlinarith [sq_nonneg (n - 2), sq_nonneg (n + 2), abs_nonneg n]
  · nlinarith

lemma golden_gap (a b : ℝ) (n : ℤ) (N : ℝ) (hN : N = 1 ∨ N = -1) (hab : a * b = N)
    (hsum : a + b = n) (h1 : 1 < |a|) (h2 : |a| < Real.goldenRatio) : False := by
  have hA1 : 1 < a ^ 2 := by
    have := sq_abs a; nlinarith [abs_nonneg a]
  have hA2 : a ^ 2 < Real.goldenRatio ^ 2 := by
    have := sq_abs a; nlinarith [abs_nonneg a]
  have hφ := Real.goldenRatio_sq
  have hψ := Real.goldenConj_sq
  have hφψ := Real.goldenRatio_mul_goldenConj
  have hφψs := Real.goldenRatio_add_goldenConj
  have hψneg := Real.goldenConj_neg
  have hN2 : N ^ 2 = 1 := by rcases hN with h | h <;> simp [h]
  have hB : a ^ 2 * b ^ 2 = 1 := by rw [← mul_pow, hab, hN2]
  -- a^2 + b^2 ∈ (2, 3)
  have hlo : 2 < a ^ 2 + b ^ 2 := by nlinarith
  have hhi : a ^ 2 + b ^ 2 < 3 := by
    have hψ2 : Real.goldenConj ^ 2 < 1 := by nlinarith
    have hprod : Real.goldenRatio ^ 2 * Real.goldenConj ^ 2 = 1 := by
      rw [← mul_pow, hφψ]; norm_num
    have hsum2 : Real.goldenRatio ^ 2 + Real.goldenConj ^ 2 = 3 := by nlinarith
    have key : (a ^ 2 - Real.goldenRatio ^ 2) * (a ^ 2 - Real.goldenConj ^ 2) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (by linarith)
    nlinarith
  have hn2 : (n : ℝ) ^ 2 = a ^ 2 + b ^ 2 + 2 * N := by rw [← hsum, ← hab]; ring
  apply golden_no_int_sq n
  rcases hN with h | h
  · left; rw [h] at hn2; constructor <;> linarith
  · right; rw [h] at hn2; constructor <;> linarith

lemma golden_no_small_unit (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (hreal : ∀ (σ : K →+* ℂ) (x : K), (σ x).im = 0)
    (u : (𝓞 K)ˣ) (σ : K →+* ℂ) : ¬ (1 < ‖σ ((u : 𝓞 K) : K)‖ ∧ ‖σ ((u : 𝓞 K) : K)‖ < Real.goldenRatio) := by
  classical
  rintro ⟨h1, h2⟩
  set x : K := ((u : 𝓞 K) : K)
  let σ' : K →ₐ[ℚ] ℂ := σ.toRatAlgHom
  have hcard : Fintype.card (K →ₐ[ℚ] ℂ) = 2 := by rw [AlgHom.card, hK]
  obtain ⟨τ, hτ⟩ := Fintype.exists_ne_of_one_lt_card (by omega) σ'
  have huniv : (Finset.univ : Finset (K →ₐ[ℚ] ℂ)) = {τ, σ'} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, hcard, Finset.card_pair hτ]
  have htr := trace_eq_sum_embeddings (K := ℚ) ℂ (x := x)
  have hnm := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [huniv, Finset.sum_pair hτ] at htr
  rw [huniv, Finset.prod_pair hτ] at hnm
  have hint : IsIntegral ℤ (Algebra.trace ℚ K x) := Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe _)
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hnorm := Units.norm K u
  set N : ℚ := Algebra.norm ℚ x
  have hN : (N : ℝ) = 1 ∨ (N : ℝ) = -1 := by
    rcases abs_eq (zero_le_one) |>.mp hnorm with h | h
    · left; exact_mod_cast h
    · right; exact_mod_cast h
  have hσx : σ' x = σ x := rfl
  have ha : σ x = ((σ x).re : ℂ) := Complex.ext rfl (by simp [hreal σ x])
  have hb : τ x = ((τ x).re : ℂ) := Complex.ext rfl (by simpa using hreal (τ : K →+* ℂ) x)
  rw [hσx, ha, hb] at htr hnm
  rw [ha, Complex.norm_real, Real.norm_eq_abs] at h1 h2
  apply golden_gap (σ x).re (τ x).re n N hN
  · have := congrArg Complex.re hnm
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at this
    rw [mul_comm, ← this]; simp
  · have := congrArg Complex.re htr
    simp only [Complex.add_re, Complex.ofReal_re] at this
    rw [add_comm, ← this, ← hn]; simp
  · exact h1
  · exact h2

open NumberField.Units NumberField.Units.dirichletUnitTheorem in
theorem solution (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) (α : K) (hα : α ^ 2 = α + 1) :
    Units.regulator K = Real.log ((1 + Real.sqrt 5) / 2) := by
  classical
  have hreal := golden_emb_real K hK α hα
  have hwreal : ∀ w : InfinitePlace K, w.IsReal := by
    intro w
    rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq, Complex.conj_eq_iff_im]
    exact hreal _ x
  have hmult : ∀ w : InfinitePlace K, (w.mult : ℝ) = 1 := by
    intro w; simp [InfinitePlace.mult, hwreal w]
  have hcard : Fintype.card (InfinitePlace K) = 2 := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    have h3 : InfinitePlace.nrComplexPlaces K = 0 :=
      (NumberField.nrComplexPlaces_eq_zero_iff).mpr ⟨hwreal⟩
    omega
  have hrank : Units.rank K = 1 := by rw [Units.rank, hcard]
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega) (w₀ : InfinitePlace K)
  have hall : ∀ v : InfinitePlace K, v = w₀ ∨ v = w := by
    intro v
    by_contra! h
    have : ({w₀, w, v} : Finset (InfinitePlace K)).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm h.2)]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hw, Ne.symm h.1⟩
    have := Finset.card_le_univ ({w₀, w, v} : Finset (InfinitePlace K))
    omega
  let iw : {v : InfinitePlace K // v ≠ w₀} := ⟨w, hw⟩
  have : Unique {v : InfinitePlace K // v ≠ w₀} :=
    { default := iw, uniq := fun v => Subtype.ext ((hall v.1).resolve_left v.2) }
  have hc1 : Fintype.card {v : InfinitePlace K // v ≠ w₀} = Fintype.card (Fin (Units.rank K)) := by
    rw [Fintype.card_unique, Fintype.card_fin, hrank]
  let e : {v : InfinitePlace K // v ≠ w₀} ≃ Fin (Units.rank K) := Fintype.equivOfCardEq hc1
  have : Subsingleton (Fin (Units.rank K)) := e.symm.injective.subsingleton
  set ε := Units.fundSystem K (e iw) with hε
  let L : (𝓞 K)ˣ → ℝ := fun u => logEmbedding K (Additive.ofMul u) iw
  have hL : ∀ u : (𝓞 K)ˣ, L u = Real.log (w ((u : 𝓞 K) : K)) := by
    intro u
    simp only [L, logEmbedding_component, iw, hmult, one_mul]
  have hreg : Units.regulator K = |L ε| := by
    have hdef : (default : {v : InfinitePlace K // v ≠ w₀}) = iw := Subsingleton.elim _ _
    rw [Units.regulator_eq_det K w₀ e, Matrix.det_unique, hL, hdef]
    simp only [Matrix.of_apply]
    rw [hmult, one_mul]
  have hLdec : ∀ u : (𝓞 K)ˣ, ∃ k : ℤ, L u = k * L ε := by
    intro u
    obtain ⟨⟨ζ, k⟩, hu, -⟩ := Units.exist_unique_eq_mul_prod K u
    refine ⟨k (e iw), ?_⟩
    simp only at hu
    rw [Fintype.prod_subsingleton _ (e iw)] at hu
    have hζ : logEmbedding K (Additive.ofMul (ζ : (𝓞 K)ˣ)) = 0 :=
      logEmbedding_eq_zero_iff.mpr ζ.2
    simp only [L, hu, ofMul_mul, ofMul_zpow, map_add, map_zsmul, hζ, zero_add, Pi.smul_apply,
      ← hε]
    rw [zsmul_eq_mul]
  -- the unit `α`
  have hαint : IsIntegral ℤ α := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X - 1, ?_, ?_⟩
    · monicity!
    · simp [hα]
  let a : 𝓞 K := ⟨α, hαint⟩
  have ha1 : a * (a - 1) = 1 := by
    apply RingOfIntegers.coe_injective
    simp only [map_mul, map_sub, map_one]
    show α * (α - 1) = 1
    linear_combination hα
  let αu : (𝓞 K)ˣ := ⟨a, a - 1, ha1, by rw [mul_comm]; exact ha1⟩
  have hφ1 := Real.one_lt_goldenRatio
  have hlogφ : 0 < Real.log Real.goldenRatio := Real.log_pos hφ1
  -- `|L αu| = log φ`
  have hLα : |L αu| = Real.log Real.goldenRatio := by
    rw [hL]
    show |Real.log (w α)| = _
    rw [← InfinitePlace.norm_embedding_eq]
    set z := w.embedding α
    have hz2 : z ^ 2 = z + 1 := by rw [← map_pow, hα, map_add, map_one]
    have hzim : z.im = 0 := golden_real_root z hz2
    have hzr : z = (z.re : ℂ) := Complex.ext rfl (by simp [hzim])
    rw [hzr, Complex.norm_real, Real.norm_eq_abs]
    have hre2 : z.re ^ 2 = z.re + 1 := by
      have := congrArg Complex.re hz2
      rw [hzr] at this
      simpa [sq] using (by exact_mod_cast this : (z.re : ℝ) ^ 2 = z.re + 1)
    have hfac : (z.re - Real.goldenRatio) * (z.re - Real.goldenConj) = 0 := by
      linear_combination hre2 - z.re * Real.goldenRatio_add_goldenConj + Real.goldenRatio_mul_goldenConj
    rcases mul_eq_zero.mp hfac with h | h
    · rw [show z.re = Real.goldenRatio by linarith, abs_of_pos Real.goldenRatio_pos,
        abs_of_pos hlogφ]
    · rw [show z.re = Real.goldenConj by linarith, abs_of_neg Real.goldenConj_neg,
        ← Real.inv_goldenRatio, Real.log_inv, abs_neg, abs_of_pos hlogφ]
  obtain ⟨k, hk⟩ := hLdec αu
  have hRpos : 0 < |L ε| := hreg ▸ Units.regulator_pos K
  rw [hreg]
  rw [hk, abs_mul] at hLα
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hLα
    linarith
  by_contra hne
  have hk2 : 2 ≤ |(k : ℝ)| := by
    have : 2 ≤ |k| := by
      by_contra h
      have : |k| = 1 := by have := abs_pos.mpr hk0; omega
      apply hne
      rw [← hLα, show |(k : ℝ)| = 1 by exact_mod_cast this, one_mul]
    exact_mod_cast this
  have hsmall : |L ε| < Real.log Real.goldenRatio := by nlinarith
  -- a unit with `0 < L u < log φ`
  obtain ⟨u, hu1, hu2⟩ : ∃ u : (𝓞 K)ˣ, 0 < L u ∧ L u < Real.log Real.goldenRatio := by
    rcases le_or_gt 0 (L ε) with h | h
    · exact ⟨ε, by rw [abs_of_nonneg h] at hRpos; exact hRpos,
        by rw [abs_of_nonneg h] at hsmall; exact hsmall⟩
    · refine ⟨ε⁻¹, ?_, ?_⟩
      · have : L ε⁻¹ = - L ε := by simp [L]
        rw [this]; linarith
      · have : L ε⁻¹ = - L ε := by simp [L]
        rw [this, ← abs_of_neg h]; exact hsmall
  rw [hL] at hu1 hu2
  have hpos : 0 < w ((u : 𝓞 K) : K) := Units.pos_at_place u w
  apply golden_no_small_unit K hK hreal u w.embedding
  rw [InfinitePlace.norm_embedding_eq]
  constructor
  · rw [← Real.exp_log hpos]; exact Real.one_lt_exp_iff.mpr hu1 |>.trans_le' le_rfl
  · rw [← Real.exp_log hpos, ← Real.exp_log Real.goldenRatio_pos]
    exact Real.exp_lt_exp.mpr hu2
