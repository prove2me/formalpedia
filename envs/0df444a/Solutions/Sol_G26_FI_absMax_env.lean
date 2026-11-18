-- Prove2me | solution 1 for G26.FI.absMax_env
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:31:25.305484+00:00
-- url     : https://prove2.me/submissions/c1e38416-6757-4226-a1c5-854d9379dbb6

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_G26_body
import Definitions.Def_IAFTRL_G26_run
import Definitions.Def_IAFTRL_G26_window
import Theorems.Thm_IAFTRL_lemma_G_12
import Theorems.Thm_IAFTRL_lemma_J_4

-- ===== Solutions.C37.Base =====

/-! # Elementary inequalities for the scalar moment analysis (v1 Appendix I.5 and helpers) -/

namespace C37

/-! ## Second-order remainders of powers -/

/-- `(y+z)^{m+2} − y^{m+2} − (m+2) y^{m+1} z` is at most `(m+2)(m+1)/2 (|y|+|z|)^m z²` in absolute
value (v1 (I.8), by induction on the exponent). -/
lemma binom_rem (y z : ℝ) (m : ℕ) :
    |(y + z) ^ (m + 2) - y ^ (m + 2) - (m + 2) * y ^ (m + 1) * z| ≤
      ((m + 2) * (m + 1) / 2 : ℝ) * (|y| + |z|) ^ m * z ^ 2 := by
  induction m with
  | zero =>
    have e : (y + z) ^ (0 + 2) - y ^ (0 + 2) - ((0 : ℕ) + 2 : ℝ) * y ^ (0 + 1) * z = z ^ 2 := by
      push_cast; ring
    rw [e]; simp [abs_of_nonneg (sq_nonneg z)]
  | succ m ih =>
    have e : (y + z) ^ (m + 1 + 2) - y ^ (m + 1 + 2) - ((m + 1 : ℕ) + 2 : ℝ) * y ^ (m + 1 + 1) * z =
        (y + z) * ((y + z) ^ (m + 2) - y ^ (m + 2) - (m + 2) * y ^ (m + 1) * z) +
          (m + 2) * y ^ (m + 1) * z ^ 2 := by
      push_cast; ring
    rw [e]
    have hyz : |y + z| ≤ |y| + |z| := abs_add_le y z
    have hs0 : 0 ≤ |y| + |z| := by positivity
    have hy : |y| ^ (m + 1) ≤ (|y| + |z|) ^ (m + 1) :=
      pow_le_pow_left₀ (abs_nonneg y) (by linarith [abs_nonneg z]) _
    have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
    calc |(y + z) * ((y + z) ^ (m + 2) - y ^ (m + 2) - (m + 2) * y ^ (m + 1) * z) +
          (m + 2) * y ^ (m + 1) * z ^ 2|
        ≤ |y + z| * |(y + z) ^ (m + 2) - y ^ (m + 2) - (m + 2) * y ^ (m + 1) * z| +
            (m + 2) * |y| ^ (m + 1) * z ^ 2 := by
          refine (abs_add_le _ _).trans (add_le_add (le_of_eq (abs_mul _ _)) (le_of_eq ?_))
          rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hz2, abs_of_nonneg (by positivity : (0:ℝ) ≤ m + 2)]
      _ ≤ (|y| + |z|) * (((m + 2) * (m + 1) / 2 : ℝ) * (|y| + |z|) ^ m * z ^ 2) +
            (m + 2) * (|y| + |z|) ^ (m + 1) * z ^ 2 := by
          gcongr
      _ = (((m + 1 : ℕ) + 2) * ((m + 1 : ℕ) + 1) / 2 : ℝ) * (|y| + |z|) ^ (m + 1) * z ^ 2 := by
          push_cast; ring

/-- the upper Taylor bound for an arbitrary power `P ≥ 2` -/
lemma pow_taylor (y z : ℝ) (P : ℕ) (hP : 2 ≤ P) :
    (y + z) ^ P ≤ y ^ P + P * y ^ (P - 1) * z +
      ((P : ℝ) * (P - 1) / 2) * (|y| + |z|) ^ (P - 2) * z ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, P = m + 2 := ⟨P - 2, by omega⟩
  have h := le_abs_self ((y + z) ^ (m + 2) - y ^ (m + 2) - (m + 2) * y ^ (m + 1) * z)
  have h2 := binom_rem y z m
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 - 2 = m := by omega
  rw [e1, e2]
  push_cast
  have e3 : ((m : ℝ) + 2) * ((m : ℝ) + 2 - 1) / 2 = ((m + 2) * (m + 1) / 2 : ℝ) := by ring
  rw [e3]
  linarith

end C37


-- ===== Solutions.G2.Haus =====

/-! ### The `k`-dimensional Hausdorff measure of a compact convex set of affine dimension `k` -/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace G11

variable {d : ℕ}

theorem hausdorff_pos_fin {K : Set (Fin d → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) :
    0 < μH[(Module.finrank ℝ (vectorSpan ℝ K) : ℝ)] K ∧
      μH[(Module.finrank ℝ (vectorSpan ℝ K) : ℝ)] K < ∞ := by
  set V := vectorSpan ℝ K with hV
  set k := Module.finrank ℝ V with hk
  obtain ⟨b₀, hb₀⟩ := hne
  let bV := Module.finBasisOfFinrankEq ℝ V hk.symm
  let φ : (Fin k → ℝ) →ₗ[ℝ] (Fin d → ℝ) := V.subtype ∘ₗ bV.equivFun.symm.toLinearMap
  have hφinj : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro y z h
    exact bV.equivFun.symm.injective (Subtype.val_injective h)
  obtain ⟨ψ, hψ⟩ := φ.exists_leftInverse_of_injective hφinj
  have hψφ : ∀ y, ψ (φ y) = y := fun y => by
    simpa using LinearMap.congr_fun hψ y
  have hφsurj : ∀ v ∈ V, ∃ y, φ y = v := fun v hv =>
    ⟨bV.equivFun ⟨v, hv⟩, by simp [φ]⟩
  let L : (Fin k → ℝ) → (Fin d → ℝ) := fun y => b₀ + φ y
  let G : (Fin d → ℝ) → (Fin k → ℝ) := fun x => ψ (x - b₀)
  have hLG : ∀ x ∈ K, L (G x) = x := by
    intro x hx
    obtain ⟨y, hy⟩ := hφsurj (x - b₀) (vsub_mem_vectorSpan ℝ hx hb₀)
    simp only [L, G, ← hy, hψφ]
    rw [hy]; abel
  have hKimg : L '' (G '' K) = K := by
    rw [Set.image_image]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; show L (G y) ∈ K; rw [hLG y hy]; exact hy
    · intro hx; exact ⟨x, hx, hLG x hx⟩
  -- Lipschitz constants
  obtain ⟨Kφ, hLφ⟩ : ∃ C, LipschitzWith C φ :=
    ⟨_, by simpa using (LinearMap.toContinuousLinearMap φ).lipschitz⟩
  obtain ⟨Kψ, hLψ⟩ : ∃ C, LipschitzWith C ψ :=
    ⟨_, by simpa using (LinearMap.toContinuousLinearMap ψ).lipschitz⟩
  have hL : LipschitzWith Kφ L := LipschitzWith.of_dist_le_mul fun y z => by
    simp only [L]; rw [dist_add_left]; exact hLφ.dist_le_mul _ _
  have hG : LipschitzWith Kψ G := LipschitzWith.of_dist_le_mul fun x y => by
    simp only [G]; rw [← dist_sub_right x y b₀]; exact hLψ.dist_le_mul _ _
  have hvol : (μH[(k : ℝ)] : Measure (Fin k → ℝ)) = volume := by
    simpa using (hausdorffMeasure_pi_real (ι := Fin k))
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  -- the image `G '' K` is compact, convex and full-dimensional
  have hGK : IsCompact (G '' K) := hK.image hG.continuous
  have hGconv : Convex ℝ (G '' K) := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a b ha hb hab
    refine ⟨a • x + b • y, hconv hx hy ha hb hab, ?_⟩
    simp only [G]
    have : a • x + b • y - b₀ = a • (x - b₀) + b • (y - b₀) := by
      rw [smul_sub, smul_sub]
      nth_rewrite 1 [show b₀ = (a + b) • b₀ by rw [hab, one_smul]]
      rw [add_smul]; abel
    rw [this, map_add, map_smul, map_smul]
  have hspan : vectorSpan ℝ (G '' K) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hmem : ∀ w ∈ V, ψ w ∈ vectorSpan ℝ (G '' K) := by
      intro w hw
      rw [hV, vectorSpan_def] at hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_vsub.1 hw
        have : ψ (x -ᵥ y) = G x -ᵥ G y := by
          simp only [G, vsub_eq_sub]
          rw [← map_sub]; congr 1; abel
        rw [this]
        exact vsub_mem_vectorSpan ℝ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
    have := hmem (φ z) (by
      simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply]; exact Submodule.coe_mem _)
    rwa [hψφ] at this
  have hGne : (G '' K).Nonempty := ⟨G b₀, b₀, hb₀, rfl⟩
  have haff : affineSpan ℝ (G '' K) = ⊤ :=
    (AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ _ _ hGne).2 hspan
  obtain ⟨z, hz⟩ := (hGconv.interior_nonempty_iff_affineSpan_eq_top).2 haff
  have hvolpos : 0 < volume (G '' K) :=
    lt_of_lt_of_le (isOpen_interior.measure_pos volume ⟨z, hz⟩) (measure_mono interior_subset)
  constructor
  · -- positivity
    have h1 := hG.hausdorffMeasure_image_le hk0 K
    rw [hvol] at h1
    by_contra h0
    push Not at h0
    have h0' : μH[(k : ℝ)] K = 0 := nonpos_iff_eq_zero.1 h0
    rw [h0', mul_zero] at h1
    exact absurd (nonpos_iff_eq_zero.1 h1) hvolpos.ne'
  · -- finiteness
    have h1 := hL.hausdorffMeasure_image_le hk0 (G '' K)
    rw [hKimg, hvol] at h1
    refine lt_of_le_of_lt h1 (ENNReal.mul_lt_top ?_ hGK.measure_lt_top)
    exact ENNReal.rpow_lt_top_of_nonneg hk0 ENNReal.coe_ne_top

end G11


-- ===== Solutions.G26.IAlg =====

/-! ### Scalar and integral inequalities for the moment recurrences -/

open MeasureTheory

namespace G26

/-- weighted AM–GM: `x^k A^{P−k} ≤ (k x^P + (P−k) A^P)/P` -/
lemma amgm_k (x A : ℝ) (k P : ℕ) (hk : k ≤ P) (hP : 1 ≤ P) (hx : 0 ≤ x) (hA : 0 ≤ A) :
    x ^ k * A ^ (P - k) ≤ ((k : ℝ) * x ^ P + ((P : ℝ) - k) * A ^ P) / P := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hkP : (k : ℝ) ≤ P := by exact_mod_cast hk
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := (k : ℝ) / P) (w₂ := ((P : ℝ) - k) / P)
    (p₁ := x ^ P) (p₂ := A ^ P) (by positivity) (div_nonneg (by linarith) hPr.le)
    (by positivity) (by positivity) (by field_simp; ring)
  have e1 : (x ^ P) ^ ((k : ℝ) / P) = x ^ k := by
    rw [← Real.rpow_natCast x P, ← Real.rpow_mul hx, mul_div_cancel₀ _ hPr.ne', Real.rpow_natCast]
  have e2 : (A ^ P) ^ (((P : ℝ) - k) / P) = A ^ (P - k) := by
    rw [← Real.rpow_natCast A P, ← Real.rpow_mul hA, mul_div_cancel₀ _ hPr.ne',
      ← Nat.cast_sub hk, Real.rpow_natCast]
  rw [e1, e2] at h
  calc x ^ k * A ^ (P - k) ≤ (k : ℝ) / P * x ^ P + ((P : ℝ) - k) / P * A ^ P := h
    _ = _ := by field_simp

/-- power mean on a probability space: `∫ f^P ≤ A^P` implies `∫ f^k ≤ A^k` -/
lemma int_pow_le {Ω : Type*} [MeasurableSpace Ω] {σ : Measure Ω} [IsProbabilityMeasure σ]
    {f : Ω → ℝ} {k P : ℕ} (hf0 : ∀ u, 0 ≤ f u) (hk_int : Integrable (fun u => f u ^ k) σ)
    (hP_int : Integrable (fun u => f u ^ P) σ) {A : ℝ} (hA : 0 < A) (hk : k ≤ P) (hP : 1 ≤ P)
    (hG : ∫ u, f u ^ P ∂σ ≤ A ^ P) : ∫ u, f u ^ k ∂σ ≤ A ^ k := by
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hkP : (k : ℝ) ≤ P := by exact_mod_cast hk
  have hpt : ∀ u, f u ^ k ≤ ((k : ℝ) * f u ^ P + ((P : ℝ) - k) * A ^ P) / P / A ^ (P - k) := by
    intro u
    rw [le_div_iff₀ (by positivity)]
    exact amgm_k (f u) A k P hk hP (hf0 u) hA.le
  have hint : Integrable (fun u => ((k : ℝ) * f u ^ P + ((P : ℝ) - k) * A ^ P) / P /
      A ^ (P - k)) σ :=
    (((hP_int.const_mul _).add (integrable_const _)).div_const _).div_const _
  calc ∫ u, f u ^ k ∂σ ≤ ∫ u, ((k : ℝ) * f u ^ P + ((P : ℝ) - k) * A ^ P) / P / A ^ (P - k) ∂σ :=
        integral_mono hk_int hint hpt
    _ = ((k : ℝ) * ∫ u, f u ^ P ∂σ + ((P : ℝ) - k) * A ^ P) / P / A ^ (P - k) := by
        rw [integral_div, integral_div, integral_add (hP_int.const_mul _) (integrable_const _),
          integral_const_mul, integral_const]
        simp
    _ ≤ ((k : ℝ) * A ^ P + ((P : ℝ) - k) * A ^ P) / P / A ^ (P - k) := by
        gcongr
    _ = A ^ k := by
        have e : A ^ P = A ^ k * A ^ (P - k) := by rw [← pow_add]; congr 1; omega
        rw [e]; field_simp; ring

/-- convexity of `t^k`: `(x + M)^k ≤ ((A+M)/A)^{k−1} x^k + ((A+M)/M)^{k−1} M^k` -/
lemma conv_pow (x A M : ℝ) (k : ℕ) (hx : 0 ≤ x) (hA : 0 < A) (hM : 0 < M) :
    (x + M) ^ k ≤ ((A + M) / A) ^ (k - 1) * x ^ k + ((A + M) / M) ^ (k - 1) * M ^ k := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [pow_zero, zero_tsub, mul_one]
    norm_num
  set l := A / (A + M) with hl
  have hl0 : 0 < l := by positivity
  have hl1 : l < 1 := by rw [hl, div_lt_one (by positivity)]; linarith
  have h := (convexOn_pow k).2 (Set.mem_Ici.2 (div_nonneg hx hl0.le))
    (Set.mem_Ici.2 (div_nonneg hM.le (sub_pos.2 hl1).le)) hl0.le (sub_pos.2 hl1).le
    (by ring)
  simp only [smul_eq_mul] at h
  have hl1' : (1 - l) ≠ 0 := (sub_pos.2 hl1).ne'
  have e1 : l * (x / l) + (1 - l) * (M / (1 - l)) = x + M := by
    rw [mul_div_cancel₀ _ hl0.ne', mul_div_cancel₀ _ hl1']
  rw [e1] at h
  have e2 : 1 - l = M / (A + M) := by rw [hl]; field_simp; ring
  refine h.trans (le_of_eq ?_)
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have key : ∀ t y : ℝ, 0 < t → t * (y / t) ^ (j + 1) = (1 / t) ^ j * y ^ (j + 1) := by
    intro t y ht
    rw [div_pow, one_div_pow, pow_succ t]; field_simp
  rw [key l x hl0, key (1 - l) M (sub_pos.2 hl1), e2, hl, one_div_div, one_div_div]

/-- Minkowski with a constant: `∫ f^P ≤ A^P` implies `∫ (f + M)^k ≤ (A + M)^k` -/
lemma int_shift_pow_le {Ω : Type*} [MeasurableSpace Ω] {σ : Measure Ω} [IsProbabilityMeasure σ]
    {f : Ω → ℝ} {k P : ℕ} {M : ℝ} (hf0 : ∀ u, 0 ≤ f u) (hk_int : Integrable (fun u => f u ^ k) σ)
    (hP_int : Integrable (fun u => f u ^ P) σ)
    (hkM_int : Integrable (fun u => (f u + M) ^ k) σ) {A : ℝ} (hA : 0 < A) (hM : 0 < M)
    (hk1 : 1 ≤ k) (hk : k ≤ P) (hP : 1 ≤ P) (hG : ∫ u, f u ^ P ∂σ ≤ A ^ P) :
    ∫ u, (f u + M) ^ k ∂σ ≤ (A + M) ^ k := by
  have h1 := int_pow_le hf0 hk_int hP_int hA hk hP hG
  have hint : Integrable (fun u => ((A + M) / A) ^ (k - 1) * f u ^ k +
      ((A + M) / M) ^ (k - 1) * M ^ k) σ := (hk_int.const_mul _).add (integrable_const _)
  calc ∫ u, (f u + M) ^ k ∂σ ≤ ∫ u, (((A + M) / A) ^ (k - 1) * f u ^ k +
        ((A + M) / M) ^ (k - 1) * M ^ k) ∂σ :=
        integral_mono hkM_int hint fun u => conv_pow (f u) A M k (hf0 u) hA hM
    _ = ((A + M) / A) ^ (k - 1) * ∫ u, f u ^ k ∂σ + ((A + M) / M) ^ (k - 1) * M ^ k := by
        rw [integral_add (hk_int.const_mul _) (integrable_const _), integral_const_mul,
          integral_const]
        simp
    _ ≤ ((A + M) / A) ^ (k - 1) * A ^ k + ((A + M) / M) ^ (k - 1) * M ^ k := by
        gcongr
    _ = (A + M) ^ k := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        rw [div_pow, div_pow, pow_succ A, pow_succ M, pow_succ (A + M)]
        field_simp

/-- linearization of a lower power: `c x^k ≤ θ x^P + c L^k` with `L = max 1 (c/θ)` -/
lemma lin_pow (c θ x : ℝ) (k P : ℕ) (hkP : k < P) (hc : 0 ≤ c) (hθ : 0 < θ) (hx : 0 ≤ x) :
    c * x ^ k ≤ θ * x ^ P + c * (max 1 (c / θ)) ^ k := by
  set L := max 1 (c / θ) with hL
  have hL1 : 1 ≤ L := le_max_left _ _
  rcases le_or_gt x L with h | h
  · have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx h k) hc
    have : 0 ≤ θ * x ^ P := by positivity
    linarith
  · have hx1 : 1 ≤ x := le_trans hL1 h.le
    have h1 : c / θ ≤ x ^ (P - k) := by
      calc c / θ ≤ L := le_max_right _ _
        _ ≤ x := h.le
        _ = x ^ 1 := (pow_one x).symm
        _ ≤ x ^ (P - k) := pow_le_pow_right₀ hx1 (by omega)
    have h2 : c ≤ θ * x ^ (P - k) := by rwa [div_le_iff₀ hθ, mul_comm] at h1
    have e : x ^ P = x ^ (P - k) * x ^ k := by rw [← pow_add]; congr 1; omega
    have h3 : c * x ^ k ≤ θ * x ^ P := by
      rw [e, ← mul_assoc]; exact mul_le_mul_of_nonneg_right h2 (by positivity)
    have : 0 ≤ c * L ^ k := by positivity
    linarith

/-- binomial lower bound `(n+1)^P ≥ n^P + P n^{P−1}` -/
lemma pow_succ_lb (x : ℝ) (hx : 0 ≤ x) (P : ℕ) (hP : 1 ≤ P) :
    x ^ P + P * x ^ (P - 1) ≤ (x + 1) ^ P := by
  obtain ⟨j, rfl⟩ : ∃ j, P = j + 1 := ⟨P - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : (x + 1) ^ (j + 1 + 1) = (x + 1) ^ (j + 1) * (x + 1) := pow_succ _ _
    rw [h1]
    have h2 : 0 ≤ x ^ j := pow_nonneg hx j
    have h3 : ((x ^ (j + 1) + ((j + 1 : ℕ) : ℝ) * x ^ j)) * (x + 1) ≤ (x + 1) ^ (j + 1) * (x + 1) :=
      mul_le_mul_of_nonneg_right (ih (by omega)) (by linarith)
    push_cast at h3 ⊢
    have e : x ^ (j + 1 + 1) = x ^ (j + 1) * x := pow_succ _ _
    have e2 : x ^ (j + 1) = x ^ j * x := pow_succ _ _
    nlinarith [mul_nonneg h2 hx, mul_nonneg (mul_nonneg h2 hx) hx]

/-- supersolution of the linear recursion `g_{n+1} ≤ (1 + v/(n+1)) g_n + K (n+1)^{P−1}` -/
lemma supersol (g : ℕ → ℝ) (v K C : ℝ) (P : ℕ) (hP : 1 ≤ P) (hv : 0 ≤ v) (hK : 0 ≤ K)
    (hC : 0 ≤ C) (hvP : v * C + K ≤ P * C) (h0 : g 0 ≤ C) (N : ℕ)
    (hrec : ∀ n < N, g (n + 1) ≤ (1 + v / ((n : ℝ) + 1)) * g n + K * ((n : ℝ) + 1) ^ (P - 1)) :
    ∀ n ≤ N, g n ≤ C * ((n : ℝ) + 1) ^ P := by
  intro n hn
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have ih' := ih (by omega)
    set x : ℝ := (n : ℝ) + 1 with hx
    have hx1 : 1 ≤ x := by simp only [x]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hcoef : 0 ≤ 1 + v / x := by positivity
    have h1 := hrec n (by omega)
    have e : x ^ P = x * x ^ (P - 1) := by rw [← pow_succ']; congr 1; omega
    have h2 : (1 + v / x) * g n ≤ (1 + v / x) * (C * x ^ P) := mul_le_mul_of_nonneg_left ih' hcoef
    have h3 : (1 + v / x) * (C * x ^ P) = C * x ^ P + v * C * x ^ (P - 1) := by
      rw [e]; field_simp
    have h4 := pow_succ_lb x (by linarith) P hP
    have h5 : C * x ^ P + v * C * x ^ (P - 1) + K * x ^ (P - 1) ≤ C * (x + 1) ^ P := by
      have : (v * C + K) * x ^ (P - 1) ≤ P * C * x ^ (P - 1) :=
        mul_le_mul_of_nonneg_right hvP (by positivity)
      nlinarith
    push_cast
    rw [show (n : ℝ) + 1 + 1 = x + 1 by simp [x]]
    linarith

end G26

namespace G26

end G26


-- ===== Solutions.G26.AbsAlg =====

/-! ### Pathwise algebra of the absolute integral moment recurrence (Lemma G.23) -/

namespace G26

lemma exp_small (m : ℕ) (y : ℝ) (hy : 0 ≤ y) (hmy : m * y ≤ 2 / 5) : (1 + y) ^ m ≤ 2 := by
  have h1 : (1 + y) ^ m ≤ Real.exp (m * y) := by
    calc (1 + y) ^ m ≤ Real.exp y ^ m := pow_le_pow_left₀ (by linarith) (by
          have := Real.add_one_le_exp y; linarith) m
      _ = Real.exp (m * y) := (Real.exp_nat_mul y m).symm
  have h2 : Real.exp (m * y) ≤ Real.exp (2 / 5) := Real.exp_le_exp.2 hmy
  have h3 : Real.exp (2 / 5) ≤ 2 := by
    have he := Real.exp_one_lt_d9
    have h4 : Real.exp (2 / 5) ^ 5 = Real.exp 2 := by rw [← Real.exp_nat_mul]; norm_num
    have h5 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    by_contra hc
    push_neg at hc
    have h6 : (2 : ℝ) ^ 5 ≤ Real.exp (2 / 5) ^ 5 := pow_le_pow_left₀ (by norm_num) hc.le 5
    have h7 : Real.exp 1 ^ 2 < 2.7182818286 ^ 2 :=
      pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
    rw [h4, h5] at h6
    norm_num at h6 h7
    linarith
  linarith

lemma pow_pred_mul (n : ℝ) (P : ℕ) (hP : 1 ≤ P) : n * n ^ (P - 1) = n ^ P := by
  rw [← pow_succ']; congr 1; omega

lemma pow_sub2_mul (n : ℝ) (P : ℕ) (hP : 2 ≤ P) : n * n ^ (P - 2) = n ^ (P - 1) := by
  rw [← pow_succ']; congr 1; omega

/-- drift term of the absolute recurrence -/
lemma abs_drift (P : ℕ) (hP : 2 ≤ P) (b β n G At : ℝ) (hn : 0 < n) (hβ : 0 ≤ β)
    (hβb : β ≤ b * n) (hA0 : 0 ≤ At) (hAtG : At ^ P ≤ G + β ^ P) :
    2 * P * At ^ (P - 1) ≤ G / n + (2 * P * (max 1 (2 * (P : ℝ))) ^ (P - 1) + b ^ P) * n ^ (P - 1) := by
  set x := At / n with hx
  have hx0 : 0 ≤ x := by positivity
  have hAx : At = x * n := by rw [hx]; field_simp
  have h1 := lin_pow (2 * P) 1 x (P - 1) P (by omega) (by positivity) one_pos hx0
  rw [div_one] at h1
  have e1 : 2 * P * At ^ (P - 1) = n ^ (P - 1) * (2 * P * x ^ (P - 1)) := by rw [hAx, mul_pow]; ring
  have e2 : n ^ (P - 1) * (1 * x ^ P) = At ^ P / n := by
    rw [hAx, mul_pow, ← pow_pred_mul n P (by omega)]; field_simp
  have h3 : At ^ P / n ≤ G / n + b ^ P * n ^ (P - 1) := by
    have h5 : β ^ P ≤ (b * n) ^ P := pow_le_pow_left₀ hβ hβb P
    rw [mul_pow, ← pow_pred_mul n P (by omega)] at h5
    have e3 : (G + b ^ P * (n * n ^ (P - 1))) / n = G / n + b ^ P * n ^ (P - 1) := by
      field_simp
    rw [← e3]
    exact div_le_div_of_nonneg_right (by linarith) hn.le
  have h4 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ n ^ (P - 1))
  rw [mul_add, e2] at h4
  rw [e1]
  linarith only [h4, h3]

/-- curvature term, large branch -/
lemma abs_curv_big (P : ℕ) (hP : 4 ≤ P) (B b β n At M : ℝ) (hB : 2 ^ 20 * (P : ℝ) ≤ B)
    (hn : 0 < n) (hβ : 0 < β) (hβb : β ≤ b * n) (hbig : 8 * P * β ≤ At) (hM0 : 0 ≤ M)
    (hM : M ≤ 3 * β + 24 * At / B) :
    (10 * β + 1152 * At ^ 2 / (B * n)) * (P ^ 2 / 2 * (At + M) ^ (P - 2)) ≤
      (1 + 1152 * P ^ 2 / B) / n * At ^ P +
        10 * P ^ 2 * b * (max 1 (10 * (P : ℝ) ^ 2 * b)) ^ (P - 2) * n ^ (P - 1) := by
  have hPr : (4 : ℝ) ≤ P := by exact_mod_cast hP
  have hB0 : 0 < B := by linarith
  have hA0 : 0 < At := by nlinarith
  have hb0 : 0 ≤ b := by
    by_contra h; push_neg at h; nlinarith
  have hM' : At + M ≤ At * (1 + (3 / (8 * P) + 24 / B)) := by
    have h1 : 3 * β ≤ At * (3 / (8 * P)) := by
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]; nlinarith
    have h2 : 24 * At / B = At * (24 / B) := by ring
    nlinarith
  have hexp : (1 + (3 / (8 * P) + 24 / B)) ^ (P - 2) ≤ 2 := by
    apply exp_small _ _ (by positivity)
    have hP2 : ((P - 2 : ℕ) : ℝ) ≤ P := by rw [Nat.cast_sub (by omega)]; linarith
    have h1 : ((P - 2 : ℕ) : ℝ) * (3 / (8 * P)) ≤ 3 / 8 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    have h2 : ((P - 2 : ℕ) : ℝ) * (24 / B) ≤ 1 / 40 := by
      rw [mul_div_assoc', div_le_iff₀ hB0]; nlinarith
    rw [mul_add]; linarith
  have hpow : (At + M) ^ (P - 2) ≤ 2 * At ^ (P - 2) := by
    calc (At + M) ^ (P - 2) ≤ (At * (1 + (3 / (8 * P) + 24 / B))) ^ (P - 2) :=
          pow_le_pow_left₀ (by positivity) hM' _
      _ = At ^ (P - 2) * (1 + (3 / (8 * P) + 24 / B)) ^ (P - 2) := mul_pow _ _ _
      _ ≤ At ^ (P - 2) * 2 := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = 2 * At ^ (P - 2) := by ring
  have h1 : (10 * β + 1152 * At ^ 2 / (B * n)) * (P ^ 2 / 2 * (At + M) ^ (P - 2)) ≤
      (10 * β + 1152 * At ^ 2 / (B * n)) * (P ^ 2 * At ^ (P - 2)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have := mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ P ^ 2 / 2)
    linarith
  have eAP : At ^ 2 * At ^ (P - 2) = At ^ P := by rw [← pow_add]; congr 1; omega
  have h2 : (10 * β + 1152 * At ^ 2 / (B * n)) * (P ^ 2 * At ^ (P - 2)) =
      10 * P ^ 2 * β * At ^ (P - 2) + 1152 * P ^ 2 / B / n * At ^ P := by
    rw [← eAP]; field_simp
  -- linearize `10 P² β At^{P−2}`
  set x := At / n with hx
  have hx0 : 0 ≤ x := by positivity
  have hAx : At = x * n := by rw [hx]; field_simp
  have h3 : 10 * P ^ 2 * β * At ^ (P - 2) ≤
      At ^ P / n + 10 * P ^ 2 * b * (max 1 (10 * (P : ℝ) ^ 2 * b)) ^ (P - 2) * n ^ (P - 1) := by
    have hl := lin_pow (10 * P ^ 2 * b) 1 x (P - 2) P (by omega) (by positivity) one_pos hx0
    rw [div_one] at hl
    have hl' := mul_le_mul_of_nonneg_left hl (by positivity : (0 : ℝ) ≤ n ^ (P - 1))
    have e1 : n ^ (P - 1) * (1 * x ^ P) = At ^ P / n := by
      rw [hAx, mul_pow, ← pow_pred_mul n P (by omega)]; field_simp
    have e2 : n ^ (P - 1) * (10 * P ^ 2 * b * x ^ (P - 2)) =
        10 * P ^ 2 * (b * n) * At ^ (P - 2) := by
      rw [hAx, mul_pow, ← pow_sub2_mul n P (by omega)]; ring
    rw [mul_add, e1, e2] at hl'
    have h4 : 10 * P ^ 2 * β * At ^ (P - 2) ≤ 10 * P ^ 2 * (b * n) * At ^ (P - 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hβb (by positivity)
    have e3 : n ^ (P - 1) * (10 * P ^ 2 * b * (max 1 (10 * (P : ℝ) ^ 2 * b)) ^ (P - 2)) =
        10 * P ^ 2 * b * (max 1 (10 * (P : ℝ) ^ 2 * b)) ^ (P - 2) * n ^ (P - 1) := by ring
    rw [e3] at hl'
    linarith only [hl', h4]
  have e5 : (1 + 1152 * P ^ 2 / B) / n * At ^ P = At ^ P / n + 1152 * P ^ 2 / B / n * At ^ P := by
    ring
  rw [e5]
  linarith only [h1, h2, h3]

/-- curvature term, small branch -/
lemma abs_curv_small (P : ℕ) (hP : 4 ≤ P) (B b β n At M : ℝ) (hB : 2 ^ 20 * (P : ℝ) ≤ B)
    (hn : 1 ≤ n) (hβ : 0 < β) (hβb : β ≤ b * n) (hA0 : 0 ≤ At) (hsmall : At < 8 * P * β)
    (hM0 : 0 ≤ M) (hM : M ≤ 3 * β + 24 * At / B) :
    (10 * β + 1152 * At ^ 2 / (B * n)) * (P ^ 2 / 2 * (At + M) ^ (P - 2)) ≤
      P ^ 2 / 2 * (12 * P * b) ^ (P - 2) * (10 * b + 73728 * P ^ 2 * b ^ 2 / B) * n ^ (P - 1) := by
  have hPr : (4 : ℝ) ≤ P := by exact_mod_cast hP
  have hB0 : 0 < B := by linarith
  have hn0 : 0 < n := by linarith
  have hb0 : 0 ≤ b := by
    by_contra h; push_neg at h; nlinarith
  have hAM : At + M ≤ 12 * P * β := by
    have h2 : 24 * At / B ≤ β := by
      rw [div_le_iff₀ hB0]; nlinarith
    nlinarith
  have hV : 10 * β + 1152 * At ^ 2 / (B * n) ≤ (10 * b + 73728 * P ^ 2 * b ^ 2 / B) * n := by
    have h1 : At ^ 2 ≤ 64 * P ^ 2 * β ^ 2 := by nlinarith
    have h2 : β ^ 2 ≤ b ^ 2 * n ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hβ.le hβb 2
    have h3 : 1152 * At ^ 2 / (B * n) ≤ 73728 * P ^ 2 * b ^ 2 / B * n := by
      rw [div_le_iff₀ (by positivity)]
      have h4 : 1152 * At ^ 2 ≤ 73728 * P ^ 2 * (b ^ 2 * n ^ 2) := by nlinarith
      have e : 73728 * P ^ 2 * b ^ 2 / B * n * (B * n) = 73728 * P ^ 2 * (b ^ 2 * n ^ 2) := by
        field_simp
      linarith
    have h5 : 10 * β ≤ 10 * b * n := by linarith
    nlinarith
  have hpow : (At + M) ^ (P - 2) ≤ (12 * P * b) ^ (P - 2) * n ^ (P - 2) := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) (hAM.trans ?_) _
    have := mul_le_mul_of_nonneg_left hβb (by positivity : (0 : ℝ) ≤ 12 * P)
    linarith
  calc (10 * β + 1152 * At ^ 2 / (B * n)) * (P ^ 2 / 2 * (At + M) ^ (P - 2))
      ≤ ((10 * b + 73728 * P ^ 2 * b ^ 2 / B) * n) *
          (P ^ 2 / 2 * ((12 * P * b) ^ (P - 2) * n ^ (P - 2))) :=
        mul_le_mul hV (mul_le_mul_of_nonneg_left hpow (by positivity)) (by positivity)
          (by positivity)
    _ = _ := by rw [← pow_sub2_mul n P (by omega)]; ring

/-- **absolute recurrence, pathwise** -/
lemma abs_alg (P : ℕ) (hP : 4 ≤ P) (B b β n G At R I1 I2 : ℝ) (hB : 2 ^ 20 * (P : ℝ) ≤ B)
    (hn : 1 ≤ n) (hβ : 0 < β) (hβb : β ≤ b * n) (hAt : β ≤ At)
    (hcase : 8 * P * β ≤ At → At ^ P = G) (hAtG : At ^ P ≤ G + β ^ P) (hG : 0 ≤ G)
    (hR : 0 ≤ R) (hR8 : R ≤ 8 * At) (hI1 : I1 ≤ At ^ (P - 1))
    (hI2 : I2 ≤ (At + (3 * β + 3 * R / B)) ^ (P - 2)) (hI20 : 0 ≤ I2) :
    G + 2 * P * I1 + (10 * β + 18 * R ^ 2 / (B * n)) * ((P * (P - 1 : ℝ) / 2) * I2) ≤
      (1 + (3 + 1152 * P ^ 2 / B) / n) * G + Kabs P b B * n ^ (P - 1) := by
  have hPr : (4 : ℝ) ≤ P := by exact_mod_cast hP
  have hB0 : 0 < B := by linarith
  have hn0 : 0 < n := by linarith
  have hA0 : 0 < At := lt_of_lt_of_le hβ hAt
  have hdrift := abs_drift P (by omega) b β n G At hn0 hβ.le hβb hA0.le hAtG
  have hd' : 2 * P * I1 ≤ 2 * P * At ^ (P - 1) := mul_le_mul_of_nonneg_left hI1 (by positivity)
  set M := 3 * β + 3 * R / B with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hM : M ≤ 3 * β + 24 * At / B := by
    have : 3 * R / B ≤ 24 * At / B := div_le_div_of_nonneg_right (by linarith) hB0.le
    linarith
  have hc0 : 0 ≤ (P * (P - 1 : ℝ) / 2) := by nlinarith
  have hcP : (P * (P - 1 : ℝ) / 2) ≤ P ^ 2 / 2 := by nlinarith
  have hVR : 10 * β + 18 * R ^ 2 / (B * n) ≤ 10 * β + 1152 * At ^ 2 / (B * n) := by
    have : 18 * R ^ 2 ≤ 1152 * At ^ 2 := by nlinarith
    gcongr
  have hX : (10 * β + 18 * R ^ 2 / (B * n)) * ((P * (P - 1 : ℝ) / 2) * I2) ≤
      (10 * β + 1152 * At ^ 2 / (B * n)) * (P ^ 2 / 2 * (At + M) ^ (P - 2)) := by
    apply mul_le_mul hVR _ (by positivity) (by positivity)
    exact mul_le_mul hcP hI2 hI20 (by positivity)
  have hK0 : 0 ≤ 10 * P ^ 2 * b * (max 1 (10 * (P : ℝ) ^ 2 * b)) ^ (P - 2) := by
    have : 0 ≤ b := by by_contra h; push_neg at h; nlinarith
    positivity
  have hK1 : 0 ≤ P ^ 2 / 2 * (12 * P * b) ^ (P - 2) * (10 * b + 73728 * P ^ 2 * b ^ 2 / B) := by
    have : 0 ≤ b := by by_contra h; push_neg at h; nlinarith
    positivity
  have hcurv : (10 * β + 1152 * At ^ 2 / (B * n)) * (P ^ 2 / 2 * (At + M) ^ (P - 2)) ≤
      (1 + 1152 * P ^ 2 / B) / n * G +
        (10 * P ^ 2 * b * (max 1 (10 * (P : ℝ) ^ 2 * b)) ^ (P - 2) +
          P ^ 2 / 2 * (12 * P * b) ^ (P - 2) * (10 * b + 73728 * P ^ 2 * b ^ 2 / B)) * n ^ (P - 1) := by
    have hnn : 0 ≤ n ^ (P - 1) := by positivity
    rw [add_mul]
    rcases le_or_gt (8 * P * β) At with hbig | hsmall
    · have h := abs_curv_big P hP B b β n At M hB hn0 hβ hβb hbig hM0 hM
      have h1 := mul_nonneg hK1 hnn
      rw [hcase hbig] at h
      linarith only [h, h1]
    · have h := abs_curv_small P hP B b β n At M hB hn hβ hβb hA0.le hsmall hM0 hM
      have h1 : 0 ≤ (1 + 1152 * P ^ 2 / B) / n * G := by positivity
      have h2 := mul_nonneg hK0 hnn
      linarith only [h, h1, h2]
  unfold Kabs
  set K0 := 10 * P ^ 2 * b * (max 1 (10 * (P : ℝ) ^ 2 * b)) ^ (P - 2)
  set K1 := P ^ 2 / 2 * (12 * P * b) ^ (P - 2) * (10 * b + 73728 * P ^ 2 * b ^ 2 / B)
  set Kd := 2 * P * (max 1 (2 * (P : ℝ))) ^ (P - 1) + b ^ P
  have e : (1 + (3 + 1152 * P ^ 2 / B) / n) * G =
      G + G / n + ((1 + 1152 * P ^ 2 / B) / n * G + G / n) := by
    field_simp; ring
  have e2 : (2 * P * (max 1 (2 * (P : ℝ))) ^ (P - 1) + b ^ P + K0 + K1) * n ^ (P - 1) =
      Kd * n ^ (P - 1) + (K0 + K1) * n ^ (P - 1) := by ring
  rw [e, e2]
  have : 0 ≤ G / n := by positivity
  linarith only [hdrift, hd', hX, hcurv, this]

end G26


-- ===== Solutions.G26.J11 =====

/-! ### Lemma J.11: uniform estimates for affine functions on a convex body -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace J11

variable {d : ℕ}

section

variable {D : Set (Fin d → ℝ)} (hD : IsCompact D) (hconv : Convex ℝ D) (hne : D.Nonempty)
include hD hconv hne

lemma haus_pos_fin : 0 < μH[(rdim D : ℝ)] D ∧ μH[(rdim D : ℝ)] D < ∞ :=
  G11.hausdorff_pos_fin hD hconv hne

lemma nvol_prob : IsProbabilityMeasure (nvol D) := by
  obtain ⟨h1, h2⟩ := haus_pos_fin hD hconv hne
  exact cond_isProbabilityMeasure_of_finite h1.ne' h2.ne

omit hconv hne in
lemma nvol_supp : nvol D Dᶜ = 0 := by
  unfold nvol
  rw [cond_apply hD.isClosed.measurableSet, Set.inter_compl_self, measure_empty, mul_zero]

/-- a homothetic copy of `D` with ratio `λ ∈ (0, 1]` has normalized volume `λ^r` -/
lemma nvol_hom {x0 : Fin d → ℝ} (hx0 : x0 ∈ D) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    AffineMap.homothety x0 r '' D ⊆ D ∧
    nvol D (AffineMap.homothety x0 r '' D) = ENNReal.ofReal (r ^ rdim D) := by
  obtain ⟨hHpos, hHfin⟩ := haus_pos_fin hD hconv hne
  have hhom : ∀ x, AffineMap.homothety x0 r x = r • (x - x0) + x0 := fun x => by
    rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  have hsub : AffineMap.homothety x0 r '' D ⊆ D := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hhom]
    have := hconv hx0 hx (by linarith : (0 : ℝ) ≤ 1 - r) hr0.le (by ring)
    convert this using 1
    rw [smul_sub, sub_smul, one_smul]; abel
  refine ⟨hsub, ?_⟩
  set c : ℝ≥0∞ := ((‖r‖₊ ^ (rdim D : ℝ) : ℝ≥0) : ℝ≥0∞) with hc
  have hlam : nvol D (AffineMap.homothety x0 r '' D) = c := by
    unfold nvol
    rw [cond_apply hD.isClosed.measurableSet, Set.inter_eq_right.2 hsub,
      hausdorffMeasure_homothety_image (Nat.cast_nonneg _) x0 hr0.ne', ENNReal.smul_def,
      smul_eq_mul, ← mul_assoc, mul_comm _ (c : ℝ≥0∞), mul_assoc,
      ENNReal.inv_mul_cancel hHpos.ne' hHfin.ne, mul_one]
  rw [hlam, hc, ← ENNReal.ofReal_coe_nnreal]
  congr 1
  rw [NNReal.coe_rpow, coe_nnnorm, Real.norm_eq_abs, abs_of_pos hr0, Real.rpow_natCast]

/-- **The contraction lower bound**: if `g ≥ c ≥ 0` on the `λ`-contraction of `D` toward
`x0`, then `∫ g dσ ≥ λ^r c` -/
lemma contr_lb {x0 : Fin d → ℝ} (hx0 : x0 ∈ D) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    {g : (Fin d → ℝ) → ℝ} (hg : Integrable g (nvol D)) (hg0 : ∀ x ∈ D, 0 ≤ g x) {c : ℝ}
    (hc : 0 ≤ c) (hgc : ∀ x ∈ D, c ≤ g (AffineMap.homothety x0 r x)) :
    r ^ rdim D * c ≤ ∫ x, g x ∂(nvol D) := by
  haveI := nvol_prob hD hconv hne
  obtain ⟨hsub, hvol⟩ := nvol_hom hD hconv hne hx0 hr0 hr1
  set H := AffineMap.homothety x0 r '' D with hH
  have hHm : MeasurableSet H :=
    (hD.image (AffineMap.homothety x0 r).continuous_of_finiteDimensional).isClosed.measurableSet
  have hsupp := nvol_supp hD
  have h1 : ∫ x, H.indicator (fun _ => c) x ∂(nvol D) ≤ ∫ x, g x ∂(nvol D) := by
    refine integral_mono_ae ((integrable_const c).indicator hHm) hg ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hsupp] with x hx
    simp only [Set.mem_compl_iff, not_not] at hx
    by_cases hxH : x ∈ H
    · rw [indicator_of_mem hxH]
      obtain ⟨y, hy, rfl⟩ := hxH
      exact hgc y hy
    · rw [indicator_of_notMem hxH]; exact hg0 x hx
  rw [integral_indicator hHm, setIntegral_const, smul_eq_mul, measureReal_def, hvol,
    ENNReal.toReal_ofReal (pow_nonneg hr0.le _)] at h1
  exact h1

end

/-- affine functions along a homothety -/
lemma aff_hom' (v : Fin d → ℝ) (c : ℝ) (x0 x : Fin d → ℝ) (r : ℝ) :
    AffineMap.homothety x0 r x ⬝ᵥ v + c = (1 - r) * (x0 ⬝ᵥ v + c) + r * (x ⬝ᵥ v + c) := by
  rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  simp only [add_dotProduct, smul_dotProduct, sub_dotProduct, smul_eq_mul]; ring

section Ineq

variable {D : Set (Fin d → ℝ)} (hD : IsCompact D) (hconv : Convex ℝ D) (hne : D.Nonempty)
include hD hconv hne

lemma cont_aff (v : Fin d → ℝ) (c : ℝ) : Continuous fun x : Fin d → ℝ => x ⬝ᵥ v + c := by
  simp only [dotProduct]; fun_prop

/-- **(J.17)** `R^p ≤ 2^p 4^r ∫ |f|^p dσ` at a maximizer of `|f|` -/
theorem J17 (v : Fin d → ℝ) (c : ℝ) {x0 : Fin d → ℝ} (hx0 : x0 ∈ D)
    (hmax : ∀ x ∈ D, |x ⬝ᵥ v + c| ≤ |x0 ⬝ᵥ v + c|) (p : ℕ) :
    |x0 ⬝ᵥ v + c| ^ p ≤ 2 ^ p * 4 ^ rdim D * ∫ x, |x ⬝ᵥ v + c| ^ p ∂(nvol D) := by
  haveI := nvol_prob hD hconv hne
  set R := |x0 ⬝ᵥ v + c| with hR
  have hR0 : 0 ≤ R := abs_nonneg _
  have hfc := (cont_aff hD hconv hne v c).abs.pow p
  have hint : Integrable (fun x => |x ⬝ᵥ v + c| ^ p) (nvol D) := by
    obtain ⟨Cb, hCb⟩ := hD.exists_bound_of_continuousOn hfc.continuousOn
    refine Integrable.of_bound hfc.aestronglyMeasurable Cb ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (nvol_supp hD)] with x hx
    simp only [Set.mem_compl_iff, not_not] at hx
    exact hCb x hx
  have h := contr_lb hD hconv hne hx0 (r := 1 / 4) (by norm_num) (by norm_num) hint
    (fun x _ => by positivity) (c := (R / 2) ^ p) (by positivity) (fun x hx => by
      refine pow_le_pow_left₀ (by positivity) ?_ p
      rw [aff_hom']
      have h1 := hmax x hx
      have h2 := abs_le.1 h1
      rcases le_total 0 (x0 ⬝ᵥ v + c) with h0 | h0
      · rw [hR, abs_of_nonneg h0] at h2 ⊢
        rw [abs_of_nonneg (by nlinarith)]; nlinarith
      · rw [hR, abs_of_nonpos h0] at h2 ⊢
        rw [abs_of_nonpos (by nlinarith)]; nlinarith)
  have e : R ^ p = 2 ^ p * 4 ^ rdim D * ((1 / 4) ^ rdim D * (R / 2) ^ p) := by
    rw [div_pow, div_pow, one_pow]; field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left h (by positivity)

end Ineq

end J11


-- ===== Solutions.G26.Supp =====

/-! ### Support functions and extrema of affine fields on a compact body -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {d : ℕ}

/-- the `ℓ¹` radius of `D` -/
noncomputable def rad1 (D : Set (Fin d → ℝ)) : ℝ := sSup ((fun u : Fin d → ℝ => ∑ i, |u i|) '' D)

lemma abs_dot_le (u v : Fin d → ℝ) : |u ⬝ᵥ v| ≤ (∑ i, |u i|) * ‖v‖ := by
  unfold dotProduct
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (abs_nonneg _)

section

variable {D : Set (Fin d → ℝ)} (hD : IsCompact D)
include hD

lemma bdd_img (w : Fin d → ℝ) : BddAbove ((fun u => u ⬝ᵥ w) '' D) :=
  (hD.image (by simp only [dotProduct]; fun_prop)).bddAbove

lemma le_supp {u : Fin d → ℝ} (hu : u ∈ D) (w : Fin d → ℝ) : u ⬝ᵥ w ≤ supp D w :=
  le_csSup (bdd_img hD w) ⟨u, hu, rfl⟩

lemma supp_mem (hne : D.Nonempty) (w : Fin d → ℝ) : ∃ u ∈ D, u ⬝ᵥ w = supp D w := by
  have hc : IsCompact ((fun u => u ⬝ᵥ w) '' D) :=
    hD.image (by simp only [dotProduct]; fun_prop)
  obtain ⟨u, hu, he⟩ := hc.sSup_mem (hne.image _)
  exact ⟨u, hu, he⟩

lemma le_rad1 {u : Fin d → ℝ} (hu : u ∈ D) : ∑ i, |u i| ≤ rad1 D :=
  le_csSup (hD.image (by fun_prop)).bddAbove ⟨u, hu, rfl⟩

lemma supp_sub_le (hne : D.Nonempty) (w w' : Fin d → ℝ) :
    supp D w - supp D w' ≤ rad1 D * ‖w - w'‖ := by
  obtain ⟨u, hu, he⟩ := supp_mem hD hne w
  have h1 := le_supp hD hu w'
  have h2 := abs_dot_le u (w - w')
  have h3 : (∑ i, |u i|) * ‖w - w'‖ ≤ rad1 D * ‖w - w'‖ :=
    mul_le_mul_of_nonneg_right (le_rad1 hD hu) (norm_nonneg _)
  rw [dotProduct_sub] at h2
  have := (abs_le.1 h2).2
  linarith

lemma rad1_nonneg (hne : D.Nonempty) : 0 ≤ rad1 D := by
  obtain ⟨u, hu⟩ := hne
  exact le_trans (Finset.sum_nonneg fun i _ => abs_nonneg _) (le_rad1 hD hu)

lemma supp_lip (hne : D.Nonempty) : LipschitzWith (Real.toNNReal (rad1 D)) (supp D) := by
  refine LipschitzWith.of_dist_le_mul fun w w' => ?_
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (rad1_nonneg hD hne)]
  refine abs_le.2 ⟨?_, supp_sub_le hD hne w w'⟩
  have := supp_sub_le hD hne w' w
  rw [norm_sub_rev] at this
  linarith

lemma supp_cont (hne : D.Nonempty) : Continuous (supp D) := (supp_lip hD hne).continuous

lemma negMax_ge {u : Fin d → ℝ} (hu : u ∈ D) (V : Fin d → ℝ) (c : ℝ) :
    -(u ⬝ᵥ V + c) ≤ negMax D V c := by
  have := le_supp hD hu (-V)
  rw [dotProduct_neg] at this
  unfold negMax; linarith

lemma posMax_ge {u : Fin d → ℝ} (hu : u ∈ D) (V : Fin d → ℝ) (c : ℝ) :
    u ⬝ᵥ V + c ≤ posMax D V c := by
  have := le_supp hD hu V
  unfold posMax; linarith

lemma abs_le_absMax {u : Fin d → ℝ} (hu : u ∈ D) (V : Fin d → ℝ) (c : ℝ) :
    |u ⬝ᵥ V + c| ≤ absMax D V c := by
  unfold absMax
  refine abs_le.2 ⟨?_, le_trans (posMax_ge hD hu V c) (le_max_left _ _)⟩
  have := le_trans (negMax_ge hD hu V c) (le_max_right (posMax D V c) _)
  linarith

omit hD in
lemma negMax_le_absMax (V : Fin d → ℝ) (c : ℝ) : negMax D V c ≤ absMax D V c :=
  le_max_right _ _

lemma negMax_mem (hne : D.Nonempty) (V : Fin d → ℝ) (c : ℝ) :
    ∃ u ∈ D, -(u ⬝ᵥ V + c) = negMax D V c := by
  obtain ⟨u, hu, he⟩ := supp_mem hD hne (-V)
  refine ⟨u, hu, ?_⟩
  rw [dotProduct_neg] at he
  unfold negMax; linarith

lemma posMax_mem (hne : D.Nonempty) (V : Fin d → ℝ) (c : ℝ) :
    ∃ u ∈ D, u ⬝ᵥ V + c = posMax D V c := by
  obtain ⟨u, hu, he⟩ := supp_mem hD hne V
  exact ⟨u, hu, by unfold posMax; linarith⟩

/-- the absolute maximum is attained -/
lemma absMax_mem (hne : D.Nonempty) (V : Fin d → ℝ) (c : ℝ) :
    ∃ u ∈ D, |u ⬝ᵥ V + c| = absMax D V c ∧ ∀ x ∈ D, |x ⬝ᵥ V + c| ≤ |u ⬝ᵥ V + c| := by
  obtain ⟨u1, hu1, h1⟩ := posMax_mem hD hne V c
  obtain ⟨u2, hu2, h2⟩ := negMax_mem hD hne V c
  rcases le_total (negMax D V c) (posMax D V c) with h | h
  · have hA : absMax D V c = posMax D V c := max_eq_left h
    have hval : |u1 ⬝ᵥ V + c| = absMax D V c := by
      rw [hA, h1]
      refine abs_of_nonneg ?_
      have := negMax_ge hD hu1 V c
      linarith
    exact ⟨u1, hu1, hval, fun x hx => hval ▸ abs_le_absMax hD hx V c⟩
  · have hA : absMax D V c = negMax D V c := max_eq_right h
    have hval : |u2 ⬝ᵥ V + c| = absMax D V c := by
      rw [hA, ← h2, abs_of_nonpos]
      have := posMax_ge hD hu2 V c
      linarith
    exact ⟨u2, hu2, hval, fun x hx => hval ▸ abs_le_absMax hD hx V c⟩

lemma negMax_cont (hne : D.Nonempty) :
    Continuous fun p : (Fin d → ℝ) × ℝ => negMax D p.1 p.2 := by
  unfold negMax
  exact ((supp_cont hD hne).comp continuous_fst.neg).sub continuous_snd

lemma posMax_cont (hne : D.Nonempty) :
    Continuous fun p : (Fin d → ℝ) × ℝ => posMax D p.1 p.2 := by
  unfold posMax
  exact ((supp_cont hD hne).comp continuous_fst).add continuous_snd

lemma absMax_cont (hne : D.Nonempty) :
    Continuous fun p : (Fin d → ℝ) × ℝ => absMax D p.1 p.2 :=
  (posMax_cont hD hne).max (negMax_cont hD hne)

lemma absMax_meas (hne : D.Nonempty) {Ω : Type*} {m : MeasurableSpace Ω} {V : Ω → Fin d → ℝ}
    {c : Ω → ℝ} (hV : Measurable V) (hc : Measurable c) :
    Measurable fun ω => absMax D (V ω) (c ω) := by
  have h := (absMax_cont hD hne).measurable
  exact h.comp (f := fun ω => (V ω, c ω)) (hV.prodMk hc)

end

end G26


-- ===== Solutions.G26.Step =====

/-! ### The killed one-step expectation tool, pointwise and integrated over a body -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : ℕ → MeasurableSpace Ω} {n : ℕ}

lemma int_of_ae_bdd {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) {c : ℝ}
    (h : ∀ᵐ ω ∂μ, |f ω| ≤ c) : Integrable f μ :=
  Integrable.of_bound hf c (by filter_upwards [h] with ω hω; rwa [Real.norm_eq_abs])

/-- **Killed second-order step.** If on `J ∈ F` the next value obeys a second-order
expansion `H ≤ g₀ + g₁ ξ + g₂ ξ²` with `F`-measurable `g₁, g₂ ≥ 0`, then the conditional
drift and second-moment bounds may be substituted. -/
lemma pstep (hF : F n ≤ mΩ) {J : Set Ω} (hJ : MeasurableSet[F n] J)
    {H g0 g1 g2 ξ b1 V : Ω → ℝ} {c : ℝ}
    (hHm : AEStronglyMeasurable H μ) (hg0m : AEStronglyMeasurable g0 μ)
    (hg1m : StronglyMeasurable[F n] g1) (hg2m : StronglyMeasurable[F n] g2)
    (hξm : AEStronglyMeasurable ξ μ) (hb1m : AEStronglyMeasurable b1 μ)
    (hVm : AEStronglyMeasurable V μ)
    (hbd : ∀ᵐ ω ∂μ, |H ω| ≤ c ∧ |g0 ω| ≤ c ∧ |g1 ω| ≤ c ∧ |g2 ω| ≤ c ∧ |ξ ω| ≤ c ∧
      |b1 ω| ≤ c ∧ |V ω| ≤ c)
    (hpt : ∀ᵐ ω ∂μ, ω ∈ J → H ω ≤ g0 ω + g1 ω * ξ ω + g2 ω * ξ ω ^ 2)
    (hdr : ∀ᵐ ω ∂μ, ω ∈ J → g1 ω * μ[ξ | F n] ω ≤ b1 ω)
    (hse : ∀ᵐ ω ∂μ, ω ∈ J → μ[fun ω => ξ ω ^ 2 | F n] ω ≤ V ω)
    (hg2n : ∀ᵐ ω ∂μ, ω ∈ J → 0 ≤ g2 ω) :
    ∫ ω, J.indicator H ω ∂μ ≤ ∫ ω, J.indicator (fun ω => g0 ω + b1 ω + g2 ω * V ω) ω ∂μ := by
  have hJm : MeasurableSet J := hF _ hJ
  set G1 := J.indicator g1 with hG1
  set G2 := J.indicator g2 with hG2
  have hG1m : StronglyMeasurable[F n] G1 := hg1m.indicator hJ
  have hG2m : StronglyMeasurable[F n] G2 := hg2m.indicator hJ
  have hc : ∀ᵐ ω ∂μ, 0 ≤ c := by
    filter_upwards [hbd] with ω h; exact le_trans (abs_nonneg _) h.1
  have hbG1 : ∀ᵐ ω ∂μ, ‖G1 ω‖ ≤ c := by
    filter_upwards [hbd, hc] with ω h hc0
    simp only [G1, Real.norm_eq_abs]
    by_cases hω : ω ∈ J
    · rw [Set.indicator_of_mem hω]; exact h.2.2.1
    · rw [Set.indicator_of_notMem hω, abs_zero]; exact hc0
  have hbG2 : ∀ᵐ ω ∂μ, ‖G2 ω‖ ≤ c := by
    filter_upwards [hbd, hc] with ω h hc0
    simp only [G2, Real.norm_eq_abs]
    by_cases hω : ω ∈ J
    · rw [Set.indicator_of_mem hω]; exact h.2.2.2.1
    · rw [Set.indicator_of_notMem hω, abs_zero]; exact hc0
  have hξi : Integrable ξ μ := int_of_ae_bdd hξm (by filter_upwards [hbd] with ω h; exact h.2.2.2.2.1)
  have hξ2i : Integrable (fun ω => ξ ω ^ 2) μ := by
    refine int_of_ae_bdd (hξm.pow 2) (c := c ^ 2) ?_
    filter_upwards [hbd] with ω h
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h.2.2.2.2.1 2
  have hG1a : AEStronglyMeasurable G1 μ := (hG1m.mono hF).aestronglyMeasurable
  have hG2a : AEStronglyMeasurable G2 μ := (hG2m.mono hF).aestronglyMeasurable
  have i1 : Integrable (G1 * ξ) μ := hξi.bdd_mul hG1a hbG1
  have i2 : Integrable (G2 * fun ω => ξ ω ^ 2) μ := hξ2i.bdd_mul hG2a hbG2
  have hg0i : Integrable (J.indicator g0) μ :=
    (int_of_ae_bdd hg0m (by filter_upwards [hbd] with ω h; exact h.2.1)).indicator hJm
  have hHi : Integrable (J.indicator H) μ :=
    (int_of_ae_bdd hHm (by filter_upwards [hbd] with ω h; exact h.1)).indicator hJm
  -- the conditional substitutions
  have e1 : ∫ ω, (G1 * ξ) ω ∂μ = ∫ ω, (G1 * μ[ξ | F n]) ω ∂μ := by
    rw [← integral_condExp hF]
    exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hG1m i1 hξi)
  have e2 : ∫ ω, (G2 * fun ω => ξ ω ^ 2) ω ∂μ =
      ∫ ω, (G2 * μ[fun ω => ξ ω ^ 2 | F n]) ω ∂μ := by
    rw [← integral_condExp hF]
    exact integral_congr_ae (condExp_mul_of_stronglyMeasurable_left hG2m i2 hξ2i)
  have j1 : Integrable (G1 * μ[ξ | F n]) μ := integrable_condExp.bdd_mul hG1a hbG1
  have j2 : Integrable (G2 * μ[fun ω => ξ ω ^ 2 | F n]) μ := integrable_condExp.bdd_mul hG2a hbG2
  have hRi : Integrable (J.indicator fun ω => g0 ω + b1 ω + g2 ω * V ω) μ := by
    refine (int_of_ae_bdd (c := c + c + c * c) ((hg0m.add hb1m).add
      ((hg2m.mono hF).aestronglyMeasurable.mul hVm)) ?_).indicator hJm
    filter_upwards [hbd] with ω h
    obtain ⟨-, h0, -, h2, -, hb, hV⟩ := h
    calc |g0 ω + b1 ω + g2 ω * V ω| ≤ |g0 ω| + |b1 ω| + |g2 ω| * |V ω| := by
          rw [← abs_mul]
          exact le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ c + c + c * c := by
          gcongr
          exact le_trans (abs_nonneg _) h0
  calc ∫ ω, J.indicator H ω ∂μ
      ≤ ∫ ω, (J.indicator g0 ω + (G1 * ξ) ω + (G2 * fun ω => ξ ω ^ 2) ω) ∂μ := by
        refine integral_mono_ae hHi ((hg0i.add i1).add i2) ?_
        filter_upwards [hpt] with ω hω
        by_cases hJω : ω ∈ J
        · simp only [Set.indicator_of_mem hJω, G1, G2, Pi.mul_apply]
          exact hω hJω
        · simp [Set.indicator_of_notMem hJω, G1, G2]
    _ = ∫ ω, J.indicator g0 ω ∂μ + ∫ ω, (G1 * ξ) ω ∂μ + ∫ ω, (G2 * fun ω => ξ ω ^ 2) ω ∂μ := by
        rw [integral_add (f := fun ω => J.indicator g0 ω + (G1 * ξ) ω)
          (g := fun ω => (G2 * fun ω => ξ ω ^ 2) ω) (hg0i.add i1) i2,
          integral_add (f := fun ω => J.indicator g0 ω) (g := fun ω => (G1 * ξ) ω) hg0i i1]
    _ = ∫ ω, (J.indicator g0 ω + (G1 * μ[ξ | F n]) ω + (G2 * μ[fun ω => ξ ω ^ 2 | F n]) ω) ∂μ := by
        rw [e1, e2, integral_add (f := fun ω => J.indicator g0 ω + (G1 * μ[ξ | F n]) ω)
          (g := fun ω => (G2 * μ[fun ω => ξ ω ^ 2 | F n]) ω) (hg0i.add j1) j2,
          integral_add (f := fun ω => J.indicator g0 ω) (g := fun ω => (G1 * μ[ξ | F n]) ω)
            hg0i j1]
    _ ≤ ∫ ω, J.indicator (fun ω => g0 ω + b1 ω + g2 ω * V ω) ω ∂μ := by
        refine integral_mono_ae ((hg0i.add j1).add j2) hRi ?_
        filter_upwards [hdr, hse, hg2n] with ω hd hs hn
        by_cases hJω : ω ∈ J
        · simp only [Set.indicator_of_mem hJω, G1, G2, Pi.mul_apply]
          have := mul_le_mul_of_nonneg_left (hs hJω) (hn hJω)
          linarith [hd hJω]
        · simp [Set.indicator_of_notMem hJω, G1, G2]

/-- **Integrated killed step** over a probability measure `σ` concentrated on `D`. -/
lemma istep {E : Type*} [MeasurableSpace E] {σ : Measure E} [IsProbabilityMeasure σ]
    {D : Set E} (hσ : σ Dᶜ = 0) (hF : F n ≤ mΩ) {J : Set Ω} (hJ : MeasurableSet[F n] J)
    {H g0 g1 g2 ξ b1 V : E → Ω → ℝ} {c : ℝ}
    (hHj : Measurable (Function.uncurry H))
    (hRj : Measurable (Function.uncurry fun u ω => g0 u ω + b1 u ω + g2 u ω * V u ω))
    (hg0m : ∀ u ∈ D, AEStronglyMeasurable (g0 u) μ)
    (hg1m : ∀ u ∈ D, StronglyMeasurable[F n] (g1 u)) (hg2m : ∀ u ∈ D, StronglyMeasurable[F n] (g2 u))
    (hξm : ∀ u ∈ D, AEStronglyMeasurable (ξ u) μ) (hb1m : ∀ u ∈ D, AEStronglyMeasurable (b1 u) μ)
    (hVm : ∀ u ∈ D, AEStronglyMeasurable (V u) μ)
    (hbd : ∀ u ∈ D, ∀ᵐ ω ∂μ, |H u ω| ≤ c ∧ |g0 u ω| ≤ c ∧ |g1 u ω| ≤ c ∧ |g2 u ω| ≤ c ∧
      |ξ u ω| ≤ c ∧ |b1 u ω| ≤ c ∧ |V u ω| ≤ c)
    (hpt : ∀ u ∈ D, ∀ᵐ ω ∂μ, ω ∈ J → H u ω ≤ g0 u ω + g1 u ω * ξ u ω + g2 u ω * ξ u ω ^ 2)
    (hdr : ∀ u ∈ D, ∀ᵐ ω ∂μ, ω ∈ J → g1 u ω * μ[ξ u | F n] ω ≤ b1 u ω)
    (hse : ∀ u ∈ D, ∀ᵐ ω ∂μ, ω ∈ J → μ[fun ω => ξ u ω ^ 2 | F n] ω ≤ V u ω)
    (hg2n : ∀ u ∈ D, ∀ᵐ ω ∂μ, ω ∈ J → 0 ≤ g2 u ω) :
    ∫ ω, J.indicator (fun ω => ∫ u, H u ω ∂σ) ω ∂μ ≤
      ∫ ω, J.indicator (fun ω => ∫ u, (g0 u ω + b1 u ω + g2 u ω * V u ω) ∂σ) ω ∂μ := by
  have hJm : MeasurableSet J := hF _ hJ
  have hDae : ∀ᵐ u ∂σ, u ∈ D := measure_eq_zero_iff_ae_notMem.1 hσ |>.mono fun u hu => by
    simpa using hu
  set R : E → Ω → ℝ := fun u ω => g0 u ω + b1 u ω + g2 u ω * V u ω with hR
  -- bounds on the product
  have hbdR : ∀ u ∈ D, ∀ᵐ ω ∂μ, |H u ω| ≤ c ∧ |R u ω| ≤ c + c + c * c := by
    intro u hu
    filter_upwards [hbd u hu] with ω h
    obtain ⟨hH, h0, -, h2, -, hb, hV⟩ := h
    refine ⟨hH, ?_⟩
    calc |R u ω| ≤ |g0 u ω| + |b1 u ω| + |g2 u ω| * |V u ω| := by
          simp only [R]
          rw [← abs_mul]
          exact le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ c + c + c * c := by
          gcongr
          exact le_trans (abs_nonneg _) h0
  -- the swapped integrands
  set fH : E → Ω → ℝ := fun u ω => J.indicator (H u) ω with hfH
  set fR : E → Ω → ℝ := fun u ω => J.indicator (R u) ω with hfR
  have hfHm : Measurable (Function.uncurry fH) := by
    have : Function.uncurry fH = (fun p : E × Ω => (Set.univ ×ˢ J).indicator
        (Function.uncurry H) p) := by
      funext ⟨u, ω⟩
      simp only [fH, Function.uncurry_apply_pair, Set.indicator]
      by_cases hω : ω ∈ J
      · rw [if_pos hω, if_pos (Set.mk_mem_prod (Set.mem_univ u) hω)]
      · rw [if_neg hω, if_neg (fun h => hω (Set.mem_prod.1 h).2)]
    rw [this]; exact hHj.indicator (MeasurableSet.univ.prod hJm)
  have hfRm : Measurable (Function.uncurry fR) := by
    have : Function.uncurry fR = (fun p : E × Ω => (Set.univ ×ˢ J).indicator
        (Function.uncurry R) p) := by
      funext ⟨u, ω⟩
      simp only [fR, Function.uncurry_apply_pair, Set.indicator]
      by_cases hω : ω ∈ J
      · rw [if_pos hω, if_pos (Set.mk_mem_prod (Set.mem_univ u) hω)]
      · rw [if_neg hω, if_neg (fun h => hω (Set.mem_prod.1 h).2)]
    rw [this]; exact hRj.indicator (MeasurableSet.univ.prod hJm)
  have hprodbd : ∀ {f : E → Ω → ℝ} (_ : Measurable (Function.uncurry f)) (C : ℝ),
      (∀ u ∈ D, ∀ᵐ ω ∂μ, |f u ω| ≤ C) → Integrable (Function.uncurry f) (σ.prod μ) := by
    intro f hf C hC
    refine Integrable.of_bound hf.aestronglyMeasurable C ?_
    have hs : MeasurableSet {p : E × Ω | ‖Function.uncurry f p‖ ≤ C} :=
      measurableSet_le hf.norm measurable_const
    rw [Measure.ae_prod_iff_ae_ae hs]
    filter_upwards [hDae] with u hu
    filter_upwards [hC u hu] with ω hω
    simpa [Real.norm_eq_abs] using hω
  have hiH : Integrable (Function.uncurry fH) (σ.prod μ) := by
    refine hprodbd hfHm c fun u hu => ?_
    filter_upwards [hbdR u hu] with ω h
    simp only [fH, Set.indicator]; split_ifs
    · exact h.1
    · rw [abs_zero]; exact le_trans (abs_nonneg _) h.1
  have hiR : Integrable (Function.uncurry fR) (σ.prod μ) := by
    refine hprodbd hfRm (c + c + c * c) fun u hu => ?_
    filter_upwards [hbdR u hu] with ω h
    simp only [fR, Set.indicator]; split_ifs
    · exact h.2
    · rw [abs_zero]; exact le_trans (abs_nonneg _) h.2
  have eL : ∫ ω, J.indicator (fun ω => ∫ u, H u ω ∂σ) ω ∂μ = ∫ u, ∫ ω, fH u ω ∂μ ∂σ := by
    rw [integral_integral_swap hiH]
    congr 1; funext ω
    simp only [fH, Set.indicator]; split_ifs <;> simp
  have eR : ∫ ω, J.indicator (fun ω => ∫ u, R u ω ∂σ) ω ∂μ = ∫ u, ∫ ω, fR u ω ∂μ ∂σ := by
    rw [integral_integral_swap hiR]
    congr 1; funext ω
    simp only [fR, Set.indicator]; split_ifs <;> simp
  rw [eL, eR]
  refine integral_mono_ae hiH.integral_prod_left hiR.integral_prod_left ?_
  filter_upwards [hDae] with u hu
  have hHm : AEStronglyMeasurable (H u) μ :=
    (hHj.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact pstep hF hJ hHm (hg0m u hu) (hg1m u hu) (hg2m u hu) (hξm u hu) (hb1m u hu) (hVm u hu)
    (hbd u hu) (hpt u hu) (hdr u hu) (hse u hu) (hg2n u hu)

end G26


-- ===== Solutions.G26.Iface =====

/-! ### The abstract affine-field interface of Lemma G.25 -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {d : ℕ} {Ω : Type*}

lemma fz_succ (V : ℕ → Ω → (Fin d → ℝ)) (c : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (u : Fin d → ℝ) :
    fz V c (n + 1) ω u = fz V c n ω u + fxi V c n ω u := by unfold fxi; ring

section

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma FI.Vm' (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) : Measurable (V n) :=
  (I.Vm n hn).mono (I.Fle n hn) le_rfl

lemma FI.cm' (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) : Measurable (c n) :=
  (I.cm n hn).mono (I.Fle n hn) le_rfl

lemma FI.Jm' (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) : MeasurableSet (J n) :=
  I.Fle n hn _ (I.Jm n hn)

/-- the field at a fixed point is `F_n`-measurable -/
lemma FI.fz_meas (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) (u : Fin d → ℝ) :
    Measurable[F n] (fun ω => fz V c n ω u) := by
  unfold fz
  have h : Continuous fun p : (Fin d → ℝ) × ℝ => u ⬝ᵥ p.1 + p.2 := by
    simp only [dotProduct]; fun_prop
  exact h.measurable.comp ((I.Vm n hn).prodMk (I.cm n hn))

/-- joint measurability of the field -/
lemma FI.fz_jmeas (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) :
    Measurable (Function.uncurry fun (u : Fin d → ℝ) (ω : Ω) => fz V c n ω u) := by
  unfold fz Function.uncurry
  have h : Continuous fun p : (Fin d → ℝ) × (Fin d → ℝ) × ℝ => p.1 ⬝ᵥ p.2.1 + p.2.2 := by
    simp only [dotProduct]; fun_prop
  exact h.measurable.comp (measurable_fst.prodMk (((I.Vm' hn).comp measurable_snd).prodMk
    ((I.cm' hn).comp measurable_snd)))

lemma FI.absMax_meas (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) :
    Measurable[F n] (fun ω => absMax D (V n ω) (c n ω)) :=
  G26.absMax_meas I.hD I.hne (I.Vm n hn) (I.cm n hn)

/-- deterministic envelope of the field and its extrema -/
lemma FI.env' (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) :
    ∃ r : ℝ, 0 ≤ r ∧ ∀ᵐ ω ∂μ, absMax D (V n ω) (c n ω) ≤ r ∧
      ∀ u ∈ D, |fz V c n ω u| ≤ r := by
  obtain ⟨r, hr⟩ := I.env n hn
  refine ⟨max r 0, le_max_right _ _, ?_⟩
  filter_upwards [hr] with ω h
  obtain ⟨x0, hx0, hval, -⟩ := absMax_mem I.hD I.hne (V n ω) (c n ω)
  have hA : absMax D (V n ω) (c n ω) ≤ max r 0 := by
    rw [← hval]; exact (h x0 hx0).trans (le_max_left _ _)
  exact ⟨hA, fun u hu => (abs_le_absMax I.hD hu _ _).trans hA⟩

end

end G26


-- ===== Solutions.G26.AbsRec =====

/-! ### The absolute integral moment recurrence (Lemmas G.23, G.25) -/

open MeasureTheory ProbabilityTheory Set J11

namespace G26

variable {d : ℕ} {Ω : Type*}

section

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma cont_bdd_int (hD : IsCompact D) {φ : (Fin d → ℝ) → ℝ} (hφ : Continuous φ) :
    Integrable φ (nvol D) := by
  have : IsFiniteMeasure (nvol D) := by
    unfold nvol; infer_instance
  obtain ⟨Cb, hCb⟩ := hD.exists_bound_of_continuousOn hφ.continuousOn
  refine Integrable.of_bound hφ.aestronglyMeasurable Cb ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (nvol_supp hD)] with x hx
  simp only [Set.mem_compl_iff, not_not] at hx
  exact hCb x hx

omit mΩ in
lemma fz_cont (V : ℕ → Ω → (Fin d → ℝ)) (c : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Continuous fun u => fz V c n ω u := by
  unfold fz; simp only [dotProduct]; fun_prop

lemma FI.Gf_meas (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) (P : ℕ) :
    StronglyMeasurable (Gf D V c P n) := by
  have := nvol_prob I.hD I.hconv I.hne
  have h : StronglyMeasurable (fun p : Ω × (Fin d → ℝ) => fz V c n p.1 p.2 ^ P) := by
    have := (I.fz_jmeas hn).pow_const P
    exact (this.comp measurable_swap).stronglyMeasurable
  exact h.integral_prod_right'

omit mΩ in
lemma FI.Gf_nonneg {P : ℕ} (hev : Even P) (n : ℕ) (ω : Ω) : 0 ≤ Gf D V c P n ω :=
  integral_nonneg fun _ => hev.pow_nonneg _

lemma FI.Gf_bdd [IsProbabilityMeasure μ] (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T)
    {P : ℕ} (hev : Even P) : ∃ r : ℝ, ∀ᵐ ω ∂μ, |Gf D V c P n ω| ≤ r := by
  haveI := nvol_prob I.hD I.hconv I.hne
  obtain ⟨r, hr0, hr⟩ := I.env' hn
  refine ⟨r ^ P, ?_⟩
  filter_upwards [hr] with ω hω
  have h := hω.2
  rw [abs_of_nonneg (FI.Gf_nonneg hev n ω)]
  have hint := cont_bdd_int I.hD ((fz_cont V c n ω).pow P)
  calc Gf D V c P n ω ≤ ∫ _u, r ^ P ∂(nvol D) := by
        refine integral_mono_ae hint (integrable_const _) ?_
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 (nvol_supp I.hD)] with u hu
        simp only [Set.mem_compl_iff, not_not] at hu
        rw [← hev.pow_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (h u hu) _
    _ = r ^ P := by simp

lemma FI.Gf_int [IsProbabilityMeasure μ] (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T)
    {P : ℕ} (hev : Even P) (S : Set Ω) (hS : MeasurableSet S) :
    Integrable (S.indicator (Gf D V c P n)) μ := by
  obtain ⟨r, hr⟩ := I.Gf_bdd hn hev
  exact (int_of_ae_bdd (I.Gf_meas hn P).aestronglyMeasurable hr).indicator hS

/-- the pathwise bound of the absolute recurrence at a fixed history -/
lemma FI.abs_path (I : FI D μ F T V c J β B lo hi m0) {P : ℕ} (hP : 4 ≤ P) (hev : Even P)
    (hjP : rdim D ≤ P) (hB : 2 ^ 20 * (P : ℝ) ≤ B) {b βn x : ℝ} (hβ : 0 < βn)
    (hβb : βn ≤ b * x) (hx : 1 ≤ x) {n : ℕ} (ω : Ω) :
    ∫ u, (fz V c n ω u ^ P + 2 * P * |fz V c n ω u| ^ (P - 1) +
        (P * (P - 1 : ℝ) / 2) * (|fz V c n ω u| + (3 * βn + 3 * absMax D (V n ω) (c n ω) / B)) ^ (P - 2) *
          (10 * βn + 18 * absMax D (V n ω) (c n ω) ^ 2 / (B * x))) ∂(nvol D) ≤
      (1 + (3 + 1152 * P ^ 2 / B) / x) * Gf D V c P n ω + Kabs P b B * x ^ (P - 1) := by
  have := nvol_prob I.hD I.hconv I.hne
  have hPr : (4 : ℝ) ≤ P := by exact_mod_cast hP
  have hB0 : 0 < B := by linarith
  obtain ⟨x0, hx0, hRx, hmax⟩ := absMax_mem I.hD I.hne (V n ω) (c n ω)
  set G := Gf D V c P n ω with hGdef
  set R := absMax D (V n ω) (c n ω) with hRdef
  set M := 3 * βn + 3 * R / B with hMdef
  set f : (Fin d → ℝ) → ℝ := fun u => |fz V c n ω u| with hf
  have hfc : Continuous f := (fz_cont V c n ω).abs
  have hf0 : ∀ u, 0 ≤ f u := fun u => abs_nonneg _
  have hR0 : 0 ≤ R := by rw [← hRx]; exact abs_nonneg _
  have hM0 : 0 < M := by positivity
  have hfP : ∀ u, f u ^ P = fz V c n ω u ^ P := fun u => hev.pow_abs _
  have hGf : ∫ u, f u ^ P ∂(nvol D) = G := by simp_rw [hfP]; rfl
  have hG0 : 0 ≤ G := FI.Gf_nonneg hev n ω
  -- the effective root
  set A0 := G ^ ((1 : ℝ) / P) with hA0
  have hA00 : 0 ≤ A0 := Real.rpow_nonneg hG0 _
  have hA0P : A0 ^ P = G := by
    rw [hA0, ← Real.rpow_natCast, ← Real.rpow_mul hG0, one_div_mul_cancel (by positivity),
      Real.rpow_one]
  set At := max A0 βn with hAt
  have hAtβ : βn ≤ At := le_max_right _ _
  have hAt0 : 0 < At := lt_of_lt_of_le hβ hAtβ
  have hGAt : G ≤ At ^ P := by
    rw [← hA0P]; exact pow_le_pow_left₀ hA00 (le_max_left _ _) _
  have hcase : 8 * P * βn ≤ At → At ^ P = G := by
    intro h
    have : At = A0 := by
      rcases max_cases A0 βn with ⟨h1, -⟩ | ⟨h1, h2⟩
      · exact h1
      · exfalso; rw [hAt, h1] at h; nlinarith
    rw [this, hA0P]
  have hAtG : At ^ P ≤ G + βn ^ P := by
    rcases max_cases A0 βn with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [hAt, h1, hA0P]; have := pow_nonneg hβ.le P; linarith
    · rw [hAt, h1]; linarith
  -- `R ≤ 8 At` by (J.17)
  have hR8 : R ≤ 8 * At := by
    have hJ := J17 I.hD I.hconv I.hne (V n ω) (c n ω) hx0 hmax P
    have e1 : ∫ x, |x ⬝ᵥ V n ω + c n ω| ^ P ∂(nvol D) = G := by
      rw [← hGf]; rfl
    rw [e1, hRx] at hJ
    have h4 : (4 : ℝ) ^ rdim D ≤ 4 ^ P := pow_le_pow_right₀ (by norm_num) hjP
    have h5 : R ^ P ≤ (8 * At) ^ P := by
      calc R ^ P ≤ 2 ^ P * 4 ^ rdim D * G := hJ
        _ ≤ 2 ^ P * 4 ^ P * At ^ P := by gcongr
        _ = (8 * At) ^ P := by rw [mul_pow, show (8 : ℝ) = 2 * 4 by norm_num, mul_pow]
    exact le_of_pow_le_pow_left₀ (by omega) (by positivity) h5
  -- integrability
  have i0 : Integrable (fun u => fz V c n ω u ^ P) (nvol D) :=
    cont_bdd_int I.hD ((fz_cont V c n ω).pow P)
  have i1 : Integrable (fun u => f u ^ (P - 1)) (nvol D) := cont_bdd_int I.hD (hfc.pow _)
  have i1' : Integrable (fun u => f u ^ P) (nvol D) := cont_bdd_int I.hD (hfc.pow _)
  have i2 : Integrable (fun u => (f u + M) ^ (P - 2)) (nvol D) :=
    cont_bdd_int I.hD ((hfc.add continuous_const).pow _)
  have i2' : Integrable (fun u => f u ^ (P - 2)) (nvol D) := cont_bdd_int I.hD (hfc.pow _)
  have hI1 : ∫ u, f u ^ (P - 1) ∂(nvol D) ≤ At ^ (P - 1) :=
    int_pow_le hf0 i1 i1' hAt0 (by omega) (by omega) (by rw [hGf]; exact hGAt)
  have hI2 : ∫ u, (f u + M) ^ (P - 2) ∂(nvol D) ≤ (At + M) ^ (P - 2) :=
    int_shift_pow_le hf0 i2' i1' i2 hAt0 hM0 (by omega) (by omega) (by omega)
      (by rw [hGf]; exact hGAt)
  have hI20 : 0 ≤ ∫ u, (f u + M) ^ (P - 2) ∂(nvol D) :=
    integral_nonneg fun u => by have := hf0 u; positivity
  have halg := abs_alg P hP B b βn x G At R (∫ u, f u ^ (P - 1) ∂(nvol D))
    (∫ u, (f u + M) ^ (P - 2) ∂(nvol D)) hB hx hβ hβb hAtβ hcase hAtG hG0 hR0 hR8 hI1 hI2 hI20
  -- split the integral
  set Vb := 10 * βn + 18 * R ^ 2 / (B * x)
  have e : ∫ u, (fz V c n ω u ^ P + 2 * P * f u ^ (P - 1) +
      (P * (P - 1 : ℝ) / 2) * (f u + M) ^ (P - 2) * Vb) ∂(nvol D) =
      G + 2 * P * ∫ u, f u ^ (P - 1) ∂(nvol D) +
        Vb * ((P * (P - 1 : ℝ) / 2) * ∫ u, (f u + M) ^ (P - 2) ∂(nvol D)) := by
    have j1 : Integrable (fun u => 2 * (P : ℝ) * f u ^ (P - 1)) (nvol D) := i1.const_mul _
    have j2 : Integrable (fun u => (P * (P - 1 : ℝ) / 2) * (f u + M) ^ (P - 2) * Vb) (nvol D) :=
      (i2.const_mul _).mul_const _
    rw [integral_add (f := fun u => fz V c n ω u ^ P + 2 * P * f u ^ (P - 1))
      (g := fun u => (P * (P - 1 : ℝ) / 2) * (f u + M) ^ (P - 2) * Vb) (i0.add j1) j2,
      integral_add (f := fun u => fz V c n ω u ^ P) (g := fun u => 2 * (P : ℝ) * f u ^ (P - 1))
        i0 j1, integral_mul_const, integral_const_mul, integral_const_mul]
    have hG' : ∫ u, fz V c n ω u ^ P ∂(nvol D) = G := rfl
    rw [hG']
    ring
  calc _ = ∫ u, (fz V c n ω u ^ P + 2 * P * f u ^ (P - 1) +
        (P * (P - 1 : ℝ) / 2) * (f u + M) ^ (P - 2) * Vb) ∂(nvol D) := rfl
    _ = _ := e
    _ ≤ _ := halg

end

end G26

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma fz_add_negMax_abs (hD : IsCompact D) {u : Fin d → ℝ} (hu : u ∈ D) (W : Fin d → ℝ) (c0 : ℝ) :
    |u ⬝ᵥ W + c0 + 2 * negMax D W c0| ≤ 3 * absMax D W c0 := by
  have h1 := abs_le_absMax hD hu W c0
  have h2 := negMax_ge hD hu W c0
  have h3 := negMax_le_absMax (D := D) W c0
  rw [abs_le] at h1 ⊢
  constructor <;> linarith

/-- **one step of the absolute integral moment recurrence (G.443)** -/
theorem FI.abs_step [IsProbabilityMeasure μ] (I : FI D μ F T V c J β B lo hi m0)
    (hlo : -2 ≤ lo) (hhi : hi ≤ 2) {P : ℕ} (hP : 4 ≤ P) (hev : Even P) (hjP : rdim D ≤ P)
    (hB : 2 ^ 20 * (P : ℝ) ≤ B) {b : ℝ} (hβ : ∀ n, 0 < β n)
    (hβb : ∀ n, β n ≤ b * ((n : ℝ) + 1)) {n : ℕ} (hm0 : m0 ≤ n) (hn : n < T) :
    ∫ ω, (J (n + 1)).indicator (Gf D V c P (n + 1)) ω ∂μ ≤
      (1 + (3 + 1152 * P ^ 2 / B) / ((n : ℝ) + 1)) * ∫ ω, (J n).indicator (Gf D V c P n) ω ∂μ +
        Kabs P b B * ((n : ℝ) + 1) ^ (P - 1) := by
  have := nvol_prob I.hD I.hconv I.hne
  have hPr : (4 : ℝ) ≤ P := by exact_mod_cast hP
  have hB0 : 0 < B := by linarith
  set x : ℝ := (n : ℝ) + 1 with hx
  have hx1 : 1 ≤ x := by simp only [x]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hFn := I.Fle n hn.le
  have hJn : MeasurableSet[F n] (J n) := I.Jm n hn.le
  -- the ingredients
  set A : Ω → ℝ := fun ω => absMax D (V n ω) (c n ω) with hA
  set M : Ω → ℝ := fun ω => 3 * β n + 3 * A ω / B with hM
  let H : (Fin d → ℝ) → Ω → ℝ := fun u ω => fz V c (n + 1) ω u ^ P
  let g0 : (Fin d → ℝ) → Ω → ℝ := fun u ω => fz V c n ω u ^ P
  let g1 : (Fin d → ℝ) → Ω → ℝ := fun u ω => P * fz V c n ω u ^ (P - 1)
  let g2 : (Fin d → ℝ) → Ω → ℝ := fun u ω =>
    (P * (P - 1 : ℝ) / 2) * (|fz V c n ω u| + M ω) ^ (P - 2)
  let ξ : (Fin d → ℝ) → Ω → ℝ := fun u ω => fxi V c n ω u
  let b1 : (Fin d → ℝ) → Ω → ℝ := fun u ω => 2 * P * |fz V c n ω u| ^ (P - 1)
  let Vb : (Fin d → ℝ) → Ω → ℝ := fun _ ω => 10 * β n + 18 * A ω ^ 2 / (B * x)
  -- measurability
  have hAm : Measurable[F n] A := I.absMax_meas hn.le
  have hAm' : Measurable A := hAm.mono hFn le_rfl
  have hzm : ∀ u, Measurable[F n] (fun ω => fz V c n ω u) := fun u => I.fz_meas hn.le u
  have hzj := I.fz_jmeas hn.le
  have hzj1 := I.fz_jmeas (n := n + 1) hn
  have hAj : Measurable (fun p : (Fin d → ℝ) × Ω => A p.2) := hAm'.comp measurable_snd
  have hHj : Measurable (Function.uncurry H) := hzj1.pow_const P
  have hRj : Measurable (Function.uncurry fun u ω => g0 u ω + b1 u ω + g2 u ω * Vb u ω) := by
    have h1 : Measurable (fun p : (Fin d → ℝ) × Ω => fz V c n p.2 p.1) := hzj
    have hM' : Measurable (fun p : (Fin d → ℝ) × Ω => M p.2) :=
      (measurable_const.add ((measurable_const.mul hAj).div_const _))
    exact ((h1.pow_const P).add (measurable_const.mul (h1.abs.pow_const _))).add
      ((measurable_const.mul ((h1.abs.add hM').pow_const _)).mul
        (measurable_const.add ((measurable_const.mul (hAj.pow_const 2)).div_const _)))
  -- envelopes
  obtain ⟨r0, hr00, hr0⟩ := I.env' hn.le
  obtain ⟨r1, hr10, hr1⟩ := I.env' (n := n + 1) hn
  have hβn := hβ n
  set cb : ℝ := r1 ^ P + r0 ^ P + P * r0 ^ (P - 1) +
    (P * (P - 1 : ℝ) / 2) * (r0 + (3 * β n + 3 * r0 / B)) ^ (P - 2) + (r1 + r0) +
    2 * P * r0 ^ (P - 1) + (10 * β n + 18 * r0 ^ 2 / (B * x)) with hcb
  have hc0 : 0 ≤ (P * (P - 1 : ℝ) / 2) := by nlinarith
  have hbd : ∀ u ∈ D, ∀ᵐ ω ∂μ, |H u ω| ≤ cb ∧ |g0 u ω| ≤ cb ∧ |g1 u ω| ≤ cb ∧ |g2 u ω| ≤ cb ∧
      |ξ u ω| ≤ cb ∧ |b1 u ω| ≤ cb ∧ |Vb u ω| ≤ cb := by
    intro u hu
    filter_upwards [hr0, hr1] with ω hω0 hω1
    obtain ⟨hA0, hz0⟩ := hω0
    have hz1 := hω1.2
    have hz0u := hz0 u hu
    have hz1u := hz1 u hu
    have hA0' : 0 ≤ A ω := le_trans (abs_nonneg _) ((abs_le_absMax I.hD hu _ _))
    have t1 : |H u ω| ≤ r1 ^ P := by
      simp only [H]; rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hz1u _
    have t2 : |g0 u ω| ≤ r0 ^ P := by
      simp only [g0]; rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hz0u _
    have t3 : |g1 u ω| ≤ P * r0 ^ (P - 1) := by
      simp only [g1]; rw [abs_mul, abs_pow, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hz0u _) (by positivity)
    have t4 : |g2 u ω| ≤ (P * (P - 1 : ℝ) / 2) * (r0 + (3 * β n + 3 * r0 / B)) ^ (P - 2) := by
      simp only [g2, M]
      rw [abs_mul, abs_of_nonneg hc0, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) hc0
      have : 3 * A ω / B ≤ 3 * r0 / B := div_le_div_of_nonneg_right (by linarith) hB0.le
      linarith
    have t5 : |ξ u ω| ≤ r1 + r0 := by
      simp only [ξ, fxi]
      exact le_trans (abs_sub _ _) (add_le_add hz1u hz0u)
    have t6 : |b1 u ω| ≤ 2 * P * r0 ^ (P - 1) := by
      simp only [b1]
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * P), abs_pow, abs_abs]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) hz0u _) (by positivity)
    have t7 : |Vb u ω| ≤ 10 * β n + 18 * r0 ^ 2 / (B * x) := by
      simp only [Vb]
      rw [abs_of_nonneg (by positivity)]
      have : A ω ^ 2 ≤ r0 ^ 2 := pow_le_pow_left₀ hA0' hA0 2
      gcongr
    have p1 : 0 ≤ r1 ^ P := by positivity
    have p2 : 0 ≤ r0 ^ P := by positivity
    have p3 : 0 ≤ (P : ℝ) * r0 ^ (P - 1) := by positivity
    have p4 : 0 ≤ (P * (P - 1 : ℝ) / 2) * (r0 + (3 * β n + 3 * r0 / B)) ^ (P - 2) := by positivity
    have p5 : 0 ≤ r1 + r0 := by positivity
    have p6 : 0 ≤ 2 * (P : ℝ) * r0 ^ (P - 1) := by positivity
    have p7 : 0 ≤ 10 * β n + 18 * r0 ^ 2 / (B * x) := by positivity
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [cb] <;> linarith
  -- the pointwise expansion
  have hpt : ∀ u ∈ D, ∀ᵐ ω ∂μ, ω ∈ J n →
      H u ω ≤ g0 u ω + g1 u ω * ξ u ω + g2 u ω * ξ u ω ^ 2 := by
    intro u hu
    filter_upwards [I.mag n hm0 hn] with ω hω hJ
    have hm := hω hJ u hu
    have h3 := fz_add_negMax_abs I.hD hu (V n ω) (c n ω)
    have hξM : |ξ u ω| ≤ M ω := by
      simp only [ξ, M, A]
      have : (fz V c n ω u + 2 * negMax D (V n ω) (c n ω)) / B ≤
          3 * absMax D (V n ω) (c n ω) / B :=
        div_le_div_of_nonneg_right (le_trans (le_abs_self _) h3) hB0.le
      linarith
    have hT := C37.pow_taylor (fz V c n ω u) (ξ u ω) P (by omega)
    have hpow : (|fz V c n ω u| + |ξ u ω|) ^ (P - 2) ≤ (|fz V c n ω u| + M ω) ^ (P - 2) :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    have h4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hc0)
      (sq_nonneg (ξ u ω))
    simp only [H, g0, g1, g2, ξ] at hT h4 ⊢
    rw [fz_succ]
    linarith
  -- drift
  have hdr : ∀ u ∈ D, ∀ᵐ ω ∂μ, ω ∈ J n → g1 u ω * μ[ξ u | F n] ω ≤ b1 u ω := by
    intro u hu
    filter_upwards [I.drift n hm0 hn u hu] with ω hω hJ
    obtain ⟨h1, h2⟩ := hω hJ
    have hE : |μ[ξ u | F n] ω| ≤ 2 := abs_le.2 ⟨by simp only [ξ]; linarith, by simp only [ξ]; linarith⟩
    simp only [g1, b1]
    calc (P : ℝ) * fz V c n ω u ^ (P - 1) * μ[ξ u | F n] ω
        ≤ |(P : ℝ) * fz V c n ω u ^ (P - 1) * μ[ξ u | F n] ω| := le_abs_self _
      _ = P * |fz V c n ω u| ^ (P - 1) * |μ[ξ u | F n] ω| := by
          rw [abs_mul, abs_mul, abs_pow, Nat.abs_cast]
      _ ≤ P * |fz V c n ω u| ^ (P - 1) * 2 := mul_le_mul_of_nonneg_left hE (by positivity)
      _ = 2 * P * |fz V c n ω u| ^ (P - 1) := by ring
  -- second moment
  have hse : ∀ u ∈ D, ∀ᵐ ω ∂μ, ω ∈ J n → μ[fun ω => ξ u ω ^ 2 | F n] ω ≤ Vb u ω := by
    intro u hu
    filter_upwards [I.sec n hm0 hn u hu] with ω hω hJ
    have h1 := hω hJ
    have h3 := fz_add_negMax_abs I.hD hu (V n ω) (c n ω)
    have h4 : (fz V c n ω u + 2 * negMax D (V n ω) (c n ω)) ^ 2 ≤ 9 * A ω ^ 2 := by
      have := sq_le_sq' (abs_le.1 h3).1 (abs_le.1 h3).2
      simp only [A]; unfold fz at this ⊢; nlinarith
    have h5 : 2 * (fz V c n ω u + 2 * negMax D (V n ω) (c n ω)) ^ 2 / (B * ((n : ℝ) + 1)) ≤
        18 * A ω ^ 2 / (B * x) := by
      rw [show ((n : ℝ) + 1) = x from rfl]
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    simp only [Vb, ξ]
    linarith
  have hAnn : ∀ ω, 0 ≤ A ω := fun ω => by
    obtain ⟨x0, hx0⟩ := I.hne
    exact le_trans (abs_nonneg _) (abs_le_absMax I.hD hx0 _ _)
  have hg2n : ∀ u ∈ D, ∀ᵐ ω ∂μ, ω ∈ J n → 0 ≤ g2 u ω := fun u _ =>
    ae_of_all _ fun ω _ => by
      simp only [g2, M]
      have := hβ n
      have := hAnn ω
      exact mul_nonneg hc0 (pow_nonneg (by positivity) _)
  -- measurability of the coefficients
  have hg1m : ∀ u ∈ D, StronglyMeasurable[F n] (g1 u) := fun u _ =>
    (((hzm u).pow_const _).const_mul _).stronglyMeasurable
  have hg2m : ∀ u ∈ D, StronglyMeasurable[F n] (g2 u) := by
    intro u _
    have hφ : Continuous (fun p : ℝ × ℝ => (P * (P - 1 : ℝ) / 2) *
        (|p.1| + (3 * β n + 3 * p.2 / B)) ^ (P - 2)) := by fun_prop
    exact (hφ.measurable.comp ((hzm u).prodMk hAm)).stronglyMeasurable
  have hg0m : ∀ u ∈ D, AEStronglyMeasurable (g0 u) μ := fun u _ =>
    (((hzm u).mono hFn le_rfl).pow_const _).aestronglyMeasurable
  have hξm : ∀ u ∈ D, AEStronglyMeasurable (ξ u) μ := fun u _ =>
    (((I.fz_meas hn u).mono (I.Fle (n + 1) hn) le_rfl).sub
      ((hzm u).mono hFn le_rfl)).aestronglyMeasurable
  have hb1m : ∀ u ∈ D, AEStronglyMeasurable (b1 u) μ := fun u _ =>
    (measurable_const.mul (((hzm u).mono hFn le_rfl).abs.pow_const _)).aestronglyMeasurable
  have hVm : ∀ u ∈ D, AEStronglyMeasurable (Vb u) μ := fun u _ =>
    (measurable_const.add ((measurable_const.mul (hAm'.pow_const 2)).div_const _)).aestronglyMeasurable
  have hstep := istep (nvol_supp I.hD) hFn hJn hHj hRj hg0m hg1m hg2m hξm hb1m hVm hbd hpt
    hdr hse hg2n
  -- pathwise bound
  have hpath : ∀ ω, (J n).indicator (fun ω => ∫ u, (g0 u ω + b1 u ω + g2 u ω * Vb u ω) ∂(nvol D)) ω ≤
      (J n).indicator (fun ω => (1 + (3 + 1152 * P ^ 2 / B) / x) * Gf D V c P n ω +
        Kabs P b B * x ^ (P - 1)) ω := by
    intro ω
    by_cases hJ : ω ∈ J n
    · rw [Set.indicator_of_mem hJ, Set.indicator_of_mem hJ]
      have h := I.abs_path hP hev hjP hB (b := b) (hβ n) (hβb n) hx1 (n := n) ω
      simp only [g0, b1, g2, Vb, M, A]
      convert h using 3
    · rw [Set.indicator_of_notMem hJ, Set.indicator_of_notMem hJ]
  -- assemble
  have hGi := I.Gf_int hn.le hev (J n) (I.Jm' hn.le)
  have hGi1 := I.Gf_int (n := n + 1) hn hev (J n) (I.Jm' hn.le)
  have hGi1' := I.Gf_int (n := n + 1) hn hev (J (n + 1)) (I.Jm' hn)
  have hRi : Integrable ((J n).indicator (fun ω => (1 + (3 + 1152 * P ^ 2 / B) / x) *
      Gf D V c P n ω + Kabs P b B * x ^ (P - 1))) μ := by
    have h1 : Integrable (fun ω => (1 + (3 + 1152 * P ^ 2 / B) / x) * Gf D V c P n ω +
        Kabs P b B * x ^ (P - 1)) μ := by
      obtain ⟨r, hr⟩ := I.Gf_bdd hn.le hev
      exact ((int_of_ae_bdd (I.Gf_meas hn.le P).aestronglyMeasurable hr).const_mul _).add
        (integrable_const _)
    exact h1.indicator (I.Jm' hn.le)
  have hK0 : 0 ≤ Kabs P b B := by
    have hb0 : 0 ≤ b := by
      have := hβb 0; have := hβ 0; simp at *; nlinarith
    unfold Kabs; positivity
  calc ∫ ω, (J (n + 1)).indicator (Gf D V c P (n + 1)) ω ∂μ
      ≤ ∫ ω, (J n).indicator (Gf D V c P (n + 1)) ω ∂μ := by
        refine integral_mono hGi1' hGi1 fun ω => ?_
        exact Set.indicator_le_indicator_of_subset (I.Jmono n) (fun ω => FI.Gf_nonneg hev _ ω) ω
    _ = ∫ ω, (J n).indicator (fun ω => ∫ u, H u ω ∂(nvol D)) ω ∂μ := rfl
    _ ≤ ∫ ω, (J n).indicator (fun ω => ∫ u, (g0 u ω + b1 u ω + g2 u ω * Vb u ω) ∂(nvol D)) ω ∂μ :=
        hstep
    _ ≤ ∫ ω, (J n).indicator (fun ω => (1 + (3 + 1152 * P ^ 2 / B) / x) * Gf D V c P n ω +
          Kabs P b B * x ^ (P - 1)) ω ∂μ := by
        refine integral_mono_of_nonneg ?_ hRi (ae_of_all _ hpath)
        refine ae_of_all _ fun ω => ?_
        by_cases hJ : ω ∈ J n
        · rw [Set.indicator_of_mem hJ]
          refine integral_nonneg fun u => ?_
          simp only [g0, b1, g2, Vb, M, A]
          have := hev.pow_nonneg (fz V c n ω u)
          have := hβ n
          have : 0 ≤ absMax D (V n ω) (c n ω) := by
            obtain ⟨x0, hx0⟩ := I.hne
            exact le_trans (abs_nonneg _) (abs_le_absMax I.hD hx0 _ _)
          positivity
        · simp [Set.indicator_of_notMem hJ]
    _ = (1 + (3 + 1152 * P ^ 2 / B) / x) * ∫ ω, (J n).indicator (Gf D V c P n) ω ∂μ +
          Kabs P b B * x ^ (P - 1) * (μ (J n)).toReal := by
        rw [show (J n).indicator (fun ω => (1 + (3 + 1152 * P ^ 2 / B) / x) * Gf D V c P n ω +
            Kabs P b B * x ^ (P - 1)) = fun ω => (1 + (3 + 1152 * P ^ 2 / B) / x) *
              (J n).indicator (Gf D V c P n) ω + (J n).indicator (fun _ => Kabs P b B * x ^ (P - 1)) ω from by
          funext ω; by_cases hJ : ω ∈ J n <;> simp [hJ]]
        rw [integral_add (hGi.const_mul _) ((integrable_const _).indicator (I.Jm' hn.le)),
          integral_const_mul, integral_indicator_const _ (I.Jm' hn.le), smul_eq_mul,
          measureReal_def]
        ring
    _ ≤ _ := by
        have h1 : (μ (J n)).toReal ≤ 1 := by
          rw [← measureReal_def]; exact measureReal_le_one
        have h2 : 0 ≤ Kabs P b B * x ^ (P - 1) := by positivity
        nlinarith

end G26

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma vabs_lt (P : ℕ) (hP : 4 ≤ P) (B : ℝ) (hB : 2 ^ 20 * (P : ℝ) ≤ B) :
    3 + 1152 * (P : ℝ) ^ 2 / B < P := by
  have hPr : (4 : ℝ) ≤ P := by exact_mod_cast hP
  have hB0 : 0 < B := by linarith
  have : 1152 * (P : ℝ) ^ 2 / B ≤ P / 900 := by
    rw [div_le_div_iff₀ hB0 (by norm_num)]; nlinarith
  linarith

/-- **the absolute integral envelope (Lemma G.25)**: `E[1_{J_n} ∫ Z_n^P dσ] ≤ C (n+1)^P` -/
theorem FI.abs_env [IsProbabilityMeasure μ] (I : FI D μ F T V c J β B lo hi m0) (hm00 : m0 = 0)
    (hlo : -2 ≤ lo) (hhi : hi ≤ 2) {P : ℕ} (hP : 4 ≤ P) (hev : Even P) (hjP : rdim D ≤ P)
    (hB : 2 ^ 20 * (P : ℝ) ≤ B) {b : ℝ} (hβ : ∀ n, 0 < β n)
    (hβb : ∀ n, β n ≤ b * ((n : ℝ) + 1)) {C0 : ℝ}
    (h0 : ∫ ω, (J 0).indicator (Gf D V c P 0) ω ∂μ ≤ C0) :
    ∀ n ≤ T, ∫ ω, (J n).indicator (Gf D V c P n) ω ∂μ ≤ Cabs P b B C0 * ((n : ℝ) + 1) ^ P := by
  have hv := vabs_lt P hP B hB
  have hPr : (4 : ℝ) ≤ P := by exact_mod_cast hP
  have hB0 : 0 < B := by linarith
  have hb0 : 0 ≤ b := by have := hβb 0; have := hβ 0; simp at *; nlinarith
  have hK0 : 0 ≤ Kabs P b B := by unfold Kabs; positivity
  have hv0 : 0 ≤ 3 + 1152 * (P : ℝ) ^ 2 / B := by positivity
  have hC0' : 0 ≤ C0 := le_trans (integral_nonneg fun ω => Set.indicator_nonneg
    (fun ω _ => FI.Gf_nonneg hev 0 ω) ω) h0
  have hC : 0 ≤ Cabs P b B C0 := le_trans hC0' (le_max_left _ _)
  refine supersol (fun n => ∫ ω, (J n).indicator (Gf D V c P n) ω ∂μ) _ (Kabs P b B) _ P
    (by omega) hv0 hK0 hC ?_ (h0.trans (le_max_left _ _)) T fun n hn =>
      I.abs_step hlo hhi hP hev hjP hB hβ hβb (by omega) hn
  have h1 : Kabs P b B / (P - (3 + 1152 * P ^ 2 / B)) ≤ Cabs P b B C0 := le_max_right _ _
  rw [div_le_iff₀ (by linarith)] at h1
  calc (3 + 1152 * (P : ℝ) ^ 2 / B) * Cabs P b B C0 + Kabs P b B ≤
      (3 + 1152 * (P : ℝ) ^ 2 / B) * Cabs P b B C0 +
        Cabs P b B C0 * (P - (3 + 1152 * (P : ℝ) ^ 2 / B)) := by linarith
    _ = P * Cabs P b B C0 := by ring

/-- the absolute maximum is controlled by the integral moment, (J.17) -/
lemma FI.absMax_pow_le (I : FI D μ F T V c J β B lo hi m0) {P : ℕ} (hev : Even P) (n : ℕ) (ω : Ω) :
    absMax D (V n ω) (c n ω) ^ P ≤ 2 ^ P * 4 ^ rdim D * Gf D V c P n ω := by
  obtain ⟨x0, hx0, hRx, hmax⟩ := absMax_mem I.hD I.hne (V n ω) (c n ω)
  have hJ := J17 I.hD I.hconv I.hne (V n ω) (c n ω) hx0 hmax P
  rw [hRx] at hJ
  have e : ∫ x, |x ⬝ᵥ V n ω + c n ω| ^ P ∂(nvol D) = Gf D V c P n ω := by
    unfold Gf fz; simp_rw [hev.pow_abs]
  rwa [e] at hJ

end G26


-- ===== Solutions.G26.RunEnv =====

/-! ### Envelopes of the run fields: absolute maxima and block crossings (Lemmas G.15, G.30) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26

variable {d : ℕ} {Ω : Type*}

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma FI.absMax_int [IsProbabilityMeasure μ] (I : FI D μ F T V c J β B lo hi m0) {n : ℕ}
    (hn : n ≤ T) (P : ℕ) : Integrable (fun ω => absMax D (V n ω) (c n ω) ^ P) μ := by
  obtain ⟨r, hr0, hr⟩ := I.env' hn
  refine Integrable.of_bound
    (((I.absMax_meas hn).mono (I.Fle n hn) le_rfl).pow_const P).aestronglyMeasurable (r ^ P) ?_
  filter_upwards [hr, I.N0 n hn] with ω h h0
  have h1 : 0 ≤ absMax D (V n ω) (c n ω) := h0.trans (negMax_le_absMax _ _)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h1 _)]
  exact pow_le_pow_left₀ h1 h.1 P

/-- the absolute maximum envelope from time zero -/
theorem FI.absMax_env [IsProbabilityMeasure μ] (I : FI D μ F T V c J β B lo hi 0)
    (hlo : -2 ≤ lo) (hhi : hi ≤ 2) {P : ℕ} (hP : 4 ≤ P) (hev : Even P) (hjP : rdim D ≤ P)
    (hB : 2 ^ 20 * (P : ℝ) ≤ B) {b : ℝ} (hβ : ∀ n, 0 < β n)
    (hβb : ∀ n, β n ≤ b * ((n : ℝ) + 1)) (h0 : ∀ ω, Gf D V c P 0 ω = 0) {n : ℕ} (hn : n ≤ T) :
    ∫ ω, (J n).indicator (fun ω => absMax D (V n ω) (c n ω) ^ P) ω ∂μ ≤
      2 ^ P * 4 ^ rdim D * Cabs P b B 0 * ((n : ℝ) + 1) ^ P := by
  have henv := I.abs_env rfl hlo hhi hP hev hjP hB hβ hβb (C0 := 0)
    (by rw [show Gf D V c P 0 = 0 from funext h0]; simp) n hn
  have hJm := I.Jm' hn
  calc ∫ ω, (J n).indicator (fun ω => absMax D (V n ω) (c n ω) ^ P) ω ∂μ
      ≤ ∫ ω, (2 ^ P * 4 ^ rdim D : ℝ) * (J n).indicator (Gf D V c P n) ω ∂μ := by
        refine integral_mono ((I.absMax_int hn P).indicator hJm)
          ((I.Gf_int hn hev _ hJm).const_mul _) fun ω => ?_
        by_cases h : ω ∈ J n
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; exact I.absMax_pow_le hev n ω
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
    _ = (2 ^ P * 4 ^ rdim D : ℝ) * ∫ ω, (J n).indicator (Gf D V c P n) ω ∂μ := integral_const_mul _ _
    _ ≤ (2 ^ P * 4 ^ rdim D : ℝ) * (Cabs P b B 0 * ((n : ℝ) + 1) ^ P) :=
        mul_le_mul_of_nonneg_left henv (by positivity)
    _ = _ := by ring

end G26

namespace G26G

open G26 G26R

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ} {θ astar : Fin d → ℝ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

namespace Sharp

variable (H : Sharp 𝒜 ℬ θ astar)
include H

end Sharp

end G26G


theorem _root_.solution : type_of% @G26.FI.absMax_env := @G26.FI.absMax_env
