-- Prove2me | solution 1 for G26.FI.cross_env
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:31:26.050783+00:00
-- url     : https://prove2.me/submissions/a6d1cb8c-bfeb-4686-9e75-84213f9de3d7

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

/-- (I.7): the positive-part Taylor bound for an even power -/
lemma pos_taylor (y z : ℝ) (P : ℕ) (hP : 2 ≤ P) (hev : Even P) :
    (max (y + z) 0) ^ P ≤ (max y 0) ^ P + P * (max y 0) ^ (P - 1) * z +
      ((P : ℝ) * (P - 1) / 2) * (max (y + |z|) 0) ^ (P - 2) * z ^ 2 := by
  have hc : (1 : ℝ) ≤ (P : ℝ) * (P - 1) / 2 := by
    have : (2 : ℝ) ≤ P := by exact_mod_cast hP
    nlinarith
  have hc0 : (0 : ℝ) ≤ (P : ℝ) * (P - 1) / 2 := by linarith
  have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
  rcases le_or_gt y 0 with hy | hy
  · rw [max_eq_right hy]
    simp only [zero_pow (by omega : P ≠ 0), zero_pow (by omega : P - 1 ≠ 0), mul_zero, zero_mul,
      add_zero, zero_add]
    rcases le_or_gt (y + z) 0 with hyz | hyz
    · rw [max_eq_right hyz, zero_pow (by omega)]
      positivity
    · rw [max_eq_left hyz.le]
      have hz : 0 < z := by linarith
      have h1 : y + z ≤ y + |z| := by rw [abs_of_pos hz]
      rw [max_eq_left (by linarith : (0:ℝ) ≤ y + |z|)]
      obtain ⟨m, rfl⟩ : ∃ m, P = m + 2 := ⟨P - 2, by omega⟩
      have e : m + 2 - 2 = m := by omega
      rw [e, pow_add]
      have h2 : (y + z) ^ m ≤ (y + |z|) ^ m := pow_le_pow_left₀ hyz.le h1 m
      have h3 : (y + z) ^ 2 ≤ z ^ 2 := by nlinarith
      have h4 : 0 ≤ (y + z) ^ m := pow_nonneg hyz.le m
      calc (y + z) ^ m * (y + z) ^ 2 ≤ (y + |z|) ^ m * z ^ 2 :=
            mul_le_mul h2 h3 (sq_nonneg _) (pow_nonneg (by linarith) m)
        _ = 1 * (y + |z|) ^ m * z ^ 2 := by ring
        _ ≤ ((↑(m + 2) : ℝ) * (↑(m + 2) - 1) / 2) * (y + |z|) ^ m * z ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hc (pow_nonneg (by linarith) m)) hz2
  · rw [max_eq_left hy.le]
    have hT := pow_taylor y z P hP
    rw [abs_of_pos hy] at hT
    rw [max_eq_left (by positivity : (0:ℝ) ≤ y + |z|)]
    rcases le_or_gt (y + z) 0 with hyz | hyz
    · rw [max_eq_right hyz, zero_pow (by omega)]
      have hpow : 0 ≤ (y + z) ^ P := hev.pow_nonneg _
      -- the remainder identity gives `RHS ≥ (y+z)^P ≥ 0`
      obtain ⟨m, rfl⟩ : ∃ m, P = m + 2 := ⟨P - 2, by omega⟩
      have hb := binom_rem y z m
      rw [abs_of_pos hy] at hb
      have hl := le_abs_self ((y + z) ^ (m + 2) - y ^ (m + 2) - (m + 2) * y ^ (m + 1) * z)
      have e1 : m + 2 - 1 = m + 1 := by omega
      have e2 : m + 2 - 2 = m := by omega
      rw [e1, e2]
      push_cast
      have e3 : ((m : ℝ) + 2) * ((m : ℝ) + 2 - 1) / 2 = ((m + 2) * (m + 1) / 2 : ℝ) := by ring
      rw [e3]
      linarith
    · rw [max_eq_left hyz.le]
      exact hT

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

end G26

namespace G26

/-- Bernoulli: `1 + v/x ≤ (1 + 1/x)^V` for `v ≤ V` -/
lemma bern_V (v x : ℝ) (V : ℕ) (hx : 0 < x) (hv : v ≤ V) : 1 + v / x ≤ (1 + 1 / x) ^ V := by
  have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / x by
    have : 0 < 1 / x := by positivity
    linarith) V
  have : v / x ≤ V * (1 / x) := by rw [mul_one_div]; exact div_le_div_of_nonneg_right hv hx.le
  linarith

/-- supersolution from a starting time `m` with arbitrary initial value:
`g_n ≤ H (n+1)^q + ((n+1)/(m+1))^V g_m` -/
lemma supersol_from (g : ℕ → ℝ) (v K H : ℝ) (q V : ℕ) (hq : 1 ≤ q) (hv0 : 0 ≤ v) (hvV : v ≤ V)
    (hH : 0 ≤ H) (hvq : v * H + K ≤ q * H) (m N : ℕ) (hg : 0 ≤ g m)
    (hrec : ∀ n, m ≤ n → n < N →
      g (n + 1) ≤ (1 + v / ((n : ℝ) + 1)) * g n + K * ((n : ℝ) + 1) ^ (q - 1)) :
    ∀ n, m ≤ n → n ≤ N →
      g n ≤ H * ((n : ℝ) + 1) ^ q + (((n : ℝ) + 1) / ((m : ℝ) + 1)) ^ V * g m := by
  intro n hmn hnN
  induction n, hmn using Nat.le_induction with
  | base =>
    have : 0 ≤ H * ((m : ℝ) + 1) ^ q := by positivity
    rw [div_self (by positivity), one_pow, one_mul]; linarith
  | succ n hmn ih =>
    have ih' := ih (by omega)
    set x : ℝ := (n : ℝ) + 1 with hx
    have hx1 : 1 ≤ x := by simp only [x]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have hx0 : 0 < x := by linarith
    set y : ℝ := (m : ℝ) + 1 with hy
    have hy0 : 0 < y := by positivity
    have h1 := hrec n hmn (by omega)
    have hcoef : 0 ≤ 1 + v / x := by positivity
    have h2 : (1 + v / x) * g n ≤ (1 + v / x) * (H * x ^ q + (x / y) ^ V * g m) :=
      mul_le_mul_of_nonneg_left ih' hcoef
    have e : x ^ q = x * x ^ (q - 1) := by rw [← pow_succ']; congr 1; omega
    have h3 : (1 + v / x) * (H * x ^ q) = H * x ^ q + v * H * x ^ (q - 1) := by
      rw [e]; field_simp
    have h4 : (1 + v / x) * (x / y) ^ V ≤ ((x + 1) / y) ^ V := by
      have hb := bern_V v x V hx0 hvV
      calc (1 + v / x) * (x / y) ^ V ≤ (1 + 1 / x) ^ V * (x / y) ^ V :=
            mul_le_mul_of_nonneg_right hb (by positivity)
        _ = ((x + 1) / y) ^ V := by
            rw [← mul_pow]; congr 1; field_simp
    have h5 := pow_succ_lb x hx0.le q hq
    have h6 : (v * H + K) * x ^ (q - 1) ≤ q * H * x ^ (q - 1) :=
      mul_le_mul_of_nonneg_right hvq (by positivity)
    have h7 : H * (x ^ q + q * x ^ (q - 1)) ≤ H * (x + 1) ^ q := mul_le_mul_of_nonneg_left h5 hH
    have h8 : (1 + v / x) * ((x / y) ^ V * g m) ≤ ((x + 1) / y) ^ V * g m := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h4 hg
    push_cast
    rw [show (n : ℝ) + 1 + 1 = x + 1 by simp [x]]
    have e2 : (1 + v / x) * (H * x ^ q + (x / y) ^ V * g m) =
        (1 + v / x) * (H * x ^ q) + (1 + v / x) * ((x / y) ^ V * g m) := by ring
    nlinarith

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

/-- **(J.18)** `M^{p+r} ≤ 2^p 4^r R^r ∫ f₊^p dσ` at a maximizer of `f` with value `M > 0` -/
theorem J18 (v : Fin d → ℝ) (c : ℝ) {x0 : Fin d → ℝ} (hx0 : x0 ∈ D)
    (hmax : ∀ x ∈ D, x ⬝ᵥ v + c ≤ x0 ⬝ᵥ v + c) (hM : 0 < x0 ⬝ᵥ v + c) {R : ℝ}
    (hR : ∀ x ∈ D, |x ⬝ᵥ v + c| ≤ R) (p : ℕ) :
    (x0 ⬝ᵥ v + c) ^ (p + rdim D) ≤
      2 ^ p * 4 ^ rdim D * R ^ rdim D * ∫ x, (max (x ⬝ᵥ v + c) 0) ^ p ∂(nvol D) := by
  haveI := nvol_prob hD hconv hne
  set M := x0 ⬝ᵥ v + c with hMdef
  have hMR : M ≤ R := le_trans (le_abs_self _) (hR x0 hx0)
  have hR0 : 0 < R := lt_of_lt_of_le hM hMR
  have hfc : Continuous fun x : Fin d → ℝ => (max (x ⬝ᵥ v + c) 0) ^ p :=
    ((cont_aff hD hconv hne v c).max continuous_const).pow p
  have hint : Integrable (fun x => (max (x ⬝ᵥ v + c) 0) ^ p) (nvol D) := by
    obtain ⟨Cb, hCb⟩ := hD.exists_bound_of_continuousOn hfc.continuousOn
    refine Integrable.of_bound hfc.aestronglyMeasurable Cb ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (nvol_supp hD)] with x hx
    simp only [Set.mem_compl_iff, not_not] at hx
    exact hCb x hx
  set l := M / (2 * (M + R)) with hl
  have hl0 : 0 < l := by positivity
  have hl1 : l ≤ 1 := by rw [hl, div_le_one (by positivity)]; linarith
  have h := contr_lb hD hconv hne hx0 hl0 hl1 hint (fun x _ => by positivity)
    (c := (M / 2) ^ p) (by positivity) (fun x hx => by
      refine pow_le_pow_left₀ (by positivity) ?_ p
      rw [aff_hom']
      have h1 := (abs_le.1 (hR x hx)).1
      have h2 : M / 2 ≤ (1 - l) * M + l * (x ⬝ᵥ v + c) := by
        have : (1 - l) * M + l * (x ⬝ᵥ v + c) ≥ (1 - l) * M - l * R := by nlinarith
        have e : (1 - l) * M - l * R = M / 2 := by rw [hl]; field_simp; ring
        linarith
      exact le_trans h2 (le_max_left _ _))
  have hlb : M / (4 * R) ≤ l := by
    rw [hl, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h2 : (M / (4 * R)) ^ rdim D * (M / 2) ^ p ≤ ∫ x, (max (x ⬝ᵥ v + c) 0) ^ p ∂(nvol D) :=
    le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hlb _)
      (by positivity)) h
  have e : M ^ (p + rdim D) = 2 ^ p * 4 ^ rdim D * R ^ rdim D *
      ((M / (4 * R)) ^ rdim D * (M / 2) ^ p) := by
    rw [div_pow, div_pow, mul_pow, pow_add]; field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

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

lemma negMax_meas (hne : D.Nonempty) {Ω : Type*} {m : MeasurableSpace Ω} {V : Ω → Fin d → ℝ}
    {c : Ω → ℝ} (hV : Measurable V) (hc : Measurable c) :
    Measurable fun ω => negMax D (V ω) (c ω) := by
  have h := (negMax_cont hD hne).measurable
  exact h.comp (f := fun ω => (V ω, c ω)) (hV.prodMk hc)

end

end G26


-- ===== Solutions.G26.J19 =====

/-! ### (J.19): curvature integrals of positive parts of affine functions -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace G26

open J11

variable {d : ℕ} {D : Set (Fin d → ℝ)} (hD : IsCompact D) (hconv : Convex ℝ D) (hne : D.Nonempty)
include hD hconv hne

lemma hom_mem {x0 : Fin d → ℝ} (hx0 : x0 ∈ D) {l : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1)
    {x : Fin d → ℝ} (hx : x ∈ D) : AffineMap.homothety x0 l x ∈ D :=
  (nvol_hom hD hconv hne hx0 hl0 hl1).1 ⟨x, hx, rfl⟩

/-- the pushforward of `σ` under a contraction toward a point of `D` is at most `λ^{-r} σ` -/
lemma map_hom_le {x0 : Fin d → ℝ} (hx0 : x0 ∈ D) {l : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) :
    (nvol D).map (AffineMap.homothety x0 l) ≤
      ((‖l‖₊⁻¹ ^ (rdim D : ℝ) : ℝ≥0) : ℝ≥0∞) • nvol D := by
  have hm : Measurable (AffineMap.homothety x0 l) :=
    (AffineMap.homothety_continuous x0 l).measurable
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.map_apply hm hs, Measure.smul_apply, smul_eq_mul]
  unfold nvol
  rw [cond_apply hD.isClosed.measurableSet, cond_apply hD.isClosed.measurableSet]
  have hsub : D ∩ AffineMap.homothety x0 l ⁻¹' s ⊆ AffineMap.homothety x0 l ⁻¹' (D ∩ s) :=
    fun x hx => ⟨hom_mem hD hconv hne hx0 hl0 hl1 hx.1, hx.2⟩
  have h1 := measure_mono (μ := μH[(rdim D : ℝ)]) hsub
  rw [hausdorffMeasure_homothety_preimage (Nat.cast_nonneg _) x0 hl0.ne', ENNReal.smul_def,
    smul_eq_mul] at h1
  calc (μH[(rdim D : ℝ)] D)⁻¹ * μH[(rdim D : ℝ)] (D ∩ AffineMap.homothety x0 l ⁻¹' s)
      ≤ (μH[(rdim D : ℝ)] D)⁻¹ * (((‖l‖₊⁻¹ ^ (rdim D : ℝ) : ℝ≥0) : ℝ≥0∞) *
          μH[(rdim D : ℝ)] (D ∩ s)) := by
        gcongr
    _ = _ := by ring

/-- integrals of nonnegative functions composed with a contraction -/
lemma int_comp_hom_le {x0 : Fin d → ℝ} (hx0 : x0 ∈ D) {l : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1)
    {φ : (Fin d → ℝ) → ℝ} (hφ : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x) :
    ∫ x, φ (AffineMap.homothety x0 l x) ∂(nvol D) ≤ (l ^ rdim D)⁻¹ * ∫ x, φ x ∂(nvol D) := by
  have := nvol_prob hD hconv hne
  have hm : Measurable (AffineMap.homothety x0 l) :=
    (AffineMap.homothety_continuous x0 l).measurable
  obtain ⟨Cb, hCb⟩ := hD.exists_bound_of_continuousOn hφ.continuousOn
  have hint : Integrable φ (nvol D) := by
    refine Integrable.of_bound hφ.aestronglyMeasurable Cb ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (nvol_supp hD)] with x hx
    simp only [Set.mem_compl_iff, not_not] at hx
    exact hCb x hx
  set c : ℝ≥0 := ‖l‖₊⁻¹ ^ (rdim D : ℝ) with hc
  have hcval : (c : ℝ) = (l ^ rdim D)⁻¹ := by
    rw [hc, NNReal.coe_rpow, NNReal.coe_inv, coe_nnnorm, Real.norm_eq_abs, abs_of_pos hl0,
      Real.rpow_natCast, inv_pow]
  rw [← integral_map hm.aemeasurable hφ.aestronglyMeasurable]
  calc ∫ x, φ x ∂((nvol D).map (AffineMap.homothety x0 l))
      ≤ ∫ x, φ x ∂((c : ℝ≥0∞) • nvol D) :=
        integral_mono_measure (map_hom_le hD hconv hne hx0 hl0 hl1)
          (ae_of_all _ hφ0) (hint.smul_measure ENNReal.coe_ne_top)
    _ = _ := by
        rw [integral_smul_measure, ENNReal.coe_toReal, hcval, smul_eq_mul]

/-- measure of the contraction of a subset of `D` -/
lemma nvol_hom_sub {x0 : Fin d → ℝ} (hx0 : x0 ∈ D) {l : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1)
    {A : Set (Fin d → ℝ)} (hA : A ⊆ D) :
    nvol D (AffineMap.homothety x0 l '' A) = ENNReal.ofReal (l ^ rdim D) * nvol D A := by
  have hsub : AffineMap.homothety x0 l '' A ⊆ D := by
    rintro _ ⟨x, hx, rfl⟩; exact hom_mem hD hconv hne hx0 hl0 hl1 (hA hx)
  unfold nvol
  rw [cond_apply hD.isClosed.measurableSet, cond_apply hD.isClosed.measurableSet,
    Set.inter_eq_right.2 hsub, Set.inter_eq_right.2 hA,
    hausdorffMeasure_homothety_image (Nat.cast_nonneg _) x0 hl0.ne', ENNReal.smul_def,
    smul_eq_mul]
  have e : ((‖l‖₊ ^ (rdim D : ℝ) : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (l ^ rdim D) := by
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_rpow, coe_nnnorm, Real.norm_eq_abs,
      abs_of_pos hl0, Real.rpow_natCast]
  rw [e]; ring

/-- the third inequality of Lemma J.11, with constant `32`:
`M² ∫ f₊^{p−2} dσ ≤ 32 ∫ f₊^p dσ` when `M = max f > 0` and `r ≤ p` -/
theorem J19a (v : Fin d → ℝ) (c : ℝ) {x0 : Fin d → ℝ} (hx0 : x0 ∈ D) (hM : 0 < x0 ⬝ᵥ v + c) {p : ℕ} (hp : 3 ≤ p)
    (hrp : rdim D ≤ p) :
    (x0 ⬝ᵥ v + c) ^ 2 * ∫ x, (max (x ⬝ᵥ v + c) 0) ^ (p - 2) ∂(nvol D) ≤
      32 * ∫ x, (max (x ⬝ᵥ v + c) 0) ^ p ∂(nvol D) := by
  haveI := nvol_prob hD hconv hne
  set M := x0 ⬝ᵥ v + c with hMdef
  have hfc := cont_aff hD hconv hne v c
  set f : (Fin d → ℝ) → ℝ := fun x => x ⬝ᵥ v + c with hf
  have hfm : Measurable f := hfc.measurable
  -- integrability of bounded continuous functions
  have hbd : ∀ {φ : (Fin d → ℝ) → ℝ}, Continuous φ → Integrable φ (nvol D) := fun {φ} hφ => by
    obtain ⟨Cb, hCb⟩ := hD.exists_bound_of_continuousOn hφ.continuousOn
    refine Integrable.of_bound hφ.aestronglyMeasurable Cb ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (nvol_supp hD)] with x hx
    simp only [Set.mem_compl_iff, not_not] at hx
    exact hCb x hx
  have hpos : Continuous fun x => (max (f x) 0) ^ p := (hfc.max continuous_const).pow p
  have hpos2 : Continuous fun x => (max (f x) 0) ^ (p - 2) :=
    (hfc.max continuous_const).pow (p - 2)
  -- the positive set and its contraction
  set Dp : Set (Fin d → ℝ) := D ∩ {x | 0 < f x} with hDp
  set Dh : Set (Fin d → ℝ) := {x | M / 2 < f x} with hDh
  have hDhm : MeasurableSet Dh := measurableSet_lt measurable_const hfm
  have hDpm : MeasurableSet {x | 0 < f x} := measurableSet_lt measurable_const hfm
  have himg : AffineMap.homothety x0 (1 / 2 : ℝ) '' Dp ⊆ Dh := by
    rintro _ ⟨x, ⟨hxD, hx⟩, rfl⟩
    simp only [Dh, Set.mem_ofPred_eq, f]
    rw [aff_hom']
    simp only [Set.mem_ofPred_eq, f] at hx
    linarith
  have hvol := nvol_hom_sub hD hconv hne hx0 (l := 1 / 2) (by norm_num) (by norm_num)
    (Set.inter_subset_left : Dp ⊆ D)
  -- σ(Dh) ≥ 2^{-r} σ(Dp)
  have hσ : ((1 / 2 : ℝ) ^ rdim D) * (nvol D Dp).toReal ≤ (nvol D Dh).toReal := by
    have h1 := measure_mono (μ := nvol D) himg
    rw [hvol] at h1
    have h2 := ENNReal.toReal_mono (measure_ne_top _ _) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
  -- F ≥ (M/2)^p σ(Dh)
  have hF : (M / 2) ^ p * (nvol D Dh).toReal ≤ ∫ x, (max (f x) 0) ^ p ∂(nvol D) := by
    have h := integral_mono (μ := nvol D) (f := Dh.indicator fun _ => (M / 2) ^ p)
      (g := fun x => (max (f x) 0) ^ p)
      ((integrable_const _).indicator hDhm) (hbd hpos) (fun x => by
        by_cases hx : x ∈ Dh
        · rw [Set.indicator_of_mem hx]
          simp only [Dh, Set.mem_ofPred_eq] at hx
          exact pow_le_pow_left₀ (by positivity) (le_trans hx.le (le_max_left _ _)) _
        · rw [Set.indicator_of_notMem hx]; positivity)
    rw [integral_indicator hDhm, setIntegral_const, smul_eq_mul, mul_comm] at h
    simpa [measureReal_def] using h
  -- pointwise split of `f₊^{p-2}`
  have hpt : ∀ x, (max (f x) 0) ^ (p - 2) ≤
      (M / 4) ^ (p - 2) * ({x | 0 < f x}.indicator (fun _ => (1 : ℝ)) x) +
        16 / M ^ 2 * (max (f x) 0) ^ p := by
    intro x
    rcases le_or_gt (f x) 0 with h0 | h0
    · rw [max_eq_right h0, zero_pow (by omega), zero_pow (by omega), mul_zero]
      have : 0 ≤ {x | 0 < f x}.indicator (fun _ => (1 : ℝ)) x :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) _
      positivity
    · rw [max_eq_left h0.le, Set.indicator_of_mem (show x ∈ {x | 0 < f x} from h0), mul_one]
      rcases le_or_gt (f x) (M / 4) with h1 | h1
      · have := pow_le_pow_left₀ h0.le h1 (p - 2)
        have : 0 ≤ 16 / M ^ 2 * f x ^ p := by positivity
        linarith
      · obtain ⟨k, hk⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
        subst hk
        simp only [Nat.add_sub_cancel]
        have h2 : (M / 4) ^ 2 ≤ f x ^ 2 := pow_le_pow_left₀ (by positivity) h1.le 2
        have h3 : f x ^ k * (M / 4) ^ 2 ≤ f x ^ k * f x ^ 2 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
        have e : 16 / M ^ 2 * f x ^ (k + 2) = (f x ^ k * f x ^ 2) / (M / 4) ^ 2 := by
          rw [pow_add]; field_simp; ring
        rw [e]
        have h4 : f x ^ k ≤ f x ^ k * f x ^ 2 / (M / 4) ^ 2 := by
          rw [le_div_iff₀ (by positivity)]; exact h3
        have : 0 ≤ (M / 4) ^ k := by positivity
        linarith
  have hind : Integrable ({x | 0 < f x}.indicator fun _ => (1 : ℝ)) (nvol D) :=
    (integrable_const _).indicator hDpm
  have hint := integral_mono (hbd hpos2) (((hind.const_mul _)).add ((hbd hpos).const_mul _)) hpt
  simp only [Pi.add_apply] at hint
  rw [integral_add (hind.const_mul _) ((hbd hpos).const_mul _), integral_const_mul,
    integral_const_mul, integral_indicator hDpm, setIntegral_const, smul_eq_mul, mul_one] at hint
  -- σ({f > 0}) = σ(Dp)
  have hDpeq : (nvol D).real {x | 0 < f x} = (nvol D Dp).toReal := by
    rw [measureReal_def]
    congr 1
    unfold nvol
    rw [cond_apply hD.isClosed.measurableSet, cond_apply hD.isClosed.measurableSet,
      ← Set.inter_assoc, Set.inter_self]
  rw [hDpeq] at hint
  -- combine
  set F := ∫ x, (max (f x) 0) ^ p ∂(nvol D)
  have hF0 : 0 ≤ F := integral_nonneg fun x => by positivity
  have hDp0 : 0 ≤ (nvol D Dp).toReal := ENNReal.toReal_nonneg
  have hσDp : (nvol D Dp).toReal ≤ 2 ^ (p + rdim D) * F / M ^ p := by
    rw [le_div_iff₀ (by positivity)]
    have h1 : (M / 2) ^ p * ((1 / 2 : ℝ) ^ rdim D * (nvol D Dp).toReal) ≤ F :=
      le_trans (mul_le_mul_of_nonneg_left hσ (by positivity)) hF
    have e : (M / 2) ^ p * ((1 / 2 : ℝ) ^ rdim D * (nvol D Dp).toReal) =
        (nvol D Dp).toReal * M ^ p / 2 ^ (p + rdim D) := by
      rw [div_pow, one_div_pow, pow_add]; field_simp
    rw [e, div_le_iff₀ (by positivity)] at h1
    linarith
  have hkey : M ^ 2 * ((M / 4) ^ (p - 2) * (nvol D Dp).toReal) ≤ 16 * F := by
    have h1 : M ^ 2 * ((M / 4) ^ (p - 2) * (nvol D Dp).toReal) ≤
        M ^ 2 * ((M / 4) ^ (p - 2) * (2 ^ (p + rdim D) * F / M ^ p)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hσDp (by positivity)) (by positivity)
    have e : M ^ 2 * ((M / 4) ^ (p - 2) * (2 ^ (p + rdim D) * F / M ^ p)) =
        F * (2 ^ (p + rdim D) / 4 ^ (p - 2)) := by
      obtain ⟨k, hk⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
      subst hk
      simp only [Nat.add_sub_cancel]
      rw [div_pow, pow_add M]; field_simp
    have h2 : (2 : ℝ) ^ (p + rdim D) / 4 ^ (p - 2) ≤ 16 := by
      rw [div_le_iff₀ (by positivity)]
      obtain ⟨k, hk⟩ : ∃ k, p = k + 2 := ⟨p - 2, by omega⟩
      subst hk
      simp only [Nat.add_sub_cancel]
      have h4 : (4 : ℝ) ^ k = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
      rw [h4, show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_add]
      have := hrp
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    rw [e] at h1
    nlinarith
  have hfin : M ^ 2 * ((M / 4) ^ (p - 2) * (nvol D Dp).toReal + 16 / M ^ 2 * F) ≤ 32 * F := by
    have e : M ^ 2 * (16 / M ^ 2 * F) = 16 * F := by field_simp
    rw [mul_add, e]; linarith
  calc M ^ 2 * ∫ x, (max (x ⬝ᵥ v + c) 0) ^ (p - 2) ∂(nvol D)
      ≤ M ^ 2 * ((M / 4) ^ (p - 2) * (nvol D Dp).toReal + 16 / M ^ 2 * F) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ ≤ 32 * F := hfin

/-- **(J.19)** with constant `32`: for `c ≥ 0` and `M = max f > 0`,
`∫ (f + c)₊^{p−2} dσ ≤ 32 (1 + c/M)^{p−2+r} ∫ f₊^p dσ / M²` -/
theorem J19 (v : Fin d → ℝ) (c : ℝ) {x0 : Fin d → ℝ} (hx0 : x0 ∈ D) (hM : 0 < x0 ⬝ᵥ v + c) {p : ℕ} (hp : 3 ≤ p)
    (hrp : rdim D ≤ p) {b : ℝ} (hb : 0 ≤ b) :
    (x0 ⬝ᵥ v + c) ^ 2 * ∫ x, (max (x ⬝ᵥ v + c + b) 0) ^ (p - 2) ∂(nvol D) ≤
      32 * (1 + b / (x0 ⬝ᵥ v + c)) ^ (p - 2 + rdim D) *
        ∫ x, (max (x ⬝ᵥ v + c) 0) ^ p ∂(nvol D) := by
  set M := x0 ⬝ᵥ v + c with hMdef
  set l := M / (M + b) with hl
  have hl0 : 0 < l := by positivity
  have hl1 : l ≤ 1 := by rw [hl, div_le_one (by positivity)]; linarith
  have hfc := cont_aff hD hconv hne v c
  have hpt : ∀ x, (max (x ⬝ᵥ v + c + b) 0) ^ (p - 2) =
      (l ^ (p - 2))⁻¹ * (max (AffineMap.homothety x0 l x ⬝ᵥ v + c) 0) ^ (p - 2) := by
    intro x
    rw [aff_hom']
    have e : (1 - l) * M + l * (x ⬝ᵥ v + c) = l * (x ⬝ᵥ v + c + b) := by
      rw [hl]; field_simp; ring
    have hmx : max (l * (x ⬝ᵥ v + c + b)) 0 = l * max (x ⬝ᵥ v + c + b) 0 := by
      rw [mul_max_of_nonneg _ _ hl0.le, mul_zero]
    rw [e, hmx, mul_pow]
    field_simp
  have hφ : Continuous fun x : Fin d → ℝ => (max (x ⬝ᵥ v + c) 0) ^ (p - 2) :=
    (hfc.max continuous_const).pow _
  have h1 := int_comp_hom_le hD hconv hne hx0 hl0 hl1 hφ (fun x => by positivity)
  have h2 := J19a hD hconv hne v c hx0 hM hp hrp
  simp_rw [hpt]
  rw [integral_const_mul]
  have hli : (l : ℝ)⁻¹ = 1 + b / M := by rw [hl]; field_simp
  have e : (1 + b / M) ^ (p - 2 + rdim D) = (l ^ (p - 2))⁻¹ * (l ^ rdim D)⁻¹ := by
    rw [← hli, pow_add, inv_pow, inv_pow]
  rw [e]
  set I2 := ∫ x, (max (x ⬝ᵥ v + c) 0) ^ (p - 2) ∂(nvol D)
  set I1 := ∫ x, (max (AffineMap.homothety x0 l x ⬝ᵥ v + c) 0) ^ (p - 2) ∂(nvol D)
  have hi1 : (l ^ (p - 2))⁻¹ * I1 ≤ (l ^ (p - 2))⁻¹ * ((l ^ rdim D)⁻¹ * I2) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  calc M ^ 2 * ((l ^ (p - 2))⁻¹ * I1) ≤ M ^ 2 * ((l ^ (p - 2))⁻¹ * ((l ^ rdim D)⁻¹ * I2)) :=
        mul_le_mul_of_nonneg_left hi1 (by positivity)
    _ = (l ^ (p - 2))⁻¹ * (l ^ rdim D)⁻¹ * (M ^ 2 * I2) := by ring
    _ ≤ (l ^ (p - 2))⁻¹ * (l ^ rdim D)⁻¹ * (32 * ∫ x, (max (x ⬝ᵥ v + c) 0) ^ p ∂(nvol D)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

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

lemma FI.negMax_meas (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) :
    Measurable[F n] (fun ω => negMax D (V n ω) (c n ω)) :=
  G26.negMax_meas I.hD I.hne (I.Vm n hn) (I.cm n hn)

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

end G26

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

end G26


-- ===== Solutions.G26.Freeze =====

/-! ### Freezing an affine field at a predictable stopping rule -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {d : ℕ} {Ω : Type*}

lemma survS_anti (A : ℕ → Set Ω) {m n : ℕ} (h : m ≤ n) : survS A n ⊆ survS A m := by
  intro ω hω
  simp only [survS, Set.mem_iInter, Finset.mem_range] at hω ⊢
  exact fun i hi => hω i (by omega)

/-- on the surviving set the frozen field is the field -/
lemma frz_eq {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) :
    ∀ n ω, (n = 0 ∨ ω ∈ survS A (n - 1)) → frz X A n ω = X n ω := by
  intro n ω h
  cases n with
  | zero => rfl
  | succ n =>
    simp only [Nat.add_sub_cancel] at h
    rcases h with h | h
    · omega
    · simp only [frz, if_pos h]

lemma frz_eq_of_mem {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) {n : ℕ} {ω : Ω}
    (h : ω ∈ survS A n) : frz X A n ω = X n ω := by
  cases n with
  | zero => rfl
  | succ n => exact frz_eq X A (n + 1) ω (Or.inr (survS_anti A (by omega) h))

lemma frz_succ_of_notMem {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) {n : ℕ} {ω : Ω}
    (h : ω ∉ survS A n) : frz X A (n + 1) ω = frz X A n ω := by
  simp only [frz, if_neg h]

/-- once frozen at the first failure `i`, the field stays at its value at `i` -/
lemma frz_stop {E : Type*} (X : ℕ → Ω → E) (A : ℕ → Set Ω) {i : ℕ} {ω : Ω}
    (hi : i = 0 ∨ ω ∈ survS A (i - 1)) (hfail : ω ∉ A i) :
    ∀ N, i ≤ N → frz X A N ω = X i ω := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact frz_eq X A i ω hi
  | succ N hiN ih =>
    have hnot : ω ∉ survS A N := by
      intro h
      have := survS_anti A hiN h
      simp only [survS, Set.mem_iInter, Finset.mem_range] at this
      exact hfail (this i (by omega))
    rw [frz_succ_of_notMem X A hnot, ih]

/-- the frozen pair `(V, c)` at time `n` equals the pair at a common earlier time -/
lemma frz_pair_exists (V : ℕ → Ω → (Fin d → ℝ)) (c : ℕ → Ω → ℝ) (A : ℕ → Set Ω) :
    ∀ n ω, ∃ i ≤ n, frz V A n ω = V i ω ∧ frz c A n ω = c i ω := by
  intro n ω
  induction n with
  | zero => exact ⟨0, le_rfl, rfl, rfl⟩
  | succ n ih =>
    by_cases h : ω ∈ survS A n
    · exact ⟨n + 1, le_rfl, by simp only [frz, if_pos h], by simp only [frz, if_pos h]⟩
    · obtain ⟨i, hi, he, he'⟩ := ih
      exact ⟨i, by omega, by rw [frz_succ_of_notMem V A h, he],
        by rw [frz_succ_of_notMem c A h, he']⟩

/-- the increment of the frozen field -/
lemma fxi_frz (V : ℕ → Ω → (Fin d → ℝ)) (c : ℕ → Ω → ℝ) (A : ℕ → Set Ω) (n : ℕ) (ω : Ω)
    (u : Fin d → ℝ) :
    fxi (frz V A) (frz c A) n ω u = (survS A n).indicator (fun ω => fxi V c n ω u) ω := by
  by_cases h : ω ∈ survS A n
  · rw [Set.indicator_of_mem h]
    unfold fxi fz
    rw [frz_eq_of_mem V A h, frz_eq_of_mem c A h]
    simp only [frz, if_pos h]
  · rw [Set.indicator_of_notMem h]
    unfold fxi fz
    rw [frz_succ_of_notMem V A h, frz_succ_of_notMem c A h]; ring

section

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma FI.Fmono' (I : FI D μ F T V c J β B lo hi m0) {m n : ℕ} (hmn : m ≤ n) (hn : n ≤ T) :
    F m ≤ F n := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hmn ih => exact (ih (by omega)).trans (I.Fmono n (by omega))

lemma FI.survS_meas (I : FI D μ F T V c J β B lo hi m0) {A : ℕ → Set Ω}
    (hA : ∀ n ≤ T, MeasurableSet[F n] (A n)) {n : ℕ} (hn : n ≤ T) :
    MeasurableSet[F n] (survS A n) := by
  unfold survS
  refine Finset.measurableSet_biInter _ fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  exact I.Fmono' (by omega) hn _ (hA i (by omega))

lemma FI.frz_meas (I : FI D μ F T V c J β B lo hi m0) {A : ℕ → Set Ω}
    (hA : ∀ n ≤ T, MeasurableSet[F n] (A n)) {E : Type*} [MeasurableSpace E]
    (X : ℕ → Ω → E) (hX : ∀ n ≤ T, Measurable[F n] (X n)) :
    ∀ n ≤ T, Measurable[F n] (frz X A n) := by
  intro n hn
  induction n with
  | zero => exact hX 0 hn
  | succ n ih =>
    have hS := I.survS_meas hA (n := n) (by omega)
    have hmono := I.Fmono n (by omega)
    classical
    show Measurable[F (n + 1)] fun ω => if ω ∈ survS A n then X (n + 1) ω else frz X A n ω
    exact Measurable.ite (hmono _ hS) (hX (n + 1) hn) ((ih (by omega)).mono hmono le_rfl)

lemma FI.fxi_int [IsFiniteMeasure μ] (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n < T)
    {u : Fin d → ℝ} (hu : u ∈ D) :
    ∃ r : ℝ, Integrable (fun ω => fxi V c n ω u) μ ∧ ∀ᵐ ω ∂μ, |fxi V c n ω u| ≤ r := by
  obtain ⟨r0, -, hr0⟩ := I.env' hn.le
  obtain ⟨r1, -, hr1⟩ := I.env' (n := n + 1) hn
  have hb : ∀ᵐ ω ∂μ, |fxi V c n ω u| ≤ r1 + r0 := by
    filter_upwards [hr0, hr1] with ω h0 h1
    unfold fxi
    exact le_trans (abs_sub _ _) (add_le_add (h1.2 u hu) (h0.2 u hu))
  refine ⟨r1 + r0, ?_, hb⟩
  have hm : Measurable (fun ω => fxi V c n ω u) := by
    unfold fxi
    exact ((I.fz_meas hn u).mono (I.Fle (n + 1) hn) le_rfl).sub
      ((I.fz_meas hn.le u).mono (I.Fle n hn.le) le_rfl)
  exact Integrable.of_bound hm.aestronglyMeasurable _ (by
    filter_upwards [hb] with ω h; rwa [Real.norm_eq_abs])

lemma FI.frz_N0 (I : FI D μ F T V c J β B lo hi m0) (A : ℕ → Set Ω) {n : ℕ} (hn : n ≤ T) :
    ∀ᵐ ω ∂μ, 0 ≤ negMax D (frz V A n ω) (frz c A n ω) := by
  have hall : ∀ᵐ ω ∂μ, ∀ i : Fin (n + 1), 0 ≤ negMax D (V i ω) (c i ω) :=
    ae_all_iff.2 fun i => I.N0 i (by have := i.2; omega)
  filter_upwards [hall] with ω hω
  obtain ⟨i, hi, hV, hc⟩ := frz_pair_exists V c A n ω
  rw [hV, hc]; exact hω ⟨i, by omega⟩

/-- **freezing preserves the field interface** -/
theorem FI.freeze [IsFiniteMeasure μ] (I : FI D μ F T V c J β B lo hi m0) {A : ℕ → Set Ω}
    (hA : ∀ n ≤ T, MeasurableSet[F n] (A n)) (hlo : lo ≤ 0) (hhi : 0 ≤ hi)
    (hβ : ∀ n, 0 ≤ β n) (hB : 0 < B) {J' : ℕ → Set Ω} (hJ'm : ∀ n ≤ T, MeasurableSet[F n] (J' n))
    (hJ'mono : ∀ n, J' (n + 1) ⊆ J' n) (hAJ : ∀ n, survS A n ∩ J' n ⊆ J n) :
    FI D μ F T (frz V A) (frz c A) J' β B lo hi m0 where
  hD := I.hD
  hconv := I.hconv
  hne := I.hne
  Fle := I.Fle
  Fmono := I.Fmono
  Vm := I.frz_meas hA V I.Vm
  cm := I.frz_meas hA c I.cm
  Jm := hJ'm
  Jmono := hJ'mono
  env := by
    intro n hn
    have : ∀ i ∈ Finset.range (n + 1), ∃ r : ℝ, ∀ᵐ ω ∂μ, ∀ u ∈ D, |u ⬝ᵥ V i ω + c i ω| ≤ r :=
      fun i hi => I.env i (by have := Finset.mem_range.1 hi; omega)
    choose r hr using this
    refine ⟨∑ i ∈ (Finset.range (n + 1)).attach, max (r i.1 i.2) 0, ?_⟩
    have hall : ∀ᵐ ω ∂μ, ∀ i : Finset.range (n + 1), ∀ u ∈ D, |u ⬝ᵥ V i ω + c i ω| ≤ r i.1 i.2 :=
      ae_all_iff.2 fun i => hr i.1 i.2
    filter_upwards [hall] with ω hω u hu
    obtain ⟨i, hi, hV, hc⟩ := frz_pair_exists V c A n ω
    have hmem : i ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
    have hle : max (r i hmem) 0 ≤ ∑ j ∈ (Finset.range (n + 1)).attach, max (r j.1 j.2) 0 :=
      Finset.single_le_sum (f := fun j : Finset.range (n + 1) => max (r j.1 j.2) 0)
        (fun j _ => le_max_right _ _) (Finset.mem_attach _ ⟨i, hmem⟩)
    rw [hV, hc]
    exact ((hω ⟨i, hmem⟩ u hu).trans (le_max_left _ _)).trans hle
  N0 := fun n hn => I.frz_N0 A hn
  drift := by
    intro n hm0 hn u hu
    have hS := I.survS_meas hA (n := n) hn.le
    obtain ⟨r, hint, -⟩ := I.fxi_int hn hu
    have hce : μ[fun ω => fxi (frz V A) (frz c A) n ω u | F n] =ᵐ[μ]
        (survS A n).indicator (μ[fun ω => fxi V c n ω u | F n]) := by
      have e : (fun ω => fxi (frz V A) (frz c A) n ω u) =
          (survS A n).indicator (fun ω => fxi V c n ω u) := by
        funext ω; exact fxi_frz V c A n ω u
      rw [e]
      exact condExp_indicator hint hS
    filter_upwards [hce, I.drift n hm0 hn u hu] with ω h1 h2 hJ
    rw [h1]
    by_cases hω : ω ∈ survS A n
    · rw [Set.indicator_of_mem hω]; exact h2 (hAJ n ⟨hω, hJ⟩)
    · rw [Set.indicator_of_notMem hω]; exact ⟨hlo, hhi⟩
  mag := by
    intro n hm0 hn
    filter_upwards [I.mag n hm0 hn, I.frz_N0 A hn.le] with ω hω hN hJ u hu
    by_cases hS : ω ∈ survS A n
    · rw [fxi_frz, Set.indicator_of_mem hS, fz, frz_eq_of_mem V A hS, frz_eq_of_mem c A hS]
      exact hω (hAJ n ⟨hS, hJ⟩) u hu
    · rw [fxi_frz, Set.indicator_of_notMem hS, abs_zero]
      have h1 := negMax_ge I.hD hu (frz V A n ω) (frz c A n ω)
      have h2 : 0 ≤ fz (frz V A) (frz c A) n ω u + 2 * negMax D (frz V A n ω) (frz c A n ω) := by
        unfold fz; linarith
      have := hβ n
      positivity
  sec := by
    intro n hm0 hn u hu
    have hS := I.survS_meas hA (n := n) hn.le
    obtain ⟨r, hint, hb⟩ := I.fxi_int hn hu
    have hint2 : Integrable (fun ω => fxi V c n ω u ^ 2) μ := by
      refine Integrable.of_bound (hint.aestronglyMeasurable.pow 2) (r ^ 2) ?_
      filter_upwards [hb] with ω h
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    have hce : μ[fun ω => fxi (frz V A) (frz c A) n ω u ^ 2 | F n] =ᵐ[μ]
        (survS A n).indicator (μ[fun ω => fxi V c n ω u ^ 2 | F n]) := by
      have e : (fun ω => fxi (frz V A) (frz c A) n ω u ^ 2) =
          (survS A n).indicator (fun ω => fxi V c n ω u ^ 2) := by
        funext ω
        rw [fxi_frz]
        by_cases hω : ω ∈ survS A n
        · simp [hω]
        · simp [hω]
      rw [e]
      exact condExp_indicator hint2 hS
    filter_upwards [hce, I.sec n hm0 hn u hu] with ω h1 h2 hJ
    rw [h1]
    by_cases hω : ω ∈ survS A n
    · rw [Set.indicator_of_mem hω, fz, frz_eq_of_mem V A hω, frz_eq_of_mem c A hω]
      exact h2 (hAJ n ⟨hω, hJ⟩)
    · rw [Set.indicator_of_notMem hω]
      have := hβ n
      positivity

end

end G26


-- ===== Solutions.G26.NegAlg =====

/-! ### Pathwise algebra of the negative integral moment recurrence (Lemma G.24) -/

namespace G26

/-- linearization of the large-branch remainder `320 P² β F / Q²` -/
lemma neg_lin (k : ℕ) (hk : 2 ≤ k) (b β x F Q : ℝ) (hx : 1 ≤ x) (hβ : 0 ≤ β)
    (hβb : β ^ 2 ≤ b ^ 2 * x) (hb : 0 ≤ b) (hQ : 0 < Q) (hF0 : 0 ≤ F) (hFQ : F ≤ Q ^ (4 * k)) :
    320 * (4 * k : ℝ) ^ 2 * β * F / Q ^ 2 ≤
      F / x + (320 * (4 * k : ℝ) ^ 2) ^ (2 * k) * b ^ (2 * k) * x ^ (3 * k - 1) := by
  set c := 320 * (4 * k : ℝ) ^ 2 with hc
  have hc0 : 0 < c := by positivity
  have hx0 : 0 < x := by linarith
  rcases le_or_gt (c * β * x) (Q ^ 2) with hbig | hsm
  · have : c * β * F / Q ^ 2 ≤ F / x := by
      rw [div_le_div_iff₀ (by positivity) hx0]
      have := mul_le_mul_of_nonneg_left hbig hF0
      nlinarith
    have : 0 ≤ c ^ (2 * k) * b ^ (2 * k) * x ^ (3 * k - 1) := by positivity
    linarith
  · -- small negative maximum
    have h1 : c * β * F / Q ^ 2 ≤ c * β * Q ^ (4 * k - 2) := by
      rw [div_le_iff₀ (by positivity)]
      have e : Q ^ (4 * k - 2) * Q ^ 2 = Q ^ (4 * k) := by rw [← pow_add]; congr 1; omega
      calc c * β * F ≤ c * β * Q ^ (4 * k) := mul_le_mul_of_nonneg_left hFQ (by positivity)
        _ = c * β * Q ^ (4 * k - 2) * Q ^ 2 := by rw [← e]; ring
    have h2 : Q ^ (4 * k - 2) ≤ (c * β * x) ^ (2 * k - 1) := by
      have e : Q ^ (4 * k - 2) = (Q ^ 2) ^ (2 * k - 1) := by rw [← pow_mul]; congr 1; omega
      rw [e]; exact pow_le_pow_left₀ (by positivity) hsm.le _
    have h3 : c * β * (c * β * x) ^ (2 * k - 1) = c ^ (2 * k) * β ^ (2 * k) * x ^ (2 * k - 1) := by
      rw [mul_pow, mul_pow]
      have e1 : c * c ^ (2 * k - 1) = c ^ (2 * k) := by rw [← pow_succ']; congr 1; omega
      have e2 : β * β ^ (2 * k - 1) = β ^ (2 * k) := by rw [← pow_succ']; congr 1; omega
      rw [← e1, ← e2]; ring
    have h4 : β ^ (2 * k) ≤ b ^ (2 * k) * x ^ k := by
      have e : β ^ (2 * k) = (β ^ 2) ^ k := by rw [← pow_mul]
      have e' : b ^ (2 * k) * x ^ k = (b ^ 2 * x) ^ k := by rw [mul_pow, ← pow_mul]
      rw [e, e']; exact pow_le_pow_left₀ (by positivity) hβb k
    have h5 : x ^ k * x ^ (2 * k - 1) = x ^ (3 * k - 1) := by rw [← pow_add]; congr 1; omega
    have h6 : c * β * Q ^ (4 * k - 2) ≤ c ^ (2 * k) * b ^ (2 * k) * x ^ (3 * k - 1) := by
      calc c * β * Q ^ (4 * k - 2) ≤ c * β * (c * β * x) ^ (2 * k - 1) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = c ^ (2 * k) * β ^ (2 * k) * x ^ (2 * k - 1) := h3
        _ ≤ c ^ (2 * k) * (b ^ (2 * k) * x ^ k) * x ^ (2 * k - 1) := by gcongr
        _ = c ^ (2 * k) * b ^ (2 * k) * x ^ (3 * k - 1) := by rw [← h5]; ring
    have : 0 ≤ F / x := by positivity
    linarith

/-- **negative recurrence, pathwise** (with `P = 4k`, `j ≤ P`) -/
lemma neg_alg (k : ℕ) (hk : 2 ≤ k) (j : ℕ) (hj : j ≤ 4 * k) (B b β x F Q I2 : ℝ)
    (hB : 2 ^ 20 * (4 * k : ℝ) ≤ B) (hx : 1 ≤ x) (hβ : 1 ≤ β) (hβb : β ^ 2 ≤ b ^ 2 * x)
    (hb : 0 ≤ b) (hQ : 0 ≤ Q) (hF0 : 0 ≤ F) (hFQ : F ≤ Q ^ (4 * k)) (hI20 : 0 ≤ I2)
    (hA : 16 * ((4 * k : ℝ) + j) * β ≤ Q → Q ^ 2 * I2 ≤ 64 * F)
    (hS : Q < 16 * ((4 * k : ℝ) + j) * β → I2 ≤ (37 * (4 * k : ℝ) * β) ^ (4 * k - 2)) :
    F + ((4 * k : ℝ) * (4 * k - 1) / 2) * ((10 * β + 2 * (3 * Q + 4 * β) ^ 2 / (B * x)) * I2) ≤
      (1 + (1 + 1024 * (4 * k : ℝ) ^ 2 / B) / x) * F + Kneg k b B * x ^ (3 * k - 1) := by
  set P : ℝ := 4 * k with hPdef
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hPr : (8 : ℝ) ≤ P := by rw [hPdef]; linarith
  have hB0 : 0 < B := by nlinarith
  have hx0 : 0 < x := by linarith
  have hjr : (j : ℝ) ≤ P := by rw [hPdef]; exact_mod_cast hj
  have hc0 : 0 ≤ P * (P - 1) / 2 := by nlinarith
  have hcP : P * (P - 1) / 2 ≤ P ^ 2 / 2 := by nlinarith
  have hK1 : 0 ≤ (320 * P ^ 2) ^ (2 * k) * b ^ (2 * k) * x ^ (3 * k - 1) := by positivity
  have hK2 : 0 ≤ P ^ 2 / 2 * (10 + 20000 * P ^ 2 / B) * (37 * P) ^ (4 * k - 2) * b ^ (4 * k) *
      x ^ (3 * k - 1) := by positivity
  have hKe : Kneg k b B * x ^ (3 * k - 1) = (320 * P ^ 2) ^ (2 * k) * b ^ (2 * k) * x ^ (3 * k - 1) +
      P ^ 2 / 2 * (10 + 20000 * P ^ 2 / B) * (37 * P) ^ (4 * k - 2) * b ^ (4 * k) *
        x ^ (3 * k - 1) := by
    unfold Kneg; rw [hPdef]; ring
  rw [hKe]
  have hV0 : 0 ≤ 10 * β + 2 * (3 * Q + 4 * β) ^ 2 / (B * x) := by positivity
  rcases le_or_gt (16 * (P + j) * β) Q with hbig | hsm
  · have hQ0 : 0 < Q := by nlinarith
    have hI := hA hbig
    have h4β : 4 * β ≤ Q := by nlinarith
    have h1 : (3 * Q + 4 * β) ^ 2 ≤ 16 * Q ^ 2 := by nlinarith
    have hI2Q : I2 ≤ 64 * F / Q ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
    -- curvature ≤ 320 P² β F/Q² + 1024 P² F/(B x)
    have hcurv : (P * (P - 1) / 2) * ((10 * β + 2 * (3 * Q + 4 * β) ^ 2 / (B * x)) * I2) ≤
        320 * P ^ 2 * β * F / Q ^ 2 + 1024 * P ^ 2 / B / x * F := by
      have h2 : (10 * β + 2 * (3 * Q + 4 * β) ^ 2 / (B * x)) ≤ 10 * β + 32 * Q ^ 2 / (B * x) := by
        have : 2 * (3 * Q + 4 * β) ^ 2 ≤ 32 * Q ^ 2 := by linarith
        gcongr
      calc (P * (P - 1) / 2) * ((10 * β + 2 * (3 * Q + 4 * β) ^ 2 / (B * x)) * I2)
          ≤ (P ^ 2 / 2) * ((10 * β + 32 * Q ^ 2 / (B * x)) * (64 * F / Q ^ 2)) :=
            mul_le_mul hcP (mul_le_mul h2 hI2Q hI20 (by positivity)) (by positivity)
              (by positivity)
        _ = 320 * P ^ 2 * β * F / Q ^ 2 + 1024 * P ^ 2 / B / x * F := by
            field_simp; ring
    have hlin := neg_lin k hk b β x F Q hx (by linarith) hβb hb hQ0 hF0 hFQ
    rw [← hPdef] at hlin
    have e : (1 + (1 + 1024 * P ^ 2 / B) / x) * F = F + F / x + 1024 * P ^ 2 / B / x * F := by
      field_simp; ring
    rw [e]
    linarith only [hcurv, hlin, hK2]
  · -- small branch
    have hI := hS hsm
    have hjb : 16 * (P + j) * β ≤ 32 * P * β := by
      have : 16 * (P + j) ≤ 32 * P := by linarith
      exact mul_le_mul_of_nonneg_right this (by linarith)
    have hQ' : Q < 32 * P * β := lt_of_lt_of_le hsm hjb
    have hβ2 : β ≤ β ^ 2 := by nlinarith
    have hV : 10 * β + 2 * (3 * Q + 4 * β) ^ 2 / (B * x) ≤ (10 + 20000 * P ^ 2 / B) * β ^ 2 := by
      have h0 : 3 * Q + 4 * β ≤ 100 * P * β := by
        have : 4 * β ≤ 4 * P * β := by
          have := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ P by linarith) (by linarith : (0:ℝ) ≤ β)
          linarith
        linarith only [this, hQ']
      have h1 : (3 * Q + 4 * β) ^ 2 ≤ 10000 * P ^ 2 * β ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) h0 2
        calc (3 * Q + 4 * β) ^ 2 ≤ (100 * P * β) ^ 2 := this
          _ = 10000 * P ^ 2 * β ^ 2 := by ring
      have h2 : 2 * (3 * Q + 4 * β) ^ 2 / (B * x) ≤ 20000 * P ^ 2 / B * β ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        have e1 : 20000 * P ^ 2 / B * β ^ 2 * (B * x) = 20000 * P ^ 2 * β ^ 2 * x := by field_simp
        rw [e1]
        have h3 : 20000 * P ^ 2 * β ^ 2 ≤ 20000 * P ^ 2 * β ^ 2 * x :=
          le_mul_of_one_le_right (by positivity) hx
        linarith only [h1, h3]
      have e2 : (10 + 20000 * P ^ 2 / B) * β ^ 2 = 10 * β ^ 2 + 20000 * P ^ 2 / B * β ^ 2 := by ring
      rw [e2]
      linarith only [h2, hβ2]
    have hpow : β ^ 2 * β ^ (4 * k - 2) = β ^ (4 * k) := by rw [← pow_add]; congr 1; omega
    have hβP : β ^ (4 * k) ≤ b ^ (4 * k) * x ^ (2 * k) := by
      have e : β ^ (4 * k) = (β ^ 2) ^ (2 * k) := by rw [← pow_mul]; congr 1; ring
      have e' : b ^ (4 * k) * x ^ (2 * k) = (b ^ 2 * x) ^ (2 * k) := by
        rw [mul_pow, ← pow_mul]; congr 2; ring
      rw [e, e']; exact pow_le_pow_left₀ (by positivity) hβb _
    have hx2 : x ^ (2 * k) ≤ x ^ (3 * k - 1) := pow_le_pow_right₀ hx (by omega)
    have hcurv : (P * (P - 1) / 2) * ((10 * β + 2 * (3 * Q + 4 * β) ^ 2 / (B * x)) * I2) ≤
        P ^ 2 / 2 * (10 + 20000 * P ^ 2 / B) * (37 * P) ^ (4 * k - 2) * b ^ (4 * k) *
          x ^ (3 * k - 1) := by
      calc (P * (P - 1) / 2) * ((10 * β + 2 * (3 * Q + 4 * β) ^ 2 / (B * x)) * I2)
          ≤ (P ^ 2 / 2) * (((10 + 20000 * P ^ 2 / B) * β ^ 2) * (37 * P * β) ^ (4 * k - 2)) :=
            mul_le_mul hcP (mul_le_mul hV hI hI20 (by positivity)) (by positivity) (by positivity)
        _ = P ^ 2 / 2 * (10 + 20000 * P ^ 2 / B) * (37 * P) ^ (4 * k - 2) * β ^ (4 * k) := by
            rw [mul_pow (37 * P), ← hpow]; ring
        _ ≤ P ^ 2 / 2 * (10 + 20000 * P ^ 2 / B) * (37 * P) ^ (4 * k - 2) *
              (b ^ (4 * k) * x ^ (2 * k)) := by gcongr
        _ ≤ P ^ 2 / 2 * (10 + 20000 * P ^ 2 / B) * (37 * P) ^ (4 * k - 2) * b ^ (4 * k) *
              x ^ (3 * k - 1) := by
            rw [← mul_assoc]; gcongr
    have h1 : 0 ≤ (1 + 1024 * P ^ 2 / B) / x * F := by positivity
    have e : (1 + (1 + 1024 * P ^ 2 / B) / x) * F = F + (1 + 1024 * P ^ 2 / B) / x * F := by ring
    rw [e]
    linarith only [hcurv, h1, hK1]

end G26


-- ===== Solutions.G26.NegRec =====

/-! ### The negative integral moment recurrence (Lemmas G.24, G.25) -/

open MeasureTheory ProbabilityTheory Set J11

namespace G26

variable {d : ℕ} {Ω : Type*}

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

omit mΩ in
lemma Ff_nonneg (P : ℕ) (n : ℕ) (ω : Ω) : 0 ≤ Ff D V c P n ω :=
  integral_nonneg fun _ => pow_nonneg (le_max_right _ _) _

lemma FI.Ff_meas (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T) (P : ℕ) :
    StronglyMeasurable (Ff D V c P n) := by
  have := nvol_prob I.hD I.hconv I.hne
  have h : StronglyMeasurable (fun p : Ω × (Fin d → ℝ) => (max (-fz V c n p.1 p.2) 0) ^ P) := by
    have h0 : Measurable (fun p : (Fin d → ℝ) × Ω => (max (-fz V c n p.2 p.1) 0) ^ P) :=
      ((I.fz_jmeas hn).neg.max (measurable_const (a := (0 : ℝ)))).pow_const P
    exact (h0.comp measurable_swap).stronglyMeasurable
  exact h.integral_prod_right'

/-- `F_n ≤ N_n^P` -/
lemma FI.Ff_le (I : FI D μ F T V c J β B lo hi m0) (P : ℕ) (n : ℕ) (ω : Ω)
    (hN : 0 ≤ negMax D (V n ω) (c n ω)) :
    Ff D V c P n ω ≤ negMax D (V n ω) (c n ω) ^ P := by
  have := nvol_prob I.hD I.hconv I.hne
  have hint := cont_bdd_int I.hD (φ := fun u => (max (-fz V c n ω u) 0) ^ P)
    (((fz_cont V c n ω).neg.max continuous_const).pow P)
  calc Ff D V c P n ω ≤ ∫ _u, negMax D (V n ω) (c n ω) ^ P ∂(nvol D) := by
        refine integral_mono_ae hint (integrable_const _) ?_
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 (nvol_supp I.hD)] with u hu
        simp only [Set.mem_compl_iff, not_not] at hu
        refine pow_le_pow_left₀ (le_max_right _ _) (max_le ?_ hN) _
        exact negMax_ge I.hD hu _ _
    _ = _ := by simp

lemma FI.Ff_bdd [IsProbabilityMeasure μ] (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T)
    (P : ℕ) : ∃ r : ℝ, ∀ᵐ ω ∂μ, |Ff D V c P n ω| ≤ r := by
  obtain ⟨r, hr0, hr⟩ := I.env' hn
  refine ⟨r ^ P, ?_⟩
  filter_upwards [hr, I.N0 n hn] with ω hω hN
  rw [abs_of_nonneg (Ff_nonneg P n ω)]
  refine (I.Ff_le P n ω hN).trans (pow_le_pow_left₀ hN ?_ _)
  exact (negMax_le_absMax _ _).trans hω.1

lemma FI.Ff_int [IsProbabilityMeasure μ] (I : FI D μ F T V c J β B lo hi m0) {n : ℕ} (hn : n ≤ T)
    (P : ℕ) (S : Set Ω) (hS : MeasurableSet S) : Integrable (S.indicator (Ff D V c P n)) μ := by
  obtain ⟨r, hr⟩ := I.Ff_bdd hn P
  exact (int_of_ae_bdd (I.Ff_meas hn P).aestronglyMeasurable hr).indicator hS

/-- the shift constant `c = (3β + 2N/B)/(1 − 1/B)` -/
noncomputable def ccf (B β N : ℝ) : ℝ := (3 * β * B + 2 * N) / (B - 1)

lemma ccf_le {B β N : ℝ} (hB : 4 ≤ B) (hβ : 0 ≤ β) (hN : 0 ≤ N) :
    0 ≤ ccf B β N ∧ ccf B β N ≤ 4 * β + 3 * N / B := by
  unfold ccf
  have hB1 : 0 < B - 1 := by linarith
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ hB1]
  have e : (4 * β + 3 * N / B) * (B - 1) = 4 * β * B - 4 * β + 3 * N - 3 * N / B := by
    field_simp; ring
  rw [e]
  have h1 : 3 * N / B ≤ N := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  nlinarith

/-- the step bound for the positive part: `(f + |ξ|)₊ ≤ (f + c)₊` -/
lemma pos_shift_le {B β N f ξ : ℝ} (hB : 4 ≤ B) (hξ : |ξ| ≤ 3 * β + (2 * N - f) / B) :
    max (f + |ξ|) 0 ≤ max (f + ccf B β N) 0 := by
  rcases le_or_gt (f + |ξ|) 0 with h | h
  · rw [max_eq_right h]; exact le_max_right _ _
  · rw [max_eq_left h.le]
    refine le_trans ?_ (le_max_left _ _)
    unfold ccf
    have hB1 : 0 < B - 1 := by linarith
    have hB0 : 0 < B := by linarith
    -- `f + |ξ| ≤ (1 − 1/B)(f + c)`
    have h1 : f + |ξ| ≤ (B - 1) / B * f + (3 * β * B + 2 * N) / B := by
      have e : (B - 1) / B * f + (3 * β * B + 2 * N) / B = f + (3 * β + (2 * N - f) / B) := by
        field_simp; ring
      rw [e]; linarith
    have e2 : (B - 1) / B * f + (3 * β * B + 2 * N) / B =
        (B - 1) / B * (f + (3 * β * B + 2 * N) / (B - 1)) := by
      field_simp
    rw [e2] at h1
    have hpos : 0 < f + (3 * β * B + 2 * N) / (B - 1) := by
      by_contra hc; push_neg at hc
      have : (B - 1) / B * (f + (3 * β * B + 2 * N) / (B - 1)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
      linarith
    have h3 : (B - 1) / B ≤ 1 := by rw [div_le_one hB0]; linarith
    calc f + |ξ| ≤ (B - 1) / B * (f + (3 * β * B + 2 * N) / (B - 1)) := h1
      _ ≤ 1 * (f + (3 * β * B + 2 * N) / (B - 1)) := mul_le_mul_of_nonneg_right h3 hpos.le
      _ = _ := one_mul _

end G26

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma neg_fz (V : ℕ → Ω → (Fin d → ℝ)) (c : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) (u : Fin d → ℝ) :
    -fz V c n ω u = u ⬝ᵥ (-V n ω) + (-c n ω) := by
  unfold fz; rw [dotProduct_neg]; ring

/-- the pathwise bound of the negative recurrence at a fixed history -/
lemma FI.neg_path (I : FI D μ F T V c J β B lo hi m0) {k : ℕ} (hk : 2 ≤ k) (hjP : rdim D ≤ 4 * k)
    (hB : 2 ^ 20 * (4 * k : ℝ) ≤ B) {b βn x : ℝ} (hβ : 1 ≤ βn) (hβb : βn ^ 2 ≤ b ^ 2 * x)
    (hb : 0 ≤ b) (hx : 1 ≤ x) {n : ℕ} (ω : Ω) (hN : 0 ≤ negMax D (V n ω) (c n ω)) :
    ∫ u, ((max (-fz V c n ω u) 0) ^ (4 * k) + 0 +
        ((4 * k : ℝ) * (4 * k - 1) / 2) *
          (max (-fz V c n ω u + ccf B βn (negMax D (V n ω) (c n ω))) 0) ^ (4 * k - 2) *
          (10 * βn + 2 * (fz V c n ω u + 2 * negMax D (V n ω) (c n ω)) ^ 2 / (B * x))) ∂(nvol D) ≤
      (1 + (1 + 1024 * (4 * k : ℝ) ^ 2 / B) / x) * Ff D V c (4 * k) n ω +
        Kneg k b B * x ^ (3 * k - 1) := by
  have := nvol_prob I.hD I.hconv I.hne
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hB0 : 0 < B := by nlinarith
  have hB4 : 4 ≤ B := by nlinarith
  set Q := negMax D (V n ω) (c n ω) with hQ
  set cc := ccf B βn Q with hccdef
  obtain ⟨hcc0, hcc⟩ := ccf_le (β := βn) hB4 (by linarith) hN
  set P : ℕ := 4 * k with hPdef
  set fF := Ff D V c P n ω with hfF
  set Vc := 10 * βn + 2 * (3 * Q + 4 * βn) ^ 2 / (B * x) with hVc
  have hc0 : 0 ≤ ((4 * k : ℝ) * (4 * k - 1) / 2) := by nlinarith
  set f : (Fin d → ℝ) → ℝ := fun u => -fz V c n ω u with hf
  have hfc : Continuous f := (fz_cont V c n ω).neg
  have hfQ : ∀ u ∈ D, f u ≤ Q := fun u hu => negMax_ge I.hD hu _ _
  -- pointwise comparison of the curvature integrand
  have hpt : ∀ u ∈ D, (max (f u + cc) 0) ^ (P - 2) *
      (10 * βn + 2 * (fz V c n ω u + 2 * Q) ^ 2 / (B * x)) ≤ (max (f u + cc) 0) ^ (P - 2) * Vc := by
    intro u hu
    rcases le_or_gt (f u + cc) 0 with h | h
    · rw [max_eq_right h, zero_pow (by omega), zero_mul, zero_mul]
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      have h1 : 0 ≤ fz V c n ω u + 2 * Q := by have := hfQ u hu; simp only [f] at this; linarith
      have h2 : fz V c n ω u + 2 * Q ≤ 3 * Q + 4 * βn := by
        simp only [f] at h
        have : 3 * Q / B ≤ Q := by rw [div_le_iff₀ hB0]; nlinarith
        linarith
      have h3 : (fz V c n ω u + 2 * Q) ^ 2 ≤ (3 * Q + 4 * βn) ^ 2 := pow_le_pow_left₀ h1 h2 2
      simp only [Vc]
      gcongr
  -- the curvature integral
  set I2 := ∫ u, (max (f u + cc) 0) ^ (P - 2) ∂(nvol D) with hI2
  have i0 : Integrable (fun u => (max (f u) 0) ^ P) (nvol D) :=
    cont_bdd_int I.hD ((hfc.max continuous_const).pow _)
  have i2 : Integrable (fun u => (max (f u + cc) 0) ^ (P - 2)) (nvol D) :=
    cont_bdd_int I.hD (((hfc.add continuous_const).max continuous_const).pow _)
  have iL : Integrable (fun u => (max (f u) 0) ^ P + 0 + ((4 * k : ℝ) * (4 * k - 1) / 2) *
      (max (f u + cc) 0) ^ (P - 2) * (10 * βn + 2 * (fz V c n ω u + 2 * Q) ^ 2 / (B * x)))
      (nvol D) := by
    refine cont_bdd_int I.hD ?_
    have := fz_cont V c n ω
    fun_prop
  have hI20 : 0 ≤ I2 := integral_nonneg fun u => by positivity
  have hstep1 : ∫ u, ((max (f u) 0) ^ P + 0 + ((4 * k : ℝ) * (4 * k - 1) / 2) *
      (max (f u + cc) 0) ^ (P - 2) * (10 * βn + 2 * (fz V c n ω u + 2 * Q) ^ 2 / (B * x))) ∂(nvol D) ≤
      fF + ((4 * k : ℝ) * (4 * k - 1) / 2) * (Vc * I2) := by
    have iR : Integrable (fun u => (max (f u) 0) ^ P + ((4 * k : ℝ) * (4 * k - 1) / 2) *
        ((max (f u + cc) 0) ^ (P - 2) * Vc)) (nvol D) :=
      i0.add ((i2.mul_const _).const_mul _)
    calc _ ≤ ∫ u, ((max (f u) 0) ^ P + ((4 * k : ℝ) * (4 * k - 1) / 2) *
          ((max (f u + cc) 0) ^ (P - 2) * Vc)) ∂(nvol D) := by
          refine integral_mono_ae iL iR ?_
          filter_upwards [measure_eq_zero_iff_ae_notMem.1 (nvol_supp I.hD)] with u hu
          simp only [Set.mem_compl_iff, not_not] at hu
          have := mul_le_mul_of_nonneg_left (hpt u hu) hc0
          simp only [add_zero]
          nlinarith [this]
      _ = fF + ((4 * k : ℝ) * (4 * k - 1) / 2) * (Vc * I2) := by
          rw [integral_add i0 ((i2.mul_const _).const_mul _), integral_const_mul,
            integral_mul_const]
          simp only [fF, Ff, f]
          ring
  -- the two branches for `I2`
  obtain ⟨x0, hx0, hx0Q⟩ := negMax_mem I.hD I.hne (V n ω) (c n ω)
  have hA : 16 * ((4 * k : ℝ) + rdim D) * βn ≤ Q → Q ^ 2 * I2 ≤ 64 * fF := by
    intro hbig
    have hQ0 : 0 < Q := by
      have : 0 < 16 * ((4 * k : ℝ) + rdim D) * βn := by positivity
      linarith
    have hx0' : x0 ⬝ᵥ (-V n ω) + (-c n ω) = Q := by rw [← neg_fz]; exact hx0Q
    have hJ := J19 I.hD I.hconv I.hne (-V n ω) (-c n ω) hx0 (by rw [hx0']; exact hQ0)
      (p := P) (by omega) hjP hcc0
    rw [hx0'] at hJ
    have e1 : ∫ x, (max (x ⬝ᵥ -V n ω + -c n ω + cc) 0) ^ (P - 2) ∂(nvol D) = I2 := by
      simp only [I2, f, neg_fz]
    have e2 : ∫ x, (max (x ⬝ᵥ -V n ω + -c n ω) 0) ^ P ∂(nvol D) = fF := by
      simp only [fF, Ff, neg_fz]
    rw [e1, e2] at hJ
    have hexp : (1 + cc / Q) ^ (P - 2 + rdim D) ≤ 2 := by
      apply exp_small _ _ (by positivity)
      have hj' : (rdim D : ℝ) ≤ 4 * k := by exact_mod_cast hjP
      have h1 : cc / Q ≤ 1 / (4 * (4 * k + rdim D)) + 3 / B := by
        rw [div_le_iff₀ hQ0]
        have e : (1 / (4 * (4 * k + rdim D)) + 3 / B) * Q =
            Q / (4 * (4 * k + rdim D)) + 3 * Q / B := by ring
        rw [e]
        have : 4 * βn ≤ Q / (4 * (4 * k + rdim D)) := by
          rw [le_div_iff₀ (by positivity)]; linarith
        linarith
      have hm : ((P - 2 + rdim D : ℕ) : ℝ) ≤ 4 * k + rdim D := by
        push_cast [hPdef, Nat.cast_sub (show 2 ≤ 4 * k by omega)]; linarith
      calc ((P - 2 + rdim D : ℕ) : ℝ) * (cc / Q)
          ≤ (4 * k + rdim D) * (1 / (4 * (4 * k + rdim D)) + 3 / B) :=
            mul_le_mul hm h1 (by positivity) (by positivity)
        _ = 1 / 4 + 3 * (4 * k + rdim D) / B := by field_simp
        _ ≤ 2 / 5 := by
            have : 3 * (4 * k + (rdim D : ℝ)) / B ≤ 1 / 100 := by
              rw [div_le_iff₀ hB0]; nlinarith
            linarith
    have hF0 : 0 ≤ fF := Ff_nonneg _ _ _
    calc Q ^ 2 * I2 ≤ 32 * (1 + cc / Q) ^ (P - 2 + rdim D) * fF := hJ
      _ ≤ 32 * 2 * fF := by gcongr
      _ = 64 * fF := by ring
  have hS : Q < 16 * ((4 * k : ℝ) + rdim D) * βn → I2 ≤ (37 * (4 * k : ℝ) * βn) ^ (4 * k - 2) := by
    intro hsm
    have hj' : (rdim D : ℝ) ≤ 4 * k := by exact_mod_cast hjP
    have hQc : Q + cc ≤ 37 * (4 * k) * βn := by
      have h1 : 3 * Q / B ≤ Q / 1000 := by
        rw [div_le_div_iff₀ hB0 (by norm_num)]; nlinarith
      have h2 : Q < 32 * (4 * k) * βn := by nlinarith
      nlinarith
    calc I2 ≤ ∫ _u, (37 * (4 * k : ℝ) * βn) ^ (4 * k - 2) ∂(nvol D) := by
          refine integral_mono_ae i2 (integrable_const _) ?_
          filter_upwards [measure_eq_zero_iff_ae_notMem.1 (nvol_supp I.hD)] with u hu
          simp only [Set.mem_compl_iff, not_not] at hu
          refine pow_le_pow_left₀ (le_max_right _ _) (max_le ?_ (by positivity)) _
          have := hfQ u hu; linarith
      _ = _ := by simp
  have halg := neg_alg k hk (rdim D) hjP B b βn x fF Q I2 hB hx hβ hβb hb hN
    (Ff_nonneg _ _ _) (I.Ff_le _ n ω hN) hI20 hA hS
  calc _ = ∫ u, ((max (f u) 0) ^ P + 0 + ((4 * k : ℝ) * (4 * k - 1) / 2) *
        (max (f u + cc) 0) ^ (P - 2) * (10 * βn + 2 * (fz V c n ω u + 2 * Q) ^ 2 / (B * x))) ∂(nvol D) := rfl
    _ ≤ fF + ((4 * k : ℝ) * (4 * k - 1) / 2) * (Vc * I2) := hstep1
    _ ≤ _ := halg

end G26

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma ccf_cont (B β : ℝ) : Continuous fun N => ccf B β N := by
  unfold ccf; fun_prop

/-- **one step of the negative integral moment recurrence (G.467)** -/
theorem FI.neg_step [IsProbabilityMeasure μ] (I : FI D μ F T V c J β B lo hi m0) (hlo : 0 ≤ lo)
    {k : ℕ} (hk : 2 ≤ k) (hjP : rdim D ≤ 4 * k) (hB : 2 ^ 20 * (4 * k : ℝ) ≤ B) {b : ℝ}
    (hb : 0 ≤ b) (hβ : ∀ n, 1 ≤ β n) (hβb : ∀ n, β n ^ 2 ≤ b ^ 2 * ((n : ℝ) + 1))
    {n : ℕ} (hm0 : m0 ≤ n) (hn : n < T) :
    ∫ ω, (J (n + 1)).indicator (Ff D V c (4 * k) (n + 1)) ω ∂μ ≤
      (1 + (1 + 1024 * (4 * k : ℝ) ^ 2 / B) / ((n : ℝ) + 1)) *
        ∫ ω, (J n).indicator (Ff D V c (4 * k) n) ω ∂μ +
        Kneg k b B * ((n : ℝ) + 1) ^ (3 * k - 1) := by
  have := nvol_prob I.hD I.hconv I.hne
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hB0 : 0 < B := by nlinarith
  have hB4 : 4 ≤ B := by nlinarith
  set x : ℝ := (n : ℝ) + 1 with hx
  have hx1 : 1 ≤ x := by simp only [x]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hFn := I.Fle n hn.le
  have hJn : MeasurableSet[F n] (J n) := I.Jm n hn.le
  set P : ℕ := 4 * k with hPdef
  have hPc : (P : ℝ) = 4 * k := by simp [hPdef]
  have hc0 : 0 ≤ ((4 * k : ℝ) * (4 * k - 1) / 2) := by nlinarith
  set N : Ω → ℝ := fun ω => negMax D (V n ω) (c n ω) with hNdef
  set cc : Ω → ℝ := fun ω => ccf B (β n) (N ω) with hccdef
  let H : (Fin d → ℝ) → Ω → ℝ := fun u ω => (max (-fz V c (n + 1) ω u) 0) ^ P
  let g0 : (Fin d → ℝ) → Ω → ℝ := fun u ω => (max (-fz V c n ω u) 0) ^ P
  let g1 : (Fin d → ℝ) → Ω → ℝ := fun u ω => -(4 * k : ℝ) * (max (-fz V c n ω u) 0) ^ (P - 1)
  let g2 : (Fin d → ℝ) → Ω → ℝ := fun u ω =>
    ((4 * k : ℝ) * (4 * k - 1) / 2) * (max (-fz V c n ω u + cc ω) 0) ^ (P - 2)
  let ξ : (Fin d → ℝ) → Ω → ℝ := fun u ω => fxi V c n ω u
  let b1 : (Fin d → ℝ) → Ω → ℝ := fun _ _ => 0
  let Vb : (Fin d → ℝ) → Ω → ℝ := fun u ω =>
    10 * β n + 2 * (fz V c n ω u + 2 * N ω) ^ 2 / (B * x)
  -- measurability
  have hNm : Measurable[F n] N := I.negMax_meas hn.le
  have hNm' : Measurable N := hNm.mono hFn le_rfl
  have hccm : Measurable[F n] cc := (ccf_cont B (β n)).measurable.comp hNm
  have hccm' : Measurable cc := hccm.mono hFn le_rfl
  have hzm : ∀ u, Measurable[F n] (fun ω => fz V c n ω u) := fun u => I.fz_meas hn.le u
  have hzj := I.fz_jmeas hn.le
  have hzj1 := I.fz_jmeas (n := n + 1) hn
  have hHj : Measurable (Function.uncurry H) := by
    have h0 : Measurable (fun p : (Fin d → ℝ) × Ω => (max (-fz V c (n + 1) p.2 p.1) 0) ^ P) :=
      (hzj1.neg.max (measurable_const (a := (0 : ℝ)))).pow_const P
    exact h0
  have hRj : Measurable (Function.uncurry fun u ω => g0 u ω + b1 u ω + g2 u ω * Vb u ω) := by
    have h1 : Measurable (fun p : (Fin d → ℝ) × Ω => fz V c n p.2 p.1) := hzj
    have hNj : Measurable (fun p : (Fin d → ℝ) × Ω => N p.2) := hNm'.comp measurable_snd
    have hcj : Measurable (fun p : (Fin d → ℝ) × Ω => cc p.2) := hccm'.comp measurable_snd
    have hφ : Continuous (fun q : ℝ × ℝ × ℝ => (max (-q.1) 0) ^ P + 0 +
        ((4 * k : ℝ) * (4 * k - 1) / 2) * (max (-q.1 + q.2.2) 0) ^ (P - 2) *
          (10 * β n + 2 * (q.1 + 2 * q.2.1) ^ 2 / (B * x))) := by fun_prop
    exact hφ.measurable.comp (h1.prodMk (hNj.prodMk hcj))
  -- envelopes
  obtain ⟨r0, hr00, hr0⟩ := I.env' hn.le
  obtain ⟨r1, hr10, hr1⟩ := I.env' (n := n + 1) hn
  have hβn := hβ n
  set cb : ℝ := r1 ^ P + r0 ^ P + (4 * k : ℝ) * r0 ^ (P - 1) +
    ((4 * k : ℝ) * (4 * k - 1) / 2) * (r0 + (4 * β n + 3 * r0 / B)) ^ (P - 2) + (r1 + r0) +
    (10 * β n + 2 * (3 * r0) ^ 2 / (B * x)) with hcb
  have hbd : ∀ u ∈ D, ∀ᵐ ω ∂μ, |H u ω| ≤ cb ∧ |g0 u ω| ≤ cb ∧ |g1 u ω| ≤ cb ∧ |g2 u ω| ≤ cb ∧
      |ξ u ω| ≤ cb ∧ |b1 u ω| ≤ cb ∧ |Vb u ω| ≤ cb := by
    intro u hu
    filter_upwards [hr0, hr1, I.N0 n hn.le] with ω hω0 hω1 hN0
    obtain ⟨hA0, hz0⟩ := hω0
    have hz1 := hω1.2
    have hz0u := hz0 u hu
    have hz1u := hz1 u hu
    have hNr : N ω ≤ r0 := (negMax_le_absMax _ _).trans hA0
    obtain ⟨hcc0, hcc⟩ := ccf_le (β := β n) hB4 (by linarith) hN0
    have hm0 : max (-fz V c n ω u) 0 ≤ r0 :=
      max_le (by linarith [(abs_le.1 hz0u).1]) hr00
    have hm1 : max (-fz V c (n + 1) ω u) 0 ≤ r1 :=
      max_le (by linarith [(abs_le.1 hz1u).1]) hr10
    have t1 : |H u ω| ≤ r1 ^ P := by
      simp only [H]; rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (le_max_right _ _) hm1 _
    have t2 : |g0 u ω| ≤ r0 ^ P := by
      simp only [g0]; rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (le_max_right _ _) hm0 _
    have t3 : |g1 u ω| ≤ (4 * k : ℝ) * r0 ^ (P - 1) := by
      simp only [g1]
      rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * k),
        abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_max_right _ _) hm0 _) (by positivity)
    have t4 : |g2 u ω| ≤ ((4 * k : ℝ) * (4 * k - 1) / 2) * (r0 + (4 * β n + 3 * r0 / B)) ^ (P - 2) := by
      simp only [g2]
      rw [abs_mul, abs_of_nonneg hc0, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_max_right _ _) ?_ _) hc0
      refine max_le ?_ (by positivity)
      have h3 : 3 * N ω / B ≤ 3 * r0 / B := div_le_div_of_nonneg_right (by linarith) hB0.le
      have : cc ω ≤ 4 * β n + 3 * r0 / B := by simp only [cc]; linarith
      linarith [(abs_le.1 hz0u).1]
    have t5 : |ξ u ω| ≤ r1 + r0 := by
      simp only [ξ, fxi]
      exact le_trans (abs_sub _ _) (add_le_add hz1u hz0u)
    have t6 : |b1 u ω| ≤ 0 := by simp [b1]
    have t7 : |Vb u ω| ≤ 10 * β n + 2 * (3 * r0) ^ 2 / (B * x) := by
      simp only [Vb]
      rw [abs_of_nonneg (by positivity)]
      have h3 := fz_add_negMax_abs I.hD hu (V n ω) (c n ω)
      have h4 : (fz V c n ω u + 2 * N ω) ^ 2 ≤ (3 * r0) ^ 2 := by
        have h5 : |fz V c n ω u + 2 * N ω| ≤ 3 * r0 := h3.trans (by linarith)
        have := sq_le_sq' (abs_le.1 h5).1 (abs_le.1 h5).2
        linarith
      gcongr
    have p1 : 0 ≤ r1 ^ P := by positivity
    have p2 : 0 ≤ r0 ^ P := by positivity
    have p3 : 0 ≤ (4 * k : ℝ) * r0 ^ (P - 1) := by positivity
    have p4 : 0 ≤ ((4 * k : ℝ) * (4 * k - 1) / 2) * (r0 + (4 * β n + 3 * r0 / B)) ^ (P - 2) := by
      positivity
    have p5 : 0 ≤ r1 + r0 := by positivity
    have p7 : 0 ≤ 10 * β n + 2 * (3 * r0) ^ 2 / (B * x) := by positivity
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [cb] <;> linarith
  -- the pointwise expansion
  have hpt : ∀ u ∈ D, ∀ᵐ ω ∂μ, ω ∈ J n →
      H u ω ≤ g0 u ω + g1 u ω * ξ u ω + g2 u ω * ξ u ω ^ 2 := by
    intro u hu
    filter_upwards [I.mag n hm0 hn] with ω hω hJ
    have hm := hω hJ u hu
    have hT := C37.pos_taylor (-fz V c n ω u) (-ξ u ω) P (by omega) ⟨2 * k, by omega⟩
    have hsh : max (-fz V c n ω u + |ξ u ω|) 0 ≤ max (-fz V c n ω u + cc ω) 0 := by
      apply pos_shift_le hB4
      simp only [ξ]
      have e : (fz V c n ω u + 2 * negMax D (V n ω) (c n ω)) = 2 * N ω - -fz V c n ω u := by
        simp only [N]; ring
      rw [← e]; exact hm
    have hpow : (max (-fz V c n ω u + |ξ u ω|) 0) ^ (P - 2) ≤ (max (-fz V c n ω u + cc ω) 0) ^ (P - 2) :=
      pow_le_pow_left₀ (le_max_right _ _) hsh _
    rw [abs_neg, neg_sq] at hT
    have h4 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hc0) (sq_nonneg (ξ u ω))
    rw [hPc] at hT
    simp only [H, g0, g1, g2]
    rw [fz_succ, show -(fz V c n ω u + fxi V c n ω u) = -fz V c n ω u + -ξ u ω by simp [ξ]; ring]
    have e2 : (4 * (k : ℝ)) * (max (-fz V c n ω u) 0) ^ (P - 1) * -ξ u ω =
        -(4 * k : ℝ) * (max (-fz V c n ω u) 0) ^ (P - 1) * ξ u ω := by ring
    rw [e2] at hT
    linarith
  -- drift
  have hdr : ∀ u ∈ D, ∀ᵐ ω ∂μ, ω ∈ J n → g1 u ω * μ[ξ u | F n] ω ≤ b1 u ω := by
    intro u hu
    filter_upwards [I.drift n hm0 hn u hu] with ω hω hJ
    have h1 := (hω hJ).1
    simp only [g1, b1]
    have : 0 ≤ μ[ξ u | F n] ω := by simp only [ξ]; linarith
    have h2 : 0 ≤ (4 * k : ℝ) * (max (-fz V c n ω u) 0) ^ (P - 1) := by positivity
    nlinarith
  -- second moment
  have hse : ∀ u ∈ D, ∀ᵐ ω ∂μ, ω ∈ J n → μ[fun ω => ξ u ω ^ 2 | F n] ω ≤ Vb u ω := by
    intro u hu
    filter_upwards [I.sec n hm0 hn u hu] with ω hω hJ
    simp only [Vb, ξ, N]
    exact hω hJ
  have hg2n : ∀ u ∈ D, ∀ᵐ ω ∂μ, ω ∈ J n → 0 ≤ g2 u ω := fun u _ =>
    ae_of_all _ fun ω _ => by simp only [g2]; positivity
  -- measurability of the coefficients
  have hg1m : ∀ u ∈ D, StronglyMeasurable[F n] (g1 u) := by
    intro u _
    have hφ : Continuous (fun q : ℝ => -(4 * k : ℝ) * (max (-q) 0) ^ (P - 1)) := by fun_prop
    exact (hφ.measurable.comp (hzm u)).stronglyMeasurable
  have hg2m : ∀ u ∈ D, StronglyMeasurable[F n] (g2 u) := by
    intro u _
    have hφ : Continuous (fun q : ℝ × ℝ => ((4 * k : ℝ) * (4 * k - 1) / 2) *
        (max (-q.1 + q.2) 0) ^ (P - 2)) := by fun_prop
    exact (hφ.measurable.comp ((hzm u).prodMk hccm)).stronglyMeasurable
  have hg0m : ∀ u ∈ D, AEStronglyMeasurable (g0 u) μ := fun u _ =>
    ((((hzm u).mono hFn le_rfl).neg.max measurable_const).pow_const _).aestronglyMeasurable
  have hξm : ∀ u ∈ D, AEStronglyMeasurable (ξ u) μ := fun u _ =>
    (((I.fz_meas hn u).mono (I.Fle (n + 1) hn) le_rfl).sub
      ((hzm u).mono hFn le_rfl)).aestronglyMeasurable
  have hb1m : ∀ u ∈ D, AEStronglyMeasurable (b1 u) μ := fun u _ => aestronglyMeasurable_const
  have hVm : ∀ u ∈ D, AEStronglyMeasurable (Vb u) μ := by
    intro u _
    have hφ : Continuous (fun q : ℝ × ℝ => 10 * β n + 2 * (q.1 + 2 * q.2) ^ 2 / (B * x)) := by
      fun_prop
    exact (hφ.measurable.comp (((hzm u).mono hFn le_rfl).prodMk hNm')).aestronglyMeasurable
  have hstep := istep (nvol_supp I.hD) hFn hJn hHj hRj hg0m hg1m hg2m hξm hb1m hVm hbd hpt
    hdr hse hg2n
  -- pathwise bound
  have hpath : ∀ᵐ ω ∂μ, (J n).indicator
      (fun ω => ∫ u, (g0 u ω + b1 u ω + g2 u ω * Vb u ω) ∂(nvol D)) ω ≤
      (J n).indicator (fun ω => (1 + (1 + 1024 * (4 * k : ℝ) ^ 2 / B) / x) * Ff D V c P n ω +
        Kneg k b B * x ^ (3 * k - 1)) ω := by
    filter_upwards [I.N0 n hn.le] with ω hN0
    by_cases hJ : ω ∈ J n
    · rw [Set.indicator_of_mem hJ, Set.indicator_of_mem hJ]
      exact I.neg_path hk hjP hB (hβ n) (hβb n) hb hx1 ω hN0
    · rw [Set.indicator_of_notMem hJ, Set.indicator_of_notMem hJ]
  -- assemble
  have hGi := I.Ff_int hn.le P (J n) (I.Jm' hn.le)
  have hGi1 := I.Ff_int (n := n + 1) hn P (J n) (I.Jm' hn.le)
  have hGi1' := I.Ff_int (n := n + 1) hn P (J (n + 1)) (I.Jm' hn)
  have hRi : Integrable ((J n).indicator (fun ω => (1 + (1 + 1024 * (4 * k : ℝ) ^ 2 / B) / x) *
      Ff D V c P n ω + Kneg k b B * x ^ (3 * k - 1))) μ := by
    have h1 : Integrable (fun ω => (1 + (1 + 1024 * (4 * k : ℝ) ^ 2 / B) / x) * Ff D V c P n ω +
        Kneg k b B * x ^ (3 * k - 1)) μ := by
      obtain ⟨r, hr⟩ := I.Ff_bdd hn.le P
      exact ((int_of_ae_bdd (I.Ff_meas hn.le P).aestronglyMeasurable hr).const_mul _).add
        (integrable_const _)
    exact h1.indicator (I.Jm' hn.le)
  have hK0 : 0 ≤ Kneg k b B := by unfold Kneg; positivity
  calc ∫ ω, (J (n + 1)).indicator (Ff D V c P (n + 1)) ω ∂μ
      ≤ ∫ ω, (J n).indicator (Ff D V c P (n + 1)) ω ∂μ := by
        refine integral_mono hGi1' hGi1 fun ω => ?_
        exact Set.indicator_le_indicator_of_subset (I.Jmono n) (fun ω => Ff_nonneg _ _ ω) ω
    _ = ∫ ω, (J n).indicator (fun ω => ∫ u, H u ω ∂(nvol D)) ω ∂μ := rfl
    _ ≤ ∫ ω, (J n).indicator (fun ω => ∫ u, (g0 u ω + b1 u ω + g2 u ω * Vb u ω) ∂(nvol D)) ω ∂μ :=
        hstep
    _ ≤ ∫ ω, (J n).indicator (fun ω => (1 + (1 + 1024 * (4 * k : ℝ) ^ 2 / B) / x) * Ff D V c P n ω +
          Kneg k b B * x ^ (3 * k - 1)) ω ∂μ := by
        refine integral_mono_of_nonneg ?_ hRi hpath
        filter_upwards [I.N0 n hn.le] with ω hN0
        by_cases hJ : ω ∈ J n
        · rw [Set.indicator_of_mem hJ]
          refine integral_nonneg fun u => ?_
          simp only [g0, b1, g2, Vb]
          have := hβ n
          positivity
        · simp [Set.indicator_of_notMem hJ]
    _ = (1 + (1 + 1024 * (4 * k : ℝ) ^ 2 / B) / x) * ∫ ω, (J n).indicator (Ff D V c P n) ω ∂μ +
          Kneg k b B * x ^ (3 * k - 1) * (μ (J n)).toReal := by
        rw [show (J n).indicator (fun ω => (1 + (1 + 1024 * (4 * k : ℝ) ^ 2 / B) / x) *
            Ff D V c P n ω + Kneg k b B * x ^ (3 * k - 1)) = fun ω =>
              (1 + (1 + 1024 * (4 * k : ℝ) ^ 2 / B) / x) * (J n).indicator (Ff D V c P n) ω +
                (J n).indicator (fun _ => Kneg k b B * x ^ (3 * k - 1)) ω from by
          funext ω; by_cases hJ : ω ∈ J n <;> simp [hJ]]
        rw [integral_add (hGi.const_mul _) ((integrable_const _).indicator (I.Jm' hn.le)),
          integral_const_mul, integral_indicator_const _ (I.Jm' hn.le), smul_eq_mul,
          measureReal_def]
        ring
    _ ≤ _ := by
        have h1 : (μ (J n)).toReal ≤ 1 := by
          rw [← measureReal_def]; exact measureReal_le_one
        have h2 : 0 ≤ Kneg k b B * x ^ (3 * k - 1) := by positivity
        nlinarith

end G26

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma vneg_lt (k : ℕ) (hk : 2 ≤ k) (B : ℝ) (hB : 2 ^ 20 * (4 * k : ℝ) ≤ B) :
    1 + 1024 * (4 * k : ℝ) ^ 2 / B < 3 * k := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hB0 : 0 < B := by nlinarith
  have : 1024 * (4 * k : ℝ) ^ 2 / B ≤ k := by
    rw [div_le_iff₀ hB0]; nlinarith
  linarith

/-- **the negative integral envelope from a start time `m` (G.582)** -/
theorem FI.neg_env [IsProbabilityMeasure μ] (I : FI D μ F T V c J β B lo hi m0) (hlo : 0 ≤ lo)
    {k : ℕ} (hk : 2 ≤ k) (hjP : rdim D ≤ 4 * k) (hB : 2 ^ 20 * (4 * k : ℝ) ≤ B) {b : ℝ}
    (hb : 0 ≤ b) (hβ : ∀ n, 1 ≤ β n) (hβb : ∀ n, β n ^ 2 ≤ b ^ 2 * ((n : ℝ) + 1)) {W : ℕ}
    (hW : 1 + 1024 * (4 * k : ℝ) ^ 2 / B ≤ W) (m : ℕ) (hm : m0 ≤ m) :
    ∀ n, m ≤ n → n ≤ T →
      ∫ ω, (J n).indicator (Ff D V c (4 * k) n) ω ∂μ ≤ Hneg k b B * ((n : ℝ) + 1) ^ (3 * k) +
        (((n : ℝ) + 1) / ((m : ℝ) + 1)) ^ W * ∫ ω, (J m).indicator (Ff D V c (4 * k) m) ω ∂μ := by
  have hv := vneg_lt k hk B hB
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hB0 : 0 < B := by nlinarith
  have hK0 : 0 ≤ Kneg k b B := by unfold Kneg; positivity
  have hv0 : 0 ≤ 1 + 1024 * (4 * k : ℝ) ^ 2 / B := by positivity
  have hH0 : 0 ≤ Hneg k b B := by unfold Hneg; exact div_nonneg hK0 (by linarith)
  intro n hmn hnT
  have hg0 : 0 ≤ ∫ ω, (J m).indicator (Ff D V c (4 * k) m) ω ∂μ :=
    integral_nonneg fun ω => Set.indicator_nonneg (fun ω _ => Ff_nonneg _ _ ω) ω
  refine supersol_from (fun n => ∫ ω, (J n).indicator (Ff D V c (4 * k) n) ω ∂μ) _ (Kneg k b B)
    (Hneg k b B) (3 * k) W (by omega) hv0 hW hH0 ?_ m T hg0 (fun n _ hn => ?_) n hmn hnT
  · have e : Hneg k b B * (3 * k - (1 + 1024 * (4 * k : ℝ) ^ 2 / B)) = Kneg k b B := by
      unfold Hneg; exact div_mul_cancel₀ _ (by linarith)
    push_cast
    nlinarith
  · exact I.neg_step hlo hk hjP hB hb hβ hβb (by omega) hn

end G26


-- ===== Solutions.G26.NegMax =====

/-! ### Negative maxima from integral moments: (J.18) and Hölder -/

open MeasureTheory ProbabilityTheory Set J11

namespace G26

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

end G26

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

/-- pathwise (J.18): `N^{P+j} ≤ 2^P 4^j R^j F` -/
lemma FI.negMax_J18 (I : FI D μ F T V c J β B lo hi m0) {P : ℕ} (hP : 1 ≤ P) (n : ℕ) (ω : Ω)
    (hN : 0 ≤ negMax D (V n ω) (c n ω)) :
    negMax D (V n ω) (c n ω) ^ (P + rdim D) ≤
      2 ^ P * 4 ^ rdim D * absMax D (V n ω) (c n ω) ^ rdim D * Ff D V c P n ω := by
  rcases eq_or_lt_of_le hN with h0 | hpos
  · rw [← h0, zero_pow (by omega)]
    · have : 0 ≤ absMax D (V n ω) (c n ω) := hN.trans (negMax_le_absMax _ _)
      have := Ff_nonneg (D := D) (V := V) (c := c) P n ω
      positivity
  obtain ⟨x0, hx0, hx0Q⟩ := negMax_mem I.hD I.hne (V n ω) (c n ω)
  have hx0' : x0 ⬝ᵥ (-V n ω) + (-c n ω) = negMax D (V n ω) (c n ω) := by
    rw [← neg_fz]; exact hx0Q
  have hmax : ∀ x ∈ D, x ⬝ᵥ (-V n ω) + (-c n ω) ≤ x0 ⬝ᵥ (-V n ω) + (-c n ω) := by
    intro x hx; rw [hx0', ← neg_fz]; exact negMax_ge I.hD hx _ _
  have hR : ∀ x ∈ D, |x ⬝ᵥ (-V n ω) + (-c n ω)| ≤ absMax D (V n ω) (c n ω) := by
    intro x hx; rw [← neg_fz, abs_neg]; exact abs_le_absMax I.hD hx _ _
  have h := J18 I.hD I.hconv I.hne (-V n ω) (-c n ω) hx0 hmax (by rw [hx0']; exact hpos) hR P
  rw [hx0'] at h
  have e : ∫ x, (max (x ⬝ᵥ -V n ω + -c n ω) 0) ^ P ∂(nvol D) = Ff D V c P n ω := by
    simp only [Ff, neg_fz]
  rwa [e] at h

end G26


-- ===== Solutions.G26.Cross =====

/-! ### Block maxima of negative maxima by freezing at the first crossing -/

open MeasureTheory ProbabilityTheory Set J11

namespace G26

variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

lemma FI.crossA_meas (I : FI D μ F T V c J β B lo hi m0) (v : ℕ) (lam : ℝ) :
    ∀ n ≤ T, MeasurableSet[F n] (crossA D V c J v lam n) := by
  intro n hn
  refine (I.Jm n hn).inter ?_
  by_cases h : n < v
  · simp [h]
  · simp only [h, false_or]
    exact measurableSet_le (I.negMax_meas hn) measurable_const

/-- the field frozen at the first crossing still satisfies the interface, without killing -/
lemma FI.cross_FI [IsFiniteMeasure μ] (I : FI D μ F T V c J β B lo hi m0) (hlo : lo ≤ 0)
    (hhi : 0 ≤ hi) (hβ : ∀ n, 0 ≤ β n) (hB : 0 < B) (v : ℕ) (lam : ℝ) :
    FI D μ F T (frz V (crossA D V c J v lam)) (frz c (crossA D V c J v lam)) (fun _ => univ)
      β B lo hi m0 :=
  I.freeze (I.crossA_meas v lam) hlo hhi hβ hB (fun _ _ => MeasurableSet.univ)
    (fun _ => subset_rfl) (fun n ω hω => by
      have h1 : ω ∈ crossA D V c J v lam n := by
        have := hω.1
        simp only [survS, Set.mem_iInter, Finset.mem_range] at this
        exact this n (by omega)
      exact h1.1)

/-- a crossing while alive is recorded by the frozen field at the end of the block -/
lemma cross_frozen (I : FI D μ F T V c J β B lo hi m0) {v N : ℕ} {lam : ℝ} {ω : Ω} {s : ℕ}
    (hvs : v ≤ s) (hsN : s ≤ N) (hJ : ω ∈ J s) (hcr : lam < negMax D (V s ω) (c s ω)) :
    lam < negMax D (frz V (crossA D V c J v lam) N ω) (frz c (crossA D V c J v lam) N ω) := by
  classical
  have hex : ∃ i, ω ∉ crossA D V c J v lam i := ⟨s, fun h => by
    rcases h.2 with h2 | h2
    · omega
    · linarith⟩
  set i := Nat.find hex with hi
  have hfail : ω ∉ crossA D V c J v lam i := Nat.find_spec hex
  have hmin : ∀ j < i, ω ∈ crossA D V c J v lam j := fun j hj => by
    by_contra h; exact Nat.find_min hex hj h
  have his : i ≤ s := Nat.find_min' hex (fun h => by
    rcases h.2 with h2 | h2
    · omega
    · linarith)
  have hJi : ω ∈ J i := by
    have : ∀ a b, a ≤ b → J b ⊆ J a := fun a b hab => by
      induction b, hab using Nat.le_induction with
      | base => exact subset_rfl
      | succ b _ ih => exact (I.Jmono b).trans ih
    exact this i s his hJ
  have hcross : v ≤ i ∧ lam < negMax D (V i ω) (c i ω) := by
    by_contra h
    apply hfail
    refine ⟨hJi, ?_⟩
    simp only [Set.mem_setOf_eq]
    by_cases hv : i < v
    · exact Or.inl hv
    · right; push_neg at h; exact h (by omega)
  have hsurv : i = 0 ∨ ω ∈ survS (crossA D V c J v lam) (i - 1) := by
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · exact Or.inl h0
    · right
      simp only [survS, Set.mem_iInter, Finset.mem_range]
      exact fun j hj => hmin j (by omega)
  rw [frz_stop V _ hsurv hfail N (by omega), frz_stop c _ hsurv hfail N (by omega)]
  exact hcross.2

/-- **splitting the negative maximum**: `P(Q > λ) ≤ P(R > ρ) + 2^P 4^j ρ^j E[F]/λ^{P+j}` -/
lemma FI.negMax_split [IsProbabilityMeasure μ] (I : FI D μ F T V c J β B lo hi m0) {P : ℕ}
    (hP : 1 ≤ P) {N : ℕ} (hN : N ≤ T) {lam ρ : ℝ} (hlam : 0 < lam) (hρ : 0 < ρ) :
    μ.real {ω | lam < negMax D (V N ω) (c N ω)} ≤ μ.real {ω | ρ < absMax D (V N ω) (c N ω)} +
      2 ^ P * 4 ^ rdim D * ρ ^ rdim D / lam ^ (P + rdim D) * ∫ ω, Ff D V c P N ω ∂μ := by
  set j := rdim D
  set k := 2 ^ P * 4 ^ j * ρ ^ j / lam ^ (P + j) with hk
  have hk0 : 0 ≤ k := by positivity
  have hFi : Integrable (Ff D V c P N) μ := by
    have := I.Ff_int hN P univ MeasurableSet.univ
    simpa using this
  have hsub : {ω | lam < negMax D (V N ω) (c N ω)} ⊆
      {ω | ρ < absMax D (V N ω) (c N ω)} ∪ {ω | 1 ≤ k * Ff D V c P N ω} := by
    intro ω hω
    simp only [mem_setOf_eq] at hω
    by_cases hR : ρ < absMax D (V N ω) (c N ω)
    · exact Or.inl hR
    · right
      push Not at hR
      simp only [mem_setOf_eq]
      have hQ0 : 0 ≤ negMax D (V N ω) (c N ω) := hlam.le.trans hω.le
      have h1 := I.negMax_J18 hP N ω hQ0
      have hR0 : 0 ≤ absMax D (V N ω) (c N ω) := hQ0.trans (negMax_le_absMax _ _)
      have h2 : lam ^ (P + j) ≤ negMax D (V N ω) (c N ω) ^ (P + j) :=
        pow_le_pow_left₀ hlam.le hω.le _
      have h3 : absMax D (V N ω) (c N ω) ^ j ≤ ρ ^ j := pow_le_pow_left₀ hR0 hR j
      have hF0 := Ff_nonneg (D := D) (V := V) (c := c) P N ω
      have h4 : lam ^ (P + j) ≤ 2 ^ P * 4 ^ j * ρ ^ j * Ff D V c P N ω := by
        calc lam ^ (P + j) ≤ 2 ^ P * 4 ^ j * absMax D (V N ω) (c N ω) ^ j * Ff D V c P N ω :=
              h2.trans h1
          _ ≤ 2 ^ P * 4 ^ j * ρ ^ j * Ff D V c P N ω := by gcongr
      rw [hk, div_mul_eq_mul_div, le_div_iff₀ (by positivity), one_mul]
      exact h4
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (Filter.Eventually.of_forall fun ω => mul_nonneg hk0 (Ff_nonneg (D := D) (V := V) (c := c) P N ω))
    (hFi.const_mul k) 1
  rw [one_mul, integral_const_mul] at hmark
  calc μ.real {ω | lam < negMax D (V N ω) (c N ω)}
      ≤ μ.real ({ω | ρ < absMax D (V N ω) (c N ω)} ∪ {ω | 1 ≤ k * Ff D V c P N ω}) :=
        measureReal_mono hsub
    _ ≤ μ.real {ω | ρ < absMax D (V N ω) (c N ω)} + μ.real {ω | 1 ≤ k * Ff D V c P N ω} :=
        measureReal_union_le _ _
    _ ≤ _ := by linarith

/-- **block crossing, split form**: a crossing of level `λ` in `[v, N]` while alive is controlled by
the absolute maximum and the negative integral of the field frozen at the first crossing -/
theorem FI.cross_split [IsProbabilityMeasure μ] (I : FI D μ F T V c J β B 0 hi m0)
    (hhi : 0 ≤ hi) (hβ : ∀ n, 0 ≤ β n) (hB : 0 < B) {v N : ℕ} (hN : N ≤ T) {lam ρ : ℝ}
    (hlam : 0 < lam) (hρ : 0 < ρ) {P : ℕ} (hP : 1 ≤ P) :
    μ.real {ω | ∃ s, v ≤ s ∧ s ≤ N ∧ ω ∈ J s ∧ lam < negMax D (V s ω) (c s ω)} ≤
      μ.real {ω | ρ < absMax D (frz V (crossA D V c J v lam) N ω)
        (frz c (crossA D V c J v lam) N ω)} +
      2 ^ P * 4 ^ rdim D * ρ ^ rdim D / lam ^ (P + rdim D) *
        ∫ ω, Ff D (frz V (crossA D V c J v lam)) (frz c (crossA D V c J v lam)) P N ω ∂μ := by
  have I' := I.cross_FI le_rfl hhi hβ hB v lam
  refine le_trans (measureReal_mono ?_) (I'.negMax_split hP hN hlam hρ)
  rintro ω ⟨s, hvs, hsN, hJ, hcr⟩
  exact cross_frozen I hvs hsN hJ hcr

end G26


-- ===== Solutions.G26.RunK =====

/-! ### The loss-difference field on `K` satisfies the field interface (Lemma G.10) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix

namespace G26R

open G26

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}

section

variable (hd : 1 ≤ d) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ) (hspan : Submodule.span ℝ 𝒜 = ⊤)
include hd hℬ hgen hspan

end

end G26R

namespace G26R

open G26

variable {d : ℕ} {𝒜 ℬ : Set (Fin d → ℝ)} {e : ℕ → Fin d → ℚ}
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {T : ℕ} {R : GRun d Ω}

lemma cumEst_succ (n : ℕ) (ω : Ω) : R.cumEst (n + 1) ω = R.cumEst n ω + R.thetaHat n ω := by
  simp [GRun.cumEst, Finset.sum_range_succ]

end G26R


-- ===== Solutions.G26.RunEnv =====

/-! ### Envelopes of the run fields: absolute maxima and block crossings (Lemmas G.15, G.30) -/

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11

namespace G26

variable {d : ℕ} {Ω : Type*}

variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

/-- **crossing envelope**: a crossing of `λ` in `[v, N]` while alive costs the tail of the frozen
absolute maximum plus the negative-integral envelope started at `m` -/
theorem FI.cross_env [IsProbabilityMeasure μ] (I : FI D μ F T V c J β B 0 hi m0) (hhi : 0 ≤ hi)
    {k : ℕ} (hk : 2 ≤ k) (hjP : rdim D ≤ 4 * k) (hB : 2 ^ 20 * (4 * k : ℝ) ≤ B) {b : ℝ}
    (hb : 0 ≤ b) (hβ1 : ∀ n, 1 ≤ β n) (hβb : ∀ n, β n ^ 2 ≤ b ^ 2 * ((n : ℝ) + 1)) {W : ℕ}
    (hW : 1 + 1024 * (4 * k : ℝ) ^ 2 / B ≤ W) {v N m : ℕ} (hm0 : m0 ≤ m) (hmN : m ≤ N)
    (hN : N ≤ T) {lam ρ : ℝ} (hlam : 1 ≤ lam) (hlρ : lam ≤ ρ) {pA F0 : ℝ}
    (hpA : μ.real {ω | ρ < absMax D (frz V (crossA D V c J v lam) N ω)
      (frz c (crossA D V c J v lam) N ω)} ≤ pA)
    (hF0 : ∫ ω, Ff D (frz V (crossA D V c J v lam)) (frz c (crossA D V c J v lam)) (4 * k) m ω ∂μ
      ≤ F0) :
    μ.real {ω | ∃ s, v ≤ s ∧ s ≤ N ∧ ω ∈ J s ∧ lam < negMax D (V s ω) (c s ω)} ≤
      pA + 2 ^ (4 * k) * 4 ^ rdim D * (ρ / lam) ^ rdim D / lam ^ (4 * k) *
        (Hneg k b B * ((N : ℝ) + 1) ^ (3 * k) + (((N : ℝ) + 1) / ((m : ℝ) + 1)) ^ W * F0) := by
  have hB0 : 0 < B := by
    have : (0 : ℝ) < 2 ^ 20 * (4 * k : ℝ) := by
      have : (2 : ℝ) ≤ k := by exact_mod_cast hk
      positivity
    linarith
  have hβ0 : ∀ n, 0 ≤ β n := fun n => le_trans zero_le_one (hβ1 n)
  have hlam0 : 0 < lam := by linarith
  have hρ0 : 0 < ρ := by linarith
  have h1 := I.cross_split hhi hβ0 hB0 (v := v) hN hlam0 hρ0 (P := 4 * k) (by omega)
  have I' := I.cross_FI le_rfl hhi hβ0 hB0 v lam
  have hneg := I'.neg_env le_rfl hk hjP hB hb hβ1 hβb hW m hm0 N hmN hN
  simp only [Set.indicator_univ] at hneg
  set j := rdim D
  have hF : ∫ ω, Ff D (frz V (crossA D V c J v lam)) (frz c (crossA D V c J v lam)) (4 * k) N ω ∂μ
      ≤ Hneg k b B * ((N : ℝ) + 1) ^ (3 * k) + (((N : ℝ) + 1) / ((m : ℝ) + 1)) ^ W * F0 := by
    refine hneg.trans ?_
    gcongr
  have e : 2 ^ (4 * k) * 4 ^ j * ρ ^ j / lam ^ (4 * k + j) =
      2 ^ (4 * k) * 4 ^ j * (ρ / lam) ^ j / lam ^ (4 * k) := by
    rw [div_pow, pow_add]; field_simp
  have hc0 : 0 ≤ 2 ^ (4 * k) * 4 ^ j * (ρ / lam) ^ j / lam ^ (4 * k) := by positivity
  rw [e] at h1
  calc _ ≤ _ := h1
    _ ≤ pA + 2 ^ (4 * k) * 4 ^ j * (ρ / lam) ^ j / lam ^ (4 * k) *
        (Hneg k b B * ((N : ℝ) + 1) ^ (3 * k) + (((N : ℝ) + 1) / ((m : ℝ) + 1)) ^ W * F0) := by
        gcongr

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


theorem _root_.solution : type_of% @G26.FI.cross_env := @G26.FI.cross_env
