-- Prove2me | solution 1 for G26.SI.pos_moment
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:31:24.129086+00:00
-- url     : https://prove2.me/submissions/fdcf8209-9f8b-414a-86ed-cc4882ba4a5c

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

/-- (C.120): the relative positive-power bound, `(1+ε)^{P−2} ≤ 2` -/
lemma pow_taylor_rel (y z ε : ℝ) (P : ℕ) (hP : 2 ≤ P) (hy : 0 < y) (hε : 0 ≤ ε)
    (hz : |z| ≤ ε * y) (hεP : (1 + ε) ^ (P - 2) ≤ 2) :
    (y + z) ^ P ≤ y ^ P + P * y ^ (P - 1) * z + (P : ℝ) * (P - 1) * y ^ (P - 2) * z ^ 2 := by
  have hT := pow_taylor y z P hP
  rw [abs_of_pos hy] at hT
  have h1 : (y + |z|) ^ (P - 2) ≤ 2 * y ^ (P - 2) := by
    calc (y + |z|) ^ (P - 2) ≤ ((1 + ε) * y) ^ (P - 2) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = (1 + ε) ^ (P - 2) * y ^ (P - 2) := mul_pow _ _ _
      _ ≤ 2 * y ^ (P - 2) := mul_le_mul_of_nonneg_right hεP (by positivity)
  have hc0 : (0 : ℝ) ≤ (P : ℝ) * (P - 1) / 2 := by
    have : (2 : ℝ) ≤ P := by exact_mod_cast hP
    nlinarith
  have h2 : ((P : ℝ) * (P - 1) / 2) * (y + |z|) ^ (P - 2) * z ^ 2 ≤
      ((P : ℝ) * (P - 1) / 2) * (2 * y ^ (P - 2)) * z ^ 2 := by gcongr
  linarith

end C37


-- ===== Solutions.C37.Seq =====

/-! # Scalar inequalities: weighted AM–GM tangents, Bernoulli bounds, power tails -/

namespace C37

open Finset

/-- tangent of `y ↦ y^P`: `P c y^{P−1} ≤ (P−1) y^P + c^P` -/
lemma amgm_pos (P : ℕ) (hP : 2 ≤ P) (y c : ℝ) (hy : 0 ≤ y) (hc : 0 ≤ c) :
    (P : ℝ) * c * y ^ (P - 1) ≤ ((P : ℝ) - 1) * y ^ P + c ^ P := by
  rcases eq_or_lt_of_le hy with h0 | hpos
  · subst h0
    rw [zero_pow (by omega), zero_pow (by omega)]; simp; positivity
  · set u := c / y with hu
    have hu0 : 0 ≤ u := by positivity
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ u - 1 by linarith) P
    have e1 : c = u * y := by rw [hu]; field_simp
    rw [e1]
    have hyP : 0 < y ^ P := by positivity
    have e2 : (u * y) ^ P = (1 + (u - 1)) ^ P * y ^ P := by rw [mul_pow]; ring_nf
    have e3 : (P : ℝ) * (u * y) * y ^ (P - 1) = P * u * y ^ P := by
      have : y ^ P = y * y ^ (P - 1) := by rw [← pow_succ']; congr 1; omega
      rw [this]; ring
    rw [e2, e3]
    have := mul_le_mul_of_nonneg_right hb hyP.le
    linarith

/-- `1 + p x/(1+x) ≤ (1 + x)^p` for `p ≥ 0`, `x ≥ 0` -/
lemma rpow_lower (p x : ℝ) (hp : 0 ≤ p) (hx : 0 ≤ x) : 1 + p * x / (1 + x) ≤ (1 + x) ^ p := by
  have h1 : 0 < 1 + x := by linarith
  rcases le_or_gt 1 p with hp1 | hp1
  · have hb := one_add_mul_self_le_rpow_one_add (show (-1 : ℝ) ≤ x by linarith) hp1
    have : p * x / (1 + x) ≤ p * x := by
      rw [div_le_iff₀ h1]; nlinarith [mul_nonneg hp hx]
    linarith
  · set y := 1 / (1 + x) with hy
    have hy0 : 0 < y := by positivity
    have hy1 : y ≤ 1 := by rw [hy, div_le_one h1]; linarith
    have hb := rpow_one_add_le_one_add_mul_self (show (-1 : ℝ) ≤ y - 1 by linarith) hp hp1.le
    have e1 : (1 + x) ^ p = 1 / y ^ p := by
      rw [hy, Real.div_rpow zero_le_one h1.le, Real.one_rpow, one_div_one_div]
    rw [e1]
    have hyp : 0 < y ^ p := Real.rpow_pos_of_pos hy0 p
    have e2 : 1 + (y - 1) = y := by ring
    rw [e2] at hb
    have hv : p * x / (1 + x) = p * (1 - y) := by rw [hy]; field_simp; ring
    rw [hv]
    have hv1 : p * (1 - y) < 1 := by linarith
    rw [le_div_iff₀ hyp]
    have : 0 ≤ p * (1 - y) := mul_nonneg hp (by linarith)
    nlinarith

end C37

namespace C37

/-- binomial lower bound `x^P + P x^{P−1} y ≤ (x + y)^P` -/
lemma add_pow_ge (P : ℕ) (hP : 1 ≤ P) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ P + P * x ^ (P - 1) * y ≤ (x + y) ^ P := by
  rcases eq_or_lt_of_le hx with h0 | hpos
  · subst h0
    rcases Nat.lt_or_ge P 2 with h1 | h2
    · have : P = 1 := by omega
      subst this; simp
    · rw [zero_pow (by omega), zero_pow (by omega)]; simp; positivity
  · have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ y / x by
      have : 0 ≤ y / x := by positivity
      linarith) P
    have e1 : (x + y) ^ P = x ^ P * (1 + y / x) ^ P := by
      rw [← mul_pow]; congr 1; field_simp
    have e2 : x ^ P = x * x ^ (P - 1) := by rw [← pow_succ']; congr 1; omega
    rw [e1]
    have hxP : 0 < x ^ P := by positivity
    have := mul_le_mul_of_nonneg_left hb hxP.le
    have e3 : x ^ P * (1 + P * (y / x)) = x ^ P + P * x ^ (P - 1) * y := by
      rw [e2]; field_simp
    linarith

end C37


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

end G26


-- ===== Solutions.G26.Scalar =====

/-! ### Killed scalar local moments (Lemma G.22 and the local moments of Lemma G.28) -/

open MeasureTheory ProbabilityTheory Set

namespace G26

variable {Ω : Type*}

variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω} {F : ℕ → MeasurableSpace Ω}
  {Y : ℕ → Ω → ℝ} {I : ℕ → Set Ω} {m N : ℕ} {τ β : ℕ → ℝ} {B : ℝ}

lemma SI.Ym' (S : SI μ F Y I m N τ β B) {n : ℕ} (hn : n ≤ N) : Measurable (Y n) :=
  (S.Ym n hn).mono (S.Fle n hn) le_rfl

lemma SI.Im' (S : SI μ F Y I m N τ β B) {n : ℕ} (hn : n ≤ N) : MeasurableSet (I n) :=
  S.Fle n hn _ (S.Im n hn)

lemma exp_small_aux (m : ℕ) (y : ℝ) (hy : 0 ≤ y) (hmy : m * y ≤ 2 / 5) : (1 + y) ^ m ≤ 2 := by
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

lemma SI.kpos_int [IsFiniteMeasure μ] (S : SI μ F Y I m N τ β B) {n : ℕ} (hn : n ≤ N) (P : ℕ) :
    Integrable ((I n).indicator (fun ω => Y n ω ^ P)) μ := by
  obtain ⟨r, hr⟩ := S.env n hn
  refine Integrable.of_bound (((S.Ym' hn).pow_const P).indicator (S.Im' hn)).aestronglyMeasurable
    (|r| ^ P) ?_
  filter_upwards [hr] with ω hω
  rw [Real.norm_eq_abs]
  by_cases h : ω ∈ I n
  · rw [Set.indicator_of_mem h, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hω.trans (le_abs_self _)) _
  · rw [Set.indicator_of_notMem h, abs_zero]; positivity

/-- **one step of the killed positive moment recursion (G.610)** -/
lemma SI.pos_step [IsProbabilityMeasure μ] (S : SI μ F Y I m N τ β B) {P : ℕ} (hP : 2 ≤ P)
    (hPB : 8 * (P : ℝ) ≤ B) {Dh : ℝ} (hDh : 0 ≤ Dh) {n : ℕ} (hmn : m ≤ n) (hnN : n < N)
    (hdr : ∀ᵐ ω ∂μ, ω ∈ I n → μ[fun ω => Y (n + 1) ω - Y n ω | F n] ω ≤ Dh) (hβ : 0 ≤ β n) :
    kpos μ Y I P (n + 1) ≤
      ∫ ω, (I n).indicator (fun ω => (1 + 2 * P * (P - 1) / (B * ((n : ℝ) + 1))) * Y n ω ^ P +
        P * (Dh + 10 * (P - 1) * β n / τ n) * Y n ω ^ (P - 1)) ω ∂μ := by
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hB0 : 0 < B := by linarith
  have hτ := S.τpos n
  set x : ℝ := (n : ℝ) + 1 with hx
  have hx1 : 1 ≤ x := by simp only [x]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hFn := S.Fle n hnN.le
  have hJ := S.Im n hnN.le
  have hJm := S.Im' hnN.le
  have hYm := S.Ym n hnN.le
  have hYm' := S.Ym' hnN.le
  have hYm1' := S.Ym' (n := n + 1) hnN
  obtain ⟨r0, hr0⟩ := S.env n hnN.le
  obtain ⟨r1, hr1⟩ := S.env (n + 1) hnN
  have hc1 : (0 : ℝ) ≤ P * (P - 1) := by nlinarith
  let H : Ω → ℝ := (I n).indicator (fun ω => Y (n + 1) ω ^ P)
  let g0 : Ω → ℝ := (I n).indicator (fun ω => Y n ω ^ P)
  let g1 : Ω → ℝ := (I n).indicator (fun ω => (P : ℝ) * Y n ω ^ (P - 1))
  let g2 : Ω → ℝ := (I n).indicator (fun ω => (P : ℝ) * (P - 1) * Y n ω ^ (P - 2))
  let ξ : Ω → ℝ := fun ω => Y (n + 1) ω - Y n ω
  let b1 : Ω → ℝ := (I n).indicator (fun ω => (P : ℝ) * Y n ω ^ (P - 1) * Dh)
  let V : Ω → ℝ := fun ω => 10 * β n + 2 * Y n ω ^ 2 / (B * x)
  set R := |r0| + |r1| + 1 with hR
  have hR1 : 1 ≤ R := by have := abs_nonneg r0; have := abs_nonneg r1; linarith
  set cb : ℝ := R ^ P + R ^ P + P * R ^ P + P * (P - 1) * R ^ P + 2 * R + P * R ^ P * Dh +
    (10 * β n + 2 * R ^ 2 / (B * x)) with hcb
  have hfacts : ∀ᵐ ω ∂μ, ω ∈ I n → τ n ≤ Y n ω ∧ |ξ ω| ≤ 3 / B * Y n ω := by
    filter_upwards [S.low n hmn hnN.le, S.mag n hmn hnN] with ω h1 h2 hI
    exact ⟨h1 hI, by simp only [ξ]; rw [show 3 / B * Y n ω = 3 * Y n ω / B by ring]; exact h2 hI⟩
  have hbd : ∀ᵐ ω ∂μ, |H ω| ≤ cb ∧ |g0 ω| ≤ cb ∧ |g1 ω| ≤ cb ∧ |g2 ω| ≤ cb ∧ |ξ ω| ≤ cb ∧
      |b1 ω| ≤ cb ∧ |V ω| ≤ cb := by
    filter_upwards [hr0, hr1] with ω h0 h1
    have a0 : |Y n ω| ≤ R := by have := abs_nonneg r1; linarith [le_abs_self r0]
    have a1 : |Y (n + 1) ω| ≤ R := by have := abs_nonneg r0; linarith [le_abs_self r1]
    have hpow : ∀ k ≤ P, |Y n ω| ^ k ≤ R ^ P := fun k hk =>
      (pow_le_pow_left₀ (abs_nonneg _) a0 k).trans (pow_le_pow_right₀ hR1 hk)
    have q1 : 0 ≤ R ^ P := by positivity
    have q2 : 0 ≤ (P : ℝ) * R ^ P := by positivity
    have q3 : 0 ≤ (P : ℝ) * (P - 1) * R ^ P := by positivity
    have q4 : 0 ≤ (P : ℝ) * R ^ P * Dh := by positivity
    have q5 : 0 ≤ 10 * β n + 2 * R ^ 2 / (B * x) := by positivity
    have tV : |V ω| ≤ 10 * β n + 2 * R ^ 2 / (B * x) := by
      simp only [V]; rw [abs_of_nonneg (by positivity)]
      have : Y n ω ^ 2 ≤ R ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) a0 2
      gcongr
    have tξ : |ξ ω| ≤ 2 * R := by
      simp only [ξ]; linarith [abs_sub (Y (n + 1) ω) (Y n ω)]
    by_cases hI : ω ∈ I n
    · simp only [H, g0, g1, g2, b1, Set.indicator_of_mem hI]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [abs_pow]
        have := (pow_le_pow_left₀ (abs_nonneg _) a1 P); simp only [cb]; linarith
      · rw [abs_pow]; have := hpow P le_rfl; simp only [cb]; linarith
      · rw [abs_mul, Nat.abs_cast, abs_pow]
        have := mul_le_mul_of_nonneg_left (hpow (P - 1) (by omega)) (Nat.cast_nonneg P)
        simp only [cb]; linarith
      · rw [abs_mul, abs_of_nonneg hc1, abs_pow]
        have := mul_le_mul_of_nonneg_left (hpow (P - 2) (by omega)) hc1
        simp only [cb]; linarith
      · simp only [cb]; linarith
      · rw [abs_mul, abs_mul, Nat.abs_cast, abs_pow, abs_of_nonneg hDh]
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpow (P - 1) (by omega))
          (Nat.cast_nonneg P)) hDh
        simp only [cb]; linarith
      · simp only [cb]; linarith
    · simp only [H, g0, g1, g2, b1, Set.indicator_of_notMem hI, abs_zero]
      have : 0 ≤ 2 * R := by linarith
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [cb] <;> linarith
  have hexp : (1 + 3 / B) ^ (P - 2) ≤ 2 := by
    apply exp_small_aux _ _ (by positivity)
    have hP2 : ((P - 2 : ℕ) : ℝ) ≤ P := by rw [Nat.cast_sub hP]; linarith
    rw [mul_div_assoc', div_le_iff₀ hB0]; nlinarith
  have hpt : ∀ᵐ ω ∂μ, ω ∈ I n → H ω ≤ g0 ω + g1 ω * ξ ω + g2 ω * ξ ω ^ 2 := by
    filter_upwards [hfacts] with ω hf hI
    obtain ⟨hy, hξ⟩ := hf hI
    have hY0 : 0 < Y n ω := lt_of_lt_of_le hτ hy
    have hT := C37.pow_taylor_rel (Y n ω) (ξ ω) (3 / B) P hP hY0 (by positivity) hξ hexp
    simp only [H, g0, g1, g2, Set.indicator_of_mem hI]
    have e1 : Y (n + 1) ω = Y n ω + ξ ω := by simp only [ξ]; ring
    rw [e1]; linarith
  have hdr' : ∀ᵐ ω ∂μ, ω ∈ I n → g1 ω * μ[ξ | F n] ω ≤ b1 ω := by
    filter_upwards [hdr, hfacts] with ω h hf hI
    have hY0 : 0 < Y n ω := lt_of_lt_of_le hτ (hf hI).1
    simp only [g1, b1, Set.indicator_of_mem hI]
    exact mul_le_mul_of_nonneg_left (h hI) (by positivity)
  have hse : ∀ᵐ ω ∂μ, ω ∈ I n → μ[fun ω => ξ ω ^ 2 | F n] ω ≤ V ω := by
    filter_upwards [S.sec n hmn hnN] with ω h hI
    exact h hI
  have hg2n : ∀ᵐ ω ∂μ, ω ∈ I n → 0 ≤ g2 ω := by
    filter_upwards [hfacts] with ω hf hI
    have hY0 : 0 < Y n ω := lt_of_lt_of_le hτ (hf hI).1
    simp only [g2, Set.indicator_of_mem hI]; positivity
  have hst := pstep (μ := μ) (F := F) (n := n) hFn hJ (H := H) (g0 := g0) (g1 := g1) (g2 := g2)
    (ξ := ξ) (b1 := b1) (V := V)
    (((hYm1'.pow_const P).indicator hJm).aestronglyMeasurable)
    (((hYm'.pow_const P).indicator hJm).aestronglyMeasurable)
    (((hYm.pow_const _).const_mul _).indicator hJ).stronglyMeasurable
    (((hYm.pow_const _).const_mul _).indicator hJ).stronglyMeasurable
    ((hYm1'.sub hYm').aestronglyMeasurable)
    ((((hYm'.pow_const _).const_mul _).mul_const _).indicator hJm).aestronglyMeasurable
    ((measurable_const.add ((measurable_const.mul (hYm'.pow_const 2)).div_const _)).aestronglyMeasurable)
    hbd hpt hdr' hse hg2n
  have hL : kpos μ Y I P (n + 1) ≤ ∫ ω, (I n).indicator H ω ∂μ := by
    have hLi := S.kpos_int (n := n + 1) hnN P
    have hHi : Integrable ((I n).indicator H) μ :=
      (Integrable.of_bound (((hYm1'.pow_const P).indicator hJm).aestronglyMeasurable) cb
        (by filter_upwards [hbd] with ω h; rw [Real.norm_eq_abs]; exact h.1)).indicator hJm
    refine integral_mono_ae hLi hHi ?_
    filter_upwards [hfacts, S.mag n hmn hnN] with ω hf hm
    by_cases h1 : ω ∈ I (n + 1)
    · have hI := S.Imono n h1
      simp only [H, Set.indicator_of_mem h1, Set.indicator_of_mem hI, le_refl]
    · rw [Set.indicator_of_notMem h1]
      by_cases hI : ω ∈ I n
      · obtain ⟨hy, hξ⟩ := hf hI
        have hY0 : 0 < Y n ω := lt_of_lt_of_le hτ hy
        have : 0 < Y (n + 1) ω := by
          have h3 : 3 * Y n ω / B ≤ Y n ω / 2 := by
            rw [div_le_div_iff₀ hB0 (by norm_num)]; nlinarith
          have := (abs_le.1 (hm hI)).1
          linarith
        simp only [H, Set.indicator_of_mem hI]; positivity
      · simp [H, Set.indicator_of_notMem hI]
  have hRle : ∫ ω, (I n).indicator (fun ω => g0 ω + b1 ω + g2 ω * V ω) ω ∂μ ≤
      ∫ ω, (I n).indicator (fun ω => (1 + 2 * P * (P - 1) / (B * x)) * Y n ω ^ P +
        P * (Dh + 10 * (P - 1) * β n / τ n) * Y n ω ^ (P - 1)) ω ∂μ := by
    have hRi : Integrable ((I n).indicator (fun ω => g0 ω + b1 ω + g2 ω * V ω)) μ := by
      refine Integrable.of_bound ?_ (cb + cb + cb * cb) ?_
      · exact (((((hYm'.pow_const P).indicator hJm).add
          ((((hYm'.pow_const _).const_mul _).mul_const _).indicator hJm)).add
          ((((hYm'.pow_const _).const_mul _).indicator hJm).mul
            (measurable_const.add ((measurable_const.mul (hYm'.pow_const 2)).div_const _)))).indicator
              hJm).aestronglyMeasurable
      · filter_upwards [hbd] with ω h
        obtain ⟨-, h0, -, h2, -, hb, hV⟩ := h
        rw [Real.norm_eq_abs]
        by_cases hI : ω ∈ I n
        · rw [Set.indicator_of_mem hI]
          calc |g0 ω + b1 ω + g2 ω * V ω| ≤ |g0 ω| + |b1 ω| + |g2 ω| * |V ω| := by
                rw [← abs_mul]
                exact le_trans (abs_add_le _ _) (add_le_add (abs_add_le _ _) le_rfl)
            _ ≤ cb + cb + cb * cb := by
                have hc0 := le_trans (abs_nonneg _) h0
                have := mul_le_mul h2 hV (abs_nonneg _) hc0
                linarith
        · rw [Set.indicator_of_notMem hI, abs_zero]
          have := le_trans (abs_nonneg _) h0
          positivity
    have hRi2 : Integrable ((I n).indicator (fun ω => (1 + 2 * P * (P - 1) / (B * x)) * Y n ω ^ P +
        P * (Dh + 10 * (P - 1) * β n / τ n) * Y n ω ^ (P - 1))) μ := by
      have h1 := S.kpos_int hnN.le P
      have h2 := S.kpos_int hnN.le (P - 1)
      have e : (I n).indicator (fun ω => (1 + 2 * P * (P - 1) / (B * x)) * Y n ω ^ P +
          P * (Dh + 10 * (P - 1) * β n / τ n) * Y n ω ^ (P - 1)) = fun ω =>
          (1 + 2 * P * (P - 1) / (B * x)) * (I n).indicator (fun ω => Y n ω ^ P) ω +
            P * (Dh + 10 * (P - 1) * β n / τ n) * (I n).indicator (fun ω => Y n ω ^ (P - 1)) ω := by
        funext ω; by_cases hI : ω ∈ I n <;> simp [hI]
      rw [e]; exact (h1.const_mul _).add (h2.const_mul _)
    refine integral_mono_ae hRi hRi2 ?_
    filter_upwards [hfacts] with ω hf
    by_cases hI : ω ∈ I n
    · obtain ⟨hy, -⟩ := hf hI
      have hY0 : 0 < Y n ω := lt_of_lt_of_le hτ hy
      simp only [g0, b1, g2, V, Set.indicator_of_mem hI]
      have h1 : Y n ω ^ (P - 2) * τ n ≤ Y n ω ^ (P - 1) := by
        have e : Y n ω ^ (P - 1) = Y n ω ^ (P - 2) * Y n ω := by rw [← pow_succ]; congr 1; omega
        rw [e]; exact mul_le_mul_of_nonneg_left hy (by positivity)
      have h2 : (P : ℝ) * (P - 1) * Y n ω ^ (P - 2) * (10 * β n) ≤
          P * (10 * (P - 1) * β n / τ n) * Y n ω ^ (P - 1) := by
        have e : (P : ℝ) * (10 * (P - 1) * β n / τ n) * Y n ω ^ (P - 1) =
            (P : ℝ) * (P - 1) * (10 * β n) * (Y n ω ^ (P - 1) / τ n) := by ring
        rw [e]
        have : Y n ω ^ (P - 2) ≤ Y n ω ^ (P - 1) / τ n := by rw [le_div_iff₀ hτ]; exact h1
        have hc : 0 ≤ (P : ℝ) * (P - 1) * (10 * β n) := by positivity
        nlinarith
      have h3 : (P : ℝ) * (P - 1) * Y n ω ^ (P - 2) * (2 * Y n ω ^ 2 / (B * x)) =
          2 * P * (P - 1) / (B * x) * Y n ω ^ P := by
        have e : Y n ω ^ (P - 2) * Y n ω ^ 2 = Y n ω ^ P := by rw [← pow_add]; congr 1; omega
        rw [← e]; field_simp
      have e4 : (P : ℝ) * (P - 1) * Y n ω ^ (P - 2) * (10 * β n + 2 * Y n ω ^ 2 / (B * x)) =
          (P : ℝ) * (P - 1) * Y n ω ^ (P - 2) * (10 * β n) +
            (P : ℝ) * (P - 1) * Y n ω ^ (P - 2) * (2 * Y n ω ^ 2 / (B * x)) := by ring
      rw [e4, h3]
      have e5 : (P : ℝ) * (Dh + 10 * (P - 1) * β n / τ n) * Y n ω ^ (P - 1) =
          P * Y n ω ^ (P - 1) * Dh + P * (10 * (P - 1) * β n / τ n) * Y n ω ^ (P - 1) := by ring
      rw [e5]
      linarith
    · simp [g0, b1, g2, Set.indicator_of_notMem hI]
  exact hL.trans (hst.trans hRle)

set_option maxHeartbeats 1000000 in
/-- **the killed positive local moment (G.612)**, with `k₀ = 2(P−1)/B`:
`E[1_{I_t} Y_t^P] ≤ (A(t+1)/(1−k₀) + w₀((t+1)/(m+1))^{2k₀})^P` -/
theorem SI.pos_moment [IsProbabilityMeasure μ] (S : SI μ F Y I m N τ β B) {P : ℕ} (hP : 2 ≤ P)
    (hPB : 8 * (P : ℝ) ≤ B) {t : ℕ} (hmt : m ≤ t) (htN : t ≤ N) {A : ℝ} (hA0 : 0 ≤ A)
    (Dh : ℕ → ℝ) (hDh : ∀ s, 0 ≤ Dh s)
    (hdr : ∀ n, m ≤ n → n < t → ∀ᵐ ω ∂μ, ω ∈ I n → μ[fun ω => Y (n + 1) ω - Y n ω | F n] ω ≤ Dh n)
    (hA : ∀ s, m ≤ s → s < t → Dh s + 10 * ((P : ℝ) - 1) * β s / τ s ≤ A)
    (hβ : ∀ n, 0 ≤ β n) {w0 : ℝ} (hw0 : 0 < w0) (hW0 : kpos μ Y I P m ≤ w0 ^ P) :
    kpos μ Y I P t ≤ (A * ((t : ℝ) + 1) / (1 - 2 * ((P : ℝ) - 1) / B) +
      w0 * (((t : ℝ) + 1) / ((m : ℝ) + 1)) ^ (2 * (2 * ((P : ℝ) - 1) / B))) ^ P := by
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hB0 : 0 < B := by linarith
  set k0 := 2 * ((P : ℝ) - 1) / B with hk0def
  have hk0 : 0 ≤ k0 := by rw [hk0def]; apply div_nonneg _ hB0.le; linarith
  have hk1 : k0 ≤ 1 / 4 := by
    rw [hk0def, div_le_div_iff₀ hB0 (by norm_num)]; linarith
  have hk0' : 0 < 1 - k0 := by linarith
  have hnm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  let W : ℕ → ℝ := fun s => kpos μ Y I P s
  let φ : ℕ → ℝ := fun s => A * ((s : ℝ) + 1) / (1 - k0) + w0 * (((s : ℝ) + 1) / ((m : ℝ) + 1)) ^ (2 * k0)
  have claim : ∀ k, m + k ≤ t → ∃ c, 0 < c ∧ c ≤ φ (m + k) ∧ W (m + k) ≤ c ^ P := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨w0, hw0, ?_, by simpa using hW0⟩
      simp only [φ, add_zero]
      rw [div_self hnm.ne', Real.one_rpow, mul_one]
      have : 0 ≤ A * ((m : ℝ) + 1) / (1 - k0) := by positivity
      linarith
    | succ k ih =>
      intro hk
      obtain ⟨c, hc0, hc1, hc2⟩ := ih (by omega)
      set s := m + k with hs
      have hsN : s < N := by omega
      set n : ℝ := (s : ℝ) + 1 with hn
      have hn1 : (1 : ℝ) ≤ n := by simp only [n]; linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
      have hnpos : 0 < n := by linarith
      have hstep := S.pos_step hP hPB (hDh s) (n := s) (by omega) hsN (hdr s (by omega) (by omega))
        (hβ s)
      have hAs := hA s (by omega) (by omega)
      -- pointwise bound
      have hpt : ∀ᵐ ω ∂μ, (I s).indicator (fun ω => (1 + 2 * P * (P - 1) / (B * ((s : ℝ) + 1))) *
          Y s ω ^ P + P * (Dh s + 10 * (P - 1) * β s / τ s) * Y s ω ^ (P - 1)) ω ≤
          (1 + P * k0 / n + A / c * (P - 1)) * (I s).indicator (fun ω => Y s ω ^ P) ω +
            A / c * c ^ P := by
        filter_upwards [S.low s (by omega) hsN.le] with ω hlow
        by_cases hI : ω ∈ I s
        · rw [Set.indicator_of_mem hI, Set.indicator_of_mem hI]
          set y := Y s ω with hy
          have hy0 : 0 ≤ y := le_trans (S.τpos s).le (hlow hI)
          have hyp : 0 ≤ y ^ (P - 1) := pow_nonneg hy0 _
          have h1 : P * (Dh s + 10 * (P - 1) * β s / τ s) * y ^ (P - 1) ≤ P * A * y ^ (P - 1) := by
            apply mul_le_mul_of_nonneg_right _ hyp
            exact mul_le_mul_of_nonneg_left hAs (by positivity)
          have h2 := C37.amgm_pos P hP y c hy0 hc0.le
          have h3 : P * A * y ^ (P - 1) ≤ A / c * ((P - 1) * y ^ P + c ^ P) := by
            have e : P * A * y ^ (P - 1) = A / c * (P * c * y ^ (P - 1)) := by field_simp
            rw [e]
            exact mul_le_mul_of_nonneg_left h2 (by positivity)
          have e2 : 2 * (P : ℝ) * (P - 1) / (B * ((s : ℝ) + 1)) = P * k0 / n := by
            rw [hk0def, hn]; field_simp
          rw [e2]
          have : 0 ≤ (P : ℝ) * k0 / n * y ^ P := by positivity
          nlinarith
        · rw [Set.indicator_of_notMem hI, Set.indicator_of_notMem hI, mul_zero, zero_add]
          positivity
      have iL : Integrable ((I s).indicator (fun ω => (1 + 2 * P * (P - 1) / (B * ((s : ℝ) + 1))) *
          Y s ω ^ P + P * (Dh s + 10 * (P - 1) * β s / τ s) * Y s ω ^ (P - 1))) μ := by
        have h1 := S.kpos_int hsN.le P
        have h2 := S.kpos_int hsN.le (P - 1)
        have e : (I s).indicator (fun ω => (1 + 2 * P * (P - 1) / (B * ((s : ℝ) + 1))) *
            Y s ω ^ P + P * (Dh s + 10 * (P - 1) * β s / τ s) * Y s ω ^ (P - 1)) = fun ω =>
            (1 + 2 * P * (P - 1) / (B * ((s : ℝ) + 1))) * (I s).indicator (fun ω => Y s ω ^ P) ω +
              P * (Dh s + 10 * (P - 1) * β s / τ s) * (I s).indicator (fun ω => Y s ω ^ (P - 1)) ω := by
          funext ω; by_cases hI : ω ∈ I s <;> simp [hI]
        rw [e]; exact (h1.const_mul _).add (h2.const_mul _)
      have iR : Integrable (fun ω => (1 + P * k0 / n + A / c * (P - 1)) *
          (I s).indicator (fun ω => Y s ω ^ P) ω + A / c * c ^ P) μ :=
        ((S.kpos_int hsN.le P).const_mul _).add (integrable_const _)
      have hint := integral_mono_ae iL iR hpt
      rw [integral_add ((S.kpos_int hsN.le P).const_mul _) (integrable_const _),
        integral_const_mul, integral_const] at hint
      simp only [probReal_univ, one_smul, smul_eq_mul, one_mul] at hint
      have hW1 : W (s + 1) ≤ (1 + P * k0 / n + A / c * (P - 1)) * W s + A / c * c ^ P :=
        hstep.trans hint
      set c' := (1 + k0 / n) * c + A with hc'
      refine ⟨c', by positivity, ?_, ?_⟩
      · have hcast : ((m + (k + 1) : ℕ) : ℝ) + 1 = n + 1 := by simp only [n, hs]; push_cast; ring
        have hcast0 : ((m + k : ℕ) : ℝ) + 1 = n := by simp only [n, hs]
        simp only [φ] at hc1 ⊢
        rw [hcast]
        rw [hcast0] at hc1
        have h1 : c' ≤ (1 + k0 / n) * (A * n / (1 - k0) + w0 * (n / ((m : ℝ) + 1)) ^ (2 * k0)) + A := by
          rw [hc']; linarith [mul_le_mul_of_nonneg_left hc1 (by positivity : (0 : ℝ) ≤ 1 + k0 / n)]
        have h2 : (1 + k0 / n) * (A * n / (1 - k0)) + A = A * (n + 1) / (1 - k0) := by
          field_simp; ring
        have h3 : (1 + k0 / n) * (n / ((m : ℝ) + 1)) ^ (2 * k0) ≤ ((n + 1) / ((m : ℝ) + 1)) ^ (2 * k0) := by
          have e : (n + 1) / ((m : ℝ) + 1) = (n / ((m : ℝ) + 1)) * (1 + 1 / n) := by field_simp
          rw [e, Real.mul_rpow (by positivity) (by positivity)]
          rw [mul_comm]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hl := C37.rpow_lower (2 * k0) (1 / n) (by positivity) (by positivity)
          have e2 : 2 * k0 * (1 / n) / (1 + 1 / n) = 2 * k0 / (n + 1) := by field_simp
          rw [e2] at hl
          have h4 : k0 / n ≤ 2 * k0 / (n + 1) := by
            rw [div_le_div_iff₀ hnpos (by linarith)]
            have := mul_nonneg hk0 (by linarith : (0 : ℝ) ≤ n - 1)
            linarith
          linarith
        have h5 := mul_le_mul_of_nonneg_left h3 hw0.le
        linarith
      · have hW2 : W (s + 1) ≤ (1 + P * k0 / n) * c ^ P + P * A * c ^ (P - 1) := by
          have hP1 : (0 : ℝ) ≤ (P : ℝ) - 1 := by linarith
          have hq1 : 0 ≤ (P : ℝ) * k0 / n := div_nonneg (mul_nonneg (by positivity) hk0) hnpos.le
          have hq2 : 0 ≤ A / c * ((P : ℝ) - 1) := mul_nonneg (div_nonneg hA0 hc0.le) hP1
          have h1 := mul_le_mul_of_nonneg_left hc2 (by linarith : (0 : ℝ) ≤ 1 + P * k0 / n + A / c * (P - 1))
          have e : (1 + P * k0 / n + A / c * (P - 1)) * c ^ P + A / c * c ^ P =
              (1 + P * k0 / n) * c ^ P + P * A * c ^ (P - 1) := by
            have : c ^ P = c * c ^ (P - 1) := by rw [← pow_succ']; congr 1; omega
            rw [this]; field_simp; ring
          linarith
        set x := (1 + k0 / n) * c with hx
        have hxc : c ≤ x := by
          rw [hx]; have : 0 ≤ k0 / n * c := by positivity
          linarith
        have hb := C37.add_pow_ge P (by omega) x A (by positivity) hA0
        have hxP : (1 + P * k0 / n) * c ^ P ≤ x ^ P := by
          rw [hx, mul_pow]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have := one_add_mul_le_pow (show (-2 : ℝ) ≤ k0 / n by
            have : 0 ≤ k0 / n := by positivity
            linarith) P
          have e : (P : ℝ) * (k0 / n) = P * k0 / n := by ring
          linarith
        have hxP1 : P * A * c ^ (P - 1) ≤ P * x ^ (P - 1) * A := by
          have := pow_le_pow_left₀ hc0.le hxc (P - 1)
          linarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ P * A)]
        show W (s + 1) ≤ c' ^ P
        rw [hc']
        linarith
  obtain ⟨c, hc0, hc1, hc2⟩ := claim (t - m) (by omega)
  have ht' : m + (t - m) = t := by omega
  rw [ht'] at hc1 hc2
  exact hc2.trans (pow_le_pow_left₀ hc0.le hc1 _)

end G26


theorem _root_.solution : type_of% @G26.SI.pos_moment := @G26.SI.pos_moment
