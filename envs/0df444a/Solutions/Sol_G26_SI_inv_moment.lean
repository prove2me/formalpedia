-- Prove2me | solution 1 for G26.SI.inv_moment
-- status  : ACCEPTED   (prove)
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:31:02.477914+00:00
-- url     : https://prove2.me/submissions/e0b376cb-f19e-49b2-bde0-b0414b65543b

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

/-- (C.202a): the inverse-power bound for small relative increments, `Pε ≤ 1/2` -/
lemma inv_pow_taylor (y z ε : ℝ) (P : ℕ) (hP : 2 ≤ P) (hy : 0 < y) (hε : 0 ≤ ε)
    (hz : |z| ≤ ε * y) (hεP : (P : ℝ) * ε ≤ 1 / 2) :
    1 / (y + z) ^ P ≤ 1 / y ^ P - P * z / y ^ (P + 1) + (P : ℝ) * (P + 1) * z ^ 2 / y ^ (P + 2) := by
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hε1 : ε ≤ 1 / 4 := by nlinarith
  have hzy : z ≥ -(ε * y) := by have := neg_abs_le z; linarith
  have hyz : 0 < y + z := by nlinarith
  set x := z / y with hx
  have hxa : |x| ≤ ε := by rw [hx, abs_div, abs_of_pos hy, div_le_iff₀ hy]; exact hz
  have hx1 : 0 < 1 + x := by
    have := neg_abs_le x; linarith
  set w := -x / (1 + x) with hw
  -- `(y/(y+z))^P = (1 + w)^P`
  have hq : y / (y + z) = 1 + w := by
    rw [hw, hx]; field_simp; ring
  have hT := pow_taylor 1 w P hP
  simp only [one_pow, mul_one, abs_one] at hT
  -- bounds on `w`
  have hxle : 1 - ε ≤ 1 + x := by have := neg_abs_le x; linarith
  have h1ε : 0 < 1 - ε := by linarith
  have hw_abs : |w| ≤ ε / (1 - ε) := by
    rw [hw, abs_div, abs_neg, abs_of_pos hx1]
    exact div_le_div₀ hε hxa h1ε hxle
  have hwlin : (P : ℝ) * w ≤ -(P * x) + P * (2 * x ^ 2) := by
    have e : w = -x + x ^ 2 / (1 + x) := by rw [hw]; field_simp; ring
    rw [e]
    have : x ^ 2 / (1 + x) ≤ 2 * x ^ 2 := by
      rw [div_le_iff₀ hx1]; nlinarith [sq_nonneg x]
    nlinarith
  have hw2 : w ^ 2 ≤ x ^ 2 / (1 - ε) ^ 2 := by
    rw [hw, div_pow, neg_sq]
    exact div_le_div_of_nonneg_left (sq_nonneg x) (by positivity) (pow_le_pow_left₀ h1ε.le hxle 2)
  have hgeo : (1 + |w|) ^ (P - 2) / (1 - ε) ^ 2 ≤ 2 := by
    have hb : 1 + |w| ≤ 1 / (1 - ε) := by
      have : 1 + ε / (1 - ε) = 1 / (1 - ε) := by field_simp; ring
      linarith
    have hpe : (1 - ε) ^ P ≥ 1 / 2 := by
      have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ -ε by linarith) P
      have e : (1 + -ε) = 1 - ε := by ring
      rw [e] at h
      linarith
    have e : (1 / (1 - ε)) ^ (P - 2) / (1 - ε) ^ 2 = 1 / (1 - ε) ^ P := by
      obtain ⟨m, rfl⟩ : ∃ m, P = m + 2 := ⟨P - 2, by omega⟩
      have : m + 2 - 2 = m := by omega
      rw [this, one_div_pow, div_div, ← pow_add]
    calc (1 + |w|) ^ (P - 2) / (1 - ε) ^ 2 ≤ (1 / (1 - ε)) ^ (P - 2) / (1 - ε) ^ 2 := by
          gcongr
      _ = 1 / (1 - ε) ^ P := e
      _ ≤ 2 := by rw [div_le_iff₀ (by positivity)]; linarith
  have hcoef : ((P : ℝ) * (P - 1) / 2) * (1 + |w|) ^ (P - 2) * w ^ 2 ≤
      ((P : ℝ) * (P - 1)) * x ^ 2 := by
    have hc0 : (0 : ℝ) ≤ (P : ℝ) * (P - 1) / 2 := by nlinarith
    calc ((P : ℝ) * (P - 1) / 2) * (1 + |w|) ^ (P - 2) * w ^ 2
        ≤ ((P : ℝ) * (P - 1) / 2) * (1 + |w|) ^ (P - 2) * (x ^ 2 / (1 - ε) ^ 2) := by gcongr
      _ = ((P : ℝ) * (P - 1) / 2) * ((1 + |w|) ^ (P - 2) / (1 - ε) ^ 2) * x ^ 2 := by ring
      _ ≤ ((P : ℝ) * (P - 1) / 2) * 2 * x ^ 2 := by gcongr
      _ = ((P : ℝ) * (P - 1)) * x ^ 2 := by ring
  have hmain : (1 + w) ^ P ≤ 1 - P * x + (P : ℝ) * (P + 1) * x ^ 2 := by
    have e : (P : ℝ) * (P + 1) * x ^ 2 = P * (2 * x ^ 2) + ((P : ℝ) * (P - 1)) * x ^ 2 := by ring
    rw [e]
    linarith
  -- rescale by `y^{-P}`
  have hfrac : 1 / (y + z) ^ P = (y / (y + z)) ^ P / y ^ P := by
    rw [div_pow]; field_simp
  rw [hfrac, hq]
  have hyP : 0 < y ^ P := pow_pos hy P
  calc (1 + w) ^ P / y ^ P ≤ (1 - P * x + (P : ℝ) * (P + 1) * x ^ 2) / y ^ P :=
        div_le_div_of_nonneg_right hmain hyP.le
    _ = 1 / y ^ P - P * z / y ^ (P + 1) + (P : ℝ) * (P + 1) * z ^ 2 / y ^ (P + 2) := by
        rw [hx]; field_simp; ring

end C37


-- ===== Solutions.C37.Seq =====

/-! # Scalar inequalities: weighted AM–GM tangents, Bernoulli bounds, power tails -/

namespace C37

open Finset

/-- tangent of `x ↦ x^{P+1}`: `(P+1) w x^P ≤ P x^{P+1} + w^{P+1}` -/
lemma amgm_inv (P : ℕ) (x w : ℝ) (hx : 0 ≤ x) (hw : 0 ≤ w) :
    ((P : ℝ) + 1) * w * x ^ P ≤ P * x ^ (P + 1) + w ^ (P + 1) := by
  rcases eq_or_lt_of_le hx with h0 | hpos
  · subst h0
    rcases Nat.eq_zero_or_pos P with hP | hP
    · subst hP; simp
    · rw [zero_pow (by omega), zero_pow (by omega)]; simp; positivity
  · set u := w / x with hu
    have hu0 : 0 ≤ u := by positivity
    have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ u - 1 by linarith) (P + 1)
    have e1 : w = u * x := by rw [hu]; field_simp
    rw [e1]
    have hxP : 0 < x ^ (P + 1) := by positivity
    have e2 : (u * x) ^ (P + 1) = (1 + (u - 1)) ^ (P + 1) * x ^ (P + 1) := by
      rw [mul_pow]; ring_nf
    rw [e2]
    have e3 : ((P : ℝ) + 1) * (u * x) * x ^ P = ((P : ℝ) + 1) * u * x ^ (P + 1) := by ring
    rw [e3]
    have := mul_le_mul_of_nonneg_right hb hxP.le
    push_cast at this
    linarith

/-- Bernoulli for negative powers: `1 − P h ≤ (1 + h)^{−P}` -/
lemma inv_bern (P : ℕ) (h : ℝ) (hh : -1 < h) : 1 - P * h ≤ 1 / (1 + h) ^ P := by
  have h1 : 0 < 1 + h := by linarith
  set g := -h / (1 + h) with hg
  have hg2 : (-2 : ℝ) ≤ g := by
    rw [hg, le_div_iff₀ h1]; linarith
  have hb := one_add_mul_le_pow hg2 P
  have e : 1 / (1 + h) ^ P = (1 + g) ^ P := by
    rw [hg, one_div, ← inv_pow]; congr 1; field_simp; ring
  rw [e]
  have hgh : -h ≤ g := by
    rw [hg, le_div_iff₀ h1]; linarith [sq_nonneg h]
  have hP : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  nlinarith

end C37

namespace C37

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

lemma SI.kinv_int [IsFiniteMeasure μ] (S : SI μ F Y I m N τ β B) {n : ℕ} (hmn : m ≤ n)
    (hn : n ≤ N) (P : ℕ) :
    Integrable ((I n).indicator (fun ω => (Y n ω)⁻¹ ^ P)) μ := by
  refine Integrable.of_bound (((S.Ym' hn).inv.pow_const P).indicator (S.Im' hn)).aestronglyMeasurable
    ((τ n)⁻¹ ^ P) ?_
  filter_upwards [S.low n hmn hn] with ω hω
  rw [Real.norm_eq_abs]
  by_cases h : ω ∈ I n
  · rw [Set.indicator_of_mem h]
    have hτ := S.τpos n
    have hy := hω h
    rw [abs_of_nonneg (by have : 0 < Y n ω := by linarith
                          positivity)]
    exact pow_le_pow_left₀ (by have : 0 < Y n ω := by linarith
                               positivity) (inv_anti₀ hτ hy) _
  · rw [Set.indicator_of_notMem h, abs_zero]; have := S.τpos n; positivity

/-- the curvature remainder of the inverse Taylor step -/
lemma inv_curv (P : ℕ) (β B x y τ : ℝ) (hτ : 0 < τ) (hy : τ ≤ y) (hβ : 0 ≤ β) (hx : 1 ≤ x)
    (hB8 : 8 * ((P : ℝ) + 1) ≤ B) (hτβ : 40 * ((P : ℝ) + 1) * β * x ≤ τ ^ 2) :
    (P : ℝ) * (P + 1) * y⁻¹ ^ (P + 2) * (10 * β + 2 * y ^ 2 / (B * x)) ≤ P / (2 * x) * y⁻¹ ^ P := by
  have hy0 : 0 < y := lt_of_lt_of_le hτ hy
  have hB0 : 0 < B := by have : (0 : ℝ) ≤ P := Nat.cast_nonneg P; linarith
  have hx0 : 0 < x := by linarith
  set z := y⁻¹ ^ P with hz
  have hz0 : 0 ≤ z := by positivity
  have e1 : y⁻¹ ^ (P + 2) * (10 * β + 2 * y ^ 2 / (B * x)) = z * (10 * β / y ^ 2 + 2 / (B * x)) := by
    rw [hz, pow_add, inv_pow y 2]; field_simp
  have h1 : 10 * β / y ^ 2 ≤ 10 * β / τ ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hτ.le hy 2)
  have h2 : ((P : ℝ) + 1) * (10 * β / τ ^ 2) ≤ 1 / (4 * x) := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h3 : ((P : ℝ) + 1) * (2 / (B * x)) ≤ 1 / (4 * x) := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h4 : ((P : ℝ) + 1) * (10 * β / y ^ 2 + 2 / (B * x)) ≤ 1 / (2 * x) := by
    have : 1 / (4 * x) + 1 / (4 * x) = 1 / (2 * x) := by field_simp; ring
    have h5 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (P : ℝ) + 1)
    nlinarith
  calc (P : ℝ) * (P + 1) * y⁻¹ ^ (P + 2) * (10 * β + 2 * y ^ 2 / (B * x))
      = (P : ℝ) * z * (((P : ℝ) + 1) * (10 * β / y ^ 2 + 2 / (B * x))) := by
        rw [mul_assoc, e1]; ring
    _ ≤ (P : ℝ) * z * (1 / (2 * x)) := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = P / (2 * x) * z := by ring

/-- **one step of the killed inverse moment recursion (G.432)–(G.438)** -/
lemma SI.inv_step [IsProbabilityMeasure μ] (S : SI μ F Y I m N τ β B) {P : ℕ} (hP : 2 ≤ P)
    (hPB : (P : ℝ) * (3 / B) ≤ 1 / 2) (hB8 : 8 * ((P : ℝ) + 1) ≤ B) {Δ : ℝ} (hΔ : 0 ≤ Δ)
    {n : ℕ} (hmn : m ≤ n) (hnN : n < N)
    (hdr : ∀ᵐ ω ∂μ, ω ∈ I n → Δ ≤ μ[fun ω => Y (n + 1) ω - Y n ω | F n] ω)
    (hτβ : 40 * ((P : ℝ) + 1) * β n * ((n : ℝ) + 1) ≤ τ n ^ 2) (hβ : 0 ≤ β n) :
    kinv μ Y I P (n + 1) ≤ (1 + P / (2 * ((n : ℝ) + 1))) * kinv μ Y I P n -
      P * Δ * kinv μ Y I (P + 1) n := by
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
  let H : Ω → ℝ := (I n).indicator (fun ω => (Y (n + 1) ω)⁻¹ ^ P)
  let g0 : Ω → ℝ := (I n).indicator (fun ω => (Y n ω)⁻¹ ^ P)
  let g1 : Ω → ℝ := (I n).indicator (fun ω => -(P : ℝ) * (Y n ω)⁻¹ ^ (P + 1))
  let g2 : Ω → ℝ := (I n).indicator (fun ω => (P : ℝ) * (P + 1) * (Y n ω)⁻¹ ^ (P + 2))
  let ξ : Ω → ℝ := fun ω => Y (n + 1) ω - Y n ω
  let b1 : Ω → ℝ := (I n).indicator (fun ω => -(P : ℝ) * Δ * (Y n ω)⁻¹ ^ (P + 1))
  let V : Ω → ℝ := fun ω => 10 * β n + 2 * Y n ω ^ 2 / (B * x)
  set cb : ℝ := (2 / τ n) ^ P + (τ n)⁻¹ ^ P + P * (τ n)⁻¹ ^ (P + 1) +
    P * (P + 1) * (τ n)⁻¹ ^ (P + 2) + (|r1| + |r0|) + P * Δ * (τ n)⁻¹ ^ (P + 1) +
    (10 * β n + 2 * r0 ^ 2 / (B * x)) with hcb
  -- pointwise facts on the alive set
  have hfacts : ∀ᵐ ω ∂μ, ω ∈ I n → τ n ≤ Y n ω ∧ |ξ ω| ≤ 3 / B * Y n ω ∧ Y n ω / 2 ≤ Y (n + 1) ω := by
    filter_upwards [S.low n hmn hnN.le, S.mag n hmn hnN] with ω h1 h2 hI
    have hy := h1 hI
    have hm := h2 hI
    refine ⟨hy, by simp only [ξ]; rw [show 3 / B * Y n ω = 3 * Y n ω / B by ring]; exact hm, ?_⟩
    have : 3 * Y n ω / B ≤ Y n ω / 2 := by
      rw [div_le_div_iff₀ hB0 (by norm_num)]; nlinarith
    have := (abs_le.1 hm).1
    linarith
  have hbd : ∀ᵐ ω ∂μ, |H ω| ≤ cb ∧ |g0 ω| ≤ cb ∧ |g1 ω| ≤ cb ∧ |g2 ω| ≤ cb ∧ |ξ ω| ≤ cb ∧
      |b1 ω| ≤ cb ∧ |V ω| ≤ cb := by
    filter_upwards [hfacts, hr0, hr1] with ω hf h0 h1
    have p1 : 0 ≤ (2 / τ n) ^ P := by positivity
    have p2 : 0 ≤ (τ n)⁻¹ ^ P := by positivity
    have p3 : 0 ≤ (P : ℝ) * (τ n)⁻¹ ^ (P + 1) := by positivity
    have p4 : 0 ≤ (P : ℝ) * (P + 1) * (τ n)⁻¹ ^ (P + 2) := by positivity
    have p5 : 0 ≤ |r1| + |r0| := by positivity
    have p6 : 0 ≤ (P : ℝ) * Δ * (τ n)⁻¹ ^ (P + 1) := by positivity
    have p7 : 0 ≤ 10 * β n + 2 * r0 ^ 2 / (B * x) := by positivity
    have tV : |V ω| ≤ 10 * β n + 2 * r0 ^ 2 / (B * x) := by
      simp only [V]
      rw [abs_of_nonneg (by positivity)]
      have : Y n ω ^ 2 ≤ r0 ^ 2 := by
        have := sq_le_sq' (abs_le.1 h0).1 (abs_le.1 h0).2; linarith
      gcongr
    have tξ : |ξ ω| ≤ |r1| + |r0| := by
      simp only [ξ]
      exact le_trans (abs_sub _ _) (add_le_add (h1.trans (le_abs_self _)) (h0.trans (le_abs_self _)))
    by_cases hI : ω ∈ I n
    · obtain ⟨hy, -, hy1⟩ := hf hI
      have hY0 : 0 < Y n ω := lt_of_lt_of_le hτ hy
      have hinv : (Y n ω)⁻¹ ≤ (τ n)⁻¹ := inv_anti₀ hτ hy
      have hinv1 : (Y (n + 1) ω)⁻¹ ≤ 2 / τ n := by
        rw [show 2 / τ n = (τ n / 2)⁻¹ by field_simp]
        exact inv_anti₀ (by positivity) (by linarith)
      have hY1 : 0 < Y (n + 1) ω := by linarith
      simp only [H, g0, g1, g2, b1, Set.indicator_of_mem hI]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [abs_of_nonneg (by positivity)]
        have := pow_le_pow_left₀ (by positivity) hinv1 P; simp only [cb]; linarith
      · rw [abs_of_nonneg (by positivity)]
        have := pow_le_pow_left₀ (by positivity) hinv P; simp only [cb]; linarith
      · rw [abs_mul, abs_neg, Nat.abs_cast, abs_of_nonneg (by positivity)]
        have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv (P + 1))
          (Nat.cast_nonneg P)
        simp only [cb]; linarith
      · rw [abs_of_nonneg (by positivity)]
        have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv (P + 2))
          (by positivity : (0 : ℝ) ≤ P * (P + 1))
        simp only [cb]; linarith
      · simp only [cb]; linarith
      · rw [abs_mul, abs_mul, abs_neg, Nat.abs_cast, abs_of_nonneg hΔ, abs_of_nonneg (by positivity)]
        have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hinv (P + 1))
          (by positivity : (0 : ℝ) ≤ P * Δ)
        simp only [cb]; linarith
      · simp only [cb]; linarith
    · simp only [H, g0, g1, g2, b1, Set.indicator_of_notMem hI, abs_zero]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [cb] <;> linarith
  have hpt : ∀ᵐ ω ∂μ, ω ∈ I n → H ω ≤ g0 ω + g1 ω * ξ ω + g2 ω * ξ ω ^ 2 := by
    filter_upwards [hfacts] with ω hf hI
    obtain ⟨hy, hξ, -⟩ := hf hI
    have hY0 : 0 < Y n ω := lt_of_lt_of_le hτ hy
    have hT := C37.inv_pow_taylor (Y n ω) (ξ ω) (3 / B) P hP hY0 (by positivity) hξ hPB
    simp only [H, g0, g1, g2, Set.indicator_of_mem hI]
    have e1 : Y (n + 1) ω = Y n ω + ξ ω := by simp only [ξ]; ring
    rw [e1, inv_pow, inv_pow, inv_pow, inv_pow]
    rw [one_div, one_div] at hT
    have e2 : (P : ℝ) * ξ ω / Y n ω ^ (P + 1) = (P : ℝ) * (Y n ω ^ (P + 1))⁻¹ * ξ ω := by
      field_simp
    have e3 : (P : ℝ) * (P + 1) * ξ ω ^ 2 / Y n ω ^ (P + 2) =
        (P : ℝ) * (P + 1) * (Y n ω ^ (P + 2))⁻¹ * ξ ω ^ 2 := by field_simp
    rw [e2, e3] at hT
    linarith
  have hdr' : ∀ᵐ ω ∂μ, ω ∈ I n → g1 ω * μ[ξ | F n] ω ≤ b1 ω := by
    filter_upwards [hdr, hfacts] with ω h hf hI
    obtain ⟨hy, -, -⟩ := hf hI
    have hY0 : 0 < Y n ω := lt_of_lt_of_le hτ hy
    simp only [g1, b1, Set.indicator_of_mem hI]
    have hd := h hI
    have hc : 0 ≤ (P : ℝ) * (Y n ω)⁻¹ ^ (P + 1) := by positivity
    have : (P : ℝ) * (Y n ω)⁻¹ ^ (P + 1) * Δ ≤ (P : ℝ) * (Y n ω)⁻¹ ^ (P + 1) * μ[ξ | F n] ω :=
      mul_le_mul_of_nonneg_left hd hc
    linarith
  have hse : ∀ᵐ ω ∂μ, ω ∈ I n → μ[fun ω => ξ ω ^ 2 | F n] ω ≤ V ω := by
    filter_upwards [S.sec n hmn hnN] with ω h hI
    exact h hI
  have hg2n : ∀ᵐ ω ∂μ, ω ∈ I n → 0 ≤ g2 ω := by
    filter_upwards [hfacts] with ω hf hI
    obtain ⟨hy, -, -⟩ := hf hI
    have hY0 : 0 < Y n ω := lt_of_lt_of_le hτ hy
    simp only [g2, Set.indicator_of_mem hI]; positivity
  have hst := pstep (μ := μ) (F := F) (n := n) hFn hJ (H := H) (g0 := g0) (g1 := g1) (g2 := g2)
    (ξ := ξ) (b1 := b1) (V := V)
    (((hYm1'.inv.pow_const P).indicator hJm).aestronglyMeasurable)
    (((hYm'.inv.pow_const P).indicator hJm).aestronglyMeasurable)
    (((hYm.inv.pow_const _).const_mul _).indicator hJ).stronglyMeasurable
    (((hYm.inv.pow_const _).const_mul _).indicator hJ).stronglyMeasurable
    ((hYm1'.sub hYm').aestronglyMeasurable)
    ((((hYm'.inv.pow_const _).const_mul _).indicator hJm).aestronglyMeasurable)
    ((measurable_const.add ((measurable_const.mul (hYm'.pow_const 2)).div_const _)).aestronglyMeasurable)
    hbd hpt hdr' hse hg2n
  -- compare both sides with the killed moments
  have hL : kinv μ Y I P (n + 1) ≤ ∫ ω, (I n).indicator H ω ∂μ := by
    have hLi := S.kinv_int (n := n + 1) (by omega) hnN P
    have hHi : Integrable ((I n).indicator H) μ :=
      (Integrable.of_bound (((hYm1'.inv.pow_const P).indicator hJm).aestronglyMeasurable) cb
        (by filter_upwards [hbd] with ω h; rw [Real.norm_eq_abs]; exact h.1)).indicator hJm
    refine integral_mono_ae hLi hHi ?_
    filter_upwards [hfacts] with ω hf
    by_cases h1 : ω ∈ I (n + 1)
    · have hI := S.Imono n h1
      simp only [H, Set.indicator_of_mem h1, Set.indicator_of_mem hI, le_refl]
    · rw [Set.indicator_of_notMem h1]
      by_cases hI : ω ∈ I n
      · obtain ⟨hy, -, hy1⟩ := hf hI
        have : 0 < Y (n + 1) ω := by linarith
        simp only [H, Set.indicator_of_mem hI]; positivity
      · simp [H, Set.indicator_of_notMem hI]
  have hR : ∫ ω, (I n).indicator (fun ω => g0 ω + b1 ω + g2 ω * V ω) ω ∂μ ≤
      (1 + P / (2 * x)) * kinv μ Y I P n - P * Δ * kinv μ Y I (P + 1) n := by
    have i1 := S.kinv_int hmn hnN.le P
    have i2 := S.kinv_int hmn hnN.le (P + 1)
    have hRi : Integrable ((I n).indicator (fun ω => g0 ω + b1 ω + g2 ω * V ω)) μ := by
      refine Integrable.of_bound ?_ (cb + cb + cb * cb) ?_
      · exact (((((hYm'.inv.pow_const P).indicator hJm).add
          (((hYm'.inv.pow_const _).const_mul _).indicator hJm)).add
          ((((hYm'.inv.pow_const _).const_mul _).indicator hJm).mul
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
    have hRi2 : Integrable (fun ω => (1 + P / (2 * x)) * (I n).indicator (fun ω => (Y n ω)⁻¹ ^ P) ω -
        P * Δ * (I n).indicator (fun ω => (Y n ω)⁻¹ ^ (P + 1)) ω) μ :=
      (i1.const_mul _).sub (i2.const_mul _)
    calc ∫ ω, (I n).indicator (fun ω => g0 ω + b1 ω + g2 ω * V ω) ω ∂μ
        ≤ ∫ ω, ((1 + P / (2 * x)) * (I n).indicator (fun ω => (Y n ω)⁻¹ ^ P) ω -
            P * Δ * (I n).indicator (fun ω => (Y n ω)⁻¹ ^ (P + 1)) ω) ∂μ := by
          refine integral_mono_ae hRi hRi2 ?_
          filter_upwards [hfacts] with ω hf
          by_cases hI : ω ∈ I n
          · obtain ⟨hy, -, -⟩ := hf hI
            have hY0 : 0 < Y n ω := lt_of_lt_of_le hτ hy
            simp only [g0, b1, g2, V, Set.indicator_of_mem hI]
            have hc := inv_curv P (β n) B x (Y n ω) (τ n) hτ hy hβ hx1 hB8 hτβ
            have e : (1 + P / (2 * x)) * (Y n ω)⁻¹ ^ P = (Y n ω)⁻¹ ^ P + P / (2 * x) * (Y n ω)⁻¹ ^ P := by
              ring
            rw [e]
            have e2 : -(P : ℝ) * Δ * (Y n ω)⁻¹ ^ (P + 1) = -(P * Δ * (Y n ω)⁻¹ ^ (P + 1)) := by ring
            rw [e2]
            linarith only [hc]
          · simp [g0, b1, g2, Set.indicator_of_notMem hI]
      _ = (1 + P / (2 * x)) * kinv μ Y I P n - P * Δ * kinv μ Y I (P + 1) n := by
          rw [integral_sub (i1.const_mul _) (i2.const_mul _), integral_const_mul,
            integral_const_mul]
          rfl
  have hHH : ∫ ω, (I n).indicator H ω ∂μ ≤
      ∫ ω, (I n).indicator (fun ω => g0 ω + b1 ω + g2 ω * V ω) ω ∂μ := hst
  linarith

lemma SI.kinv_init [IsProbabilityMeasure μ] (S : SI μ F Y I m N τ β B) (hmN : m ≤ N) (P : ℕ) :
    kinv μ Y I P m ≤ 1 / τ m ^ P := by
  have hτ := S.τpos m
  unfold kinv
  calc ∫ ω, (I m).indicator (fun ω => (Y m ω)⁻¹ ^ P) ω ∂μ ≤ ∫ _ω, (τ m)⁻¹ ^ P ∂μ := by
        refine integral_mono_ae (S.kinv_int le_rfl hmN P) (integrable_const _) ?_
        filter_upwards [S.low m le_rfl hmN] with ω h
        by_cases hI : ω ∈ I m
        · rw [Set.indicator_of_mem hI]
          have hy := h hI
          exact pow_le_pow_left₀ (by have : 0 < Y m ω := by linarith
                                     positivity) (inv_anti₀ hτ hy) _
        · rw [Set.indicator_of_notMem hI]; positivity
    _ = 1 / τ m ^ P := by simp [inv_pow]

/-- the tangent inequality `(P+1) w E[1_I Y^{-P}] ≤ P E[1_I Y^{-(P+1)}] + w^{P+1}` -/
lemma SI.kinv_tangent [IsProbabilityMeasure μ] (S : SI μ F Y I m N τ β B) {n : ℕ} (hmn : m ≤ n)
    (hnN : n ≤ N) (P : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    ((P : ℝ) + 1) * w * kinv μ Y I P n ≤ P * kinv μ Y I (P + 1) n + w ^ (P + 1) := by
  have i1 := S.kinv_int hmn hnN P
  have i2 := S.kinv_int hmn hnN (P + 1)
  have hpt : ∀ᵐ ω ∂μ, ((P : ℝ) + 1) * w * (I n).indicator (fun ω => (Y n ω)⁻¹ ^ P) ω ≤
      P * (I n).indicator (fun ω => (Y n ω)⁻¹ ^ (P + 1)) ω + w ^ (P + 1) := by
    filter_upwards [S.low n hmn hnN] with ω h
    by_cases hI : ω ∈ I n
    · rw [Set.indicator_of_mem hI, Set.indicator_of_mem hI]
      have hy : 0 < Y n ω := lt_of_lt_of_le (S.τpos n) (h hI)
      exact C37.amgm_inv P (Y n ω)⁻¹ w (by positivity) hw
    · rw [Set.indicator_of_notMem hI, Set.indicator_of_notMem hI]; simp; positivity
  have h := integral_mono_ae (i1.const_mul _) ((i2.const_mul _).add (integrable_const _)) hpt
  simp only [Pi.add_apply] at h
  rw [integral_const_mul, integral_add (i2.const_mul _) (integrable_const _), integral_const_mul,
    integral_const] at h
  simpa [kinv] using h

set_option maxHeartbeats 1000000 in
/-- **the killed inverse local moment (G.442)**: `E[1_{I_t} Y_t^{-P}] ≤ (4/((t+1)Δ))^P` -/
theorem SI.inv_moment [IsProbabilityMeasure μ] (S : SI μ F Y I m N τ β B) {P : ℕ} (hP : 2 ≤ P)
    (hPB : (P : ℝ) * (3 / B) ≤ 1 / 2) (hB8 : 8 * ((P : ℝ) + 1) ≤ B) {Δ : ℝ} (hΔ : 0 < Δ)
    {t : ℕ} (hmt : m ≤ t) (htN : t ≤ N) (hmhalf : 2 * ((m : ℝ) + 1) ≤ (t : ℝ) + 1)
    (hτm : ((P : ℝ) + 1) * Δ ≤ τ m) (hmP : (P : ℝ) + 1 ≤ 2 * ((m : ℝ) + 1))
    (hdr : ∀ n, m ≤ n → n < t → ∀ᵐ ω ∂μ, ω ∈ I n → Δ ≤ μ[fun ω => Y (n + 1) ω - Y n ω | F n] ω)
    (hτβ : ∀ n, m ≤ n → n < t → 40 * ((P : ℝ) + 1) * β n * ((n : ℝ) + 1) ≤ τ n ^ 2)
    (hβ : ∀ n, 0 ≤ β n) :
    kinv μ Y I P t ≤ (4 / (((t : ℝ) + 1) * Δ)) ^ P := by
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
  let u : ℕ → ℝ := fun s => kinv μ Y I P s
  let v : ℕ → ℝ := fun s => kinv μ Y I (P + 1) s
  have claim : ∀ k, m + k ≤ t → ∃ c, ((P : ℝ) + 1) * Δ ≤ c ∧
      Δ * ((((m + k : ℕ) : ℝ) + 1) ^ 2 - ((m : ℝ) + 1) ^ 2) / 2 ≤ (((m + k : ℕ) : ℝ) + 1) * c ∧
      u (m + k) ≤ 1 / c ^ P := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨τ m, hτm, by simp; have := S.τpos m; positivity, ?_⟩
      simpa [u] using S.kinv_init (by omega) P
    | succ k ih =>
      intro hk
      obtain ⟨c, hc1, hc2, hc3⟩ := ih (by omega)
      set s := m + k with hs
      have hsN : s < N := by omega
      set n : ℝ := (s : ℝ) + 1 with hn
      have hn1 : (1 : ℝ) ≤ n := by simp only [n]; linarith [(Nat.cast_nonneg s : (0 : ℝ) ≤ s)]
      have hnpos : 0 < n := by linarith
      have hnP : (P : ℝ) + 1 ≤ 2 * n := by
        have : (m : ℝ) ≤ s := by exact_mod_cast (show m ≤ s by omega)
        linarith
      have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hc1
      have hstep := S.inv_step hP hPB hB8 hΔ.le (n := s) (by omega) hsN (hdr s (by omega) (by omega))
        (hτβ s (by omega) (by omega)) (hβ s)
      have htan := S.kinv_tangent (n := s) (by omega) hsN.le P (w := 1 / c) (by positivity)
      set c' := (1 - 1 / (2 * n)) * c + Δ with hc'
      refine ⟨c', ?_, ?_, ?_⟩
      · have h1 : (1 - 1 / (2 * n)) * (((P : ℝ) + 1) * Δ) ≤ (1 - 1 / (2 * n)) * c :=
          mul_le_mul_of_nonneg_left hc1 (by
            have : 1 / (2 * n) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
            linarith)
        have h2 : ((P : ℝ) + 1) * Δ / (2 * n) ≤ Δ := by
          rw [div_le_iff₀ (by positivity)]
          have := mul_le_mul_of_nonneg_left hnP hΔ.le
          linarith
        have e : (1 - 1 / (2 * n)) * (((P : ℝ) + 1) * Δ) = ((P : ℝ) + 1) * Δ - ((P : ℝ) + 1) * Δ / (2 * n) := by
          ring
        linarith
      · have hcast : (((m + (k + 1) : ℕ) : ℝ) + 1) = n + 1 := by
          simp only [n, hs]; push_cast; ring
        have hcast0 : (((m + k : ℕ) : ℝ) + 1) = n := by simp only [n, hs]
        rw [hcast]
        have h1 : n * c + Δ * (n + 1) ≤ (n + 1) * c' := by
          rw [hc']
          have e : (n + 1) * ((1 - 1 / (2 * n)) * c + Δ) = n * c + Δ * (n + 1) + c * (1 / 2 - 1 / (2 * n)) := by
            field_simp; ring
          rw [e]
          have : 0 ≤ c * (1 / 2 - 1 / (2 * n)) := mul_nonneg hc0.le (by
            rw [sub_nonneg, div_le_div_iff₀ (by linarith) (by norm_num)]; linarith)
          linarith
        nlinarith
      · have hcoef : 0 ≤ 1 + P / (2 * n) - ((P : ℝ) + 1) * Δ / c := by
          have : ((P : ℝ) + 1) * Δ / c ≤ 1 := by rw [div_le_one hc0]; exact hc1
          have : 0 ≤ (P : ℝ) / (2 * n) := by positivity
          linarith
        have hu1 : u (s + 1) ≤ (1 + P / (2 * n) - ((P : ℝ) + 1) * Δ / c) * u s + Δ * (1 / c) ^ (P + 1) := by
          have hv : P * Δ * v s ≥ Δ * (((P : ℝ) + 1) * (1 / c) * u s - (1 / c) ^ (P + 1)) := by
            have := mul_le_mul_of_nonneg_left htan hΔ.le
            simp only [u, v]
            linarith
          have e : (1 + P / (2 * n) - ((P : ℝ) + 1) * Δ / c) * u s =
              (1 + P / (2 * n)) * u s - Δ * (((P : ℝ) + 1) * (1 / c) * u s) := by field_simp
          simp only [u, v] at hstep hv ⊢
          rw [e]
          linarith
        have hu2 : u (s + 1) ≤ (1 + P / (2 * n) - P * Δ / c) * (1 / c ^ P) := by
          have h1 := mul_le_mul_of_nonneg_left hc3 hcoef
          have e : (1 + P / (2 * n) - ((P : ℝ) + 1) * Δ / c) * (1 / c ^ P) + Δ * (1 / c) ^ (P + 1) =
              (1 + P / (2 * n) - P * Δ / c) * (1 / c ^ P) := by
            rw [one_div_pow, pow_succ]; field_simp; ring
          linarith
        have hh : -1 < -1 / (2 * n) + Δ / c := by
          have : -1 / (2 * n) ≥ -1 / 2 := by
            rw [ge_iff_le, div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
          have : 0 ≤ Δ / c := by positivity
          linarith
        have hb := C37.inv_bern P (-1 / (2 * n) + Δ / c) hh
        have hcc : c' = c * (1 + (-1 / (2 * n) + Δ / c)) := by rw [hc']; field_simp; ring
        have hfin : (1 + P / (2 * n) - P * Δ / c) * (1 / c ^ P) ≤ 1 / c' ^ P := by
          rw [hcc, mul_pow, ← one_div_mul_one_div, mul_comm (1 + (P : ℝ) / (2 * n) - P * Δ / c)]
          have e : 1 - (P : ℝ) * (-1 / (2 * n) + Δ / c) = 1 + P / (2 * n) - P * Δ / c := by ring
          rw [← e]
          exact mul_le_mul_of_nonneg_left hb (by positivity)
        have : u (m + (k + 1)) = u (s + 1) := rfl
        rw [this]
        exact hu2.trans hfin
  obtain ⟨c, hc1, hc2, hc3⟩ := claim (t - m) (by omega)
  have ht' : m + (t - m) = t := by omega
  rw [ht'] at hc2 hc3
  have hc0 : 0 < c := lt_of_lt_of_le (by positivity) hc1
  have htn : (0 : ℝ) < (t : ℝ) + 1 := by positivity
  have hc4 : ((t : ℝ) + 1) * Δ / 4 ≤ c := by
    have h0 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    have hm2 : ((m : ℝ) + 1) ^ 2 ≤ ((t : ℝ) + 1) ^ 2 / 4 := by
      have := pow_le_pow_left₀ h0 (show (m : ℝ) + 1 ≤ ((t : ℝ) + 1) / 2 by linarith) 2
      have e : (((t : ℝ) + 1) / 2) ^ 2 = ((t : ℝ) + 1) ^ 2 / 4 := by ring
      linarith
    have h4 : Δ * ((m : ℝ) + 1) ^ 2 ≤ Δ * (((t : ℝ) + 1) ^ 2 / 4) :=
      mul_le_mul_of_nonneg_left hm2 hΔ.le
    have h5 : 0 ≤ Δ * ((t : ℝ) + 1) ^ 2 := by positivity
    have h6 : ((t : ℝ) + 1) * (((t : ℝ) + 1) * Δ / 4) ≤ ((t : ℝ) + 1) * c := by linarith
    exact le_of_mul_le_mul_left h6 htn
  calc kinv μ Y I P t = u t := rfl
    _ ≤ 1 / c ^ P := hc3
    _ ≤ 1 / (((t : ℝ) + 1) * Δ / 4) ^ P :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hc4 _)
    _ = (4 / (((t : ℝ) + 1) * Δ)) ^ P := by rw [one_div, ← inv_pow, inv_div]

end G26


theorem _root_.solution : type_of% @G26.SI.inv_moment := @G26.SI.inv_moment
