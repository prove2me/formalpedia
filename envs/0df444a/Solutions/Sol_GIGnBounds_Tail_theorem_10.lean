-- Prove2me | solution 1 for GIGnBounds.Tail.theorem_10
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T23:56:10.418998+00:00
-- url     : https://prove2.me/submissions/b74f70a9-5e33-41ef-893a-b5ca2ec01287
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_GIGnBounds_Tail_Setting
import Theorems.Thm_GIGnBounds_Tail_lemma_2
import Theorems.Thm_GIGnBounds_Tail_lemma_3
import Theorems.Thm_GIGnBounds_Tail_lemma_4

open MeasureTheory ProbabilityTheory GIGnBounds.Tail

namespace GIGnT10Aux

lemma half_mul_rpow_neg (x q : ℝ) (hx : 0 ≤ x) :
    (1 / 2 * x) ^ (-q) = x ^ (-q) * (2 : ℝ) ^ q := by
  rw [Real.mul_rpow (by norm_num) hx, one_div, Real.inv_rpow (by norm_num),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv, mul_comm]

lemma two_mul_rpow (b q : ℝ) (hb : 0 ≤ b) : (2 * b) ^ q = (2 : ℝ) ^ q * b ^ q :=
  Real.mul_rpow (by norm_num) hb

lemma exp_009_le : Real.exp ((9 : ℝ) / 100) ≤ 11 / 10 := by
  have h := Real.add_one_le_exp (-((9 : ℝ) / 100))
  have hpos := Real.exp_pos ((9 : ℝ) / 100)
  have : Real.exp (-((9 : ℝ) / 100)) * Real.exp ((9 : ℝ) / 100) = 1 := by
    rw [← Real.exp_add]; simp
  nlinarith

end GIGnT10Aux

open GIGnT10Aux in
theorem solution (n : ℕ) (hn : 1 ≤ n) (μA μS : Measure ℝ) [IsProbabilityMeasure μA] [IsProbabilityMeasure μS]
    (hA : IsTimeLaw μA) (hS : IsTimeLaw μS)
    (hS1 : mean μS = 1) (hA2 : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂μA < ⊤)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : RenewalFamily Ω P n μA μS) (C₁ C₂ r₁ r₂ s : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hr₁s : s < r₁) (hs : 1 < s) (hr₂ : 2 < r₂)
    (hi : rate μA < n)
    (hii : ∀ t : ℝ, 1 ≤ t →
      ∫⁻ ω, ENNReal.ofReal (|∑ i, (F.Ne i ω t : ℝ) - n * t| ^ r₁) ∂P ≤ ENNReal.ofReal (C₁ * (n : ℝ) ^ (r₁ / 2) * t ^ s))
    (hiii : ∀ t : ℝ, 2 / (n : ℝ) ≤ t → t ≤ 1 →
      ∫⁻ ω, ENNReal.ofReal (|∑ i, (F.Ne i ω t : ℝ) - n * t| ^ r₂) ∂P ≤ ENNReal.ofReal (C₂ * ((n : ℝ) * t) ^ (r₂ / 2)))
    (x : ℝ) (hx : 18 ≤ x) :
    P.real {ω | (x : EReal) ≤ supFrom (fun t => (F.Ae ω t : ℝ) - ∑ i, (F.Ne i ω t : ℝ))} ≤
      18 / 10 * (1 + 1 / (r₁ - s)) * (32 * (r₁ + 1) / (s - 1)) ^ (r₁ + 1) * C₁ *
          (n : ℝ) ^ (r₁ / 2) * (n - rate μA) ^ (-s) * x ^ (-(r₁ - s)) +
        18 / 10 * (1 + 1 / (r₁ - s)) * (46 * (r₂ + 1) / (r₂ / 2 - 1)) ^ (r₂ + 1) * C₂ *
          (n : ℝ) ^ (r₂ / 2) * (n - rate μA) ^ (-(r₂ / 2)) * x ^ (-(r₂ / 2)) +
        11 / 10 * Real.exp (-((45 : ℝ) / 1000) * ((n - rate μA) / (n + rate μA)) *
          (nMoment μA 2)⁻¹ * x) := by
  set μ := rate μA with hμdef
  have hμ : 0 < μ := inv_pos.mpr hA.mean_pos
  set d : ℝ := (n : ℝ) - μ with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  -- the later arrival intervals are i.i.d. with law `μA`
  have hinj : Function.Injective
      (fun j : ℕ => (Sum.inl (some j) : Option ℕ ⊕ (Fin n × Option ℕ))) := by
    intro a b h; simpa using h
  have hiid : IsIIDSeq P (fun j => F.arr (some j)) μA :=
    ⟨fun j => F.measurable_arr (some j), F.indep_all.precomp hinj, fun j => F.law_arr_some j⟩
  -- Lemma 2: split into the arrival part and the service part
  have h2 := GIGnBounds.Tail.lemma_2 n μA μS hA hS hS1 hi Ω P F x (by linarith)
  -- Lemma 3 for the arrival part with `ν = (n - μ_A)/2`, level `x/2 - 1`
  have h3 := GIGnBounds.Tail.lemma_3 μA hA hA2 Ω P (fun j => F.arr (some j)) hiid
    (1 / 2 * d) (1 / 2 * x - 1) (by positivity) (by linarith)
  -- Lemma 4 for the service part with `ν = (n - μ_A)/2`, level `x/2`
  have h4 := GIGnBounds.Tail.lemma_4 n hn μS hS hS1 Ω P F.toServiceFamily C₁ C₂ r₁ r₂ s
    hC₁ hC₂ hr₁s hs hr₂ hii hiii (1 / 2 * d) (1 / 2 * x) (by positivity) (by linarith)
  -- algebra for the service part
  have hx0 : 0 ≤ x := by linarith
  have hb1 : 0 ≤ 16 * (r₁ + 1) / (s - 1) := by
    apply div_nonneg (by linarith) (by linarith)
  have hb2 : 0 ≤ 23 * (r₂ + 1) / (r₂ / 2 - 1) := by
    apply div_nonneg (by linarith) (by linarith)
  have e32 : (32 * (r₁ + 1) / (s - 1)) ^ (r₁ + 1) =
      (2 : ℝ) ^ (r₁ + 1) * (16 * (r₁ + 1) / (s - 1)) ^ (r₁ + 1) := by
    rw [← two_mul_rpow _ _ hb1]; ring_nf
  have e46 : (46 * (r₂ + 1) / (r₂ / 2 - 1)) ^ (r₂ + 1) =
      (2 : ℝ) ^ (r₂ + 1) * (23 * (r₂ + 1) / (r₂ / 2 - 1)) ^ (r₂ + 1) := by
    rw [← two_mul_rpow _ _ hb2]; ring_nf
  have eds : (1 / 2 * d) ^ (-s) = d ^ (-s) * (2 : ℝ) ^ s := half_mul_rpow_neg d s hdpos.le
  have exs : (1 / 2 * x) ^ (-(r₁ - s)) = x ^ (-(r₁ - s)) * (2 : ℝ) ^ (r₁ - s) :=
    half_mul_rpow_neg x (r₁ - s) hx0
  have exd : (1 / 2 * x * (1 / 2 * d)) ^ (-(r₂ / 2)) =
      x ^ (-(r₂ / 2)) * d ^ (-(r₂ / 2)) * (2 : ℝ) ^ r₂ := by
    have : 1 / 2 * x * (1 / 2 * d) = 1 / 2 * (1 / 2 * (x * d)) := by ring
    rw [this, half_mul_rpow_neg _ _ (by positivity), half_mul_rpow_neg _ _ (by positivity),
      Real.mul_rpow hx0 hdpos.le, mul_assoc, ← Real.rpow_add (by norm_num)]
    ring_nf
  have p1 : (2 : ℝ) ^ (r₁ + 1) = 2 * (2 : ℝ) ^ r₁ := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring
  have p2 : (2 : ℝ) ^ s * (2 : ℝ) ^ (r₁ - s) = (2 : ℝ) ^ r₁ := by
    rw [← Real.rpow_add (by norm_num)]; ring_nf
  have p3 : (2 : ℝ) ^ (r₂ + 1) = 2 * (2 : ℝ) ^ r₂ := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]; ring
  have hB4 : 36 / 10 * (1 + 1 / (r₁ - s)) *
        ((16 * (r₁ + 1) / (s - 1)) ^ (r₁ + 1) * C₁ * (n : ℝ) ^ (r₁ / 2) * (1 / 2 * d) ^ (-s) *
            (1 / 2 * x) ^ (-(r₁ - s)) +
          (23 * (r₂ + 1) / (r₂ / 2 - 1)) ^ (r₂ + 1) * C₂ * (n : ℝ) ^ (r₂ / 2) *
            (1 / 2 * x * (1 / 2 * d)) ^ (-(r₂ / 2))) =
      18 / 10 * (1 + 1 / (r₁ - s)) * (32 * (r₁ + 1) / (s - 1)) ^ (r₁ + 1) * C₁ *
          (n : ℝ) ^ (r₁ / 2) * d ^ (-s) * x ^ (-(r₁ - s)) +
        18 / 10 * (1 + 1 / (r₁ - s)) * (46 * (r₂ + 1) / (r₂ / 2 - 1)) ^ (r₂ + 1) * C₂ *
          (n : ℝ) ^ (r₂ / 2) * d ^ (-(r₂ / 2)) * x ^ (-(r₂ / 2)) := by
    rw [eds, exs, exd, e32, e46, p1, p3]
    have : (2 : ℝ) ^ s * (2 : ℝ) ^ (r₁ - s) = (2 : ℝ) ^ r₁ := p2
    linear_combination (36 / 10 * (1 + 1 / (r₁ - s)) * (16 * (r₁ + 1) / (s - 1)) ^ (r₁ + 1) *
      C₁ * (n : ℝ) ^ (r₁ / 2) * d ^ (-s) * x ^ (-(r₁ - s))) * this
  -- second moment `m ≥ 1`
  set m := nMoment μA 2 with hm
  have hI2 : Integrable (fun z : ℝ => z ^ 2) μA := by
    refine ⟨(continuous_pow 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun z => sq_nonneg z))]
    exact hA2
  have hI1 : Integrable (fun z : ℝ => z) μA := hA.integrable
  have hmge : 1 ≤ m := by
    have hmeq : m = ∫ z, μ ^ 2 * z ^ 2 ∂μA := by
      rw [hm, nMoment]
      congr 1; ext z
      rw [Real.rpow_two, ← hμdef]; ring
    have hle : ∫ z, (2 * μ * z - 1) ∂μA ≤ ∫ z, μ ^ 2 * z ^ 2 ∂μA := by
      apply integral_mono ((hI1.const_mul (2 * μ)).sub (integrable_const 1))
        (hI2.const_mul (μ ^ 2))
      intro z
      show 2 * μ * z - 1 ≤ μ ^ 2 * z ^ 2
      nlinarith [sq_nonneg (μ * z - 1)]
    rw [integral_sub (hI1.const_mul (2 * μ)) (integrable_const 1), integral_const_mul] at hle
    have hmean : μ * ∫ z, z ∂μA = 1 := by
      rw [hμdef, rate, mean]; exact inv_mul_cancel₀ hA.mean_pos.ne'
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hle
    have h2 : 2 * μ * ∫ z, z ∂μA = 2 := by rw [mul_assoc, hmean]; ring
    rw [hmeq]; linarith
  have hmpos : 0 < m := by linarith
  -- algebra for the arrival part
  have hE3 : Real.exp (-((9 : ℝ) / 100) * (1 / 2 * d / (1 / 2 * d + μ)) * m⁻¹ * (1 / 2 * x - 1)) ≤
      11 / 10 * Real.exp (-((45 : ℝ) / 1000) * ((n - μ) / (n + μ)) * m⁻¹ * x) := by
    have hnμ : 0 < (n : ℝ) + μ := by linarith
    have hratio : 1 / 2 * d / (1 / 2 * d + μ) = d / (n + μ) := by
      have e : (n : ℝ) + μ = d + 2 * μ := by rw [hd]; ring
      rw [e]; field_simp
    rw [hratio, ← hd]
    set a := d / (n + μ) * m⁻¹ with ha
    have ha0 : 0 ≤ a := by positivity
    have ha1 : a ≤ 1 := by
      have h1 : d / (n + μ) ≤ 1 := by rw [div_le_one hnμ]; linarith
      have h2 : m⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hmge
      calc a = d / (n + μ) * m⁻¹ := rfl
        _ ≤ 1 * 1 := mul_le_mul h1 h2 (by positivity) (by norm_num)
        _ = 1 := by norm_num
    have hsplit : -((9 : ℝ) / 100) * (d / (n + μ)) * m⁻¹ * (1 / 2 * x - 1) =
        9 / 100 * a + -((45 : ℝ) / 1000) * (d / (n + μ)) * m⁻¹ * x := by
      rw [ha]; ring
    rw [hsplit, Real.exp_add]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    calc Real.exp (9 / 100 * a) ≤ Real.exp (9 / 100) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ 11 / 10 := exp_009_le
  have h3' : P.real {ω | ((1 / 2 * x - 1 : ℝ) : EReal) ≤
          supFrom (fun t => (F.Ao ω t : ℝ) - rate μA * t - 1 / 2 * (n - rate μA) * t)} ≤
      11 / 10 * Real.exp (-((45 : ℝ) / 1000) * ((n - rate μA) / (n + rate μA)) *
          (nMoment μA 2)⁻¹ * x) := by
    refine le_trans ?_ hE3
    exact h3
  have h4' : P.real {ω | ((1 / 2 * x : ℝ) : EReal) ≤
          supFrom (fun t => n * t - ∑ i, (F.Ne i ω t : ℝ) - 1 / 2 * (n - rate μA) * t)} ≤
      18 / 10 * (1 + 1 / (r₁ - s)) * (32 * (r₁ + 1) / (s - 1)) ^ (r₁ + 1) * C₁ *
          (n : ℝ) ^ (r₁ / 2) * d ^ (-s) * x ^ (-(r₁ - s)) +
        18 / 10 * (1 + 1 / (r₁ - s)) * (46 * (r₂ + 1) / (r₂ / 2 - 1)) ^ (r₂ + 1) * C₂ *
          (n : ℝ) ^ (r₂ / 2) * d ^ (-(r₂ / 2)) * x ^ (-(r₂ / 2)) := by
    rw [← hB4]
    exact h4
  linarith
