-- Prove2me | solution 1 for BundleShaping.NoOrderSet.theorem_2_b_concave
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T21:35:08.740538+00:00
-- url     : https://prove2.me/submissions/015d70b6-712e-443f-95c9-cf3edb05c76a

import Mathlib
import Definitions.Def_BundleShaping_NoOrderSet_Model

open MeasureTheory Matrix Set

namespace NOSAux

/-! ## Generic lemmas -/

lemma norm_mulVec_le' {I J : Type} [Fintype I] [Fintype J] (A : Matrix I J ℝ) (u : J → ℝ) :
    ‖A *ᵥ u‖ ≤ (∑ i, ∑ j, |A i j|) * ‖u‖ := by
  have hB : 0 ≤ ∑ i, ∑ j, |A i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hB (norm_nonneg _))).2 fun i => ?_
  rw [Real.norm_eq_abs]
  calc |(A *ᵥ u) i| = |∑ j, A i j * u j| := rfl
    _ ≤ ∑ j, |A i j * u j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |A i j| * ‖u‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using norm_le_pi_norm u j)
          (abs_nonneg _)
    _ = (∑ j, |A i j|) * ‖u‖ := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, |A i j|) * ‖u‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun i => ∑ j, |A i j|)
          (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i)

lemma abs_integral_sub_le' {α : Type} [MeasurableSpace α] {μ : Measure α} (f g k : α → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hk : Integrable k μ)
    (hb : ∀ a, |f a - g a| ≤ k a) : |∫ a, f a ∂μ - ∫ a, g a ∂μ| ≤ ∫ a, k a ∂μ := by
  rw [← integral_sub hf hg]
  exact (abs_integral_le_integral_abs).trans
    (integral_mono (hf.sub hg).abs hk (fun a => by simpa using hb a))

lemma continuous_of_lip' {X : Type} [PseudoMetricSpace X] (F : X → ℝ) (C : ℝ)
    (h : ∀ x x', |F x - F x'| ≤ C * dist x x') : Continuous F :=
  (LipschitzWith.of_dist_le' (K := C) (fun x y => by rw [Real.dist_eq]; exact h x y)).continuous

lemma concaveOn_integral' {α E : Type} [MeasurableSpace α] {μ : Measure α}
    [AddCommGroup E] [Module ℝ E] {s : Set E} (hs : Convex ℝ s) (f : E → α → ℝ)
    (hf : ∀ a, ∀ x ∈ s, ∀ y ∈ s, ∀ p q : ℝ, 0 ≤ p → 0 ≤ q → p + q = 1 →
      p * f x a + q * f y a ≤ f (p • x + q • y) a)
    (hi : ∀ x ∈ s, Integrable (f x) μ) :
    ConcaveOn ℝ s (fun x => ∫ a, f x a ∂μ) := by
  refine ⟨hs, fun x hx y hy p q hp hq hpq => ?_⟩
  simp only [smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hi x hx).const_mul _)
    ((hi y hy).const_mul _)]
  exact integral_mono (((hi x hx).const_mul _).add ((hi y hy).const_mul _))
    (hi _ (hs hx hy hp hq hpq)) (fun a => hf a x hx y hy p q hp hq hpq)

/-- maximizer existence for a continuous coercive function on `ℝ^J × Ω`. -/
lemma exists_max_coercive {J : Type} [Fintype J] (Ω : Set (J → ℝ)) (hΩc : IsCompact Ω)
    (hΩn : Ω.Nonempty) (F : (J → ℝ) × (J → ℝ) → ℝ) (hF : ContinuousOn F (univ ×ˢ Ω))
    (κ K : ℝ) (hκ : 0 < κ) (hb : ∀ z, ∀ q ∈ Ω, F (z, q) ≤ K - κ * ‖z‖) :
    ∃ z, ∃ q ∈ Ω, ∀ z', ∀ q' ∈ Ω, F (z', q') ≤ F (z, q) := by
  obtain ⟨q0, hq0⟩ := hΩn
  set R := (K - F (0, q0)) / κ
  have hc : IsCompact (Metric.closedBall (0 : J → ℝ) R ×ˢ Ω) :=
    (isCompact_closedBall _ _).prod hΩc
  have hR : 0 ≤ R := by
    have := hb 0 q0 hq0
    simp at this
    exact div_nonneg (by linarith) hκ.le
  have hne : (Metric.closedBall (0 : J → ℝ) R ×ˢ Ω).Nonempty :=
    ⟨(0, q0), ⟨Metric.mem_closedBall_self hR, hq0⟩⟩
  obtain ⟨⟨z, q⟩, ⟨hz, hq⟩, hmax⟩ := hc.exists_isMaxOn hne
    (hF.mono (prod_mono (subset_univ _) le_rfl))
  refine ⟨z, q, hq, fun z' q' hq' => ?_⟩
  by_cases hz' : ‖z'‖ ≤ R
  · exact hmax ⟨by simpa using hz', hq'⟩
  · push_neg at hz'
    have h0 : F (0, q0) ≤ F (z, q) := hmax ⟨Metric.mem_closedBall_self hR, hq0⟩
    have h1 := hb z' q' hq'
    have : κ * R = K - F (0, q0) := by
      simp only [R]; field_simp
    have : κ * R < κ * ‖z'‖ := mul_lt_mul_of_pos_left hz' hκ
    linarith

end NOSAux

namespace NOSAux

open BundleShaping.NoOrderSet

variable {I J : Type} [Fintype I] [Fintype J]

lemma sum_comb {K : Type} [Fintype K] (c x y : K → ℝ) (a b : ℝ) :
    ∑ k, c k * (a * x k + b * y k) = a * ∑ k, c k * x k + b * ∑ k, c k * y k := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

lemma max_comb (a b u w : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max (a * u + b * w) 0 ≤ a * max u 0 + b * max w 0 := by
  apply max_le
  · have := le_max_left u 0; have := le_max_left w 0; nlinarith
  · have := le_max_right u 0; have := le_max_right w 0; positivity

variable (P : Params I J)

lemma demand_comb (s : ℕ) (q q' ε : J → ℝ) (a b : ℝ) :
    P.demand s (a • q + b • q') ε = a • P.demand s q ε + b • P.demand s q' ε := by
  funext j; simp [Params.demand]; ring

lemma demand_norm (s : ℕ) (q ε : J → ℝ) :
    ‖P.demand s q ε‖ ≤ ‖q‖ * ∑ j, |P.lam s + ε j| := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _)
    (Finset.sum_nonneg fun j _ => abs_nonneg _))).2 fun j => ?_
  rw [Real.norm_eq_abs]
  have : P.demand s q ε j = q j * (P.lam s + ε j) := by simp [Params.demand]; ring
  rw [this, abs_mul]
  refine mul_le_mul (by simpa [Real.norm_eq_abs] using norm_le_pi_norm q j) ?_ (abs_nonneg _)
    (norm_nonneg _)
  exact Finset.single_le_sum (f := fun j => |P.lam s + ε j|) (fun j _ => abs_nonneg _)
    (Finset.mem_univ j)

lemma demand_sub_norm (s : ℕ) (q q' ε : J → ℝ) :
    ‖P.demand s q ε - P.demand s q' ε‖ ≤ ‖q - q'‖ * ∑ j, |P.lam s + ε j| := by
  have : P.demand s q ε - P.demand s q' ε = P.demand s (q - q') ε := by
    funext j; simp [Params.demand]; ring
  rw [this]; exact demand_norm P s _ _

section Integrability

variable (s : ℕ) [hμ : IsProbabilityMeasure (P.μ s)]
  (hε : ∀ j, Integrable (fun ε : J → ℝ => ε j) (P.μ s))
include hε

lemma int_E : Integrable (fun ε : J → ℝ => ∑ j, |P.lam s + ε j|) (P.μ s) :=
  integrable_finsetSum _ fun j _ => ((integrable_const _).add (hε j)).abs

lemma int_lin (z q : J → ℝ) (j : J) :
    Integrable (fun ε : J → ℝ => P.demand s q ε j - z j) (P.μ s) := by
  simp only [Params.demand]
  exact ((integrable_const _).add ((hε j).const_mul _)).sub (integrable_const _)

lemma int_pos (z q : J → ℝ) (j : J) :
    Integrable (fun ε : J → ℝ => max (P.demand s q ε j - z j) 0) (P.μ s) :=
  (int_lin P s hε z q j).pos_part

lemma int_neg (z q : J → ℝ) (j : J) :
    Integrable (fun ε : J → ℝ => max (z j - P.demand s q ε j) 0) (P.μ s) := by
  have := (int_lin P s hε z q j).neg.pos_part
  simpa using this

lemma int_V (W : (I → ℝ) → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hW : ∀ x x', |W x - W x'| ≤ L * ‖x - x'‖) (y : I → ℝ) (q : J → ℝ) :
    Integrable (fun ε : J → ℝ => W (y - P.A *ᵥ P.demand s q ε)) (P.μ s) := by
  have hWc : Continuous W := continuous_of_lip' W L (fun x x' => by
    rw [dist_eq_norm]; exact hW x x')
  have hc : Continuous (fun ε : J → ℝ => W (y - P.A *ᵥ P.demand s q ε)) := by
    refine hWc.comp (continuous_const.sub (Continuous.matrix_mulVec continuous_const ?_))
    show Continuous (fun ε : J → ℝ => fun j => q j * P.lam s + q j * ε j)
    fun_prop
  set B := ∑ i, ∑ j, |P.A i j|
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  refine Integrable.mono' (g := fun ε => |W 0| + L * (‖y‖ + B * (‖q‖ * ∑ j, |P.lam s + ε j|)))
    ((integrable_const _).add (((integrable_const ‖y‖).add (((int_E P s hε).const_mul ‖q‖).const_mul B)).const_mul L)) hc.aestronglyMeasurable (Filter.Eventually.of_forall fun ε => ?_)
  rw [Real.norm_eq_abs]
  have h1 := hW (y - P.A *ᵥ P.demand s q ε) 0
  simp only [sub_zero] at h1
  have h2 : ‖y - P.A *ᵥ P.demand s q ε‖ ≤ ‖y‖ + B * (‖q‖ * ∑ j, |P.lam s + ε j|) :=
    (norm_sub_le _ _).trans (add_le_add le_rfl ((norm_mulVec_le' _ _).trans
      (mul_le_mul_of_nonneg_left (demand_norm P s q ε) hB)))
  have h3 := abs_sub_abs_le_abs_sub (W (y - P.A *ᵥ P.demand s q ε)) (W 0)
  nlinarith [mul_le_mul_of_nonneg_left h2 hL]

lemma Ep_comb (z z' q q' : J → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (j : J) :
    ∫ ε, max (P.demand s (a • q + b • q') ε j - (a • z + b • z') j) 0 ∂(P.μ s) ≤
      a * ∫ ε, max (P.demand s q ε j - z j) 0 ∂(P.μ s) +
      b * ∫ ε, max (P.demand s q' ε j - z' j) 0 ∂(P.μ s) := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((int_pos P s hε z q j).const_mul _) ((int_pos P s hε z' q' j).const_mul _)]
  refine integral_mono (int_pos P s hε _ _ j)
    (((int_pos P s hε z q j).const_mul _).add ((int_pos P s hε z' q' j).const_mul _))
    (fun ε => ?_)
  have := max_comb a b (P.demand s q ε j - z j) (P.demand s q' ε j - z' j) ha hb
  simp only [demand_comb, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
  exact (congrArg (fun t => max t 0) (by ring)).trans_le this

lemma Em_comb (z z' q q' : J → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (j : J) :
    ∫ ε, max ((a • z + b • z') j - P.demand s (a • q + b • q') ε j) 0 ∂(P.μ s) ≤
      a * ∫ ε, max (z j - P.demand s q ε j) 0 ∂(P.μ s) +
      b * ∫ ε, max (z' j - P.demand s q' ε j) 0 ∂(P.μ s) := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    ((int_neg P s hε z q j).const_mul _) ((int_neg P s hε z' q' j).const_mul _)]
  refine integral_mono (int_neg P s hε _ _ j)
    (((int_neg P s hε z q j).const_mul _).add ((int_neg P s hε z' q' j).const_mul _))
    (fun ε => ?_)
  have := max_comb a b (z j - P.demand s q ε j) (z' j - P.demand s q' ε j) ha hb
  simp only [demand_comb, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
  exact (congrArg (fun t => max t 0) (by ring)).trans_le this

lemma H_comb (hbp : ∀ j, 0 ≤ P.bp s j) (hh : ∀ i, 0 ≤ P.h s i) (hA : ∀ i j, 0 ≤ P.A i j)
    (y y' : I → ℝ) (z z' q q' : J → ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    P.H s (a • y + b • y') (a • z + b • z') (a • q + b • q') ≤
      a * P.H s y z q + b * P.H s y' z' q' := by
  unfold Params.H
  have e3 : ∀ i, (a • y + b • y' - P.A *ᵥ (a • z + b • z')) i =
      a * (y - P.A *ᵥ z) i + b * (y' - P.A *ᵥ z') i := by
    intro i; simp [Matrix.mulVec_add, Matrix.mulVec_smul]; ring
  calc _ ≤ ∑ j, P.bp s j * (a * ∫ ε, max (P.demand s q ε j - z j) 0 ∂(P.μ s) +
        b * ∫ ε, max (P.demand s q' ε j - z' j) 0 ∂(P.μ s)) +
      ∑ i, P.h s i * ∑ j, P.A i j * (a * ∫ ε, max (z j - P.demand s q ε j) 0 ∂(P.μ s) +
        b * ∫ ε, max (z' j - P.demand s q' ε j) 0 ∂(P.μ s)) +
      ∑ i, P.h s i * (a * (y - P.A *ᵥ z) i + b * (y' - P.A *ᵥ z') i) := by
        refine add_le_add (add_le_add ?_ ?_) (le_of_eq (Finset.sum_congr rfl fun i _ => by
          rw [e3]))
        · exact Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (Ep_comb P s hε z z' q q' a b ha hb j) (hbp j)
        · exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
              (Em_comb P s hε z z' q q' a b ha hb j) (hA i j)) (hh i)
    _ = _ := by
        rw [sum_comb, sum_comb]
        have : ∀ i, P.h s i * ∑ j, P.A i j * (a * ∫ ε, max (z j - P.demand s q ε j) 0 ∂(P.μ s) +
            b * ∫ ε, max (z' j - P.demand s q' ε j) 0 ∂(P.μ s)) =
            a * (P.h s i * ∑ j, P.A i j * ∫ ε, max (z j - P.demand s q ε j) 0 ∂(P.μ s)) +
            b * (P.h s i * ∑ j, P.A i j * ∫ ε, max (z' j - P.demand s q' ε j) 0 ∂(P.μ s)) := by
          intro i; rw [sum_comb]; ring
        rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum]
        ring

end Integrability

lemma Gm_sub (s : ℕ) (y y' : I → ℝ) (z q : J → ℝ) :
    P.Gm s y z q - P.Gm s y' z q = -∑ i, (P.cp s i + P.h s i) * (y i - y' i) := by
  unfold Params.Gm Params.H
  have h1 : ∑ i, P.cp s i * (y - P.lam s • (P.A *ᵥ q)) i -
      ∑ i, P.cp s i * (y' - P.lam s • (P.A *ᵥ q)) i = ∑ i, P.cp s i * (y i - y' i) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by simp; ring
  have h2 : ∑ i, P.h s i * (y - P.A *ᵥ z) i - ∑ i, P.h s i * (y' - P.A *ᵥ z) i =
      ∑ i, P.h s i * (y i - y' i) := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by simp; ring
  have h3 : ∑ i, (P.cp s i + P.h s i) * (y i - y' i) =
      ∑ i, P.cp s i * (y i - y' i) + ∑ i, P.h s i * (y i - y' i) := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  linarith


lemma G_sub (s : ℕ) (y y' : I → ℝ) (z q : J → ℝ) :
    P.G s y z q - P.G s y' z q = -∑ i, (P.cp s i + P.h s i) * (y i - y' i) +
      P.β * ((∫ ε, P.V (s + 1) (y - P.A *ᵥ P.demand s q ε) ∂(P.μ s)) -
        ∫ ε, P.V (s + 1) (y' - P.A *ᵥ P.demand s q ε) ∂(P.μ s)) := by
  have := Gm_sub P s y y' z q
  simp only [Params.G]
  linear_combination this

section GProps

variable (s : ℕ) [hμ : IsProbabilityMeasure (P.μ s)]
  (hε : ∀ j, Integrable (fun ε : J → ℝ => ε j) (P.μ s))
  (L : ℝ) (hL : 0 ≤ L) (hW : ∀ x x', |P.V (s + 1) x - P.V (s + 1) x'| ≤ L * ‖x - x'‖)
include hε hL hW

lemma G_antitone (hβ : 0 ≤ P.β) (hch : ∀ i, 0 ≤ P.cp s i + P.h s i)
    (hWa : Antitone (P.V (s + 1))) (z q : J → ℝ) :
    Antitone (fun y => P.G s y z q) := by
  intro y y' hyy'
  have e := G_sub P s y' y z q
  have h1 : 0 ≤ ∑ i, (P.cp s i + P.h s i) * (y' i - y i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hch i) (sub_nonneg.2 (hyy' i))
  have h2 : ∫ ε, P.V (s + 1) (y' - P.A *ᵥ P.demand s q ε) ∂(P.μ s) ≤
      ∫ ε, P.V (s + 1) (y - P.A *ᵥ P.demand s q ε) ∂(P.μ s) :=
    integral_mono (int_V P s hε _ L hL hW y' q) (int_V P s hε _ L hL hW y q)
      (fun ε => hWa (sub_le_sub_right hyy' _))
  have h3 := mul_le_mul_of_nonneg_left h2 hβ
  simp only
  linarith

lemma G_lip_y (hβ : 0 ≤ P.β) (z q : J → ℝ) (y y' : I → ℝ) :
    |P.G s y z q - P.G s y' z q| ≤
      ((∑ i, |P.cp s i + P.h s i|) + P.β * L) * ‖y - y'‖ := by
  rw [G_sub]
  have h1 : |∑ i, (P.cp s i + P.h s i) * (y i - y' i)| ≤ (∑ i, |P.cp s i + P.h s i|) * ‖y - y'‖ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    simpa [Real.norm_eq_abs] using norm_le_pi_norm (y - y') i
  have h2 : |(∫ ε, P.V (s + 1) (y - P.A *ᵥ P.demand s q ε) ∂(P.μ s)) -
      ∫ ε, P.V (s + 1) (y' - P.A *ᵥ P.demand s q ε) ∂(P.μ s)| ≤ L * ‖y - y'‖ := by
    have := abs_integral_sub_le' _ _ (fun _ => L * ‖y - y'‖) (int_V P s hε _ L hL hW y q)
      (int_V P s hε _ L hL hW y' q) (integrable_const _) (fun ε => by
        have := hW (y - P.A *ᵥ P.demand s q ε) (y' - P.A *ᵥ P.demand s q ε)
        simpa using this)
    simpa using this
  have h3 : |P.β * ((∫ ε, P.V (s + 1) (y - P.A *ᵥ P.demand s q ε) ∂(P.μ s)) -
      ∫ ε, P.V (s + 1) (y' - P.A *ᵥ P.demand s q ε) ∂(P.μ s))| ≤ P.β * (L * ‖y - y'‖) := by
    rw [abs_mul, abs_of_nonneg hβ]; exact mul_le_mul_of_nonneg_left h2 hβ
  calc _ ≤ |-∑ i, (P.cp s i + P.h s i) * (y i - y' i)| + |P.β * ((∫ ε, P.V (s + 1)
        (y - P.A *ᵥ P.demand s q ε) ∂(P.μ s)) -
        ∫ ε, P.V (s + 1) (y' - P.A *ᵥ P.demand s q ε) ∂(P.μ s))| := abs_add_le _ _
    _ ≤ _ := by rw [abs_neg]; nlinarith

lemma G_comb (hβ : 0 ≤ P.β) (hlam : 0 < P.lam s) (hτ : ConcaveOn ℝ P.Ω (P.τ s))
    (hbp : ∀ j, 0 ≤ P.bp s j) (hh : ∀ i, 0 ≤ P.h s i) (hA : ∀ i j, 0 ≤ P.A i j)
    (hWc : ConcaveOn ℝ univ (P.V (s + 1)))
    (y y' : I → ℝ) (z z' q q' : J → ℝ) (hq : q ∈ P.Ω) (hq' : q' ∈ P.Ω)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * P.G s y z q + b * P.G s y' z' q' ≤ P.G s (a • y + b • y') (a • z + b • z') (a • q + b • q') := by
  have epr : a * P.profitRate s q + b * P.profitRate s q' ≤ P.profitRate s (a • q + b • q') := by
    unfold Params.profitRate
    have h1 := hτ.2 hq hq' ha hb hab
    simp only [smul_eq_mul] at h1
    have h2 : ∑ j, P.a s j * (a • q + b • q') j = a * ∑ j, P.a s j * q j + b * ∑ j, P.a s j * q' j := by
      rw [← sum_comb]; rfl
    have h3 : ∑ i, P.c s i * (P.A *ᵥ (a • q + b • q')) i =
        a * ∑ i, P.c s i * (P.A *ᵥ q) i + b * ∑ i, P.c s i * (P.A *ᵥ q') i := by
      rw [← sum_comb]; simp [Matrix.mulVec_add, Matrix.mulVec_smul]
    rw [h2, h3]; linarith
  have elin : ∑ i, P.cp s i * (a • y + b • y' - P.lam s • (P.A *ᵥ (a • q + b • q'))) i =
      a * ∑ i, P.cp s i * (y - P.lam s • (P.A *ᵥ q)) i +
      b * ∑ i, P.cp s i * (y' - P.lam s • (P.A *ᵥ q')) i := by
    rw [← sum_comb]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_add,
        Matrix.mulVec_smul]; ring
  have eH := H_comb P s hε hbp hh hA y y' z z' q q' a b ha hb
  have eI : a * ∫ ε, P.V (s + 1) (y - P.A *ᵥ P.demand s q ε) ∂(P.μ s) +
      b * ∫ ε, P.V (s + 1) (y' - P.A *ᵥ P.demand s q' ε) ∂(P.μ s) ≤
      ∫ ε, P.V (s + 1) (a • y + b • y' - P.A *ᵥ P.demand s (a • q + b • q') ε) ∂(P.μ s) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add
      ((int_V P s hε _ L hL hW y q).const_mul _) ((int_V P s hε _ L hL hW y' q').const_mul _)]
    refine integral_mono (((int_V P s hε _ L hL hW y q).const_mul _).add
      ((int_V P s hε _ L hL hW y' q').const_mul _)) (int_V P s hε _ L hL hW _ _) (fun ε => ?_)
    have := hWc.2 (mem_univ (y - P.A *ᵥ P.demand s q ε)) (mem_univ (y' - P.A *ᵥ P.demand s q' ε))
      ha hb hab
    simp only [smul_eq_mul] at this
    refine this.trans_eq ?_
    congr 1
    rw [demand_comb, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    funext i; simp; ring
  have e1 := mul_le_mul_of_nonneg_left epr hlam.le
  have e4 := mul_le_mul_of_nonneg_left eI hβ
  simp only [Params.G, Params.Gm]
  linear_combination e1 + eH + e4 + elin

end GProps


/-- the feasible value set of (9). -/
def S9 (s : ℕ) (x : I → ℝ) : Set ℝ := {v | ∃ (y : I → ℝ) (z q : J → ℝ), P.Feas9 x y z q ∧ v = P.G s y z q}

lemma V_eq (s : ℕ) (hs : s ≤ P.T) (x : I → ℝ) : P.V s x = sSup (S9 P s x) := by
  simp only [Params.V, S9, Params.G]
  rw [show P.T + 1 - (s + 1) = P.T - s by omega, show P.T + 1 - s = P.T - s + 1 by omega]
  rfl

lemma S9_nonempty (s : ℕ) (hΩn : P.Ω.Nonempty) (x : I → ℝ) : (S9 P s x).Nonempty := by
  obtain ⟨q0, hq0⟩ := hΩn
  exact ⟨_, x ⊔ 0, 0, q0, ⟨by simp, le_sup_left, hq0⟩, rfl⟩

lemma S9_anti (s : ℕ) {x x' : I → ℝ} (h : x ≤ x') : S9 P s x' ⊆ S9 P s x := by
  rintro v ⟨y, z, q, ⟨h1, h2, h3⟩, rfl⟩
  exact ⟨y, z, q, ⟨h1, h.trans h2, h3⟩, rfl⟩

section VStep

variable (s : ℕ) [hμ : IsProbabilityMeasure (P.μ s)]
  (hε : ∀ j, Integrable (fun ε : J → ℝ => ε j) (P.μ s))
  (L : ℝ) (hL : 0 ≤ L) (hW : ∀ x x', |P.V (s + 1) x - P.V (s + 1) x'| ≤ L * ‖x - x'‖)
include hε hL hW

lemma S9_transfer (hβ : 0 ≤ P.β) (x x' : I → ℝ) (v : ℝ) (hv : v ∈ S9 P s x) :
    ∃ v' ∈ S9 P s x', v - ((∑ i, |P.cp s i + P.h s i|) + P.β * L) * ‖x - x'‖ ≤ v' := by
  obtain ⟨y, z, q, ⟨h1, h2, h3⟩, rfl⟩ := hv
  refine ⟨_, ⟨y ⊔ x', z, q, ⟨h1.trans le_sup_left, le_sup_right, h3⟩, rfl⟩, ?_⟩
  have hl := G_lip_y P s hε L hL hW hβ z q (y ⊔ x') y
  have hn : ‖y ⊔ x' - y‖ ≤ ‖x - x'‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    have := norm_le_pi_norm (x - x') i
    simp only [Pi.sub_apply, Pi.sup_apply, Real.norm_eq_abs] at this ⊢
    have hi := h2 i
    rcases le_total (y i) (x' i) with hc | hc
    · rw [max_eq_right hc, abs_of_nonneg (by linarith)]
      rw [abs_sub_comm] at this
      exact (le_abs_self _).trans' (by linarith) |>.trans this
    · rw [max_eq_left hc]; simp
  have hC : 0 ≤ (∑ i, |P.cp s i + P.h s i|) + P.β * L :=
    add_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) (mul_nonneg hβ hL)
  have := mul_le_mul_of_nonneg_left hn hC
  have := (abs_le.1 hl).1
  linarith

lemma V_step (hs : s ≤ P.T) (hβ : 0 ≤ P.β) (hlam : 0 < P.lam s) (hτ : ConcaveOn ℝ P.Ω (P.τ s))
    (hbp : ∀ j, 0 ≤ P.bp s j) (hh : ∀ i, 0 ≤ P.h s i) (hA : ∀ i j, 0 ≤ P.A i j)
    (hch : ∀ i, 0 ≤ P.cp s i + P.h s i) (hΩ : Convex ℝ P.Ω) (hΩn : P.Ω.Nonempty)
    (hWa : Antitone (P.V (s + 1))) (hWc : ConcaveOn ℝ univ (P.V (s + 1))) :
    ConcaveOn ℝ univ (P.V s) ∧ Antitone (P.V s) ∧
      ∃ L', 0 ≤ L' ∧ ∀ x x', |P.V s x - P.V s x'| ≤ L' * ‖x - x'‖ := by
  set C := (∑ i, |P.cp s i + P.h s i|) + P.β * L with hCdef
  have hC : 0 ≤ C := add_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) (mul_nonneg hβ hL)
  by_cases hB : ∀ x, BddAbove (S9 P s x)
  · -- one-sided Lipschitz bound
    have hone : ∀ x x', P.V s x - C * ‖x - x'‖ ≤ P.V s x' := by
      intro x x'
      rw [V_eq P s hs, V_eq P s hs]
      have : sSup (S9 P s x) ≤ sSup (S9 P s x') + C * ‖x - x'‖ := by
        refine csSup_le (S9_nonempty P s hΩn x) fun v hv => ?_
        obtain ⟨v', hv', hle⟩ := S9_transfer P s hε L hL hW hβ x x' v hv
        have := le_csSup (hB x') hv'
        linarith
      linarith
    refine ⟨⟨convex_univ, fun x1 _ x2 _ a b ha hb hab => ?_⟩, fun x x' hxx' => ?_,
      C, hC, fun x x' => ?_⟩
    · simp only [smul_eq_mul]
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      rw [V_eq P s hs x1, V_eq P s hs x2, V_eq P s hs]
      obtain ⟨v1, hv1, hlt1⟩ := exists_lt_of_lt_csSup (S9_nonempty P s hΩn x1)
        (sub_lt_self (sSup (S9 P s x1)) hδ)
      obtain ⟨v2, hv2, hlt2⟩ := exists_lt_of_lt_csSup (S9_nonempty P s hΩn x2)
        (sub_lt_self (sSup (S9 P s x2)) hδ)
      obtain ⟨y1, z1, q1, ⟨f1, f2, f3⟩, rfl⟩ := hv1
      obtain ⟨y2, z2, q2, ⟨g1, g2, g3⟩, rfl⟩ := hv2
      have hmem : P.G s (a • y1 + b • y2) (a • z1 + b • z2) (a • q1 + b • q2) ∈
          S9 P s (a • x1 + b • x2) := by
        refine ⟨_, _, _, ⟨?_, ?_, hΩ f3 g3 ha hb hab⟩, rfl⟩
        · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
          exact add_le_add (smul_le_smul_of_nonneg_left f1 ha) (smul_le_smul_of_nonneg_left g1 hb)
        · exact add_le_add (smul_le_smul_of_nonneg_left f2 ha) (smul_le_smul_of_nonneg_left g2 hb)
      have hc := G_comb P s hε L hL hW hβ hlam hτ hbp hh hA hWc y1 y2 z1 z2 q1 q2 f3 g3 a b ha hb hab
      have hle := le_csSup (hB _) hmem
      have e1 := mul_le_mul_of_nonneg_left hlt1.le ha
      have e2 := mul_le_mul_of_nonneg_left hlt2.le hb
      nlinarith
    · rw [V_eq P s hs, V_eq P s hs]
      exact csSup_le_csSup (hB x) (S9_nonempty P s hΩn x') (S9_anti P s hxx')
    · have h1 := hone x x'
      have h2 := hone x' x
      rw [norm_sub_rev x' x] at h2
      rw [abs_le]; constructor <;> linarith
  · push_neg at hB
    obtain ⟨x0, hx0⟩ := hB
    have hz : ∀ x, P.V s x = 0 := by
      intro x
      rw [V_eq P s hs]
      refine Real.sSup_of_not_bddAbove fun ⟨M, hM⟩ => hx0 ⟨M + C * ‖x0 - x‖, fun v hv => ?_⟩
      obtain ⟨v', hv', hle⟩ := S9_transfer P s hε L hL hW hβ x0 x v hv
      have := hM hv'
      linarith
    have hz' : P.V s = fun _ => 0 := funext hz
    rw [hz']
    refine ⟨concaveOn_const 0 convex_univ, fun _ _ _ => le_rfl, 0, le_rfl, fun _ _ => by simp⟩

end VStep


lemma per_j (c bp h E E' z q lam κ M : ℝ) (hE : 0 ≤ E) (hE2 : q * lam - z ≤ E) (hE' : 0 ≤ E')
    (hE'2 : z - q * lam ≤ E') (hbp : 0 ≤ bp) (hh : 0 ≤ h) (hk1 : κ ≤ c + h) (hk2 : κ ≤ bp - c)
    (hq0 : 0 ≤ q) (hqM : q ≤ M) (hlam : 0 < lam) :
    -(c * z) - bp * E - h * E' ≤ -(κ * |z|) + (bp + h) * M * lam := by
  have hql : q * lam ≤ M * lam := mul_le_mul_of_nonneg_right hqM hlam.le
  have hql0 : 0 ≤ q * lam := mul_nonneg hq0 hlam.le
  rcases le_total 0 z with hz | hz
  · rw [abs_of_nonneg hz]
    have h1 : h * (z - q * lam) ≤ h * E' := mul_le_mul_of_nonneg_left hE'2 hh
    have h2 : 0 ≤ bp * E := mul_nonneg hbp hE
    have h3 : κ * z ≤ (c + h) * z := mul_le_mul_of_nonneg_right hk1 hz
    have h4 : h * (q * lam) ≤ h * (M * lam) := mul_le_mul_of_nonneg_left hql hh
    have h5 : 0 ≤ bp * (M * lam) := mul_nonneg hbp (hql0.trans hql)
    nlinarith
  · rw [abs_of_nonpos hz]
    have h1 : bp * (q * lam - z) ≤ bp * E := mul_le_mul_of_nonneg_left hE2 hbp
    have h2 : 0 ≤ h * E' := mul_nonneg hh hE'
    have h3 : κ * (-z) ≤ (bp - c) * (-z) := mul_le_mul_of_nonneg_right hk2 (by linarith)
    have h4 : 0 ≤ bp * (q * lam) := mul_nonneg hbp hql0
    have h5 : 0 ≤ h * (M * lam) := mul_nonneg hh (hql0.trans hql)
    have h6 : bp * (q * lam) ≤ bp * (M * lam) := mul_le_mul_of_nonneg_left hql hbp
    nlinarith

lemma exists_kappa (f g : J → ℝ) (hf : ∀ j, 0 < f j) (hg : ∀ j, 0 < g j) :
    ∃ κ > 0, ∀ j, κ ≤ f j ∧ κ ≤ g j := by
  rcases isEmpty_or_nonempty J with hJ | hJ
  · exact ⟨1, one_pos, fun j => (IsEmpty.false j).elim⟩
  · obtain ⟨j0, hj0⟩ := Finite.exists_min (fun j => min (f j) (g j))
    exact ⟨min (f j0) (g j0), lt_min (hf j0) (hg j0), fun j =>
      ⟨(hj0 j).trans (min_le_left _ _), (hj0 j).trans (min_le_right _ _)⟩⟩

lemma norm_le_sum_abs (z : J → ℝ) : ‖z‖ ≤ ∑ j, |z j| := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _)).2 fun j => ?_
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun j => |z j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)

section Coercive

variable (s : ℕ) [hμ : IsProbabilityMeasure (P.μ s)]
  (hε : ∀ j, Integrable (fun ε : J → ℝ => ε j) (P.μ s))
  (hmean : ∀ j, ∫ ε, ε j ∂(P.μ s) = 0)
  (L : ℝ) (hL : 0 ≤ L) (hW : ∀ x x', |P.V (s + 1) x - P.V (s + 1) x'| ≤ L * ‖x - x'‖)
include hε hmean hL hW

lemma int_lin_eq (z q : J → ℝ) (j : J) :
    ∫ ε, (P.demand s q ε j - z j) ∂(P.μ s) = q j * P.lam s - z j := by
  simp only [Params.demand]
  have h1 : Integrable (fun ε : J → ℝ => q j * P.lam s + q j * ε j) (P.μ s) :=
    (integrable_const _).add ((hε j).const_mul _)
  rw [integral_sub h1 (integrable_const _), integral_add (integrable_const _) ((hε j).const_mul _),
    integral_const_mul (q j) (fun a : J → ℝ => a j), hmean j]
  simp

lemma G_coercive (hβ : 0 ≤ P.β) (hlam : 0 < P.lam s) (hτc : ContinuousOn (P.τ s) P.Ω)
    (hΩc : IsCompact P.Ω) (hΩ0 : ∀ q ∈ P.Ω, 0 ≤ q)
    (hbp : ∀ j, 0 ≤ P.bp s j) (hh : ∀ i, 0 ≤ P.h s i) (hA : ∀ i j, 0 ≤ P.A i j)
    (hch : ∀ i, 0 ≤ P.cp s i + P.h s i) (hWa : Antitone (P.V (s + 1)))
    (hc1 : ∀ j, P.ctilp s j < P.bp s j) (hc2 : ∀ j, 0 < P.ctilp s j + P.htil s j)
    (U : ℝ) (hU : ∀ x, P.V (s + 1) x ≤ U) :
    ∃ κ > 0, ∃ K, ∀ (y : I → ℝ) (z q : J → ℝ), q ∈ P.Ω → P.A *ᵥ z ≤ y →
      P.G s y z q ≤ K - κ * ‖z‖ := by
  obtain ⟨κ, hκ, hκj⟩ := exists_kappa (fun j => P.ctilp s j + P.htil s j)
    (fun j => P.bp s j - P.ctilp s j) hc2 (fun j => by linarith [hc1 j])
  obtain ⟨M, hM⟩ := hΩc.exists_bound_of_continuousOn (f := id) continuousOn_id
  set Q : (J → ℝ) → ℝ := fun q => P.lam s * P.profitRate s q +
    P.lam s * ∑ i, P.cp s i * (P.A *ᵥ q) i
  have hQc : ContinuousOn Q P.Ω := by
    simp only [Q, Params.profitRate]
    refine ContinuousOn.add (continuousOn_const.mul (ContinuousOn.sub (ContinuousOn.sub hτc
      (Continuous.continuousOn (by fun_prop))) (Continuous.continuousOn ?_)))
      (Continuous.continuousOn ?_)
    · exact continuous_finsetSum _ fun i _ => continuous_const.mul
        ((continuous_apply i).comp (Continuous.matrix_mulVec continuous_const continuous_id))
    · exact continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_const.mul
        ((continuous_apply i).comp (Continuous.matrix_mulVec continuous_const continuous_id)))
  obtain ⟨K1, hK1⟩ := hΩc.bddAbove_image hQc
  refine ⟨κ, hκ, K1 + (∑ j, (P.bp s j + P.htil s j) * M * P.lam s) + P.β * U, ?_⟩
  intro y z q hq hzy
  have hanti := G_antitone P s hε L hL hW hβ hch hWa z q hzy
  refine (show P.G s y z q ≤ P.G s (P.A *ᵥ z) z q from hanti).trans ?_
  have hQ : Q q ≤ K1 := hK1 ⟨q, hq, rfl⟩
  have hI : ∫ ε, P.V (s + 1) (P.A *ᵥ z - P.A *ᵥ P.demand s q ε) ∂(P.μ s) ≤ U := by
    have := integral_mono (int_V P s hε _ L hL hW (P.A *ᵥ z) q) (integrable_const U)
      (fun ε => hU (P.A *ᵥ z - P.A *ᵥ P.demand s q ε))
    simpa using this
  have hsplit : P.G s (P.A *ᵥ z) z q = Q q +
      ∑ j, (-(P.ctilp s j * z j) - P.bp s j * ∫ ε, max (P.demand s q ε j - z j) 0 ∂(P.μ s) -
        P.htil s j * ∫ ε, max (z j - P.demand s q ε j) 0 ∂(P.μ s)) +
      P.β * ∫ ε, P.V (s + 1) (P.A *ᵥ z - P.A *ᵥ P.demand s q ε) ∂(P.μ s) := by
    have e1 : ∑ i, P.cp s i * (P.A *ᵥ z) i = ∑ j, P.ctilp s j * z j := by
      simp only [Params.ctilp, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i, P.h s i * ∑ j, P.A i j * ∫ ε, max (z j - P.demand s q ε j) 0 ∂(P.μ s) =
        ∑ j, P.htil s j * ∫ ε, max (z j - P.demand s q ε j) 0 ∂(P.μ s) := by
      simp only [Params.htil, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun j _ =>
        Finset.sum_congr rfl fun i _ => by ring
    have e3 : ∑ i, P.cp s i * (P.A *ᵥ z - P.lam s • (P.A *ᵥ q)) i =
        ∑ i, P.cp s i * (P.A *ᵥ z) i - P.lam s * ∑ i, P.cp s i * (P.A *ᵥ q) i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp; ring
    have e4 : ∑ i, P.h s i * (P.A *ᵥ z - P.A *ᵥ z) i = 0 := by simp
    simp only [Params.G, Params.Gm, Params.H, Q]
    rw [e3, e1, e4, e2]
    simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    ring
  have hj : ∀ j, -(P.ctilp s j * z j) - P.bp s j * ∫ ε, max (P.demand s q ε j - z j) 0 ∂(P.μ s) -
        P.htil s j * ∫ ε, max (z j - P.demand s q ε j) 0 ∂(P.μ s) ≤
      -(κ * |z j|) + (P.bp s j + P.htil s j) * M * P.lam s := by
    intro j
    have hqj : q j ≤ M := by
      have := hM q hq
      exact (le_abs_self _).trans ((by simpa [Real.norm_eq_abs] using norm_le_pi_norm q j :
        |q j| ≤ ‖q‖).trans this)
    have hht : 0 ≤ P.htil s j :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hh i) (hA i j)
    refine per_j _ _ _ _ _ _ _ _ _ _ (integral_nonneg fun _ => le_max_right _ _) ?_
      (integral_nonneg fun _ => le_max_right _ _) ?_ (hbp j) hht (hκj j).1 (by linarith [(hκj j).2])
      (hΩ0 q hq j) hqj hlam
    · rw [← int_lin_eq P s hε hmean L hL hW z q j]
      exact integral_mono (int_lin P s hε z q j) (int_pos P s hε z q j) fun _ => le_max_left _ _
    · have h := int_lin_eq P s hε hmean L hL hW z q j
      have : ∫ ε, (z j - P.demand s q ε j) ∂(P.μ s) = z j - q j * P.lam s := by
        rw [integral_sub (integrable_const _) ((int_lin P s hε 0 q j).congr
          (Filter.Eventually.of_forall fun _ => by simp))]
        have h0 := int_lin_eq P s hε hmean L hL hW 0 q j
        simp only [Pi.zero_apply, sub_zero] at h0
        rw [h0]; simp
      rw [← this]
      exact integral_mono ((integrable_const _).sub ((int_lin P s hε 0 q j).congr
          (Filter.Eventually.of_forall fun _ => by simp))) (int_neg P s hε z q j)
        fun _ => le_max_left _ _
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hj j
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum] at hsum
  have hn := mul_le_mul_of_nonneg_left (norm_le_sum_abs z) hκ.le
  have hbI := mul_le_mul_of_nonneg_left hI hβ
  rw [hsplit]
  linarith

end Coercive


abbrev Tri (I J : Type) := (I → ℝ) × (J → ℝ) × (J → ℝ)

lemma dist_y (v v' : Tri I J) : ‖v.1 - v'.1‖ ≤ dist v v' := by
  rw [← dist_eq_norm, Prod.dist_eq]; exact le_max_left _ _

lemma dist_qn (v v' : Tri I J) : ‖v.2.2 - v'.2.2‖ ≤ dist v v' := by
  rw [← dist_eq_norm]
  have h2 : dist v.2.2 v'.2.2 ≤ dist v.2 v'.2 := by rw [Prod.dist_eq]; exact le_max_right _ _
  have h3 : dist v.2 v'.2 ≤ dist v v' := by rw [Prod.dist_eq (x := v)]; exact le_max_right _ _
  linarith

lemma dist_q (v v' : Tri I J) (j : J) : |v.2.2 j - v'.2.2 j| ≤ dist v v' := by
  have h1 := dist_le_pi_dist v.2.2 v'.2.2 j
  rw [Real.dist_eq] at h1
  have := dist_qn v v'
  rw [← dist_eq_norm] at this
  linarith

lemma dist_z (v v' : Tri I J) (j : J) : |v.2.1 j - v'.2.1 j| ≤ dist v v' := by
  have h1 := dist_le_pi_dist v.2.1 v'.2.1 j
  rw [Real.dist_eq] at h1
  have h2 : dist v.2.1 v'.2.1 ≤ dist v.2 v'.2 := by rw [Prod.dist_eq]; exact le_max_left _ _
  have h3 : dist v.2 v'.2 ≤ dist v v' := by rw [Prod.dist_eq (x := v)]; exact le_max_right _ _
  linarith

section Cont

variable (s : ℕ) [hμ : IsProbabilityMeasure (P.μ s)]
  (hε : ∀ j, Integrable (fun ε : J → ℝ => ε j) (P.μ s))
include hε

lemma cont_Ep (j : J) : Continuous (fun v : Tri I J =>
    ∫ ε, max (P.demand s v.2.2 ε j - v.2.1 j) 0 ∂(P.μ s)) := by
  have hk : Integrable (fun ε : J → ℝ => |P.lam s + ε j| + 1) (P.μ s) :=
    ((integrable_const _).add (hε j)).abs.add (integrable_const _)
  refine continuous_of_lip' _ (∫ ε, (|P.lam s + ε j| + 1) ∂(P.μ s)) fun v v' => ?_
  have := abs_integral_sub_le' _ _ (fun ε => (|P.lam s + ε j| + 1) * dist v v')
    (int_pos P s hε v.2.1 v.2.2 j) (int_pos P s hε v'.2.1 v'.2.2 j) (hk.mul_const _)
    (fun ε => by
      refine (abs_max_sub_max_le_abs _ _ 0).trans ?_
      have e : P.demand s v.2.2 ε j - v.2.1 j - (P.demand s v'.2.2 ε j - v'.2.1 j) =
          (v.2.2 j - v'.2.2 j) * (P.lam s + ε j) - (v.2.1 j - v'.2.1 j) := by
        simp [Params.demand]; ring
      rw [e]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul]
      have := dist_q v v' j
      have := dist_z v v' j
      have := abs_nonneg (P.lam s + ε j)
      nlinarith)
  rwa [integral_mul_const] at this

lemma cont_Em (j : J) : Continuous (fun v : Tri I J =>
    ∫ ε, max (v.2.1 j - P.demand s v.2.2 ε j) 0 ∂(P.μ s)) := by
  have hk : Integrable (fun ε : J → ℝ => |P.lam s + ε j| + 1) (P.μ s) :=
    ((integrable_const _).add (hε j)).abs.add (integrable_const _)
  refine continuous_of_lip' _ (∫ ε, (|P.lam s + ε j| + 1) ∂(P.μ s)) fun v v' => ?_
  have := abs_integral_sub_le' _ _ (fun ε => (|P.lam s + ε j| + 1) * dist v v')
    (int_neg P s hε v.2.1 v.2.2 j) (int_neg P s hε v'.2.1 v'.2.2 j) (hk.mul_const _)
    (fun ε => by
      refine (abs_max_sub_max_le_abs _ _ 0).trans ?_
      have e : v.2.1 j - P.demand s v.2.2 ε j - (v'.2.1 j - P.demand s v'.2.2 ε j) =
          (v.2.1 j - v'.2.1 j) - (v.2.2 j - v'.2.2 j) * (P.lam s + ε j) := by
        simp [Params.demand]; ring
      rw [e]
      refine (abs_sub _ _).trans ?_
      rw [abs_mul]
      have := dist_q v v' j
      have := dist_z v v' j
      have := abs_nonneg (P.lam s + ε j)
      nlinarith)
  rwa [integral_mul_const] at this

variable (L : ℝ) (hL : 0 ≤ L) (hW : ∀ x x', |P.V (s + 1) x - P.V (s + 1) x'| ≤ L * ‖x - x'‖)
include hL hW

lemma cont_I : Continuous (fun v : Tri I J =>
    ∫ ε, P.V (s + 1) (v.1 - P.A *ᵥ P.demand s v.2.2 ε) ∂(P.μ s)) := by
  set B := ∑ i, ∑ j, |P.A i j|
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hk : Integrable (fun ε : J → ℝ => L * (1 + B * ∑ j, |P.lam s + ε j|)) (P.μ s) :=
    ((integrable_const _).add ((int_E P s hε).const_mul _)).const_mul _
  refine continuous_of_lip' _ (∫ ε, L * (1 + B * ∑ j, |P.lam s + ε j|) ∂(P.μ s)) fun v v' => ?_
  have := abs_integral_sub_le' (fun ε => P.V (s + 1) (v.1 - P.A *ᵥ P.demand s v.2.2 ε))
    (fun ε => P.V (s + 1) (v'.1 - P.A *ᵥ P.demand s v'.2.2 ε))
    (fun ε => L * (1 + B * ∑ j, |P.lam s + ε j|) * dist v v')
    (int_V P s hε _ L hL hW v.1 v.2.2) (int_V P s hε _ L hL hW v'.1 v'.2.2) (hk.mul_const _)
    (fun ε => by
      refine (hW _ _).trans ?_
      have e : v.1 - P.A *ᵥ P.demand s v.2.2 ε - (v'.1 - P.A *ᵥ P.demand s v'.2.2 ε) =
          (v.1 - v'.1) - P.A *ᵥ (P.demand s v.2.2 ε - P.demand s v'.2.2 ε) := by
        rw [Matrix.mulVec_sub]; exact sub_sub_sub_comm _ _ _ _
      rw [e]
      have h1 := norm_sub_le (v.1 - v'.1) (P.A *ᵥ (P.demand s v.2.2 ε - P.demand s v'.2.2 ε))
      have h2 := norm_mulVec_le' P.A (P.demand s v.2.2 ε - P.demand s v'.2.2 ε)
      have h3 := demand_sub_norm P s v.2.2 v'.2.2 ε
      have h4 := dist_y v v'
      have h5 := dist_qn v v'
      have hE : 0 ≤ ∑ j, |P.lam s + ε j| := Finset.sum_nonneg fun j _ => abs_nonneg _
      have h6 : ‖v.2.2 - v'.2.2‖ * ∑ j, |P.lam s + ε j| ≤ dist v v' * ∑ j, |P.lam s + ε j| :=
        mul_le_mul_of_nonneg_right h5 hE
      have h7 : B * ‖P.demand s v.2.2 ε - P.demand s v'.2.2 ε‖ ≤
          B * (dist v v' * ∑ j, |P.lam s + ε j|) :=
        mul_le_mul_of_nonneg_left (h3.trans h6) hB
      have h8 : ‖v.1 - v'.1 - P.A *ᵥ (P.demand s v.2.2 ε - P.demand s v'.2.2 ε)‖ ≤
          (1 + B * ∑ j, |P.lam s + ε j|) * dist v v' := by
        calc _ ≤ dist v v' + B * (dist v v' * ∑ j, |P.lam s + ε j|) := by linarith
          _ = _ := by ring
      calc L * ‖v.1 - v'.1 - P.A *ᵥ (P.demand s v.2.2 ε - P.demand s v'.2.2 ε)‖
          ≤ L * ((1 + B * ∑ j, |P.lam s + ε j|) * dist v v') := mul_le_mul_of_nonneg_left h8 hL
        _ = _ := by ring)
  rwa [integral_mul_const] at this

lemma G_cont (hτc : ContinuousOn (P.τ s) P.Ω) :
    ContinuousOn (fun v : Tri I J => P.G s v.1 v.2.1 v.2.2) (univ ×ˢ univ ×ˢ P.Ω) := by
  have cτ : ContinuousOn (fun v : Tri I J => P.τ s v.2.2) (univ ×ˢ univ ×ˢ P.Ω) :=
    hτc.comp (by fun_prop : Continuous fun v : Tri I J => v.2.2).continuousOn
      (fun v hv => hv.2.2)
  have cmv : ∀ i, Continuous (fun v : Tri I J => (P.A *ᵥ v.2.2) i) := fun i =>
    (continuous_apply i).comp (Continuous.matrix_mulVec continuous_const (by fun_prop))
  have cmz : ∀ i, Continuous (fun v : Tri I J => (P.A *ᵥ v.2.1) i) := fun i =>
    (continuous_apply i).comp (Continuous.matrix_mulVec continuous_const (by fun_prop))
  have cA1 : Continuous (fun v : Tri I J => ∑ j, P.a s j * v.2.2 j) :=
    continuous_finsetSum _ fun j _ => continuous_const.mul (by fun_prop)
  have cA2 : Continuous (fun v : Tri I J => ∑ i, P.c s i * (P.A *ᵥ v.2.2) i) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (cmv i)
  have cLin : Continuous (fun v : Tri I J => ∑ i, P.cp s i * (v.1 - P.lam s • (P.A *ᵥ v.2.2)) i) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (by
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      exact ((continuous_apply i).comp continuous_fst).sub (continuous_const.mul (cmv i)))
  have cH1 : Continuous (fun v : Tri I J => ∑ j, P.bp s j *
      ∫ ε, max (P.demand s v.2.2 ε j - v.2.1 j) 0 ∂(P.μ s)) :=
    continuous_finsetSum _ fun j _ => continuous_const.mul (cont_Ep P s hε j)
  have cH2 : Continuous (fun v : Tri I J => ∑ i, P.h s i * ∑ j, P.A i j *
      ∫ ε, max (v.2.1 j - P.demand s v.2.2 ε j) 0 ∂(P.μ s)) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_finsetSum _ fun j _ =>
      continuous_const.mul (cont_Em P s hε j))
  have cH3 : Continuous (fun v : Tri I J => ∑ i, P.h s i * (v.1 - P.A *ᵥ v.2.1) i) :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (by
      simp only [Pi.sub_apply]
      exact ((continuous_apply i).comp continuous_fst).sub (cmz i))
  have cI := cont_I P s hε L hL hW
  simp only [Params.G, Params.Gm, Params.H, Params.profitRate]
  exact ((continuousOn_const.mul ((cτ.sub cA1.continuousOn).sub cA2.continuousOn)).sub
    cLin.continuousOn |>.sub ((cH1.add cH2).add cH3).continuousOn).add
    (continuousOn_const.mul cI.continuousOn)

end Cont


lemma V_last : P.V (P.T + 1) = fun _ => 0 := by
  funext x; simp [Params.V, Params.Vfrom]

lemma V_of_opt (t : ℕ) (ht : t ≤ P.T) (x y : I → ℝ) (z q : J → ℝ) (h : P.Opt9 t x y z q) :
    P.G t y z q = P.V t x := by
  rw [V_eq P t ht]
  have hg : IsGreatest (S9 P t x) (P.G t y z q) := ⟨⟨y, z, q, h.1, rfl⟩, by
    rintro v ⟨y', z', q', hf, rfl⟩; exact h.2 y' z' q' hf⟩
  exact hg.csSup_eq.symm

/-- the backward-induction invariant. -/
def Good (s : ℕ) : Prop :=
  ConcaveOn ℝ univ (P.V s) ∧ Antitone (P.V s) ∧
    (∃ L, 0 ≤ L ∧ ∀ x x', |P.V s x - P.V s x'| ≤ L * ‖x - x'‖) ∧
    (P.Coercive → ∃ U, ∀ x, P.V s x ≤ U)

lemma V_good (hS : P.Standing) : ∀ n s, s + n = P.T + 1 → 1 ≤ s → Good P s := by
  obtain ⟨hT, hβ0, hβ1, hA, hΩn, hΩc, hΩcv, hΩ0, hper⟩ := hS
  intro n
  induction n with
  | zero =>
    intro s hs _
    have : s = P.T + 1 := by omega
    subst this
    rw [Good, V_last]
    exact ⟨concaveOn_const 0 convex_univ, fun _ _ _ => le_rfl, ⟨0, le_rfl, fun _ _ => by simp⟩,
      fun _ => ⟨0, fun _ => le_rfl⟩⟩
  | succ n ih =>
    intro s hs h1
    have hsT : s ≤ P.T := by omega
    obtain ⟨hWc, hWa, ⟨L, hL, hW⟩, hWU⟩ := ih (s + 1) (by omega) (by omega)
    obtain ⟨hlam, hprob, hεi, hmean, _, hτ, hbp, hch, hh⟩ := hper s h1 hsT
    have := hprob
    obtain ⟨c1, c2, c3⟩ := V_step P s hεi L hL hW hsT hβ0.le hlam hτ hbp hh hA hch hΩcv hΩn
      hWa hWc
    refine ⟨c1, c2, c3, fun hC => ?_⟩
    obtain ⟨U, hU⟩ := hWU hC
    obtain ⟨hτc, hc1, hc2⟩ := hC s h1 hsT
    obtain ⟨κ, hκ, K, hK⟩ := G_coercive P s hεi hmean L hL hW hβ0.le hlam hτc hΩc hΩ0 hbp hh hA
      hch hWa hc1 hc2 U hU
    refine ⟨max K 0, fun x => ?_⟩
    rw [V_eq P s hsT]
    refine Real.sSup_le ?_ (le_max_right _ _)
    rintro v ⟨y, z, q, ⟨f1, f2, f3⟩, rfl⟩
    have := hK y z q f3 f1
    have := mul_nonneg hκ.le (norm_nonneg z)
    exact (by linarith : P.G s y z q ≤ K).trans (le_max_left _ _)


theorem main_thm (hS : P.Standing) (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) :
    (ConcaveOn ℝ Set.univ (P.V (t + 1)) ∧ Antitone (P.V (t + 1))) ∧
    ConcaveOn ℝ (Set.univ ×ˢ Set.univ ×ˢ P.Ω)
      (fun v : (I → ℝ) × (J → ℝ) × (J → ℝ) => P.G t v.1 v.2.1 v.2.2) ∧
    (∀ (x : I → ℝ) (z q : J → ℝ), P.Max14 t ∅ 0 (P.A *ᵥ z) z q → x ≤ P.A *ᵥ z →
      P.Opt9 t x (P.A *ᵥ z) z q ∧ P.G t (P.A *ᵥ z) z q = P.V t x) ∧
    (P.Coercive →
      (∃ (z q : J → ℝ), P.Max14 t ∅ 0 (P.A *ᵥ z) z q) ∧
      ∀ x : I → ℝ, (∀ (z q : J → ℝ), P.Max14 t ∅ 0 (P.A *ᵥ z) z q → ¬ x ≤ P.A *ᵥ z) →
        ∃ S : Finset I, S.Nonempty ∧ ∃ (y : I → ℝ) (z q : J → ℝ),
          P.Max14 t S x y z q ∧ P.Opt9 t x y z q ∧ P.G t y z q = P.V t x) := by
  classical
  obtain ⟨hVc, hVa, ⟨L, hL, hW⟩, hVU⟩ := V_good P hS (P.T - t) (t + 1) (by omega) (by omega)
  obtain ⟨hT, hβ0, hβ1, hA, hΩn, hΩc, hΩcv, hΩ0, hper⟩ := hS
  obtain ⟨hlam, hprob, hεi, hmean, _, hτ, hbp, hch, hh⟩ := hper t ht1 htT
  have := hprob
  have hanti := G_antitone P t hεi L hL hW hβ0.le hch hVa
  have hcomb := G_comb P t hεi L hL hW hβ0.le hlam hτ hbp hh hA hVc
  refine ⟨⟨hVc, hVa⟩, ⟨convex_univ.prod (convex_univ.prod hΩcv), ?_⟩, ?_, ?_⟩
  · rintro ⟨y, z, q⟩ hv ⟨y', z', q'⟩ hv' a b ha hb hab
    simp only [smul_eq_mul, Prod.smul_mk, Prod.mk_add_mk]
    exact hcomb y y' z z' q q' hv.2.2 hv'.2.2 a b ha hb hab
  · intro x z q hmax hx
    have hopt : P.Opt9 t x (P.A *ᵥ z) z q := by
      refine ⟨⟨le_rfl, hx, hmax.1.2.2.2⟩, fun y' z' q' hf => ?_⟩
      have h1 : P.G t y' z' q' ≤ P.G t (P.A *ᵥ z') z' q' := hanti z' q' hf.1
      exact h1.trans (hmax.2 _ z' q' ⟨fun i hi => absurd hi (Finset.notMem_empty i),
        fun i _ => rfl, le_rfl, hf.2.2⟩)
    exact ⟨hopt, V_of_opt P t htT x _ z q hopt⟩
  · intro hC
    obtain ⟨U, hU⟩ := hVU hC
    obtain ⟨hτc, hc1, hc2⟩ := hC t ht1 htT
    obtain ⟨κ, hκ, K, hK⟩ := G_coercive P t hεi hmean L hL hW hβ0.le hlam hτc hΩc hΩ0 hbp hh hA
      hch hVa hc1 hc2 U hU
    have hGc := G_cont P t hεi L hL hW hτc
    refine ⟨?_, ?_⟩
    · -- existence of a maximizer of (14) with I⁺ = ∅
      have hFc : ContinuousOn (fun p : (J → ℝ) × (J → ℝ) => P.G t (P.A *ᵥ p.1) p.1 p.2)
          (univ ×ˢ P.Ω) :=
        hGc.comp (f := fun p : (J → ℝ) × (J → ℝ) => (P.A *ᵥ p.1, p.1, p.2))
          (Continuous.continuousOn (by
            refine Continuous.prodMk (Continuous.matrix_mulVec continuous_const continuous_fst)
              continuous_id))
          (fun p hp => ⟨trivial, trivial, hp.2⟩)
      obtain ⟨z, q, hq, hmx⟩ := exists_max_coercive P.Ω hΩc hΩn _ hFc κ K hκ
        (fun z q hq => hK _ z q hq le_rfl)
      refine ⟨z, q, ⟨fun i hi => absurd hi (Finset.notMem_empty i), fun i _ => rfl, le_rfl, hq⟩,
        fun y' z' q' hf => ?_⟩
      have hy' : y' = P.A *ᵥ z' := funext fun i => hf.2.1 i (Finset.notMem_empty i)
      subst hy'
      exact hmx z' q' hf.2.2.2
    · intro x hno
      have hFc : ContinuousOn (fun p : (J → ℝ) × (J → ℝ) => P.G t (x ⊔ P.A *ᵥ p.1) p.1 p.2)
          (univ ×ˢ P.Ω) :=
        hGc.comp (f := fun p : (J → ℝ) × (J → ℝ) => (x ⊔ P.A *ᵥ p.1, p.1, p.2))
          (Continuous.continuousOn (by
            refine Continuous.prodMk (continuous_pi fun i => ?_) continuous_id
            simp only [Pi.sup_apply]
            exact continuous_const.sup ((continuous_apply i).comp
              (Continuous.matrix_mulVec continuous_const continuous_fst))))
          (fun p hp => ⟨trivial, trivial, hp.2⟩)
      obtain ⟨z, q, hq, hmx⟩ := exists_max_coercive P.Ω hΩc hΩn _ hFc κ K hκ
        (fun z q hq => hK _ z q hq le_sup_right)
      set y := x ⊔ P.A *ᵥ z with hydef
      have hopt : P.Opt9 t x y z q := by
        refine ⟨⟨le_sup_right, le_sup_left, hq⟩, fun y' z' q' hf => ?_⟩
        have h1 : P.G t y' z' q' ≤ P.G t (x ⊔ P.A *ᵥ z') z' q' := hanti z' q' (sup_le hf.2.1 hf.1)
        exact h1.trans (hmx z' q' hf.2.2)
      set S : Finset I := Finset.univ.filter (fun i => (P.A *ᵥ z) i ≤ x i) with hSdef
      have hyS : ∀ i ∈ S, y i = x i := by
        intro i hi
        simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp [hydef, Pi.sup_apply, hi]
      have hyN : ∀ i, i ∉ S → y i = (P.A *ᵥ z) i := by
        intro i hi
        simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
        simp [hydef, Pi.sup_apply, hi.le]
      have hgap : ∀ i, i ∉ S → x i < y i := by
        intro i hi
        rw [hyN i hi]
        simpa [hSdef] using hi
      have hf14 : P.Feas14 S x y z q := ⟨hyS, hyN, le_sup_right, hq⟩
      have hmax14 : ∀ (y' : I → ℝ) (z' q' : J → ℝ), P.Feas14 S x y' z' q' →
          P.G t y' z' q' ≤ P.G t y z q := by
        intro y' z' q' hf
        by_contra hlt
        push_neg at hlt
        obtain ⟨δ, hδ, hδi⟩ := exists_kappa (fun i => if i ∈ S then 1 else y i - x i)
          (fun i => if i ∈ S then 1 else y i - x i)
          (fun i => by split_ifs with h; exact one_pos; exact sub_pos.2 (hgap i h))
          (fun i => by split_ifs with h; exact one_pos; exact sub_pos.2 (hgap i h))
        set D := (∑ i, |y i - y' i|) + 1 with hD
        have hD0 : 0 < D := by
          have := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => abs_nonneg (y i - y' i)
          linarith
        set θ := min (1 / 2) (δ / D) with hθ
        have hθ0 : 0 < θ := lt_min (by norm_num) (div_pos hδ hD0)
        have hθ1 : θ ≤ 1 / 2 := min_le_left _ _
        have hθD : θ * D ≤ δ := by
          have := min_le_right (1 / 2 : ℝ) (δ / D)
          rw [← hθ] at this
          calc θ * D ≤ δ / D * D := mul_le_mul_of_nonneg_right this hD0.le
            _ = δ := by field_simp
        have hfeas : P.Feas9 x ((1 - θ) • y + θ • y') ((1 - θ) • z + θ • z')
            ((1 - θ) • q + θ • q') := by
          refine ⟨?_, ?_, hΩcv hq hf.2.2.2 (by linarith) hθ0.le (by ring)⟩
          · rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
            exact add_le_add (smul_le_smul_of_nonneg_left (le_sup_right : P.A *ᵥ z ≤ y)
              (by linarith)) (smul_le_smul_of_nonneg_left hf.2.2.1 hθ0.le)
          · intro i
            simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
            by_cases hi : i ∈ S
            · rw [hyS i hi, hf.1 i hi]; ring_nf; exact le_rfl
            · have hgi := hδi i
              simp only [hi, if_false] at hgi
              have hdi : y i - y' i ≤ D - 1 := by
                have := Finset.single_le_sum (f := fun i => |y i - y' i|)
                  (fun i _ => abs_nonneg _) (Finset.mem_univ i)
                have := le_abs_self (y i - y' i)
                simp only at *
                linarith
              have : θ * (y i - y' i) ≤ θ * D := mul_le_mul_of_nonneg_left (by linarith) hθ0.le
              nlinarith [hgi.1]
        have hc := hcomb y y' z z' q q' hq hf.2.2.2 (1 - θ) θ (by linarith) hθ0.le (by ring)
        have hle := hopt.2 _ _ _ hfeas
        nlinarith
      have hne : S.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hS0
        have hyA : y = P.A *ᵥ z := funext fun i => hyN i (by rw [hS0]; exact Finset.notMem_empty i)
        refine hno z q ⟨⟨fun i hi => absurd hi (Finset.notMem_empty i), fun i _ => rfl, le_rfl, hq⟩,
          fun y' z' q' hf => ?_⟩ (hyA ▸ (le_sup_left : x ≤ y))
        rw [← hyA]
        exact hmax14 y' z' q' ⟨fun i hi => absurd hi (by rw [hS0]; exact Finset.notMem_empty i),
          fun i hi => hf.2.1 i (Finset.notMem_empty i), hf.2.2.1, hf.2.2.2⟩
      exact ⟨S, hne, y, z, q, ⟨hf14, hmax14⟩, hopt, V_of_opt P t htT x y z q hopt⟩

end NOSAux

open BundleShaping.NoOrderSet in
theorem solution {I J : Type} [Fintype I] [Fintype J] (P : Params I J) (hS : P.Standing) (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) : ConcaveOn ℝ (Set.univ ×ˢ Set.univ ×ˢ P.Ω) (fun v : (I → ℝ) × (J → ℝ) × (J → ℝ) => P.G t v.1 v.2.1 v.2.2) :=
  (NOSAux.main_thm P hS t ht1 htT).2.1
