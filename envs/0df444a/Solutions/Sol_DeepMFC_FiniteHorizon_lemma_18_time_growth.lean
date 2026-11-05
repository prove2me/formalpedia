-- Prove2me | solution 1 for DeepMFC.FiniteHorizon.lemma_18_time_growth
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T21:37:08.438272+00:00
-- url     : https://prove2.me/submissions/87519f0d-1cf8-41db-9d9b-804bd7876138

import Mathlib
import Definitions.Def_DeepMFC_FiniteHorizon_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open DeepMFC.FiniteHorizon

namespace DeepMFCLemma18Fixed

lemma dot_eq {n : ℕ} (u v : Fin n → ℝ) : dot u v = u ⬝ᵥ v := rfl

lemma abs_dot_le {n : ℕ} (u v : Fin n → ℝ) : |dot u v| ≤ n * (‖u‖ * ‖v‖) := by
  unfold dot
  calc |∑ i, u i * v i| ≤ ∑ i, |u i * v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ‖u‖ * ‖v‖ := by
        apply Finset.sum_le_sum; intro i _
        rw [abs_mul]
        have h1 := norm_le_pi_norm u i
        have h2 := norm_le_pi_norm v i
        rw [Real.norm_eq_abs] at h1 h2
        exact mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    _ = n * (‖u‖ * ‖v‖) := by simp

lemma dotL_apply {n : ℕ} (v w : Fin n → ℝ) : dotL v w = dot v w := by
  simp [dotL, dot]

/-- First-order condition for the minimizer. -/
lemma foc {d k : ℕ} (M : Model d k) (D : Deriv d k) (hC : Coeff M D)
    (αhat : ℝ → E d → Measure (E d) → E d → Fin k → ℝ) (hmin : IsMinimizer M αhat)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) M.T) (x : E d) (μ : Measure (E d)) (y : E d)
    (hμ : IsP2 μ) (h : Fin k → ℝ) :
    dot (D.fα t x μ (αhat t x μ y)) h + dot ((D.b2 t).mulVec h) y = 0 := by
  set a0 := αhat t x μ y
  set c : E d := D.b0 t + (D.b1 t).mulVec x + (D.b1bar t).mulVec (mean μ)
  let g : ℝ → ℝ := fun s => M.Htilde t x μ y (a0 + s • h)
  have hg : ∀ s, g s = (dot (c + (D.b2 t).mulVec a0) y + s * dot ((D.b2 t).mulVec h) y)
      + M.f t x μ (a0 + s • h) := by
    intro s
    simp only [g, Model.Htilde]
    rw [(hC.a1.1 t ht x μ (a0 + s • h) hμ).1]
    congr 1
    simp only [dot_eq, Matrix.mulVec_add, Matrix.mulVec_smul, c]
    simp [add_dotProduct, smul_dotProduct]
    ring
  -- derivative of the f part
  have hf := hC.a2.1 t ht x μ a0 hμ
  have hpath : HasDerivAt (fun s : ℝ => (x, a0 + s • h)) ((0 : E d), h) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => a0 + s • h) h 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add a0
    exact (hasDerivAt_const (0 : ℝ) x).prodMk h1
  have hf' : HasDerivAt (fun s : ℝ => M.f t x μ (a0 + s • h)) (dot (D.fα t x μ a0) h) 0 := by
    have hpath' : HasDerivAt (fun s : ℝ => (x, a0 + s • h)) ((0 : E d), h) 0 := hpath
    have hf2 : HasFDerivAt (fun p : E d × (Fin k → ℝ) => M.f t p.1 μ p.2)
        ((dotL (D.fx t x μ a0)).coprod (dotL (D.fα t x μ a0))) (x, a0 + (0 : ℝ) • h) := by
      simpa using hf
    have h3 := hf2.comp_hasDerivAt (0 : ℝ) hpath'
    have e : ((dotL (D.fx t x μ a0)).coprod (dotL (D.fα t x μ a0))) ((0 : E d), h)
        = dot (D.fα t x μ a0) h := by
      rw [ContinuousLinearMap.coprod_apply, dotL_apply, dotL_apply]; simp [dot]
    rw [e] at h3; exact h3
  have hlin : HasDerivAt (fun s : ℝ => dot (c + (D.b2 t).mulVec a0) y
      + s * dot ((D.b2 t).mulVec h) y) (dot ((D.b2 t).mulVec h) y) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (dot ((D.b2 t).mulVec h) y)).const_add
      (dot (c + (D.b2 t).mulVec a0) y)
  have hderiv : HasDerivAt g (dot ((D.b2 t).mulVec h) y + dot (D.fα t x μ a0) h) 0 := by
    have e : g = (fun s : ℝ => dot (c + (D.b2 t).mulVec a0) y
      + s * dot ((D.b2 t).mulVec h) y) + (fun s : ℝ => M.f t x μ (a0 + s • h)) := funext hg
    rw [e]; exact hlin.add hf'
  have hloc : IsLocalMin g 0 := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    show g 0 ≤ g s
    have : g 0 = M.Htilde t x μ y a0 := by simp [g]
    rw [this]
    exact hmin t ht x μ y hμ _
  have := hloc.hasDerivAt_eq_zero hderiv
  linarith

/-- Strong monotonicity of `∂_α f` from (A4). -/
lemma mono {d k : ℕ} (M : Model d k) (D : Deriv d k) (hC : Coeff M D) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ (x : E d) (μ : Measure (E d))
      (a a' : Fin k → ℝ), IsP2 μ →
      2 * lam * ‖a' - a‖ ^ 2 ≤ dot (D.fα t x μ a' - D.fα t x μ a) (a' - a) := by
  obtain ⟨lam, hlam, hf, -⟩ := hC.a4
  refine ⟨lam, hlam, fun t ht x μ a a' hμ => ?_⟩
  have hmeas : Measurable (fun z : E d => (z, z)) := measurable_id.prodMk measurable_id
  set π : Measure (E d × E d) := μ.map (fun z => (z, z))
  have hcpl : IsCoupling μ μ π := by
    constructor
    · rw [Measure.map_map measurable_fst hmeas]; simp [Function.comp_def]
    · rw [Measure.map_map measurable_snd hmeas]; simp [Function.comp_def]
  have hdiag : ∀ F : E d → E d, ∫ p, dot (F p.1) (p.2 - p.1) ∂π = 0 := by
    intro F
    have hae : ∀ᵐ p ∂π, p.1 = p.2 := by
      rw [ae_map_iff hmeas.aemeasurable]
      · exact Filter.Eventually.of_forall (fun z => rfl)
      · exact (isClosed_eq continuous_fst continuous_snd).measurableSet
    have : (fun p : E d × E d => dot (F p.1) (p.2 - p.1)) =ᵐ[π] fun _ => 0 := by
      filter_upwards [hae] with p hp
      rw [hp]; simp [dot]
    rw [integral_congr_ae this]; simp
  have h1 := hf t ht x x μ μ a a' hμ hμ π hcpl
  have h2 := hf t ht x x μ μ a' a hμ hμ π hcpl
  rw [hdiag] at h1 h2
  have e1 : dot (D.fx t x μ a) (x - x) = 0 := by simp [dot]
  have e2 : dot (D.fx t x μ a') (x - x) = 0 := by simp [dot]
  have e3 : ‖a - a'‖ = ‖a' - a‖ := norm_sub_rev _ _
  have e4 : dot (D.fα t x μ a') (a - a') = - dot (D.fα t x μ a') (a' - a) := by
    simp only [dot_eq]; rw [← dotProduct_neg, neg_sub]
  have e5 : dot (D.fα t x μ a' - D.fα t x μ a) (a' - a)
      = dot (D.fα t x μ a') (a' - a) - dot (D.fα t x μ a) (a' - a) := by
    simp only [dot_eq, sub_dotProduct]
  rw [e1] at h1; rw [e2, e3, e4] at h2
  rw [e5]
  linarith

end DeepMFCLemma18Fixed

open DeepMFCLemma18Fixed in
theorem solution {d k : ℕ} (M : Model d k) (D : Deriv d k) (hC : Coeff M D)
    (αhat : ℝ → E d → Measure (E d) → E d → Fin k → ℝ) (hmin : IsMinimizer M αhat) :
    ∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ t' ∈ Set.Icc (0 : ℝ) M.T,
      ∀ (x x' : E d) (μ μ' : Measure (E d)) (y y' : E d), IsP2 μ → IsP2 μ' →
        ‖αhat t x μ y - αhat t' x' μ' y'‖
          ≤ L * ((1 + ‖y'‖) * |t - t'| + ‖x - x'‖ + (W2 μ μ').toReal + ‖y - y'‖) := by
  obtain ⟨lam, hlam, hmono⟩ := mono M D hC
  obtain ⟨L3, hL3⟩ := hC.a3
  obtain ⟨LB, hLB⟩ := hC.b1
  have hb2 := hC.a1.2.2.2.2.1
  choose Cb hCb using hb2
  set B : ℝ := ∑ i, ∑ j, |Cb i j| with hBdef
  have hCbB : ∀ i j, |Cb i j| ≤ B := by
    intro i j
    have h1 : |Cb i j| ≤ ∑ j', |Cb i j'| :=
      Finset.single_le_sum (f := fun j' => |Cb i j'|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)
    have h2 : ∑ j', |Cb i j'| ≤ B :=
      Finset.single_le_sum (f := fun i' => ∑ j', |Cb i' j'|)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i)
    linarith
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  set K : ℝ := k * (|L3| + |LB|) + d * k * B with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K / (2 * lam), ?_⟩
  intro t ht t' ht' x x' μ μ' y y' hμ hμ'
  set a := αhat t x μ y
  set a' := αhat t' x' μ' y'
  set u := a' - a with hu
  set W : ℝ := (W2 μ μ').toReal
  have hW : 0 ≤ W := ENNReal.toReal_nonneg
  set S : ℝ := (1 + ‖y'‖) * |t - t'| + ‖x - x'‖ + W + ‖y - y'‖ with hS
  have hS0 : 0 ≤ S := by positivity
  -- first-order conditions
  have F1 := foc M D hC αhat hmin t ht x μ y hμ u
  have F2 := foc M D hC αhat hmin t' ht' x' μ' y' hμ' u
  -- monotonicity at (t, x, μ)
  have hm := hmono t ht x μ a a' hμ
  -- Lipschitz bound on ∂_α f
  have hfa : ‖D.fα t x μ a' - D.fα t' x' μ' a'‖ ≤ |L3| * (‖x - x'‖ + W) + |LB| * |t - t'| := by
    have h1 := (hL3 t ht x x' μ μ' a' a' hμ hμ').2.1
    have h2 := hLB μ' a' hμ' t ht t' ht' x' x'
    simp only [sub_self, norm_zero, add_zero] at h1 h2
    rw [norm_sub_rev] at h1
    rw [norm_sub_rev x' x] at h1
    have h1' : ‖D.fα t x μ a' - D.fα t x' μ' a'‖ ≤ |L3| * (‖x - x'‖ + W) :=
      h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
    have h2' : ‖D.fα t x' μ' a' - D.fα t' x' μ' a'‖ ≤ |LB| * |t - t'| :=
      h2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _))
    calc ‖D.fα t x μ a' - D.fα t' x' μ' a'‖
        = ‖(D.fα t x μ a' - D.fα t x' μ' a') + (D.fα t x' μ' a' - D.fα t' x' μ' a')‖ := by
          congr 1; abel
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add h1' h2'
  -- the b₂ part
  have hbpart : |dot ((D.b2 t).mulVec u) y - dot ((D.b2 t').mulVec u) y'|
      ≤ d * k * B * ‖u‖ * (‖y - y'‖ + |t - t'| * ‖y'‖) := by
    have hexp : dot ((D.b2 t).mulVec u) y - dot ((D.b2 t').mulVec u) y'
        = ∑ i, ∑ j, u j * (D.b2 t i j * (y i - y' i) + (D.b2 t i j - D.b2 t' i j) * y' i) := by
      simp only [dot, Matrix.mulVec, dotProduct, Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _
      ring
    rw [hexp]
    have hterm : ∀ i j, |u j * (D.b2 t i j * (y i - y' i) + (D.b2 t i j - D.b2 t' i j) * y' i)|
        ≤ ‖u‖ * (B * ‖y - y'‖ + B * |t - t'| * ‖y'‖) := by
      intro i j
      obtain ⟨hb1, -⟩ := hCb i j t ht t ht
      obtain ⟨-, hb2'⟩ := hCb i j t ht t' ht'
      have hu1 : |u j| ≤ ‖u‖ := by
        have := norm_le_pi_norm u j; rwa [Real.norm_eq_abs] at this
      have hy1 : |y i - y' i| ≤ ‖y - y'‖ := by
        have := norm_le_pi_norm (y - y') i; rwa [Real.norm_eq_abs] at this
      have hy2 : |y' i| ≤ ‖y'‖ := by
        have := norm_le_pi_norm y' i; rwa [Real.norm_eq_abs] at this
      have hc1 : |D.b2 t i j| ≤ B := hb1.trans ((le_abs_self _).trans (hCbB i j))
      have hc2 : |D.b2 t i j - D.b2 t' i j| ≤ B * |t - t'| :=
        hb2'.trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (hCbB i j))
          (abs_nonneg _))
      rw [abs_mul]
      apply mul_le_mul hu1 _ (abs_nonneg _) (norm_nonneg _)
      calc |D.b2 t i j * (y i - y' i) + (D.b2 t i j - D.b2 t' i j) * y' i|
          ≤ |D.b2 t i j * (y i - y' i)| + |(D.b2 t i j - D.b2 t' i j) * y' i| := abs_add_le _ _
        _ = |D.b2 t i j| * |y i - y' i| + |D.b2 t i j - D.b2 t' i j| * |y' i| := by
            rw [abs_mul, abs_mul]
        _ ≤ B * ‖y - y'‖ + (B * |t - t'|) * ‖y'‖ := by
            apply add_le_add
            · exact mul_le_mul hc1 hy1 (abs_nonneg _) hB0
            · exact mul_le_mul hc2 hy2 (abs_nonneg _) (by positivity)
    calc |∑ i, ∑ j, u j * (D.b2 t i j * (y i - y' i) + (D.b2 t i j - D.b2 t' i j) * y' i)|
        ≤ ∑ i, |∑ j, u j * (D.b2 t i j * (y i - y' i) + (D.b2 t i j - D.b2 t' i j) * y' i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |u j * (D.b2 t i j * (y i - y' i) + (D.b2 t i j - D.b2 t' i j) * y' i)| :=
          Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin d, ∑ _j : Fin k, ‖u‖ * (B * ‖y - y'‖ + B * |t - t'| * ‖y'‖) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
      _ = d * k * B * ‖u‖ * (‖y - y'‖ + |t - t'| * ‖y'‖) := by
          simp; ring
  -- the key identity
  have hkey : dot (D.fα t x μ a' - D.fα t x μ a) u
      = dot (D.fα t x μ a' - D.fα t' x' μ' a') u
        + (dot ((D.b2 t).mulVec u) y - dot ((D.b2 t').mulVec u) y') := by
    have e : dot (D.fα t x μ a' - D.fα t x μ a) u
        = dot (D.fα t x μ a' - D.fα t' x' μ' a') u + dot (D.fα t' x' μ' a') u
          - dot (D.fα t x μ a) u := by
      simp only [dot_eq, sub_dotProduct]; ring
    rw [e]; linarith
  have hd1 := abs_dot_le (D.fα t x μ a' - D.fα t' x' μ' a') u
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg _
  -- combine: 2 λ ‖u‖² ≤ K ‖u‖ S
  have hmain : 2 * lam * ‖u‖ ^ 2 ≤ K * S * ‖u‖ := by
    have hA : dot (D.fα t x μ a' - D.fα t' x' μ' a') u
        ≤ k * ((|L3| * (‖x - x'‖ + W) + |LB| * |t - t'|) * ‖u‖) := by
      have := (le_abs_self _).trans hd1
      refine this.trans ?_
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right hfa hu0
    have hBp := (le_abs_self _).trans hbpart
    have hsum : 2 * lam * ‖u‖ ^ 2 ≤ k * ((|L3| * (‖x - x'‖ + W) + |LB| * |t - t'|) * ‖u‖)
        + d * k * B * ‖u‖ * (‖y - y'‖ + |t - t'| * ‖y'‖) := by
      have := hm; rw [← hu] at this; linarith
    refine hsum.trans ?_
    have ht0 : 0 ≤ |t - t'| := abs_nonneg _
    have hy0 : 0 ≤ ‖y'‖ := norm_nonneg _
    have hxx : 0 ≤ ‖x - x'‖ := norm_nonneg _
    have hyy : 0 ≤ ‖y - y'‖ := norm_nonneg _
    have hL3' : 0 ≤ |L3| := abs_nonneg _
    have hLB' : 0 ≤ |LB| := abs_nonneg _
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    -- each piece is bounded by its share of K * S
    have p1 : |L3| * (‖x - x'‖ + W) + |LB| * |t - t'| ≤ (|L3| + |LB|) * S := by
      rw [hS]; nlinarith [mul_nonneg hy0 ht0]
    have p2 : ‖y - y'‖ + |t - t'| * ‖y'‖ ≤ S := by
      rw [hS]; nlinarith [mul_nonneg hy0 ht0]
    have q1 : k * ((|L3| * (‖x - x'‖ + W) + |LB| * |t - t'|) * ‖u‖)
        ≤ k * ((|L3| + |LB|) * S * ‖u‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right p1 hu0) hk
    have q2 : d * k * B * ‖u‖ * (‖y - y'‖ + |t - t'| * ‖y'‖) ≤ d * k * B * ‖u‖ * S :=
      mul_le_mul_of_nonneg_left p2 (by positivity)
    calc _ ≤ k * ((|L3| + |LB|) * S * ‖u‖) + d * k * B * ‖u‖ * S := add_le_add q1 q2
      _ = K * S * ‖u‖ := by rw [hK]; ring
  -- conclude
  have hgoal : ‖u‖ ≤ K / (2 * lam) * S := by
    rcases hu0.eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      have : 2 * lam * ‖u‖ ^ 2 = (‖u‖ * (2 * lam)) * ‖u‖ := by ring
      rw [this] at hmain
      exact le_of_mul_le_mul_right hmain hpos
  have : ‖a - a'‖ = ‖u‖ := by rw [hu, norm_sub_rev]
  rw [this]
  exact hgoal
