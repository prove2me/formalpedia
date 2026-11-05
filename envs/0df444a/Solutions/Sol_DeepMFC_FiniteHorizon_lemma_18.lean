-- Prove2me | solution 1 for DeepMFC.FiniteHorizon.lemma_18
-- status  : ACCEPTED   (disprove)
-- author  : @tianyipeng
-- created : 2026-11-04T21:30:23.328708+00:00
-- url     : https://prove2.me/submissions/dd23aca7-0470-4474-b343-0902ebfc2e1a

import Mathlib
import Definitions.Def_DeepMFC_FiniteHorizon_Assumptions

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open DeepMFC.FiniteHorizon

namespace DeepMFCLemma18Counter

/-- Coefficients: everything zero except `b₂(t) = t` and `∂_α f = 2α`. -/
noncomputable def D0 : Deriv 1 1 where
  b0 := fun _ => 0
  b1 := fun _ => 0
  b1bar := fun _ => 0
  b2 := fun t => fun _ _ => t
  σ0 := fun _ => 0
  σ1 := fun _ _ => 0
  σ1bar := fun _ _ => 0
  fx := fun _ _ _ _ => 0
  fα := fun _ _ _ a => (2 : ℝ) • a
  fμ := fun _ _ _ _ _ => 0
  gx := fun _ _ => 0
  gμ := fun _ _ _ => 0
  ft := fun _ _ _ _ => 0
  fxx := fun _ _ _ _ => 0
  fxα := fun _ _ _ _ => 0
  fαα := fun _ _ _ _ => (2 : ℝ) • ContinuousLinearMap.id ℝ (Fin 1 → ℝ)
  fxμ := fun _ _ _ _ _ => 0
  fαμ := fun _ _ _ _ _ => 0
  fvμ := fun _ _ _ _ _ => 0
  fμμ := fun _ _ _ _ _ _ _ => 0

noncomputable def M0 : Model 1 1 where
  T := 1
  hT := one_pos
  b := fun t x μ a => D0.b0 t + (D0.b1 t).mulVec x + (D0.b1bar t).mulVec (mean μ) + (D0.b2 t).mulVec a
  σ := fun t x μ => D0.σ0 t + ∑ j, x j • D0.σ1 t j + ∑ j, mean μ j • D0.σ1bar t j
  f := fun _ _ _ a => (a 0) ^ 2
  g := fun _ _ => 0
  μ0 := Measure.dirac 0
  hμ0 := inferInstance

lemma norm_fin1 (v : Fin 1 → ℝ) : ‖v‖ = |v 0| := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 ?_
    intro i
    rw [Subsingleton.elim i 0, Real.norm_eq_abs]
  · have := norm_le_pi_norm v 0
    rwa [Real.norm_eq_abs] at this

lemma dotL_zero {n : ℕ} : dotL (0 : Fin n → ℝ) = 0 := by
  simp [dotL]

lemma isLDeriv_const {d : ℕ} (c : ℝ) :
    IsLDeriv (d := d) (fun _ => c) (fun _ _ => 0) := by
  intro ϑ₀ _ ε hε
  refine ⟨1, one_pos, ?_⟩
  intro ϑ _ _
  have : (fun ω => dot (0 : E d) (ϑ ω - ϑ₀ ω)) = fun _ => 0 := by
    funext ω; simp [dot]
  simp only [this, integral_zero, sub_self, abs_zero]
  exact mul_nonneg hε.le ENNReal.toReal_nonneg

lemma M2_nonneg {d : ℕ} (μ : Measure (E d)) : 0 ≤ M2 μ := by
  unfold M2
  apply Real.rpow_nonneg
  exact integral_nonneg (fun _ => by positivity)

lemma bddLip_zero (T : ℝ≥0) : BddLipOn T (fun _ => 0) :=
  ⟨0, fun _ _ _ _ => by simp⟩

lemma hC0 : Coeff M0 D0 where
  a1 := by
    refine ⟨fun t _ x μ a _ => ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i; exact bddLip_zero _
    · intro i j; exact bddLip_zero _
    · intro i j; exact bddLip_zero _
    · intro i j
      refine ⟨1, fun t ht s _ => ⟨?_, ?_⟩⟩
      · show |t| ≤ 1
        have h1 : t ≤ 1 := by simpa [M0] using ht.2
        rw [abs_le]; constructor <;> linarith [ht.1]
      · show |t - s| ≤ 1 * |t - s|
        simp
    · intro i j; exact bddLip_zero _
    · intro l i j; exact bddLip_zero _
    · intro l i j; exact bddLip_zero _
  a2 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t _ x μ a _
      show HasFDerivAt (fun p : E 1 × (Fin 1 → ℝ) => (p.2 0) ^ 2)
        ((dotL (0 : E 1)).coprod (dotL ((2 : ℝ) • a))) (x, a)
      have h1 : HasFDerivAt (fun p : E 1 × (Fin 1 → ℝ) => p.2 0)
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp
            (ContinuousLinearMap.snd ℝ (E 1) (Fin 1 → ℝ))) (x, a) :=
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).comp
            (ContinuousLinearMap.snd ℝ (E 1) (Fin 1 → ℝ))).hasFDerivAt
      have h2 := h1.pow 2
      refine h2.congr_fderiv ?_
      refine ContinuousLinearMap.ext fun p => ?_
      simp [dotL, ContinuousLinearMap.coprod_apply]
    · intro t _ x a
      exact isLDeriv_const _
    · intro x μ _
      show HasFDerivAt (fun _ : E 1 => (0 : ℝ)) (dotL (0 : E 1)) x
      rw [dotL_zero]; exact hasFDerivAt_const _ _
    · intro x
      exact isLDeriv_const _
    · exact ⟨0, fun t _ => by simp [M0]⟩
    · refine ⟨2, fun R hR t _ x μ a _ _ _ ha => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
      · show ‖(0 : E 1)‖ ≤ 2 * (1 + R); simp; linarith
      · show ‖(0 : E 1)‖ ≤ 2 * (1 + R); simp; linarith
      · show ‖(2 : ℝ) • a‖ ≤ 2 * (1 + R)
        rw [norm_smul]; norm_num; linarith
      · show ∫⁻ x', ‖(0 : E 1)‖ₑ ^ 2 ∂μ ≤ _; simp
      · show ∫⁻ x', ‖(0 : E 1)‖ₑ ^ 2 ∂μ ≤ _; simp
  a3 := by
    refine ⟨2, fun t _ x x' μ μ' a a' _ _ => ⟨?_, ?_, ?_, ?_⟩⟩
    · show ‖(0 : E 1) - 0‖ ≤ _
      simp only [sub_self, norm_zero]
      have := ENNReal.toReal_nonneg (a := W2 μ μ')
      positivity
    · show ‖(2 : ℝ) • a' - (2 : ℝ) • a‖ ≤ 2 * (‖x' - x‖ + ‖a' - a‖ + (W2 μ μ').toReal)
      rw [← smul_sub, norm_smul]
      have := ENNReal.toReal_nonneg (a := W2 μ μ')
      have := norm_nonneg (x' - x)
      norm_num; linarith
    · show ‖(0 : E 1) - 0‖ ≤ _
      simp only [sub_self, norm_zero]
      have := ENNReal.toReal_nonneg (a := W2 μ μ')
      positivity
    · intro π _
      constructor
      · show ∫⁻ p, ‖(0 : E 1) - 0‖ₑ ^ 2 ∂π ≤ _; simp
      · show ∫⁻ p, ‖(0 : E 1) - 0‖ₑ ^ 2 ∂π ≤ _; simp
  a4 := by
    refine ⟨1, one_pos, ?_, ?_⟩
    · intro t _ x x' μ μ' a a' _ _ π _
      show (a' 0) ^ 2 - (a 0) ^ 2 - dot (0 : E 1) (x' - x) - dot ((2 : ℝ) • a) (a' - a)
        - ∫ p, dot (0 : E 1) (p.2 - p.1) ∂π ≥ 1 * ‖a' - a‖ ^ 2
      rw [norm_fin1]
      simp [dot, sq_abs]
      ring_nf; nlinarith [sq_nonneg (a' 0 - a 0)]
    · intro x x' μ μ' _ _ π _
      show (0 : ℝ) - 0 - dot (0 : E 1) (x' - x) - ∫ p, dot (0 : E 1) (p.2 - p.1) ∂π ≥ 0
      simp [dot]
  b1 := ⟨0, fun μ a _ t _ t' _ x x' => by
    show ‖(2 : ℝ) • a - (2 : ℝ) • a‖ ≤ _
    simp⟩
  b3 := by
    refine ⟨inferInstance, ?_⟩
    show ∫⁻ x, ‖x‖ₑ ^ 4 ∂(Measure.dirac (0 : E 1)) < ⊤
    rw [lintegral_dirac]; simp
  c1 := by
    refine ⟨?_, ?_, ?_⟩
    · intro t _ x μ a _
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact hasDerivWithinAt_const _ _ _
      · exact hasFDerivAt_const _ _
      · exact hasFDerivAt_const _ _
      · show HasFDerivAt (fun a' : Fin 1 → ℝ => (2 : ℝ) • a')
          ((2 : ℝ) • ContinuousLinearMap.id ℝ (Fin 1 → ℝ)) a
        exact (hasFDerivAt_id a).const_smul (2 : ℝ)
      · intro x'
        exact ⟨hasFDerivAt_const _ _, hasFDerivAt_const _ _, hasFDerivAt_const _ _⟩
    · intro t _ x x' a j
      exact isLDeriv_const _
    · refine ⟨2, fun t _ x x' μ a _ => ?_⟩
      have hM := M2_nonneg μ
      have hs : 0 ≤ sizeΘ t x μ a := by
        unfold sizeΘ; positivity
      have hs' : ‖a‖ ≤ sizeΘ t x μ a := by
        unfold sizeΘ; have := abs_nonneg t; have := norm_nonneg x; linarith
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show |(0 : ℝ)| ≤ _; simp <;> positivity
      · show ‖(2 : ℝ) • a‖ ≤ _
        rw [norm_smul]; norm_num; linarith
      · show ‖(0 : E 1)‖ ≤ _; simp; linarith
      · show ‖(0 : E 1)‖ ≤ _; simp; have := norm_nonneg x'; linarith
      · show ‖(0 : E 1 →L[ℝ] E 1)‖ ≤ _; simp
      · show ‖(0 : (Fin 1 → ℝ) →L[ℝ] E 1)‖ ≤ _; simp
      · show ‖(2 : ℝ) • ContinuousLinearMap.id ℝ (Fin 1 → ℝ)‖ ≤ 2
        rw [norm_smul]
        have := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Fin 1 → ℝ)
        norm_num <;> linarith
      · show ‖(0 : E 1 →L[ℝ] E 1)‖ ≤ _; simp
      · show ‖(0 : (Fin 1 → ℝ) →L[ℝ] E 1)‖ ≤ _; simp
      · show ‖(0 : E 1 →L[ℝ] E 1)‖ ≤ _; simp
      · intro j; show ‖(0 : E 1)‖ ≤ _; simp

/-- The minimizer `α̂(t, x, μ, y) = -t y / 2`. -/
noncomputable def αhat0 : ℝ → E 1 → Measure (E 1) → E 1 → Fin 1 → ℝ :=
  fun t _ _ y => fun _ => -(t * y 0) / 2

lemma hmin0 : IsMinimizer M0 αhat0 := by
  intro t _ x μ y _ a
  simp only [Model.Htilde, M0, D0, dot]
  simp [Matrix.mulVec, dotProduct, αhat0]
  nlinarith [sq_nonneg (a 0 + t * y 0 / 2)]

end DeepMFCLemma18Counter

open DeepMFCLemma18Counter in
theorem solution : ¬ (∀ {d k : ℕ} (M : Model d k) (D : Deriv d k) (hC : Coeff M D)
    (αhat : ℝ → E d → Measure (E d) → E d → Fin k → ℝ) (hmin : IsMinimizer M αhat),
    ∃ L : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) M.T, ∀ t' ∈ Set.Icc (0 : ℝ) M.T,
      ∀ (x x' : E d) (μ μ' : Measure (E d)) (y y' : E d), IsP2 μ → IsP2 μ' →
        ‖αhat t x μ y - αhat t' x' μ' y'‖
          ≤ L * (|t - t'| + ‖x - x'‖ + (W2 μ μ').toReal + ‖y - y'‖)) := by
  intro h
  obtain ⟨L, hL⟩ := h M0 D0 hC0 αhat0 hmin0
  have hP2 : IsP2 (Measure.dirac (0 : E 1)) := by
    refine ⟨inferInstance, ?_⟩
    rw [lintegral_dirac]; simp
  set c : ℝ := (W2 (Measure.dirac (0 : E 1)) (Measure.dirac 0)).toReal with hc
  set Y : ℝ := 2 * (|L| * (1 + c) + 1) with hY
  have hT : ((M0.T : ℝ)) = 1 := by simp [M0]
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) M0.T := by rw [hT]; exact ⟨zero_le_one, le_rfl⟩
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) M0.T := by rw [hT]; exact ⟨le_rfl, zero_le_one⟩
  have key := hL 1 h1 0 h0 0 0 (Measure.dirac 0) (Measure.dirac 0) (fun _ => Y) (fun _ => Y)
    hP2 hP2
  rw [← hc] at key
  have hlhs : ‖αhat0 1 0 (Measure.dirac 0) (fun _ => Y) - αhat0 0 0 (Measure.dirac 0) (fun _ => Y)‖
      = |Y| / 2 := by
    rw [norm_fin1]
    simp [αhat0, abs_div]
  rw [hlhs] at key
  simp only [sub_zero, abs_one, sub_self, norm_zero, add_zero] at key
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hYpos : 0 < Y := by rw [hY]; positivity
  rw [abs_of_pos hYpos, hY] at key
  have : L * (1 + c) ≤ |L| * (1 + c) :=
    mul_le_mul_of_nonneg_right (le_abs_self L) (by linarith)
  linarith
