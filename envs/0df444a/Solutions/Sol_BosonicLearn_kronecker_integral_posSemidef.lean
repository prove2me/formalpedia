-- Prove2me | solution 1 for BosonicLearn.kronecker_integral_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-13T06:21:39.3012+00:00
-- url     : https://prove2.me/submissions/ac903721-f7bb-4278-aa6e-69252a73d884

import Mathlib

open MeasureTheory
open scoped ENNReal Matrix ComplexOrder
open Filter Topology

noncomputable section

/-- The case of a simple function: the matrix is a finite sum of Kronecker products of positive
semidefinite matrices. -/
private lemma simple_case {Ω ι₁ ι₂ K : Type} [MeasurableSpace Ω] [Fintype ι₁] [Fintype ι₂]
    [Fintype K] (μ : ι₁ → ι₁ → K → Measure Ω) (hμ : ∀ u v k, IsFiniteMeasure (μ u v k))
    (coef : ι₁ → ι₁ → K → ℂ)
    (hA : ∀ B : Set Ω, MeasurableSet B →
      (Matrix.of fun u v => ∑ k, coef u v k * (((μ u v k B).toReal : ℝ) : ℂ)).PosSemidef)
    (g : SimpleFunc Ω (ι₂ → ι₂ → ℂ)) (hg : ∀ x, (Matrix.of (g x)).PosSemidef) :
    (Matrix.of fun (p q : ι₁ × ι₂) =>
      ∑ k, coef p.1 q.1 k * ∫ x, g x p.2 q.2 ∂(μ p.1 q.1 k)).PosSemidef := by
  have hint : ∀ (m : Measure Ω) [IsFiniteMeasure m] (a b : ι₂),
      ∫ x, g x a b ∂m = ∑ P ∈ g.range, (((m (g ⁻¹' {P})).toReal : ℝ) : ℂ) * P a b := by
    intro m _ a b
    have h1 := SimpleFunc.map_integral (μ := m) g (fun P : ι₂ → ι₂ → ℂ => P a b)
      (SimpleFunc.integrable_of_isFiniteMeasure g) rfl
    have h2 := SimpleFunc.integral_eq_integral (μ := m) (g.map fun P : ι₂ → ι₂ → ℂ => P a b)
      (SimpleFunc.integrable_of_isFiniteMeasure _)
    have h3 : ∫ x, g x a b ∂m = ∫ x, (g.map fun P : ι₂ → ι₂ → ℂ => P a b) x ∂m := rfl
    rw [h3, ← h2, h1]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [Complex.real_smul]
    rfl
  have heq : (Matrix.of fun (p q : ι₁ × ι₂) =>
      ∑ k, coef p.1 q.1 k * ∫ x, g x p.2 q.2 ∂(μ p.1 q.1 k)) =
      ∑ P ∈ g.range, Matrix.kroneckerMap (fun x1 x2 => x1 * x2)
        (Matrix.of fun u v => ∑ k, coef u v k * (((μ u v k (g ⁻¹' {P})).toReal : ℝ) : ℂ))
        (Matrix.of P) := by
    ext p q
    rw [Matrix.sum_apply]
    simp only [Matrix.of_apply, Matrix.kroneckerMap_apply]
    have hk : ∀ k, coef p.1 q.1 k * ∫ x, g x p.2 q.2 ∂(μ p.1 q.1 k) =
        ∑ P ∈ g.range, coef p.1 q.1 k * (((μ p.1 q.1 k (g ⁻¹' {P})).toReal : ℝ) : ℂ) * P p.2 q.2 := by
      intro k
      have := hμ p.1 q.1 k
      rw [hint (μ p.1 q.1 k) p.2 q.2, Finset.mul_sum]
      exact Finset.sum_congr rfl fun P _ => by ring
    rw [Finset.sum_congr rfl fun k _ => hk k, Finset.sum_comm]
    exact Finset.sum_congr rfl fun P _ => by rw [Finset.sum_mul]
  rw [heq]
  refine Matrix.posSemidef_sum _ fun P hP => ?_
  obtain ⟨x, rfl⟩ := SimpleFunc.mem_range.mp hP
  exact (hA _ (g.measurableSet_fiber _)).kronecker (hg x)

theorem solution {Ω ι₁ ι₂ K : Type} [MeasurableSpace Ω] [Fintype ι₁] [Fintype ι₂]
    [Fintype K] (μ : ι₁ → ι₁ → K → Measure Ω) (hμ : ∀ u v k, IsFiniteMeasure (μ u v k))
    (coef : ι₁ → ι₁ → K → ℂ)
    (hA : ∀ B : Set Ω, MeasurableSet B →
      (Matrix.of fun u v => ∑ k, coef u v k * (((μ u v k B).toReal : ℝ) : ℂ)).PosSemidef)
    (G : Ω → Matrix ι₂ ι₂ ℂ) (hGm : ∀ a b, Measurable fun x => G x a b)
    (hGb : ∀ x a b, ‖G x a b‖ ≤ 1) (hG : ∀ x, (G x).PosSemidef) :
    (Matrix.of fun (p q : ι₁ × ι₂) =>
      ∑ k, coef p.1 q.1 k * ∫ x, G x p.2 q.2 ∂(μ p.1 q.1 k)).PosSemidef := by
  classical
  let Gf : Ω → ι₂ → ι₂ → ℂ := fun x => G x
  have hGf : Measurable Gf := measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b => hGm a b
  let S : Set (ι₂ → ι₂ → ℂ) := {P | (Matrix.of P).PosSemidef ∧ ∀ a b, ‖P a b‖ ≤ 1}
  have h0 : (0 : ι₂ → ι₂ → ℂ) ∈ S := ⟨Matrix.PosSemidef.zero, fun a b => by simp⟩
  have hGS : ∀ x, Gf x ∈ S := fun x => ⟨hG x, hGb x⟩
  let g : ℕ → SimpleFunc Ω (ι₂ → ι₂ → ℂ) := fun n => SimpleFunc.approxOn Gf hGf S 0 h0 n
  have hgS : ∀ n x, g n x ∈ S := fun n x => SimpleFunc.approxOn_mem hGf h0 n x
  have hgt : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (Gf x)) := fun x =>
    SimpleFunc.tendsto_approxOn hGf h0 (subset_closure (hGS x))
  have hint : ∀ (m : Measure Ω) [IsFiniteMeasure m] (a b : ι₂),
      Tendsto (fun n => ∫ x, g n x a b ∂m) atTop (𝓝 (∫ x, G x a b ∂m)) := by
    intro m _ a b
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun n => ?_)
      (integrable_const _) (fun n => Eventually.of_forall fun x => (hgS n x).2 a b)
      (Eventually.of_forall fun x => ?_)
    · exact ((measurable_pi_apply b).comp
        ((measurable_pi_apply a).comp (g n).measurable)).aestronglyMeasurable
    · exact ((continuous_apply b).tendsto _).comp (((continuous_apply a).tendsto _).comp (hgt x))
  let W : ℕ → Matrix (ι₁ × ι₂) (ι₁ × ι₂) ℂ := fun n => Matrix.of fun p q =>
    ∑ k, coef p.1 q.1 k * ∫ x, g n x p.2 q.2 ∂(μ p.1 q.1 k)
  have hWn : ∀ n, (W n).PosSemidef := fun n =>
    simple_case μ hμ coef hA (g n) (fun x => (hgS n x).1)
  have hWt : ∀ p q : ι₁ × ι₂, Tendsto (fun n => W n p q) atTop
      (𝓝 (∑ k, coef p.1 q.1 k * ∫ x, G x p.2 q.2 ∂(μ p.1 q.1 k))) := by
    intro p q
    refine tendsto_finsetSum _ fun k _ => tendsto_const_nhds.mul ?_
    have := hμ p.1 q.1 k
    exact hint _ _ _
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun z => ?_
  · ext p q
    rw [Matrix.conjTranspose_apply]
    have h1 : Tendsto (fun n => star (W n q p)) atTop
        (𝓝 (star (∑ k, coef q.1 p.1 k * ∫ x, G x q.2 p.2 ∂(μ q.1 p.1 k)))) :=
      (continuous_star.tendsto _).comp (hWt q p)
    have h2 : ∀ n, star (W n q p) = W n p q := fun n => by
      have h := congrFun (congrFun (hWn n).isHermitian p) q
      rwa [Matrix.conjTranspose_apply] at h
    exact tendsto_nhds_unique h1 ((hWt p q).congr fun n => (h2 n).symm)
  · have h1 : Tendsto (fun n => star z ⬝ᵥ (W n).mulVec z) atTop
        (𝓝 (star z ⬝ᵥ (Matrix.of fun (p q : ι₁ × ι₂) =>
          ∑ k, coef p.1 q.1 k * ∫ x, G x p.2 q.2 ∂(μ p.1 q.1 k)).mulVec z)) := by
      simp only [dotProduct, Matrix.mulVec]
      exact tendsto_finsetSum _ fun p _ => tendsto_const_nhds.mul
        (tendsto_finsetSum _ fun q _ => (hWt p q).mul tendsto_const_nhds)
    exact ge_of_tendsto' h1 fun n => (hWn n).dotProduct_mulVec_nonneg z
