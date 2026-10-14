-- Prove2me | solution 1 for DbarRegularity.tendsto_circle_average_div
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T20:47:08.237587+00:00
-- url     : https://prove2.me/submissions/3597a6a4-2bfb-44ea-b3a5-1c6126279e03

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Theorems.Thm_DbarRegularity_integral_sphere_two_moments



namespace DbarRegularity

open MeasureTheory Metric Set Filter Topology

/-- For `f ∈ C¹(ℝ²)` and `x ∈ ℝ²`, the circle averages
`ε⁻¹ ∫_{S¹} f(x - ε ω) / (ω₀ + i ω₁) dσ(ω)` converge, as `ε → 0⁺`, to
`-π (∂₁f(x) - i ∂₂f(x))`. -/
theorem tendsto_circle_average_div_aux (f : EuclideanSpace ℝ (Fin 2) → ℂ) (hf : ContDiff ℝ 1 f)
    (x : EuclideanSpace ℝ (Fin 2)) :
    Tendsto (fun ε : ℝ => ((ε⁻¹ : ℝ) : ℂ) * ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        f (x - ε • ω.1) / ((ω.1 0 : ℂ) + (ω.1 1 : ℂ) * Complex.I) ∂volume.toSphere)
      (𝓝[>] 0)
      (𝓝 (-(Real.pi : ℂ) * (fderiv ℝ f x (EuclideanSpace.single 0 1) -
        Complex.I * fderiv ℝ f x (EuclideanSpace.single 1 1)))) := by
  set σ := (volume : Measure (EuclideanSpace ℝ (Fin 2))).toSphere with hσ
  set L := fderiv ℝ f x with hL
  set a := L (EuclideanSpace.single 0 1) with ha
  set b := L (EuclideanSpace.single 1 1) with hb
  obtain ⟨hm1, hm2⟩ := integral_sphere_two_moments
  -- continuous functions on the circle are integrable
  have hcint : ∀ g : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → ℂ, Continuous g →
      Integrable g σ := fun g hg =>
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hrint : ∀ g : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → ℝ, Continuous g →
      Integrable g σ := fun g hg =>
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcoord : ∀ i : Fin 2, Continuous fun ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 => ω.1 i :=
    fun i => (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).continuous.comp
      continuous_subtype_val
  -- the conjugate on the circle
  set c : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → ℂ := fun ω =>
    (ω.1 0 : ℂ) - (ω.1 1 : ℂ) * Complex.I with hc
  have hcc : Continuous c := by
    simp only [hc]
    exact (Complex.continuous_ofReal.comp (hcoord 0)).sub
      ((Complex.continuous_ofReal.comp (hcoord 1)).mul continuous_const)
  have hsq : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, ω.1 0 ^ 2 + ω.1 1 ^ 2 = 1 := by
    intro ω
    have hω : ‖ω.1‖ = 1 := by simpa using ω.2
    have := EuclideanSpace.real_norm_sq_eq ω.1
    rw [hω, Fin.sum_univ_two] at this
    linarith
  have hinv : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      1 / ((ω.1 0 : ℂ) + (ω.1 1 : ℂ) * Complex.I) = c ω := by
    intro ω
    rw [one_div]
    apply inv_eq_of_mul_eq_one_right
    simp only [hc]
    have h1 : ((ω.1 0 ^ 2 + ω.1 1 ^ 2 : ℝ) : ℂ) = 1 := by rw [hsq ω]; simp
    push_cast at h1
    linear_combination h1 - ((ω.1 1 : ℂ) ^ 2) * Complex.I_sq
  have hnc : ∀ ω, ‖c ω‖ = 1 := by
    intro ω
    have h := hinv ω
    have hn : ‖(ω.1 0 : ℂ) + (ω.1 1 : ℂ) * Complex.I‖ = 1 := by
      have : (ω.1 0 : ℂ) + (ω.1 1 : ℂ) * Complex.I = Complex.orthonormalBasisOneI.repr.symm ω.1 :=
        (Complex.orthonormalBasisOneI_repr_symm_apply ω.1).symm
      rw [this, LinearIsometryEquiv.norm_map]
      simpa using ω.2
    rw [← h, norm_div, norm_one, hn, div_one]
  -- the moments
  have hM1 : ∫ ω, c ω ∂σ = 0 := by
    simp only [hc]
    rw [integral_sub, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal, hm1 0, hm1 1]
    · simp
    all_goals (apply hcint; fun_prop)
  have hLω : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      L ω.1 = (ω.1 0 : ℂ) * a + (ω.1 1 : ℂ) * b := by
    intro ω
    have : ω.1 = (ω.1 0) • EuclideanSpace.single 0 (1 : ℝ) +
        (ω.1 1) • EuclideanSpace.single 1 (1 : ℝ) := by
      ext i
      fin_cases i <;> simp
    conv_lhs => rw [this]
    rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  have hpint : ∀ i j : Fin 2, Integrable
      (fun ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 => ((ω.1 i * ω.1 j : ℝ) : ℂ)) σ :=
    fun i j => hcint _ (Complex.continuous_ofReal.comp ((hcoord i).mul (hcoord j)))
  have hM2 : ∫ ω, L ω.1 * c ω ∂σ = Real.pi * (a - Complex.I * b) := by
    have hpt : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, L ω.1 * c ω =
        a * ((ω.1 0 * ω.1 0 : ℝ) : ℂ) + (-a * Complex.I) * ((ω.1 0 * ω.1 1 : ℝ) : ℂ) +
          b * ((ω.1 1 * ω.1 0 : ℝ) : ℂ) + (-b * Complex.I) * ((ω.1 1 * ω.1 1 : ℝ) : ℂ) := by
      intro ω
      rw [hLω]
      simp only [hc]
      push_cast
      ring
    simp_rw [hpt]
    rw [integral_add, integral_add, integral_add,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_complex_ofReal, integral_complex_ofReal, integral_complex_ofReal, integral_complex_ofReal,
      hm2 0 0, hm2 0 1, hm2 1 0, hm2 1 1]
    · simp
      ring
    all_goals (apply hcint; fun_prop)
  -- the main estimate
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  set S := σ.real univ with hS
  have hS0 : 0 ≤ S := measureReal_nonneg
  set η := δ / (S + 1) with hη
  have hη0 : 0 < η := div_pos hδ (by linarith)
  have hcont : ContinuousAt (fderiv ℝ f) x := (hf.continuous_fderiv (by norm_num)).continuousAt
  obtain ⟨ρ, hρ, hρL⟩ := Metric.continuousAt_iff.1 hcont η hη0
  refine ⟨ρ, hρ, fun ε hε hεd => ?_⟩
  have hε0 : 0 < ε := hε
  rw [Real.dist_eq, sub_zero, abs_of_pos hε0] at hεd
  -- remainder
  set φ : EuclideanSpace ℝ (Fin 2) → ℂ := fun z => f z - L z with hφ
  have hφd : ∀ z ∈ ball x ρ, DifferentiableAt ℝ φ z := fun z _ =>
    (hf.differentiable (by norm_num) z).sub L.differentiableAt
  have hφb : ∀ z ∈ ball x ρ, ‖fderiv ℝ φ z‖ ≤ η := by
    intro z hz
    have hd : HasFDerivAt φ (fderiv ℝ f z - L) z :=
      (hf.differentiable (by norm_num) z).hasFDerivAt.sub L.hasFDerivAt
    rw [hd.fderiv, ← dist_eq_norm]
    exact (hρL hz).le
  have hrem : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      ‖f (x - ε • ω.1) - f x + (ε : ℂ) * L ω.1‖ ≤ η * ε := by
    intro ω
    have hω : ‖ω.1‖ = 1 := by simpa using ω.2
    have hmem : x - ε • ω.1 ∈ ball x ρ := by
      rw [mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul, hω, mul_one,
        Real.norm_of_nonneg hε0.le]
      exact hεd
    have := (convex_ball x ρ).norm_image_sub_le_of_norm_fderiv_le hφd hφb (mem_ball_self hρ) hmem
    rw [sub_sub_cancel_left, norm_neg, norm_smul, hω, mul_one, Real.norm_of_nonneg hε0.le] at this
    have key : f (x - ε • ω.1) - f x + (ε : ℂ) * L ω.1 = φ (x - ε • ω.1) - φ x := by
      simp only [hφ, map_sub, map_smul, Complex.real_smul]
      ring
    rw [key]
    exact this
  set r : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → ℂ := fun ω =>
    f (x - ε • ω.1) - f x + (ε : ℂ) * L ω.1 with hr
  have hfc : Continuous fun ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 => f (x - ε • ω.1) :=
    hf.continuous.comp (by fun_prop)
  have hLc : Continuous fun ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 => L ω.1 :=
    L.continuous.comp continuous_subtype_val
  have hrc : Continuous r := (hfc.sub continuous_const).add (continuous_const.mul hLc)
  have hsplit : ∫ ω, f (x - ε • ω.1) / ((ω.1 0 : ℂ) + (ω.1 1 : ℂ) * Complex.I) ∂σ =
      ∫ ω, r ω * c ω ∂σ - (ε : ℂ) * (Real.pi * (a - Complex.I * b)) := by
    have hpt : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        f (x - ε • ω.1) / ((ω.1 0 : ℂ) + (ω.1 1 : ℂ) * Complex.I) =
        r ω * c ω + f x * c ω - (ε : ℂ) * (L ω.1 * c ω) := by
      intro ω
      rw [div_eq_mul_one_div, hinv, hr]
      ring
    simp_rw [hpt]
    rw [integral_sub, integral_add, integral_const_mul, integral_const_mul, hM1, hM2]
    · ring
    · exact hcint _ (hrc.mul hcc)
    · exact hcint _ (continuous_const.mul hcc)
    · exact hcint _ ((hrc.mul hcc).add (continuous_const.mul hcc))
    · exact hcint _ (continuous_const.mul (hLc.mul hcc))
  have hbound : ‖∫ ω, r ω * c ω ∂σ‖ ≤ η * ε * S := by
    refine norm_integral_le_of_norm_le_const (Eventually.of_forall fun ω => ?_)
    rw [norm_mul, hnc, mul_one]
    exact hrem ω
  rw [hsplit, dist_eq_norm]
  have hεc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hε0.ne'
  have heq : ((ε⁻¹ : ℝ) : ℂ) * (∫ ω, r ω * c ω ∂σ - (ε : ℂ) * (Real.pi * (a - Complex.I * b))) -
      -(Real.pi : ℂ) * (a - Complex.I * b) = ((ε⁻¹ : ℝ) : ℂ) * ∫ ω, r ω * c ω ∂σ := by
    push_cast
    field_simp
    ring
  rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hε0.le)]
  calc ε⁻¹ * ‖∫ ω, r ω * c ω ∂σ‖ ≤ ε⁻¹ * (η * ε * S) := by gcongr
    _ = η * S := by field_simp
    _ < δ := by
      rw [hη, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
      nlinarith

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Set Filter Topology

theorem solution (f : EuclideanSpace ℝ (Fin 2) → ℂ) (hf : ContDiff ℝ 1 f)
    (x : EuclideanSpace ℝ (Fin 2)) :
    Tendsto (fun ε : ℝ => ((ε⁻¹ : ℝ) : ℂ) * ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        f (x - ε • ω.1) / ((ω.1 0 : ℂ) + (ω.1 1 : ℂ) * Complex.I) ∂volume.toSphere)
      (𝓝[>] 0)
      (𝓝 (-(Real.pi : ℂ) * (fderiv ℝ f x (EuclideanSpace.single 0 1) -
        Complex.I * fderiv ℝ f x (EuclideanSpace.single 1 1)))) :=
  tendsto_circle_average_div_aux f hf x
