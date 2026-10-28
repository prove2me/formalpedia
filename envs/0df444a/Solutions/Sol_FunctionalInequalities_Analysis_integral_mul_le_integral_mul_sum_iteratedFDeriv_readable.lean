-- Prove2me | solution 1 for FunctionalInequalities.Analysis.integral_mul_le_integral_mul_sum_iteratedFDeriv_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:38:11.537461+00:00
-- url     : https://prove2.me/submissions/ed0317b1-1f5f-4ced-8fc8-4f0aa0b13da0

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_SecondOrder
import Theorems.Thm_FunctionalInequalities_Analysis_tendsto_integral_secondDifference_mul_readable

noncomputable section
open Set Filter
open scoped RealInnerProductSpace Topology
section LT12D7FatouSecondDifference
open MeasureTheory Set Filter
open scoped Topology
section StructuredSpace
variable {E : Type*}
variable [NormedAddCommGroup E]
section NormedSpace
variable [NormedSpace ℝ E]
private lemma FunctionalInequalities.Analysis.second_derivative_continuous_compact {χ : E → ℝ}
    (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) (v : E) :
    Continuous (fun x => iteratedFDeriv ℝ 2 χ x (fun _ => v)) ∧
      HasCompactSupport (fun x => iteratedFDeriv ℝ 2 χ x (fun _ => v)) := by
  simp only [iteratedFDeriv_two_apply]
  constructor
  · have hd := (hχ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
    exact (hd.clm_apply continuous_const).clm_apply continuous_const
  · exact ((hχc.fderiv ℝ).fderiv_apply ℝ v).comp_left
      (g := fun L : E →L[ℝ] ℝ => L v) (by simp)
end NormedSpace
section InnerProduct
variable [InnerProductSpace ℝ E]
section FiniteDimensional
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
private lemma FunctionalInequalities.Analysis.secondDifference_integrable {u χ : E → ℝ}
    (hu : Continuous u) (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (v : E) (t : ℝ) :
    Integrable
      (fun x => (u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2 * χ x)
      (volume : Measure E) := by
  have hcont :
      Continuous
        (fun x => (u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2 * χ x) :=
    ((((hu.comp (continuous_id.add continuous_const)).add
      (hu.comp (continuous_id.sub continuous_const))).sub
        (continuous_const.mul hu)).div_const (t ^ 2)).mul hχ
  exact hcont.integrable_of_hasCompactSupport hχc.mul_left
end FiniteDimensional
private lemma FunctionalInequalities.Analysis.convex_secondDifference_nonneg {u : E → ℝ} (hconv : ConvexOn ℝ univ u)
    (x w : E) :
    0 ≤ u (x + w) + u (x - w) - 2 * u x := by
  have hm : (1 / 2 : ℝ) • (x + w) + (1 / 2 : ℝ) • (x - w) = x := by
    module
  have H := hconv.2 (mem_univ (x + w)) (mem_univ (x - w))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  rw [hm] at H
  dsimp at H
  linarith
private lemma FunctionalInequalities.Analysis.ofReal_mul_le_of_sub (a k : ℝ) (B : ENNReal)
    (h : ∀ ε > 0, ENNReal.ofReal ((a - ε) * k) ≤ B) :
    ENNReal.ofReal (a * k) ≤ B := by
  have hz : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun ε : ℝ => ENNReal.ofReal ((a - ε) * k))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal (a * k))) := by
    simpa only [sub_zero] using
      ENNReal.tendsto_ofReal ((tendsto_const_nhds.sub hz).mul_const k)
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact h ε hε
/-- **Fatou bound for the distributional second derivatives of a convex function** (weak Letwin route, input of the distributional log-det inequality): if `g` is below the lower limit of a
nonnegative combination of second difference quotients of the convex `u` almost everywhere, then
`∫ g χ ≤ ∫ u ∑ᵢ cᵢ ∂²_{vᵢ} χ` for every nonnegative `χ ∈ C²` with compact support. -/
theorem solution [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} (hconv : ConvexOn ℝ univ u) {ι : Type*} [Fintype ι] (v : ι → E) {c : ι → ℝ}
    (hc : ∀ i, 0 ≤ c i) {χ : E → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) {g : E → ℝ} (hgm : AEStronglyMeasurable g (volume : Measure E))
    (hg : ∀ᵐ x ∂(volume : Measure E), ∀ ε > 0, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      g x - ε ≤ ∑ i, c i * ((u (x + t • v i) + u (x - t • v i) - 2 * u x) / t ^ 2)) :
    ∫ x, g x * χ x ≤ ∫ x, u x * ∑ i, c i * iteratedFDeriv ℝ 2 χ x (fun _ => v i) := by
  classical
  have hu : Continuous u := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  let A : ℝ → ι → E → ℝ := fun t i x =>
    (u (x + t • v i) + u (x - t • v i) - 2 * u x) / t ^ 2 * χ x
  let F : ℝ → E → ℝ := fun t x => ∑ i, c i * A t i x
  let R : ℝ := ∫ x, u x * ∑ i, c i * iteratedFDeriv ℝ 2 χ x (fun _ => v i)
  have hAi (t : ℝ) (i : ι) : Integrable (A t i) (volume : Measure E) :=
    FunctionalInequalities.Analysis.secondDifference_integrable hu hχ.continuous hχc (v i) t
  have hFi (t : ℝ) : Integrable (F t) (volume : Measure E) :=
    integrable_finsetSum Finset.univ fun i _ => (hAi t i).const_mul (c i)
  have hF0 (t : ℝ) (x : E) : 0 ≤ F t x := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hc i)
      (mul_nonneg
        (div_nonneg (FunctionalInequalities.Analysis.convex_secondDifference_nonneg hconv x (t • v i))
          (sq_nonneg t)) (hχ0 x))
  have hDi (i : ι) :
      Integrable (fun x => u x * iteratedFDeriv ℝ 2 χ x (fun _ => v i))
        (volume : Measure E) := by
    obtain ⟨hdc, hds⟩ := FunctionalInequalities.Analysis.second_derivative_continuous_compact hχ hχc (v i)
    exact (hu.mul hdc).integrable_of_hasCompactSupport hds.mul_left
  have hR : R = ∑ i, c i * (∫ x, u x * iteratedFDeriv ℝ 2 χ x (fun _ => v i)) := by
    have heq :
        (fun x => u x * ∑ i, c i * iteratedFDeriv ℝ 2 χ x (fun _ => v i)) =
          (fun x => ∑ i, c i * (u x * iteratedFDeriv ℝ 2 χ x (fun _ => v i))) := by
      funext x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    dsimp only [R]
    rw [heq, integral_finsetSum Finset.univ
      (fun i _ => (hDi i).const_mul (c i))]
    simp_rw [integral_const_mul]
  have hI (t : ℝ) :
      (∫ x, F t x) = ∑ i, c i * (∫ x, A t i x) := by
    dsimp only [F]
    rw [integral_finsetSum Finset.univ (fun i _ => (hAi t i).const_mul (c i))]
    simp_rw [integral_const_mul]
  have hlim : Tendsto (fun t : ℝ => ∫ x, F t x) (𝓝[>] 0) (𝓝 R) := by
    rw [hR]
    have H := tendsto_finsetSum Finset.univ (fun i _ =>
      (FunctionalInequalities.Analysis.tendsto_integral_secondDifference_mul_readable hu hχ hχc (v i)).const_mul (c i))
    exact H.congr' (.of_forall fun t => (hI t).symm)
  have hR0 : 0 ≤ R :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (.of_forall fun t => integral_nonneg (hF0 t))
  by_cases hgi : Integrable (fun x => g x * χ x) (volume : Measure E)
  · have hgi' : Integrable (fun x => g x * χ x) (volume : Measure E) :=
      ⟨hgm.mul hχ.continuous.aestronglyMeasurable, hgi.2⟩
    have hpoint :
        ∀ᵐ x ∂(volume : Measure E),
          ENNReal.ofReal (g x * χ x) ≤
            liminf (fun t : ℝ => ENNReal.ofReal (F t x)) (𝓝[>] 0) := by
      filter_upwards [hg] with x hx
      apply FunctionalInequalities.Analysis.ofReal_mul_le_of_sub
      intro ε hε
      obtain ⟨δ, hδ, hbound⟩ := hx ε hε
      have hev :
          ∀ᶠ t : ℝ in 𝓝[>] 0,
            ENNReal.ofReal ((g x - ε) * χ x) ≤ ENNReal.ofReal (F t x) := by
        have hδevent : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioo 0 δ :=
          (nhdsGT_basis (0 : ℝ)).mem_iff.mpr ⟨δ, hδ, subset_rfl⟩
        filter_upwards [hδevent] with t ht
        apply ENNReal.ofReal_le_ofReal
        calc
          (g x - ε) * χ x ≤
              (∑ i, c i *
                ((u (x + t • v i) + u (x - t • v i) - 2 * u x) / t ^ 2)) *
                χ x :=
            mul_le_mul_of_nonneg_right (hbound t ht.1 ht.2) (hχ0 x)
          _ = F t x := by
            dsimp only [F, A]
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            ring
      exact le_liminf_of_le (h := hev)
    have hL :
        Tendsto (fun t : ℝ => ∫⁻ x, ENNReal.ofReal (F t x))
          (𝓝[>] 0) (𝓝 (ENNReal.ofReal R)) := by
      exact (ENNReal.tendsto_ofReal hlim).congr' (.of_forall fun t =>
        ofReal_integral_eq_lintegral_ofReal (hFi t) (.of_forall (hF0 t)))
    have hfatou :
        (∫⁻ x, ENNReal.ofReal (g x * χ x)) ≤ ENNReal.ofReal R := by
      calc
        _ ≤ ∫⁻ x, liminf (fun t : ℝ => ENNReal.ofReal (F t x)) (𝓝[>] 0) :=
          lintegral_mono_ae hpoint
        _ ≤ liminf (fun t : ℝ => ∫⁻ x, ENNReal.ofReal (F t x)) (𝓝[>] 0) :=
          lintegral_liminf_le' (fun t =>
            ENNReal.continuous_ofReal.measurable.comp_aemeasurable
              (hFi t).aestronglyMeasurable.aemeasurable)
        _ = ENNReal.ofReal R := hL.liminf_eq
    have hp :
        ENNReal.ofReal (∫ x, max (g x * χ x) 0) ≤ ENNReal.ofReal R := by
      calc
        _ = ∫⁻ x, ENNReal.ofReal (g x * χ x) := by
          rw [ofReal_integral_eq_lintegral_ofReal hgi'.pos_part
            (.of_forall fun x => le_max_right (g x * χ x) 0)]
          apply lintegral_congr
          intro x
          simp
        _ ≤ ENNReal.ofReal R := hfatou
    exact (integral_mono hgi' hgi'.pos_part
      (fun x => le_max_left (g x * χ x) 0)).trans
        ((ENNReal.ofReal_le_ofReal_iff hR0).mp hp)
  · rw [integral_undef hgi]
    exact hR0
