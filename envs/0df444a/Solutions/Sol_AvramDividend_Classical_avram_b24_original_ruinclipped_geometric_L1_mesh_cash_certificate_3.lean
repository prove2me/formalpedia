-- Prove2me | solution 3 for AvramDividend.Classical.avram_b24_original_ruinclipped_geometric_L1_mesh_cash_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:16:15.432265+00:00
-- url     : https://prove2.me/submissions/df9dcd03-5717-4178-89bc-d863ea8663d5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_positiveclock_signed_ito_physmesh_L1_error_no_sign
import Theorems.Thm_AvramDividend_Classical_avram_b24_simultaneous_geometric_L1_subsequence_from_original_three_cauchy_sources
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_arbitrary_intrinsic_source_mesh_centering
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_ruinclipped_zero_clock_full_cash_bound
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X :
    SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ :
    X.σ ≠ 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0) (hw_cont :
    ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y
    ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable
    w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤
    deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD :
    IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤
    w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
    rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D
    t ω - D t ω))) (n : ℕ) (hn : 0 < n) (σ : Ω → ℝ≥0) (hσstop : IsStoppingTime 𝓕.rightCont (fun ω =>
    (σ ω : WithTop ℝ≥0))) (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0)) (hσclip : ∀ ω, σ ω ≤ (min (ruinTime X x D
    ω) (n : ℝ≥0∞)).toNNReal) (F : Ω → ℝ) (hFsource : ∀ ω, F ω = Real.exp (-(q * (σ ω : ℝ))) * w (if
    σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (σ ω) ω - rightLimit D (σ ω) ω else
    riskProcess X x D (σ ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
    ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) (hFI : Integrable F P)
    (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤) (R Jsmall : ℝ≥0 → Ω → ℝ) (hRsource : ∀ᵐ ω ∂P, ∀ u :
    ℝ≥0, Tendsto (fun k : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω) atTop (𝓝 (R
    u ω))) (hJsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, Tendsto (fun k : ℕ =>
    avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω) atTop (𝓝 (Jsmall u ω))) : ∃ (G J E
    : ℕ → Ω → ℝ), Integrable (G 0) P ∧ Integrable (J 0) P ∧ (∀ k, Integrable (fun ω => G (k + 1) ω -
    G k ω) P) ∧ (∀ k, Integrable (fun ω => J (k + 1) ω - J k ω) P) ∧ (∀ k, Integrable (E k) P) ∧ (∀
    k, (∫ ω, ‖G (k + 1) ω - G k ω‖ ∂P) ≤ ((1 : ℝ) / 2) ^ k) ∧ (∀ k, (∫ ω, ‖J (k + 1) ω - J k ω‖ ∂P)
    ≤ ((1 : ℝ) / 2) ^ k) ∧ (∀ k, (∫ ω, ‖E k ω‖ ∂P) ≤ ((1 : ℝ) / 2) ^ k) ∧ (∀ k, ∃ (S : Finset ℕ) (a
    b : ℕ → ℝ≥0) (WG WJ : ℕ → Ω → ℝ) (LG LJ : ℝ), (∀ i ∈ S, a i ≤ b i) ∧ (∀ i ∈ S,
    Measurable[𝓕.rightCont (a i)] (WG i)) ∧ (∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WJ i)) ∧ 0 ≤ LG
    ∧ 0 ≤ LJ ∧ (∀ i ∈ S, ∀ ω, ‖WG i ω‖ ≤ LG) ∧ (∀ i ∈ S, ∀ ω, ‖WJ i ω‖ ≤ LJ) ∧ (∀ ω, G k ω = ∑ i ∈
    S, (if σ ω ≤ a i then 0 else WG i ω) * (R (b i) ω - R (a i) ω)) ∧ (∀ ω, J k ω = ∑ i ∈ S, (if σ ω
    ≤ a i then 0 else WJ i ω) * (Jsmall (b i) ω - Jsmall (a i) ω))) ∧ (∀ k, ∀ᵐ ω ∂P, F ω ≤ w x + G k
    ω + J k ω + E k ω) := by
  obtain ⟨G, J, E, hEI, hMesh, hCash, hGC, hJC, hEC⟩ :=
    avram_b24_original_positiveclock_signed_ito_physmesh_L1_error_no_sign
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn σ
      hσstop hσbound hσclip F hFsource hFI hFiniteActivity
      R Jsmall hRsource hJsource
  have hGainI (k : ℕ) : Integrable (G k) P ∧ Integrable (J k) P := by
    obtain ⟨S,a,b,WG,WJ,LG,LJ,hab,hWG,hWJ,hLG,hLJ,hWGb,hWJb,hGf,hJf⟩ :=
      hMesh k
    obtain ⟨hGI,_,hJI,_⟩ :=
      avram_b24_original_arbitrary_intrinsic_source_mesh_centering
        X hX hFiniteActivity R Jsmall hRsource hJsource
        S a b WG WJ hab hWG hWJ σ hσstop LG LJ hLG hLJ hWGb hWJb
    refine ⟨hGI.congr ?_, hJI.congr ?_⟩
    · filter_upwards [] with ω; exact (hGf ω).symm
    · filter_upwards [] with ω; exact (hJf ω).symm
  let Epos : ℕ → Ω → ℝ := fun k ω => max (E k ω) 0
  have hEposI (k : ℕ) : Integrable (Epos k) P := (hEI k).pos_part
  have hEbound (k : ℕ) (ω : Ω) : ‖Epos k ω‖ ≤ ‖E k ω‖ := by
    have hp : 0 ≤ max (E k ω) 0 := le_max_right _ _
    have hle : max (E k ω) 0 ≤ |E k ω| :=
      max_le (le_abs_self _) (abs_nonneg _)
    simpa only [Epos, Real.norm_eq_abs, abs_of_nonneg hp] using hle
  have hEsmall : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ,
      ∀ k : ℕ, N ≤ k → (∫ ω, ‖Epos k ω‖ ∂P) ≤ ε := by
    intro ε hε
    obtain ⟨N,hN⟩ := hEC ε hε
    refine ⟨N, fun k hk => ?_⟩
    calc
      (∫ ω, ‖Epos k ω‖ ∂P) ≤ (∫ ω, ‖E k ω‖ ∂P) :=
        integral_mono_ae (hEposI k).norm (hEI k).norm
          (Filter.Eventually.of_forall (hEbound k))
      _ ≤ ε := hN k hk
  obtain ⟨K,hKinc,hKrG,hKrJ,hKrE⟩ :=
    avram_b24_simultaneous_geometric_L1_subsequence_from_original_three_cauchy_sources
      P G J Epos hGC hJC hEsmall
  have hZero := avram_b24_original_ruinclipped_zero_clock_full_cash_bound
    X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth
    hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn σ
    hσstop hσbound hσclip F hFsource hFI hFiniteActivity
    R Jsmall hRsource hJsource
  have hMeshZero (k : ℕ) (ω : Ω) (hz : σ ω = 0) :
      G k ω = 0 ∧ J k ω = 0 := by
    obtain ⟨S,a,b,WG,WJ,LG,LJ,hab,hWG,hWJ,hLG,hLJ,hWGb,hWJb,hGf,hJf⟩ :=
      hMesh k
    have hMask (i : ℕ) : σ ω ≤ a i := by rw [hz]; positivity
    constructor
    · rw [hGf ω]; apply Finset.sum_eq_zero
      intro i hi; simp [hMask i]
    · rw [hJf ω]; apply Finset.sum_eq_zero
      intro i hi; simp [hMask i]
  have hCashAll (k : ℕ) :
      ∀ᵐ ω ∂P, F ω ≤ w x + G k ω + J k ω + Epos k ω := by
    filter_upwards [hCash k] with ω hk
    by_cases hp : 0 < σ ω
    · have hle := hk hp
      have hrel : E k ω ≤ Epos k ω := le_max_left _ _
      linarith
    · have hz : σ ω = 0 := le_antisymm (le_of_not_gt hp) (by positivity)
      obtain ⟨hg,hj⟩ := hMeshZero k ω hz
      have hle := hZero ω hz
      have hepos : 0 ≤ Epos k ω := le_max_right _ _
      rw [hg,hj]; linarith
  refine ⟨(fun k => G (K k)), (fun k => J (K k)),
    (fun k => Epos (K k)), (hGainI (K 0)).1, (hGainI (K 0)).2,
    (fun k => (hGainI (K (k+1))).1.sub (hGainI (K k)).1),
    (fun k => (hGainI (K (k+1))).2.sub (hGainI (K k)).2),
    (fun k => hEposI (K k)), hKrG, hKrJ, hKrE,
    (fun k => hMesh (K k)), (fun k => hCashAll (K k))⟩
