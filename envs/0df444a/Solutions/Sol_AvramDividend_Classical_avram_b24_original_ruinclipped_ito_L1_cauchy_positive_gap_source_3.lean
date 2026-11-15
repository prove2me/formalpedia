-- Prove2me | solution 3 for AvramDividend.Classical.avram_b24_original_ruinclipped_ito_L1_cauchy_positive_gap_source
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:38:10.782583+00:00
-- url     : https://prove2.me/submissions/6720ea5d-4f8c-4d11-b26f-14a98042c74b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_positiveclock_signed_ito_physmesh_L1_error_no_sign
import Theorems.Thm_AvramDividend_Classical_avram_b24_integrable_signed_L1_error_to_nonnegative_error
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_arbitrary_intrinsic_source_mesh_centering
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_ruinclipped_zero_clock_full_cash_bound
import Theorems.Thm_AvramDividend_Classical_avram_b24_signed_ito_ledger_error_controls_positive_cash_gap_L1
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

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X :
SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ
≠ 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0) (hw_cont :
ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧
ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y
∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
(x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
(hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
(hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w
(riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 <
n) (σ : Ω → ℝ≥0) (hσstop : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0))) (hσbound : ∀
ω, σ ω ≤ (n : ℝ≥0)) (hσclip : ∀ ω, σ ω ≤ (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (F : Ω → ℝ)
(hFsource : ∀ ω, F ω = Real.exp (-(q * (σ ω : ℝ))) * w (if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D
ω then x + X.X (σ ω) ω - rightLimit D (σ ω) ω else riskProcess X x D (σ ω) ω) + (∫⁻ s in
paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s)))
∂(dividendMeasure D ω)).toReal) (hFI : Integrable F P) (hFiniteActivity : X.ν (Iio (0 : ℝ)) ≠ ⊤) (R
Jsmall : ℝ≥0 → Ω → ℝ) (hRsource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, Tendsto (fun k : ℕ =>
avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω) atTop (𝓝 (R u ω))) (hJsource : ∀ᵐ ω ∂P, ∀
u : ℝ≥0, Tendsto (fun k : ℕ => avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω) atTop
(𝓝 (Jsmall u ω))) : ∃ (G J : ℕ → Ω → ℝ), (∀ m, Integrable (G m) P) ∧ (∀ m, Integrable (J m) P) ∧ (∀
m, ∃ (S : Finset ℕ) (a b : ℕ → ℝ≥0) (WG WJ : ℕ → Ω → ℝ) (LG LJ : ℝ), (∀ i ∈ S, a i ≤ b i) ∧ (∀ i ∈
S, Measurable[𝓕.rightCont (a i)] (WG i)) ∧ (∀ i ∈ S, Measurable[𝓕.rightCont (a i)] (WJ i)) ∧ 0 ≤ LG
∧ 0 ≤ LJ ∧ (∀ i ∈ S, ∀ ω, ‖WG i ω‖ ≤ LG) ∧ (∀ i ∈ S, ∀ ω, ‖WJ i ω‖ ≤ LJ) ∧ (∀ ω, G m ω = ∑ i ∈ S,
(if σ ω ≤ a i then 0 else WG i ω) * (R (b i) ω - R (a i) ω)) ∧ (∀ ω, J m ω = ∑ i ∈ S, (if σ ω ≤ a i
then 0 else WJ i ω) * (Jsmall (b i) ω - Jsmall (a i) ω))) ∧ (∀ m, Integrable (fun ω => max 0 (F ω -
w x - G m ω - J m ω)) P) ∧ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m l : ℕ, N ≤ m → N ≤ l → (∫ ω, ‖G m ω - G l
ω‖ ∂P) ≤ ε) ∧ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m l : ℕ, N ≤ m → N ≤ l → (∫ ω, ‖J m ω - J l ω‖ ∂P) ≤ ε)
∧ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ, N ≤ m → (∫ ω, ‖max 0 (F ω - w x - G m ω - J m ω)‖ ∂P) ≤ ε) := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨G, J, E, hEI, hMesh, hPositive, hGC, hJC, hEC⟩ :=
    avram_b24_original_positiveclock_signed_ito_physmesh_L1_error_no_sign
      X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg hw_smooth
      hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn σ hσstop
      hσbound hσclip F hFsource hFI hFiniteActivity R Jsmall
      hRsource hJsource
  obtain ⟨Ep, hEpI, hMajor, hEpC⟩ :=
    avram_b24_integrable_signed_L1_error_to_nonnegative_error E hEI hEC
  have hGainI (k : ℕ) : Integrable (G k) P ∧ Integrable (J k) P := by
    obtain ⟨S,a,b,WG,WJ,LG,LJ,hab,hWG,hWJ,hLG,hLJ,hWGb,hWJb,hGf,hJf⟩ :=
      hMesh k
    obtain ⟨hGI,_,hJI,_⟩ :=
      avram_b24_original_arbitrary_intrinsic_source_mesh_centering
        X hX hFiniteActivity R Jsmall hRsource hJsource
        S a b WG WJ hab hWG hWJ σ hσstop LG LJ hLG hLJ hWGb hWJb
    refine ⟨hGI.congr ?_, hJI.congr ?_⟩
    · filter_upwards [] with ω
      exact (hGf ω).symm
    · filter_upwards [] with ω
      exact (hJf ω).symm
  have hZero :=
    avram_b24_original_ruinclipped_zero_clock_full_cash_bound
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
    · rw [hGf ω]
      apply Finset.sum_eq_zero
      intro i hi
      simp [hMask i]
    · rw [hJf ω]
      apply Finset.sum_eq_zero
      intro i hi
      simp [hMask i]
  have hCashAll (k : ℕ) :
      ∀ᵐ ω ∂P, F ω ≤ w x + G k ω + J k ω + Ep k ω := by
    filter_upwards [hPositive k] with ω hp
    by_cases hσ0 : σ ω = 0
    · obtain ⟨hg,hj⟩ := hMeshZero k ω hσ0
      have hle := hZero ω hσ0
      have hepos := (hMajor k ω).1
      rw [hg,hj]
      linarith
    · have hpos : 0 < σ ω := pos_iff_ne_zero.mpr hσ0
      linarith [hp hpos, (hMajor k ω).2]
  refine ⟨G,J,(fun k => (hGainI k).1),(fun k => (hGainI k).2),
    hMesh,?_,hGC,hJC,?_⟩
  · intro k
    exact (avram_b24_signed_ito_ledger_error_controls_positive_cash_gap_L1
      (F := F) (G := G k) (J := J k) (E := Ep k) (b := w x)
      hFI (hGainI k).1 (hGainI k).2 (hEpI k) (hCashAll k)).1
  · intro ε hε
    obtain ⟨N,hN⟩ := hEpC ε hε
    refine ⟨N,fun k hk => ?_⟩
    calc
      (∫ ω, ‖max 0 (F ω - w x - G k ω - J k ω)‖ ∂P) ≤
          ∫ ω, ‖Ep k ω‖ ∂P :=
        (avram_b24_signed_ito_ledger_error_controls_positive_cash_gap_L1
          (F := F) (G := G k) (J := J k) (E := Ep k) (b := w x)
          hFI (hGainI k).1 (hGainI k).2 (hEpI k) (hCashAll k)).2
      _ ≤ ε := hN k hk
