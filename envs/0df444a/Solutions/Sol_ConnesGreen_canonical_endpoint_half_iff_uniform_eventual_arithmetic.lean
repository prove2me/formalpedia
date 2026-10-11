-- Prove2me | solution 1 for ConnesGreen.canonical_endpoint_half_iff_uniform_eventual_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T18:56:38.663466+00:00
-- url     : https://prove2.me/submissions/d7f9d383-590c-48b2-a99d-80f674727c1c

import Theorems.Thm_ConnesGreen_canonical_endpoint_half_iff_eventual_restored_arithmetic
import Theorems.Thm_ConnesGreen_canonical_finite_marker_lower_iff_arithmetic_tests
import Definitions.Def_ConnesGreen_RG0_original_actors
import Definitions.Def_WeilMarker_regularized_cost
import Definitions.Def_ConnesGreen_RG0_original_support_right_marker
open Complex MeasureTheory ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative WeilDefect.MarkerStability
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
open ContinuousLinearMap Filter Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
lemma ConnesGreen.original_scalar_identity_mono
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    {a b : ℝ} (hab : a ≤ b) : a • (1 : K →L[ℂ] K) ≤ b • 1 := by
  exact smul_le_smul_of_nonneg_right hab zero_le_one

lemma ConnesGreen.original_marker_selfAdjoint
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (N : K →L[ℂ] H) :
    IsSelfAdjoint (marker A N) := by
  have hc := hA.ringInverse.conj_adjoint N.adjoint
  simp only [ContinuousLinearMap.adjoint_adjoint] at hc
  simpa only [marker, selectedCost, WeilDefect.WDT13.operatorInverse] using
    ((IsSelfAdjoint.one (K →L[ℂ] K)).add hc).ringInverse

lemma ConnesGreen.original_scalar_lower_of_norm_close
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A B : K →L[ℂ] K) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (a η : ℝ) (ha : a • (1 : K →L[ℂ] K) ≤ A) (hη : ‖A - B‖ ≤ η) :
    (a - η) • (1 : K →L[ℂ] K) ≤ B := by
  have hd := IsSelfAdjoint.le_algebraMap_norm_self (hA.sub hB)
  have he : A - B ≤ η • (1 : K →L[ℂ] K) := hd.trans (by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      smul_le_smul_of_nonneg_right hη (zero_le_one : (0 : K →L[ℂ] K) ≤ 1))
  rw [sub_smul]
  exact sub_le_iff_le_add.mpr (by
    simpa only [add_comm] using ha.trans (sub_le_iff_le_add.mp he))

theorem solution
    (T : ℝ) (hT : 0 < T) (S : Finset CriticalZeros)
    (K : ℕ → Finset CriticalZeros) (μ ε : ℕ → ℝ)
    (hμ : ∀ n, 0 < μ n) (hε : ∀ n, 0 < ε n) (hε1 : ∀ n, ε n < 1)
    (hμlim : Tendsto μ atTop (nhds 0)) (hεlim : Tendsto ε atTop (nhds 0)) :
    ∃ F : ℕ → Finset CriticalZeros, Monotone F ∧
      (∀ n, S ⊆ F n ∧ K n ⊆ F n ∧ (∀ τ ∈ F n, reflectedZero τ ∈ F n)) ∧
      (∀ n, ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        ∃ Ptail : ℓ²({τ : CriticalZeros // τ ∉ (F n)}, ℂ) →L[ℂ] Physical t,
          (∀ τ, Ptail (lp.single 2 τ (1 : ℂ)) =
            positiveGreenColumn (fun σ => sourceEmbed t (actualGreenSource σ)) τ.1) ∧
          ‖Ptail ∘L Ptail.adjoint‖ + ‖canonicalTailCovariance t ht (F n)‖ < ε n ∧
          (∀ ν : ℝ, μ n ≤ ν →
            ‖canonicalTailCovariance t ht (F n)‖ ≤ ε n * ν ∧
            IsStrictlyPositive (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n)) ∧
            0 ≤ marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n))
                (canonicalSelectedSynthesis t ht S) ∧
            ‖marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n))
                (canonicalSelectedSynthesis t ht S)‖ ≤ ε n) ∧
          (∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
            Summable (fun τ : CriticalZeros => ‖if τ ∈ (F n) then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) ∧
            (∑' τ : CriticalZeros, ‖if τ ∈ (F n) then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) < ε n)) ∧
      (∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
          ‖canonicalTailCovariance t ht (F n)‖ < δ ∧
          (∀ ν : ℝ, μ n ≤ ν → ‖marker (canonicalPositiveCovariance t ht + ν • 1) (canonicalSelectedSynthesis t ht S) -
              marker (canonicalPositiveCovariance t ht + ν • 1 - canonicalTailCovariance t ht (F n))
                (canonicalSelectedSynthesis t ht S)‖ < δ) ∧
          (∀ g : ℝ → ℂ, SupportedTest t g → ‖sourceEmbed t (problemOneL g)‖ ^ 2 ≤ 1 →
            (∑' τ : CriticalZeros, ‖if τ ∈ F n then 0 else
              (zeroMult τ.1 : ℂ) * mellinHat (conv g (starInv g)) τ.1‖) < δ)) ∧
      (∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
        Tendsto (fun n => marker (canonicalPositiveCovariance t ht + μ n • 1 - canonicalTailCovariance t ht (F n))
              (canonicalSelectedSynthesis t ht S))
          atTop (nhds (canonicalPicardMarker t ht S))) ∧
      (∀ c : ℝ, ∀ hc : 0 ≤ c, c < T → ∀ δ : ℝ, 0 < δ →
        ∃ d : ℝ, 0 < d ∧ c + d ≤ T ∧
          ∀ t : ℝ, ∀ ht : 0 < t, c < t → t < c + d →
            ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
              ‖marker (canonicalPositiveCovariance t ht + μ n • 1 - canonicalTailCovariance t ht (F n))
              (canonicalSelectedSynthesis t ht S) - canonicalSupportRightMarker c hc S‖ < δ) ∧
      (∀ c : ℝ, ∀ hc : 0 ≤ c, c < T →
        ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalSupportRightMarker c hc S ↔
          ∀ η : ℝ, 0 < η → η < 1 / 2 →
      ∃ d : ℝ, 0 < d ∧ c + d ≤ T ∧
        ∀ t : ℝ, ∀ ht : 0 < t, c < t → t < c + d →
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            ∀ g : ℝ → ℂ, SupportedTest t g →
              ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 ≤
                ((1 / 2 - η)⁻¹ - 1) * (((weilDistribution (conv g (starInv g))).re) +
                  ‖(canonicalSelectedSynthesis t ht (F n)).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 +
                  μ n * ((∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) +
                    (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2))))) ∧
      (∀ c : ℝ, ∀ hc : 0 ≤ c, c < T →
        ((1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalSupportRightMarker c hc S ↔
          ∀ η : ℝ, 0 < η → η < 1 / 2 →
      ∃ d : ℝ, 0 < d ∧ c + d ≤ T ∧
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ∀ t : ℝ, ∀ ht : 0 < t, c < t → t < c + d →
            ∀ g : ℝ → ℂ, SupportedTest t g →
              ‖(canonicalSelectedSynthesis t ht S).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 ≤
                ((1 / 2 - η)⁻¹ - 1) * (((weilDistribution (conv g (starInv g))).re) +
                  ‖(canonicalSelectedSynthesis t ht (F n)).adjoint (sourceEmbed t (problemOneL g))‖ ^ 2 +
                  μ n * ((∫ x : ℝ, ‖iteratedDeriv 1 g x‖ ^ 2) +
                    (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2))))) := by
  obtain ⟨F, hmono, hrequests, hstage, huniform, hinner, hordered, hequiv⟩ :=
    canonical_endpoint_half_iff_eventual_restored_arithmetic T hT S K μ ε hμ hε hε1 hμlim hεlim
  refine ⟨F, hmono, hrequests, hstage, huniform, hinner, hordered, hequiv, ?_⟩
  intro c hc hcT
  constructor
  · intro hh η hη hηhalf
    have hhalf : 0 < η / 2 := half_pos hη
    obtain ⟨d₀, hd₀, hnear⟩ := Metric.tendsto_nhdsWithin_nhds.mp
      (canonicalSupportRightMarker_spec c hc S).2.2.2 (η / 2) hhalf
    let d : ℝ := min d₀ (T - c)
    have hd : 0 < d := lt_min hd₀ (sub_pos.mpr hcT)
    have hdT : c + d ≤ T := by
      have hm : d ≤ T - c := min_le_right _ _
      linarith
    have hev : ∀ᶠ n in atTop, ε n < η / 2 := (tendsto_order.mp hεlim).2 (η / 2) hhalf
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    refine ⟨d, hd, hdT, N, ?_⟩
    intro n hn t ht hct htd
    have htT : t ≤ T := (le_of_lt htd).trans hdT
    have hdist : dist t c < d₀ := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hct)]
      have hm : d ≤ d₀ := min_le_left _ _
      linarith
    have hpnear : ‖canonicalSupportRightMarker c hc S - canonicalPicardMarker t ht S‖ ≤ η / 2 := by
      simpa only [positiveWindowPicardMarker_eq t ht S, dist_eq_norm, norm_sub_rev] using
        (hnear hct hdist).le
    have hpSelf : IsSelfAdjoint (canonicalPicardMarker t ht S) :=
      ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (canonicalPicardMarker_spec t ht S).1).isSelfAdjoint
    have hoSelf : IsSelfAdjoint (canonicalSupportRightMarker c hc S) :=
      ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (canonicalSupportRightMarker_spec c hc S).1).isSelfAdjoint
    have hpic := original_scalar_lower_of_norm_close _ _ hoSelf hpSelf (1 / 2) (η / 2) hh hpnear
    have hpr : canonicalPicardMarker t ht S ≤ canonicalRegularizedMarker t ht S (μ n) :=
      (canonicalPicardMarker_spec t ht S).2.2.1.1 ⟨μ n, hμ n, rfl⟩
    have hrSelf : IsSelfAdjoint (canonicalRegularizedMarker t ht S (μ n)) := by
      have hs := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (sub_nonneg.mpr hpr)).isSelfAdjoint
      simpa only [sub_add_cancel] using hs.add hpSelf
    obtain ⟨Ptail, hcols, hsmall, hband, hactual⟩ := hstage n t ht htT
    have ha := (hband (μ n) le_rfl).2.1
    have hmSelf := original_marker_selfAdjoint _
      ((ContinuousLinearMap.nonneg_iff_isPositive _).mp ha.nonneg).isSelfAdjoint
      (canonicalSelectedSynthesis t ht S)
    have herr : ‖canonicalRegularizedMarker t ht S (μ n) -
        marker (canonicalPositiveCovariance t ht + μ n • 1 - canonicalTailCovariance t ht (F n))
          (canonicalSelectedSynthesis t ht S)‖ ≤ η / 2 :=
      ((hband (μ n) le_rfl).2.2.2).trans (hN n hn).le
    have hb := original_scalar_lower_of_norm_close _ _ hrSelf hmSelf
      (1 / 2 - η / 2) (η / 2) (hpic.trans hpr) herr
    have he : (1 / 2 - η / 2 - η / 2 : ℝ) = 1 / 2 - η := by ring
    rw [he] at hb
    have haTests := (canonical_finite_marker_lower_iff_arithmetic_tests t ht S (F n) (μ n)
      (1 / 2 - η) (by linarith) (by linarith) ha).mp hb
    exact haTests
  · intro hu
    apply (hequiv c hc hcT).mpr
    intro η hη hηhalf
    obtain ⟨d, hd, hdT, N, hN⟩ := hu η hη hηhalf
    refine ⟨d, hd, hdT, ?_⟩
    intro t ht hct htd
    exact ⟨N, fun n hn => hN n hn t ht hct htd⟩
