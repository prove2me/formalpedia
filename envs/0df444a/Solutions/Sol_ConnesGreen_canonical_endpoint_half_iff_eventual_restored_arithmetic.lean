-- Prove2me | solution 1 for ConnesGreen.canonical_endpoint_half_iff_eventual_restored_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T18:42:17.782585+00:00
-- url     : https://prove2.me/submissions/12eef9eb-0331-4a97-ac27-c9196512970e

import Theorems.Thm_ConnesGreen_canonical_restored_diagonal_original_ordered_endpoint
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

lemma ConnesGreen.original_scalar_lower_iff_all_slacks
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (A : K →L[ℂ] K) (a : ℝ) :
    a • (1 : K →L[ℂ] K) ≤ A ↔ ∀ η : ℝ, 0 < η → (a - η) • 1 ≤ A := by
  constructor
  · intro h η hη
    have hm : (a - η) • (1 : K →L[ℂ] K) ≤ a • 1 :=
      original_scalar_identity_mono (by linarith)
    exact hm.trans h
  · intro h
    have ht : Tendsto (fun η : ℝ => (a - η) • (1 : K →L[ℂ] K))
        (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds (a • (1 : K →L[ℂ] K))) := by
      simpa using ((tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds)).smul
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : K →L[ℂ] K))
          (nhdsWithin 0 (Ioi (0 : ℝ))) (nhds 1)))
    apply isClosed_Iic.mem_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact h η hη

lemma ConnesGreen.original_endpoint_half_iff_eventual_restored_markers
    (T : ℝ) (S : Finset CriticalZeros) (F : ℕ → Finset CriticalZeros) (μ : ℕ → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (hcT : c < T)
    (hself : ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T → ∀ n, IsSelfAdjoint (marker (canonicalPositiveCovariance t ht + μ n • 1 - canonicalTailCovariance t ht (F n))
              (canonicalSelectedSynthesis t ht S)))
    (hinner : ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T →
      Tendsto (fun n => marker (canonicalPositiveCovariance t ht + μ n • 1 - canonicalTailCovariance t ht (F n))
              (canonicalSelectedSynthesis t ht S)) atTop (nhds (canonicalPicardMarker t ht S)))
    (hordered : ∀ δ : ℝ, 0 < δ → ∃ d : ℝ, 0 < d ∧ c + d ≤ T ∧
      ∀ t : ℝ, ∀ ht : 0 < t, c < t → t < c + d →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          ‖marker (canonicalPositiveCovariance t ht + μ n • 1 - canonicalTailCovariance t ht (F n))
              (canonicalSelectedSynthesis t ht S) - canonicalSupportRightMarker c hc S‖ < δ) :
    (1 / 2 : ℝ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalSupportRightMarker c hc S ↔
    ∀ η : ℝ, 0 < η → η < 1 / 2 →
      ∃ d : ℝ, 0 < d ∧ c + d ≤ T ∧
        ∀ t : ℝ, ∀ ht : 0 < t, c < t → t < c + d →
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            (1 / 2 - η) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ marker (canonicalPositiveCovariance t ht + μ n • 1 - canonicalTailCovariance t ht (F n))
              (canonicalSelectedSynthesis t ht S) := by
  constructor
  · intro hh η hη hηhalf
    obtain ⟨d, hd, hdT, hnear⟩ := hordered η hη
    refine ⟨d, hd, hdT, ?_⟩
    intro t ht hct htd
    obtain ⟨N, hN⟩ := hnear t ht hct htd
    refine ⟨N, ?_⟩
    intro n hn
    apply original_scalar_lower_of_norm_close _ _
      ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (canonicalSupportRightMarker_spec c hc S).1).isSelfAdjoint
      (hself t ht ((le_of_lt htd).trans hdT) n) (1 / 2) η hh
    simpa only [norm_sub_rev] using (hN n hn).le
  · intro h
    apply (original_scalar_lower_iff_all_slacks _ (1 / 2)).mpr
    intro ζ hζ
    let η : ℝ := min (ζ / 2) (1 / 4)
    have hη : 0 < η := lt_min (half_pos hζ) (by norm_num)
    have hηhalf : η < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
    have hηζ : η ≤ ζ := (min_le_left _ _).trans (by linarith)
    obtain ⟨d, hd, hdT, hnear⟩ := h η hη hηhalf
    let t : ℝ := c + d / 2
    have ht : 0 < t := by dsimp [t]; linarith
    have hct : c < t := by dsimp [t]; linarith
    have htd : t < c + d := by dsimp [t]; linarith
    have htT : t ≤ T := (le_of_lt htd).trans hdT
    obtain ⟨N, hN⟩ := hnear t ht hct htd
    have hpic : (1 / 2 - η) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker t ht S :=
      isClosed_Ici.mem_of_tendsto (hinner t ht htT)
        (eventually_atTop.mpr ⟨N, hN⟩)
    have houter : canonicalPicardMarker t ht S ≤ canonicalSupportRightMarker c hc S := by
      simpa only [positiveWindowPicardMarker_eq t ht S] using
        (canonicalSupportRightMarker_spec c hc S).2.2.1.1
          (mem_image_of_mem (fun u => positiveWindowPicardMarker u S) hct)
    have hm : (1 / 2 - ζ) • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ] ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ (1 / 2 - η) • 1 :=
      original_scalar_identity_mono (by linarith)
    exact hm.trans (hpic.trans houter)
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
                    (1 / 4 : ℝ) * (∫ x : ℝ, ‖g x‖ ^ 2))))) := by
  obtain ⟨F, hmono, hrequests, hstage, huniform, hinner, hordered⟩ :=
    canonical_restored_diagonal_original_ordered_endpoint T hT S K μ ε hμ hε hε1 hμlim hεlim
  have hpos : ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T → ∀ n,
      IsStrictlyPositive (canonicalPositiveCovariance t ht + μ n • 1 - canonicalTailCovariance t ht (F n)) := by
    intro t ht htT n
    obtain ⟨Ptail, hcols, hsmall, hband, hactual⟩ := hstage n t ht htT
    exact (hband (μ n) le_rfl).2.1
  have hself : ∀ t : ℝ, ∀ ht : 0 < t, t ≤ T → ∀ n, IsSelfAdjoint (marker (canonicalPositiveCovariance t ht + μ n • 1 - canonicalTailCovariance t ht (F n))
              (canonicalSelectedSynthesis t ht S)) := by
    intro t ht htT n
    apply original_marker_selfAdjoint
    exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp (hpos t ht htT n).nonneg).isSelfAdjoint
  refine ⟨F, hmono, hrequests, hstage, huniform, hinner, hordered, ?_⟩
  intro c hc hcT
  rw [original_endpoint_half_iff_eventual_restored_markers T S F μ c hc hcT hself hinner (hordered c hc hcT)]
  constructor
  · intro hm η hη hηhalf
    obtain ⟨d, hd, hdT, hb⟩ := hm η hη hηhalf
    refine ⟨d, hd, hdT, ?_⟩
    intro t ht hct htd
    obtain ⟨N, hN⟩ := hb t ht hct htd
    refine ⟨N, ?_⟩
    intro n hn
    have hbβ : 0 < 1 / 2 - η := by linarith
    have hbβ1 : 1 / 2 - η < 1 := by linarith
    have ha := (canonical_finite_marker_lower_iff_arithmetic_tests t ht S (F n) (μ n)
      (1 / 2 - η) hbβ hbβ1 (hpos t ht ((le_of_lt htd).trans hdT) n)).mp (hN n hn)
    exact ha
  · intro ha η hη hηhalf
    obtain ⟨d, hd, hdT, hb⟩ := ha η hη hηhalf
    refine ⟨d, hd, hdT, ?_⟩
    intro t ht hct htd
    obtain ⟨N, hN⟩ := hb t ht hct htd
    refine ⟨N, ?_⟩
    intro n hn
    have hbβ : 0 < 1 / 2 - η := by linarith
    have hbβ1 : 1 / 2 - η < 1 := by linarith
    apply (canonical_finite_marker_lower_iff_arithmetic_tests t ht S (F n) (μ n)
      (1 / 2 - η) hbβ hbβ1 (hpos t ht ((le_of_lt htd).trans hdT) n)).mpr
    exact hN n hn
