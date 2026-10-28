-- Prove2me | solution 1 for FiniteEnergyPlane.exists_norm_mul_fderiv_le_of_energy_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-24T21:14:15.707896+00:00
-- url     : https://prove2.me/submissions/7c7053ca-fa08-46fa-b600-3392ce1487f2

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_hofer_lemma
import Theorems.Thm_FiniteEnergyPlane_isJHolomorphicOn_comp_add_smul
import Theorems.Thm_JHolomorphic_exists_subseq_tendstoCInftyLocOn
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Complex.FiniteDimensional



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Gradient bound at a puncture (Wendl, Lemma 9.3, in disc coordinates). -/
theorem exists_norm_mul_fderiv_le_of_energy_lt_top_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (K : Set E) (hK : IsCompact K) (hKO : K ⊆ O)
    (u : ℂ → E) (hu : ContDiffOn ℝ ∞ u (ball 0 1 \ {0}))
    (hhol : JHolomorphic.IsJHolomorphicOn J (ball 0 1 \ {0}) u)
    (hmaps : Set.MapsTo u (ball 0 1 \ {0}) K)
    (hE : ∫⁻ z in ball 0 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) < ⊤) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * ‖fderiv ℝ u z‖ ≤ C := by
  classical
  set S : Set ℂ := ball 0 1 \ {0} with hS
  have hSo : IsOpen S := isOpen_ball.sdiff isClosed_singleton
  set g : ℂ → ℝ := fun z => ‖fderiv ℝ u z‖ with hg
  have hgc : ContinuousOn g S :=
    (hu.continuousOn_fderiv_of_isOpen hSo (by simp)).norm
  by_contra hcon
  push_neg at hcon
  have hz : ∀ k : ℕ, ∃ z : ℂ, z ≠ 0 ∧ ‖z‖ < 1 / 2 ∧ 4 * ((k : ℝ) + 1) < ‖z‖ * g z :=
    fun k => hcon (1 / 2) (by norm_num) (4 * ((k : ℝ) + 1))
  choose z hz0 hzr hzC using hz
  -- Hofer's lemma on a closed ball around `z k`
  have hH : ∀ k, ∃ ζ : ℂ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ‖z k‖ / 4 * g (z k) ≤ ε * g ζ ∧
      closedBall ζ ε ⊆ S ∧ ∀ y ∈ closedBall ζ ε, g y ≤ 2 * g ζ := by
    intro k
    set r := ‖z k‖ with hr
    have hr0 : 0 < r := norm_pos_iff.2 (hz0 k)
    set X : Set ℂ := closedBall (z k) (3 * r / 4) with hX
    have hXS : X ⊆ S := by
      intro w hw
      rw [hX, mem_closedBall, dist_eq_norm] at hw
      refine ⟨?_, ?_⟩
      · rw [mem_ball_zero_iff]
        have := norm_le_norm_add_norm_sub' w (z k)
        have h2 := hzr k
        linarith
      · intro h0
        rw [Set.mem_singleton_iff] at h0
        rw [h0, zero_sub, norm_neg] at hw
        linarith
    haveI : CompleteSpace X := isClosed_closedBall.isComplete.completeSpace_coe
    have hcont : Continuous (fun x : X => g x) :=
      hgc.comp_continuous continuous_subtype_val (fun x => hXS x.2)
    obtain ⟨x, ε, hε, hεle, hεg, hdist, hball⟩ :=
      hofer_lemma (fun x : X => g x) hcont (fun _ => norm_nonneg _)
        ⟨z k, mem_closedBall_self (by positivity)⟩ (r / 4) (by positivity)
    have hsubX : closedBall (x : ℂ) ε ⊆ X := by
      intro y hy
      rw [mem_closedBall] at hy
      rw [hX, mem_closedBall]
      have h1 : dist (x : ℂ) (z k) ≤ 2 * (r / 4) := hdist
      linarith [dist_triangle y x (z k)]
    refine ⟨x, ε, hε, ?_, hεg, hsubX.trans hXS, fun y hy => ?_⟩
    · have := hzr k
      linarith
    · exact hball ⟨y, hsubX hy⟩ hy
  choose ζ ε hεpos hεle hεg hsub hbd using hH
  set R : ℕ → ℝ := fun k => g (ζ k) with hR
  have hRk : ∀ k : ℕ, ((k : ℝ) + 1) < ε k * R k := by
    intro k
    have := hzC k
    have := hεg k
    simp only [hR]
    nlinarith
  have hRpos : ∀ k : ℕ, 0 < R k := by
    intro k
    have h1 := hRk k
    have h2 : 0 < ε k * R k := by linarith
    exact pos_of_mul_pos_right h2 (hεpos k).le
  have hRge : ∀ k : ℕ, (k : ℝ) + 1 < R k := by
    intro k
    have := hRk k
    have := hεle k
    have := hRpos k
    nlinarith
  have hRinv : ∀ k : ℕ, (R k)⁻¹ ≤ ε k := by
    intro k
    rw [inv_le_iff_one_le_mul₀ (hRpos k)]
    have := hRk k
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  -- the rescaled maps
  set v : ℕ → ℂ → E := fun k w => u (ζ k + (R k)⁻¹ • w) with hv
  have hmem : ∀ k, ∀ w ∈ ball (0 : ℂ) 1, ζ k + (R k)⁻¹ • w ∈ closedBall (ζ k) (ε k) := by
    intro k w hw
    rw [mem_ball_zero_iff] at hw
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 (hRpos k))]
    calc (R k)⁻¹ * ‖w‖ ≤ (R k)⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hw.le (inv_pos.2 (hRpos k)).le
      _ ≤ ε k := by rw [mul_one]; exact hRinv k
  have hA := fun k => isJHolomorphicOn_comp_add_smul J S u hhol (ζ k) (R k)⁻¹
  have hvhol : ∀ k, JHolomorphic.IsJHolomorphicOn J (ball 0 1) (v k) :=
    fun k w hw => (hA k).1 w (hsub k (hmem k w hw))
  have hvder : ∀ k, ∀ w ∈ ball (0 : ℂ) 1,
      ‖fderiv ℝ (v k) w‖ = (R k)⁻¹ * g (ζ k + (R k)⁻¹ • w) := by
    intro k w hw
    rw [(hA k).2 w (hsub k (hmem k w hw)), norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 (hRpos k))]
  have hv1 : ∀ k, ContDiffOn ℝ 1 (v k) (ball 0 1) := by
    intro k
    have haff : ContDiffOn ℝ 1 (fun w : ℂ => ζ k + (R k)⁻¹ • w) (ball 0 1) :=
      (by fun_prop : ContDiff ℝ 1 (fun w : ℂ => ζ k + (R k)⁻¹ • w)).contDiffOn
    exact (hu.of_le (by simp)).comp haff (fun w hw => hsub k (hmem k w hw))
  have hvmaps : ∀ k, Set.MapsTo (v k) (ball 0 1) K :=
    fun k w hw => hmaps (hsub k (hmem k w hw))
  have hvbd : ∀ k, ∀ w ∈ ball (0 : ℂ) 1, ‖fderiv ℝ (v k) w‖ ≤ 2 := by
    intro k w hw
    rw [hvder k w hw]
    have h := hbd k _ (hmem k w hw)
    have hi := inv_pos.2 (hRpos k)
    calc (R k)⁻¹ * g (ζ k + (R k)⁻¹ • w) ≤ (R k)⁻¹ * (2 * R k) :=
          mul_le_mul_of_nonneg_left h hi.le
      _ = 2 := by field_simp [(hRpos k).ne']
  have hv0 : ∀ k, ‖fderiv ℝ (v k) 0‖ = 1 := by
    intro k
    rw [hvder k 0 (mem_ball_self one_pos), smul_zero, add_zero]
    exact inv_mul_cancel₀ (hRpos k).ne'
  -- compactness
  obtain ⟨φ, hφ, vlim, hvlim, -, -, hconv⟩ :=
    JHolomorphic.exists_subseq_tendstoCInftyLocOn J (fun _ => J) O K hJ (fun _ => hJ)
      (fun K' _ _ m => Metric.tendstoUniformlyOn_iff.2 fun e he =>
        Eventually.of_forall fun _ _ _ => by simpa using he) hK hKO v hv1 hvhol hvmaps 2 hvbd
  have hU := hconv (closedBall 0 (1 / 2)) (closedBall_subset_ball (by norm_num))
    (isCompact_closedBall 0 _) 1
  have h0mem : (0 : ℂ) ∈ closedBall (0 : ℂ) (1 / 2) := mem_closedBall_self (by norm_num)
  have hlim1 : ‖fderiv ℝ vlim 0‖ = 1 := by
    have ht := (hU.tendsto_at h0mem).norm
    simp only [norm_iteratedFDeriv_one, hv0] at ht
    exact (tendsto_nhds_unique tendsto_const_nhds ht).symm
  have hcw : ContinuousAt (fun w => ‖fderiv ℝ vlim w‖) 0 :=
    ((hvlim.continuousOn_fderiv_of_isOpen isOpen_ball (by simp)).norm).continuousAt
      (ball_mem_nhds 0 one_pos)
  have hev : ∀ᶠ w in 𝓝 (0 : ℂ), (1 / 2 : ℝ) < ‖fderiv ℝ vlim w‖ :=
    hcw.eventually (lt_mem_nhds (by show (1 / 2 : ℝ) < ‖fderiv ℝ vlim 0‖; rw [hlim1]; norm_num))
  obtain ⟨δ₀, hδ₀, hδ₀b⟩ := Metric.eventually_nhds_iff_ball.1 hev
  set δ := min δ₀ (1 / 2) with hδ
  have hδpos : 0 < δ := lt_min hδ₀ (by norm_num)
  have hδle : δ ≤ 1 / 2 := min_le_right _ _
  have hδlarge : ∀ w ∈ ball (0 : ℂ) δ, (1 / 2 : ℝ) < ‖fderiv ℝ vlim w‖ :=
    fun w hw => hδ₀b w (ball_subset_ball (min_le_left _ _) hw)
  -- eventually, `‖Dv‖ > 1/4` on `ball 0 δ`
  have hev1 : ∀ᶠ ν in atTop, ∀ w ∈ ball (0 : ℂ) δ, (1 / 4 : ℝ) < ‖fderiv ℝ (v (φ ν)) w‖ := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hU (1 / 4) (by norm_num)] with ν hν w hw
    have hwc : w ∈ closedBall (0 : ℂ) (1 / 2) :=
      ball_subset_closedBall (ball_subset_ball hδle hw)
    have h1 := hν w hwc
    rw [dist_eq_norm] at h1
    have h2 := norm_sub_norm_le (iteratedFDeriv ℝ 1 vlim w) (iteratedFDeriv ℝ 1 (v (φ ν)) w)
    rw [norm_iteratedFDeriv_one, norm_iteratedFDeriv_one] at h2
    have h3 := hδlarge w hw
    linarith
  -- absolute continuity of the energy
  set F : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (g z ^ 2) with hF
  set V := volume (ball (0 : ℂ) 1) with hV
  have hV0 : V ≠ 0 := (measure_ball_pos volume (0 : ℂ) one_pos).ne'
  have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
  set η : ℝ≥0∞ := ENNReal.ofReal (δ ^ 2 / 16) * V with hη
  have hη0 : η ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.2 (by positivity)).ne' hV0
  obtain ⟨θ, hθ, hθs⟩ := exists_pos_setLIntegral_lt_of_measure_lt
    (μ := volume.restrict S) (f := F) hE.ne hη0
  have hball_vol : ∀ k, volume (ball (ζ k) (δ / R k)) = ENNReal.ofReal ((δ / R k) ^ 2) * V := by
    intro k
    rw [Measure.addHaar_ball volume (ζ k) (div_pos hδpos (hRpos k)).le, Complex.finrank_real_complex]
  have hsmall : Tendsto (fun n : ℕ => ENNReal.ofReal ((δ / ((n : ℝ) + 1)) ^ 2) * V) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (δ / ((n : ℝ) + 1)) ^ 2) atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ).pow 2
      simpa [div_eq_mul_inv, mul_zero] using this
    have h2 := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1) (Or.inr hVtop)
    simpa using h2
  have hev2 : ∀ᶠ ν in atTop, volume.restrict S (ball (ζ (φ ν)) (δ / R (φ ν))) < θ := by
    filter_upwards [hsmall.eventually (gt_mem_nhds hθ)] with ν hν
    refine lt_of_le_of_lt (Measure.restrict_apply_le _ _) ?_
    rw [hball_vol]
    refine lt_of_le_of_lt (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (zero_le)) hν
    have hφν : (ν : ℝ) + 1 ≤ R (φ ν) := by
      have := hRge (φ ν)
      have : (ν : ℝ) ≤ φ ν := by exact_mod_cast hφ.id_le ν
      linarith
    have hpos : (0 : ℝ) < (ν : ℝ) + 1 := by positivity
    have hd : δ / R (φ ν) ≤ δ / ((ν : ℝ) + 1) := div_le_div_of_nonneg_left hδpos.le hpos hφν
    exact pow_le_pow_left₀ (div_pos hδpos (hRpos _)).le hd 2
  obtain ⟨ν, hν1, hν2⟩ := (hev1.and hev2).exists
  -- the lower bound on the energy of `ball ζ (δ / R)`
  set k := φ ν with hk
  set s := ball (ζ k) (δ / R k) with hs
  have hsS : s ⊆ S := by
    refine (ball_subset_closedBall.trans (closedBall_subset_closedBall ?_)).trans (hsub k)
    calc δ / R k ≤ 1 / R k := div_le_div_of_nonneg_right (by linarith) (hRpos k).le
      _ = (R k)⁻¹ := one_div _
      _ ≤ ε k := hRinv k
  have hlow : ∀ y ∈ s, ENNReal.ofReal (R k ^ 2 / 16) ≤ F y := by
    intro y hy
    set w : ℂ := R k • (y - ζ k) with hw
    have hwb : w ∈ ball (0 : ℂ) δ := by
      rw [mem_ball_zero_iff, hw, norm_smul, Real.norm_eq_abs, abs_of_pos (hRpos k)]
      rw [hs, mem_ball, dist_eq_norm] at hy
      have := (lt_div_iff₀' (hRpos k)).1 hy
      linarith
    have hyw : ζ k + (R k)⁻¹ • w = y := by
      rw [hw, smul_smul, inv_mul_cancel₀ (hRpos k).ne', one_smul, add_sub_cancel]
    have h1 := hν1 w hwb
    rw [hvder k w (ball_subset_ball hδle |>.trans (ball_subset_ball (by norm_num)) hwb), hyw] at h1
    have hgy : R k / 4 ≤ g y := by
      have hi := hRpos k
      rw [inv_mul_eq_div, lt_div_iff₀ hi] at h1
      linarith
    refine ENNReal.ofReal_le_ofReal ?_
    have := pow_le_pow_left₀ (by linarith [hRpos k]) hgy 2
    nlinarith
  have hint : ∫⁻ x in s, F x ∂volume.restrict S = ∫⁻ x in s, F x := by
    rw [Measure.restrict_restrict measurableSet_ball, Set.inter_eq_self_of_subset_left hsS]
  have hge : η ≤ ∫⁻ x in s, F x ∂volume.restrict S := by
    rw [hint]
    calc η = ENNReal.ofReal (R k ^ 2 / 16) * volume s := by
          rw [hs, hball_vol, hη, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          field_simp [(hRpos k).ne']
      _ = ∫⁻ _ in s, ENNReal.ofReal (R k ^ 2 / 16) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in s, F x := setLIntegral_mono' measurableSet_ball hlow
  exact absurd (hθs s hν2) (not_lt.2 hge)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (K : Set E) (hK : IsCompact K) (hKO : K ⊆ O)
    (u : ℂ → E) (hu : ContDiffOn ℝ ∞ u (ball 0 1 \ {0}))
    (hhol : JHolomorphic.IsJHolomorphicOn J (ball 0 1 \ {0}) u)
    (hmaps : Set.MapsTo u (ball 0 1 \ {0}) K)
    (hE : ∫⁻ z in ball 0 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) < ⊤) :
    ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * ‖fderiv ℝ u z‖ ≤ C :=
  FiniteEnergyPlane.exists_norm_mul_fderiv_le_of_energy_lt_top_aux J O hJ K hK hKO u hu hhol hmaps hE
