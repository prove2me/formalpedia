-- Prove2me | solution 1 for FiniteEnergyPlane.tendsto_norm_mul_fderiv_of_energy_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-24T21:47:30.19179+00:00
-- url     : https://prove2.me/submissions/86e0ae73-5b4f-4f97-8afc-59c852d8d3b0

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_JHolomorphic_exists_subseq_tendstoCInftyLocOn
import Theorems.Thm_FiniteEnergyPlane_isJHolomorphicOn_comp_add_smul
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Calculus.FDeriv.Measurable



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem hasFDerivAt_affine_aux (a : ℂ) (c : ℝ) (ζ : ℂ) :
    HasFDerivAt (fun ζ : ℂ => a + (c : ℂ) * ζ) (c • ContinuousLinearMap.id ℝ ℂ) ζ := by
  have h1 : HasFDerivAt (fun ζ : ℂ => (c : ℂ) * ζ) (c • ContinuousLinearMap.id ℝ ℂ) ζ := by
    have e : (fun ζ : ℂ => (c : ℂ) * ζ) = fun ζ => c • ζ := by
      funext w; simp [Complex.real_smul]
    rw [e]
    exact (hasFDerivAt_id ζ).const_smul c
  simpa using h1.const_add a

/-- Decay of the weighted gradient at a puncture. -/
theorem tendsto_norm_mul_fderiv_of_energy_lt_top_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (K : Set E) (hK : IsCompact K) (hKO : K ⊆ O)
    (u : ℂ → E) (hu : ContDiffOn ℝ ∞ u (ball 0 1 \ {0}))
    (hhol : JHolomorphic.IsJHolomorphicOn J (ball 0 1 \ {0}) u)
    (hmaps : Set.MapsTo u (ball 0 1 \ {0}) K)
    (hE : ∫⁻ z in ball 0 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) < ⊤)
    (hG : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * ‖fderiv ℝ u z‖ ≤ C) :
    Tendsto (fun z : ℂ => ‖z‖ * ‖fderiv ℝ u z‖) (𝓝[≠] 0) (𝓝 0) := by
  set S : Set ℂ := ball 0 1 \ {0} with hS
  set g : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) with hg
  have hgm : Measurable g := ((measurable_fderiv ℝ u).norm.pow_const 2).ennreal_ofReal
  obtain ⟨r, hr, C, hC⟩ := hG
  -- small energy near the puncture
  have htail : ∀ M : ℝ≥0∞, 0 < M → ∃ s₁ : ℝ, 0 < s₁ ∧ ∫⁻ z in ball 0 s₁ ∩ S, g z < M := by
    intro M hM
    have hfin : ∫⁻ z, g z ∂(volume.restrict S) ≠ ⊤ := hE.ne
    have hvol : Tendsto ((volume.restrict S) ∘ fun s : ℝ => ball (0 : ℂ) s) (𝓝[>] 0) (𝓝 0) := by
      have hup : Tendsto (fun s : ℝ => ENNReal.ofReal s ^ 2 * (NNReal.pi : ℝ≥0∞)) (𝓝[>] 0)
          (𝓝 0) := by
        have h1 : Tendsto (fun s : ℝ => ENNReal.ofReal s) (𝓝[>] 0) (𝓝 0) := by
          have := (ENNReal.continuous_ofReal.tendsto 0).mono_left
            (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
          simpa using this
        have h2 : Tendsto (fun s : ℝ => ENNReal.ofReal s ^ 2) (𝓝[>] 0) (𝓝 0) := by
          have := ((ENNReal.continuous_pow 2).tendsto 0).comp h1
          simpa [Function.comp_def] using this
        have h3 := ENNReal.Tendsto.mul_const h2 (Or.inr ENNReal.coe_ne_top)
          (b := (NNReal.pi : ℝ≥0∞))
        simpa using h3
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
        (fun _ => bot_le) (fun s => ?_)
      simp only [Function.comp_apply]
      rw [← Complex.volume_ball]
      exact Measure.restrict_apply_le _ _
    have h := tendsto_setLIntegral_zero hfin hvol
    obtain ⟨s₁, hs₁, hs₁'⟩ := ((h.eventually (gt_mem_nhds hM)).and self_mem_nhdsWithin).exists
    refine ⟨s₁, hs₁', ?_⟩
    rw [Measure.restrict_restrict measurableSet_ball] at hs₁
    exact hs₁
  by_contra hnt
  rw [Metric.tendsto_nhds] at hnt
  push_neg at hnt
  obtain ⟨ε, hε, hfr⟩ := hnt
  set R0 := min r 1 with hR0def
  have hR0 : 0 < R0 := lt_min hr one_pos
  have hR0r : R0 ≤ r := min_le_left _ _
  have hR01 : R0 ≤ 1 := min_le_right _ _
  -- a sequence of bad points tending to the puncture
  have hseq : ∀ k : ℕ, ∃ z : ℂ, z ≠ 0 ∧ ‖z‖ < R0 / (2 * (k + 1)) ∧
      ε ≤ ‖z‖ * ‖fderiv ℝ u z‖ := by
    intro k
    have hpos : 0 < R0 / (2 * (k + 1)) := by positivity
    have he : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ≠ 0 ∧ ‖z‖ < R0 / (2 * (k + 1)) := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (0 : ℂ) hpos)] with z hz hzρ
      exact ⟨hz, by simpa using hzρ⟩
    obtain ⟨z, hz, hz'⟩ := (hfr.and_eventually he).exists
    refine ⟨z, hz'.1, hz'.2, ?_⟩
    have h0 : 0 ≤ ‖z‖ * ‖fderiv ℝ u z‖ := by positivity
    simpa [Real.dist_eq, abs_of_nonneg h0] using hz
  choose zs hzs0 hzsR hzsε using hseq
  set lam : ℕ → ℝ := fun k => ‖zs k‖ / 2 with hlam
  have hlam0 : ∀ k, 0 < lam k := fun k => by
    simp only [hlam]; have := norm_pos_iff.mpr (hzs0 k); positivity
  have hzsR0 : ∀ k, ‖zs k‖ < R0 / 2 := fun k => by
    have h := hzsR k
    have : R0 / (2 * ((k : ℝ) + 1)) ≤ R0 / 2 := by
      apply div_le_div_of_nonneg_left hR0.le (by norm_num)
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    linarith
  -- the rescaled points
  have hnorm_mul : ∀ k (ζ : ℂ), ‖(lam k : ℂ) * ζ‖ = lam k * ‖ζ‖ := fun k ζ => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hlam0 k)]
  have hpt : ∀ k, ∀ ζ ∈ ball (0 : ℂ) 1, lam k < ‖zs k + (lam k : ℂ) * ζ‖ ∧
      ‖zs k + (lam k : ℂ) * ζ‖ < 3 * lam k := by
    intro k ζ hζ
    rw [mem_ball_zero_iff] at hζ
    have h1 : ‖zs k‖ ≤ ‖zs k + (lam k : ℂ) * ζ‖ + ‖(lam k : ℂ) * ζ‖ := by
      have := norm_sub_le (zs k + (lam k : ℂ) * ζ) ((lam k : ℂ) * ζ)
      simpa using this
    have h2 := norm_add_le (zs k) ((lam k : ℂ) * ζ)
    rw [hnorm_mul] at h1 h2
    have h3 : lam k * ‖ζ‖ < lam k := by
      have := hlam0 k; nlinarith
    have h4 : ‖zs k‖ = 2 * lam k := by simp only [hlam]; ring
    constructor <;> linarith
  have hptS : ∀ k, ∀ ζ ∈ ball (0 : ℂ) 1, zs k + (lam k : ℂ) * ζ ∈ S := by
    intro k ζ hζ
    obtain ⟨h1, h2⟩ := hpt k ζ hζ
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff]
      have : 3 * lam k < R0 := by
        have := hzsR0 k; simp only [hlam]; linarith
      linarith
    · intro h0
      rw [Set.mem_singleton_iff] at h0
      rw [h0, norm_zero] at h1
      linarith [hlam0 k]
  set w : ℕ → ℂ → E := fun k ζ => u (zs k + (lam k : ℂ) * ζ) with hw
  have hwd : ∀ k, ∀ ζ ∈ ball (0 : ℂ) 1, fderiv ℝ (w k) ζ =
      (fderiv ℝ u (zs k + (lam k : ℂ) * ζ)).comp (lam k • ContinuousLinearMap.id ℝ ℂ) := by
    intro k ζ hζ
    have hd : DifferentiableAt ℝ u (zs k + (lam k : ℂ) * ζ) := (hhol _ (hptS k ζ hζ)).1
    exact (hd.hasFDerivAt.comp ζ (hasFDerivAt_affine_aux (zs k) (lam k) ζ)).fderiv
  have hwn : ∀ k, ∀ ζ ∈ ball (0 : ℂ) 1,
      ‖fderiv ℝ (w k) ζ‖ = lam k * ‖fderiv ℝ u (zs k + (lam k : ℂ) * ζ)‖ := by
    intro k ζ hζ
    rw [hwd k ζ hζ]
    have : (fderiv ℝ u (zs k + (lam k : ℂ) * ζ)).comp (lam k • ContinuousLinearMap.id ℝ ℂ) =
        lam k • fderiv ℝ u (zs k + (lam k : ℂ) * ζ) := by
      ext x; simp
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (hlam0 k)]
  have hw1 : ∀ k, ContDiffOn ℝ 1 (w k) (ball 0 1) := by
    intro k
    have haff : ContDiff ℝ ∞ (fun ζ : ℂ => zs k + (lam k : ℂ) * ζ) :=
      contDiff_const.add (contDiff_const.mul contDiff_id)
    exact (hu.comp haff.contDiffOn (fun ζ hζ => hptS k ζ hζ)).of_le (by exact_mod_cast le_top)
  have hwhol : ∀ k, JHolomorphic.IsJHolomorphicOn J (ball 0 1) (w k) := by
    intro k ζ hζ
    have h := (isJHolomorphicOn_comp_add_smul J S u hhol (zs k) (lam k)).1 ζ
      (by simpa [Complex.real_smul] using hptS k ζ hζ)
    have e : (fun x : ℂ => u (zs k + lam k • x)) = w k := by
      funext x; simp [hw, Complex.real_smul]
    rwa [e] at h
  have hwmaps : ∀ k, Set.MapsTo (w k) (ball 0 1) K := fun k ζ hζ => hmaps (hptS k ζ hζ)
  have hwC : ∀ k, ∀ ζ ∈ ball (0 : ℂ) 1, ‖fderiv ℝ (w k) ζ‖ ≤ C := by
    intro k ζ hζ
    rw [hwn k ζ hζ]
    obtain ⟨h1, h2⟩ := hpt k ζ hζ
    have hy0 : zs k + (lam k : ℂ) * ζ ≠ 0 := (hptS k ζ hζ).2
    have hyr : ‖zs k + (lam k : ℂ) * ζ‖ < r := by
      have := hzsR0 k; simp only [hlam] at h2; linarith
    have := hC _ hy0 hyr
    have hD0 : 0 ≤ ‖fderiv ℝ u (zs k + (lam k : ℂ) * ζ)‖ := norm_nonneg _
    nlinarith
  have hconst : JHolomorphic.TendstoCInftyLocOn (fun _ : ℕ => J) J O := by
    intro K' _ _ m
    intro U hU
    exact Eventually.of_forall fun _ x _ => refl_mem_uniformity hU
  obtain ⟨φ, hφ, v, hv, -, -, hconv⟩ :=
    JHolomorphic.exists_subseq_tendstoCInftyLocOn J (fun _ => J) O K hJ (fun _ => hJ) hconst hK
      hKO w hw1 hwhol hwmaps C hwC
  have hcb : closedBall (0 : ℂ) (1 / 2) ⊆ ball 0 1 := closedBall_subset_ball (by norm_num)
  have h1 := hconv (closedBall 0 (1 / 2)) hcb (isCompact_closedBall _ _) 1
  rw [Metric.tendstoUniformlyOn_iff] at h1
  have hD : ∀ η > 0, ∀ᶠ n in atTop, ∀ ζ ∈ closedBall (0 : ℂ) (1 / 2),
      |‖fderiv ℝ v ζ‖ - ‖fderiv ℝ (w (φ n)) ζ‖| < η := by
    intro η hη
    filter_upwards [h1 η hη] with n hn ζ hζ
    have := hn ζ hζ
    rw [dist_eq_norm] at this
    have h2 := abs_norm_sub_norm_le (iteratedFDeriv ℝ 1 v ζ)
      (iteratedFDeriv ℝ 1 (w (φ n)) ζ)
    rw [norm_iteratedFDeriv_one, norm_iteratedFDeriv_one] at h2
    linarith
  have hw0 : ∀ k, ε / 2 ≤ ‖fderiv ℝ (w k) 0‖ := by
    intro k
    rw [hwn k 0 (mem_ball_self one_pos), mul_zero, add_zero]
    have := hzsε k
    simp only [hlam]
    linarith
  have h0half : (0 : ℂ) ∈ closedBall (0 : ℂ) (1 / 2) := mem_closedBall_self (by norm_num)
  have hv0 : 3 * ε / 8 < ‖fderiv ℝ v 0‖ := by
    obtain ⟨n, hn⟩ := (hD (ε / 8) (by positivity)).exists
    have h := hn 0 h0half
    have := hw0 (φ n)
    rw [abs_lt] at h
    linarith
  have hvc : ContinuousOn (fderiv ℝ v) (ball 0 1) :=
    hv.continuousOn_fderiv_of_isOpen isOpen_ball (by exact_mod_cast le_top)
  have hvca : ContinuousAt (fun ζ => ‖fderiv ℝ v ζ‖) 0 :=
    (hvc.continuousAt (ball_mem_nhds 0 one_pos)).norm
  have hev := hvca.eventually (lt_mem_nhds hv0)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hδ'⟩ := hev
  set δ' := min δ (1 / 2) with hδ'def
  have hδ'0 : 0 < δ' := lt_min hδ (by norm_num)
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  have hδ'h : δ' ≤ 1 / 2 := min_le_right _ _
  set M : ℝ≥0∞ := ENNReal.ofReal (ε ^ 2 * δ' ^ 2 / 16) * (NNReal.pi : ℝ≥0∞) with hM
  have hMpos : 0 < M := by
    apply ENNReal.mul_pos
    · exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
    · rw [ne_eq, ENNReal.coe_eq_zero, ← NNReal.coe_eq_zero, NNReal.coe_real_pi]
      exact Real.pi_ne_zero
  obtain ⟨s₁, hs₁, hs₁E⟩ := htail M hMpos
  have hlim : ∀ᶠ n : ℕ in atTop, R0 / n < s₁ :=
    (tendsto_const_div_atTop_nhds_zero_nat R0).eventually (gt_mem_nhds hs₁)
  obtain ⟨n, hn, hnR, hn1⟩ :=
    ((hD (ε / 8) (by positivity)).and (hlim.and (eventually_ge_atTop 1))).exists
  set k := φ n with hk
  have hnk : n ≤ k := hφ.id_le n
  -- the small ball around `zs k`
  set B := ball (zs k) (lam k * δ') with hB
  have hζ : ∀ y ∈ B, (y - zs k) / (lam k : ℂ) ∈ ball (0 : ℂ) δ' ∧
      zs k + (lam k : ℂ) * ((y - zs k) / (lam k : ℂ)) = y := by
    intro y hy
    have hl : (lam k : ℂ) ≠ 0 := by exact_mod_cast (hlam0 k).ne'
    refine ⟨?_, by field_simp; ring⟩
    rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hlam0 k), div_lt_iff₀ (hlam0 k)]
    rw [mem_ball, dist_eq_norm] at hy
    linarith
  have hBsub : B ⊆ ball 0 s₁ ∩ S := by
    intro y hy
    obtain ⟨hz1, hz2⟩ := hζ y hy
    have hz1' : (y - zs k) / (lam k : ℂ) ∈ ball (0 : ℂ) 1 :=
      ball_subset_ball (hδ'h.trans (by norm_num)) hz1
    have hS' := hptS k _ hz1'
    have hb := (hpt k _ hz1').2
    rw [hz2] at hS' hb
    refine ⟨?_, hS'⟩
    rw [mem_ball_zero_iff]
    have hk1 : R0 / (2 * ((k : ℝ) + 1)) ≤ R0 / (2 * n) := by
      apply div_le_div_of_nonneg_left hR0.le
      · have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        positivity
      · have : (n : ℝ) ≤ k := by exact_mod_cast hnk
        linarith
    have h2n : R0 / (2 * n) = R0 / n / 2 := by ring
    have := hzsR k
    have hRn : 0 ≤ R0 / n := by positivity
    simp only [hlam] at hb
    linarith
  have hlow : ∀ y ∈ B, ENNReal.ofReal (ε ^ 2 / (16 * lam k ^ 2)) ≤ g y := by
    intro y hy
    obtain ⟨hz1, hz2⟩ := hζ y hy
    set ζ := (y - zs k) / (lam k : ℂ)
    have hz1' : ζ ∈ ball (0 : ℂ) 1 := ball_subset_ball (hδ'h.trans (by norm_num)) hz1
    have hzc : ζ ∈ closedBall (0 : ℂ) (1 / 2) :=
      ball_subset_closedBall (ball_subset_ball hδ'h hz1)
    have hvζ : 3 * ε / 8 < ‖fderiv ℝ v ζ‖ := hδ' (by
      rw [dist_zero_right]; exact lt_of_lt_of_le (mem_ball_zero_iff.mp hz1) hδ'δ)
    have hdiff := hn ζ hzc
    rw [abs_lt] at hdiff
    have hwζ : ε / 4 < lam k * ‖fderiv ℝ u y‖ := by
      have := hwn k ζ hz1'
      rw [hz2] at this
      linarith
    have hl := hlam0 k
    have hge : ε / (4 * lam k) ≤ ‖fderiv ℝ u y‖ := by
      rw [div_le_iff₀ (by positivity)]; linarith
    apply ENNReal.ofReal_le_ofReal
    calc ε ^ 2 / (16 * lam k ^ 2) = (ε / (4 * lam k)) ^ 2 := by field_simp; ring
      _ ≤ ‖fderiv ℝ u y‖ ^ 2 := pow_le_pow_left₀ (by positivity) hge 2
  have hint_low : M ≤ ∫⁻ y in B, g y := by
    calc M = ∫⁻ _ in B, ENNReal.ofReal (ε ^ 2 / (16 * lam k ^ 2)) := by
          rw [setLIntegral_const, hB, Complex.volume_ball, hM, ← mul_assoc,
            ← ENNReal.ofReal_pow (by have := hlam0 k; positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          have := (hlam0 k).ne'
          field_simp
      _ ≤ ∫⁻ y in B, g y := setLIntegral_mono hgm hlow
  have hint_up : ∫⁻ y in B, g y ≤ ∫⁻ y in ball 0 s₁ ∩ S, g y := lintegral_mono_set hBsub
  exact (lt_irrefl M) (hint_low.trans_lt (hint_up.trans_lt hs₁E))

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (K : Set E) (hK : IsCompact K) (hKO : K ⊆ O)
    (u : ℂ → E) (hu : ContDiffOn ℝ ∞ u (ball 0 1 \ {0}))
    (hhol : JHolomorphic.IsJHolomorphicOn J (ball 0 1 \ {0}) u)
    (hmaps : Set.MapsTo u (ball 0 1 \ {0}) K)
    (hE : ∫⁻ z in ball 0 1 \ {0}, ENNReal.ofReal (‖fderiv ℝ u z‖ ^ 2) < ⊤)
    (hG : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * ‖fderiv ℝ u z‖ ≤ C) :
    Tendsto (fun z : ℂ => ‖z‖ * ‖fderiv ℝ u z‖) (𝓝[≠] 0) (𝓝 0) :=
  FiniteEnergyPlane.tendsto_norm_mul_fderiv_of_energy_lt_top_aux J O hJ K hK hKO u hu hhol hmaps hE hG
