-- Prove2me | solution 1 for ErgSingMFG.Abelian.theorem_5_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T18:52:16.952486+00:00
-- url     : https://prove2.me/submissions/ed9c866b-2a6d-487e-94b4-d65c0e48a4a5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ErgSingMFG_Abelian_Analytic
import Definitions.Def_ErgSingMFG_Abelian_Systems
import Definitions.Def_ErgSingMFG_Abelian_Model
import Theorems.Thm_AGT_brouwer_fixed_point
import Theorems.Thm_ErgSingMFG_Abelian_theorem_4_2
import Theorems.Thm_ErgSingMFG_Abelian_theorem_4_4
import Theorems.Thm_ErgSingMFG_Abelian_lemma_5_1
import Theorems.Thm_ErgSingMFG_Abelian_theorem_4_2_step_2_limit_law
import Theorems.Thm_ErgSingMFG_Abelian_theorem_5_2_step_1_jacobian
import Theorems.Thm_ErgSingMFG_Abelian_theorem_5_2_step_2_barrier_value
import Theorems.Thm_ErgSingMFG_Abelian_theorem_5_2_step_2_gradient
import Theorems.Thm_ErgSingMFG_Abelian_exists_decrFundHat

open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
open ErgSingMFG.Abelian



theorem zeroNear (Ψ : ℝ × ℝ → ℝ → ℝ × ℝ) (p0 : ℝ × ℝ) (U : Set (ℝ × ℝ)) (hU : IsOpen U)
    (hp0 : p0 ∈ U) (ε0 : ℝ) (hε0 : 0 < ε0)
    (hc : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => Ψ q.1 q.2) (U ×ˢ Ioo (-ε0) ε0))
    (h0 : Ψ p0 0 = 0) (D : ℝ × ℝ →L[ℝ] ℝ × ℝ) (hD : HasFDerivAt (fun p => Ψ p 0) D p0)
    (hdet : LinearMap.det (D : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) ≠ 0) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ r in 𝓝 (0 : ℝ), ∃ p, dist p p0 < η ∧ Ψ p r = 0 := by
  set L : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
    (LinearMap.equivOfDetNeZero (D : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) hdet).toContinuousLinearEquiv with hLdef
  have hLD : ∀ v, L v = D v := fun v => rfl
  set M : ℝ := ‖(L.symm : ℝ × ℝ →L[ℝ] ℝ × ℝ)‖ + 1 with hM
  have hMpos : 0 < M := by positivity
  have hLs : ∀ v, ‖L.symm v‖ ≤ M * ‖v‖ := by
    intro v
    have := (L.symm : ℝ × ℝ →L[ℝ] ℝ × ℝ).le_opNorm v
    have : ‖(L.symm : ℝ × ℝ →L[ℝ] ℝ × ℝ) v‖ = ‖L.symm v‖ := rfl
    nlinarith [norm_nonneg v]
  -- differentiability estimate
  have hlo := hD.isLittleO.def (c := 1 / (2 * M)) (by positivity)
  obtain ⟨ρ1, hρ1, hball1⟩ := Metric.eventually_nhds_iff.mp hlo
  obtain ⟨ρ2, hρ2, hball2⟩ := Metric.isOpen_iff.mp hU p0 hp0
  set ρ := min (min ρ1 ρ2) η / 2 with hρ
  have hρpos : 0 < ρ := by positivity
  have hρ1' : ρ < ρ1 := by
    have := min_le_left (min ρ1 ρ2) η; have := min_le_left ρ1 ρ2; linarith
  have hρ2' : ρ < ρ2 := by
    have := min_le_left (min ρ1 ρ2) η; have := min_le_right ρ1 ρ2; linarith
  have hρη : ρ < η := by have := min_le_right (min ρ1 ρ2) η; linarith
  have hKU : closedBall p0 ρ ⊆ U := fun p hp =>
    hball2 (lt_of_le_of_lt (mem_closedBall.mp hp) hρ2')
  -- uniform continuity on a compact set
  set K : Set ((ℝ × ℝ) × ℝ) := closedBall p0 ρ ×ˢ closedBall (0 : ℝ) (ε0 / 2) with hK
  have hKsub : K ⊆ U ×ˢ Ioo (-ε0) ε0 := by
    rintro ⟨p, r⟩ ⟨hp, hr⟩
    refine ⟨hKU hp, ?_⟩
    rw [mem_closedBall, Real.dist_eq, sub_zero] at hr
    constructor <;> [linarith [neg_abs_le r]; linarith [le_abs_self r]]
  have hKc : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have huc := Metric.uniformContinuousOn_iff.mp
    (hKc.uniformContinuousOn_of_continuous (hc.mono hKsub)) (ρ / (2 * M)) (by positivity)
  obtain ⟨δ, hδ, hδK⟩ := huc
  have hev : ∀ᶠ r in 𝓝 (0 : ℝ), r ∈ ball (0 : ℝ) (min δ (ε0 / 2)) :=
    ball_mem_nhds _ (by positivity)
  filter_upwards [hev] with r hr
  rw [mem_ball, Real.dist_eq, sub_zero] at hr
  have hrδ : |r| < δ := lt_of_lt_of_le hr (min_le_left _ _)
  have hrε : |r| < ε0 / 2 := lt_of_lt_of_le hr (min_le_right _ _)
  have hrK : r ∈ closedBall (0 : ℝ) (ε0 / 2) := by
    rw [mem_closedBall, Real.dist_eq, sub_zero]; exact hrε.le
  have h0K : (0 : ℝ) ∈ closedBall (0 : ℝ) (ε0 / 2) := by
    rw [mem_closedBall, dist_self]; positivity
  -- the Newton-type map
  set g : ℝ × ℝ → ℝ × ℝ := fun p => p - L.symm (Ψ p r) with hg
  have hgc : ContinuousOn g (closedBall p0 ρ) := by
    apply continuousOn_id.sub
    apply L.symm.continuous.comp_continuousOn
    have : ContinuousOn (fun p : ℝ × ℝ => ((p, r) : (ℝ × ℝ) × ℝ)) (closedBall p0 ρ) :=
      (continuous_id.prodMk continuous_const).continuousOn
    exact (hc.mono hKsub).comp this (fun p hp => ⟨hp, hrK⟩)
  have hgm : MapsTo g (closedBall p0 ρ) (closedBall p0 ρ) := by
    intro p hp
    have hpd : dist p p0 ≤ ρ := mem_closedBall.mp hp
    have e1 : ‖Ψ p 0 - Ψ p0 0 - D (p - p0)‖ ≤ 1 / (2 * M) * ‖p - p0‖ :=
      hball1 (lt_of_le_of_lt hpd hρ1')
    rw [h0, sub_zero] at e1
    have e2 : dist (Ψ p r) (Ψ p 0) < ρ / (2 * M) := by
      have := hδK (p, r) ⟨hp, hrK⟩ (p, 0) ⟨hp, h0K⟩ (by
        rw [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero]
        simpa using hrδ)
      simpa using this
    rw [dist_eq_norm] at e2
    have hpn : ‖p - p0‖ ≤ ρ := by rw [← dist_eq_norm]; exact hpd
    have key : g p - p0 = L.symm (D (p - p0) - Ψ p r) := by
      have : L.symm (D (p - p0)) = p - p0 := by rw [← hLD]; simp
      rw [map_sub, this]
      show p - L.symm (Ψ p r) - p0 = (p - p0) - L.symm (Ψ p r)
      abel
    rw [mem_closedBall, dist_eq_norm, key]
    calc ‖L.symm (D (p - p0) - Ψ p r)‖ ≤ M * ‖D (p - p0) - Ψ p r‖ := hLs _
      _ ≤ M * (‖Ψ p 0 - D (p - p0)‖ + ‖Ψ p r - Ψ p 0‖) := by
          gcongr
          calc ‖D (p - p0) - Ψ p r‖ = ‖-(Ψ p 0 - D (p - p0)) - (Ψ p r - Ψ p 0)‖ := by
                congr 1; abel
            _ ≤ ‖-(Ψ p 0 - D (p - p0))‖ + ‖Ψ p r - Ψ p 0‖ := norm_sub_le _ _
            _ = _ := by rw [norm_neg]
      _ ≤ M * (1 / (2 * M) * ρ + ρ / (2 * M)) := by
          gcongr
          · exact e1.trans (by gcongr)
      _ = ρ := by field_simp; ring
  obtain ⟨p, hp, hfix⟩ := AGT.brouwer_fixed_point (convex_closedBall p0 ρ)
    (isCompact_closedBall p0 ρ) ⟨p0, mem_closedBall_self hρpos.le⟩ g hgc hgm
  refine ⟨p, lt_of_le_of_lt (mem_closedBall.mp hp) hρη, ?_⟩
  have : L.symm (Ψ p r) = 0 := by
    have := hfix; simp only [hg] at this
    have h2 : p - L.symm (Ψ p r) = p - 0 := by rw [this, sub_zero]
    exact sub_right_injective h2
  simpa using congrArg L this

section Helpers


lemma F_strictMono (m : Model) (h33 : Asm33 m) : StrictMonoOn m.F (Ici 0) := by
  obtain ⟨-, -, -, -, -, -, hFc, -, -, -, -, hder, -⟩ := h33
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) hFc
  intro x hx
  rw [interior_Ici] at hx
  exact (hder x hx).1

lemma f_pos (m : Model) (h33 : Asm33 m) (x : ℝ) (hx : 0 < x) : 0 < m.f x := by
  obtain ⟨-, -, -, -, -, -, -, hfc, hnn, -, -, hder, -⟩ := h33
  have hmono : StrictMonoOn m.f (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) hfc
    intro y hy
    rw [interior_Ici] at hy
    exact (hder y hy).2
  have := hmono ((mem_Ici.mpr le_rfl)) (mem_Ici.mpr hx.le) hx
  linarith [(hnn 0 le_rfl).2]

lemma Finv_eq (m : Model) (h33 : Asm33 m) (z θ : ℝ) (hz : 0 ≤ z) (hF : m.F z = θ) :
    Finv m θ = z := by
  have hsm := F_strictMono m h33
  unfold Finv
  split_ifs with h
  · rcases hz.lt_or_eq with hz' | hz'
    · have := hsm (mem_Ici.mpr le_rfl) (mem_Ici.mpr hz) hz'
      linarith
    · exact hz'
  · have hex : ∃ a ∈ Ici (0 : ℝ), m.F a = θ := ⟨z, hz, hF⟩
    obtain ⟨h1, h2⟩ := Function.invFunOn_pos hex
    exact hsm.injOn h1 (mem_Ici.mpr hz) (h2.trans hF.symm)

lemma Finv_spec (m : Model) (h33 : Asm33 m) (θ : ℝ) (hθ : m.F 0 < θ) :
    0 ≤ Finv m θ ∧ m.F (Finv m θ) = θ := by
  have h33' := h33
  obtain ⟨-, -, -, -, -, -, hFc, -, -, -, -, -, -, hFtop, -⟩ := h33
  obtain ⟨N, hN⟩ := (tendsto_atTop.mp hFtop θ).exists_forall_of_atTop
  have hN0 : ∀ y ≥ max N 0, θ ≤ m.F y := fun y hy => hN y (le_trans (le_max_left _ _) hy)
  have hivt := intermediate_value_Icc (le_max_right N 0) (hFc.mono Icc_subset_Ici_self)
  obtain ⟨z, hz, hFz⟩ := hivt ⟨hθ.le, hN0 _ le_rfl⟩
  have := Finv_eq m h33' z θ hz.1 hFz
  rw [this]
  exact ⟨hz.1, hFz⟩

lemma mp_nonneg (m : Model) (y : ℝ) : 0 ≤ mp m y := by
  unfold mp Sp; positivity

lemma mp_pos (m : Model) (h21 : Asm21 m) (y : ℝ) (hy : 0 < y) : 0 < mp m y := by
  have := h21.2.2.1 y hy
  unfold mp Sp; positivity

lemma mp_contOn (m : Model) (h21 : Asm21 m) : ContinuousOn (mp m) (Ioi 0) := by
  obtain ⟨hb, hσ, hσpos, -, -⟩ := h21
  have hg : ContinuousOn (fun z => 2 * m.b z / m.σ z ^ 2) (Ioi 0) := by
    apply ContinuousOn.div (continuousOn_const.mul hb.continuousOn) (hσ.continuousOn.pow 2)
    intro z hz; exact pow_ne_zero 2 (hσpos z hz).ne'
  have hI : ContinuousOn (fun x => ∫ z in (1 : ℝ)..x, 2 * m.b z / m.σ z ^ 2) (Ioi 0) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hsub : uIcc 1 x ⊆ Ioi 0 := by
      intro z hz
      have := hz.1
      simp only [mem_Ioi]
      exact lt_of_lt_of_le (lt_min one_pos hx) this
    exact (intervalIntegral.integral_hasDerivAt_right ((hg.mono hsub).intervalIntegrable)
      (hg.stronglyMeasurableAtFilter isOpen_Ioi x hx)
      (hg.continuousAt (Ioi_mem_nhds hx))).continuousAt
  have hSp : ContinuousOn (Sp m) (Ioi 0) := by
    unfold Sp; exact (hI.neg).rexp
  unfold mp
  apply ContinuousOn.div continuousOn_const ((hσ.continuousOn.pow 2).mul hSp)
  intro z hz
  exact mul_ne_zero (pow_ne_zero 2 (hσpos z hz).ne') (by unfold Sp; exact (Real.exp_pos _).ne')

variable {Ω : Type} [MeasurableSpace Ω]

lemma refl_lt_false (m : Model) (S : Setting Ω) (h21 : Asm21 m) (h22 : Asm22 m) (hFR : FundReq m)
    (hS : IsSetting S) (x : ℝ) (hx : 0 < x) (ν X : ℝ≥0 → Ω → ℝ) (hν : IsControl S ν)
    (hX : IsStateSol m S x ν X) (a a' : ℝ) (ha : 0 < a) (haa : a < a')
    (hR : ReflAt S a ν X) (hR' : ReflAt S a' ν X) : False := by
  obtain ⟨-, hL⟩ := theorem_4_2_step_2_limit_law m S h21 h22 hFR hS a x ha hx ν X hν hX hR
  obtain ⟨-, hL'⟩ := theorem_4_2_step_2_limit_law m S h21 h22 hFR hS a' x (ha.trans haa) hx ν X hν hX hR'
  set Z := ∫ z in Ioi a, mp m z with hZ
  set μ := (volume.restrict (Ici a)).withDensity (fun y => ENNReal.ofReal (mp m y / Z)) with hμ
  set μ' := (volume.restrict (Ici a')).withDensity
    (fun y => ENNReal.ofReal (mp m y / ∫ z in Ioi a', mp m z)) with hμ'
  have := hL.1
  have := hL'.1
  have heq : μ = μ' := ext_of_forall_integral_eq_of_IsFiniteMeasure
    (fun g => tendsto_nhds_unique (hL.2 g) (hL'.2 g))
  have h1 : μ' (Iio a') = 0 := by
    rw [hμ', withDensity_apply _ measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
    have : Iio a' ∩ Ici a' = ∅ := by
      ext y; simp only [mem_inter_iff, mem_Iio, mem_Ici, mem_empty_iff_false, iff_false]
      intro ⟨h1, h2⟩; linarith
    rw [this, Measure.restrict_empty, lintegral_zero_measure]
  have hZpos : 0 < Z := by
    by_contra hZ'
    push Not at hZ'
    have h0 : (fun y => ENNReal.ofReal (mp m y / Z)) = 0 := by
      funext y
      exact ENNReal.ofReal_eq_zero.mpr (div_nonpos_of_nonneg_of_nonpos (mp_nonneg m y) hZ')
    have : μ univ = 0 := by rw [hμ, h0, withDensity_zero]; rfl
    rw [measure_univ] at this
    exact one_ne_zero this
  obtain ⟨y0, hy0, hmin⟩ := (isCompact_Icc (a := a) (b := a')).exists_isMinOn
    (nonempty_Icc.mpr haa.le) ((mp_contOn m h21).mono (fun y hy => lt_of_lt_of_le ha hy.1))
  have hκ : 0 < mp m y0 := mp_pos m h21 y0 (lt_of_lt_of_le ha hy0.1)
  have h2 : 0 < μ (Iio a') := by
    rw [hμ, withDensity_apply _ measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
    have hset : Iio a' ∩ Ici a = Ico a a' := by
      ext y; simp only [mem_inter_iff, mem_Iio, mem_Ici, mem_Ico]; tauto
    rw [hset]
    have hle : ∫⁻ y in Ico a a', ENNReal.ofReal (mp m y0 / Z) ≤
        ∫⁻ y in Ico a a', ENNReal.ofReal (mp m y / Z) := by
      apply setLIntegral_mono' measurableSet_Ico
      intro y hy
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_right _ hZpos.le
      exact hmin ⟨hy.1, hy.2.le⟩
    refine lt_of_lt_of_le ?_ hle
    rw [setLIntegral_const, Real.volume_Ico]
    apply ENNReal.mul_pos
    · exact (ENNReal.ofReal_pos.mpr (div_pos hκ hZpos)).ne'
    · exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  rw [heq, h1] at h2
  exact lt_irrefl _ h2

lemma refl_eq (m : Model) (S : Setting Ω) (h21 : Asm21 m) (h22 : Asm22 m) (hFR : FundReq m)
    (hS : IsSetting S) (x : ℝ) (hx : 0 < x) (ν X : ℝ≥0 → Ω → ℝ) (hν : IsControl S ν)
    (hX : IsStateSol m S x ν X) (a a' : ℝ) (ha : 0 < a)
    (hR : ReflAt S a ν X) (hR' : ReflAt S a' ν X) : a' = a := by
  rcases lt_trichotomy a' a with h | h | h
  · exfalso
    set a'' := max a' (a / 2) with ha''
    have h''pos : 0 < a'' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have h''lt : a'' < a := max_lt h (by linarith)
    have hR'' : ReflAt S a'' ν X := by
      filter_upwards [hR, hR'] with ω h1 h2
      refine ⟨fun t => le_trans h''lt.le (h1.1 t), ?_⟩
      refine measure_mono_null ?_ h2.2
      intro t ht
      exact ⟨ht.1, lt_of_le_of_lt (le_max_left _ _) ht.2⟩
    exact refl_lt_false m S h21 h22 hFR hS x hx ν X hν hX a'' a h''pos h''lt hR'' hR
  · exact h
  · exact (refl_lt_false m S h21 h22 hFR hS x hx ν X hν hX a a' ha h hR hR').elim
end Helpers



lemma sysAt_of_phi (m : Model) (h33 : Asm33 m) (φ : ℝ → ℝ) (r a θ : ℝ) (ha : 0 < a)
    (hφpos : 0 < φ a) (hθ : m.F 0 < θ)
    (hint1 : IntegrableOn (fun y => φ y * Pi m y θ r) (Ioi a))
    (hint2 : IntegrableOn (fun y => (m.f y - Finv m θ) * mp m y) (Ioi a))
    (hK : KHat m φ a θ r = 0) (hG : GHat m a θ = 0) : SysAt m φ r a θ := by
  have hF0 : 0 ≤ m.F 0 := (h33.2.2.2.2.2.2.2.2.1 0 le_rfl).1
  obtain ⟨hz, hFz⟩ := Finv_spec m h33 θ hθ
  refine ⟨ha, by linarith, hint1, ?_, Finv m θ, hz, hFz, hint2, hG⟩
  unfold KHat at hK
  rcases div_eq_zero_iff.mp hK with h | h
  · exact h
  · exact absurd h hφpos.ne'

theorem solution {Ω : Type} [MeasurableSpace Ω] (m : Model) (S : Setting Ω)
    (h21 : Asm21 m) (h22 : Asm22 m) (h33 : Asm33 m) (hFR : FundReq m) (h43 : Asm43 m)
    (h41 : ∀ r ∈ Ioc (0 : ℝ) 1, ∀ θ > 0, ∃ xh, xHatProp m r θ xh)
    (hS : IsSetting S) (x : ℝ) (hx : 0 < x) :
    ((∀ r ∈ Ioc (0 : ℝ) 1, ∃ (ν X : ℝ≥0 → Ω → ℝ) (θ a : ℝ),
        IsDiscEq m S r x ν X θ ∧ ReflAt S a ν X) ∧
      ∃ (ν X : ℝ≥0 → Ω → ℝ) (θ a : ℝ), IsErgEq m S x ν X θ ∧ ReflAt S a ν X) ∧
    ∀ (ν X : ℝ → ℝ≥0 → Ω → ℝ) (θ xs : ℝ → ℝ) (νe Xe : ℝ≥0 → Ω → ℝ) (θe xe : ℝ),
      (∀ r ∈ Ioc (0 : ℝ) 1, IsDiscEq m S r x (ν r) (X r) (θ r) ∧ ReflAt S (xs r) (ν r) (X r)) →
      IsErgEq m S x νe Xe θe → ReflAt S xe νe Xe →
      Tendsto (fun r => (xs r, θ r)) (𝓝[>] 0) (𝓝 (xe, θe)) ∧
      Tendsto (fun r : ℝ => (r : EReal) * V m S x (θ r) r) (𝓝[>] 0) (𝓝 (lamStar m S x θe)) := by
  obtain ⟨hc, hb', -⟩ := id h43
  -- the fundamental solutions `φ̂_r`, `r ∈ (−c, 1)`
  have hex : ∀ r ∈ Ioo (-m.c) 1, ∃ φ : ℝ → ℝ, IsDecrFundHat m r φ := by
    intro r hr
    exact exists_decrFundHat m h21 hFR r (r + m.c) (by linarith [hr.1])
      (fun y hy => by linarith [hb' y hy])
  choose! φh hφ using hex
  have h0mem : (0 : ℝ) ∈ Ioo (-m.c) 1 := ⟨by linarith, one_pos⟩
  have h51 := lemma_5_1 m h21 h22 h33 hFR h43 φh hφ
  -- `∫ₐ^∞ f m′ < ∞`
  have hfm : ∀ a > 0, IntegrableOn (fun y => m.f y * mp m y) (Ioi a) := by
    intro a ha
    have h1 := ((h51.1 a ha 1 one_pos 0 h0mem).2)
    have h2 := (h22 a ha).const_mul (Finv m 1)
    have := h1.add h2
    refine this.congr_fun (fun y _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]; ring
  have h41' : ∀ r ∈ Ioc (0 : ℝ) 1, Asm41 m r := fun r hr =>
    ⟨⟨m.c, hc, fun y hy => by linarith [hb' y hy, hr.1]⟩, h41 r hr⟩
  have T42 := fun r (hr : r ∈ Ioc (0 : ℝ) 1) =>
    theorem_4_2 m S r x hr.1 hx h21 h22 h33 hFR (h41' r hr) hfm hS
  have T44 := theorem_4_4 m S x hx h21 h22 h33 hFR h43 hS
  refine ⟨⟨fun r hr => ?_, T44.1⟩, ?_⟩
  · obtain ⟨ν, X, θ, hE⟩ := (T42 r hr).1
    obtain ⟨a, hR, -⟩ := (T42 r hr).2.2.1 ν X θ hE
    exact ⟨ν, X, θ, a, hE, hR⟩
  intro ν X θ xs νe Xe θe xe hfam hE hRe
  obtain ⟨-, hSys43, hlam⟩ := T44.2.2.2.1 νe Xe θe xe hE hRe
  have hsys0 := hSys43 (φh 0) (hφ 0 h0mem)
  -- discounted systems
  have hsysr : ∀ r ∈ Ioo (0 : ℝ) 1, SysAt m (φh r) r (xs r) (θ r) := by
    intro r hr
    have hr' : r ∈ Ioc (0 : ℝ) 1 := ⟨hr.1, hr.2.le⟩
    obtain ⟨hEr, hRr⟩ := hfam r hr'
    obtain ⟨a, hRa, -, hSys⟩ := (T42 r hr').2.2.1 _ _ _ hEr
    have hSa := hSys (φh r) (hφ r ⟨by linarith [hr.1], hr.2⟩)
    have := refl_eq m S h21 h22 hFR hS x hx (ν r) (X r) hEr.2.1.1 hEr.2.2.1 a (xs r) hSa.1 hRa hRr
    rw [this]; exact hSa
  obtain ⟨hxe, hθe, hint0, hK0, ze, hze, hFze, hintz, hGz⟩ := hsys0
  have hzepos : 0 < ze := by
    rcases hze.lt_or_eq with h | h
    · exact h
    · exfalso
      subst h
      have hpos : 0 < ∫ y in Ioi xe, (m.f y - 0) * mp m y := by
        rw [setIntegral_pos_iff_support_of_nonneg_ae _ hintz]
        · calc (0 : ℝ≥0∞) < volume (Ioi xe) := by rw [Real.volume_Ioi]; exact ENNReal.zero_lt_top
            _ ≤ _ := by
              apply measure_mono
              intro y hy
              refine ⟨?_, hy⟩
              rw [Function.mem_support, sub_zero]
              exact (mul_pos (f_pos m h33 y (hxe.trans hy)) (mp_pos m h21 y (hxe.trans hy))).ne'
        · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_)
          show 0 ≤ (m.f y - 0) * mp m y
          rw [sub_zero]
          exact mul_nonneg (h33.2.2.2.2.2.2.2.2.1 y (hxe.trans hy).le).2 (mp_nonneg m y)
      linarith
  have hθF : m.F 0 < θe := by
    rw [← hFze]; exact F_strictMono m h33 (mem_Ici.mpr le_rfl) (mem_Ici.mpr hze) hzepos
  -- the map `Ψ(p, r) = Φ(p.1, p.2; r)`
  set Ψ : ℝ × ℝ → ℝ → ℝ × ℝ := fun p r => Phi m φh p.1 p.2 r with hΨ
  set ε0 := min m.c 1 with hε0
  have hε0pos : 0 < ε0 := lt_min hc one_pos
  have hcont : ContinuousOn (fun q : (ℝ × ℝ) × ℝ => Ψ q.1 q.2)
      ((Ioi 0 ×ˢ Ioi 0) ×ˢ Ioo (-ε0) ε0) := by
    have h2 := h51.2
    have he : Continuous (fun q : (ℝ × ℝ) × ℝ => ((q.1.1, q.1.2, q.2) : ℝ × ℝ × ℝ)) := by
      fun_prop
    refine h2.comp he.continuousOn ?_
    rintro ⟨⟨p1, p2⟩, r⟩ ⟨⟨hp1, hp2⟩, hr⟩
    refine ⟨hp1, hp2, ?_, ?_⟩
    · have := hr.1; have := min_le_left m.c 1; simp only; linarith
    · have := hr.2; have := min_le_right m.c 1; simp only; linarith
  have hΨ0 : Ψ (xe, θe) 0 = 0 := by
    simp only [hΨ, Phi, KHat, GHat]
    rw [hK0, zero_div, Finv_eq m h33 ze θe hze hFze, hGz]; rfl
  obtain ⟨ε, hε, -, -, B, hB, hJ⟩ :=
    theorem_5_2_step_1_jacobian m h21 h22 h33 hFR h43 φh hφ xe θe
      ⟨hxe, hθe, hint0, hK0, ze, hze, hFze, hintz, hGz⟩
  obtain ⟨D, hD, hdet⟩ := hJ 0 ⟨by linarith, hε⟩ (xe, θe) (mem_of_mem_nhds hB)
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := isOpen_Ioi.prod isOpen_Ioi
  have hconv : Tendsto (fun r => (xs r, θ r)) (𝓝[>] 0) (𝓝 (xe, θe)) := by
    rw [Metric.tendsto_nhds]
    intro η hη
    set η0 := min xe (θe - m.F 0) with hη0
    have hη0pos : 0 < η0 := lt_min hxe (by linarith)
    have hZ := zeroNear Ψ (xe, θe) _ hU ⟨hxe, hθe⟩ ε0 hε0pos hcont hΨ0 D hD hdet.ne'
      (min η η0) (lt_min hη hη0pos)
    filter_upwards [nhdsWithin_le_nhds hZ, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)]
      with r hr hr01
    obtain ⟨p, hpd, hpz⟩ := hr
    have hd1 : dist p.1 xe < η0 :=
      lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hpd (min_le_right _ _))
    have hd2 : dist p.2 θe < η0 :=
      lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le hpd (min_le_right _ _))
    rw [Real.dist_eq] at hd1 hd2
    have hp1 : 0 < p.1 := by
      have := (abs_lt.mp hd1).1; have := min_le_left xe (θe - m.F 0); linarith
    have hp2 : m.F 0 < p.2 := by
      have := (abs_lt.mp hd2).1; have := min_le_right xe (θe - m.F 0); linarith
    have hF0 : 0 ≤ m.F 0 := (h33.2.2.2.2.2.2.2.2.1 0 le_rfl).1
    have hrm : r ∈ Ioo (-m.c) 1 := ⟨by linarith [hr01.1], hr01.2⟩
    have hint := h51.1 p.1 hp1 p.2 (by linarith) r hrm
    have hPz : KHat m (φh r) p.1 p.2 r = 0 ∧ GHat m p.1 p.2 = 0 := by
      have := congrArg Prod.fst hpz; have h' := congrArg Prod.snd hpz
      exact ⟨this, h'⟩
    have hSp : SysAt m (φh r) r p.1 p.2 :=
      sysAt_of_phi m h33 (φh r) r p.1 p.2 hp1 ((hφ r hrm).2.1 p.1 hp1) hp2 hint.1 hint.2
        hPz.1 hPz.2
    have hr' : r ∈ Ioc (0 : ℝ) 1 := ⟨hr01.1, hr01.2.le⟩
    obtain ⟨e1, e2⟩ := (T42 r hr').2.2.2 (φh r) (hφ r hrm) p.1 p.2 (xs r) (θ r) hSp
      (hsysr r hr01)
    have : (xs r, θ r) = p := by rw [← e1, ← e2]
    rw [this]
    exact lt_of_lt_of_le hpd (min_le_left _ _)
  refine ⟨hconv, ?_⟩
  -- the value
  rw [hlam]
  set v : ℝ → ℝ → ℝ := fun r z => (V m S z (θ r) r).toReal with hv
  have hstep : ∀ r ∈ Ioo (0 : ℝ) 1,
      (r : EReal) * V m S x (θ r) r = ((r * v r x : ℝ) : EReal) ∧
      |r * v r x - (m.b (xs r) + m.π (xs r) (θ r))| ≤ r * |x - xs r| := by
    intro r hr
    have hr' : r ∈ Ioc (0 : ℝ) 1 := ⟨hr.1, hr.2.le⟩
    obtain ⟨ha, hθr, hint, hK, -⟩ := hsysr r hr
    have hgr := theorem_5_2_step_2_gradient m S r (θ r) hr.1 hθr h21 h22 h33 hFR (h41' r hr') hS
    have hbv := theorem_5_2_step_2_barrier_value m S r (θ r) hr.1 hθr h21 h22 h33 hFR
      (h41' r hr') hS (φh r) (hφ r ⟨by linarith [hr.1], hr.2⟩) (xs r) ha hint hK
    obtain ⟨hfin, hC2, hder⟩ := hgr
    have hVx : V m S x (θ r) r = ((v r x : ℝ) : EReal) :=
      (EReal.coe_toReal (hfin x hx).1 (hfin x hx).2).symm
    have hVa : V m S (xs r) (θ r) r = ((v r (xs r) : ℝ) : EReal) :=
      (EReal.coe_toReal (hfin _ ha).1 (hfin _ ha).2).symm
    have hbar : r * v r (xs r) = m.b (xs r) + m.π (xs r) (θ r) := by
      rw [hVa, ← EReal.coe_mul] at hbv; exact EReal.coe_eq_coe_iff.mp hbv
    refine ⟨by rw [hVx, EReal.coe_mul], ?_⟩
    have hdiff : ∀ y ∈ Ioi (0 : ℝ), DifferentiableAt ℝ (v r) y := fun y hy =>
      (hC2.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds hy)
    have hbd : ∀ y ∈ Ioi (0 : ℝ), ‖deriv (v r) y‖ ≤ 1 := fun y hy => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hder y hy).1, (hder y hy).2]
    have hmv := (convex_Ioi (0 : ℝ)).norm_image_sub_le_of_norm_deriv_le hdiff hbd
      (show xs r ∈ Ioi 0 from ha) (show x ∈ Ioi 0 from hx)
    rw [← hbar, ← mul_sub, abs_mul, abs_of_pos hr.1]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul] at hmv
    exact mul_le_mul_of_nonneg_left hmv hr.1.le
  have hxs : Tendsto xs (𝓝[>] 0) (𝓝 xe) := (continuous_fst.tendsto _).comp hconv
  have hA : Tendsto (fun r => m.b (xs r) + m.π (xs r) (θ r)) (𝓝[>] 0)
      (𝓝 (m.b xe + m.π xe θe)) := by
    have hb : ContinuousAt m.b xe := h21.1.continuousOn.continuousAt (Ioi_mem_nhds hxe)
    have hπ : ContinuousAt (fun p : ℝ × ℝ => m.π p.1 p.2) (xe, θe) :=
      h33.2.1.continuousOn.continuousAt ((isOpen_Ioi.prod isOpen_Ioi).mem_nhds ⟨hxe, hθe⟩)
    exact (hb.tendsto.comp hxs).add (hπ.tendsto.comp hconv)
  have hE : Tendsto (fun r => r * |x - xs r|) (𝓝[>] 0) (𝓝 0) := by
    have := (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 (0 : ℝ)))).mul
      ((continuous_abs.tendsto _).comp ((tendsto_const_nhds (x := x)).sub hxs))
    simpa using this
  have hw : Tendsto (fun r => r * v r x) (𝓝[>] 0) (𝓝 (m.b xe + m.π xe θe)) := by
    have hdiffT : Tendsto (fun r => r * v r x - (m.b (xs r) + m.π (xs r) (θ r))) (𝓝[>] 0)
        (𝓝 0) := by
      apply squeeze_zero_norm' _ hE
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr
      rw [Real.norm_eq_abs]; exact (hstep r hr).2
    have := hdiffT.add hA
    simpa using this
  have hw' := (continuous_coe_real_ereal.tendsto _).comp hw
  refine Tendsto.congr' ?_ hw'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr
  exact ((hstep r hr).1).symm