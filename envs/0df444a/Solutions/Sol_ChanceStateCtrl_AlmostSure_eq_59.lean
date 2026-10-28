-- Prove2me | solution 1 for ChanceStateCtrl.AlmostSure.eq_59
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T21:30:51.249031+00:00
-- url     : https://prove2.me/submissions/bb9dc4bb-6986-4048-a9a3-3a1de93a6f8e

import Mathlib
import Definitions.Def_ChanceStateCtrl_AlmostSure_Setting

open MeasureTheory Filter Topology
open ChanceStateCtrl.AlmostSure

namespace ChanceStateCtrl.AlmostSure.Eq57Aux

variable {Ω : Type*} [MeasurableSpace Ω] {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem measurable_lam_simple (lam : Ω → StrongDual ℝ X)
    (hm : ∀ x : X, Measurable fun ω => lam ω x) (s : SimpleFunc Ω X) :
    Measurable fun ω => lam ω (s ω) := by
  have : (fun ω => lam ω (s ω)) =
      fun ω => ∑ c ∈ s.range, (s ⁻¹' {c}).indicator (fun ω => lam ω c) ω := by
    funext ω
    rw [Finset.sum_eq_single (s ω)]
    · simp [Set.indicator_of_mem]
    · intro c _ hc
      rw [Set.indicator_of_notMem]
      simpa [eq_comm] using hc
    · intro h; exact absurd (s.mem_range_self ω) h
  rw [this]
  refine Finset.measurable_sum _ fun c _ => ?_
  exact (hm c).indicator (s.measurableSet_fiber c)

theorem aesm_lam (P : Measure Ω) (lam : Ω → StrongDual ℝ X)
    (hm : ∀ x : X, Measurable fun ω => lam ω x) (y : Ω → X) (hy : AEStronglyMeasurable y P) :
    AEStronglyMeasurable (fun ω => lam ω (y ω)) P := by
  have hsm := hy.stronglyMeasurable_mk
  have h1 : Measurable fun ω => lam ω (hy.mk y ω) := by
    refine measurable_of_tendsto_metrizable (f := fun n ω => lam ω (hsm.approx n ω))
      (fun n => measurable_lam_simple lam hm _) ?_
    rw [tendsto_pi_nhds]
    intro ω
    exact ((lam ω).continuous.tendsto _).comp (hsm.tendsto_approx ω)
  refine ⟨_, h1.stronglyMeasurable, ?_⟩
  filter_upwards [hy.ae_eq_mk] with ω hω
  rw [hω]

theorem integrable_lam (P : Measure Ω) (lam : Ω → StrongDual ℝ X)
    (hlam : lam ∈ Lambda1 X P) (y : Lp X ⊤ P) :
    Integrable (fun ω => lam ω (y ω)) P := by
  refine ⟨aesm_lam P lam hlam.1 y (Lp.aestronglyMeasurable y), ?_⟩
  have hfin : eLpNormEssSup y P ≠ ⊤ := by
    have := Lp.eLpNorm_lt_top y
    rw [eLpNorm_exponent_top] at this
    exact this.ne
  unfold HasFiniteIntegral
  calc ∫⁻ ω, ‖lam ω (y ω)‖ₑ ∂P ≤ ∫⁻ ω, ‖lam ω‖ₑ * eLpNormEssSup y P ∂P := by
        apply lintegral_mono_ae
        filter_upwards [ae_le_eLpNormEssSup (f := fun ω => y ω) (μ := P)] with ω hω
        exact (lam ω).le_opENorm_of_le hω
    _ = (∫⁻ ω, ‖lam ω‖ₑ ∂P) * eLpNormEssSup y P := lintegral_mul_const' _ _ hfin
    _ < ⊤ := ENNReal.mul_lt_top hlam.2 hfin.lt_top

end ChanceStateCtrl.AlmostSure.Eq57Aux

open ChanceStateCtrl.AlmostSure.Eq57Aux

theorem solution {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace (closure D)]
    (Ainv : ChanceStateCtrl.PDE.L2 D →L[ℝ] C(closure D, ℝ))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ftil : Lp (ChanceStateCtrl.PDE.L2 D) ⊤ P) (α : ℝ) (us : ChanceStateCtrl.PDE.L2 D)
    (lamStar lamA lamSing : StrongDual ℝ (Linf D P)) (lam : Ω → StrongDual ℝ C(closure D, ℝ))
    (hlam : lam ∈ Lambda1 C(closure D, ℝ) P)
    (hrep : ∀ y : Linf D P, lamA y = ∫ ω, lam ω (y ω) ∂P)
    (hsing : IsSingular P lamSing) (hsplit : lamStar = lamA + lamSing)
    (h57 : ∀ y ∈ Kcone D P, lamSing y ≤ 0 ∧ ∫ ω, lam ω (y ω) ∂P ≤ 0)
    (hfeas : Gop P Ainv ftil α us ∈ Kcone D P) (hcompl : lamStar (Gop P Ainv ftil α us) = 0) :
    -- (a) `λ(·, ω) ≥ 0`, `P`-a.s.
    (∀ᵐ ω ∂P, ∀ φ : C(closure D, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ lam ω φ) ∧
    -- (b) (59)
    (lamSing (Gop P Ainv ftil α us) = 0 ∧ lamA (Gop P Ainv ftil α us) = 0 ∧
      ∫ ω, lam ω (Gop P Ainv ftil α us ω) ∂P = 0) ∧
    -- (c) pointwise complementarity
    (∀ᵐ ω ∂P, lam ω (Gop P Ainv ftil α us ω) = 0) := by
  -- (a) for a single nonnegative `φ`
  have hstep : ∀ φ : C(closure D, ℝ), (∀ x, 0 ≤ φ x) → ∀ᵐ ω ∂P, 0 ≤ lam ω φ := by
    intro φ hφ
    have hg : Integrable (fun ω => lam ω φ) P := by
      refine (integrable_lam P lam hlam (Lp.const ⊤ P φ)).congr ?_
      filter_upwards [Lp.coeFn_const (p := ⊤) (μ := P) φ] with ω h
      rw [h]; rfl
    apply ae_nonneg_of_forall_setIntegral_nonneg hg
    intro s hs _
    let yA : Linf D P := indicatorConstLp ⊤ hs (measure_ne_top P s) (-φ)
    have hK : yA ∈ Kcone D P := by
      show ∀ᵐ ω ∂P, ∀ x : closure D, yA ω x ≤ 0
      filter_upwards [indicatorConstLp_coeFn (p := ⊤) (hs := hs) (hμs := measure_ne_top P s)
        (c := -φ)] with ω h x
      simp only [yA]
      rw [h]
      by_cases hω : ω ∈ s
      · simp [Set.indicator_of_mem hω, hφ x]
      · simp [Set.indicator_of_notMem hω]
    have h1 := (h57 yA hK).2
    have h2 : ∫ ω, lam ω (yA ω) ∂P = ∫ ω, s.indicator (fun ω => -lam ω φ) ω ∂P := by
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := ⊤) (hs := hs) (hμs := measure_ne_top P s)
        (c := -φ)] with ω h
      simp only [yA]
      rw [h]
      by_cases hω : ω ∈ s
      · simp [Set.indicator_of_mem hω]
      · simp [Set.indicator_of_notMem hω]
    rw [h2, integral_indicator hs, integral_neg] at h1
    linarith
  have hnn : ∀ᵐ ω ∂P, ∀ φ : C(closure D, ℝ), (∀ x, 0 ≤ φ x) → 0 ≤ lam ω φ := by
    set S : Set C(closure D, ℝ) := {φ | ∀ x, 0 ≤ φ x}
    obtain ⟨T, hTS, hTc, hST⟩ :=
      (TopologicalSpace.IsSeparable.of_separableSpace S).exists_countable_dense_subset
    have hT : ∀ᵐ ω ∂P, ∀ φ ∈ T, 0 ≤ lam ω φ :=
      (ae_ball_iff hTc).2 (fun φ hφ => hstep φ (hTS hφ))
    filter_upwards [hT] with ω hω φ hφ
    have hcl : IsClosed {ψ : C(closure D, ℝ) | 0 ≤ lam ω ψ} :=
      isClosed_le continuous_const (lam ω).continuous
    exact (closure_minimal (fun ψ hψ => hω ψ hψ) hcl) (hST hφ)
  set G := Gop P Ainv ftil α us with hG
  have hfi := integrable_lam P lam hlam G
  obtain ⟨hs1, hs2⟩ := h57 G hfeas
  have hsum : lamA G + lamSing G = 0 := by
    rw [hsplit] at hcompl; simpa using hcompl
  rw [hrep] at hsum
  have hb1 : lamSing G = 0 := by linarith
  have hb3 : ∫ ω, lam ω (G ω) ∂P = 0 := by linarith
  refine ⟨hnn, ⟨hb1, by rw [hrep]; exact hb3, hb3⟩, ?_⟩
  have hpos : 0 ≤ᵐ[P] fun ω => -lam ω (G ω) := by
    have hf' : ∀ᵐ ω ∂P, ∀ x : closure D, G ω x ≤ 0 := hfeas
    filter_upwards [hnn, hf'] with ω h1 h2
    have := h1 (-(G ω)) (fun x => by simp only [ContinuousMap.neg_apply]; linarith [h2 x])
    simpa using this
  have := (integral_eq_zero_iff_of_nonneg_ae hpos hfi.neg).1 (by rw [integral_neg, hb3, neg_zero])
  filter_upwards [this] with ω hω
  simpa using hω
