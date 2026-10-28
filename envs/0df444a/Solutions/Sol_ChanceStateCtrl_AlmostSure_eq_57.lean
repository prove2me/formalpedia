-- Prove2me | solution 1 for ChanceStateCtrl.AlmostSure.eq_57
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T21:29:41.80699+00:00
-- url     : https://prove2.me/submissions/eeb9165d-bfbb-4e8f-ab36-b73d2d9997a5

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

/-- `y · 1_A` as an element of `L∞`. -/
noncomputable def indLp (P : Measure Ω) (y : Lp X ⊤ P) {A : Set Ω} (hA : MeasurableSet A) :
    Lp X ⊤ P :=
  ((Lp.memLp y).indicator hA).toLp (A.indicator y)

theorem indLp_ae (P : Measure Ω) (y : Lp X ⊤ P) {A : Set Ω} (hA : MeasurableSet A) :
    ∀ᵐ ω ∂P, indLp P y hA ω = A.indicator y ω :=
  ((Lp.memLp y).indicator hA).coeFn_toLp


variable (P : Measure Ω)

theorem indLp_apply_lam (lam : Ω → StrongDual ℝ X) (y : Lp X ⊤ P) {A : Set Ω}
    (hA : MeasurableSet A) :
    ∫ ω, lam ω (indLp P y hA ω) ∂P = ∫ ω, A.indicator (fun ω => lam ω (y ω)) ω ∂P := by
  apply integral_congr_ae
  filter_upwards [indLp_ae P y hA] with ω h
  rw [h]
  by_cases hω : ω ∈ A
  · simp [Set.indicator_of_mem hω]
  · simp [Set.indicator_of_notMem hω]

theorem tendsto_ind (f : Ω → ℝ) (hf : Integrable f P) (Fs : ℕ → Set Ω)
    (hFm : ∀ n, MeasurableSet (Fs n)) (hFdec : ∀ n, Fs (n + 1) ⊆ Fs n)
    (hFlim : Tendsto (fun n => P (Fs n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (Fs n).indicator f ω ∂P) atTop (𝓝 0) := by
  have hanti : Antitone Fs := antitone_nat_of_succ_le hFdec
  have hN : P (⋂ n, Fs n) = 0 := by
    have : P (⋂ n, Fs n) ≤ 0 :=
      ge_of_tendsto' hFlim (fun n => measure_mono (Set.iInter_subset _ n))
    exact nonpos_iff_eq_zero.1 this
  have hae : ∀ᵐ ω ∂P, ω ∉ ⋂ n, Fs n := (measure_eq_zero_iff_ae_notMem).1 hN
  have := tendsto_integral_of_dominated_convergence (fun ω => ‖f ω‖)
    (F := fun n => (Fs n).indicator f) (f := fun _ => (0 : ℝ))
    (fun n => (hf.indicator (hFm n)).aestronglyMeasurable) hf.norm
    (fun n => Eventually.of_forall fun ω => by
      by_cases h : ω ∈ Fs n
      · simp [Set.indicator_of_mem h]
      · simp [Set.indicator_of_notMem h])
    (by
      filter_upwards [hae] with ω hω
      simp only [Set.mem_iInter, not_forall] at hω
      obtain ⟨n0, hn0⟩ := hω
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop n0] with n hn
      rw [Set.indicator_of_notMem (fun h => hn0 (hanti hn h))])
  simpa using this

end ChanceStateCtrl.AlmostSure.Eq57Aux

open ChanceStateCtrl.AlmostSure.Eq57Aux

theorem solution {d : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace (closure D)]
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (lamStar lamA lamSing : StrongDual ℝ (Linf D P)) (lam : Ω → StrongDual ℝ C(closure D, ℝ))
    (hlam : lam ∈ Lambda1 C(closure D, ℝ) P)
    (hrep : ∀ y : Linf D P, lamA y = ∫ ω, lam ω (y ω) ∂P)
    (hsing : IsSingular P lamSing) (hsplit : lamStar = lamA + lamSing)
    (hpolar : lamStar ∈ Kpolar D P) :
    ∀ y ∈ Kcone D P, lamSing y ≤ 0 ∧ ∫ ω, lam ω (y ω) ∂P ≤ 0 := by
  intro y hy
  obtain ⟨Fs, hFm, hFdec, hFlim, hFsing⟩ := hsing
  set f : Ω → ℝ := fun ω => lam ω (y ω) with hfdef
  have hf : Integrable f P := integrable_lam P lam hlam y
  have hK : ∀ {A : Set Ω} (hA : MeasurableSet A), indLp P y hA ∈ Kcone D P := by
    intro A hA
    show ∀ᵐ ω ∂P, ∀ x : closure D, (indLp P y hA) ω x ≤ 0
    filter_upwards [indLp_ae P y hA, hy] with ω h1 h2 x
    rw [h1]
    by_cases hω : ω ∈ A
    · simp [Set.indicator_of_mem hω, h2 x]
    · simp [Set.indicator_of_notMem hω]
  have hA_eq : ∀ {A : Set Ω} (hA : MeasurableSet A),
      lamA (indLp P y hA) = ∫ ω, A.indicator f ω ∂P := by
    intro A hA
    rw [hrep, indLp_apply_lam]
  have hlim := tendsto_ind P f hf Fs hFm hFdec hFlim
  constructor
  · have hb : ∀ n, lamSing y ≤ -∫ ω, (Fs n).indicator f ω ∂P := by
      intro n
      have h0 : lamSing (y - indLp P y (hFm n)) = 0 := by
        apply hFsing
        refine ⟨n, ?_⟩
        filter_upwards [indLp_ae P y (hFm n), Lp.coeFn_sub y (indLp P y (hFm n))] with ω h1 h2 hω
        rw [h2, Pi.sub_apply, h1, Set.indicator_of_mem hω, sub_self]
      have h1 : lamStar (indLp P y (hFm n)) ≤ 0 := hpolar _ (hK (hFm n))
      rw [hsplit, ContinuousLinearMap.add_apply, hA_eq] at h1
      rw [map_sub, sub_eq_zero] at h0
      linarith
    have := hlim.neg
    rw [neg_zero] at this
    exact ge_of_tendsto' this hb
  · have hb : ∀ n, ∫ ω, f ω ∂P - ∫ ω, (Fs n).indicator f ω ∂P ≤ 0 := by
      intro n
      have hc := (hFm n).compl
      have h0 : lamSing (indLp P y hc) = 0 := by
        apply hFsing
        refine ⟨n, ?_⟩
        filter_upwards [indLp_ae P y hc] with ω h1 hω
        rw [h1, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hω)]
      have h1 : lamStar (indLp P y hc) ≤ 0 := hpolar _ (hK hc)
      have hI : ∫ ω, (f - (Fs n).indicator f) ω ∂P
          = ∫ ω, f ω ∂P - ∫ ω, (Fs n).indicator f ω ∂P := integral_sub hf (hf.indicator (hFm n))
      rw [hsplit, ContinuousLinearMap.add_apply, hA_eq, h0, add_zero, Set.indicator_compl, hI] at h1
      exact h1
    have := (tendsto_const_nhds (x := ∫ ω, f ω ∂P)).sub hlim
    rw [sub_zero] at this
    exact le_of_tendsto' this hb
