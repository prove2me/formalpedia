-- Prove2me | solution 1 for ChanceStateCtrl.AlmostSure.theorem_3_9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T21:41:40.985158+00:00
-- url     : https://prove2.me/submissions/75e3d590-927c-4afb-9ecd-6b17344b1106
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ChanceStateCtrl_AlmostSure_Setting
import Theorems.Thm_ChanceStateCtrl_AlmostSure_theorem_3_9_existence

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


/-- A functional that is both representable by `xs, xs' ∈ Λ₁` (as a difference) and vanishes on
everything supported off `Hₙ` with `P(Hₙ) → 0` is zero. -/
theorem zero_of_ac_sing (w : StrongDual ℝ (Lp X ⊤ P)) (xs xs' : Ω → StrongDual ℝ X)
    (hxs : xs ∈ Lambda1 X P) (hxs' : xs' ∈ Lambda1 X P)
    (hrep : ∀ x : Lp X ⊤ P, w x = ∫ ω, xs ω (x ω) ∂P - ∫ ω, xs' ω (x ω) ∂P)
    (Hs : ℕ → Set Ω) (hHm : ∀ n, MeasurableSet (Hs n)) (hHdec : ∀ n, Hs (n + 1) ⊆ Hs n)
    (hHlim : Filter.Tendsto (fun n => P (Hs n)) Filter.atTop (𝓝 0))
    (hvan : ∀ x : Lp X ⊤ P, (∃ n, ∀ᵐ ω ∂P, ω ∈ Hs n → x ω = 0) → w x = 0) : w = 0 := by
  ext x
  rw [ContinuousLinearMap.zero_apply]
  set f : Ω → ℝ := fun ω => xs ω (x ω)
  set f' : Ω → ℝ := fun ω => xs' ω (x ω)
  have hf := integrable_lam P xs hxs x
  have hf' := integrable_lam P xs' hxs' x
  have hb : ∀ n, w x = ∫ ω, (Hs n).indicator f ω ∂P - ∫ ω, (Hs n).indicator f' ω ∂P := by
    intro n
    have h0 : w (x - indLp P x (hHm n)) = 0 := by
      apply hvan
      refine ⟨n, ?_⟩
      filter_upwards [indLp_ae P x (hHm n), Lp.coeFn_sub x (indLp P x (hHm n))] with ω h1 h2 hω
      rw [h2, Pi.sub_apply, h1, Set.indicator_of_mem hω, sub_self]
    rw [map_sub, sub_eq_zero] at h0
    rw [h0, hrep, indLp_apply_lam, indLp_apply_lam]
  have hlim := (tendsto_ind P f hf Hs hHm hHdec hHlim).sub (tendsto_ind P f' hf' Hs hHm hHdec hHlim)
  rw [sub_zero] at hlim
  have : Filter.Tendsto (fun _ : ℕ => w x) Filter.atTop (𝓝 0) := by
    simpa [← hb] using hlim
  exact tendsto_nhds_unique tendsto_const_nhds this

end ChanceStateCtrl.AlmostSure.Eq57Aux

open ChanceStateCtrl.AlmostSure.Eq57Aux

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [TopologicalSpace.SeparableSpace X] (v : StrongDual ℝ (Lp X ⊤ P)) :
    (∃ va vs : StrongDual ℝ (Lp X ⊤ P), IsAbsCont P va ∧ IsSingular P vs ∧ v = va + vs ∧
        ‖v‖ = ‖va‖ + ‖vs‖) ∧
      ∀ va vs va' vs' : StrongDual ℝ (Lp X ⊤ P), IsAbsCont P va → IsSingular P vs →
        IsAbsCont P va' → IsSingular P vs' → v = va + vs → v = va' + vs' →
        va = va' ∧ vs = vs' := by
  refine ⟨theorem_3_9_existence P v, ?_⟩
  intro va vs va' vs' ⟨xs, hxs, hrep⟩ ⟨Fs, hFm, hFdec, hFlim, hFv⟩ ⟨xs', hxs', hrep'⟩
    ⟨Gs, hGm, hGdec, hGlim, hGv⟩ h1 h2
  have hw : va - va' = vs' - vs := by
    have : va + vs = va' + vs' := h1.symm.trans h2
    rw [sub_eq_sub_iff_add_eq_add, this, add_comm]
  have hz : va - va' = 0 := by
    apply zero_of_ac_sing P (va - va') xs xs' hxs hxs'
      (fun x => by rw [ContinuousLinearMap.sub_apply, hrep, hrep'])
      (fun n => Fs n ∪ Gs n) (fun n => (hFm n).union (hGm n))
      (fun n => Set.union_subset_union (hFdec n) (hGdec n))
    · have hsum := hFlim.add hGlim
      rw [add_zero] at hsum
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
        (fun n => bot_le) (fun n => measure_union_le _ _)
    · rintro x ⟨n, hn⟩
      rw [hw, ContinuousLinearMap.sub_apply]
      have a1 : vs' x = 0 := hGv x ⟨n, by
        filter_upwards [hn] with ω h hω; exact h (Or.inr hω)⟩
      have a2 : vs x = 0 := hFv x ⟨n, by
        filter_upwards [hn] with ω h hω; exact h (Or.inl hω)⟩
      rw [a1, a2, sub_zero]
  have e1 : va = va' := sub_eq_zero.1 hz
  refine ⟨e1, ?_⟩
  rw [e1] at h1
  exact add_left_cancel (h1.symm.trans h2)
