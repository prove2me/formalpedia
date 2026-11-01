-- Prove2me | solution 1 for ConvStochDual.Existence.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T03:31:42.627286+00:00
-- url     : https://prove2.me/submissions/42794a92-30dd-47da-988f-9af799018a83

import Mathlib
import Definitions.Def_ConvStochDual_Existence_Setting

open MeasureTheory Filter Topology

namespace CSDL13

open ConvStochDual.Existence

section Meas

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {K : ℕ}

/-- Measurability of `ω ↦ h(a ω, ω)` for a normal integrand. -/
theorem meas_comp1 (h : Ω → (Fin K → ℝ) → EReal)
    (hh : IsNormalIntegrand1 h) (a : Ω → Fin K → ℝ) (ha : Measurable a) :
    Measurable (fun ω => h ω (a ω)) := by
  obtain ⟨_, hlsc, _, hmeas⟩ := hh
  set d : ℕ → (Fin K → ℝ) := TopologicalSpace.denseSeq _ with hd
  have hdense : DenseRange d := TopologicalSpace.denseRange_denseSeq _
  have hreal : ∀ α : ℝ, MeasurableSet {ω | h ω (a ω) ≤ (α : EReal)} := by
    intro α
    have heq : {ω | h ω (a ω) ≤ (α : EReal)} =
        ⋂ k : ℕ, ⋃ j : ℕ, ({ω | dist (a ω) (d j) < 1 / ((k : ℝ) + 1)} ∩
          {ω | ∃ q ∈ Metric.ball (d j, α) (2 / ((k : ℝ) + 1)),
            h ω q.1 ≤ (q.2 : EReal)}) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro hle k
        have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        obtain ⟨j, hj⟩ := (Metric.denseRange_iff.1 hdense) (a ω) _ hk
        refine ⟨j, hj, (a ω, α), ?_, hle⟩
        rw [Metric.mem_ball]
        have h1 : dist ((a ω, α) : (Fin K → ℝ) × ℝ) (d j, α) ≤ dist (a ω) (d j) := by
          simp only [Prod.dist_eq, dist_self]
          exact max_le le_rfl dist_nonneg
        have h2 : 1 / ((k : ℝ) + 1) ≤ 2 / ((k : ℝ) + 1) := by
          apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
        linarith
      · intro hk
        have hcl : IsClosed {q : (Fin K → ℝ) × ℝ | h ω q.1 ≤ (q.2 : EReal)} := by
          have := (hlsc ω).isClosed_epigraph
          have hc : Continuous (fun q : (Fin K → ℝ) × ℝ => (q.1, ((q.2 : ℝ) : EReal))) :=
            Continuous.prodMk continuous_fst (continuous_coe_real_ereal.comp continuous_snd)
          exact this.preimage hc
        have hmem : ((a ω, α) : (Fin K → ℝ) × ℝ) ∈
            {q : (Fin K → ℝ) × ℝ | h ω q.1 ≤ (q.2 : EReal)} := by
          rw [← hcl.closure_eq, Metric.mem_closure_iff]
          intro ε hε
          obtain ⟨k, hkk⟩ := exists_nat_gt (3 / ε)
          obtain ⟨j, hj, q, hq, hqE⟩ := hk k
          refine ⟨q, hqE, ?_⟩
          rw [Metric.mem_ball] at hq
          have h1 : dist ((a ω, α) : (Fin K → ℝ) × ℝ) (d j, α) ≤ dist (a ω) (d j) := by
            simp only [Prod.dist_eq, dist_self]
            exact max_le le_rfl dist_nonneg
          have h3 := dist_triangle ((a ω, α) : (Fin K → ℝ) × ℝ) (d j, α) q
          rw [dist_comm (d j, α) q] at h3
          have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
          have : 3 / ((k : ℝ) + 1) < ε := by
            rw [div_lt_iff₀ hk1]
            rw [div_lt_iff₀ hε] at hkk
            nlinarith
          have e3 : 1 / ((k : ℝ) + 1) + 2 / ((k : ℝ) + 1) = 3 / ((k : ℝ) + 1) := by ring
          linarith
        exact hmem
    rw [heq]
    refine MeasurableSet.iInter fun k => MeasurableSet.iUnion fun j => ?_
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_lt (ha.dist measurable_const) measurable_const
    · exact hmeas _ Metric.isOpen_ball
  refine measurable_of_Iic fun c => ?_
  induction c using EReal.rec with
  | bot =>
    have : (fun ω => h ω (a ω)) ⁻¹' Set.Iic ⊥ =
        ⋂ k : ℕ, {ω | h ω (a ω) ≤ ((-(k : ℝ) : ℝ) : EReal)} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_Iic, le_bot_iff, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro hb k; rw [hb]; exact bot_le
      · intro hb
        by_contra hne
        induction hω : h ω (a ω) using EReal.rec with
        | bot => exact hne hω
        | top => have := hb 0; rw [hω] at this; simp at this
        | coe r =>
          obtain ⟨k, hk⟩ := exists_nat_gt (-r)
          have := hb k; rw [hω, EReal.coe_le_coe_iff] at this; linarith
    rw [this]; exact MeasurableSet.iInter fun k => hreal _
  | top => simp
  | coe r => exact hreal r

end Meas

section Expect

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

theorem toENNReal_coe_real (r : ℝ) : ((r : EReal)).toENNReal = ENNReal.ofReal r := by
  rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top r), EReal.toReal_coe]

theorem integrable_of_lintegral (F : Ω → ℝ) (hF : AEStronglyMeasurable F P)
    (h1 : ∫⁻ ω, ENNReal.ofReal (F ω) ∂P ≠ ⊤) (h2 : ∫⁻ ω, ENNReal.ofReal (-F ω) ∂P ≠ ⊤) :
    Integrable F P := by
  refine ⟨hF, ?_⟩
  unfold HasFiniteIntegral
  have e : (fun ω => ‖F ω‖ₑ) = fun ω => ENNReal.ofReal (F ω) + ENNReal.ofReal (-F ω) := by
    funext ω
    rw [Real.enorm_eq_ofReal_abs]
    rcases le_total (F ω) 0 with h | h
    · rw [abs_of_nonpos h, ENNReal.ofReal_eq_zero.2 h, zero_add]
    · rw [abs_of_nonneg h, ENNReal.ofReal_eq_zero.2 (by linarith : -F ω ≤ 0), add_zero]
  rw [e, lintegral_add_left' hF.aemeasurable.ennreal_ofReal]
  exact ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 h1, lt_top_iff_ne_top.2 h2⟩

theorem expect_eq_of_ae (h : Ω → EReal) (H : Ω → ℝ) (hH : Integrable H P)
    (hae : ∀ᵐ ω ∂P, h ω = (H ω : EReal)) :
    DupacovaWets.Consistency.expect P h = ((∫ ω, H ω ∂P : ℝ) : EReal) := by
  unfold DupacovaWets.Consistency.expect
  have l1 : ∫⁻ ω, (h ω).toENNReal ∂P = ∫⁻ ω, ENNReal.ofReal (H ω) ∂P := by
    refine lintegral_congr_ae (hae.mono fun ω hω => ?_)
    show (h ω).toENNReal = _
    rw [hω, toENNReal_coe_real]
  have l2 : ∫⁻ ω, (-h ω).toENNReal ∂P = ∫⁻ ω, ENNReal.ofReal (-H ω) ∂P := by
    refine lintegral_congr_ae (hae.mono fun ω hω => ?_)
    show (-h ω).toENNReal = _
    rw [hω, ← EReal.coe_neg, toENNReal_coe_real]
  have f1 : ∫⁻ ω, ENNReal.ofReal (H ω) ∂P ≠ ⊤ := hH.lintegral_lt_top.ne
  have f2 : ∫⁻ ω, ENNReal.ofReal (-H ω) ∂P ≠ ⊤ := hH.neg.lintegral_lt_top.ne
  rw [l1, l2, if_neg f1, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hH,
    ← EReal.coe_ennreal_toReal f1, ← EReal.coe_ennreal_toReal f2, EReal.coe_sub]

theorem expect_top_of (h : Ω → EReal) (hh : ∫⁻ ω, (h ω).toENNReal ∂P = ⊤) :
    DupacovaWets.Consistency.expect P h = ⊤ := by
  unfold DupacovaWets.Consistency.expect; rw [if_pos hh]

theorem lint_pos_ne_top (h : Ω → EReal) (hh : DupacovaWets.Consistency.expect P h ≠ ⊤) :
    ∫⁻ ω, (h ω).toENNReal ∂P ≠ ⊤ := fun h' => hh (expect_top_of h h')

theorem lint_neg_ne_top (h : Ω → EReal) (hh : DupacovaWets.Consistency.expect P h ≠ ⊥)
    (hh' : DupacovaWets.Consistency.expect P h ≠ ⊤) :
    ∫⁻ ω, (-h ω).toENNReal ∂P ≠ ⊤ := by
  intro h'
  apply hh
  have h1 := lint_pos_ne_top h hh'
  unfold DupacovaWets.Consistency.expect
  rw [if_neg h1, h', EReal.coe_ennreal_top, EReal.sub_top]

theorem ae_ne_top (h : Ω → EReal) (hm : Measurable h) (hh : ∫⁻ ω, (h ω).toENNReal ∂P ≠ ⊤) :
    ∀ᵐ ω ∂P, h ω ≠ ⊤ := by
  have := ae_lt_top (hm.ereal_toENNReal) hh
  filter_upwards [this] with ω hω
  intro htop
  rw [htop] at hω
  simp at hω

theorem ae_ne_bot (h : Ω → EReal) (hm : Measurable h) (hh : ∫⁻ ω, (-h ω).toENNReal ∂P ≠ ⊤) :
    ∀ᵐ ω ∂P, h ω ≠ ⊥ := by
  have := ae_lt_top (hm.neg.ereal_toENNReal) hh
  filter_upwards [this] with ω hω
  intro hbot
  simp only [Pi.neg_apply] at hω
  rw [hbot] at hω
  simp at hω

end Expect

section L13

theorem rep {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (g : Ω → EReal) (h1 : ∀ᵐ ω ∂P, g ω ≠ ⊤) (h2 : ∀ᵐ ω ∂P, g ω ≠ ⊥) :
    (∀ᵐ ω ∂P, g ω = (((g ω).toReal : ℝ) : EReal)) ∧
    ∫⁻ ω, ENNReal.ofReal ((g ω).toReal) ∂P = ∫⁻ ω, (g ω).toENNReal ∂P ∧
    ∫⁻ ω, ENNReal.ofReal (-(g ω).toReal) ∂P = ∫⁻ ω, (-g ω).toENNReal ∂P := by
  have e : ∀ᵐ ω ∂P, g ω = (((g ω).toReal : ℝ) : EReal) := by
    filter_upwards [h1, h2] with ω hω1 hω2
    exact (EReal.coe_toReal hω1 hω2).symm
  refine ⟨e, ?_, ?_⟩
  · refine lintegral_congr_ae (e.mono fun ω hω => ?_)
    show ENNReal.ofReal ((g ω).toReal) = (g ω).toENNReal
    conv_rhs => rw [hω]
    rw [toENNReal_coe_real]
  · refine lintegral_congr_ae (e.mono fun ω hω => ?_)
    show ENNReal.ofReal (-(g ω).toReal) = (-g ω).toENNReal
    conv_rhs => rw [hω]
    rw [← EReal.coe_neg, toENNReal_coe_real]

theorem setInt_tendsto_zero {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    (B : ℕ → Set Ω) (hB : ∀ j, MeasurableSet (B j)) (hanti : Antitone B)
    (hP : Tendsto (fun j => P (B j)) atTop (𝓝 0)) (f : Ω → ℝ) (hf : Integrable f P) :
    Tendsto (fun j => ∫ ω in B j, f ω ∂P) atTop (𝓝 0) := by
  have h := tendsto_setIntegral_of_antitone (μ := P) (f := f) hB hanti ⟨0, hf.integrableOn⟩
  have h0 : P (⋂ n, B n) = 0 := by
    refine le_antisymm ?_ (by simp)
    exact ge_of_tendsto' hP (fun j => measure_mono (Set.iInter_subset B j))
  rwa [setIntegral_measure_zero _ h0] at h

variable {Ω U : Type*} [MeasurableSpace Ω]
  [AddCommGroup U] [Module ℝ U] [UniformSpace U]
  [IsUniformAddGroup U] [ContinuousSMul ℝ U]
  {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
  {ι : U →ₗ[ℝ] RV Ω P k}
  {Y₀ : Submodule ℝ (RV Ω P k)}

theorem dot_ite_left (c : Prop) [Decidable c] (z w : Fin k → ℝ) :
    dot (if c then 0 else z) w = if c then 0 else dot z w := by
  split_ifs <;> simp [dot]

theorem main13 (h : Ω → (Fin k → ℝ) → EReal)
    (hS : IntegralStanding h ι Y₀) (hProper : EhProper h ι)
    (ubar : U) (y : U →L[ℝ] ℝ) (yc : Y₀) (ys : U →L[ℝ] ℝ)
    (hdecomp : IsDecomp P ι Y₀ y yc ys) (ε : ℝ) (hε : 0 ≤ ε)
    (hsub : ∀ u : U, Eh h (ι ubar) +
      ((y (u - ubar) : ℝ) : EReal) - (ε : EReal) ≤ Eh h (ι u)) :
    (∀ u : U, Eh h (ι ubar) +
      ((pair P (ι (u - ubar)) (yc : RV Ω P k) : ℝ) : EReal) -
        (ε : EReal) ≤ Eh h (ι u)) ∧
    (∀ u ∈ domEh h ι, 0 ≥ ys (u - ubar) - ε) := by
  classical
  obtain ⟨hsing, hy⟩ := hdecomp
  have hm : ∀ u : U, Measurable (fun ω => h ω (ι u ω)) := fun u =>
    meas_comp1 h hS.normal _ (ι u).stronglyMeasurable.measurable
  have Efin : ∀ u ∈ domEh h ι, ∃ H : Ω → ℝ, Integrable H P ∧
      (∀ᵐ ω ∂P, h ω (ι u ω) = (H ω : EReal)) ∧
      Eh h (ι u) = ((∫ ω, H ω ∂P : ℝ) : EReal) := by
    intro u hu
    have htop : Eh h (ι u) ≠ ⊤ := ne_of_lt hu
    have hbot : Eh h (ι u) ≠ ⊥ := hProper.1 u
    have l1 := lint_pos_ne_top (P := P) (fun ω => h ω (ι u ω)) htop
    have l2 := lint_neg_ne_top (P := P) (fun ω => h ω (ι u ω)) hbot htop
    have a1 := ae_ne_top _ (hm u) l1
    have a2 := ae_ne_bot _ (hm u) l2
    obtain ⟨e, r1, r2⟩ := rep (P := P) _ a1 a2
    have hint : Integrable (fun ω => (h ω (ι u ω)).toReal) P :=
      integrable_of_lintegral _ (hm u).ereal_toReal.aestronglyMeasurable
        (by rw [r1]; exact l1) (by rw [r2]; exact l2)
    exact ⟨_, hint, e, expect_eq_of_ae _ _ hint e⟩
  have hub : ubar ∈ domEh h ι := by
    obtain ⟨u0, hu0⟩ := hProper.2
    show Eh h (ι ubar) < ⊤
    rw [lt_top_iff_ne_top]
    intro htop
    have := hsub u0
    rw [htop, EReal.top_add_coe, EReal.top_sub_coe, top_le_iff] at this
    exact (ne_of_lt hu0) this
  obtain ⟨Hb, hHb, eHb, hEb⟩ := Efin ubar hub
  have constr : ∀ v : U, ∃ B : ℕ → Set Ω, (∀ j, MeasurableSet (B j)) ∧ Antitone B ∧
      Tendsto (fun j => P (B j)) atTop (𝓝 0) ∧ ∃ w : ℕ → U,
      (∀ j, ι (w j) =ᵐ[P] fun ω => if ω ∈ B j then 0 else ι v ω) ∧ ∀ j, ys (w j) = 0 := by
    intro v
    obtain ⟨B, hBm, hBa, hBt, hBz⟩ := hsing v
    refine ⟨B, hBm, hBa, hBt, ?_⟩
    have : ∀ j, ∃ w : U, ι w =ᵐ[P] fun ω => if ω ∈ B j then 0 else ι v ω := by
      intro j
      set g : Ω → Fin k → ℝ := fun ω => if ω ∈ B j then 0 else ι v ω with hg
      have hgm : AEStronglyMeasurable g P :=
        (StronglyMeasurable.piecewise (hBm j) stronglyMeasurable_const
          (ι v).stronglyMeasurable).aestronglyMeasurable
      obtain ⟨z, hz⟩ := hS.solidU v (AEEqFun.mk g hgm) (by
        filter_upwards [AEEqFun.coeFn_mk g hgm] with ω hω i
        rw [hω]
        simp only [hg]
        split_ifs
        · simp
        · exact le_rfl)
      exact ⟨z, by rw [hz]; exact AEEqFun.coeFn_mk g hgm⟩
    choose w hw using this
    exact ⟨w, hw, fun j => hBz j (w j) (hw j)⟩
  have hsubv : ∀ u : U, ι (u - ubar) =ᵐ[P] fun ω => ι u ω - ι ubar ω := by
    intro u; rw [map_sub]; exact AEEqFun.coeFn_sub _ _
  have haddv : ∀ u w : U, ι (u + w) =ᵐ[P] fun ω => ι u ω + ι w ω := by
    intro u w; rw [map_add]; exact AEEqFun.coeFn_add _ _
  refine ⟨?_, ?_⟩
  · intro u
    by_cases hu : u ∈ domEh h ι
    swap
    · have : Eh h (ι u) = ⊤ := not_lt_top_iff.1 hu
      rw [this]; exact le_top
    obtain ⟨H, hH, eH, hE⟩ := Efin u hu
    obtain ⟨B, hBm, hBa, hBt, w, hw, hws⟩ := constr (u - ubar)
    set g : Ω → ℝ := fun ω => dot (ι (u - ubar) ω) ((yc : RV Ω P k) ω) with hgdef
    have hg : Integrable g P := hS.pair_integrable (u - ubar) yc
    have hj : ∀ j, (∫ ω, Hb ω ∂P) + ((∫ ω, g ω ∂P) - ∫ ω in B j, g ω ∂P) - ε ≤
        (∫ ω, H ω ∂P) + ∫ ω in B j, (Hb ω - H ω) ∂P := by
      intro j
      have h1 := hsub (ubar + w j)
      rw [add_sub_cancel_left, hy (w j), hws j, add_zero] at h1
      have hval : Eh h (ι (ubar + w j)) =
          ((∫ ω, (H ω + (B j).indicator (fun ω => Hb ω - H ω) ω) ∂P : ℝ) : EReal) := by
        refine expect_eq_of_ae _ _ (hH.add ((hHb.sub hH).indicator (hBm j))) ?_
        filter_upwards [haddv ubar (w j), hw j, hsubv u, eH, eHb] with ω h1 h2 h3 h4 h5
        show h ω (ι (ubar + w j) ω) = _
        rw [h1, h2]
        by_cases hωB : ω ∈ B j
        · simp only [hωB, if_true, add_zero, Set.indicator_of_mem hωB]
          rw [h5]; congr 1; ring
        · simp only [hωB, if_false, Set.indicator_of_notMem hωB, add_zero]
          rw [h3, add_sub_cancel, h4]
      have hpair : pair P (ι (w j)) (yc : RV Ω P k) =
          (∫ ω, g ω ∂P) - ∫ ω in B j, g ω ∂P := by
        unfold pair
        rw [← integral_indicator (hBm j), ← integral_sub hg (hg.indicator (hBm j))]
        refine integral_congr_ae ?_
        filter_upwards [hw j] with ω hω
        rw [hω, dot_ite_left]
        by_cases hωB : ω ∈ B j
        · simp [hωB, hgdef]
        · simp [hωB, hgdef]
      rw [hEb, hval, hpair, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff] at h1
      rw [integral_add (f := H) (g := fun ω => (B j).indicator (fun ω => Hb ω - H ω) ω) hH
        (by exact (hHb.sub hH).indicator (hBm j)), integral_indicator (hBm j)] at h1
      exact h1
    have t1 : Tendsto (fun j => (∫ ω, Hb ω ∂P) + ((∫ ω, g ω ∂P) - ∫ ω in B j, g ω ∂P) - ε)
        atTop (𝓝 ((∫ ω, Hb ω ∂P) + ((∫ ω, g ω ∂P) - 0) - ε)) :=
      ((tendsto_const_nhds.sub (setInt_tendsto_zero B hBm hBa hBt g hg)).const_add _).sub_const _
    have t2 : Tendsto (fun j => (∫ ω, H ω ∂P) + ∫ ω in B j, (Hb ω - H ω) ∂P)
        atTop (𝓝 ((∫ ω, H ω ∂P) + 0)) :=
      (setInt_tendsto_zero B hBm hBa hBt _ (hHb.sub hH)).const_add _
    have hlim := le_of_tendsto_of_tendsto t1 t2 (Eventually.of_forall hj)
    rw [hEb, hE]
    have hp : pair P (ι (u - ubar)) (yc : RV Ω P k) = ∫ ω, g ω ∂P := rfl
    rw [hp, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    linarith
  · intro u hu
    obtain ⟨H, hH, eH, hE⟩ := Efin u hu
    obtain ⟨B, hBm, hBa, hBt, w, hw, hws⟩ := constr (u - ubar)
    set g : Ω → ℝ := fun ω => dot (ι (u - ubar) ω) ((yc : RV Ω P k) ω) with hgdef
    have hg : Integrable g P := hS.pair_integrable (u - ubar) yc
    set w' : ℕ → U := fun j => (u - ubar) - w j with hw'
    have hj : ∀ j, (∫ ω, Hb ω ∂P) + ((∫ ω in B j, g ω ∂P) + ys (u - ubar)) - ε ≤
        (∫ ω, Hb ω ∂P) + ∫ ω in B j, (H ω - Hb ω) ∂P := by
      intro j
      have h1 := hsub (ubar + w' j)
      rw [add_sub_cancel_left, hy (w' j)] at h1
      have hys : ys (w' j) = ys (u - ubar) := by
        simp only [hw', map_sub, hws j, sub_zero]
      have hw'ae : ι (w' j) =ᵐ[P] fun ω => ι (u - ubar) ω - ι (w j) ω := by
        simp only [hw']; rw [map_sub]; exact AEEqFun.coeFn_sub _ _
      have hval : Eh h (ι (ubar + w' j)) =
          ((∫ ω, (Hb ω + (B j).indicator (fun ω => H ω - Hb ω) ω) ∂P : ℝ) : EReal) := by
        refine expect_eq_of_ae _ _ (hHb.add ((hH.sub hHb).indicator (hBm j))) ?_
        filter_upwards [haddv ubar (w' j), hw'ae, hw j, hsubv u, eH, eHb] with
          ω h1 h2 h3 h4 h5 h6
        show h ω (ι (ubar + w' j) ω) = _
        rw [h1, h2, h3]
        by_cases hωB : ω ∈ B j
        · simp only [hωB, if_true, sub_zero, Set.indicator_of_mem hωB]
          rw [h4, add_sub_cancel, h5]; congr 1; ring
        · simp only [hωB, if_false, Set.indicator_of_notMem hωB, add_zero, sub_self]
          rw [h6]
      have hpair : pair P (ι (w' j)) (yc : RV Ω P k) = ∫ ω in B j, g ω ∂P := by
        unfold pair
        rw [← integral_indicator (hBm j)]
        refine integral_congr_ae ?_
        filter_upwards [hw'ae, hw j] with ω h1 h2
        rw [h1, h2]
        by_cases hωB : ω ∈ B j
        · simp [hωB, hgdef]
        · simp [hωB, hgdef, dot]
      rw [hEb, hval, hpair, hys, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_le_coe_iff] at h1
      rw [integral_add (f := Hb) (g := fun ω => (B j).indicator (fun ω => H ω - Hb ω) ω) hHb
        (by exact (hH.sub hHb).indicator (hBm j)), integral_indicator (hBm j)] at h1
      exact h1
    have t1 : Tendsto (fun j => (∫ ω, Hb ω ∂P) + ((∫ ω in B j, g ω ∂P) + ys (u - ubar)) - ε)
        atTop (𝓝 ((∫ ω, Hb ω ∂P) + (0 + ys (u - ubar)) - ε)) :=
      (((setInt_tendsto_zero B hBm hBa hBt g hg).add_const _).const_add _).sub_const _
    have t2 : Tendsto (fun j => (∫ ω, Hb ω ∂P) + ∫ ω in B j, (H ω - Hb ω) ∂P)
        atTop (𝓝 ((∫ ω, Hb ω ∂P) + 0)) :=
      (setInt_tendsto_zero B hBm hBa hBt _ (hH.sub hHb)).const_add _
    have hlim := le_of_tendsto_of_tendsto t1 t2 (Eventually.of_forall hj)
    linarith

end L13

end CSDL13

open ConvStochDual.Existence in
theorem solution {Ω U : Type*} [MeasurableSpace Ω]
  [AddCommGroup U] [Module ℝ U] [UniformSpace U]
  [IsUniformAddGroup U] [ContinuousSMul ℝ U]
  {P : Measure Ω} [IsProbabilityMeasure P] {k : ℕ}
  {ι : U →ₗ[ℝ] RV Ω P k}
  {Y₀ : Submodule ℝ (RV Ω P k)}
    (h : Ω → (Fin k → ℝ) → EReal)
    (hS : IntegralStanding h ι Y₀) (hProper : EhProper h ι)
    (ubar : U) (y : U →L[ℝ] ℝ) (yc : Y₀) (ys : U →L[ℝ] ℝ)
    (hdecomp : IsDecomp P ι Y₀ y yc ys) (ε : ℝ) (hε : 0 ≤ ε)
    (hsub : ∀ u : U, Eh h (ι ubar) +
      ((y (u - ubar) : ℝ) : EReal) - (ε : EReal) ≤ Eh h (ι u)) :
    (∀ u : U, Eh h (ι ubar) +
      ((pair P (ι (u - ubar)) (yc : RV Ω P k) : ℝ) : EReal) -
        (ε : EReal) ≤ Eh h (ι u)) ∧
    (∀ u ∈ domEh h ι, 0 ≥ ys (u - ubar) - ε) :=
  CSDL13.main13 h hS hProper ubar y yc ys hdecomp ε hε hsub
