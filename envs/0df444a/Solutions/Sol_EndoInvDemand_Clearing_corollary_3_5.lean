-- Prove2me | solution 1 for EndoInvDemand.Clearing.corollary_3_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T22:36:52.709712+00:00
-- url     : https://prove2.me/submissions/d0487fa2-4f2e-4273-a14f-818a5f543e1e

import Mathlib
import Definitions.Def_EndoInvDemand_Clearing_Setting
open MeasureTheory
open scoped ENNReal Topology
set_option linter.unusedSectionVars false

namespace EndoInvDemand.Clearing


lemma eid_bdd_of_memLp_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℝ}
    (hZ : MemLp Z ⊤ P) : ∃ C : ℝ, ∀ᵐ ω ∂P, |Z ω| ≤ C := by
  have h := hZ.2
  rw [eLpNorm_exponent_top, eLpNormEssSup_lt_top_iff_isBoundedUnder] at h
  obtain ⟨C, hC⟩ := h
  refine ⟨C, ?_⟩
  filter_upwards [hC] with ω hω
  have : ‖Z ω‖₊ ≤ C := hω
  rw [← Real.norm_eq_abs]
  exact_mod_cast this

lemma eid_weight_antitone (D : Dom) (R : ℝ → ℝ) (hR : Assumption31 D R) :
    Antitone (weight D R) := by
  intro y y' hyy'
  cases D with
  | real =>
    simp only [weight]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.2
    have := hR.1.monotoneOn (by simp [Dom.set]) (by simp [Dom.set]) hyy'
    linarith
  | pos =>
    simp only [weight]
    by_cases hy : 0 < y
    · have hy' : 0 < y' := lt_of_lt_of_le hy hyy'
      rw [if_pos hy, if_pos hy']
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.2
      have := hR.1.monotoneOn (show y ∈ Dom.set .pos from hy) (show y' ∈ Dom.set .pos from hy') hyy'
      linarith
    · rw [if_neg hy]
      split_ifs with hy'
      · exact le_iSup₂ (f := fun z (_ : z ∈ Set.Ioi (0:ℝ)) => ENNReal.ofReal (Real.exp (-R z))) y' hy'
      · exact le_rfl

lemma eid_weight_measurable (D : Dom) (R : ℝ → ℝ) (hR : Assumption31 D R) :
    Measurable (weight D R) :=
  (eid_weight_antitone D R hR).measurable

lemma eid_weight_pos (D : Dom) (R : ℝ → ℝ) (y : ℝ) : 0 < weight D R y := by
  cases D with
  | real => simp only [weight]; exact ENNReal.ofReal_pos.2 (Real.exp_pos _)
  | pos =>
    simp only [weight]
    split_ifs with hy
    · exact ENNReal.ofReal_pos.2 (Real.exp_pos _)
    · apply lt_of_lt_of_le (ENNReal.ofReal_pos.2 (Real.exp_pos (-R 1)))
      exact le_iSup₂ (f := fun z (_ : z ∈ Set.Ioi (0:ℝ)) => ENNReal.ofReal (Real.exp (-R z))) 1
        (by norm_num)

lemma eid_weight_lt_top (D : Dom) (R : ℝ → ℝ) (y : ℝ) (hy : y ∈ D.set) :
    weight D R y < ⊤ := by
  cases D with
  | real => simp [weight]
  | pos =>
    have : (0:ℝ) < y := hy
    simp [weight, this]

lemma eid_weight_toReal_of_mem (D : Dom) (R : ℝ → ℝ) (y : ℝ) (hy : y ∈ D.set) :
    (weight D R y).toReal = Real.exp (-R y) := by
  cases D with
  | real => simp [weight, (Real.exp_pos _).le]
  | pos =>
    have : (0:ℝ) < y := hy
    simp [weight, this, (Real.exp_pos _).le]


section bdd
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma eid_ae_essInf_le {f : Ω → ℝ} {C : ℝ} (hC : ∀ᵐ ω ∂P, |f ω| ≤ C) :
    ∀ᵐ ω ∂P, essInf f P ≤ f ω := by
  apply ae_essInf_le
  exact ⟨-C, Filter.eventually_map.2 (by filter_upwards [hC] with ω hω; exact (abs_le.1 hω).1)⟩

lemma eid_ae_le_essSup {f : Ω → ℝ} {C : ℝ} (hC : ∀ᵐ ω ∂P, |f ω| ≤ C) :
    ∀ᵐ ω ∂P, f ω ≤ essSup f P := by
  apply ae_le_essSup
  exact ⟨C, Filter.eventually_map.2 (by filter_upwards [hC] with ω hω; exact (abs_le.1 hω).2)⟩

lemma eid_le_essInf {f : Ω → ℝ} {C : ℝ} (hC : ∀ᵐ ω ∂P, |f ω| ≤ C) {c : ℝ}
    (hc : ∀ᵐ ω ∂P, c ≤ f ω) : c ≤ essInf f P := by
  refine le_essInf_of_ae_le c hc ?_
  exact Filter.isCoboundedUnder_ge_of_eventually_le (ae P) (x := C) (by
  filter_upwards [hC] with ω hω; exact (abs_le.1 hω).2)

lemma eid_essSup_le {f : Ω → ℝ} {C : ℝ} (hC : ∀ᵐ ω ∂P, |f ω| ≤ C) {c : ℝ}
    (hc : ∀ᵐ ω ∂P, f ω ≤ c) : essSup f P ≤ c := by
  refine essSup_le_of_ae_le c hc ?_
  exact Filter.isCoboundedUnder_le_of_eventually_le (ae P) (x := -C) (by
  filter_upwards [hC] with ω hω; exact (abs_le.1 hω).1)

lemma eid_sum_bdd {X Z : Ω → ℝ} {Cx Cz : ℝ} (hx : ∀ᵐ ω ∂P, |X ω| ≤ Cx)
    (hz : ∀ᵐ ω ∂P, |Z ω| ≤ Cz) : ∀ᵐ ω ∂P, |X ω + Z ω| ≤ Cx + Cz := by
  filter_upwards [hx, hz] with ω h1 h2
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

end bdd

section model
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Dom} {R : ℝ → ℝ} {X Z : Ω → ℝ}

lemma eid_w_aemeas (hR : Assumption31 D R) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P) (v : ℝ) :
    AEMeasurable (fun ω => weight D R (X ω + Z ω - v)) P :=
  (eid_weight_measurable D R hR).comp_aemeasurable
    ((hX.1.1.aemeasurable.add hZ.1.aemeasurable).sub_const v)

lemma eid_wr_aesm (hR : Assumption31 D R) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P) (v : ℝ) :
    AEStronglyMeasurable (fun ω => (weight D R (X ω + Z ω - v)).toReal) P :=
  (eid_w_aemeas hR hX hZ v).ennreal_toReal.aestronglyMeasurable

lemma eid_denom_lt_top_of_ae_ge (hR : Assumption31 D R) {v c : ℝ}
    (hc : ∀ᵐ ω ∂P, c ≤ X ω + Z ω - v) (hw : weight D R c < ⊤) : denom P D R X Z v < ⊤ := by
  unfold denom
  calc ∫⁻ ω, weight D R (X ω + Z ω - v) ∂P ≤ ∫⁻ _, weight D R c ∂P := by
        apply lintegral_mono_ae
        filter_upwards [hc] with ω hω
        exact eid_weight_antitone D R hR hω
    _ = weight D R c := by simp
    _ < ⊤ := hw

lemma eid_denom_pos (hR : Assumption31 D R) {v M : ℝ}
    (hM : ∀ᵐ ω ∂P, X ω + Z ω - v ≤ M) : 0 < denom P D R X Z v := by
  unfold denom
  calc (0 : ℝ≥0∞) < weight D R M := eid_weight_pos D R M
    _ = ∫⁻ _, weight D R M ∂P := by simp
    _ ≤ ∫⁻ ω, weight D R (X ω + Z ω - v) ∂P := by
        apply lintegral_mono_ae
        filter_upwards [hM] with ω hω
        exact eid_weight_antitone D R hR hω

lemma eid_XZ_bdd (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P) :
    ∃ C : ℝ, ∀ᵐ ω ∂P, |X ω + Z ω| ≤ C := by
  obtain ⟨Cx, hx⟩ := eid_bdd_of_memLp_top hX.1
  obtain ⟨Cz, hz⟩ := eid_bdd_of_memLp_top hZ
  exact ⟨_, eid_sum_bdd hx hz⟩

lemma eid_denom_pos' (hR : Assumption31 D R) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P)
    (v : ℝ) : 0 < denom P D R X Z v := by
  obtain ⟨C, hC⟩ := eid_XZ_bdd hX hZ
  exact eid_denom_pos hR (M := C - v) (by filter_upwards [hC] with ω hω; linarith [(abs_le.1 hω).2])

lemma eid_ae_e_le (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P) :
    ∀ᵐ ω ∂P, essInf (fun ω => X ω + Z ω) P ≤ X ω + Z ω := by
  obtain ⟨C, hC⟩ := eid_XZ_bdd hX hZ
  exact eid_ae_essInf_le hC

lemma eid_le_e_of_mem_domH_pos {R : ℝ → ℝ} (hX : Assumption21 P .pos X) (hZ : MemLp Z ⊤ P)
    {v : ℝ} (hv : v ∈ domH P .pos R X Z) : v ≤ essInf (fun ω => X ω + Z ω) P := by
  obtain ⟨C, hC⟩ := eid_XZ_bdd hX hZ
  exact eid_le_essInf hC hv.1

lemma eid_mem_domH_of_lt_pos {R : ℝ → ℝ} (hR : Assumption31 .pos R) (hX : Assumption21 P .pos X)
    (hZ : MemLp Z ⊤ P) {v : ℝ} (hv : v < essInf (fun ω => X ω + Z ω) P) :
    v ∈ domH P .pos R X Z := by
  have he := eid_ae_e_le hX hZ
  refine ⟨?_, ?_⟩
  · filter_upwards [he] with ω hω; linarith
  · apply eid_denom_lt_top_of_ae_ge hR (c := essInf (fun ω => X ω + Z ω) P - v)
    · filter_upwards [he] with ω hω; linarith
    · exact eid_weight_lt_top _ _ _ (show (0:ℝ) < _ by linarith)

lemma eid_denom_lt_top_of_mem (hR : Assumption31 D R) (hX : Assumption21 P D X)
    (hZ : MemLp Z ⊤ P) {v : ℝ} (hv : v ∈ domH P D R X Z) : denom P D R X Z v < ⊤ := by
  cases D with
  | pos => exact hv.2
  | real =>
    obtain ⟨C, hC⟩ := eid_XZ_bdd hX hZ
    apply eid_denom_lt_top_of_ae_ge hR (c := -C - v)
    · filter_upwards [hC] with ω hω; linarith [(abs_le.1 hω).1]
    · exact eid_weight_lt_top _ _ _ (by simp [Dom.set])

lemma eid_integrable_w (hR : Assumption31 D R) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P)
    {v : ℝ} (hd : denom P D R X Z v < ⊤) :
    Integrable (fun ω => (weight D R (X ω + Z ω - v)).toReal) P :=
  integrable_toReal_of_lintegral_ne_top (eid_w_aemeas hR hX hZ v) hd.ne

lemma eid_integral_w (hR : Assumption31 D R) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P)
    {v : ℝ} (hd : denom P D R X Z v < ⊤) :
    ∫ ω, (weight D R (X ω + Z ω - v)).toReal ∂P = (denom P D R X Z v).toReal :=
  integral_toReal (eid_w_aemeas hR hX hZ v) (ae_lt_top' (eid_w_aemeas hR hX hZ v) hd.ne)

lemma eid_integrable_mul_w (hR : Assumption31 D R) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P)
    {v : ℝ} (hd : denom P D R X Z v < ⊤) {f : Ω → ℝ} (hf : AEStronglyMeasurable f P) {C : ℝ}
    (hC : ∀ᵐ ω ∂P, |f ω| ≤ C) :
    Integrable (fun ω => f ω * (weight D R (X ω + Z ω - v)).toReal) P :=
  (eid_integrable_w hR hX hZ hd).bdd_mul hf (c := C) (by simpa [Real.norm_eq_abs] using hC)

lemma eid_denom_toReal_pos (hR : Assumption31 D R) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P)
    {v : ℝ} (hd : denom P D R X Z v < ⊤) : 0 < (denom P D R X Z v).toReal :=
  ENNReal.toReal_pos (eid_denom_pos' hR hX hZ v).ne' hd.ne

lemma eid_Theta_eq (hR : Assumption31 D R) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P)
    {v : ℝ} (hd : denom P D R X Z v < ⊤) :
    Theta P D R X Z v = (denom P D R X Z v).toReal * (H P D R X Z v - v) := by
  obtain ⟨Cz, hz⟩ := eid_bdd_of_memLp_top hZ
  have h1 := eid_integrable_mul_w hR hX hZ hd hZ.1 hz
  have h2 := eid_integrable_w hR hX hZ hd
  have hpos := eid_denom_toReal_pos hR hX hZ hd
  unfold Theta H
  have : (fun ω => (Z ω - v) * (weight D R (X ω + Z ω - v)).toReal)
      = fun ω => Z ω * (weight D R (X ω + Z ω - v)).toReal
          - v * (weight D R (X ω + Z ω - v)).toReal := by
    funext ω; ring
  rw [this, integral_sub h1 (h2.const_mul v), integral_const_mul, eid_integral_w hR hX hZ hd]
  field_simp

theorem eid_mem_V_iff_Theta_eq_zero (hR : Assumption31 D R) (hX : Assumption21 P D X)
    (hZ : MemLp Z ⊤ P) :
    ∀ v ∈ domH P D R X Z, v = H P D R X Z v ↔ Theta P D R X Z v = 0 := by
  intro v hv
  have hd := eid_denom_lt_top_of_mem hR hX hZ hv
  rw [eid_Theta_eq hR hX hZ hd]
  have hpos := eid_denom_toReal_pos hR hX hZ hd
  constructor
  · intro h; rw [← h]; ring
  · intro h
    rcases mul_eq_zero.1 h with h | h
    · linarith
    · linarith

theorem eid_H_bounds (hR : Assumption31 D R) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P) :
    ∀ v ∈ domH P D R X Z,
      essInf Z P ≤ H P D R X Z v ∧ H P D R X Z v ≤ max (essSup Z P) (essInf (fun ω => X ω + Z ω) P) := by
  intro v hv
  have hd := eid_denom_lt_top_of_mem hR hX hZ hv
  obtain ⟨Cz, hz⟩ := eid_bdd_of_memLp_top hZ
  have h1 := eid_integrable_mul_w hR hX hZ hd hZ.1 hz
  have h2 := eid_integrable_w hR hX hZ hd
  have hpos := eid_denom_toReal_pos hR hX hZ hd
  have hint := eid_integral_w hR hX hZ hd
  have hlo := eid_ae_essInf_le hz
  have hhi := eid_ae_le_essSup hz
  unfold H
  constructor
  · rw [le_div_iff₀ hpos, ← hint, ← integral_const_mul]
    apply integral_mono_ae (h2.const_mul _) h1
    filter_upwards [hlo] with ω hω
    exact mul_le_mul_of_nonneg_right hω ENNReal.toReal_nonneg
  · apply le_trans _ (le_max_left _ _)
    rw [div_le_iff₀ hpos, ← hint, ← integral_const_mul]
    apply integral_mono_ae h1 (h2.const_mul _)
    filter_upwards [hhi] with ω hω
    exact mul_le_mul_of_nonneg_right hω ENNReal.toReal_nonneg

end model




lemma eid_weight_toReal_cont_real {R : ℝ → ℝ} (hR : Assumption31 .real R) :
    Continuous (fun y => (weight .real R y).toReal) := by
  have hc : Continuous R := by
    have := hR.2.1
    rw [show Dom.set .real = Set.univ from rfl, differentiableOn_univ] at this
    exact this.continuous
  have : (fun y => (weight .real R y).toReal) = fun y => Real.exp (-R y) := by
    funext y; exact eid_weight_toReal_of_mem .real R y (by simp [Dom.set])
  rw [this]; fun_prop

lemma eid_weight_toReal_cwa_pos {R : ℝ → ℝ} (hR : Assumption31 .pos R) {y0 : ℝ} (hy0 : 0 ≤ y0)
    (hfin : weight .pos R y0 < ⊤) :
    ContinuousWithinAt (fun y => (weight .pos R y).toReal) (Set.Ici 0) y0 := by
  rcases hy0.lt_or_eq with hy0 | hy0
  · apply ContinuousAt.continuousWithinAt
    have hRc : ContinuousAt R y0 :=
      (hR.2.1.differentiableAt (isOpen_Ioi.mem_nhds hy0)).continuousAt
    have h1 : ContinuousAt (fun y => Real.exp (-R y)) y0 := by
      exact (hRc.neg).rexp
    apply h1.congr
    filter_upwards [isOpen_Ioi.mem_nhds hy0] with y hy
    exact (eid_weight_toReal_of_mem .pos R y hy).symm
  · subst hy0
    rw [← continuousWithinAt_Ioi_iff_Ici]
    have hanti := eid_weight_antitone .pos R hR
    have ht := hanti.tendsto_nhdsGT (0:ℝ)
    have hsup : sSup (weight .pos R '' Set.Ioi 0) = weight .pos R 0 := by
      rw [sSup_image]
      simp only [weight, lt_irrefl, if_false]
      refine iSup_congr (fun z => iSup_congr (fun hz => ?_))
      have : (0:ℝ) < z := hz
      simp [this]
    rw [hsup] at ht
    exact (ENNReal.tendsto_toReal hfin.ne).comp ht

section model
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Dom} {R : ℝ → ℝ} {X Z : Ω → ℝ}

lemma eid_ae_cwa (hR : Assumption31 D R) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P)
    {v : ℝ} (hv : v ∈ domH P D R X Z) :
    ∀ᵐ ω ∂P, ContinuousWithinAt (fun x => (weight D R (X ω + Z ω - x)).toReal)
      (domH P D R X Z) v := by
  cases D with
  | real =>
    refine Filter.Eventually.of_forall (fun ω => ?_)
    exact ((eid_weight_toReal_cont_real hR).comp (continuous_const.sub continuous_id)).continuousWithinAt
  | pos =>
    have hd := eid_denom_lt_top_of_mem hR hX hZ hv
    filter_upwards [hv.1, ae_lt_top' (eid_w_aemeas hR hX hZ v) hd.ne, eid_ae_e_le hX hZ]
      with ω h1 h2 h3
    have hg := eid_weight_toReal_cwa_pos hR (y0 := X ω + Z ω - v) (by linarith) h2
    refine hg.comp (continuous_const.sub continuous_id).continuousWithinAt ?_
    intro x hx
    have := eid_le_e_of_mem_domH_pos hX hZ hx
    show (0:ℝ) ≤ X ω + Z ω - x
    linarith

lemma eid_upper (hR : Assumption31 D R) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P)
    {v : ℝ} (hv : v ∈ domH P D R X Z) :
    ∃ v' ∈ domH P D R X Z, ∀ᶠ x in 𝓝[domH P D R X Z] v, x ≤ v' := by
  cases D with
  | real =>
    refine ⟨v + 1, by simp [domH], ?_⟩
    apply eventually_nhdsWithin_of_eventually_nhds
    filter_upwards [Iio_mem_nhds (show v < v + 1 by linarith)] with x hx
    exact le_of_lt hx
  | pos =>
    by_cases he : essInf (fun ω => X ω + Z ω) P ∈ domH P .pos R X Z
    · exact ⟨_, he, eventually_nhdsWithin_of_forall (fun x hx => eid_le_e_of_mem_domH_pos hX hZ hx)⟩
    · have hle := eid_le_e_of_mem_domH_pos hX hZ hv
      have hlt : v < essInf (fun ω => X ω + Z ω) P := by
        rcases hle.lt_or_eq with h | h
        · exact h
        · exact absurd (h ▸ hv) he
      refine ⟨(v + essInf (fun ω => X ω + Z ω) P) / 2,
        eid_mem_domH_of_lt_pos hR hX hZ (by linarith), ?_⟩
      apply eventually_nhdsWithin_of_eventually_nhds
      filter_upwards [Iio_mem_nhds (show v < (v + essInf (fun ω => X ω + Z ω) P) / 2 by linarith)]
        with x hx
      exact le_of_lt hx

lemma eid_w_le (hR : Assumption31 D R) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P)
    {x v' : ℝ} (hv' : v' ∈ domH P D R X Z) (hx : x ≤ v') :
    ∀ᵐ ω ∂P, (weight D R (X ω + Z ω - x)).toReal ≤ (weight D R (X ω + Z ω - v')).toReal := by
  have hd := eid_denom_lt_top_of_mem hR hX hZ hv'
  filter_upwards [ae_lt_top' (eid_w_aemeas hR hX hZ v') hd.ne] with ω hω
  exact ENNReal.toReal_mono hω.ne (eid_weight_antitone D R hR (by linarith))

lemma eid_N_cwa (hR : Assumption31 D R) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P)
    {v : ℝ} (hv : v ∈ domH P D R X Z) :
    ContinuousWithinAt (fun x => ∫ ω, Z ω * (weight D R (X ω + Z ω - x)).toReal ∂P)
      (domH P D R X Z) v := by
  obtain ⟨v', hv', hev⟩ := eid_upper hR hX hZ hv
  obtain ⟨Cz, hz⟩ := eid_bdd_of_memLp_top hZ
  have hd' := eid_denom_lt_top_of_mem hR hX hZ hv'
  apply continuousWithinAt_of_dominated
    (bound := fun ω => |Cz| * (weight D R (X ω + Z ω - v')).toReal)
  · exact Filter.Eventually.of_forall (fun x => hZ.1.mul (eid_wr_aesm hR hX hZ x))
  · filter_upwards [hev] with x hx
    filter_upwards [eid_w_le hR hX hZ hv' hx, hz] with ω h1 h2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul (h2.trans (le_abs_self _)) h1 ENNReal.toReal_nonneg (abs_nonneg _)
  · exact (eid_integrable_w hR hX hZ hd').const_mul _
  · filter_upwards [eid_ae_cwa hR hX hZ hv] with ω hω
    exact continuousWithinAt_const.mul hω

lemma eid_dR_cwa (hR : Assumption31 D R) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P)
    {v : ℝ} (hv : v ∈ domH P D R X Z) :
    ContinuousWithinAt (fun x => ∫ ω, (weight D R (X ω + Z ω - x)).toReal ∂P)
      (domH P D R X Z) v := by
  obtain ⟨v', hv', hev⟩ := eid_upper hR hX hZ hv
  have hd' := eid_denom_lt_top_of_mem hR hX hZ hv'
  apply continuousWithinAt_of_dominated
    (bound := fun ω => (weight D R (X ω + Z ω - v')).toReal)
  · exact Filter.Eventually.of_forall (fun x => eid_wr_aesm hR hX hZ x)
  · filter_upwards [hev] with x hx
    filter_upwards [eid_w_le hR hX hZ hv' hx] with ω h1
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact h1
  · exact eid_integrable_w hR hX hZ hd'
  · exact eid_ae_cwa hR hX hZ hv

theorem eid_H_continuousOn (hR : Assumption31 D R) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P) :
    ContinuousOn (H P D R X Z) (domH P D R X Z) := by
  intro v hv
  have hd := eid_denom_lt_top_of_mem hR hX hZ hv
  have hpos := eid_denom_toReal_pos hR hX hZ hd
  have h := (eid_N_cwa hR hX hZ hv).div (eid_dR_cwa hR hX hZ hv)
    (by rw [eid_integral_w hR hX hZ hd]; exact hpos.ne')
  apply h.congr
  · intro x hx
    simp only [H, Pi.div_apply]
    rw [eid_integral_w hR hX hZ (eid_denom_lt_top_of_mem hR hX hZ hx)]
  · simp only [H, Pi.div_apply]
    rw [eid_integral_w hR hX hZ hd]

end model




lemma eid_weight_rcont_pos {R : ℝ → ℝ} (hR : Assumption31 .pos R) {y : ℝ} (hy : 0 ≤ y) :
    Filter.Tendsto (weight .pos R) (𝓝[>] y) (𝓝 (weight .pos R y)) := by
  rcases hy.lt_or_eq with hy | hy
  · apply ContinuousAt.continuousWithinAt
    have hRc : ContinuousAt R y :=
      (hR.2.1.differentiableAt (isOpen_Ioi.mem_nhds hy)).continuousAt
    have h1 : ContinuousAt (fun y => ENNReal.ofReal (Real.exp (-R y))) y :=
      ENNReal.continuous_ofReal.continuousAt.comp (hRc.neg.rexp)
    apply h1.congr
    filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
    have : (0:ℝ) < z := hz
    simp [weight, this]
  · subst hy
    have ht := (eid_weight_antitone .pos R hR).tendsto_nhdsGT (0:ℝ)
    have hsup : sSup (weight .pos R '' Set.Ioi 0) = weight .pos R 0 := by
      rw [sSup_image]
      simp only [weight, lt_irrefl, if_false]
      refine iSup_congr (fun z => iSup_congr (fun hz => ?_))
      have : (0:ℝ) < z := hz
      simp [this]
    rwa [hsup] at ht

lemma eid_weight_iSup_pos {R : ℝ → ℝ} (hR : Assumption31 .pos R) {y : ℝ} (hy : 0 ≤ y) :
    ⨆ n : ℕ, weight .pos R (y + 1 / ((n:ℝ) + 1)) = weight .pos R y := by
  apply iSup_eq_of_tendsto
  · intro n m hnm
    apply eid_weight_antitone .pos R hR
    have : ((n:ℝ) + 1) ≤ (m:ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
    have h0 : (0:ℝ) < (n:ℝ) + 1 := by positivity
    have := one_div_le_one_div_of_le h0 this
    linarith
  · apply (eid_weight_rcont_pos hR hy).comp
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Filter.Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) Filter.atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (tendsto_const_nhds (x := y)).add this
    · exact Filter.Eventually.of_forall (fun n => by
        show y < y + 1 / ((n:ℝ) + 1)
        have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
        linarith)

section model
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Dom} {R : ℝ → ℝ} {X Z : Ω → ℝ}

lemma eid_denom_mono (hR : Assumption31 D R) {u v : ℝ} (huv : u ≤ v) :
    denom P D R X Z u ≤ denom P D R X Z v := by
  unfold denom
  apply lintegral_mono
  intro ω
  exact eid_weight_antitone D R hR (by linarith)

lemma eid_mem_domH_of_le_pos (hR : Assumption31 .pos R) {u v : ℝ}
    (hv : v ∈ domH P .pos R X Z) (huv : u ≤ v) : u ∈ domH P .pos R X Z := by
  refine ⟨?_, lt_of_le_of_lt (eid_denom_mono hR huv) hv.2⟩
  filter_upwards [hv.1] with ω hω; linarith

lemma eid_mem_domH_of_le (hR : Assumption31 D R) {u v : ℝ}
    (hv : v ∈ domH P D R X Z) (huv : u ≤ v) : u ∈ domH P D R X Z := by
  cases D with
  | real => simp [domH]
  | pos => exact eid_mem_domH_of_le_pos hR hv huv

lemma eid_not_mem_iff_pos (hR : Assumption31 .pos R) (hX : Assumption21 P .pos X)
    (hZ : MemLp Z ⊤ P) :
    essInf (fun ω => X ω + Z ω) P ∉ domH P .pos R X Z ↔
      denom P .pos R X Z (essInf (fun ω => X ω + Z ω) P) = ⊤ := by
  constructor
  · intro h
    by_contra h'
    exact h ⟨eid_ae_e_le hX hZ, lt_top_iff_ne_top.2 h'⟩
  · intro h h'
    exact (lt_top_iff_ne_top.1 h'.2) h

/-- As `v ↗ ess inf[𝒳+Z]` with infinite denominator at the end point, the denominator blows up. -/
lemma eid_denom_tendsto_top (hR : Assumption31 .pos R) (hX : Assumption21 P .pos X)
    (hZ : MemLp Z ⊤ P) (htop : denom P .pos R X Z (essInf (fun ω => X ω + Z ω) P) = ⊤)
    (M : ℝ≥0∞) (hM : M < ⊤) :
    ∀ᶠ u in 𝓝[<] (essInf (fun ω => X ω + Z ω) P), M < denom P .pos R X Z u := by
  set e := essInf (fun ω => X ω + Z ω) P with he_def
  have hsup : ∀ᵐ ω ∂P, ⨆ n : ℕ, weight .pos R (X ω + Z ω - (e - 1 / ((n:ℝ) + 1)))
      = weight .pos R (X ω + Z ω - e) := by
    filter_upwards [eid_ae_e_le hX hZ] with ω hω
    have := eid_weight_iSup_pos hR (y := X ω + Z ω - e) (by linarith)
    rw [← this]
    congr 1; funext n; congr 1; ring
  have hlim : ⨆ n : ℕ, denom P .pos R X Z (e - 1 / ((n:ℝ) + 1)) = ⊤ := by
    unfold denom
    rw [← lintegral_iSup']
    · rw [lintegral_congr_ae hsup]; exact htop
    · exact fun n => eid_w_aemeas hR hX hZ _
    · refine Filter.Eventually.of_forall (fun ω n m hnm => ?_)
      apply eid_weight_antitone .pos R hR
      have : ((n:ℝ) + 1) ≤ (m:ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hnm 1
      have h0 : (0:ℝ) < (n:ℝ) + 1 := by positivity
      have := one_div_le_one_div_of_le h0 this
      linarith
  rw [← hlim] at hM
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 hM
  have hpos : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
  apply eventually_nhdsWithin_of_eventually_nhds
  filter_upwards [Ioi_mem_nhds (show e - 1 / ((n:ℝ) + 1) < e by linarith)] with u hu
  exact lt_of_lt_of_le hn (eid_denom_mono hR (le_of_lt hu))

/-- Proof of Corollary 3.5: if the denominator is infinite at `ess inf[𝒳+Z]`, then `H_Z(v)` stays
below `ess inf[𝒳+Z] - δ` as `v ↗ ess inf[𝒳+Z]`. -/
lemma eid_H_le_of_top (hR : Assumption31 .pos R) (hX : Assumption21 P .pos X)
    (hZ : MemLp Z ⊤ P) (htop : denom P .pos R X Z (essInf (fun ω => X ω + Z ω) P) = ⊤) :
    ∃ δ > 0, ∀ᶠ u in 𝓝[<] (essInf (fun ω => X ω + Z ω) P),
      H P .pos R X Z u ≤ essInf (fun ω => X ω + Z ω) P - δ := by
  set e := essInf (fun ω => X ω + Z ω) P with he_def
  obtain ⟨Cx, hx⟩ := eid_bdd_of_memLp_top hX.1
  obtain ⟨Cz, hz⟩ := eid_bdd_of_memLp_top hZ
  have hX0 : (0:ℝ) < essInf X P := hX.2.2
  set ε := essInf X P / 3 with hε
  have hεpos : 0 < ε := by positivity
  have hXlow := eid_ae_essInf_le hx
  have hel := eid_ae_e_le hX hZ
  set K := |Cz| + |e| with hK
  have hK0 : 0 ≤ K := by positivity
  set c0 := (weight .pos R ε).toReal with hc0
  have hc0' : 0 ≤ c0 := ENNReal.toReal_nonneg
  set B := (2 * ε + K) * c0 with hB
  have hB0 : 0 ≤ B := by positivity
  refine ⟨ε, hεpos, ?_⟩
  have hev := eid_denom_tendsto_top hR hX hZ htop (ENNReal.ofReal (B / ε)) ENNReal.ofReal_lt_top
  filter_upwards [hev, self_mem_nhdsWithin] with u hu hlt
  have hlt' : u < e := hlt
  have hdom := eid_mem_domH_of_lt_pos hR hX hZ hlt'
  have hd := hdom.2
  have hpos := eid_denom_toReal_pos hR hX hZ hd
  have hint := eid_integral_w hR hX hZ hd
  have hI1 := eid_integrable_w hR hX hZ hd
  have hI2 := eid_integrable_mul_w hR hX hZ hd hZ.1 hz
  have hbig : B / ε < (denom P .pos R X Z u).toReal := by
    have := (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hd.ne).1 hu
    exact this
  -- pointwise bound
  have hpt : ∀ᵐ ω ∂P, Z ω * (weight .pos R (X ω + Z ω - u)).toReal ≤
      (e - 2 * ε) * (weight .pos R (X ω + Z ω - u)).toReal + B := by
    filter_upwards [hXlow, hel, hz] with ω h1 h2 h3
    have hw0 : 0 ≤ (weight .pos R (X ω + Z ω - u)).toReal := ENNReal.toReal_nonneg
    by_cases hA : X ω + Z ω - e < ε
    · have : Z ω ≤ e - 2 * ε := by linarith
      have := mul_le_mul_of_nonneg_right this hw0
      linarith
    · push Not at hA
      have hw : (weight .pos R (X ω + Z ω - u)).toReal ≤ c0 := by
        apply ENNReal.toReal_mono (eid_weight_lt_top .pos R ε hεpos).ne
        apply eid_weight_antitone .pos R hR
        linarith
      have hZe : Z ω - (e - 2 * ε) ≤ 2 * ε + K := by
        have := (abs_le.1 h3).2
        have : Z ω ≤ |Cz| := this.trans (le_abs_self _)
        have : -e ≤ |e| := neg_le_abs e
        linarith
      have : (Z ω - (e - 2 * ε)) * (weight .pos R (X ω + Z ω - u)).toReal ≤ (2 * ε + K) * c0 := by
        calc (Z ω - (e - 2 * ε)) * (weight .pos R (X ω + Z ω - u)).toReal
            ≤ (2 * ε + K) * (weight .pos R (X ω + Z ω - u)).toReal :=
              mul_le_mul_of_nonneg_right hZe hw0
          _ ≤ (2 * ε + K) * c0 := mul_le_mul_of_nonneg_left hw (by positivity)
      linarith
  have hN : ∫ ω, Z ω * (weight .pos R (X ω + Z ω - u)).toReal ∂P ≤
      (e - 2 * ε) * (denom P .pos R X Z u).toReal + B := by
    have hI3 : Integrable (fun ω => (e - 2 * ε) * (weight .pos R (X ω + Z ω - u)).toReal + B) P :=
      (hI1.const_mul (e - 2 * ε)).add (integrable_const B)
    have := integral_mono_ae hI2 hI3 hpt
    rw [integral_add (hI1.const_mul _) (integrable_const B), integral_const_mul, hint] at this
    simpa using this
  unfold H
  rw [div_le_iff₀ hpos]
  have : B ≤ ε * (denom P .pos R X Z u).toReal := by
    rw [div_lt_iff₀ hεpos] at hbig; linarith
  nlinarith

lemma eid_exists_fixed (hR : Assumption31 D R) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P)
    {a b : ℝ} (hab : a ≤ b) (hb : b ∈ domH P D R X Z) (ha : a ≤ H P D R X Z a)
    (hb' : H P D R X Z b ≤ b) : (V P D R X Z).Nonempty := by
  have hsub : Set.Icc a b ⊆ domH P D R X Z := fun x hx => eid_mem_domH_of_le hR hb hx.2
  have hcont : ContinuousOn (fun v => H P D R X Z v - v) (Set.Icc a b) :=
    ((eid_H_continuousOn hR hX hZ).mono hsub).sub continuousOn_id
  have := intermediate_value_Icc' hab hcont
  have h0 : (0:ℝ) ∈ Set.Icc (H P D R X Z b - b) (H P D R X Z a - a) := ⟨by linarith, by linarith⟩
  obtain ⟨c, hc, hc0⟩ := this h0
  exact ⟨c, hsub hc, by simp only at hc0; linarith⟩

lemma eid_exists_of_v0 (hR : Assumption31 D R) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P)
    {v0 : ℝ} (hv0 : v0 ∈ domH P D R X Z) (hle : H P D R X Z v0 ≤ v0) :
    (V P D R X Z).Nonempty := by
  have hmin := min_le_right (essInf Z P) v0
  apply eid_exists_fixed hR hX hZ hmin hv0 _ hle
  have := (eid_H_bounds hR hX hZ _ (eid_mem_domH_of_le hR hv0 hmin)).1
  exact (min_le_left _ _).trans this

lemma eid_closed_sub (hR : Assumption31 D R) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P) :
    ∃ K : Set ℝ, IsClosed K ∧ K ⊆ domH P D R X Z ∧ V P D R X Z ⊆ K := by
  cases D with
  | real => exact ⟨Set.univ, isClosed_univ, fun x _ => by simp [domH], Set.subset_univ _⟩
  | pos =>
    set e := essInf (fun ω => X ω + Z ω) P with he_def
    by_cases he : e ∈ domH P .pos R X Z
    · refine ⟨Set.Iic e, isClosed_Iic, fun x hx => eid_mem_domH_of_le_pos hR he hx, ?_⟩
      intro v hv; exact eid_le_e_of_mem_domH_pos hX hZ hv.1
    · have htop := (eid_not_mem_iff_pos hR hX hZ).1 he
      obtain ⟨δ, hδ, hev⟩ := eid_H_le_of_top hR hX hZ htop
      obtain ⟨l, hl, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).1 hev
      have hl' : l < e := hl
      set m := max l (e - δ) with hm
      have hme : m < e := max_lt hl' (by linarith)
      refine ⟨Set.Iic m, isClosed_Iic, fun x hx => eid_mem_domH_of_lt_pos hR hX hZ
        (lt_of_le_of_lt hx hme), ?_⟩
      intro v hv
      have hve : v ≤ e := eid_le_e_of_mem_domH_pos hX hZ hv.1
      have hve' : v < e := by
        rcases hve.lt_or_eq with h | h
        · exact h
        · exact absurd (h ▸ hv.1) he
      by_contra hvm
      simp only [Set.mem_Iic, not_le] at hvm
      have h1 : v ∈ Set.Ioo l e := ⟨lt_of_le_of_lt (le_max_left _ _) hvm, hve'⟩
      have h2 := hsub h1
      simp only [Set.mem_setOf_eq] at h2
      have h3 : e - δ < v := lt_of_le_of_lt (le_max_right _ _) hvm
      have h4 := hv.2
      linarith

theorem eid_theorem_3_2 (hR : Assumption31 D R) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P) :
    ((D = .real ∨ (D = .pos ∧ ∃ v₀ ∈ domH P D R X Z, H P D R X Z v₀ ≤ v₀)) →
        (V P D R X Z).Nonempty) ∧
    (D = .pos →
        ((essInf (fun ω => X ω + Z ω) P) ∈ domH P D R X Z ∧ H P D R X Z (essInf (fun ω => X ω + Z ω) P) ≤ essInf (fun ω => X ω + Z ω) P ∨
          (essInf (fun ω => X ω + Z ω) P) ∉ domH P D R X Z ∧
            Filter.liminf (H P D R X Z) (𝓝[<] (essInf (fun ω => X ω + Z ω) P)) < essInf (fun ω => X ω + Z ω) P) →
        ∃ v₀ ∈ domH P D R X Z, H P D R X Z v₀ ≤ v₀) ∧
    IsCompact (V P D R X Z) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro (hD | ⟨_, v0, hv0, hle⟩)
    · subst hD
      set b := max (essSup Z P) (essInf (fun ω => X ω + Z ω) P)
      have hb : b ∈ domH P .real R X Z := by simp [domH]
      have hbH := eid_H_bounds hR hX hZ b hb
      have ha : essInf Z P ∈ domH P .real R X Z := by simp [domH]
      have haH := eid_H_bounds hR hX hZ _ ha
      exact eid_exists_fixed hR hX hZ (hbH.1.trans hbH.2) hb haH.1 hbH.2
    · exact eid_exists_of_v0 hR hX hZ hv0 hle
  · intro hD hcond
    subst hD
    rcases hcond with ⟨he, hle⟩ | ⟨he, hlim⟩
    · exact ⟨_, he, hle⟩
    · set e := essInf (fun ω => X ω + Z ω) P with he_def
      set L := Filter.liminf (H P .pos R X Z) (𝓝[<] e) with hL
      have hcob : Filter.IsCoboundedUnder (· ≥ ·) (𝓝[<] e) (H P .pos R X Z) := by
        apply Filter.isCoboundedUnder_ge_of_eventually_le (𝓝[<] e)
          (x := max (essSup Z P) e)
        filter_upwards [self_mem_nhdsWithin] with u hu
        exact (eid_H_bounds hR hX hZ u (eid_mem_domH_of_lt_pos hR hX hZ hu)).2
      have hfreq := Filter.frequently_lt_of_liminf_lt hcob (show L < (L + e) / 2 by linarith)
      have hev : ∀ᶠ u in 𝓝[<] e, (L + e) / 2 < u ∧ u < e := by
        filter_upwards [eventually_nhdsWithin_of_eventually_nhds
          (Ioi_mem_nhds (show (L + e) / 2 < e by linarith)), self_mem_nhdsWithin] with u h1 h2
        exact ⟨h1, h2⟩
      obtain ⟨u, hu1, hu2, hu3⟩ := (hfreq.and_eventually hev).exists
      exact ⟨u, eid_mem_domH_of_lt_pos hR hX hZ hu3, by linarith⟩
  · obtain ⟨K, hK, hKd, hVK⟩ := eid_closed_sub hR hX hZ
    have hcont : ContinuousOn (fun v => H P D R X Z v - v) K :=
      ((eid_H_continuousOn hR hX hZ).mono hKd).sub continuousOn_id
    have hcl := hcont.preimage_isClosed_of_isClosed hK (isClosed_singleton (x := (0:ℝ)))
    have hVeq : V P D R X Z = K ∩ (fun v => H P D R X Z v - v) ⁻¹' {0} := by
      ext v
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hv; exact ⟨hVK hv, by rw [← hv.2]; ring⟩
      · rintro ⟨h1, h2⟩; exact ⟨hKd h1, by linarith⟩
    rw [hVeq]
    apply (isCompact_Icc (a := essInf Z P)
      (b := max (essSup Z P) (essInf (fun ω => X ω + Z ω) P))).of_isClosed_subset hcl
    rintro v ⟨h1, h2⟩
    have hb := eid_H_bounds hR hX hZ v (hKd h1)
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h2
    have : v = H P D R X Z v := by linarith
    rw [this]; exact hb

theorem eid_corollary_3_5 (hR : Assumption31 .pos R) (hX : Assumption21 P .pos X)
    (hZ : MemLp Z ⊤ P) :
    denom P .pos R X Z (essInf (fun ω => X ω + Z ω) P) = ⊤ → (V P .pos R X Z).Nonempty := by
  intro htop
  set e := essInf (fun ω => X ω + Z ω) P with he_def
  obtain ⟨δ, hδ, hev⟩ := eid_H_le_of_top hR hX hZ htop
  have hev2 : ∀ᶠ u in 𝓝[<] e, e - δ < u ∧ u < e := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (Ioi_mem_nhds (show e - δ < e by linarith)), self_mem_nhdsWithin] with u h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨u, hu1, hu2, hu3⟩ := (hev.and hev2).exists
  exact eid_exists_of_v0 hR hX hZ (eid_mem_domH_of_lt_pos hR hX hZ hu3) (by linarith)

end model

end EndoInvDemand.Clearing

open EndoInvDemand.Clearing

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (R : ℝ → ℝ) (hR : Assumption31 .pos R)
    (X Z : Ω → ℝ) (hX : Assumption21 P .pos X) (hZ : MemLp Z ⊤ P) :
    denom P .pos R X Z (essInf (fun ω => X ω + Z ω) P) = ⊤ → (V P .pos R X Z).Nonempty :=
  eid_corollary_3_5 hR hX hZ
