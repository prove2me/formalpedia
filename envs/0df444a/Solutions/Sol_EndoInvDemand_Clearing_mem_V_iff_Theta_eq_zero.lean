-- Prove2me | solution 1 for EndoInvDemand.Clearing.mem_V_iff_Theta_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T22:27:15.456538+00:00
-- url     : https://prove2.me/submissions/75ca647c-cece-475b-906c-b249491ca673

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

end EndoInvDemand.Clearing

open EndoInvDemand.Clearing

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Dom) (R : ℝ → ℝ) (hR : Assumption31 D R)
    (X Z : Ω → ℝ) (hX : Assumption21 P D X) (hZ : MemLp Z ⊤ P) :
    ∀ v ∈ domH P D R X Z, v = H P D R X Z v ↔ Theta P D R X Z v = 0 :=
  eid_mem_V_iff_Theta_eq_zero hR hX hZ
