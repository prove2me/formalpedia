-- Prove2me | solution 1 for EpiControl.SinglePeak.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:04:51.000464+00:00
-- url     : https://prove2.me/submissions/ce2a694a-cbca-4d42-a33f-224a394e498b

import Mathlib
import Definitions.Def_EpiControl_SinglePeak_Model

open MeasureTheory Set Filter Topology

namespace EpiAux13

open EpiControl.SinglePeak

/-- The largest minimiser of `b ↦ y b + c(b)` over `B`. -/
noncomputable def sel (P : Params) (y : ℝ) : ℝ :=
  sSup {b | P.ArgminAt y b}

theorem argmin_closed_nonempty (P : Params) (hP : P.Standing) (y : ℝ) :
    IsClosed {b | P.ArgminAt y b} ∧ {b | P.ArgminAt y b}.Nonempty ∧
      {b | P.ArgminAt y b} ⊆ Icc P.bl P.bbar := by
  have hf : ContinuousOn (fun b => y * b + P.c b) (Icc P.bl P.bbar) :=
    (continuousOn_const.mul continuousOn_id).add hP.c_cont
  obtain ⟨b0, hb0, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.2 hP.bl_lt_bbar.le) hf
  have heq : {b | P.ArgminAt y b} =
      Icc P.bl P.bbar ∩ (fun b => y * b + P.c b) ⁻¹' Iic (y * b0 + P.c b0) := by
    ext b
    simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, mem_Iic, Params.ArgminAt]
    constructor
    · rintro ⟨hb, h⟩; exact ⟨hb, h b0 hb0⟩
    · rintro ⟨hb, h⟩; exact ⟨hb, fun b' hb' => h.trans (hmin hb')⟩
  refine ⟨?_, ⟨b0, hb0, fun b' hb' => hmin hb'⟩, fun b hb => hb.1⟩
  rw [heq]
  exact hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic

theorem sel_spec (P : Params) (hP : P.Standing) (y : ℝ) : P.ArgminAt y (sel P y) := by
  obtain ⟨hc, hne, hsub⟩ := argmin_closed_nonempty P hP y
  exact hc.csSup_mem hne ⟨P.bbar, fun b hb => (hsub hb).2⟩

theorem argmin_anti (P : Params) {y y' b b' : ℝ} (h : P.ArgminAt y b) (h' : P.ArgminAt y' b')
    (hlt : y < y') : b' ≤ b := by
  have h1 := h.2 b' h'.1
  have h2 := h'.2 b h.1
  by_contra hne
  push Not at hne
  have : (y' - y) * (b' - b) > 0 := mul_pos (by linarith) (by linarith)
  nlinarith

theorem sel_anti (P : Params) (hP : P.Standing) : Antitone (sel P) := by
  intro y y' hle
  rcases hle.eq_or_lt with h | h
  · rw [h]
  obtain ⟨_, hne', hsub'⟩ := argmin_closed_nonempty P hP y'
  apply csSup_le hne'
  intro b' hb'
  exact argmin_anti P (sel_spec P hP y) hb' h

end EpiAux13

open EpiControl.SinglePeak in
theorem solution (P : Params) (hP : P.Standing) (β s i : ℝ → ℝ)
    (hopt : P.IsOptimal β s i) (η : ℝ → ℝ) (hη : P.IsCostate β s i η) :
    ∃ βh : ℝ → ℝ, P.IsOptimal βh s i ∧
      βh =ᵐ[volume.restrict (Icc 0 P.T)] β ∧
      ∀ t ∈ Icc 0 P.T, P.ArgminAt (gain η s i t) (βh t) := by
  classical
  have hT : 0 ≤ P.T := hP.T_pos.le
  obtain ⟨hadm, hpath, hJ⟩ := hopt
  obtain ⟨hηc, _, _, h4, _⟩ := hη
  obtain ⟨hsc, hic, heq⟩ := hpath
  set μ := volume.restrict (Icc (0:ℝ) P.T) with hμ
  set bad := {t : ℝ | ¬ P.ArgminAt (η t * i t * s t) (β t)} with hbad
  have hbad0 : μ bad = 0 := by
    rw [← ae_iff.symm.trans (by rfl : μ bad = 0 ↔ μ bad = 0)]
    have := ae_iff.1 h4
    exact this
  set N := toMeasurable μ bad with hN
  have hNm : MeasurableSet N := measurableSet_toMeasurable μ bad
  have hN0 : μ N = 0 := by rw [hN, measure_toMeasurable]; exact hbad0
  set clamp : ℝ → ℝ := fun t => max 0 (min t P.T) with hclamp
  have hclampI : ∀ t, clamp t ∈ Icc 0 P.T := fun t =>
    ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hclampid : ∀ t ∈ Icc 0 P.T, clamp t = t := fun t ht => by
    simp only [hclamp]; rw [min_eq_left ht.2, max_eq_right ht.1]
  have hcl : Continuous clamp := continuous_const.max (continuous_id.min continuous_const)
  have hG : Continuous (fun t => gain η s i (clamp t)) := by
    have : ContinuousOn (gain η s i) (Icc 0 P.T) := (hηc.mul hic).mul hsc
    exact this.comp_continuous hcl hclampI
  let βh : ℝ → ℝ := N.piecewise (fun t => EpiAux13.sel P (gain η s i (clamp t))) β
  have hβh_meas : Measurable βh :=
    Measurable.piecewise hNm (((EpiAux13.sel_anti P hP).measurable.comp hG.measurable :
      Measurable fun t => EpiAux13.sel P (gain η s i (clamp t)))) hadm.1
  have hae : βh =ᵐ[μ] β := by
    have : ∀ᵐ t ∂μ, t ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
    filter_upwards [this] with t ht
    simp [βh, Set.piecewise, ht]
  have hae' : ∀ᵐ t, t ∈ Icc 0 P.T → βh t = β t := (ae_restrict_iff' measurableSet_Icc).1 hae
  have hint_congr : ∀ t ∈ Icc 0 P.T, ∀ F : ℝ → ℝ → ℝ,
      (∫ r in (0:ℝ)..t, F (βh r) r) = ∫ r in (0:ℝ)..t, F (β r) r := by
    intro t ht F
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae'] with r hr hrI
    rw [uIoc_of_le ht.1] at hrI
    rw [hr ⟨hrI.1.le, hrI.2.trans ht.2⟩]
  have hadmh : P.Admissible βh := by
    refine ⟨hβh_meas, fun t ht => ?_⟩
    by_cases htN : t ∈ N
    · simp only [βh, Set.piecewise, htN, if_true]
      exact (EpiAux13.sel_spec P hP _).1
    · simp only [βh, Set.piecewise, htN, if_false]
      exact hadm.2 t ht
  have hJeq : P.J βh i = P.J β i := by
    unfold Params.J
    rw [hint_congr P.T ⟨hT, le_rfl⟩ (fun b r => P.v (i r) + P.c b)]
  refine ⟨βh, ⟨hadmh, ⟨hsc, hic, fun t ht => ?_⟩, fun β' s' i' h1 h2 => ?_⟩, hae, ?_⟩
  · rw [hint_congr t ht (fun b r => b * i r * s r),
      hint_congr t ht (fun b r => b * i r * s r - P.γ * i r)]
    exact heq t ht
  · rw [hJeq]; exact hJ β' s' i' h1 h2
  · intro t ht
    by_cases htN : t ∈ N
    · simp only [βh, Set.piecewise, htN, if_true]
      rw [hclampid t ht]
      exact EpiAux13.sel_spec P hP _
    · simp only [βh, Set.piecewise, htN, if_false]
      have : t ∉ bad := fun h => htN (subset_toMeasurable μ bad h)
      simp only [hbad, mem_ofPred_eq, not_not] at this
      exact this
