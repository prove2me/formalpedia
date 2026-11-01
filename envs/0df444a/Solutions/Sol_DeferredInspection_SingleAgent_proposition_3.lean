-- Prove2me | solution 1 for DeferredInspection.SingleAgent.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T01:22:00.995665+00:00
-- url     : https://prove2.me/submissions/acfe85b6-e953-43c1-bb0c-7b5fd6b17782

import Mathlib
import Definitions.Def_DeferredInspection_SingleAgent_Model

open DeferredInspection.SingleAgent MeasureTheory Set Filter Topology

namespace DIP3

variable {x : ℝ → ℝ} {vh : ℝ} (hx : IsSCD x vh)
include hx

lemma vh_pos : 0 < vh := by
  obtain ⟨-, hvh, -, -, h0, h1⟩ := hx
  rcases hvh.1.lt_or_eq with h | h
  · exact h
  · exfalso; have := h1 0 ⟨h.ge, zero_le_one⟩; rw [h0] at this; norm_num at this

lemma x_le_one {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) : x u ≤ 1 := (hx.1 u hu).2

lemma x_mono : MonotoneOn x (Icc 0 1) := by
  obtain ⟨hA, hvh, hsc, -, -, h1⟩ := hx
  intro a ha b hb hab
  rcases le_or_gt vh b with hbv | hbv
  · rw [h1 b ⟨hbv, hb.2⟩]; exact (hA a ha).2
  rcases hab.lt_or_eq with hab' | hab'
  · have haI : a ∈ Icc 0 vh := ⟨ha.1, hab.trans hbv.le⟩
    have hvI : vh ∈ Icc 0 vh := ⟨hvh.1, le_rfl⟩
    have hden : 0 < vh - a := by linarith
    set α := (vh - b) / (vh - a)
    set β := (b - a) / (vh - a)
    have hα : 0 ≤ α := div_nonneg (by linarith) hden.le
    have hβ : 0 ≤ β := div_nonneg (by linarith) hden.le
    have hαβ : α + β = 1 := by simp only [α, β]; field_simp; ring
    have hcomb : α • a + β • vh = b := by
      simp only [smul_eq_mul, α, β]; field_simp; ring
    have := hsc.concaveOn.2 haI hvI hα hβ hαβ
    rw [hcomb, h1 vh ⟨le_rfl, hvh.2⟩] at this
    simp only [smul_eq_mul] at this
    have hxa := (hA a ha).2
    nlinarith
  · rw [hab']

/-- `u` is a maximizer of `w ↦ v x(w) - w` on `[0,v]`. -/
def IsMax' (x : ℝ → ℝ) (v u : ℝ) : Prop :=
  u ∈ Icc 0 v ∧ IsMinOn (fun w => v * (x v - x w) + w) (Icc 0 v) u

omit hx in
lemma isMax'_iff {v u : ℝ} : IsMax' x v u ↔
    u ∈ Icc 0 v ∧ ∀ w ∈ Icc 0 v, v * x w - w ≤ v * x u - u := by
  unfold IsMax'
  refine and_congr_right fun _ => ?_
  rw [isMinOn_iff]
  refine forall₂_congr fun w _ => ?_
  constructor <;> intro h <;> linarith

lemma max_le_vh {v u : ℝ} (hv : v ∈ Icc (0:ℝ) 1) (hu : IsMax' x v u) : u ≤ vh := by
  rw [isMax'_iff] at hu
  by_contra h
  push Not at h
  have hvhv : vh ≤ v := h.le.trans hu.1.2
  have := hu.2 vh ⟨hx.2.1.1, hvhv⟩
  rw [hx.2.2.2.2.2 vh ⟨le_rfl, hx.2.1.2⟩, hx.2.2.2.2.2 u ⟨h.le, hu.1.2.trans hv.2⟩] at this
  linarith

lemma exists_max {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) : ∃ u, IsMax' x v u := by
  have hvh := vh_pos hx
  set m := min v vh
  have hK : IsCompact (Icc 0 m) := isCompact_Icc
  have hne : (Icc 0 m).Nonempty := nonempty_Icc.2 (le_min hv.1 hvh.le)
  have hcont : ContinuousOn (fun w => v * x w - w) (Icc 0 m) :=
    ((continuousOn_const.mul (hx.2.2.2.1.continuousOn)).sub continuousOn_id).mono
      (Icc_subset_Icc le_rfl (min_le_right _ _))
  obtain ⟨u, hu, humax⟩ := hK.exists_isMaxOn hne hcont
  refine ⟨u, isMax'_iff.2 ⟨⟨hu.1, hu.2.trans (min_le_left _ _)⟩, ?_⟩⟩
  intro w hw
  rcases le_or_gt w m with hwm | hwm
  · exact humax ⟨hw.1, hwm⟩
  · have hwvh : vh < w := by
      rcases le_total v vh with h | h
      · exfalso; have : m = v := min_eq_left h; linarith [hw.2]
      · have : m = vh := min_eq_right h; linarith
    have hvhm : vh ∈ Icc 0 m := ⟨hvh.le, le_min (hwvh.le.trans hw.2) le_rfl⟩
    have := humax hvhm
    simp only [mem_setOf_eq] at this
    rw [hx.2.2.2.2.2 vh ⟨le_rfl, hx.2.1.2⟩] at this
    rw [hx.2.2.2.2.2 w ⟨hwvh.le, hw.2.trans hv.2⟩]
    linarith

lemma max_unique {v u1 u2 : ℝ} (hv : v ∈ Icc (0:ℝ) 1) (h1 : IsMax' x v u1) (h2 : IsMax' x v u2) :
    u1 = u2 := by
  have hb1 := max_le_vh hx hv h1
  have hb2 := max_le_vh hx hv h2
  rw [isMax'_iff] at h1 h2
  by_contra hne
  rcases hv.1.lt_or_eq with hv0 | hv0
  · have hsc := hx.2.2.1
    have hI1 : u1 ∈ Icc 0 vh := ⟨h1.1.1, hb1⟩
    have hI2 : u2 ∈ Icc 0 vh := ⟨h2.1.1, hb2⟩
    have := hsc.2 hI1 hI2 hne (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2)
      (by norm_num : (1/2:ℝ) + 1/2 = 1)
    simp only [smul_eq_mul] at this
    have hmI : 1/2 * u1 + 1/2 * u2 ∈ Icc 0 v := ⟨by linarith [h1.1.1, h2.1.1], by linarith [h1.1.2, h2.1.2]⟩
    have e1 := h1.2 _ hmI
    have e12 := h1.2 u2 h2.1
    have e21 := h2.2 u1 h1.1
    nlinarith
  · subst hv0
    exact hne (le_antisymm h1.1.2 h1.1.1 ▸ (le_antisymm h2.1.2 h2.1.1).symm)

lemma bestAlt_spec {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) : IsMax' x v (bestAltOf x v) := by
  obtain ⟨u, hu⟩ := exists_max hx hv
  have hset : {u | u ∈ Icc 0 v ∧ IsMinOn (fun w => v * (x v - x w) + w) (Icc 0 v) u} = {u} := by
    ext u'
    constructor
    · intro h; exact max_unique hx hv h hu
    · rintro rfl; exact hu
  unfold bestAltOf
  rw [hset, csSup_singleton]
  exact hu

lemma bestAlt_strict {v w : ℝ} (hv : v ∈ Icc (0:ℝ) 1) (hw : w ∈ Icc 0 v) (hne : w ≠ bestAltOf x v) :
    v * x w - w < v * x (bestAltOf x v) - bestAltOf x v := by
  have hs := isMax'_iff.1 (bestAlt_spec hx hv)
  rcases (hs.2 w hw).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hne
    apply max_unique hx hv _ (bestAlt_spec hx hv)
    rw [isMax'_iff]
    refine ⟨hw, fun w' hw' => ?_⟩
    rw [h]; exact hs.2 w' hw'

lemma bestAlt_mono : MonotoneOn (bestAltOf x) (Icc 0 1) := by
  intro v1 hv1 v2 hv2 h12
  by_contra hlt
  push Not at hlt
  set u1 := bestAltOf x v1
  set u2 := bestAltOf x v2
  have hs1 := isMax'_iff.1 (bestAlt_spec hx hv1)
  have hs2 := isMax'_iff.1 (bestAlt_spec hx hv2)
  have hu2I : u2 ∈ Icc 0 v1 := ⟨hs2.1.1, hlt.le.trans hs1.1.2⟩
  have hstrict := bestAlt_strict hx hv1 hu2I hlt.ne
  have hu1I : u1 ∈ Icc 0 v2 := ⟨hs1.1.1, hs1.1.2.trans h12⟩
  have hweak := hs2.2 u1 hu1I
  have hxm := x_mono hx ⟨hs2.1.1, hs2.1.2.trans hv2.2⟩ ⟨hs1.1.1, hs1.1.2.trans hv1.2⟩ hlt.le
  nlinarith

end DIP3

open DIP3 in
theorem solution (x : ℝ → ℝ) (vh : ℝ) (hx : DeferredInspection.SingleAgent.IsSCD x vh) :
    (∀ v ∈ Icc (0 : ℝ) 1,
      ∃! u, u ∈ Icc 0 v ∧
        IsMinOn (fun w => v * (x v - x w) + w) (Icc 0 v) u) ∧
    MonotoneOn (DeferredInspection.SingleAgent.bestAltOf x) (Icc 0 1) ∧
    ∃ vl ∈ Icc (0 : ℝ) 1,
      (∀ v ∈ Icc 0 vl, DeferredInspection.SingleAgent.bestAltOf x v = 0) ∧
      StrictMonoOn (DeferredInspection.SingleAgent.bestAltOf x)
        {v | vl ≤ v ∧ v ≤ 1 ∧ DeferredInspection.SingleAgent.bestAltOf x v < vh} := by
  refine ⟨?_, bestAlt_mono hx, ?_⟩
  · intro v hv
    obtain ⟨u, hu⟩ := exists_max hx hv
    exact ⟨u, hu, fun u' hu' => max_unique hx hv hu' hu⟩
  -- the threshold `vl = sup {v : b(v) = 0}`
  set Z := {v | v ∈ Icc (0:ℝ) 1 ∧ bestAltOf x v = 0} with hZ
  have h0Z : (0:ℝ) ∈ Z := by
    refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
    have := (bestAlt_spec hx (v := 0) ⟨le_rfl, zero_le_one⟩).1
    exact le_antisymm this.2 this.1
  have hZne : Z.Nonempty := ⟨0, h0Z⟩
  have hZbdd : BddAbove Z := ⟨1, fun z hz => hz.1.2⟩
  set vl := sSup Z with hvl
  have hvl0 : 0 ≤ vl := le_csSup hZbdd h0Z
  have hvl1 : vl ≤ 1 := csSup_le hZne (fun z hz => hz.1.2)
  have hvlI : vl ∈ Icc (0:ℝ) 1 := ⟨hvl0, hvl1⟩
  -- for `z ∈ Z`, `z x(w) - w ≤ 0` on `[0,1]`
  have hZle : ∀ z ∈ Z, ∀ w ∈ Icc (0:ℝ) 1, z * x w - w ≤ 0 := by
    intro z hz w hw
    have hs := isMax'_iff.1 (bestAlt_spec hx hz.1)
    rw [hz.2, hx.2.2.2.2.1] at hs
    rcases le_or_gt w z with hwz | hwz
    · have := hs.2 w ⟨hw.1, hwz⟩; simpa using this
    · have := x_le_one hx hw
      nlinarith [hz.1.1]
  have hbvl : bestAltOf x vl = 0 := by
    apply (max_unique hx hvlI (bestAlt_spec hx hvlI) _).trans rfl
    rw [isMax'_iff]
    refine ⟨⟨le_rfl, hvl0⟩, fun w hw => ?_⟩
    rw [hx.2.2.2.2.1]
    simp only [mul_zero, sub_zero]
    have hwI : w ∈ Icc (0:ℝ) 1 := ⟨hw.1, hw.2.trans hvl1⟩
    apply le_of_forall_pos_lt_add
    intro ε hε
    obtain ⟨z, hz, hzlt⟩ := exists_lt_of_lt_csSup hZne (show vl - ε < vl by linarith)
    have h1 := hZle z hz w hwI
    have h2 := x_le_one hx hwI
    have h3 : z ≤ vl := le_csSup hZbdd hz
    have h4 := (hx.1 w hwI).1
    nlinarith
  refine ⟨vl, hvlI, ?_, ?_⟩
  · intro v hv
    have hvI : v ∈ Icc (0:ℝ) 1 := ⟨hv.1, hv.2.trans hvl1⟩
    have := bestAlt_mono hx hvI hvlI hv.2
    rw [hbvl] at this
    exact le_antisymm this (bestAlt_spec hx hvI).1.1
  · intro v1 hv1 v2 hv2 h12
    have hv1I : v1 ∈ Icc (0:ℝ) 1 := ⟨hvl0.trans hv1.1, hv1.2.1⟩
    have hv2I : v2 ∈ Icc (0:ℝ) 1 := ⟨hvl0.trans hv2.1, hv2.2.1⟩
    rcases (bestAlt_mono hx hv1I hv2I h12.le).lt_or_eq with h | heq
    · exact h
    exfalso
    set u := bestAltOf x v1 with hu
    have hs1 := isMax'_iff.1 (bestAlt_spec hx hv1I)
    have hs2 := isMax'_iff.1 (bestAlt_spec hx hv2I)
    rw [← heq] at hs2
    have hupos : 0 < u := by
      rcases hs1.1.1.lt_or_eq with h | h
      · exact h
      · exfalso
        have hv2Z : v2 ∈ Z := ⟨hv2I, heq.symm.trans h.symm⟩
        have := le_csSup hZbdd hv2Z
        linarith [hv1.1]
    have huvh : u < vh := hv1.2.2
    have hv1pos : 0 < v1 := hupos.trans_le hs1.1.2
    -- derivative of `x` at `u`
    have hdiff : DifferentiableAt ℝ x u :=
      (hx.2.2.2.1 u ⟨hupos.le, huvh.le⟩).differentiableAt (Icc_mem_nhds hupos huvh)
    have hd := hdiff.hasDerivAt
    have hsl := hasDerivAt_iff_tendsto_slope.1 hd
    -- right side, from `v2`
    have hR : deriv x u ≤ 1 / v2 := by
      have ht : Tendsto (slope x u) (𝓝[>] u) (𝓝 (deriv x u)) :=
        hsl.mono_left (nhdsWithin_mono _ (fun w hw => ne_of_gt hw))
      apply le_of_tendsto ht
      filter_upwards [Ioo_mem_nhdsGT (lt_min (hs1.1.2.trans_lt h12) huvh)] with w hw
      have hwI : w ∈ Icc 0 v2 := ⟨hupos.le.trans hw.1.le, hw.2.le.trans (min_le_left _ _)⟩
      have := hs2.2 w hwI
      rw [slope_def_field, div_le_div_iff₀ (by linarith [hw.1]) (by linarith [hv1pos])]
      nlinarith
    -- left side, from `v1`
    have hL : 1 / v1 ≤ deriv x u := by
      have ht : Tendsto (slope x u) (𝓝[<] u) (𝓝 (deriv x u)) :=
        hsl.mono_left (nhdsWithin_mono _ (fun w hw => ne_of_lt hw))
      apply ge_of_tendsto ht
      filter_upwards [Ioo_mem_nhdsLT hupos] with w hw
      have hwI : w ∈ Icc 0 v1 := ⟨hw.1.le, hw.2.le.trans hs1.1.2⟩
      have := hs1.2 w hwI
      rw [slope_def_field]
      have hneg : w - u < 0 := by linarith [hw.2]
      rw [le_div_iff_of_neg hneg]
      have e : 1 / v1 * (w - u) = (w - u) / v1 := by ring
      rw [e, le_div_iff₀ hv1pos]
      linarith
    have : 1 / v2 < 1 / v1 := one_div_lt_one_div_of_lt hv1pos h12
    linarith
