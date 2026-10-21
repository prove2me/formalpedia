-- Prove2me | solution 1 for EquiSegment.Multivalued.lemma_2_2_b
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:47:22.520745+00:00
-- url     : https://prove2.me/submissions/c56b8efb-d13b-48d3-aed8-126b3ac2698f

import Mathlib
import Definitions.Def_EquiSegment_Multivalued_Setting

set_option autoImplicit false
open EquiSegment.Multivalued

theorem solution (φ : ℝ × ℝ → ℝ → ℝ) (hφ : IsRep φ) :
    IsNice (zeroSet φ) := by
  obtain ⟨hcont, hbt⟩ := hφ
  have hSegc : IsClosed Seg := by
    show IsClosed ({s : ℝ × ℝ | 0 ≤ s.1} ∩ ({s : ℝ × ℝ | s.1 ≤ s.2} ∩ {s : ℝ × ℝ | s.2 ≤ 1}))
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst continuous_snd).inter
        (isClosed_le continuous_snd continuous_const))
  have hSegk : IsCompact Seg := by
    apply IsCompact.of_isClosed_subset ((isCompact_Icc (a := (0:ℝ)) (b := 1)).prod
      (isCompact_Icc (a := (0:ℝ)) (b := 1))) hSegc
    intro s hs
    exact ⟨⟨hs.1, le_trans hs.2.1 hs.2.2⟩, ⟨le_trans hs.1 hs.2.1, hs.2.2⟩⟩
  have hCylk : IsCompact Cyl := hSegk.prod isCompact_Icc
  have hCylc : IsClosed Cyl := hSegc.prod isClosed_Icc
  have hZeq : zeroSet φ = Cyl ∩ (fun x : (ℝ × ℝ) × ℝ => φ x.1 x.2) ⁻¹' {0} := by
    ext x
    simp [zeroSet]
  have hZcl : IsClosed (Cyl ∩ (fun x : (ℝ × ℝ) × ℝ => φ x.1 x.2) ⁻¹' {0}) :=
    hcont.preimage_isClosed_of_isClosed hCylc isClosed_singleton
  have hZk : IsCompact (zeroSet φ) := by
    rw [hZeq]; exact hCylk.of_isClosed_subset hZcl Set.inter_subset_left
  have hBot : Bottom ⊆ Cyl \ zeroSet φ := by
    rintro ⟨s, y⟩ ⟨hs, hy⟩
    have hy' : y = -1 := hy
    subst hy'
    refine ⟨⟨hs, by norm_num, by norm_num⟩, fun h => ?_⟩
    have := h.2
    have h2 := (hbt s hs).1
    simp only at this
    linarith
  have hTop : EquiSegment.Multivalued.Top ⊆ Cyl \ zeroSet φ := by
    rintro ⟨s, y⟩ ⟨hs, hy⟩
    have hy' : y = 1 := hy
    subst hy'
    refine ⟨⟨hs, by norm_num, by norm_num⟩, fun h => ?_⟩
    have := h.2
    have h2 := (hbt s hs).2
    simp only at this
    linarith
  refine ⟨hZk, ?_, hBot, hTop, ?_⟩
  · rintro ⟨s, y⟩ ⟨⟨hs, hy⟩, h0⟩
    have hy : y ∈ Set.Icc (-1 : ℝ) 1 := hy
    refine ⟨hs, ?_, ?_⟩
    · rcases hy.1.lt_or_eq with h | h
      · exact h
      · exfalso
        have h2 := (hbt s hs).1
        have h0' : φ s y = 0 := h0
        rw [← h] at h0'
        linarith
    · rcases hy.2.lt_or_eq with h | h
      · exact h
      · exfalso
        have h2 := (hbt s hs).2
        have h0' : φ s y = 0 := h0
        rw [h] at h0'
        linarith
  · rintro ⟨s, y⟩ ha ⟨t, z⟩ hb hbc
    have hC := isPreconnected_connectedComponentIn (F := Cyl \ zeroSet φ) (x := (s, y))
    have hsub := connectedComponentIn_subset (Cyl \ zeroSet φ) (s, y)
    have haC : (s, y) ∈ connectedComponentIn (Cyl \ zeroSet φ) (s, y) :=
      mem_connectedComponentIn (hBot ha)
    have hfc : ContinuousOn (fun x : (ℝ × ℝ) × ℝ => φ x.1 x.2)
        (connectedComponentIn (Cyl \ zeroSet φ) (s, y)) :=
      hcont.mono (fun x hx => (hsub hx).1)
    have hy : y = -1 := ha.2
    have hz : z = 1 := hb.2
    have hneg : φ s y < 0 := by rw [hy]; exact (hbt s ha.1).1
    have hpos : 0 < φ t z := by rw [hz]; exact (hbt t hb.1).2
    have hiv := hC.intermediate_value haC hbc hfc
    obtain ⟨x, hxC, hx0⟩ := hiv (show (0 : ℝ) ∈ Set.Icc (φ s y) (φ t z) from ⟨hneg.le, hpos.le⟩)
    have hx := hsub hxC
    exact hx.2 ⟨hx.1, hx0⟩
