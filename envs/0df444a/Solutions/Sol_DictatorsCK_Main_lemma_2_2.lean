-- Prove2me | solution 1 for DictatorsCK.Main.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-13T14:42:00.134319+00:00
-- url     : https://prove2.me/submissions/3ec8cce7-deee-4c88-bd6b-37063621ce73

import Mathlib

open Filter
open scoped Topology

set_option autoImplicit false

/-- If `G b ≤ 0` and `G' ≥ 0` wherever `G > 0`, then `G ≤ 0` on `[a,b]`: otherwise, at the first
point `s` where `G` drops to `≤ 0`, the mean value theorem produces a point `c < s` with
`G c > 0` but `G' c < 0`. -/
theorem solution (a b : ℝ) (hab : a < b) (G : ℝ → ℝ) (hcont : ContinuousOn G (Set.Icc a b))
    (hdiff : DifferentiableOn ℝ G (Set.Ioo a b)) (hGb : G b ≤ 0)
    (hpos : ∀ x ∈ Set.Ioo a b, 0 < G x → 0 ≤ deriv G x) :
    ∀ x ∈ Set.Icc a b, G x ≤ 0 := by
  intro x₀ hx₀
  by_contra hx
  push Not at hx
  have hx₀b : x₀ ≤ b := hx₀.2
  set T : Set ℝ := {x | x ∈ Set.Icc x₀ b ∧ G x ≤ 0} with hTdef
  have hTne : T.Nonempty := ⟨b, ⟨⟨hx₀b, le_rfl⟩, hGb⟩⟩
  have hTbdd : BddBelow T := ⟨x₀, fun y hy => hy.1.1⟩
  set s : ℝ := sInf T with hsdef
  have hs_x0 : x₀ ≤ s := le_csInf hTne fun y hy => hy.1.1
  have hs_b : s ≤ b := csInf_le hTbdd ⟨⟨hx₀b, le_rfl⟩, hGb⟩
  have hGs : G s ≤ 0 := by
    by_contra hcon
    push Not at hcon
    have hsmem : s ∈ Set.Icc a b := ⟨le_trans hx₀.1 hs_x0, hs_b⟩
    have hev : ∀ᶠ y in 𝓝[Set.Icc a b] s, 0 < G y :=
      (hcont.continuousWithinAt hsmem).eventually (isOpen_Ioi.mem_nhds hcon)
    obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhdsWithin_iff.mp hev
    have hs_lt_b : s < b := by
      rcases lt_or_eq_of_le hs_b with h | h
      · exact h
      · exfalso
        have h1 : G s ≤ 0 := h ▸ hGb
        linarith
    set ε' : ℝ := min ε (b - s) with hε'def
    have hε'pos : 0 < ε' := lt_min hεpos (by linarith)
    have hε'le : ε' ≤ ε := min_le_left _ _
    have hε'b : ε' ≤ b - s := min_le_right _ _
    have hlt : s < s + ε' / 2 := by linarith
    obtain ⟨y, hyT, hylt⟩ := exists_lt_of_csInf_lt (b := s + ε' / 2) hTne (by
      rw [← hsdef]
      exact hlt)
    have hys : s ≤ y := csInf_le hTbdd hyT
    have hyltb : y < b := by linarith [hylt, hε'b, hε'pos]
    have hymem : y ∈ Set.Icc a b := ⟨le_trans hx₀.1 (le_trans hs_x0 hys), le_of_lt hyltb⟩
    have hdist : dist y s < ε := by
      rw [Real.dist_eq, abs_of_nonneg (by linarith : (0:ℝ) ≤ y - s)]
      have h2 : y - s < ε' / 2 := by linarith
      linarith [hε'le]
    exact not_lt_of_ge hyT.2 (hε ⟨hdist, hymem⟩)
  have hs_gt : x₀ < s := by
    rcases lt_or_eq_of_le hs_x0 with h | h
    · exact h
    · exfalso
      have : G x₀ ≤ 0 := h ▸ hGs
      linarith
  have hcont' : ContinuousOn G (Set.Icc x₀ s) :=
    hcont.mono (Set.Icc_subset_Icc hx₀.1 hs_b)
  have hdiff' : DifferentiableOn ℝ G (Set.Ioo x₀ s) :=
    hdiff.mono (Set.Ioo_subset_Ioo hx₀.1 hs_b)
  obtain ⟨c, hc_mem, hc_deriv⟩ := exists_deriv_eq_slope G hs_gt hcont' hdiff'
  have hc_ab : c ∈ Set.Ioo a b :=
    ⟨lt_of_le_of_lt hx₀.1 hc_mem.1, lt_of_lt_of_le hc_mem.2 hs_b⟩
  have hGc : 0 < G c := by
    by_contra hcon
    push Not at hcon
    have hcT : c ∈ T := ⟨⟨le_of_lt hc_mem.1, le_of_lt (lt_of_lt_of_le hc_mem.2 hs_b)⟩, hcon⟩
    have h1 : s ≤ c := csInf_le hTbdd hcT
    linarith [hc_mem.2]
  have hneg : deriv G c < 0 := by
    rw [hc_deriv]
    exact div_neg_of_neg_of_pos (by linarith) (by linarith)
  have hnonneg : 0 ≤ deriv G c := hpos c hc_ab hGc
  linarith
