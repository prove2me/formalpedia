-- Prove2me | solution 1 for BiconvexProg.BranchBound.vex_mul_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:35:12.552534+00:00
-- url     : https://prove2.me/submissions/4a13c588-a352-48cf-9313-a27d50b1186c

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_convexEnvelope

namespace BiconvexProg.BranchBound

lemma aux_vmr_jensen3 {Ω : Set (ℝ × ℝ)} {g : ℝ × ℝ → ℝ} (hg : ConvexOn ℝ Ω g)
    (a b c : ℝ) (u v w : ℝ × ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a + b + c = 1) (hu : u ∈ Ω) (hv : v ∈ Ω) (hw : w ∈ Ω) :
    g (a • u + b • v + c • w) ≤ a * g u + b * g v + c * g w := by
  have h := hg.map_sum_le (t := Finset.univ) (w := ![a, b, c]) (p := ![u, v, w])
    (by intro i _; fin_cases i <;> simp [ha, hb, hc])
    (by simp [Fin.sum_univ_three, habc])
    (by intro i _; fin_cases i <;> simp [hu, hv, hw])
  simpa [Fin.sum_univ_three, add_assoc] using h

lemma aux_vmr_convex (l L m M : ℝ) :
    ConvexOn ℝ (Set.Icc l L ×ˢ Set.Icc m M)
      (fun q : ℝ × ℝ => max (m * q.1 + l * q.2 - l * m) (M * q.1 + L * q.2 - L * M)) := by
  refine ⟨(convex_Icc l L).prod (convex_Icc m M), ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have e1 : m * x.1 + l * x.2 - l * m ≤
      max (m * x.1 + l * x.2 - l * m) (M * x.1 + L * x.2 - L * M) := le_max_left _ _
  have e2 : M * x.1 + L * x.2 - L * M ≤
      max (m * x.1 + l * x.2 - l * m) (M * x.1 + L * x.2 - L * M) := le_max_right _ _
  have f1 : m * y.1 + l * y.2 - l * m ≤
      max (m * y.1 + l * y.2 - l * m) (M * y.1 + L * y.2 - L * M) := le_max_left _ _
  have f2 : M * y.1 + L * y.2 - L * M ≤
      max (m * y.1 + l * y.2 - l * m) (M * y.1 + L * y.2 - L * M) := le_max_right _ _
  apply max_le
  · have := mul_le_mul_of_nonneg_left e1 ha
    have := mul_le_mul_of_nonneg_left f1 hb
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith
  · have := mul_le_mul_of_nonneg_left e2 ha
    have := mul_le_mul_of_nonneg_left f2 hb
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith

end BiconvexProg.BranchBound

open BiconvexProg.BranchBound

theorem solution (l L m M : ℝ) (p : ℝ × ℝ)
    (hp : p ∈ Set.Icc l L ×ˢ Set.Icc m M) :
    convexEnvelope (Set.Icc l L ×ˢ Set.Icc m M) (fun q : ℝ × ℝ => q.1 * q.2) p =
      max (m * p.1 + l * p.2 - l * m) (M * p.1 + L * p.2 - L * M) := by
  unfold convexEnvelope
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨fun q => max (m * q.1 + l * q.2 - l * m) (M * q.1 + L * q.2 - L * M),
      aux_vmr_convex l L m M, ?_, rfl⟩
    intro w hw
    simp only [Set.mem_prod, Set.mem_Icc] at hw
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hw
    apply max_le
    · nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h3)]
    · nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h4)]
  · rintro r ⟨g, hg, hle, rfl⟩
    have hpΩ := hp
    obtain ⟨x, y⟩ := p
    simp only [Set.mem_prod, Set.mem_Icc] at hp
    obtain ⟨⟨hx1, hx2⟩, hy1, hy2⟩ := hp
    simp only
    have hgp := hle _ hpΩ
    simp only at hgp
    rcases eq_or_lt_of_le (le_trans hx1 hx2) with hlL | hlL
    · -- degenerate: l = L
      have hx : x = l := le_antisymm (hlL ▸ hx2) hx1
      subst hx
      apply le_max_of_le_left
      linarith
    rcases eq_or_lt_of_le (le_trans hy1 hy2) with hmM | hmM
    · have hy : y = m := le_antisymm (hmM ▸ hy2) hy1
      subst hy
      apply le_max_of_le_left
      linarith
    have hLl : 0 < L - l := sub_pos.2 hlL
    have hMm : 0 < M - m := sub_pos.2 hmM
    set c := (x - l) / (L - l) with hc_def
    set b := (y - m) / (M - m) with hb_def
    have hc' : c * (L - l) = x - l := div_mul_cancel₀ _ hLl.ne'
    have hb' : b * (M - m) = y - m := div_mul_cancel₀ _ hMm.ne'
    have hc0 : 0 ≤ c := div_nonneg (by linarith) hLl.le
    have hb0 : 0 ≤ b := div_nonneg (by linarith) hMm.le
    have hc1 : c ≤ 1 := (div_le_one hLl).2 (by linarith)
    have hb1 : b ≤ 1 := (div_le_one hMm).2 (by linarith)
    have mem : ∀ u v : ℝ, l ≤ u → u ≤ L → m ≤ v → v ≤ M →
        ((u, v) : ℝ × ℝ) ∈ Set.Icc l L ×ˢ Set.Icc m M := by
      intro u v h1 h2 h3 h4
      simp only [Set.mem_prod, Set.mem_Icc]
      exact ⟨⟨h1, h2⟩, h3, h4⟩
    have hlm := hle (l, m) (mem l m le_rfl hlL.le le_rfl hmM.le)
    have hlM := hle (l, M) (mem l M le_rfl hlL.le hmM.le le_rfl)
    have hLm := hle (L, m) (mem L m hlL.le le_rfl le_rfl hmM.le)
    have hLM := hle (L, M) (mem L M hlL.le le_rfl hmM.le le_rfl)
    simp only at hlm hlM hLm hLM
    rcases le_or_gt (b + c) 1 with hbc | hbc
    · -- lower-left triangle
      have hpt : ((x, y) : ℝ × ℝ) =
          (1 - b - c) • ((l, m) : ℝ × ℝ) + b • ((l, M) : ℝ × ℝ) + c • ((L, m) : ℝ × ℝ) := by
        ext
        · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
          linear_combination -hc'
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
          linear_combination -hb'
      have hj := aux_vmr_jensen3 hg (1 - b - c) b c (l, m) (l, M) (L, m)
        (by linarith) hb0 hc0 (by ring)
        (mem l m le_rfl hlL.le le_rfl hmM.le) (mem l M le_rfl hlL.le hmM.le le_rfl)
        (mem L m hlL.le le_rfl le_rfl hmM.le)
      rw [← hpt] at hj
      have t1 := mul_le_mul_of_nonneg_left hlm (show (0:ℝ) ≤ 1 - b - c by linarith)
      have t2 := mul_le_mul_of_nonneg_left hlM hb0
      have t3 := mul_le_mul_of_nonneg_left hLm hc0
      have key : (1 - b - c) * (l * m) + b * (l * M) + c * (L * m) =
          m * x + l * y - l * m := by
        linear_combination l * hb' + m * hc'
      apply le_max_of_le_left
      linarith
    · -- upper-right triangle
      have hpt : ((x, y) : ℝ × ℝ) =
          (b + c - 1) • ((L, M) : ℝ × ℝ) + (1 - c) • ((l, M) : ℝ × ℝ) +
            (1 - b) • ((L, m) : ℝ × ℝ) := by
        ext
        · simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
          linear_combination -hc'
        · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
          linear_combination -hb'
      have hj := aux_vmr_jensen3 hg (b + c - 1) (1 - c) (1 - b) (L, M) (l, M) (L, m)
        (by linarith) (by linarith) (by linarith) (by ring)
        (mem L M hlL.le le_rfl hmM.le le_rfl) (mem l M le_rfl hlL.le hmM.le le_rfl)
        (mem L m hlL.le le_rfl le_rfl hmM.le)
      rw [← hpt] at hj
      have t1 := mul_le_mul_of_nonneg_left hLM (show (0:ℝ) ≤ b + c - 1 by linarith)
      have t2 := mul_le_mul_of_nonneg_left hlM (show (0:ℝ) ≤ 1 - c by linarith)
      have t3 := mul_le_mul_of_nonneg_left hLm (show (0:ℝ) ≤ 1 - b by linarith)
      have key : (b + c - 1) * (L * M) + (1 - c) * (l * M) + (1 - b) * (L * m) =
          M * x + L * y - L * M := by
        linear_combination M * hc' + L * hb'
      apply le_max_of_le_right
      linarith
