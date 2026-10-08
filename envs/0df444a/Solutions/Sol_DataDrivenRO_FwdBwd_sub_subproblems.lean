-- Prove2me | solution 1 for DataDrivenRO.FwdBwd.sub_subproblems
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T11:31:30.333373+00:00
-- url     : https://prove2.me/submissions/93a85e2b-7afc-4a5a-852f-e0ac951c27d6

import Mathlib
import Definitions.Def_DataDrivenRO_FwdBwd_Setting

lemma p1d0472fc_quad (w s lam : ℝ) (hs : 0 < s) (hlam : 0 < lam) (hw : 0 ≤ w) :
    IsGreatest ((fun y => w * y - lam * (y ^ 2 / (2 * s ^ 2))) '' Set.Ici 0)
      (w ^ 2 * s ^ 2 / (2 * lam)) := by
  have hs2 : 0 < s ^ 2 := by positivity
  have key : ∀ y : ℝ, w * y - lam * (y ^ 2 / (2 * s ^ 2))
      = w ^ 2 * s ^ 2 / (2 * lam) - (lam * y - w * s ^ 2) ^ 2 / (2 * lam * s ^ 2) := by
    intro y
    field_simp
    ring
  refine ⟨⟨w * s ^ 2 / lam, ?_, ?_⟩, ?_⟩
  · show 0 ≤ w * s ^ 2 / lam
    positivity
  · show w * (w * s ^ 2 / lam) - lam * ((w * s ^ 2 / lam) ^ 2 / (2 * s ^ 2))
        = w ^ 2 * s ^ 2 / (2 * lam)
    rw [key]
    have : lam * (w * s ^ 2 / lam) - w * s ^ 2 = 0 := by field_simp; ring
    rw [this]; simp
  · rintro _ ⟨y, _, rfl⟩
    show w * y - lam * (y ^ 2 / (2 * s ^ 2)) ≤ w ^ 2 * s ^ 2 / (2 * lam)
    rw [key]
    have : 0 ≤ (lam * y - w * s ^ 2) ^ 2 / (2 * lam * s ^ 2) := by positivity
    linarith

lemma p1d0472fc_zero (w s lam : ℝ) (hs : 0 < s) (hlam : 0 < lam) (hw : w ≤ 0) :
    IsGreatest ((fun y => w * y - lam * (y ^ 2 / (2 * s ^ 2))) '' Set.Ici 0) 0 := by
  refine ⟨⟨0, Set.mem_Ici.mpr (le_refl 0), by simp⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have hy : (0:ℝ) ≤ y := hy
  show w * y - lam * (y ^ 2 / (2 * s ^ 2)) ≤ 0
  have h1 : w * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hw hy
  have h2 : 0 ≤ lam * (y ^ 2 / (2 * s ^ 2)) := by positivity
  linarith

theorem solution (mb mf σf σb lam v : ℝ) (hm : mb ≤ mf) (hσf : 0 < σf) (hσb : 0 < σb)
    (hlam : 0 < lam) :
    IsGreatest ((fun y => v * y) '' Set.Icc mb mf) (if 0 ≤ v then mf * v else mb * v) ∧
    IsGreatest ((fun y => v * y - lam * (y ^ 2 / (2 * σf ^ 2))) '' Set.Ici 0)
      (if 0 ≤ v then v ^ 2 * σf ^ 2 / (2 * lam) else 0) ∧
    IsGreatest ((fun y => -v * y - lam * (y ^ 2 / (2 * σb ^ 2))) '' Set.Ici 0)
      (if v ≤ 0 then v ^ 2 * σb ^ 2 / (2 * lam) else 0) := by
  refine ⟨?_, ?_, ?_⟩
  · split_ifs with hv
    · refine ⟨⟨mf, ⟨hm, le_refl _⟩, by simp [mul_comm]⟩, ?_⟩
      rintro _ ⟨y, ⟨h1, h2⟩, rfl⟩
      show v * y ≤ mf * v
      nlinarith
    · refine ⟨⟨mb, ⟨le_refl _, hm⟩, by simp [mul_comm]⟩, ?_⟩
      rintro _ ⟨y, ⟨h1, h2⟩, rfl⟩
      show v * y ≤ mb * v
      have hv' : v < 0 := lt_of_not_ge hv
      nlinarith
  · split_ifs with hv
    · exact p1d0472fc_quad v σf lam hσf hlam hv
    · exact p1d0472fc_zero v σf lam hσf hlam (by linarith)
  · split_ifs with hv
    · have := p1d0472fc_quad (-v) σb lam hσb hlam (by linarith)
      simpa [neg_sq] using this
    · exact p1d0472fc_zero (-v) σb lam hσb hlam (by linarith)
