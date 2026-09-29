-- Prove2me | solution 1 for BookProof.SirkGapTable.richardson_error
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:15:59.209506+00:00
-- url     : https://prove2.me/submissions/8bf35c08-9038-4564-8f86-08c18680c27c

import Definitions.Def_ChapterSirkGapTable
-- Adapted from Leonardo Pedro, timepiece commit 61595bc (Apache-2.0).
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSirkGapTable.lean
open BookProof.SirkGapTable Real
set_option autoImplicit false
private theorem ritzX_one_lt_ratio {l1 l2 p : ℝ} (hl1 : 0 < l1) (hl : l1 < l2) (hp : 0 < p) :
    1 < (l2 / l1) ^ p := by
  have h1 : 1 < l2 / l1 := (one_lt_div hl1).2 hl
  exact (one_lt_rpow_iff (by linarith)).2 (Or.inl ⟨h1, hp⟩)

private theorem ritzX_richardson_exact {D C l1 l2 p : ℝ} (hl1 : 0 < l1) (hl : l1 < l2) (hp : 0 < p) :
    richardson (D + C * l1 ^ (-p)) (D + C * l2 ^ (-p)) l1 l2 p = D := by
  have hl2 : 0 < l2 := lt_trans hl1 hl
  set A := l1 ^ p with hA
  set B := l2 ^ p with hB
  have hApos : 0 < A := rpow_pos_of_pos hl1 p
  have hBpos : 0 < B := rpow_pos_of_pos hl2 p
  have hAB : A < B := by
    simpa [hA, hB] using rpow_lt_rpow hl1.le hl hp
  have h1 : l1 ^ (-p) = A⁻¹ := by rw [hA, rpow_neg hl1.le]
  have h2 : l2 ^ (-p) = B⁻¹ := by rw [hB, rpow_neg hl2.le]
  have hratio : (l2 / l1) ^ p = B / A := by
    rw [div_rpow hl2.le hl1.le, hA, hB]
  rw [richardson, h1, h2, hratio]
  have hne : B - A ≠ 0 := by linarith
  field_simp
  ring

theorem solution {D C l1 l2 p d1 d2 eps : ℝ}
    (hl1 : 0 < l1) (hl : l1 < l2) (hp : 0 < p)
    (h1 : |d1 - (D + C * l1 ^ (-p))| ≤ eps) (h2 : |d2 - (D + C * l2 ^ (-p))| ≤ eps) :
    |richardson d1 d2 l1 l2 p - D| ≤ eps * (1 + 2 / ((l2 / l1) ^ p - 1)) := by
  have hX : 1 < (l2 / l1) ^ p := ritzX_one_lt_ratio hl1 hl hp
  set X := (l2 / l1) ^ p - 1 with hXdef
  have hXpos : 0 < X := by simp only [hXdef]; linarith
  have hexact : richardson (D + C * l1 ^ (-p)) (D + C * l2 ^ (-p)) l1 l2 p = D :=
    ritzX_richardson_exact hl1 hl hp
  set e1 := d1 - (D + C * l1 ^ (-p)) with he1
  set e2 := d2 - (D + C * l2 ^ (-p)) with he2
  have hdiff : richardson d1 d2 l1 l2 p - D = e2 + (e2 - e1) / X := by
    have : richardson d1 d2 l1 l2 p
        - richardson (D + C * l1 ^ (-p)) (D + C * l2 ^ (-p)) l1 l2 p
        = e2 + (e2 - e1) / X := by
      simp only [richardson, he1, he2, hXdef]
      field_simp
      ring
    rw [← hexact]
    exact this
  rw [hdiff]
  have hb1 : |e1| ≤ eps := h1
  have hb2 : |e2| ≤ eps := h2
  have hsplit : |e2 + (e2 - e1) / X| ≤ |e2| + (|e2| + |e1|) / X := by
    calc |e2 + (e2 - e1) / X| ≤ |e2| + |(e2 - e1) / X| := abs_add_le _ _
      _ = |e2| + |e2 - e1| / X := by rw [abs_div, abs_of_pos hXpos]
      _ ≤ |e2| + (|e2| + |e1|) / X := by
          gcongr
          exact abs_sub _ _
  have hmono : |e2| + (|e2| + |e1|) / X ≤ eps + (eps + eps) / X := by gcongr
  have : eps + (eps + eps) / X = eps * (1 + 2 / X) := by field_simp; ring
  linarith [hsplit, hmono, this.le, this.ge]

#print axioms solution
