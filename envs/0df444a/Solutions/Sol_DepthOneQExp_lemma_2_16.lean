-- Prove2me | solution 1 for DepthOneQExp.lemma_2_16
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T06:09:36.661502+00:00
-- url     : https://prove2.me/submissions/b0d004d2-bf0c-4471-bfce-70a8a3ac5c5d

import Mathlib
import Theorems.Thm_DepthOneQExp_hh09_lemma1

open scoped Matrix.Norms.L2Operator

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] (P A B : Matrix ι ι ℂ)
    (hP2 : P * P = P) (hPh : P.IsHermitian) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAn : ‖A‖ ≤ 1) (hBn : ‖B‖ ≤ 1) (εA εB : ℝ) (hεA : εA ∈ Set.Ioo (0 : ℝ) 1)
    (hεB : εB ∈ Set.Ioo (0 : ℝ) 1) (hPA : P * A = P) (hAP : A * P = P)
    (hA' : ‖(1 - P) * A * (1 - P)‖ ≤ 1 - εA) (hB' : ‖P * B * P‖ ≤ 1 - εB)
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    ‖(p : ℂ) • A + ((1 - p : ℝ) : ℂ) • B‖ ≤ 1 - εB / 12 * min (p * εA) (1 - p) :=
  DepthOneQExp.hh09_lemma1 P A B hP2 hPh hAn hBn εA εB ⟨hεA.1, hεA.2.le⟩ ⟨hεB.1, hεB.2.le⟩
    hPA hAP hA' hB' p hp
