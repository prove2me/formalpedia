-- Prove2me | solution 1 for DelaunayStretch.theorem_5_1_explicit_function
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T03:07:18.506272+00:00
-- url     : https://prove2.me/submissions/ed2d0b63-3b52-42f6-97b1-b1524cc1f557
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DelaunayStretch_lemma_5_6_regularity
import Theorems.Thm_DelaunayStretch_proposition_5_11_H1_H3
import Theorems.Thm_DelaunayStretch_proposition_6_7_H4

open DelaunayStretch

theorem hstarV_rev (i j : Fin 12) (l : Fin 35) :
    hstarV (Fin.rev i) (Fin.rev j) l = -hstarV i j l := by
  have hi := i.isLt; have hj := j.isLt
  have ri : ((Fin.rev i : Fin 12) : ℕ) = 11 - i := by simp [Fin.val_rev]
  have rj : ((Fin.rev j : Fin 12) : ℕ) = 11 - j := by simp [Fin.val_rev]
  unfold hstarV
  rw [ri, rj]
  by_cases h : (i : ℕ) ≤ 5
  · rw [if_neg (show ¬ (11 - (i : ℕ) ≤ 5) by omega), if_pos h,
      show 11 - (11 - (i : ℕ)) = i by omega, show 11 - (11 - (j : ℕ)) = j by omega]
  · rw [if_pos (show 11 - (i : ℕ) ≤ 5 by omega), if_neg h, neg_neg]

theorem hstarR_rev (i j : Fin 6) (l : Fin 35) :
    hstarR (Fin.rev i) (Fin.rev j) l = hstarR i j l := by
  have hi := i.isLt; have hj := j.isLt
  have ri : ((Fin.rev i : Fin 6) : ℕ) = 5 - i := by simp [Fin.val_rev]
  have rj : ((Fin.rev j : Fin 6) : ℕ) = 5 - j := by simp [Fin.val_rev]
  unfold hstarR
  rw [ri, rj]
  by_cases h : 6 * (i : ℕ) + j ≤ 17
  · rw [if_neg (show ¬ (6 * (5 - (i : ℕ)) + (5 - (j : ℕ)) ≤ 17) by omega), if_pos h,
      show 5 - (5 - (i : ℕ)) = i by omega, show 5 - (5 - (j : ℕ)) = j by omega]
  · rw [if_pos (show 6 * (5 - (i : ℕ)) + (5 - (j : ℕ)) ≤ 17 by omega), if_neg h]

theorem hstar_coeff_conditions : FamilyCoeffConditions hstarV hstarR hstarB hstarD := by
  refine ⟨hstarV_rev, hstarR_rev, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem reflect1_mem_Sigma (z : R4) (hz : z ∈ SigmaSet) : reflect1 z ∈ SigmaSet := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hz
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show |-z.1 - -z.2.1| < z.2.2.1
    rw [show -z.1 - -z.2.1 = -(z.1 - z.2.1) by ring, abs_neg]; exact h1
  · show z.2.2.1 < Real.pi - |-z.1 + -z.2.1|
    rw [show -z.1 + -z.2.1 = -(z.1 + z.2.1) by ring, abs_neg]; exact h2
  · show |-z.2.2.2 - -z.2.1| ≤ Real.sin z.2.2.1
    rw [show -z.2.2.2 - -z.2.1 = -(z.2.2.2 - z.2.1) by ring, abs_neg]; exact h3

theorem solution :
    ∃ H : R4 → ℝ, InFamilyH H ∧ SatisfiesH0toH4 (159485994 / 100000000 : ℝ) H := by
  have hc := hstar_coeff_conditions
  obtain ⟨P, h0, hinc⟩ := lemma_5_6_regularity hstarV hstarR hstarB hstarD hc
  obtain ⟨h1, h3, h2p⟩ := proposition_5_11_H1_H3
  have h4p := proposition_6_7_H4
  refine ⟨Hstar, ⟨hstarV, hstarR, hstarB, hstarD, hc, fun z _ => rfl⟩, P, h0, h1, ?_, h3, ?_⟩
  · intro z hz g hg
    rcases hinc z hz g hg with hp | ⟨hp, -⟩
    · exact h2p z g hp
    · have := h2p _ _ hp
      simpa [abs_neg] using this
  · intro z hz g hg
    rcases hinc z hz.1 g hg with hp | ⟨hp, hres⟩
    · exact h4p z hz g hp
    · change pencilResidual _ (familyH hstarV hstarR hstarB hstarD) g z ≤ 0
      rw [← hres]
      exact h4p _ (reflect1_mem_Sigma z hz) _ hp
