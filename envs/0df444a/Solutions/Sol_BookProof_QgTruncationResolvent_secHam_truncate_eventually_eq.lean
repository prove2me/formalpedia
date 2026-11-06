-- Prove2me | solution 1 for BookProof.QgTruncationResolvent.secHam_truncate_eventually_eq
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:32:17.164783+00:00
-- url     : https://prove2.me/submissions/4ff696e6-f511-4f60-8a8f-69cc651f6cd6

import Definitions.Def_ChapterQgTruncationResolvent

open Filter
open BookProof.ScalaronFiberFL
open BookProof.ScalaronFiberFL.WallPot
open BookProof.ScalaronEsa
open BookProof.QgOuterFockCoreFL
open BookProof.ScalaronOuterFockFL
open BookProof.QgTruncationResolvent

noncomputable section

variable {ι : Type*}
variable (W : WallPot) (Q : QgModeData ι)

theorem solution (Λ : ℕ → Set ι)
    (hexh : ∀ F : Finset ι, ∀ᶠ n in atTop, ∀ a ∈ F, a ∈ Λ n) (x : secCore (ι := ι)) :
    ∀ᶠ n in atTop, secHam W (truncModes Q (Λ n)) x = secHam W Q x := by
  classical
  obtain ⟨P, hP1, hP2⟩ := exists_band Q x
  filter_upwards [hexh P] with n hn
  have hP2' : ∀ a, a ∉ P → ∀ b ∈ (truncModes Q (Λ n)).nbr a,
      (x : Sec ι) b = 0 := by
    simpa only [truncModes_nbr] using hP2
  apply lp.ext
  funext a
  by_cases ha : a ∈ P
  · rw [secHam_apply, secHam_apply]
    simp only [truncModes_sig, truncModes_nbr]
    have hA : (∑ b ∈ Q.nbr a,
          (truncModes Q (Λ n)).A a b • ((fibOf x b : ccDomain ℝ) : L2R)) =
        ∑ b ∈ Q.nbr a, Q.A a b • ((fibOf x b : ccDomain ℝ) : L2R) := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hbP : b ∈ P
      · simp only [truncModes, hn a ha, hn b hbP, and_self, if_true]
      · rw [fibOf_eq_zero (hP1 b hbP)]
        simp
    have hB : (∑ b ∈ Q.nbr a, (truncModes Q (Λ n)).B a b • xCc (fibOf x b)) =
        ∑ b ∈ Q.nbr a, Q.B a b • xCc (fibOf x b) := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hbP : b ∈ P
      · simp only [truncModes, hn a ha, hn b hbP, and_self, if_true]
      · rw [fibOf_eq_zero (hP1 b hbP)]
        simp
    rw [hA, hB]
  · rw [secHam_supp W (truncModes Q (Λ n)) hP1 hP2' a ha,
      secHam_supp W Q hP1 hP2 a ha]
