-- Prove2me | solution 1 for AvgRewardPMD.SPMD.kl_uniform_le_log
-- status  : ACCEPTED   (prove)
-- author  : @frknbls
-- created : 2026-10-27T14:50:38.825404+00:00
-- url     : https://prove2.me/submissions/5fb4a217-c454-4fa7-a1b2-5e3fc95ff97e

import Definitions.Def_AvgRewardPMD_SPMD_Setting

namespace AvgRewardPMD.SPMD

open FoundationsML.ReinforcementLearning

theorem kl_uniform_le_log {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (ν : S → ℝ) (hν : ν ∈ stdSimplex ℝ S) (πstar : S → A → ℝ) (hπstar : IsPolicy πstar) :
    stationaryKL ν (fun _ _ => 1 / (Fintype.card A : ℝ)) πstar ≤ Real.log (Fintype.card A) := by
  have hkl : ∀ s, kl (πstar s) (fun _ => 1 / (Fintype.card A : ℝ)) ≤ Real.log (Fintype.card A) := by
    intro s
    obtain ⟨hnn, hsum⟩ := hπstar s
    have hA : (0 : ℝ) < Fintype.card A := by
      rcases isEmpty_or_nonempty A with h | h
      · simp at hsum
      · exact_mod_cast Fintype.card_pos
    have hle1 : ∀ a, πstar s a ≤ 1 := fun a => by
      rw [← hsum]
      exact Finset.single_le_sum (fun b _ => hnn b) (Finset.mem_univ a)
    have key : ∀ a, πstar s a * Real.log (πstar s a / (1 / (Fintype.card A : ℝ))) =
        πstar s a * Real.log (πstar s a) + πstar s a * Real.log (Fintype.card A) := by
      intro a
      rcases (hnn a).eq_or_lt with h | h
      · rw [← h]; simp
      · rw [one_div, div_inv_eq_mul, Real.log_mul h.ne' hA.ne', mul_add]
    unfold kl
    simp_rw [key]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul]
    have : ∑ a, πstar s a * Real.log (πstar s a) ≤ 0 :=
      Finset.sum_nonpos fun a _ => Real.mul_log_nonpos (hnn a) (hle1 a)
    linarith
  unfold stationaryKL
  calc ∑ s, ν s * kl (πstar s) (fun _ => 1 / (Fintype.card A : ℝ))
      ≤ ∑ s, ν s * Real.log (Fintype.card A) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hkl s) (hν.1 s)
    _ = Real.log (Fintype.card A) := by rw [← Finset.sum_mul, hν.2, one_mul]

end AvgRewardPMD.SPMD


-- Platform entry point: restates the target verbatim.
namespace AvgRewardPMD.SPMD

open FoundationsML.ReinforcementLearning

theorem _root_.solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    (ν : S → ℝ) (hν : ν ∈ stdSimplex ℝ S) (πstar : S → A → ℝ) (hπstar : IsPolicy πstar) :
    stationaryKL ν (fun _ _ => 1 / (Fintype.card A : ℝ)) πstar ≤ Real.log (Fintype.card A) := by
  apply @AvgRewardPMD.SPMD.kl_uniform_le_log <;> assumption

end AvgRewardPMD.SPMD
