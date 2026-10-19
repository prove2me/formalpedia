-- Prove2me | solution 1 for BookProof.BrstReducedTransfer.infDist_exactStates_eq_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T18:56:26.871174+00:00
-- url     : https://prove2.me/submissions/a30bd408-1498-432b-8691-b16a0e4139f4

-- Generated from ChapterBrstReducedTransfer.lean — solution of BookProof.BrstReducedTransfer.infDist_exactStates_eq_inc
import Mathlib
import Definitions.Def_ChapterBrstReducedTransfer
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.BrstReducedTransfer




open BookProof BookProof.ChapterStoneResolvent


variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

variable (Om : H →L[ℂ] H)

variable {Om}
variable (Om)
variable (U : ℝ → (H →L[ℂ] H)) (hcomm : ∀ (t : ℝ) (y : H), U t (Om y) = Om (U t y))

set_option maxHeartbeats 1000000 in

include hcomm in
theorem solution (hzero : ∀ x : H, U 0 x = x)
    (hgroup : ∀ (s t : ℝ) (x : H), U s (U t x) = U (s + t) x)
    (hisom : ∀ (t : ℝ) (x : H), ‖U t x‖ = ‖x‖) (t : ℝ) (x : H) :
    Metric.infDist (U t x) (exactStates Om) = Metric.infDist x (exactStates Om) := by
  have hne : (exactStates Om : Set H).Nonempty := ⟨0, (exactStates Om).zero_mem⟩
  have key : ∀ (s : ℝ) (y : H),
      Metric.infDist (U s y) (exactStates Om) ≤ Metric.infDist y (exactStates Om) := by
    intro s y
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨z, hz, hdz⟩ := (Metric.infDist_lt_iff hne).1
      (by linarith [Metric.infDist_nonneg (x := y) (s := (exactStates Om : Set H))] :
        Metric.infDist y (exactStates Om) < Metric.infDist y (exactStates Om) + ε)
    have hd : dist (U s y) (U s z) = dist y z := by
      simp [dist_eq_norm, ← map_sub, hisom]
    calc Metric.infDist (U s y) (exactStates Om)
        ≤ dist (U s y) (U s z) :=
          Metric.infDist_le_dist_of_mem (exactStates_invariant (hcomm s) z hz)
      _ = dist y z := hd
      _ ≤ Metric.infDist y (exactStates Om) + ε := le_of_lt hdz
  refine le_antisymm (key t x) ?_
  have hback := key (-t) (U t x)
  rwa [hgroup, neg_add_cancel, hzero] at hback
