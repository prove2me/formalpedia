-- Prove2me | solution 1 for BookProof.ChapterGaugeUnconstrainedSpectrum.isUnconstrained_of_faithful
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:40:03.450069+00:00
-- url     : https://prove2.me/submissions/7fc822e1-2184-4d66-ba56-4a25348ec5e0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterGaugeUnconstrainedSpectrum.lean — solution of BookProof.ChapterGaugeUnconstrainedSpectrum.isUnconstrained_of_faithful
import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Theorems.Thm_BookProof_ChapterGaugeUnconstrainedSpectrum_permOp_isFunctionOfSpectrum_iff
open BookProof.ChapterGaugeUnconstrainedSpectrum




variable {X : Type*}

variable {X : Type*}
variable {G : Type*} [Group G]

set_option maxHeartbeats 1000000 in
theorem solution {ρ : G →* Equiv.Perm X}
    (hρ : Function.Injective ρ) :
    IsUnconstrainedGaugeFixing (fun g => permOp (ρ g)) := by

  intro g hg hmem
  exact hg (hρ (by simpa using (permOp_isFunctionOfSpectrum_iff (ρ g)).1 hmem))
