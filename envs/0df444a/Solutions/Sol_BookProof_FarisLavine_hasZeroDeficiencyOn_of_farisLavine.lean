-- Prove2me | solution 1 for BookProof.FarisLavine.hasZeroDeficiencyOn_of_farisLavine
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T11:43:35.769776+00:00
-- url     : https://prove2.me/submissions/e4a20d08-25d7-4c54-833c-278f3453ee14

-- Generated from ChapterFarisLavine.lean — solution of BookProof.FarisLavine.hasZeroDeficiencyOn_of_farisLavine
import Mathlib
import Definitions.Def_ChapterFarisLavine
import Theorems.Thm_BookProof_FarisLavine_essentiallySelfAdjointOn_iff_hasZeroDeficiencyOn
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_FarisLavine_essentiallySelfAdjointOn_of_farisLavine
open BookProof.FarisLavine





variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}




open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.LpNat




open scoped ENNReal























open BookProof.NavierStokesFlow

set_option maxHeartbeats 1000000 in
theorem solution [CompleteSpace F]
    (D : Submodule ℂ F) (H N : D →ₗ[ℂ] D) (c : ℝ)
    (hH : SymmetricOn D (D.subtype.comp H)) (hN : SymmetricOn D (D.subtype.comp N))
    (hc : 0 ≤ c)
    (hNpos : ∀ x : D, 0 ≤ quadForm (D.subtype.comp N) x)
    (hNsurj : ∀ f : F, ∃ x : D, (N x : F) + (x : F) = f)
    (hcomm : ∀ x : D, |commForm (D.subtype.comp H) (D.subtype.comp N) x|
      ≤ c * quadForm (D.subtype.comp N) x) :
    HasZeroDeficiencyOn D H :=
  (essentiallySelfAdjointOn_iff_hasZeroDeficiencyOn D H).1
      (essentiallySelfAdjointOn_of_farisLavine (D.subtype.comp H) (D.subtype.comp N) c
        hH hN hc hNpos hNsurj hcomm)
