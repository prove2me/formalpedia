-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornFiberTwo.posSupport_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T23:57:55.732978+00:00
-- url     : https://prove2.me/submissions/c7610535-d750-4af0-b743-d8b139ecd5e6

-- Generated from ChapterFreeFieldBornFiberTwo.lean — solution of BookProof.ChapterFreeFieldBornFiberTwo.posSupport_nonempty
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberTwo
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBornCont
import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
open BookProof.ChapterFreeFieldBornFiberTwo



open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornCont BookProof.ChapterFreeFieldBornQuotient
open BookProof.ChapterFreeFieldBornFiberCardGeneral


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {p : Fin n → ℝ} (hp : p ∈ stdSimplex ℝ (Fin n)) :
    (posSupport p).Nonempty := by

  by_contra h_empty;
  simp_all only [posSupport, Finset.not_nonempty_iff_eq_empty, Finset.ext_iff, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_lt];
  exact absurd ( hp.2 ▸ Finset.sum_nonpos fun i _ => h_empty i ) ( by norm_num )
