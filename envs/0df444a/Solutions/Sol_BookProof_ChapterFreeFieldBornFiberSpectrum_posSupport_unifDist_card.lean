-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornFiberSpectrum.posSupport_unifDist_card
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:39:25.698169+00:00
-- url     : https://prove2.me/submissions/4ac96bfc-9692-492c-9dd2-b162fc38a26e

-- Generated from ChapterFreeFieldBornFiberSpectrum.lean — solution of BookProof.ChapterFreeFieldBornFiberSpectrum.posSupport_unifDist_card
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberSpectrum
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornSurj
import Definitions.Def_ChapterFreeFieldBornCont
import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
import Definitions.Def_ChapterFreeFieldBornFiberTwo
import Definitions.Def_ChapterFreeFieldBornFiberBounds
open BookProof.ChapterFreeFieldBornFiberSpectrum



open MeasureTheory
open BookProof.ChapterFreeFieldBorn BookProof.ChapterFreeFieldBornSurj
open BookProof.ChapterFreeFieldBornCont BookProof.ChapterFreeFieldBornQuotient
open BookProof.ChapterFreeFieldBornFiberCardGeneral
open BookProof.ChapterFreeFieldBornFiberTwo
open BookProof.ChapterFreeFieldBornFiberBounds


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution {k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    (posSupport (unifDist n k)).card = k := by
  convert Finset.card_eq_sum_ones ( Finset.Iio k ) using 1;
  · refine Finset.card_bij ( fun x hx => x.1 ) ?_ ?_ ?_ <;> simp only [posSupport,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, exists_prop];
    · unfold unifDist; aesop;
    · exact fun a₁ ha₁ a₂ ha₂ h => Fin.ext h;
    · intro b hb; use ⟨ b, by linarith ⟩ ; simp [ unifDist, hb ] ;
      linarith;
  · norm_num

/-
For every `1 ≤ k ≤ n` there is a probability distribution whose Born fiber
has exactly `2 ^ k` points — the uniform distribution on the first `k`
coordinates.
-/
