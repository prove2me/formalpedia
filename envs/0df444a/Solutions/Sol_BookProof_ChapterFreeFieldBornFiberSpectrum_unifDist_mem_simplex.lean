-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornFiberSpectrum.unifDist_mem_simplex
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-19T05:39:24.694665+00:00
-- url     : https://prove2.me/submissions/e1941200-838a-4212-8852-47e70c9f6814

-- Generated from ChapterFreeFieldBornFiberSpectrum.lean — solution of BookProof.ChapterFreeFieldBornFiberSpectrum.unifDist_mem_simplex
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
    unifDist n k ∈ stdSimplex ℝ (Fin n) := by
  constructor;
  · exact fun x => by unfold unifDist; split_ifs <;> positivity;
  · unfold unifDist;
    norm_num [ Finset.sum_ite ];
    rw [ show ( Finset.univ.filter fun x : Fin n => ( x : ℕ ) < k ).card = k from ?_,
        mul_inv_cancel₀ ( by positivity ) ];
    rw [ Finset.card_eq_of_bijective ];
    focus (use fun i hi => ⟨ i, by linarith ⟩);
    · grind;
    · grind;
    · lia

/-
For `1 ≤ k ≤ n`, `unifDist n k` has exactly `k` strictly positive
coordinates.
-/
