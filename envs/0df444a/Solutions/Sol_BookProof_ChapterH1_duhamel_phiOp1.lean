-- Prove2me | solution 1 for BookProof.ChapterH1.duhamel_phiOp1
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:16:06.599342+00:00
-- url     : https://prove2.me/submissions/df505c76-1593-49e5-95e6-2ca8d95463a2

-- Generated from ChapterH1.lean — solution of BookProof.ChapterH1.duhamel_phiOp1
import Mathlib
import Definitions.Def_ChapterH1
open BookProof.ChapterH1







open scoped BigOperators
open intervalIntegral


noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (g : Fin n → ℂ) (δ : ℝ) :
    (∫ s in (0 : ℝ)..δ, (NormedSpace.exp ((δ - s) • A)).mulVec g)
      = δ • phiOp1 (δ • A) g := by

  by_cases hδ : δ = 0;
  · aesop;
  · rw [ phiOp1, intervalIntegral.integral_comp_sub_left fun x => ( NormedSpace.exp ( x • A )
      ).mulVec g ] ; norm_num [ hδ ];
    convert intervalIntegral.integral_comp_div _ _ using 3 <;> ring <;> norm_num [ hδ ];
    simp [ hδ, smul_smul ]
