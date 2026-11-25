-- Prove2me | solution 1 for Formalism.MainNotions.flipOneThree.Pf.harProj_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:54:11.320904+00:00
-- url     : https://prove2.me/submissions/50c14b9d-1c22-493a-b19c-db4575cb1920

import Definitions.Def_Formalism_PolynomialDimension_FinalHar
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_HarProjEqZeroIff
import Theorems.Thm_Formalism_CountingSumsFrames_Top_harProj
import Theorems.Thm_Formalism_CountingSumsFrames_Top_harQuot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf
open Formalism.CountingSumsFrames MvPolynomial
namespace Formalism.MainNotions.flipOneThree.Pf
theorem _root_.solution {K : Type} [Field K] [CharZero K] {k : ℕ} (hk : 1 ≤ k) (p : ℕ) (hp : p.Prime)
    (Ov : ValuationSubring K) (hloc : PLocal Ov.toSubring p) {a b : ℕ} {f : PolXY K k} (hf : f ∈ PolAB K k a b) :
    harProj K k a b f = 0 ↔ ∃ G ∈ PolAB K k (a - 1) (b - 1), f = hXY K k * G := by
  have HP : Formalism.CountingSumsFrames.HarProj := Formalism.CountingSumsFrames.Top.harProj
  have HQ : Formalism.CountingSumsFrames.HarQuot := Formalism.CountingSumsFrames.Top.harQuot
  obtain ⟨hf1, g, hg, hfg⟩ := (HP K k a b hk).1 f hf
  constructor
  · intro h0
    refine ⟨g, hg, ?_⟩
    rw [h0, sub_zero] at hfg
    exact hfg
  · rintro ⟨G, -, rfl⟩
    refine (HQ K k a b p Ov 1 hk hp hloc).1 _ (G - g) hf1 ?_
    rw [mul_sub, ← hfg, sub_sub_cancel]
end Formalism.MainNotions.flipOneThree.Pf
