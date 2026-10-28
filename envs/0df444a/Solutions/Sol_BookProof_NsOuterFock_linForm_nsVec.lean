-- Prove2me | solution 1 for BookProof.NsOuterFock.linForm_nsVec
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-27T05:52:20.892273+00:00
-- url     : https://prove2.me/submissions/1b6c1f5d-1b61-413d-ac01-51498681f094

-- Generated from ChapterNsOuterFockFarisLavine.lean — solution of BookProof.NsOuterFock.linForm_nsVec
import Mathlib
import Definitions.Def_ChapterNsOuterFockFarisLavine
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterSqSumOuterFamily
import Definitions.Def_ChapterQgOuterFockEsa
open BookProof.NsOuterFock




open Finset MvPolynomial
open BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.HermiteProductCore BookProof.QgHermiteOscillator
open BookProof.QgOuterFock BookProof.QgOuterFockFL
open BookProof.QgOuterFockInteractionFL
open BookProof.SqSumOuterFamily
open BookProof.QgOuterFock

noncomputable section

variable (bv : Fin 3 → ℝ) (nu lam mu gg : ℝ)

set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} (p : Fin n) (f : NsLoc) (hne : nextPart p ≠ p) :
    linForm (nsVec bv nu lam mu gg n (p, f))
      = (∑ l : NsLoc, ((sameVec bv nu lam mu gg f l : ℝ) : ℂ) • X (coordOf p l))
        + ∑ l : NsLoc, ((nextVec lam mu f l : ℝ) : ℂ) • X (coordOf (nextPart p) l) := by

  classical
  rw [linForm, sum_reindex_parcels]
  have hval : ∀ (q : Fin n) (l : NsLoc),
      ((nsVec bv nu lam mu gg n (p, f) (coordOf q l) : ℝ) : ℂ)
          • (X (coordOf q l) : MvPolynomial (Fin (n * 18)) ℂ)
        = if q = p then ((sameVec bv nu lam mu gg f l : ℝ) : ℂ) • X (coordOf q l)
          else if q = nextPart p then ((nextVec lam mu f l : ℝ) : ℂ) • X (coordOf q l)
          else 0 := by
    intro q l
    rw [nsVec, parcelOf_coordOf, locOf_coordOf]
    by_cases h1 : q = p
    · rw [if_pos h1, if_pos h1]
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : q = nextPart p
      · rw [if_pos h2, if_pos h2]
      · rw [if_neg h2, if_neg h2]
        simp
  have hzero : ∀ q ∈ (Finset.univ : Finset (Fin n)), q ∉ ({p, nextPart p} : Finset (Fin n)) →
      (∑ l : NsLoc, ((nsVec bv nu lam mu gg n (p, f) (coordOf q l) : ℝ) : ℂ)
        • (X (coordOf q l) : MvPolynomial (Fin (n * 18)) ℂ)) = 0 := by
    intro q _ hq
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [hval q l, if_neg hq.1, if_neg hq.2]
  rw [← Finset.sum_subset (Finset.subset_univ ({p, nextPart p} : Finset (Fin n))) hzero,
    Finset.sum_pair (Ne.symm hne)]
  congr 1
  · exact Finset.sum_congr rfl fun l _ => by rw [hval p l, if_pos rfl]
  · exact Finset.sum_congr rfl fun l _ => by rw [hval (nextPart p) l, if_neg hne, if_pos rfl]
