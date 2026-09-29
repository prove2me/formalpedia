-- Prove2me | solution 1 for BookProof.ShiftedHermiteCore.hermiteTLp_total
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T09:34:30.842116+00:00
-- url     : https://prove2.me/submissions/4a7cf603-faab-40e9-846e-d03f31273dfe

-- Generated from ChapterShiftedHermiteCore.lean — solution of BookProof.ShiftedHermiteCore.hermiteTLp_total
import Mathlib
import Definitions.Def_ChapterShiftedHermiteCore
import Theorems.Thm_BookProof_ShiftedHermiteCore_span_hermiteTLp
import Theorems.Thm_BookProof_ShiftedHermiteCore_eq_zero_of_inner_coreT
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
open BookProof.ShiftedHermiteCore











open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (a k : Vd d) (v : L2d d)
    (h : ∀ α, (inner ℂ (hermiteTLp (d := d) a k α) v : ℂ) = 0) : v = 0 := by

  refine eq_zero_of_inner_coreT a k v fun z hz => ?_
  rw [← span_hermiteTLp a k] at hz
  induction hz using Submodule.span_induction with
  | mem z hz => obtain ⟨α, rfl⟩ := hz; exact h α
  | zero => simp
  | add z z' _ _ ihz ihz' => rw [inner_add_left, ihz, ihz']; ring
  | smul r z _ ih => rw [inner_smul_left, ih]; ring
