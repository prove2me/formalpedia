-- Prove2me | solution 1 for BookProof.QgHermiteFriedrichs.hasDerivAt_normSq_coordLine
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T12:54:52.509021+00:00
-- url     : https://prove2.me/submissions/89a9bf55-d6e7-41b7-a873-cd40676fe3ab

-- Generated from ChapterQgHermiteFriedrichs.lean — solution of BookProof.QgHermiteFriedrichs.hasDerivAt_normSq_coordLine
import Mathlib
import Definitions.Def_ChapterQgHermiteFriedrichs
import Theorems.Thm_BookProof_QgHermiteFriedrichs_coordLine_apply
import Theorems.Thm_BookProof_QgHermiteFriedrichs_coordLine_self
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFarisLavine
open BookProof.QgHermiteFriedrichs








open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.Starobinsky
open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension

noncomputable section

variable {d : ℕ}































variable (W : Vd d → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (x : Vd d) (j : Fin d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ‖coordLine x j s‖ ^ 2) (2 * t) t := by

  have hsplit : ∀ s : ℝ, ‖coordLine x j s‖ ^ 2
      = s ^ 2 + ∑ i ∈ Finset.univ.erase j, (x i) ^ 2 := by
    intro s
    rw [norm_sq_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), coordLine_self]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [coordLine_apply, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have h0 := (hasDerivAt_pow 2 t).add_const (∑ i ∈ Finset.univ.erase j, (x i) ^ 2)
  have h1 : HasDerivAt (fun s : ℝ => s ^ 2 + ∑ i ∈ Finset.univ.erase j, (x i) ^ 2) (2 * t) t := by
    refine h0.congr_deriv ?_
    push_cast
    ring
  simpa only [hsplit] using h1
