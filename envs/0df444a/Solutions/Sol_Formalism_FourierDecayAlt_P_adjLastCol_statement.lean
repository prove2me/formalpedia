-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.adjLastCol_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:36:32.259702+00:00
-- url     : https://prove2.me/submissions/c4faaf33-8fb9-4573-a5f7-5aa97f39f190

import Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OmegaNormCofactorOfParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C7.AdjLastCol := by
  intro r Z l u hl1 hl2 hu1 hu2 b
  have hdl : l.det = 1 := by
    rw [Matrix.det_of_lowerTriangular l (fun i j h => hl1 i j h)]; simp [hl2]
  have hdu : u.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j h => hu1 i j h)]; simp [hu2]
  have hadj : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, M.det = 1 → adjugate M = M⁻¹ := by
    intro M hM; rw [Matrix.inv_def, hM]; simp
  have hcol : ∀ d, l d (Fin.last r) = if d = Fin.last r then 1 else 0 := by
    intro d
    by_cases hd : d = Fin.last r
    · subst hd; simp [hl2]
    · rw [if_neg hd]; exact hl1 d _ (Fin.lt_last_iff_ne_last.2 hd)
  have hinv : ∀ d, l⁻¹ d (Fin.last r) = if d = Fin.last r then 1 else 0 := by
    intro d
    have e : l⁻¹ * l = 1 := Matrix.nonsing_inv_mul l (by rw [hdl]; exact isUnit_one)
    have := congrArg (fun M => M d (Fin.last r)) e
    simp only [Matrix.mul_apply, hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, Matrix.one_apply] at this
    rw [this]
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hadj u hdu, hadj l hdl, Matrix.mul_apply]
  apply Finset.sum_congr rfl; intro c _
  congr 1
  rw [Matrix.mul_apply]
  simp [hinv]
end Formalism.FourierDecayAlt.P
