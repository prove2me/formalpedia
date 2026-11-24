-- Prove2me | solution 1 for Formalism.L2.Pj.lminor_mul_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:36:50.088383+00:00
-- url     : https://prove2.me/submissions/40c0a821-4d3b-4ca1-9307-97fb18e4d825

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnifDom
import Theorems.Thm_Formalism_L2_Pj_gram_mul
import Theorems.Thm_Formalism_L2_Pj_sub_mul_tri

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex
open scoped ComplexConjugate Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace Formalism.L2.Pj
theorem _root_.solution (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P Q : Matrix (Fin r) (Fin r) ℂ)
    (hQ : Q.IsUpperTriangular) (i : Fin (r + 1)) :
    lminor (gram τ G (P * Q)) i =
      ((Complex.normSq (Q.submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
        (Fin.castLE (Nat.le_of_lt_succ i.isLt))).det : ℝ) : ℂ) * lminor (gram τ G P) i := by
  unfold lminor
  rw [gram_mul, sub_mul_tri (Nat.le_of_lt_succ i.isLt) Q (gram τ G P) hQ, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_transpose]
  generalize Q.submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt)) (Fin.castLE (Nat.le_of_lt_succ i.isLt)) = M
  rw [show (M.map (starRingEnd ℂ)).det = starRingEnd ℂ M.det from (RingHom.map_det _ M).symm,
    ← Complex.mul_conj]
  ring
end Formalism.L2.Pj
