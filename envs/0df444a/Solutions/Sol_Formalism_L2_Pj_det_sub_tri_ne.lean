-- Prove2me | solution 1 for Formalism.L2.Pj.det_sub_tri_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:16:42.213837+00:00
-- url     : https://prove2.me/submissions/1b1fd1df-1f00-4194-9c39-760deaeb4b3f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnifDom

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
theorem _root_.solution {i : ℕ} (h : i ≤ r) (Q : Matrix (Fin r) (Fin r) ℂ) (hQ : Q.IsUpperTriangular)
    (hd : Q.det ≠ 0) : (Q.submatrix (Fin.castLE h) (Fin.castLE h)).det ≠ 0 := by
  have hsub : (Q.submatrix (Fin.castLE h) (Fin.castLE h)).BlockTriangular id := by
    intro a b hab
    simp only [Matrix.submatrix_apply]
    exact hQ (by simp only [id_eq, Fin.lt_iff_val_lt_val, Fin.coe_castLE] at hab ⊢; exact hab)
  rw [Matrix.det_of_upperTriangular hsub]
  rw [Matrix.det_of_upperTriangular hQ] at hd
  rw [Finset.prod_ne_zero_iff] at hd ⊢
  intro c _
  exact hd _ (Finset.mem_univ _)
end Formalism.L2.Pj
