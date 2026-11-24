-- Prove2me | solution 1 for Formalism.L2.Pj.sub_mul_tri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:24:01.984186+00:00
-- url     : https://prove2.me/submissions/3b337b17-c6e9-4f91-bfd6-f17c2949536b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnifDom
import Theorems.Thm_Formalism_L2_Pj_sum_castLE

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
theorem _root_.solution {i : ℕ} (h : i ≤ r) (Q A : Matrix (Fin r) (Fin r) ℂ) (hQ : Q.IsUpperTriangular) :
    (Qᵀ * A * Q.map (starRingEnd ℂ)).submatrix (Fin.castLE h) (Fin.castLE h) =
      (Q.submatrix (Fin.castLE h) (Fin.castLE h))ᵀ * A.submatrix (Fin.castLE h) (Fin.castLE h) *
        (Q.submatrix (Fin.castLE h) (Fin.castLE h)).map (starRingEnd ℂ) := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [sum_castLE h]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [sum_castLE h]
    intro k hk
    have hz : Q k (Fin.castLE h a) = 0 :=
      hQ (by simp only [id_eq, Fin.lt_iff_val_lt_val, Fin.coe_castLE]; exact lt_of_lt_of_le a.isLt hk)
    rw [hz, zero_mul]
  · intro l hl
    have hz : Q l (Fin.castLE h b) = 0 :=
      hQ (by simp only [id_eq, Fin.lt_iff_val_lt_val, Fin.coe_castLE]; exact lt_of_lt_of_le b.isLt hl)
    rw [hz, map_zero, mul_zero]
end Formalism.L2.Pj
