-- Prove2me | solution 1 for Formalism.L2.Pj.dom_rmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:52:56.30648+00:00
-- url     : https://prove2.me/submissions/92487e48-133e-49cd-94d6-b0264c0078cb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnifDom
import Theorems.Thm_Formalism_L2_Pj_lminor_mul_tri
import Theorems.Thm_Formalism_L2_Pj_det_sub_tri_ne
import Theorems.Thm_Formalism_L2_Pj_bor_upper

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
theorem _root_.solution (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    rmul x b ∈ X.dom := by
  simp only [Data.dom, GG, Set.mem_setOf_eq] at hx ⊢
  intro τ
  obtain ⟨hdet, hpos⟩ := hx τ
  have hQ := bor_upper hb τ
  have hbd : (mat b τ).det ≠ 0 := (hb τ).1
  have hm : mat (rmul x b) τ = mat x τ * mat b τ := rfl
  refine ⟨?_, fun i => ?_⟩
  · rw [hm, Matrix.det_mul]
    exact mul_ne_zero hdet hbd
  · have hi := hpos i
    simp only [dmin] at hi ⊢
    rw [hm, lminor_mul_tri τ.1 X.Gm _ _ hQ i, Complex.re_ofReal_mul]
    have hn : 0 < Complex.normSq ((mat b τ).submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
        (Fin.castLE (Nat.le_of_lt_succ i.isLt))).det :=
      Complex.normSq_pos.mpr (det_sub_tri_ne _ _ hQ hbd)
    rw [mul_left_comm]
    exact mul_pos hn hi
end Formalism.L2.Pj
