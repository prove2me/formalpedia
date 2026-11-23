-- Prove2me | solution 1 for Formalism.L2.Pj.gram_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:06.958963+00:00
-- url     : https://prove2.me/submissions/40c8e823-1921-4b81-a8e1-485c729b714c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnifDom
import Theorems.Thm_Formalism_L2_Pj_gram_eq

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
theorem _root_.solution (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (P Q : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (P * Q) = Qᵀ * gram τ G P * Q.map (starRingEnd ℂ) := by
  rw [gram_eq, gram_eq, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
end Formalism.L2.Pj
