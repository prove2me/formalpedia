-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.gram_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:35.736633+00:00
-- url     : https://prove2.me/submissions/d60dee79-6c54-40a7-8914-44a0b54693ab

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FJ
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace Formalism.L2.Pj.FJ
theorem _root_.solution (X : Data E r) (τ : E →+* ℂ) (A : Matrix (Fin r) (Fin r) ℂ) :
    gram τ X.Gm A = Aᵀ * X.Gm.map τ * cM A := by
  unfold ReciprocityTheory.ChartRestriction.G.FD.gram hermC ReciprocityTheory.ChartRestriction.G.FD.col
  ext a b
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, cM, Finset.sum_mul]
  rw [Finset.sum_comm]
end Formalism.L2.Pj.FJ
