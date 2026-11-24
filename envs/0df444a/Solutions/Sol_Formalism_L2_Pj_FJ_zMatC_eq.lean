-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.zMatC_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:15:50.169368+00:00
-- url     : https://prove2.me/submissions/b2957469-c14f-4dd3-863e-a1005ea76937

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
theorem _root_.solution (X : Data E r) (e : Fin ρ → Fin r → E) (τ : E →+* ℂ) (β : Matrix (Fin ρ) (Fin ρ) ℂ) :
    zMatC X e τ β = 1 + Fm τ e * β * (X.Gm.map τ * cM (Fm τ e))ᵀ := by
  unfold zMatC
  ext k l
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.transpose_apply, Fm, cM,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring
end Formalism.L2.Pj.FJ
