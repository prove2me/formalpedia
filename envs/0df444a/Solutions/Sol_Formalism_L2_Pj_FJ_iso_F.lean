-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.iso_F
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:15:34.014438+00:00
-- url     : https://prove2.me/submissions/d883be4e-f0aa-4a16-abe2-c31cc7a4c8be

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Theorems.Thm_P2M_Formalism_L2_Pj_FJ_emb_cc__a0a14d96c40b

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
theorem _root_.solution (X : Data E r) (cu : CuspFD X ρ) (τ : E →+* ℂ) :
    (Fm τ cu.e)ᵀ * X.Gm.map τ * cM (Fm τ cu.e) = 0 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fm, cM, Matrix.of_apply, Matrix.map_apply,
    Matrix.zero_apply, Finset.sum_mul]
  have h := congrArg τ (cu.3 a b)
  unfold ReciprocityTheory.ChartRestriction.G.FD.herm at h
  simp only [map_sum, map_mul, map_zero, emb_cc'] at h
  rw [Finset.sum_comm]
  exact h
end Formalism.L2.Pj.FJ
