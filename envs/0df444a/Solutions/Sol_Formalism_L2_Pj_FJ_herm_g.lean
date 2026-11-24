-- Prove2me | solution 1 for Formalism.L2.Pj.FJ.herm_g
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:16:09.198742+00:00
-- url     : https://prove2.me/submissions/845a4f3b-bb23-48a9-a7c8-2640bfdce8a4

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
theorem _root_.solution (X : Data E r) (τ : E →+* ℂ) : (cM (X.Gm.map τ))ᵀ = X.Gm.map τ := by
  ext i j
  simp only [Matrix.transpose_apply, cM, Matrix.map_apply]
  rw [← emb_cc', X.4 j i]
end Formalism.L2.Pj.FJ
