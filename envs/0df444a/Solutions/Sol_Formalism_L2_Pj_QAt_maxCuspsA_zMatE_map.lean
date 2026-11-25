-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.maxCuspsA_zMatE_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:42:42.310498+00:00
-- url     : https://prove2.me/submissions/12c27076-9b6c-458b-9800-6a6c0332edcf

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA

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
open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix Formalism.L2.Pj.FJ Complex
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace Formalism.L2.Pj.QAt
theorem _root_.solution (X : Data E r) (e : Fin ρ → Fin r → E) (τ : E →+* ℂ)
    (β : Matrix (Fin ρ) (Fin ρ) E) : (zMatE X e β).map τ = zMatC X e τ (β.map τ) := by
  have hτ : ∀ x : E, τ (cc x) = (starRingEnd ℂ) (τ x) := fun x => by
    first
    | exact IsCMField.complexEmbedding_complexConj τ x
    | exact IsCMField.complexEmbedding_complexConj (K := E) τ x
    | simp [cc, IsCMField.complexEmbedding_complexConj]
    | simp [cc]
  ext k l
  simp only [zMatE, zMatC, Matrix.map_apply, Matrix.of_apply, map_add, map_sum, map_mul, hτ]
  split_ifs <;> simp
end Formalism.L2.Pj.QAt
