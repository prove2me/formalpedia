-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.maxCuspsA_flowMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:45:12.185917+00:00
-- url     : https://prove2.me/submissions/cb78ef9e-e93f-491a-84c8-acad60f8c343

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
import Theorems.Thm_Formalism_L2_Pj_QAt_max_cusps_rank_one_expand
import Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_vec_apply
import Theorems.Thm_Formalism_L2_Pj_FJ_FnVia_smul_apply


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
theorem _root_.solution (X : Data E r) (cu : CuspFD X ρ) (η : Fin ρ → E) (τ : X.Ψ) (z : ℂ) :
    X.flowMat (∑ a, η a • cu.e a) τ z = zMatC X cu.e τ.1 ((-(I * X.c τ) * z) • mcMηc τ.1 η) := by
  ext k l
  have hv := maxCuspsA_vec_apply cu.e η
  have h1 := max_cusps_rank_one_expand (starRingEnd ℂ) (fun k l => τ.1 (X.Gm k l)) (fun a => τ.1 (η a))
    (fun a k => τ.1 (cu.e a k)) (-(I * X.c τ) * z) k l
  simp only [map_sum, map_mul] at h1
  simp only [Data.flowMat, zMatC, mcMηc, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hv,
    map_sum, map_mul]
  rw [sub_eq_add_neg]
  congr 1
  rw [← h1]
  ring
end Formalism.L2.Pj.QAt
