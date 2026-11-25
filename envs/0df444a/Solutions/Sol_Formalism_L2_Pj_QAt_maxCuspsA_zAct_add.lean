-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.maxCuspsA_zAct_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:52:58.026232+00:00
-- url     : https://prove2.me/submissions/96e82d4e-86c8-49be-848c-1493693fc252

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
import Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_zMatC_add

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
theorem _root_.solution (X : Data E r) (cu : CuspFD X ρ) (t u : Fin (nZ X ρ) → ℝ)
    (x : Frame X.Ψ r) : zAct X cu t (zAct X cu u x) = zAct X cu (t + u) x := by
  funext τ
  have hS : (∑ k, (((t + u) k : ℝ) : ℂ) • (zBas X cu k).map τ.1) =
      (∑ k, ((t k : ℝ) : ℂ) • (zBas X cu k).map τ.1) + ∑ k, ((u k : ℝ) : ℂ) • (zBas X cu k).map τ.1 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.add_apply, Complex.ofReal_add, add_smul]
  have hm : mat (zAct X cu u x) τ =
      zMatC X cu.e τ.1 (∑ k, ((u k : ℝ) : ℂ) • (zBas X cu k).map τ.1) * mat x τ := rfl
  show zMatC X cu.e τ.1 (∑ k, ((t k : ℝ) : ℂ) • (zBas X cu k).map τ.1) * mat (zAct X cu u x) τ =
    zMatC X cu.e τ.1 (∑ k, (((t + u) k : ℝ) : ℂ) • (zBas X cu k).map τ.1) * mat x τ
  rw [hm, hS, maxCuspsA_zMatC_add, Matrix.mul_assoc]
end Formalism.L2.Pj.QAt
