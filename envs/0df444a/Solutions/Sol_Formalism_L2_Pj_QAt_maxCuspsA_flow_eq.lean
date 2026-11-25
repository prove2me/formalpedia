-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.maxCuspsA_flow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:29:01.361098+00:00
-- url     : https://prove2.me/submissions/10d418d2-4a01-4585-be82-f386437e0ae3

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
import Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_flowMat
import Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_beta_map
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
theorem _root_.solution (X : Data E r) (cu : CuspFD X ρ) (la : Wt X.Ψ r) (η : Fin ρ → E) {n : ℕ}
    (a : Fin n → E) (ha : ∀ j, cc (a j) = a j) (ω : Fin n → X.Ψ → ℝ)
    (hω : ∀ j, ω j = ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters.per X la (a j))
    (c : Fin n → Fin (nZ X ρ) → ℤ) (hc : ∀ j, ∑ k, c j k • zBas X cu k = mcBeta X la η (a j))
    (t : Fin n → ℝ) (x : Frame X.Ψ r) :
    X.flow (∑ a, η a • cu.e a) (fun τ => ∑ j, ((t j : ℝ) : ℂ) * (ω j τ : ℂ)) x =
      zAct X cu (mcT c t) x := by
  funext τ
  have hZ : ∀ j, ∑ k, ((c j k : ℤ) : ℂ) • (zBas X cu k).map τ.1 =
      (((ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters.per X la (a j) τ : ℝ) : ℂ) * (-(I * X.c τ))) • mcMηc τ.1 η := by
    intro j
    rw [← maxCuspsA_beta_map X la η (a j) (ha j) τ, ← hc j]
    ext i i'
    simp only [Matrix.sum_apply, Matrix.map_apply, Matrix.smul_apply, map_sum, map_zsmul, smul_eq_mul]
    simp only [zsmul_eq_mul]
  show X.flowMat (∑ a, η a • cu.e a) τ (∑ j, ((t j : ℝ) : ℂ) * (ω j τ : ℂ)) * mat x τ =
    zMatC X cu.e τ.1 (∑ k, ((mcT c t k : ℝ) : ℂ) • (zBas X cu k).map τ.1) * mat x τ
  rw [maxCuspsA_flowMat]
  congr 2
  have hB : (∑ k, ((mcT c t k : ℝ) : ℂ) • (zBas X cu k).map τ.1) =
      ∑ j, ((t j : ℝ) : ℂ) • ∑ k, ((c j k : ℤ) : ℂ) • (zBas X cu k).map τ.1 := by
    simp only [mcT, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_intCast, Finset.sum_smul,
      Finset.smul_sum, mul_smul]
    exact Finset.sum_comm
  rw [hB]
  simp only [hZ, smul_smul, ← Finset.sum_smul, hω]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring
end Formalism.L2.Pj.QAt
