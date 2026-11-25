-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.maxCuspsA_beta_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:17:09.714913+00:00
-- url     : https://prove2.me/submissions/e836d955-9a3c-4059-99b3-b7466ddd7b33

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
import Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_transv
import Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_kappa_cc
import Theorems.Thm_Formalism_L2_Pj_QAt_mc_cc_mul
import Theorems.Thm_Formalism_L2_Pj_QAt_mc_cc_nat
import Theorems.Thm_Formalism_L2_Pj_QAt_mc_cc_cc
import Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_iso
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
theorem _root_.solution (X : Data E r) (cu : CuspFD X ρ) (la : Wt X.Ψ r) (η : Fin ρ → E)
    (hξΛ : ∑ a, η a • cu.e a ∈ X.Λ) (a : E) (ha : cc a = a) (hai : IsIntegral ℤ a) :
    mcBeta X la η a ∈ zGam X cu := by
  have hn : ∀ n : ℕ, IsIntegral ℤ (n : E) := by
    intro n
    induction n with
    | zero => simpa using (isIntegral_zero : IsIntegral ℤ (0 : E))
    | succ k ih => simpa [Nat.cast_succ] using ih.add (isIntegral_one : IsIntegral ℤ (1 : E))
  have hs : cc ((X.chiOrd la : E) * a) = (X.chiOrd la : E) * a := by rw [mc_cc_mul, mc_cc_nat, ha]
  have hi : IsIntegral ℤ ((X.chiOrd la : E) * a) := (hn _).mul hai
  obtain ⟨γ, hγ, hγe⟩ := X.transv _ hξΛ (maxCuspsA_iso X cu η) _ hs hi
  simp only [zGam, Set.mem_setOf_eq]
  refine ⟨?_, γ, hγ, ?_⟩
  · simp only [IsSkew]
    intro i j
    simp only [mcBeta, mcMη, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mc_cc_mul, mc_cc_nat, ha,
      mc_cc_cc, maxCuspsA_kappa_cc]
    ring
  · rw [hγe, maxCuspsA_transv, mcBeta]
end Formalism.L2.Pj.QAt
