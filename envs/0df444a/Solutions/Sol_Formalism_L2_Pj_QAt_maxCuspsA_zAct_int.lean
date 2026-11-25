-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.maxCuspsA_zAct_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:50:24.853101+00:00
-- url     : https://prove2.me/submissions/18005952-f06a-444f-9404-e0916c02262c

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
import Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_zMatE_map
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
theorem _root_.solution (X : Data E r) (cu : CuspFD X ρ) (hb : IsZBasis X cu (zBas X cu))
    (n : Fin (nZ X ρ) → ℤ) : ∃ β ∈ zGam X cu, ∃ γ ∈ X.Γ,
      (γ : Matrix (Fin r) (Fin r) E) = zMatE X cu.e β ∧
      ∀ y, zAct X cu (fun i => (n i : ℝ)) y = lact γ y := by
  obtain ⟨-, hb2⟩ := hb
  have hβ : (∑ k, n k • zBas X cu k) ∈ zGam X cu := by
    rw [hb2]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hβ' := hβ
  simp only [zGam, Set.mem_setOf_eq] at hβ'
  obtain ⟨-, γ, hγ, hγe⟩ := hβ'
  refine ⟨_, hβ, γ, hγ, hγe, fun y => ?_⟩
  funext τ
  show zMatC X cu.e τ.1 (∑ k, (((n k : ℝ)) : ℂ) • (zBas X cu k).map τ.1) * mat y τ =
    (γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat y τ
  rw [hγe, maxCuspsA_zMatE_map]
  congr 2
  ext i j
  simp only [Matrix.sum_apply, Matrix.map_apply, Matrix.smul_apply, map_sum, map_zsmul, smul_eq_mul]
  simp only [zsmul_eq_mul, Complex.ofReal_intCast]
end Formalism.L2.Pj.QAt
