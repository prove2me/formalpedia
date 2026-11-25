-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.maxCuspsA_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:12:04.80244+00:00
-- url     : https://prove2.me/submissions/ad89a2b5-d2c2-4b2d-aeda-d740931c4a85

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA
import Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_zAct_add
import Theorems.Thm_Formalism_L2_Pj_QAt_maxCuspsA_zAct_int
import Theorems.Thm_Formalism_L2_Pj_FJ_zAct_mem_dom
import Theorems.Thm_Formalism_L2_Pj_FJ_zBas_skew


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
    (la : Wt X.Ψ r)
    (hchi : ∀ β ∈ zGam X cu, ∀ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E) = zMatE X cu.e β →
      X.χ la γ = 1)
    (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) (x : Frame X.Ψ r) (hx : x ∈ X.dom)
    (u : Fin (nZ X ρ) → ℝ) (n : Fin (nZ X ρ) → ℤ) :
    P (zAct X cu (u + fun i => (n i : ℝ)) x) = P (zAct X cu u x) := by
  obtain ⟨β, hβ, γ, hγ, hγe, hact⟩ := maxCuspsA_zAct_int X cu hb n
  have hy : zAct X cu u x ∈ X.dom := zAct_mem_dom X cu (zBas_skew X cu ⟨_, hb⟩) u x hx
  rw [add_comm, ← maxCuspsA_zAct_add, hact, hP.2.2 γ hγ _ hy, hchi β hβ γ hγ hγe, one_mul]
end Formalism.L2.Pj.QAt
