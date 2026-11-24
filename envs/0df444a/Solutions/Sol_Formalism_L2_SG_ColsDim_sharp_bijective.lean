-- Prove2me | solution 1 for Formalism.L2.SG.ColsDim.sharp_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:26:01.696806+00:00
-- url     : https://prove2.me/submissions/d8dd9ff4-e2e2-4b5e-b8da-f29d5688a315

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ClassAct
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_ColsDim
import Theorems.Thm_Formalism_L2_SG_ColsDim_inner_sharpFun
import Theorems.Thm_Formalism_L2_SG_ColsDim_sharpFun_mem
import Theorems.Thm_Formalism_L2_SG_ColsDim_innerFun_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.ColsDim
open Formalism.UG
open InnerProductSpace
namespace Formalism.L2.SG.ColsDim
theorem _root_.solution : SharpBij := by
  intro Γ Gi Gf _ _ _ V _ _ _ ιi ιf K ψ π hπ hψ
  let F : Equi ℂ ιf K (dualRep ιi π) ψ ≃ Sharp ℂ ιi ιf K π ψ :=
    { toFun := fun f => ⟨sharpFun (f : Gf → Module.Dual ℂ V), sharpFun_mem ιf K ιi ψ π hπ hψ f⟩
      invFun := fun φ => ⟨fun x => (innerₛₗ ℂ ((φ : Gf → V) x) : Module.Dual ℂ V),
        innerFun_mem ιf K ιi ψ π hπ hψ φ⟩
      left_inv := fun f => by
        apply Subtype.ext
        funext x
        ext ξ
        exact inner_sharpFun _ x ξ
      right_inv := fun φ => by
        apply Subtype.ext
        funext x
        apply ext_inner_right ℂ
        intro ξ
        exact inner_sharpFun _ x ξ }
  refine ⟨(colsEquiv ιf K ιi ψ π).toEquiv.trans F,
    fun T x ξ => (inner_sharpFun (toEqui ιf K ιi ψ π T) x ξ).symm, fun c T => ?_⟩
  funext x
  apply ext_inner_right ℂ
  intro ξ
  have h1 := inner_sharpFun (toEqui ιf K ιi ψ π (c • T)) x ξ
  have h2 := inner_sharpFun (toEqui ιf K ιi ψ π T) x ξ
  show inner ℂ (sharpFun (toEqui ιf K ιi ψ π (c • T)) x) ξ =
    inner ℂ ((starRingEnd ℂ c) • sharpFun (toEqui ιf K ιi ψ π T) x) ξ
  rw [h1, inner_smul_left, Complex.conj_conj, h2]
  rfl
end Formalism.L2.SG.ColsDim
