-- Prove2me | solution 1 for Formalism.L2.Th1.H.ud_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:00:08.387854+00:00
-- url     : https://prove2.me/submissions/5a6fc5f2-d44a-47ed-b406-0593125023f8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_UnitaryConstant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_LocalComponentGL
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyPhaseQuadratic
import Theorems.Thm_Formalism_L2_Th1_H_ud_adj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type} [AddCommGroup V] [Module ℂ V] {H : Sesq V} {Λ : AddSubgroup V} {α : V → ℂ}
  {δ Ae : V ≃ₗ[ℂ] V}
namespace Formalism.L2.Th1.H
theorem _root_.solution (h : UnitaryData H Λ α δ Ae) (x y : V) : H (cayC Ae x) y = -H x (cayC Ae y) := by
  have h1 := ud_adj h x y
  have hc : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 :=
    Complex.conj_eq_iff_real.mpr ⟨1 / 2, by first | norm_num | simp | (push_cast; ring)⟩
  simp only [cayC, map_sub, map_smul, map_smulₛₗ, RingHom.id_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hc]
  linear_combination h1
end Formalism.L2.Th1.H
