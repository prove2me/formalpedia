-- Prove2me | solution 1 for Formalism.ZF.laurentExpansionAtOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:55:30.804801+00:00
-- url     : https://prove2.me/submissions/53d5cb9d-bb37-41d0-8511-65f82b6ea3e0

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LaurentAtOne
import Theorems.Thm_Formalism_ZF_laU_open
import Theorems.Thm_Formalism_ZF_one_mem_laU
import Theorems.Thm_Formalism_ZF_laH_diffOn
import Theorems.Thm_Formalism_ZF_laH_one
import Theorems.Thm_Formalism_ZF_laH_deriv_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution : LaurentAtOne := by
  intro y hy
  set h := laHfun y with hdef
  have hn : laU ∈ 𝓝 (1 : ℂ) := laU_open.mem_nhds one_mem_laU
  refine ⟨dslope (dslope h 1) 1, ?_, ?_⟩
  · have h1 : DifferentiableOn ℂ (dslope (dslope h 1) 1) laU :=
      (differentiableOn_dslope hn).2 ((differentiableOn_dslope hn).2 (laH_diffOn y hy))
    exact h1.differentiableAt hn
  · have hU : ∀ᶠ w in 𝓝[≠] (1 : ℂ), w ∈ laU := nhdsWithin_le_nhds hn
    filter_upwards [log_deriv_riemannZeta_eq_neg_inv_sub_add, hU, self_mem_nhdsWithin]
      with w hw hwU hw1
    have hw1' : w - 1 ≠ 0 := sub_ne_zero.2 hw1
    have hw0 : w ≠ 0 := hwU.2
    have e1 := sub_smul_dslope h 1 w
    have e2 := sub_smul_dslope (dslope h 1) 1 w
    rw [dslope_same] at e2
    simp only [smul_eq_mul] at e1 e2
    rw [hdef, laH_deriv_one y hy] at e2
    rw [hdef, laH_one y] at e1
    have hhw : laHfun y w =
        (1 - (w - 1) * (deriv riemannZeta₁ w / riemannZeta₁ w)) * ((y : ℂ) ^ w / w) := rfl
    unfold Fy
    rw [hw]
    rw [hdef] at *
    generalize deriv riemannZeta₁ w / riemannZeta₁ w = B at hhw ⊢
    generalize (y : ℂ) ^ w = P at hhw ⊢
    generalize dslope (dslope (laHfun y) 1) 1 w = q at e2 ⊢
    generalize dslope (laHfun y) 1 w = D at e1 e2
    generalize laHfun y w = H at e1 hhw
    have key : (1 - (w - 1) * B) * (P / w) =
        y + (w - 1) * (((y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y)
          + (w - 1) * q) := by
      rw [← hhw]; linear_combination -e1 - (w - 1) * e2
    have lhs : -(-(w - 1)⁻¹ + B) * P / (w * (w - 1)) =
        (1 - (w - 1) * B) * (P / w) / (w - 1) ^ 2 := by
      field_simp
      ring
    rw [lhs, key]
    field_simp
    ring
end Formalism.ZF
