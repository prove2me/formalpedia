-- Prove2me | solution 1 for Formalism.L2.SG.Pf.WuDec.tens_update_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:41:12.602438+00:00
-- url     : https://prove2.me/submissions/188c8bf7-9f55-4cda-a603-562f7adbd364

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_TensInt
import Theorems.Thm_Formalism_L2_SG_Pf_WuDec_inner_tens_update

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.WuDec
variable {ι : Type} [Fintype ι] {V : ι → Type} [∀ v, NormedAddCommGroup (V v)] [∀ v, InnerProductSpace ℂ (V v)]
  {Vπ : Type} [NormedAddCommGroup Vπ] [InnerProductSpace ℂ Vπ] {tens : (∀ v, V v) → Vπ}
namespace Formalism.L2.SG.Pf.WuDec
theorem _root_.solution [DecidableEq ι] (hi : ∀ x y, ⟪tens x, tens y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ) (ξ : ∀ v, V v)
    (v : ι) (hne : ∀ w, w ≠ v → ξ w ≠ 0) (a b : V v)
    (h : tens (Function.update ξ v a) = tens (Function.update ξ v b)) : a = b := by
  have hP : ∏ w ∈ Finset.univ.erase v, ⟪ξ w, ξ w⟫_ℂ ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro w hw
    exact inner_self_ne_zero.mpr (hne w (Finset.ne_of_mem_erase hw))
  have e : ∀ p q : V v, ⟪tens (Function.update ξ v p), tens (Function.update ξ v q)⟫_ℂ =
      ⟪p, q⟫_ℂ * ∏ w ∈ Finset.univ.erase v, ⟪ξ w, ξ w⟫_ℂ :=
    fun p q => inner_tens_update hi ξ v p q
  have h0 : ⟪tens (Function.update ξ v a) - tens (Function.update ξ v b),
      tens (Function.update ξ v a) - tens (Function.update ξ v b)⟫_ℂ = 0 := by
    rw [h, sub_self, inner_zero_left]
  rw [inner_sub_left, inner_sub_right, inner_sub_right, e, e, e, e] at h0
  have key : ⟪a - b, a - b⟫_ℂ * ∏ w ∈ Finset.univ.erase v, ⟪ξ w, ξ w⟫_ℂ = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    linear_combination h0
  exact sub_eq_zero.mp (inner_self_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hP))
end Formalism.L2.SG.Pf.WuDec
