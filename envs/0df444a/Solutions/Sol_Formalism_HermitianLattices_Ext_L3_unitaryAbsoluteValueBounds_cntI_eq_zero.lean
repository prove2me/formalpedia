-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.cntI_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:08.765161+00:00
-- url     : https://prove2.me/submissions/1f4a2ffb-8ed2-495d-a500-0783878fbce9

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityField
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CntIOneOfNotMem
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_conjO_mem_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_sg_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
open NormLifting
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
theorem _root_.solution (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (j M : ℕ) {n : 𝓞 K}
    (hn : n ∉ extP K 𝔭 ^ 2) : cntI hF 𝔭 (j + 2) M n = 0 := by
  unfold cntI
  rw [Nat.card_eq_zero]
  left
  constructor
  rintro ⟨x, hx1, hx2⟩
  choose z hz hzx using hx1
  obtain rfl : (fun i => Ideal.Quotient.mk _ (z i)) = x := funext hzx
  simp only [sg_mk, ← map_mul, ← map_sum] at hx2
  rw [Ideal.Quotient.eq] at hx2
  have h1 : ∑ i, conjO K (z i) * z i - n ∈ extP K 𝔭 ^ 2 := Ideal.pow_le_pow_right (by omega) hx2
  have h2 : ∑ i, conjO K (z i) * z i ∈ extP K 𝔭 ^ 2 := by
    refine sum_mem fun i _ => ?_
    rw [sq]
    refine Ideal.mul_mem_mul ?_ (hz i)
    have := idealPowerSpanBounds.conjO_mem_pow hF 𝔭 1 (z i) (by rw [pow_one]; exact hz i)
    rwa [pow_one] at this
  apply hn
  have := sub_mem h2 h1
  rwa [sub_sub_cancel] at this
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
