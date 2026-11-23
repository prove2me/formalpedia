-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.cntI_one_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:20.428073+00:00
-- url     : https://prove2.me/submissions/c6f843f2-3ee0-4f7b-b280-2a9c26f1f1f0

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityField
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CntIOneOfNotMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_eq_zero_of_inQ_one
import Theorems.Thm_Formalism_H_dualEquiv_apply
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
theorem _root_.solution (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (M : ℕ) {n : 𝓞 K}
    (hn : n ∈ extP K 𝔭) : cntI hF 𝔭 1 M n = 1 := by
  unfold cntI
  rw [Nat.card_eq_one_iff_unique]
  refine ⟨⟨fun x y => ?_⟩, ⟨⟨0, fun i => ⟨0, zero_mem _, map_zero _⟩, ?_⟩⟩⟩
  · apply Subtype.ext
    funext i
    rw [eq_zero_of_inQ_one (x.2.1 i), eq_zero_of_inQ_one (y.2.1 i)]
  · symm
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
    rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
    exact hn
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
