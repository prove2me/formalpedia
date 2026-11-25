-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.cntI_one_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:23:36.526801+00:00
-- url     : https://prove2.me/submissions/e16887ce-36a6-4765-8f76-e0a190914bfd

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityField
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CntIOneOfNotMem
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_eq_zero_of_inQ_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
open NormLifting
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
theorem _root_.solution (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (M : ℕ) {n : 𝓞 K}
    (hn : n ∉ extP K 𝔭) : cntI hF 𝔭 1 M n = 0 := by
  unfold cntI
  rw [Nat.card_eq_zero]
  left
  constructor
  rintro ⟨x, hx1, hx2⟩
  apply hn
  have h0 : ∑ i, sg hF 𝔭 1 (x i) * x i = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [eq_zero_of_inQ_one (hx1 i), mul_zero]
  rw [h0] at hx2
  have := Ideal.Quotient.eq_zero_iff_mem.1 hx2.symm
  rwa [pow_one] at this
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
