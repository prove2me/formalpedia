-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.ThirdPropositionSlot.absNorm_extP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:27:31.929802+00:00
-- url     : https://prove2.me/submissions/21a2b37b-3adb-4a9b-afe0-09d4a300963b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_StarAlgebraMap
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountEqEulerFacInert
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormRepCountExtP
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_absNorm_extP_eq_sq
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.ThirdPropositionSlot
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3.ThirdPropositionSlot
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) :
    Ideal.absNorm (extP K 𝔭) = Ideal.absNorm 𝔭 ^ 2 := by
  induction 𝔭 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => simp [extP]
  | h₂ x hx =>
    rw [Ideal.isUnit_iff.mp hx]
    simp only [extP]
    simp only [Ideal.map_top, Ideal.absNorm_top, one_pow]
  | h₃ a p ha hp ih =>
    have hpm : p.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hq := idealPowerSpanBounds.absNorm_extP_eq_sq hK hF hpm
    simp only [extP] at ih hq ⊢
    rw [Ideal.map_mul, map_mul, map_mul, ih, hq, mul_pow]
end Formalism.HermitianLattices.Ext.L3.ThirdPropositionSlot
