-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.LIOrb.card_quot_inf_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:18:38.564331+00:00
-- url     : https://prove2.me/submissions/7476bb9e-618a-4aa1-9737-b5715404ba75

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardEqRelIndex
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotInfNeZero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_IA_card_eq_relIndex
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_IA_exists_pow_smul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_IA_relIndex_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.LIOrb
theorem _root_.solution {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₂ : Submodule.IsLattice K M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    Nat.card (↥(locF 𝔭 M₁) ⧸ (locF 𝔭 M₁ ⊓ locF 𝔭 M₂).submoduleOf (locF 𝔭 M₁)) ≠ 0 := by
  obtain ⟨r, hr⟩ := IA.exists_pow_smul h𝔭 hM₁ hM₂
  rw [IA.card_eq_relIndex h𝔭 hr]
  exact IA.relIndex_ne_zero hM₁ hM₂ 𝔭
end Formalism.HermitianLattices.Ext.L3.LIOrb
