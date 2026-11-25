-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.lValEta_eq_lValEtaF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:34:03.743866+00:00
-- url     : https://prove2.me/submissions/530a7e14-0f0f-4490-906d-7f5cd5a2ca6f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_EulerFacMulConjInvSplit
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LValEtaEqLValEtaF
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Regroup_tprod_eq_of_fibre
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_Regroup_hasProd_fibre
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_multipliable_eulerFac


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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
namespace Formalism.HermitianLattices.Ext.L3
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)) (M : ℕ) (hM : 2 ≤ M) :
    Formalism.HermitianLatticesTheory.lValEta K M = lValEtaF K F M := by
  unfold Formalism.HermitianLatticesTheory.lValEta lValEtaF
  exact Regroup.tprod_eq_of_fibre
    (fun x : {P : Ideal (𝓞 K) // P.IsMaximal} =>
      (⟨x.1.comap (algebraMap (𝓞 F) (𝓞 K)), Regroup.comap_isMaximal x.2⟩ :
        {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}))
    (multipliable_eulerFac hK M hM) (Regroup.hasProd_fibre hK hF M (by omega))
end Formalism.HermitianLattices.Ext.L3
