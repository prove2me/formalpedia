-- Prove2me | solution 1 for Formalism.DV.GaussP.length_residue
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:09.381617+00:00
-- url     : https://prove2.me/submissions/9ff1c182-b424-4db0-84d0-e167b974aaa0

import Definitions.Def_Formalism_GaussIdealIdentity_StatementLA
import Definitions.Def_Formalism_GaussIdealIdentity_GaussIdealPrimality_GaussLocalizationLengthHolds
import Theorems.Thm_Formalism_DV_GaussP_maximalIdeal_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial IsLocalRing
noncomputable section
open Formalism Formalism.DV Formalism.DV.GaussP
variable (σ O : Type) [Fintype σ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable [(gaussIdeal σ O).IsPrime]
local notation "A" => Localization.AtPrime (gaussIdeal σ O)
namespace Formalism.DV.GaussP
theorem _root_.solution :
    Module.length A (A ⧸ (IsLocalRing.maximalIdeal O).map (algebraMap O A)) = 1 := by
  rw [← maximalIdeal_eq σ O]
  exact Module.length_eq_one_iff.2 (isSimpleModule_iff_isCoatom.2
    (Ideal.isMaximal_def.1 (inferInstance : (IsLocalRing.maximalIdeal A).IsMaximal)))
end Formalism.DV.GaussP
