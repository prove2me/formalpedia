-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.isotropic_to_standard_substitution_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:40:29.961631+00:00
-- url     : https://prove2.me/submissions/7d4d249f-3514-44cd-b22b-6eaf9d893a6e

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemC
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowInvariant
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCInv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_SelfConjugatePlaceSetting_inv_poly
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_subG_blkProd
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_ConjugatePairPlaceSetting_inv_poly


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution : IsotropicToStdSubstLineInvariant := by
  intro C _ V T r cc a Orb _ tau gm J _ X F gaC N L pl H n plc σ i i' hi t
  rw [subG_blkProd, map_prod]
  refine Finset.prod_congr rfl fun o _ => ?_
  rw [map_prod]
  exact Finset.prod_congr rfl fun j _ => H.inv_poly plc o _ _ σ i i' hi t
end Formalism.L2.FormalSeriesBounds.RF
