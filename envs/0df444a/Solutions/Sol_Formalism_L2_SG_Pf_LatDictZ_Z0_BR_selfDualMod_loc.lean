-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.BR.selfDualMod_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:27:49.901817+00:00
-- url     : https://prove2.me/submissions/24ab2793-5eea-4e45-801b-80ec0fa9c499

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_UnimodOfSelfDual
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_hJ_symm
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_star_int
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_unimod_of_selfDual
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_StandardSymmetricSums_star_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_isSelfDualMod_loc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.BR
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA PIW.AdelClassFin
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.BR
theorem _root_.solution {J : Matrix (Fin n) (Fin n) E} (hJh : Formalism.UG.IsHerm (starRingEnd E) J)
    {L : Submodule (𝓞 E) (Fin n → E)} (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hL : SelfDual J L) {p : Ideal (𝓞 E)} (hp : p.IsMaximal) :
    IsSelfDualMod (locRing p) (hJ J) (Formalism.HermitianLatticesTheory.loc (K := E) p L).toAddSubgroup := by
  have hu := (Formalism.HermitianLatticesTheory.locDual (𝓞 E) E (Fin n → E) (hJ J) (hJ_symm hJh) star_int L hfg).2.1
    (unimod_of_selfDual hL) p hp
  exact isSelfDualMod_loc ⟨hfg, hsp⟩ hp.isPrime hu
end Formalism.L2.SG.Pf.LatDictZ.Z0.BR
