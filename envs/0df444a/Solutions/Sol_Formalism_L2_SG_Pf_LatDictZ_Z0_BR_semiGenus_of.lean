-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.BR.semiGenus_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:47:41.549562+00:00
-- url     : https://prove2.me/submissions/bdae5e13-0bba-4fa8-bb50-8a494bb8953c

import Mathlib
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_UnimodOfSelfDual
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_AlgebraMapNeZero
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_loc_iff_of_isom
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_gl_of_isom
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_hJ_nondeg
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_hJ_symm
import Theorems.Thm_Formalism_L2_SG_Pf_LatDictZ_Z0_BR_selfDualMod_loc


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
theorem _root_.solution (hG : SemiGenusLoc) : SemiGenus := by
  intro E _ _ _ n J hK hJh hdet L M hLfg hMfg hLsp hMsp hLd hMd p hp
  obtain ⟨g, hg, hm⟩ := hG E (Fin n → E) (hJ J) hK (hJ_symm hJh) (hJ_nondeg hdet) p hp
    (Formalism.HermitianLatticesTheory.loc (K := E) p L).toAddSubgroup (Formalism.HermitianLatticesTheory.loc (K := E) p M).toAddSubgroup
    (selfDualMod_loc hJh hLfg hLsp hLd hp) (selfDualMod_loc hJh hMfg hMsp hMd hp)
  obtain ⟨γ, hγ, hγg⟩ := gl_of_isom g hg
  exact ⟨γ, hγ, loc_iff_of_isom g hm γ hγg⟩
end Formalism.L2.SG.Pf.LatDictZ.Z0.BR
