-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatDictZ.Z0.LF.loc_le_of_denom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:05:10.272194+00:00
-- url     : https://prove2.me/submissions/df348116-ef7b-4d20-89fe-4e891974caf1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_LatDictZAbs
import Definitions.Def_Lemmata_Denominators_Denom
import Definitions.Def_Formalism_SelfDualUnimodular_LocalLatticeDictionary_LocFin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_conjIdeal_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_WA_mem_hcompl_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatDictZ Formalism.L2.SG.Pf.LatDictZ.Z0 Formalism.L2.SG.Pf.LatDictZ.Z0.LF
open ReciprocityTheory.ChartRestriction.L3 ReciprocityTheory.ChartRestriction.L3.WA
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
namespace Formalism.L2.SG.Pf.LatDictZ.Z0.LF
theorem _root_.solution {L M : Submodule (𝓞 E) (Fin n → E)} {N : ℕ} (hN : ∀ x ∈ L, (N : 𝓞 E) • x ∈ M)
    {p : Ideal (𝓞 E)} (hp : p.IsPrime) (hNp : (N : 𝓞 E) ∉ p) :
    Formalism.HermitianLatticesTheory.loc (K := E) p L ≤ Formalism.HermitianLatticesTheory.loc (K := E) p M := by
  rintro x ⟨t, ht, htx⟩
  have hNh : (N : 𝓞 E) ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) p := by
    rw [mem_hcompl_iff hp, mem_conjIdeal_iff, map_natCast]
    exact ⟨hNp, hNp⟩
  refine ⟨(N : 𝓞 E) * t, mul_mem hNh ht, ?_⟩
  rw [mul_smul]; exact hN _ htx
end Formalism.L2.SG.Pf.LatDictZ.Z0.LF
