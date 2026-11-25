-- Prove2me | solution 1 for Formalism.IndefR.Eqv.G5.adl_cocompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:11:56.417451+00:00
-- url     : https://prove2.me/submissions/f46b4fcc-444e-4448-adc1-69585b74f589

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL1_CompactFixesLattice_ExistsDenOfIsCompactAdele
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IntAdCpctOpen
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_LevelTypeEquivalence_AdlEqZeroOfMemNbhd
import Theorems.Thm_Formalism_IndefR_Eqv_G5_adl_inf_cocompact
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_algebraMap_mem_intAd
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_FiltrationBoundaryCriterion_CompactFixesLatticeTheory_exists_sub_mem_intAd
import Theorems.Thm_finiteAdeleIntegers_compactOpen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.IndefR Formalism.IndefR.Eqv Formalism.IndefR.Eqv.G5
variable {F : Type} [Field F] [NumberField F]
open scoped AdeleRing
namespace Formalism.IndefR.Eqv.G5
theorem _root_.solution : ∃ K : Set (AdeleRing (𝓞 F) F), IsCompact K ∧
    ∀ x, ∃ a : F, x - algebraMap F _ a ∈ K := by
  obtain ⟨C, hC, hCy⟩ := adl_inf_cocompact (F := F)
  refine ⟨C ×ˢ {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ v.adicCompletionIntegers F},
    hC.prod (finiteAdeleIntegers_compactOpen F).2, fun x => ?_⟩
  obtain ⟨u, hu⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_sub_mem_intAd x.2
  obtain ⟨r, hr⟩ := hCy (x.1 - algebraMap F _ u)
  refine ⟨u + r, ?_, ?_⟩
  · show x.1 - algebraMap F (InfiniteAdeleRing F) (u + r) ∈ C
    rw [map_add, ← sub_sub]
    exact hr
  · have : x.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) (u + r) =
        (x.2 - algebraMap F _ u) - algebraMap F _ (r : F) := by rw [map_add, sub_sub]
    show ∀ v, (x.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) (u + r)) v ∈ _
    rw [this]
    exact sub_mem hu (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.algebraMap_mem_intAd r)
end Formalism.IndefR.Eqv.G5
