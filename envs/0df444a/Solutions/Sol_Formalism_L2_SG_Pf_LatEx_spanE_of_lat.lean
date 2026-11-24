-- Prove2me | solution 1 for Formalism.L2.SG.Pf.LatEx.spanE_of_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:18:43.214367+00:00
-- url     : https://prove2.me/submissions/946bcaf2-7d6b-4295-9988-2ea8d64812b9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsDefs
import Definitions.Def_Lemmata_MiscLemmasD_Imports
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_HaarTransversals_UnitaryHaarProducts_LatExistsSat

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
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.LatEx
variable {E V : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
  [IsScalarTower (𝓞 E) E V]
local notation "𝓕" => FractionalIdeal (nonZeroDivisors (𝓞 E)) E
namespace Formalism.L2.SG.Pf.LatEx
theorem _root_.solution {ι : Type} (N : Submodule (𝓞 E) V) (g : ι → V) (Y : Submodule E V)
    (hNY : N ≤ Y.restrictScalars (𝓞 E)) (hY : Y ≤ Submodule.span E (Set.range g))
    (hg : ∀ i, ∃ t : E, t ≠ 0 ∧ t • g i ∈ N) : Submodule.span E (N : Set V) = Y := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact hNY hx
  · refine hY.trans ?_
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨t, ht, hti⟩ := hg i
    have h : g i = t⁻¹ • (t • g i) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
    rw [SetLike.mem_coe, h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hti)
end Formalism.L2.SG.Pf.LatEx
