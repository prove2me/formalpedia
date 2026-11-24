-- Prove2me | solution 1 for Formalism.L2.G.Cmp.stabStd_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:10:58.353862+00:00
-- url     : https://prove2.me/submissions/44da8c7a-1e4e-492c-ace3-b4c88e079c85

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_ComparisonMaps_ClsLat
import Theorems.Thm_Formalism_L2_G_Cmp_gMap_std_le
import Theorems.Thm_Formalism_L2_G_Cmp_mem_stabStd
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp
open Formalism.MainNotions.G Matrix
variable (W : Type) {Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ}
namespace Formalism.L2.G.Cmp
theorem _root_.solution (g : GL (Fin k) Qq) : g ∈ stabStd (k := k) (Qq := Qq) W ↔
    (∀ a b, (g : Matrix (Fin k) (Fin k) Qq) a b ∈ (algebraMap W Qq).range) ∧
      ∀ a b, ((g⁻¹ : GL (Fin k) Qq) : Matrix (Fin k) (Fin k) Qq) a b ∈ (algebraMap W Qq).range := by
  rw [mem_stabStd]
  constructor
  · intro h
    have h' : g⁻¹ ∈ stabStd (k := k) (Qq := Qq) W := inv_mem ((mem_stabStd W g).2 h)
    rw [mem_stabStd] at h'
    exact ⟨(gMap_std_le W g).1 h.le, (gMap_std_le W g⁻¹).1 h'.le⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm ((gMap_std_le W g).2 h1) ?_
    have mono : ∀ {A B : Submodule W (Fin k → Qq)}, A ≤ B → gMap W g A ≤ gMap W g B :=
      fun hAB => Submodule.map_mono hAB
    have h3 := mono ((gMap_std_le W g⁻¹).2 h2)
    rwa [← gMap_mul, mul_inv_cancel, gMap_one] at h3
end Formalism.L2.G.Cmp
