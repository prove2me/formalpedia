-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.locBasic_locS_sup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:46.123506+00:00
-- url     : https://prove2.me/submissions/f75b66d2-e9f0-4044-ac47-82bf9b21be21

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_mem_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R K V : Type*} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (S : Submonoid R) (hS : ∀ s ∈ S, algebraMap R K s ≠ 0)
    (L M : Submodule R V) : locS S (L ⊔ M) = locS S L ⊔ locS S M := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.mp hx
    obtain ⟨l, hl, m, hm, hlm⟩ := Submodule.mem_sup.mp hsx
    have ha := hS s hs
    have key : ∀ v : V, s • ((algebraMap R K s)⁻¹ • v) = v := fun v => by
      rw [← algebraMap_smul K s ((algebraMap R K s)⁻¹ • v), smul_smul, mul_inv_cancel₀ ha,
        one_smul]
    have hx' : x = (algebraMap R K s)⁻¹ • l + (algebraMap R K s)⁻¹ • m := by
      rw [← smul_add, hlm, ← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ ha, one_smul]
    rw [hx']
    refine Submodule.add_mem_sup ?_ ?_
    · exact locBasic_mem_locS.mpr ⟨s, hs, by rw [key]; exact hl⟩
    · exact locBasic_mem_locS.mpr ⟨s, hs, by rw [key]; exact hm⟩
  · exact sup_le (locBasic_locS_mono S le_sup_left) (locBasic_locS_mono S le_sup_right)
end Formalism.HermitianLatticesTheory
