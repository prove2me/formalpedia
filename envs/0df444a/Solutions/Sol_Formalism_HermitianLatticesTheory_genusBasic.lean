-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusBasic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:00.629555+00:00
-- url     : https://prove2.me/submissions/8f1d3b74-e8c9-4789-9c47-95a777c12266

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_gmap_one
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_gmap_mul
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_symm
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_int
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusBasic_dual_le
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_mem_gmap
import Theorems.Thm_Formalism_HermitianLatticesTheory_isomAct_smul
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_mem_locS


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
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution : GenusBasic := by
  intro R K V _ _ _ _ _ _ _ _ _ _ h _ hstar
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hint_of : ∀ L : Submodule R V, IsUnimodular h L → IsIntegralLat h L := by
    intro L hL x hx y hy
    have hy' : y ∈ dual h L := by
      rw [show dual h L = L from hL]
      exact hy
    exact (dualBasic_mem_dual h L y).1 hy' x hx
  have hle_dual : ∀ L : Submodule R V, IsIntegralLat h L → L ≤ dual h L := by
    intro L hL y hy
    exact (dualBasic_mem_dual h L y).2 fun x hx => hL x hx y hy
  refine ⟨⟨fun L p hp => ⟨1, (isom h).one_mem, by rw [genusBasic_gmap_one]⟩,
    fun {L M} hLM => genusBasic_symm h L M hLM, fun {L M N} h1 h2 p hp => ?_⟩, ?_, ?_⟩
  · obtain ⟨g₁, hg₁, e₁⟩ := h1 p hp
    obtain ⟨g₂, hg₂, e₂⟩ := h2 p hp
    exact ⟨g₂ * g₁, (isom h).mul_mem hg₂ hg₁, by rw [genusBasic_gmap_mul, e₁, e₂]⟩
  · intro L g hg p hp
    refine ⟨g, hg, ?_⟩
    ext x
    simp only [loc, isomAct_mem_gmap, locBasic_mem_locS, isomAct_smul]
  · intro L M hL hM hLM
    have hML := genusBasic_symm h L M hLM
    refine ⟨⟨fun hU => ?_, fun hU => ?_⟩,
      ⟨genusBasic_int hinj hstar h L M hLM, genusBasic_int hinj hstar h M L hML⟩⟩
    · exact le_antisymm (genusBasic_dual_le hinj hstar h L M hL hLM hU)
        (hle_dual M (genusBasic_int hinj hstar h L M hLM (hint_of L hU)))
    · exact le_antisymm (genusBasic_dual_le hinj hstar h M L hM hML hU)
        (hle_dual L (genusBasic_int hinj hstar h M L hML (hint_of M hU)))
end Formalism.HermitianLatticesTheory
