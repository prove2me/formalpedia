-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.genusCovol_claimB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:55.668806+00:00
-- url     : https://prove2.me/submissions/90cea386-8aee-46c8-91be-4ce658608314

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_DefsCS
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusScale
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovolBound
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusCovol
import Theorems.Thm_Formalism_HermitianLatticesTheory_genusCovol_pigeon

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (P Q : Ideal R) [P.IsPrime] [Q.IsPrime] {a : R} (haP : a ∈ P)
    (haQ : a ∉ Q) {X Y : Submodule R W}
    (hfin : X.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0) :
    locS Q.primeCompl Y ≤ locS Q.primeCompl (Y ⊓ locS P.primeCompl X) := by
  rintro y' ⟨t, ht, hty⟩
  obtain ⟨m, k, hk, hmk⟩ := genusCovol_pigeon hfin a hty
  refine ⟨a ^ m * t, ?_, ?_, ?_⟩
  · intro hmem
    rcases (Ideal.IsPrime.mem_or_mem inferInstance hmem) with h1 | h1
    · exact haQ (Ideal.IsPrime.mem_of_pow_mem inferInstance _ h1)
    · exact ht h1
  · rw [mul_smul]
    exact Y.smul_mem _ hty
  · refine ⟨1 - a ^ k, ?_, ?_⟩
    · intro hmem
      have h1 : a ^ k ∈ P := P.pow_mem_of_mem haP k hk
      have : (1 : R) ∈ P := by simpa using P.add_mem hmem h1
      exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one P).mpr this)
    · have e : (1 - a ^ k) • (a ^ m * t) • y' = a ^ m • (t • y') - a ^ (m + k) • (t • y') := by
        rw [sub_smul, one_smul, smul_smul, smul_smul, smul_smul, pow_add]
        congr 2
        ring
      rw [e]
      exact hmk
end Formalism.HermitianLatticesTheory
