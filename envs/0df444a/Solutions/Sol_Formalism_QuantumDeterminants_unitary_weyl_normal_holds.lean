-- Prove2me | solution 1 for Formalism.QuantumDeterminants.unitary_weyl_normal_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:05.007309+00:00
-- url     : https://prove2.me/submissions/afc7542c-9649-4a9e-8000-f8c5c94f7022

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_nset_iff
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_block
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uw_inv
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_conj_col
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_ell_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open WeylGroupFacts
namespace Formalism.QuantumDeterminants
theorem _root_.solution : UWNormal := by
  unfold UWNormal
  intro k r z hz h hh g hg
  have hg' := (nset_iff g).1 hg
  have hinv := uw_inv hh
  have hb := uw_block hh
  have hb' := uw_block hinv
  have hU : h ∈ UH (Hpk k r) := by
    simp only [UWset, Set.mem_setOf_eq] at hh
    exact hh.1
  have hUi : h⁻¹ ∈ UH (Hpk k r) := by
    simp only [UWset, Set.mem_setOf_eq] at hinv
    exact hinv.1
  have hzi : h⁻¹ *ᵥ z = z := by
    simp only [UWset, Set.mem_setOf_eq] at hinv
    exact hinv.2.2
  have hd := isUnit_of_uh hU
  exact ⟨(nset_iff _).2 ⟨uh_mul (uh_mul hU hg'.1) hUi,
    conj_col hb hb' (Matrix.mul_nonsing_inv h hd) hg'.2⟩, ell_conj z hb hb' hzi⟩
end Formalism.QuantumDeterminants
