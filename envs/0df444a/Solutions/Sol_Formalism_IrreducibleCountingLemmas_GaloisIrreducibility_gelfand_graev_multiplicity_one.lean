-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.gelfand_graev_multiplicity_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:27:10.035182+00:00
-- url     : https://prove2.me/submissions/85dd568b-7752-40a0-9134-f2ca4e606a98

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_MemBesselSetZeroIffUpperTriangular
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_hecke_comm
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_gelfand_trick
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_besselSpace_zero_eq_equivariant
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_bruhat_exists
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_GTAlt_transfer
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_flipG_mul
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_flipG_flipG
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_flip_char
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_flip_mono
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_mono_not_adm
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Finset Matrix
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : GelfandGraevMultOne := by
  intro K V _ _ _ _ _ N ψ₀ ρ hψ hirr
  classical
  have : Fintype (GL (Fin N) K) := Fintype.ofFinite _
  rw [besselSpace_zero_eq_equivariant]
  refine gelfand_trick ρ (uniSub K N) (uniChar ψ₀ N) ?_ hirr
  refine hecke_comm flipG flipG_mul flipG_flipG (uniSub K N) (uniChar ψ₀ N) (flip_char ψ₀) ?_
  intro g
  obtain ⟨u, u', hu, hu', π, t, ht, hn⟩ := bruhat_exists g
  refine GTAlt.transfer flipG flipG_mul (uniSub K N) (uniChar ψ₀ N) (flip_char ψ₀) ⟨u, hu⟩ ⟨u', hu'⟩
    g ?_
  by_cases hadm : MonoAdm π t
  · left
    refine ⟨1, 1, ?_, by simp⟩
    rw [flip_mono _ π t hn hadm]
    simp
  · right
    exact mono_not_adm ψ₀ hψ _ π t ht hn hadm
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
