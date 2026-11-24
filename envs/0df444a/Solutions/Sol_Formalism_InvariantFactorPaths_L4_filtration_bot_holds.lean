-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.filtration_bot_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:19.350157+00:00
-- url     : https://prove2.me/submissions/502b6fa6-62b7-4153-bb8d-ae432f5bdd50

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : FilBot := by
  intro p _ K r _ LLw q J M ρ w e he
  rw [eq_bot_iff]
  intro f hf
  rw [Submodule.mem_bot]
  simp only [FilE, MMwZ, MMw, Y, Submodule.mem_inf, Submodule.restrictScalars_mem] at hf
  obtain ⟨⟨⟨⟨⟨hPol, _⟩, _⟩, _⟩, _⟩, hS⟩ := hf
  rw [Pol, mem_restrictSupport_iff] at hPol
  rw [mem_restrictSupport_iff] at hS
  ext m
  rw [coeff_zero]
  by_contra hne
  have h1 : MultiDeg LLw m := hPol (mem_support_iff.mpr hne)
  have h2 : e ≤ m (Fin.last K, ρ) := hS (mem_support_iff.mpr hne)
  have h3 : m (Fin.last K, ρ) ≤ ∑ c, m (Fin.last K, c) :=
    Finset.single_le_sum (f := fun c => m (Fin.last K, c)) (fun c _ => Nat.zero_le _) (Finset.mem_univ ρ)
  have h4 := h1 (Fin.last K)
  omega
end Formalism.InvariantFactorPaths.L4
