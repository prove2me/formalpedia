-- Prove2me | solution 1 for Formalism.REAL.CharId_sub_lsh_apply_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:34:03.343083+00:00
-- url     : https://prove2.me/submissions/cedc1ffc-7efa-4a6b-88ab-ed4f029939cb

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementC
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorPowUpperVanishHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CharId
import Theorems.Thm_Formalism_REAL_CharId_M_apply
import Theorems.Thm_Formalism_REAL_CharId_T_apply
import Theorems.Thm_Formalism_REAL_CharId_card
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Polynomial
noncomputable section
namespace Formalism.REAL
private theorem twistedAction_single_of_lt {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (v : V) (x t a : Fin n) (hta : t < a) :
    twistedAction E a t (Pi.single a v) x = (if x = a then E x t v else 0) - (if x = t then v else 0) := by
  rw [CharId_T_apply]
  by_cases hxa : x = a
  · subst hxa
    simp [ne_of_gt hta]
  · simp [Pi.single_apply, hxa]
end Formalism.REAL
end
end

set_option autoImplicit false
open Finset Polynomial
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ V) (ν : Fin n → ℂ) (v : V) (hv : IsHW E ν v) (t : Fin n) :
    (CharId_M E - algebraMap ℂ (Module.End ℂ (Fin n → V)) (lsh ν t)) (Pi.single t v) =
      ∑ a ∈ univ.filter (fun a => t < a), twistedAction E a t (Pi.single a v) := by
  funext x
  rw [Finset.sum_apply, Finset.sum_congr rfl
    (fun a ha => twistedAction_single_of_lt E v x t a (Finset.mem_filter.1 ha).2),
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_const]
  have hs : ∑ c, E x c ((Pi.single t v : Fin n → V) c) = E x t v := by
    rw [Finset.sum_eq_single t]
    · simp
    · intro c _ hc
      simp [Pi.single_apply, hc]
    · simp
  simp only [LinearMap.sub_apply, Module.algebraMap_end_apply, Pi.sub_apply, Pi.smul_apply,
    CharId_M_apply, hs, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases lt_trichotomy x t with h | h | h
  · simp [h.ne, not_lt.2 h.le, hv.2 x t h]
  · subst h
    rw [← Nat.cast_smul_eq_nsmul ℂ, CharId_card]
    simp [hv.1 x, lsh, add_smul, sub_smul]
  · simp [h.ne', h, Pi.single_apply]
end Formalism.REAL
