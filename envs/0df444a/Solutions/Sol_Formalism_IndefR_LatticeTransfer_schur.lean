-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.schur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:56:15.265809+00:00
-- url     : https://prove2.me/submissions/8fc9f1f1-15ff-4da5-90c2-8f1408beb34f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinrankIntSelf
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_IdempotentLemmas_eS_comm
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_IdempotentLemmas_trace_eS
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_IdempotentLemmas_sum_char_eq
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_IdempotentLemmas_finrank_int_self
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_IdempotentLemmas_int_eq_zero

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
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open IdempotentLemmas
namespace Formalism.IndefR.LatticeTransfer
theorem _root_.solution : Schur := by
  intro K _ _ G _ _ S T _ _ _ τ hgood
  obtain ⟨hnt, hirr, habs, hinj⟩ := hgood
  have hcomm : ∀ s t, ∃ c : K, eS (τ s) (τ t) = c • LinearMap.id := fun s t =>
    habs t _ (fun g => by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
      exact eS_comm (τ s) (τ t) g)
  have hdim : ∀ s, charOf (τ s) 1 = (finrank K (T s) : K) := fun s => by
    unfold charOf
    rw [map_one, LinearMap.trace_one]
  have hpos : ∀ s, (finrank K (T s) : K) ≠ 0 := fun s => by
    haveI := hnt s
    exact_mod_cast (Module.finrank_pos (R := K) (M := T s)).ne'
  have hcard : (Fintype.card G : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have htr : ∀ s t, LinearMap.trace K (T t) (eS (τ s) (τ t)) =
      (finrank K (T s) : K) * finrank K (Representation.IntertwiningMap (τ s) (τ t)) := by
    intro s t
    rw [trace_eS, sum_char_eq, hdim]
    field_simp
  have hone : ∀ s, finrank K (Representation.IntertwiningMap (τ s) (τ s)) = 1 := fun s => by
    haveI := hnt s
    exact finrank_int_self (τ s) (habs s)
  have hsum : ∀ s, ∑ x : G, charOf (τ s) x⁻¹ * charOf (τ s) x = (Fintype.card G : K) := by
    intro s
    rw [sum_char_eq, hone s, Nat.cast_one, mul_one]
  refine ⟨fun s => ?_, fun s t hst => ?_, hsum⟩
  · obtain ⟨c, hc⟩ := hcomm s s
    have h1 := htr s s
    rw [hc, map_smul, LinearMap.trace_id, smul_eq_mul, hone s, Nat.cast_one, mul_one] at h1
    have h2 : (c - 1) * (finrank K (T s) : K) = 0 := by rw [sub_mul, h1, one_mul, sub_self]
    have h3 : c = 1 := sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right (hpos s))
    rw [hc, h3, one_smul]
  · obtain ⟨c, hc⟩ := hcomm s t
    have hne : charOf (τ s) ≠ charOf (τ t) := fun h => hst (hinj s t h)
    haveI : Subsingleton (Representation.IntertwiningMap (τ s) (τ t)) :=
      ⟨fun f g => (int_eq_zero (τ s) (τ t) (hirr s) (hirr t) hne f).trans
        (int_eq_zero (τ s) (τ t) (hirr s) (hirr t) hne g).symm⟩
    have h1 := htr s t
    rw [hc, map_smul, LinearMap.trace_id, smul_eq_mul,
      Module.finrank_zero_of_subsingleton (R := K) (M := Representation.IntertwiningMap (τ s) (τ t)),
      Nat.cast_zero, mul_zero] at h1
    have h3 : c = 0 := (mul_eq_zero.1 h1).resolve_right (hpos t)
    rw [hc, h3, zero_smul]
end Formalism.IndefR.LatticeTransfer
