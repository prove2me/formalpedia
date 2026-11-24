-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.dimSq_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:03:16.241198+00:00
-- url     : https://prove2.me/submissions/82bfbd99-d2be-401b-a072-1b086df4cc40

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_charFacts

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
open CharacterLemmas
namespace Formalism.IndefR.LatticeTransfer
theorem _root_.solution (h : Schur) : DimSq := by
  intro K _ _ G _ _ S T _ _ _ τ hgood s
  obtain ⟨-, -, hsum⟩ := h K G S T τ hgood
  have hs := hsum s
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := by
    first
    | exact inferInstance
    | exact ⟨(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := K)).toRingHom⟩
  have hdim : charOf (τ s) 1 = (finrank K (T s) : K) := by
    unfold charOf
    rw [map_one, LinearMap.trace_one]
  have hterm : ∀ x : G, σ (charOf (τ s) x⁻¹ * charOf (τ s) x) =
      ((‖σ (charOf (τ s) x)‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [map_mul, ((charFacts K G (T s) (τ s) x).2 σ).1]
    push_cast
    exact Complex.conj_mul' _
  have e1 := congrArg σ hs
  rw [map_sum, map_natCast] at e1
  simp_rw [hterm] at e1
  have e2 : (∑ x : G, ‖σ (charOf (τ s) x)‖ ^ 2 : ℝ) = (Fintype.card G : ℝ) := by
    exact_mod_cast e1
  have key : ((finrank K (T s) : ℝ)) ^ 2 ≤ (Fintype.card G : ℝ) := by
    rw [← e2]
    have h1 : ‖σ (charOf (τ s) 1)‖ ^ 2 = ((finrank K (T s) : ℝ)) ^ 2 := by
      rw [hdim, map_natCast, Complex.norm_natCast]
    rw [← h1]
    exact Finset.single_le_sum (f := fun x : G => ‖σ (charOf (τ s) x)‖ ^ 2)
      (fun x _ => by positivity) (Finset.mem_univ 1)
  have key' : finrank K (T s) ^ 2 ≤ Fintype.card G := by exact_mod_cast key
  refine ⟨key', fun H χ => le_trans ?_ key'⟩
  exact Nat.pow_le_pow_left (Submodule.finrank_le _) 2
end Formalism.IndefR.LatticeTransfer
