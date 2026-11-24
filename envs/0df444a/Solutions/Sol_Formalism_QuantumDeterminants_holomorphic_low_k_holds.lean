-- Prove2me | solution 1 for Formalism.QuantumDeterminants.holomorphic_low_k_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:38:58.000097+00:00
-- url     : https://prove2.me/submissions/ab58aec6-2c63-4ee0-b53e-32c0f1de97c6

import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HalfSumRootsStandard
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_DSLowK
import Theorems.Thm_Formalism_QuantumDeterminants_dslowk_lowK_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
namespace Formalism.QuantumDeterminants
theorem _root_.solution : HolLowK := by
  intro n a b
  funext i
  rw [dslowk_lowK_eq]
  unfold rhoC
  have hA : ∀ j, epsHol n j = epsHol n i ↔ (j = 0 ↔ i = 0) := by
    intro j
    unfold epsHol
    first
      | simp
      | (simp; tauto)
  by_cases hi : i = 0
  · have c1 : (univ.filter fun j => i < j ∧ epsHol n j = epsHol n i).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _ h
      have hj : j = 0 := ((hA j).1 h.2).2 hi
      rw [hj, hi] at h
      exact lt_irrefl _ h.1
    have c2 : (univ.filter fun j => j < i ∧ epsHol n j = epsHol n i).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _ h
      rw [hi] at h
      exact Fin.not_lt_zero j h.1
    rw [c1, c2]
    subst hi
    simp [lamHol]
    try ring
  · have hi' : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext (by simpa using h))
    have e1 : (univ.filter fun j => i < j ∧ epsHol n j = epsHol n i) = univ.filter fun j => i < j := by
      refine Finset.filter_congr fun j _ => ?_
      rw [hA j]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, fun hj => absurd (hj ▸ h) (Fin.not_lt_zero i), fun h' => absurd h' hi⟩
    have e2 : (univ.filter fun j => j < i ∧ epsHol n j = epsHol n i) = Finset.Ioo 0 i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioo, hA j, hi, iff_false,
        Fin.lt_iff_val_lt_val, Fin.ext_iff, Fin.val_zero]
      first
        | omega
        | (constructor <;> intro h <;> omega)
    have c1 : (univ.filter fun j => i < j ∧ epsHol n j = epsHol n i).card + (i : ℕ) = n := by
      rw [e1, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
      have := i.isLt
      omega
    have c2 : (univ.filter fun j => j < i ∧ epsHol n j = epsHol n i).card + 1 = (i : ℕ) := by
      rw [e2, Fin.card_Ioo, Fin.val_zero]
      omega
    have r1 := congrArg (Nat.cast (R := ℝ)) c1
    have r2 := congrArg (Nat.cast (R := ℝ)) c2
    push_cast at r1 r2
    simp only [lamHol, hi, ↓reduceIte]
    push_cast
    linarith
end Formalism.QuantumDeterminants
