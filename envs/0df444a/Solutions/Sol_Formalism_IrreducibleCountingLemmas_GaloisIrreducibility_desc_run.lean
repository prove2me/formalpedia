-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.desc_run
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:13.77096+00:00
-- url     : https://prove2.me/submissions/4217ef14-2328-406e-9e5d-e4bba2af936f

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_MemBesselSetZeroIffUpperTriangular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {N : ℕ}
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (τ : Equiv.Perm (Fin N))
    (h : ∀ i j : Fin N, (j : ℕ) = i + 1 → τ j < τ i → (τ i : ℕ) = τ j + 1) :
    ∀ d : ℕ, ∀ i j : Fin N, (j : ℕ) = i + d → τ j < τ i → ∀ m : Fin N, i ≤ m → m ≤ j →
      (τ m : ℕ) + m = τ i + i := by
  intro d
  induction d with
  | zero =>
    intro i j hj hlt
    have : j = i := Fin.ext (by omega)
    rw [this] at hlt
    exact absurd hlt (lt_irrefl _)
  | succ d ih =>
    intro i j hj hlt m him hmj
    have hi' : (i : ℕ) + 1 < N := by have := j.2; omega
    set i' : Fin N := ⟨i + 1, hi'⟩ with hi'def
    have hi'v : (i' : ℕ) = i + 1 := rfl
    have hne : τ i' ≠ τ i := by
      intro h'
      have := τ.injective h'
      have := congrArg Fin.val this
      omega
    have hlt' : (τ j : ℕ) < τ i := hlt
    have him' : (i : ℕ) ≤ m := him
    have hmj' : (m : ℕ) ≤ j := hmj
    by_cases hmi : m = i
    · rw [hmi]
    have hmi' : (m : ℕ) ≠ i := fun h' => hmi (Fin.ext h')
    rcases lt_or_gt_of_ne hne with h1 | h1
    · have h2 := h i i' hi'v h1
      by_cases hji : j = i'
      · have : m = i' := Fin.ext (by rw [hji] at hmj'; omega)
        rw [this]; omega
      · have h3 : τ j ≠ τ i' := fun h' => hji (τ.injective h')
        have h3' : (τ j : ℕ) ≠ τ i' := fun h' => h3 (Fin.ext h')
        have h4 : τ j < τ i' := by
          show (τ j : ℕ) < τ i'
          omega
        have := ih i' j (by omega) h4 m (by show (i' : ℕ) ≤ m; omega) hmj
        omega
    · exfalso
      have h1' : (τ i : ℕ) < τ i' := h1
      have h4 : τ j < τ i' := lt_trans hlt h1
      have hall := ih i' j (by omega) h4
      have hjj := hall j (by show (i' : ℕ) ≤ j; omega) le_rfl
      have hm0 : (i' : ℕ) + ((τ i' : ℕ) - τ i) < N := by have := j.2; omega
      set m0 : Fin N := ⟨i' + ((τ i' : ℕ) - τ i), hm0⟩ with hm0def
      have hm0v : (m0 : ℕ) = i' + ((τ i' : ℕ) - τ i) := rfl
      have := hall m0 (by show (i' : ℕ) ≤ m0; omega) (by show (m0 : ℕ) ≤ j; omega)
      have h5 : τ m0 = τ i := Fin.ext (by omega)
      have h6 := congrArg Fin.val (τ.injective h5)
      omega
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
