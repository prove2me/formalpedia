-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.eArith_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:49.933722+00:00
-- url     : https://prove2.me/submissions/464976cc-95a6-4f33-99f8-a379f19ebc59

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Finset
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution : ∀ (s : ℕ) (ka : ℕ → ℤ) (β : ℕ → ℕ) (c : ℤ),
    (∀ i, i + 1 < s → ka (i + 1) + β (i + 1) ≤ ka i) → (0 < s → ka 0 + β 0 ≤ c) →
    (∑ a ∈ range s, (β a : ℤ)) ≤
      (c - (∑ a ∈ range s, (β a : ℤ)) + 1) * (∑ a ∈ range s, (β a : ℤ)) - (∑ a ∈ range s, (β a : ℤ) * ka a) +
        ∑ b ∈ range s, ∑ a ∈ range b, ((β a : ℤ) + 1) * (β b : ℤ) := by
  intro s ka β c h1 h2
  have key : ∀ a, a < s → ka a + ∑ a' ∈ range (a + 1), (β a' : ℤ) ≤ c := by
    intro a
    induction a with
    | zero =>
      intro ha
      simpa using h2 ha
    | succ a ih =>
      intro ha
      have h3 := h1 a ha
      have h4 := ih (by omega)
      rw [Finset.sum_range_succ]
      linarith
  clear h2
  induction s with
  | zero => simp
  | succ s ihs =>
    have IH := ihs (fun i hi => h1 i (by omega)) (fun a ha => key a (by omega))
    have hk := key s (by omega)
    rw [Finset.sum_range_succ] at hk
    have hinner : ∑ a ∈ range s, ((β a : ℤ) + 1) * (β s : ℤ) = (∑ a ∈ range s, (β a : ℤ) + s) * β s := by
      rw [← Finset.sum_mul, Finset.sum_add_distrib]
      simp
    simp only [Finset.sum_range_succ, hinner]
    have hb : (0 : ℤ) ≤ β s := Nat.cast_nonneg _
    have hs : (0 : ℤ) ≤ s := Nat.cast_nonneg _
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hk), mul_nonneg hb hs]
end Formalism.InvariantFactorPaths.L4
