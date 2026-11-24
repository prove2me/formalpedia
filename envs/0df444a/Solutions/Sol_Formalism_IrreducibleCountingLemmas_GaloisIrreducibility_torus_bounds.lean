-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.torus_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:52:04.415105+00:00
-- url     : https://prove2.me/submissions/43d83abd-7d8d-4ed0-9d28-d493270db14f

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaLWeight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (g : ℕ) (hg : 2 ≤ g) (d : Multiset ℕ) : (∀ x ∈ d, 1 ≤ x) →
    0 < (d.map (fun x => (g : ℝ) ^ x - 1)).prod ∧
    (d.map (fun x => (g : ℝ) ^ x - 1)).prod ≤ (g : ℝ) ^ d.sum ∧
    (g : ℝ) ^ d.sum * (1 - (d.card : ℝ) / g) ≤ (d.map (fun x => (g : ℝ) ^ x - 1)).prod := by
  have hg' : (2 : ℝ) ≤ g := by exact_mod_cast hg
  induction d using Multiset.induction_on with
  | empty => intro _; simp
  | cons a s ih =>
    intro h
    obtain ⟨h1, h2, h3⟩ := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    have ha : 1 ≤ a := h a (Multiset.mem_cons_self a s)
    have hga : (g : ℝ) ≤ (g : ℝ) ^ a :=
      calc (g : ℝ) = (g : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (g : ℝ) ^ a := pow_le_pow_right₀ (by linarith) ha
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, Multiset.card_cons,
      pow_add]
    have hG : 0 < (g : ℝ) ^ s.sum := pow_pos (by linarith) _
    generalize (s.map (fun x => (g : ℝ) ^ x - 1)).prod = T at h1 h2 h3 ⊢
    generalize (g : ℝ) ^ s.sum = G at h2 h3 hG ⊢
    generalize (g : ℝ) ^ a = A at hga ⊢
    have hc : (0 : ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
    push_cast
    generalize (s.card : ℝ) = c at h3 hc ⊢
    refine ⟨mul_pos (by linarith) h1, ?_, ?_⟩
    · calc (A - 1) * T ≤ A * T := by nlinarith [h1]
        _ ≤ A * G := mul_le_mul_of_nonneg_left h2 (by linarith)
    · have hg0 : (g : ℝ) ≠ 0 := by linarith
      have e1 : (A - 1) * (G * (1 - c / g)) - A * G * (1 - (c + 1) / g)
          = G * ((A - g + c) / g) := by
        field_simp; ring
      have e2 : 0 ≤ G * ((A - g + c) / g) :=
        mul_nonneg hG.le (div_nonneg (by linarith) (by linarith))
      calc A * G * (1 - (c + 1) / g) ≤ (A - 1) * (G * (1 - c / g)) := by linarith
        _ ≤ (A - 1) * T := mul_le_mul_of_nonneg_left h3 (by linarith)
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
