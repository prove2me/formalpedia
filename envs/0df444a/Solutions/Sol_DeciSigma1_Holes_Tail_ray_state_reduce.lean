-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.ray_state_reduce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:52:36.234964+00:00
-- url     : https://prove2.me/submissions/9992e9bb-3e92-4d93-8d2b-7e0d5fbabf01

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Theorems.Thm_DeciSigma1_Holes_Tail_rayState_loop
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_cons_cons
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_nil
public import Theorems.Thm_DeciSigma1_Arithmetic_DifferenceSystem_weight_singleton
public import Theorems.Thm_DeciSigma1_Automata_mem_wordsUpTo
public import Theorems.Thm_DeciSigma1_Words_IsConjugate_symm
public import Theorems.Thm_DeciSigma1_Words_PeriodicFrom_add_mul
public import Theorems.Thm_DeciSigma1_Words_Ray_length_suffixBeforeOnset
public import Theorems.Thm_DeciSigma1_Words_length_suffixOfLength
public import Theorems.Thm_DeciSigma1_runFrom_cons
public import Theorems.Thm_DeciSigma1_runFrom_nil
public import Theorems.Thm_DeciSigma1_runFrom_snoc
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_cons_cons
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_nil
attribute [local simp] DeciSigma1.Arithmetic.DifferenceSystem.weight_singleton
attribute [local simp] DeciSigma1.Automata.mem_wordsUpTo
attribute [local simp] DeciSigma1.Words.Ray.length_suffixBeforeOnset
attribute [local simp] DeciSigma1.Words.length_suffixOfLength
attribute [local simp] DeciSigma1.runFrom_cons
attribute [local simp] DeciSigma1.runFrom_nil
attribute [local simp] DeciSigma1.runFrom_snoc



set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
open DeciSigma1.Arithmetic DeciSigma1.Words DeciSigma1.Automata
variable {ι : Type}
variable (M : StructuralReader α S k)
variable {M}
variable [DecidableEq α] [Fintype S]
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (q : S) (Ω : Ray α) (a : ℕ) :
    ∃ a', a' ≤ a ∧ a' < rayHorizon S Ω ∧ rayState M q Ω a' = rayState M q Ω a ∧
      ∀ t, Ω.stream (a' + t) = Ω.stream (a + t) := by
  classical
  by_cases hlt : a < rayHorizon S Ω
  · exact ⟨a, le_rfl, hlt, rfl, fun _ => rfl⟩
  unfold rayHorizon at hlt ⊢
  have hν : 0 < Ω.period := Ray.period_pos
  have hper : PeriodicFrom Ω.stream Ω.onset Ω.period := (Ray.leastStreamPeriod_shift le_rfl).2.1
  -- pigeonhole on (state, phase) over the cuts `A, …, A + N ν`
  let f : Fin (Fintype.card S * Ω.period + 1) → S × Fin Ω.period := fun m =>
    (rayState M q Ω (Ω.onset + m), ⟨m % Ω.period, Nat.mod_lt _ hν⟩)
  have hcard : Fintype.card (S × Fin Ω.period) <
      Fintype.card (Fin (Fintype.card S * Ω.period + 1)) := by
    simp [Fintype.card_prod]
  obtain ⟨m₁, m₂, hne, he⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  obtain ⟨x, d, hxA, hd, hxd, hdν, hst⟩ : ∃ x d, Ω.onset ≤ x ∧ 0 < d ∧
      x + d ≤ Ω.onset + Fintype.card S * Ω.period ∧ Ω.period ∣ d ∧
      rayState M q Ω (x + d) = rayState M q Ω x := by
    have hs := congrArg Prod.fst he
    have hp := congrArg (fun z => (z.2 : ℕ)) he
    simp only [f] at hs hp
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · refine ⟨Ω.onset + m₁, m₂ - m₁, by omega, by omega, by have := m₂.isLt; omega,
        (Nat.modEq_iff_dvd' h.le).mp hp, ?_⟩
      rw [show Ω.onset + m₁ + (m₂ - m₁) = Ω.onset + m₂ by omega]; exact hs.symm
    · refine ⟨Ω.onset + m₂, m₁ - m₂, by omega, by omega, by have := m₁.isLt; omega,
        (Nat.modEq_iff_dvd' h.le).mp hp.symm, ?_⟩
      rw [show Ω.onset + m₂ + (m₁ - m₂) = Ω.onset + m₁ by omega]; exact hs
  obtain ⟨c, rfl⟩ := hdν
  have hshift : ∀ s, Ω.stream (x + Ω.period * c + s) = Ω.stream (x + s) := by
    intro s
    have := hper.add_mul (x - Ω.onset + s) c
    rw [show Ω.onset + (x - Ω.onset + s) + c * Ω.period = x + Ω.period * c + s by
      rw [show Ω.onset + (x - Ω.onset + s) = x + s by omega]; ring,
      show Ω.onset + (x - Ω.onset + s) = x + s by omega] at this
    exact this
  have hloop := rayState_loop q Ω hst hshift
  have hdiv := Nat.mod_add_div (a - x) (Ω.period * c)
  have hmodlt := Nat.mod_lt (a - x) hd
  refine ⟨x + (a - x) % (Ω.period * c), by omega, by omega, ?_, ?_⟩
  · have := hloop ((a - x) / (Ω.period * c)) ((a - x) % (Ω.period * c))
    rw [this.symm]
    congr 1
    rw [mul_comm ((a - x) / (Ω.period * c))]; omega
  · intro t
    have key :=
        hper.add_mul (x - Ω.onset + (a - x) % (Ω.period * c) + t) (c * ((a - x) / (Ω.period * c)))
    rw [show Ω.onset + (x - Ω.onset + (a - x) % (Ω.period * c) + t) = x + (a - x) %
        (Ω.period * c) + t by
      omega] at key
    rw [← key]
    congr 1
    rw [show c * ((a - x) / (Ω.period * c)) * Ω.period = Ω.period * c * ((a - x) /
        (Ω.period * c)) by ring]
    omega
end DeciSigma1.Holes.Tail
