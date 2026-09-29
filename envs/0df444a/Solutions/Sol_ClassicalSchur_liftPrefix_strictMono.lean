-- Prove2me | solution 1 for ClassicalSchur.liftPrefix_strictMono
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-26T21:34:22.460007+00:00
-- url     : https://prove2.me/submissions/f1f1098d-c5e6-4724-a63d-93bf36893909

-- Generated from lean/ClassicalSchur/Lift.lean
--   imports : 0 platform node(s), 1 definition bundle(s)
--   inlined : 0 file-scoped / sub-threshold helper(s)
--   rename  : liftPrefix_strictMono -> solution, hoisted out of the namespace
import Definitions.Def_ClassicalSchurLift
import Mathlib



open ClassicalSchur in
theorem solution {m₁ M : ℕ} (hm₁ : 0 < m₁) (hM : m₁ ≤ M) :
    StrictMono (liftPrefix m₁ M) := by
  refine strictMono_nat_of_lt_succ fun L => ?_
  have hdm : L % m₁ + m₁ * (L / m₁) = L := Nat.mod_add_div L m₁
  have hmod : L % m₁ < m₁ := Nat.mod_lt L hm₁
  unfold liftPrefix
  rcases Nat.lt_or_ge (L % m₁ + 1) m₁ with h | h
  · obtain ⟨h1, h2⟩ := (Nat.div_mod_unique hm₁).2
      ⟨(by omega : L % m₁ + 1 + m₁ * (L / m₁) = L + 1), h⟩
    rw [h1, h2]
    omega
  · obtain ⟨h1, h2⟩ := (Nat.div_mod_unique hm₁).2
      ⟨(by rw [Nat.mul_add_one]; omega : 0 + m₁ * (L / m₁ + 1) = L + 1), hm₁⟩
    rw [h1, h2, Nat.mul_add_one]
    omega
