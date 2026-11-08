-- Prove2me | solution 1 for BauerleRiederMDP.NoArbitrage.eq_3_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:33:32.634181+00:00
-- url     : https://prove2.me/submissions/eb5a9857-a3ae-442d-b713-564d61566776

import Mathlib
import Definitions.Def_BauerleRiederMDP_NoArbitrage_FinancialMarket_relRisk
import Definitions.Def_BauerleRiederMDP_NoArbitrage_Portfolio_IsSelfFinancing

open MeasureTheory

open BauerleRiederMDP.NoArbitrage in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ}
    (M : FinancialMarket Ω P d) (φ : Portfolio M) (hφ : φ.IsSelfFinancing) :
    ∀ n, n < M.N → ∀ᵐ ω ∂P,
      φ.wealth (n + 1) ω = (1 + M.i (n + 1)) * (φ.wealth n ω + ∑ k, φ.φ n ω k * M.relRisk (n + 1) ω k) := by
  intro n hn
  have hi : 0 < 1 + M.i (n + 1) := by
    have := M.i_nonneg (n + 1) (by omega) (by omega)
    linarith
  have hW : ∀ᵐ ω ∂P, φ.wealth n ω = φ.φ0 n ω + ∑ k, φ.φ n ω k := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      exact Filter.Eventually.of_forall (fun ω => rfl)
    · exact hφ n h hn
  filter_upwards [hW] with ω hω
  rw [hω]
  show φ.φ0 n ω * (1 + M.i (n + 1)) + ∑ k, φ.φ n ω k * M.Rt (n + 1) ω k = _
  unfold FinancialMarket.relRisk
  have hk : ∀ k, (1 + M.i (n + 1)) * (φ.φ n ω k * (M.Rt (n + 1) ω k / (1 + M.i (n + 1)) - 1))
      = φ.φ n ω k * M.Rt (n + 1) ω k - (1 + M.i (n + 1)) * φ.φ n ω k := by
    intro k
    have := hi.ne'
    field_simp <;> ring
  rw [mul_add, mul_add, Finset.mul_sum (s := Finset.univ) (a := 1 + M.i (n + 1))
    (f := fun k => φ.φ n ω k * (M.Rt (n + 1) ω k / (1 + M.i (n + 1)) - 1)),
    Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring
