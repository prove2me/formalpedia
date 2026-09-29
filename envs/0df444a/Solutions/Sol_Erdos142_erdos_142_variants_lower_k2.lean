-- Prove2me | solution 1 for Erdos142.erdos_142_variants_lower_k2
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-24T04:07:49.098661+00:00
-- url     : https://prove2.me/submissions/89fbb871-ffa8-48b0-b21f-0a7b00894600

import Mathlib
import Definitions.Def_Erdos142Basic

set_option autoImplicit false

open Filter
open Topology
open Erdos142

namespace Erdos142K2

/-- A 2-AP-free finite set of naturals has at most one element: any two
distinct elements `a < b` form the 2-term progression `{a, a + (b - a)}`. -/
theorem card_le_one_of_free {S : Finset ℕ}
    (hfree : Erdos142.IsAPOfLengthFree (S : Set ℕ) (2:ℕ)) : S.card ≤ 1 := by
  by_contra h
  have h1 : 1 < S.card := by omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h1
  have key : ∀ a ∈ S, ∀ b ∈ S, a < b → False := by
    intro a ha b hb hab
    have htsub : ({a, b} : Set ℕ) ⊆ (S : Set ℕ) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact Finset.mem_coe.mpr ha
      · exact Finset.mem_coe.mpr hb
    have hAP : Erdos142.IsAPOfLength ({a, b} : Set ℕ) ((2:ℕ):ℕ∞) := by
      refine ⟨a, b - a, ?_, ?_⟩
      · rw [Nat.cast_ofNat, ENat.card_coe_set_eq]
        exact Set.encard_pair (ne_of_lt hab)
      · ext z
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_ofPred_eq]
        constructor
        · rintro (rfl | rfl)
          · exact ⟨0, ENat.natCast_lt_natCast.mpr (by norm_num), by simp⟩
          · refine ⟨1, ENat.natCast_lt_natCast.mpr (by norm_num), ?_⟩
            rw [one_smul]
            exact Nat.add_sub_cancel' (le_of_lt hab)
        · rintro ⟨n, hn, rfl⟩
          have hn2 : n < 2 := ENat.natCast_lt_natCast.mp hn
          interval_cases n
          · left; simp
          · right; rw [one_smul]; exact Nat.add_sub_cancel' (le_of_lt hab)
    have hle := hfree _ htsub hAP
    rw [← Nat.cast_one, ENat.natCast_le_natCast] at hle
    omega
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · exact key x hx y hy hlt
  · exact key y hy x hx hlt

/-- `r 2 N ≤ 1`: `r` is the sSup of admissible cardinalities, each `≤ 1`. -/
theorem r_two_le_one (N : ℕ) : r 2 N ≤ 1 := by
  show sSup {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N)
    (_ : Erdos142.IsAPOfLengthFree (α := ℕ) (↑S : Set ℕ) (↑(2:ℕ)))} ≤ 1
  apply csSup_le
  · refine ⟨0, ∅, Finset.empty_subset _, ?_, Finset.card_empty⟩
    intro t hts hAP
    obtain ⟨a, d, hcard, -⟩ := hAP
    rw [Finset.coe_empty] at hts
    have hte : t = ∅ := Set.subset_empty_iff.mp hts
    rw [hte, ENat.card_coe_set_eq, Set.encard_empty, ← Nat.cast_zero] at hcard
    -- hcard : ((0:ℕ):ℕ∞) = ((2:ℕ):ℕ∞)
    have h02 : (0:ℕ) ≠ 2 := by norm_num
    exact (h02 (ENat.natCast_inj.mp hcard)).elim
  · intro y hy
    obtain ⟨S, hsub, hfree, rfl⟩ := hy
    exact card_le_one_of_free hfree

/-- `log N / N → 0` along `atTop` on `ℕ`, from the real version. -/
theorem tendsto_log_div_nat :
    Tendsto (fun N : ℕ => Real.log (N:ℝ) / (N:ℝ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simpa using h
  have h2 := h1.comp tendsto_natCast_atTop_atTop
  simpa [Function.comp_def] using h2

/-- The ratio `(r 2 N)/(N/log N)` tends to 0, squeezed above by `log N / N`. -/
theorem tendsto_ratio_zero :
    Tendsto (fun N : ℕ => (r 2 N : ℝ) / ((N:ℝ)/(N:ℝ).log)) atTop (𝓝 0) := by
  have hr : ∀ N : ℕ, (r 2 N : ℝ) ≤ 1 := fun N => by exact_mod_cast r_two_le_one N
  apply squeeze_zero' _ _ tendsto_log_div_nat
  · filter_upwards [eventually_ge_atTop 2] with N hN
    apply div_nonneg (Nat.cast_nonneg _)
    apply div_nonneg _ (le_of_lt (Real.log_pos _))
    · exact_mod_cast (by omega : (0:ℕ) ≤ N)
    · exact_mod_cast (by omega : (1:ℕ) < N)
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have hpos : (0:ℝ) < (N:ℝ)/(N:ℝ).log :=
      div_pos (by exact_mod_cast (by omega : (0:ℕ) < N))
        (Real.log_pos (by exact_mod_cast (by omega : (1:ℕ) < N)))
    calc (r 2 N : ℝ) / ((N:ℝ)/(N:ℝ).log)
        ≤ 1 / ((N:ℝ)/(N:ℝ).log) := by
          rw [div_le_div_iff_of_pos_right hpos]
          exact hr N
      _ = Real.log (N:ℝ) / (N:ℝ) := one_div_div _ _

end Erdos142K2

open Erdos142K2

theorem solution : (fun N => (r 2 N : ℝ)) =o[atTop] (fun N : ℕ => N / (N : ℝ).log) := by
  apply Asymptotics.isLittleO_of_tendsto' _ tendsto_ratio_zero
  filter_upwards [eventually_ge_atTop 2] with N hN h
  exfalso
  apply div_ne_zero _ _ h
  · exact_mod_cast (by omega : N ≠ 0)
  · exact ne_of_gt (Real.log_pos (by exact_mod_cast (by omega : (1:ℕ) < N)))
