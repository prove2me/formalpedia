-- Prove2me | solution 1 for DetDLP.scalar_contraction_local_schedule_budget
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T23:01:10.987059+00:00
-- url     : https://prove2.me/submissions/f8c97c28-96b6-43b8-b998-5bddf8c01d26

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000
import Theorems.Thm_DetDLP_scalar_contraction_local_schedule_budget_space

set_option autoImplicit false
set_option maxHeartbeats 400000

open DetDLP
open DetDLP.ContinuationSchedule
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

theorem solution
    (C c0 : ℕ) (hC : 0 < C) (hc0 : 0 < c0)
    {se le : ℕ} (Q : BitProgram.Program 3 se le) (it iv ot ov : Fin se) (hi : it ≠ iv) (ho : ot ≠ ov)
    (L : ℕ)
    (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
    (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin ℓ' → ℕ)
    (B T U x y calls depth cap0 prepSteps : ℕ)
    (hβ : 2 ≤ β) (ht : 1 ≤ Told) (he : G.nE ≤ C * β) (hv : G.nV ≤ β ^ c0)
    (hP₁ : 1 ≤ P) (hP₂ : P ≤ C * β) (hl₁ : 1 ≤ ℓ') (hl₂ : ℓ' ≤ C * β)
    (ha : ∀ v t i, A v t i < 2 ^ P)
    (hB : 0 < B) :
    ∃ K : ℕ,
      let Δbar : ℕ := max G.maxDeg (Nat.ceil ((β : ℝ) ^ ((9 : ℝ) / 10)))
      let ρ : ℕ := max 1 (Nat.floor (Real.logb 2 ((β : ℝ) / (Δbar : ℝ))))
      let Z := BTNContract G (fun v t => ∑ i : Fin ℓ',
        Polynomial.monomial i.val (A v t i : ℤ))
      let w := encodeNatListBin (List.ofFn fun i : Fin ℓ' =>
        ((Z.coeff i.val : ZMod (2 ^ P)).val))
      let q := B + 1
      let overhead := L * (q.size * (depth + 1) + 3) ^ 2
      ((prepSteps + (2 + calls * (1 + T + overhead)) + (6 * w.length + 13) : ℕ) : ℝ) ≤
        (polyBound K (β + desc.length) * (Told : ℝ) *
          (2 : ℝ) ^ ((K : ℝ) *
            ((β : ℝ) / Real.sqrt (ρ : ℝ) + ∑ d ∈ Finset.range (ρ + 1),
              ((β : ℝ) / (8 : ℝ) ^ d) / Real.sqrt ((ρ : ℝ) / (2 : ℝ) ^ d)))) ∧
      max cap0 (max U overhead) + 6 * w.length + 13 ≤ K * (β + desc.length + 1) ^ K := by
  set Δbar : ℕ := max G.maxDeg (Nat.ceil ((β : ℝ) ^ ((9 : ℝ) / 10)))
  set ρ : ℕ := max 1 (Nat.floor (Real.logb 2 ((β : ℝ) / (Δbar : ℝ))))
  set Z := BTNContract G (fun v t => ∑ i : Fin ℓ', Polynomial.monomial i.val (A v t i : ℤ))
  set w := encodeNatListBin (List.ofFn fun i : Fin ℓ' => ((Z.coeff i.val : ZMod (2 ^ P)).val))
  set overhead : ℕ := L * ((B + 1).size * (depth + 1) + 3) ^ 2
  set lhs : ℕ := prepSteps + (2 + calls * (1 + T + overhead)) + (6 * w.length + 13)
  set expr : ℝ :=
    (β : ℝ) / Real.sqrt (ρ : ℝ) +
      ∑ d ∈ Finset.range (ρ + 1),
        ((β : ℝ) / (8 : ℝ) ^ d) / Real.sqrt ((ρ : ℝ) / (2 : ℝ) ^ d)
  obtain ⟨Kspace, hspace⟩ :=
    scalar_contraction_local_schedule_budget_space β desc w cap0 U overhead
  set K : ℕ := max Kspace (max lhs 1)
  refine ⟨K, ?_⟩
  have hKspace : Kspace ≤ K := le_max_left _ _
  have hlhs : lhs ≤ K := le_trans (le_max_left lhs 1) (le_max_right _ _)
  have hbase : 1 ≤ β + desc.length + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hexp_nonneg : 0 ≤ expr := by
    dsimp [expr]
    apply add_nonneg
    · exact div_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
    · refine Finset.sum_nonneg ?_
      intro d hd
      exact div_nonneg
        (div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num : (0:ℝ) ≤ 8) _))
        (Real.sqrt_nonneg _)
  have hpoly : (K : ℝ) ≤ polyBound K (β + desc.length) := by
    dsimp [polyBound]
    have : (1 : ℝ) ≤ ((β + desc.length : ℕ) : ℝ) + 1 := by exact_mod_cast hbase
    have hpow : (1 : ℝ) ≤ (((β + desc.length : ℕ) : ℝ) + 1) ^ K := one_le_pow₀ this
    nlinarith
  have hTold : (1 : ℝ) ≤ (Told : ℝ) := by exact_mod_cast ht
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ ((K : ℝ) * expr) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg _) hexp_nonneg)
  have hspaceK :
      max cap0 (max U overhead) + 6 * w.length + 13 ≤ K * (β + desc.length + 1) ^ K := by
    refine Nat.le_trans hspace (Nat.mul_le_mul hKspace ?_)
    exact Nat.pow_le_pow_right hbase hKspace
  have htime : (lhs : ℝ) ≤ polyBound K (β + desc.length) * (Told : ℝ) * (2 : ℝ) ^ ((K : ℝ) * expr) := by
    have hlhsR : (lhs : ℝ) ≤ (K : ℝ) := by exact_mod_cast hlhs
    have h1 : (K : ℝ) ≤ polyBound K (β + desc.length) * (Told : ℝ) := by
      nlinarith [hpoly, hTold]
    have h2 : polyBound K (β + desc.length) * (Told : ℝ) ≤
        polyBound K (β + desc.length) * (Told : ℝ) * (2 : ℝ) ^ ((K : ℝ) * expr) := by
      have hpos : 0 ≤ polyBound K (β + desc.length) * (Told : ℝ) :=
        mul_nonneg (le_trans (Nat.cast_nonneg K) hpoly) (Nat.cast_nonneg _)
      nlinarith [htwo]
    exact le_trans hlhsR (le_trans h1 h2)
  -- Unfold the goal `let`s to match our local bindings.
  change
      ((prepSteps + (2 + calls * (1 + T + overhead)) + (6 * w.length + 13) : ℕ) : ℝ) ≤
        polyBound K (β + desc.length) * (Told : ℝ) * (2 : ℝ) ^ ((K : ℝ) * expr) ∧
      max cap0 (max U overhead) + 6 * w.length + 13 ≤ K * (β + desc.length + 1) ^ K
  refine And.intro ?_ hspaceK
  simpa [lhs] using htime
