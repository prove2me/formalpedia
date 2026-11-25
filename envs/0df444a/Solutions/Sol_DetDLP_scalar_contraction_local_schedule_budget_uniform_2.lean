-- Prove2me | solution 2 for DetDLP.scalar_contraction_local_schedule_budget_uniform
-- status  : ACCEPTED   (disprove)
-- author  : @Bingsheng
-- created : 2026-11-24T22:00:57.719075+00:00
-- url     : https://prove2.me/submissions/e4a917f1-f7f5-498d-baab-c63e62672d2f

import Definitions.Def_DetDLP_ContractionContinuation
import Definitions.Def_DetDLP_BTN
import Definitions.Def_OAIQ081S000

set_option autoImplicit false

open DetDLP
open DetDLP.ContinuationSchedule
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

def counterGraph : BipartiteMultigraph where
  nV := 2
  nE := 0
  endpoints := fun e => Fin.elim0 e
  side := fun v => v.val = 0
  bipartite := fun e => Fin.elim0 e

def counterA (_v : Fin counterGraph.nV) (_t : Fin (counterGraph.deg _v) → Bool)
    (_i : Fin 1) : ℕ :=
  0

lemma hv_counter {c0 : ℕ} (hc0 : 0 < c0) : counterGraph.nV ≤ (2 : ℕ) ^ c0 := by
  change (2 : ℕ) ≤ 2 ^ c0
  rcases c0 with (_ | c)
  · exact absurd hc0 (Nat.not_lt_zero _)
  · exact Nat.pow_le_pow_right (by decide : (0 : ℕ) < 2) (Nat.succ_le_succ (Nat.zero_le c))

lemma space_fails (K cap0 U ov wl : ℕ) (hcap : cap0 = K * 3 ^ K + 1) :
    ¬ (max cap0 (max U ov) + 6 * wl + 13 ≤ K * 3 ^ K) := by
  intro hle
  have h₁ : cap0 ≤ max cap0 (max U ov) := le_max_left _ _
  have h₂ : max cap0 (max U ov) ≤ max cap0 (max U ov) + (6 * wl + 13) :=
    Nat.le_add_right _ _
  have hcap_le : cap0 ≤ max cap0 (max U ov) + 6 * wl + 13 := by
    simpa [Nat.add_assoc] using le_trans h₁ h₂
  have hlt : K * 3 ^ K < cap0 := by
    rw [hcap]
    exact Nat.lt_succ_self _
  exact (not_le_of_gt (lt_of_lt_of_le hlt hcap_le)) hle

/-- Negation of the entire quantified statement (disprove packaging). -/
theorem solution :
    ¬ (∀ (C c0 : ℕ), 0 < C → 0 < c0 →
        ∀ {se le : ℕ} (Q : BitProgram.Program 3 se le) (it iv ot ov : Fin se),
          it ≠ iv → ot ≠ ov →
          ∀ (L : ℕ),
            ∃ K : ℕ,
              ∀ (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
                (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin ℓ' → ℕ)
                (B T U x y calls depth cap0 prepSteps : ℕ),
                2 ≤ β → 1 ≤ Told → G.nE ≤ C * β → G.nV ≤ β ^ c0 →
                1 ≤ P → P ≤ C * β → 1 ≤ ℓ' → ℓ' ≤ C * β →
                (∀ v t i, A v t i < 2 ^ P) → 0 < B →
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
                max cap0 (max U overhead) + 6 * w.length + 13 ≤
                  K * (β + desc.length + 1) ^ K) := by
  intro h
  -- Use a trivial 3-register halt program to inhabit the BitProgram parameters.
  let Q : BitProgram.Program 3 3 1 :=
    { inputStack := 0, outputStack := 1, entry := 0, code := fun _ => .halt }
  have hL := h 1 1 (by decide) (by decide) (se := 3) (le := 1) Q
    (0 : Fin 3) (1 : Fin 3) (0 : Fin 3) (1 : Fin 3)
    (by decide) (by decide) 0
  rcases hL with ⟨K, hK⟩
  set cap0 : ℕ := K * 3 ^ K + 1 with hcap0
  have hne : counterGraph.nE ≤ 1 * 2 := by
    change (0 : ℕ) ≤ 2
    exact Nat.zero_le _
  have ha : ∀ v t i, counterA v t i < 2 ^ 1 := by
    intro v t i
    simp [counterA]
  have hconj :=
    hK (β := 2) (P := 1) (ℓ' := 1) (Told := 1) (desc := []) (G := counterGraph)
      (A := counterA) (B := 1) (T := 1) (U := 0) (x := 0) (y := 0) (calls := 0) (depth := 0)
      (cap0 := cap0) (prepSteps := 0)
      (by decide) (by decide) hne (hv_counter (by decide : 0 < (1 : ℕ)))
      (by decide) (by decide) (by decide) (by decide) ha (by decide)
  have hspace := hconj.2
  change max cap0 (max 0 (0 * ((1 + 1 : ℕ).size * (0 + 1) + 3) ^ 2)) +
      6 *
        (encodeNatListBin
            (List.ofFn fun i : Fin 1 =>
              ((BTNContract counterGraph (fun v t =>
                  ∑ j : Fin 1, Polynomial.monomial j.val (counterA v t j : ℤ))).coeff i.val :
                ZMod (2 ^ 1)).val)).length +
      13 ≤
      K * 3 ^ K at hspace
  exact space_fails K cap0 0 (0 * (((1 : ℕ) + 1).size * (0 + 1) + 3) ^ 2)
    (encodeNatListBin
        (List.ofFn fun i : Fin 1 =>
          ((BTNContract counterGraph (fun v t =>
              ∑ j : Fin 1, Polynomial.monomial j.val (counterA v t j : ℤ))).coeff i.val :
            ZMod (2 ^ 1)).val)).length
    hcap0 hspace
