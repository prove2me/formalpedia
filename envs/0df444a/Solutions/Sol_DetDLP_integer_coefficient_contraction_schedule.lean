-- Prove2me | solution 1 for DetDLP.integer_coefficient_contraction_schedule
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T13:33:33.940907+00:00
-- url     : https://prove2.me/submissions/d8f65a76-d8de-437a-93a0-64c3d746c140
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DetDLP_BTN
import Theorems.Thm_DetDLP_cauchy_hermite_recursion_budget
import Theorems.Thm_DetDLP_lemma_5_2_tm_from_budget
import Theorems.Thm_DetDLP_trunc_poly_int_contract_and_uniqueness

set_option autoImplicit false

open DetDLP
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

private lemma runsWithin_mono {A : PrimitiveMachine} {out : Fin A.tapeCount}
    {input output : List Bool} {τ₁ τ₂ σ₁ σ₂ : ℝ}
    (h : RunsWithin A out input output τ₁ σ₁) (hτ : τ₁ ≤ τ₂) (hσ : σ₁ ≤ σ₂) :
    RunsWithin A out input output τ₂ σ₂ := by
  obtain ⟨time, final, htr, hst, hout, htime, hspace⟩ := h
  exact ⟨time, final, htr, hst, hout, le_trans htime hτ,
    fun k c hk htk => le_trans (hspace k c hk htk) hσ⟩

theorem solution :
    ∀ (C c0 : ℕ), 0 < C → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (A : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Fin ℓ' → ℕ),
            2 ≤ β →
            1 ≤ Told →
            G.nE ≤ C * β →
            G.nV ≤ β ^ c0 →
            1 ≤ P → P ≤ C * β →
            1 ≤ ℓ' → ℓ' ≤ C * β →
            (∀ v t i, A v t i < 2^P) →
            (∀ v t, RunsWithin E outE (encodePortQuery desc v.val (List.ofFn t))
              (encodeNatListBin (List.ofFn (A v t))) (Told : ℝ) (((β+desc.length : ℕ) : ℝ)^c0)) →
            let Δbar : ℕ := max G.maxDeg (Nat.ceil ((β : ℝ) ^ ((9 : ℝ) / 10)))
            let ρ : ℕ := max 1 (Nat.floor (Real.logb 2 ((β : ℝ) / (Δbar : ℝ))))
            let Z := BTNContract G (fun v t => ∑ i : Fin ℓ',
              Polynomial.monomial i.val (A v t i : ℤ))
            let w := encodeNatListBin (List.ofFn fun i : Fin ℓ' =>
              ((Z.coeff i.val : ZMod (2^P)).val))
            RunsWithin M outM (encodeBTNInstance desc G β P ℓ') w
              (polyBound K (β+desc.length) * (Told : ℝ) * (2 : ℝ)^((K : ℝ) *
                ((β : ℝ)/Real.sqrt (ρ : ℝ) + ∑ d ∈ Finset.range (ρ+1),
                 ((β : ℝ)/(8 : ℝ)^d) / Real.sqrt ((ρ : ℝ)/(2 : ℝ)^d))))
              (polyBound K (β+desc.length)) := by
  intro C c0 hC hc0 E outE
  obtain ⟨M, outM, K, hM⟩ :=
    DetDLP.lemma_5_2_tm_from_budget DetDLP.cauchy_hermite_recursion_budget C c0 hC hc0 E outE
  refine ⟨M, outM, K, ?_⟩
  intro β P ℓ' Told desc G A hβ hTold hnE hnV hP1 hP2 hℓ1 hℓ2 hA hE
  dsimp only
  let T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P ℓ' :=
    fun v t => truncPolyOfCoeffs P ℓ' (A v t)
  have huniq := DetDLP.trunc_poly_int_contract_and_uniqueness G P ℓ' A hA
  have hEval : BTNEntryEvaluable desc G P ℓ' T E outE (Told : ℝ) (((β + desc.length : ℕ) : ℝ) ^ c0) := by
    intro v t
    exact ⟨encodeNatListBin (List.ofFn (A v t)), huniq.1 v t, hE v t⟩
  obtain ⟨w', hw'_enc, hw'_run⟩ :=
    hM β P ℓ' Told desc G T hβ hTold hnE hnV hP1 hP2 hℓ1 hℓ2 hEval
  have hw_eq := huniq.2.2 w' hw'_enc
  rw [hw_eq] at hw'_run
  let Δbar : ℕ := max G.maxDeg (Nat.ceil ((β : ℝ) ^ ((9 : ℝ) / 10)))
  let ρ : ℕ := max 1 (Nat.floor (Real.logb 2 ((β : ℝ) / (Δbar : ℝ))))
  have hsum_nn : 0 ≤ ∑ d ∈ Finset.range (ρ + 1),
      ((β : ℝ) / (8 : ℝ) ^ d) / Real.sqrt ((ρ : ℝ) / (2 : ℝ) ^ d) := by
    refine Finset.sum_nonneg fun d _ => ?_
    positivity
  have hexp :
      (K : ℝ) * (β : ℝ) / Real.sqrt (ρ : ℝ) ≤
      (K : ℝ) * ((β : ℝ) / Real.sqrt (ρ : ℝ) + ∑ d ∈ Finset.range (ρ + 1),
        ((β : ℝ) / (8 : ℝ) ^ d) / Real.sqrt ((ρ : ℝ) / (2 : ℝ) ^ d)) := by
    rw [mul_div_assoc]
    have hK : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
    nlinarith
  have hrpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp
  have hpref : 0 ≤ polyBound K (β + desc.length) * (Told : ℝ) := by
    unfold polyBound
    positivity
  exact runsWithin_mono hw'_run (mul_le_mul_of_nonneg_left hrpow hpref) (le_refl _)
