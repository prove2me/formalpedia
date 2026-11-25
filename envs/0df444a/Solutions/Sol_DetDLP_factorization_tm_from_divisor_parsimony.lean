-- Prove2me | solution 1 for DetDLP.factorization_tm_from_divisor_parsimony
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T13:33:37.982751+00:00
-- url     : https://prove2.me/submissions/0250101c-a108-4925-9a39-6c3f57ec5b77

import Mathlib
import Definitions.Def_DetDLP_BTN
import Theorems.Thm_DetDLP_bounded_divisor_search_from_btn
import Theorems.Thm_DetDLP_factor_splitting_driver_machine
import Theorems.Thm_DetDLP_factor_splitting_tree_correctness

set_option autoImplicit false

open DetDLP
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution :
    (∀ (C A c0 : ℕ), 0 < C → 0 < A → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (s P0 ℓ : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P0 ℓ),
            2 ≤ s → G.nE ≤ C * s → G.nV ≤ s ^ c0 →
            G.maxDeg ≤ Nat.ceil ((s : ℝ) ^ ((9 : ℝ) / 10)) →
            1 ≤ P0 → P0 ≤ C * s → 1 ≤ ℓ → ℓ ≤ C * s →
            BTNEntryEvaluable desc G P0 ℓ T E outE
              (((s + desc.length : ℕ) : ℝ) ^ c0 * (2 : ℝ) ^ ((A : ℝ) * (s : ℝ) ^ ((9 : ℝ) / 10)))
              (((s + desc.length : ℕ) : ℝ) ^ c0) →
            ∃ w : List Bool,
              EncodesTruncPoly P0 ℓ w (BTNContract G T) ∧
              RunsWithin M outM (encodeBTNInstance desc G s P0 ℓ) w
                (btnTimeBound K (s + desc.length) s)
                (polyBound K (s + desc.length))) →
    (∃ (E : PrimitiveMachine) (outE : Fin E.tapeCount) (K : ℕ),
      ∀ d : ℕ, 1 ≤ d →
        ∃ (G : BipartiteMultigraph)
          (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
          (ext : Fin (4 * d) → Fin G.nE),
          G.nE < 1100 * (d + 1) ∧
          (G.maxDeg : ℝ) < 136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4) ∧
          (G.nV : ℝ) ≤ polyBound K d ∧
          BoolBTNEntryEvaluable (countWord d) G T E outE (polyBound K d) (polyBound K d) ∧
          IsParsimonious G T ext (fun x =>
            bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩) *
            bitsToNat (fun i : Fin d => x ⟨d + i.val, by omega⟩) =
            bitsToNat (fun i : Fin (2 * d) => x ⟨2 * d + i.val, by omega⟩))) →
    (∀ (N : ℕ), 2 ≤ N →
      let n := bitLen (N + 1)
      N < 2 ^ n ∧
      (∀ d e : ℕ,
        (2 ≤ d ∧ d < N ∧ e < 2 ^ n ∧ d * e = N) ↔
        (2 ≤ d ∧ d < N ∧ d ∣ N ∧ e = N / d)) ∧
      ((Finset.Ico 2 N).filter (fun d => d ∣ N) = ∅ ↔ N.Prime) ∧
      (¬ N.Prime →
        N.minFac ∈ (Finset.Ico 2 N).filter (fun d => d ∣ N) ∧
        N.minFac.Prime ∧
        (∀ d ∈ (Finset.Ico 2 N).filter (fun d => d ∣ N), N.minFac ≤ d) ∧
        2 ≤ N / N.minFac ∧ N / N.minFac < N ∧
        N.primeFactorsList = N.minFac :: (N / N.minFac).primeFactorsList)) →
    (∀ (G : BipartiteMultigraph)
       (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
       {k : ℕ} (ext : Fin k → Fin G.nE) (R : (Fin k → Bool) → Prop) [DecidablePred R]
       (P0 : ℕ),
       IsParsimonious G T ext R →
       G.nE < P0 →
       (Finset.univ.filter R).card < 2 ^ P0 ∧
       BTNContract G (fun v α => truncPolyOfCoeffs P0 1 (fun _ => if T v α then 1 else 0)) =
         truncPolyOfCoeffs P0 1 (fun _ => (Finset.univ.filter R).card)) →
    ∃ (M : PrimitiveMachine) (out : Fin M.tapeCount) (K : ℕ),
      ∀ N : ℕ, 2 ≤ N →
        let n := bitLen (N + 1)
        RunsWithin M out (countWord N) (encodeNatListBin N.primeFactorsList)
          ((2 : ℝ) ^ ((K : ℝ) * (n : ℝ) / Real.sqrt (logSafe (n : ℝ))))
          (polyBound K n) := by
  intro hcontract hmult _ _
  obtain ⟨f, Md, od, Kd, hf⟩ := DetDLP.bounded_divisor_search_from_btn hcontract hmult
  obtain ⟨M, out, K, hM⟩ :=
    DetDLP.factor_splitting_driver_machine f Md od Kd (fun N hN => (hf N hN).2)
  refine ⟨M, out, K, fun N hN => ?_⟩
  dsimp only
  have hrun := hM N hN
  have hcorr := (DetDLP.factor_splitting_tree_correctness f (fun x hx => (hf x hx).1) N hN).2.2
  dsimp only at hrun hcorr
  rwa [hcorr] at hrun
