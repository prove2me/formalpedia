-- Prove2me | solution 1 for DetDLP.fermat_convolution_gadget
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T13:33:36.136178+00:00
-- url     : https://prove2.me/submissions/626b4b9f-f11f-4d6a-ab89-4980100bf1fc

import Mathlib
import Definitions.Def_DetDLP_BTN
import Theorems.Thm_DetDLP_schonhage_strassen_fermat_dft_and_carry
import Theorems.Thm_DetDLP_schonhage_strassen_btn_tm_from_fermat_carry
import Theorems.Thm_DetDLP_limb_convolution_eq_mul

set_option autoImplicit false

open DetDLP
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution :
    ∃ (E : PrimitiveMachine) (outE : Fin E.tapeCount) (K : ℕ),
      ∀ d : ℕ, 1 ≤ d →
        ∃ (k L : ℕ), 0 < k ∧ d ≤ k*L ∧ L ≤ 2^k ∧
        ∃ (G : BipartiteMultigraph)
          (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
          (ext : Fin (4 * d) → Fin G.nE),
          G.nE < 1100 * (d + 1) ∧
          (G.maxDeg : ℝ) < 136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4) ∧
          (G.nV : ℝ) ≤ polyBound K d ∧
          BoolBTNEntryEvaluable (countWord d) G T E outE (polyBound K d) (polyBound K d) ∧
          IsParsimonious G T ext (fun x =>
            let a := bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩)
            let b := bitsToNat (fun i : Fin d => x ⟨d + i.val, by omega⟩)
            let cout := bitsToNat (fun i : Fin (2*d) => x ⟨2*d+i.val, by omega⟩)
            let B := 2^k
            let Q := 2^(4*k)+1
            let limb (w i : ℕ) := w / B^i % B
            let c (u : ℕ) := ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
              if i+j=u then limb a i * limb b j else 0
            (∑ u ∈ Finset.range (2*L), (c u % Q)*B^u) = cout) := by
  obtain ⟨E, outE, K, hSS⟩ :=
    DetDLP.schonhage_strassen_btn_tm_from_fermat_carry
      DetDLP.schonhage_strassen_fermat_dft_and_carry
  refine ⟨E, outE, K, fun d hd => ?_⟩
  obtain ⟨G, T, ext, hnE, hdeg, hnV, hEval, hPar⟩ := hSS d hd
  obtain ⟨hk, hdL, hL2, hrel⟩ := DetDLP.limb_convolution_eq_mul.2 d hd
  refine ⟨d, 1, hk, hdL, hL2, G, T, ext, hnE, hdeg, hnV, hEval, ?_⟩
  rw [hrel]
  exact hPar
