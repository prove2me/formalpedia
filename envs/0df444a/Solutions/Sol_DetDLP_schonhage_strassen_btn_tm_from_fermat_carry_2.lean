-- Prove2me | solution 2 for DetDLP.schonhage_strassen_btn_tm_from_fermat_carry
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T04:39:11.271056+00:00
-- url     : https://prove2.me/submissions/04b6c34f-0386-4bf7-9510-a7608573f3a2

import Mathlib
import Definitions.Def_DetDLP_BTN
import Definitions.Def_DetDLP_W4_M5Evaluator

set_option autoImplicit false

open DetDLP DetDLP.w4_M5Evaluator DetDLP.w4_M5GraphBounds DetDLP.w4_M5PortTensor
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution :
    ((∀ (d J n0 L L1 L2 : ℕ),
        1 ≤ d → 16 ≤ J → 64 * (d + 1) ≤ J ^ 2 → J ^ 2 < 256 * (d + 1) →
        1 ≤ n0 → n0 < J / 16 + 1 → 2 * n0 ≤ L → L < 4 * n0 →
        L1 ≤ L2 → L2 ^ 2 ≤ 2 * L →
        L ≤ J / 2 ∧
        L2 ^ 2 ≤ J ∧
        4 * d + 4 * J * (J + 1) < 1100 * (d + 1) ∧
        (2 * max L1 L2 * (J + 1) : ℝ) < 136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4)) ∧
     ((∀ (J μ step : ℕ),
         μ ≤ J → J = 2 ^ μ * step →
         let M := 2 ^ J + 1
         let ω : ZMod M := (2 : ZMod M) ^ step
         (2 : ZMod M) ^ J = -1 ∧
         ω ^ (2 ^ μ) = -1 ∧
         ω ^ (2 ^ (μ + 1)) = 1 ∧
         (-(2 : ZMod M) ^ (J - μ)) * ((2 : ZMod M) ^ μ) = 1) ∧
      (∀ (L1 L2 : ℕ) (ω : ℤ) (x : ℕ → ℤ) (t1 t2 : ℕ),
         ω ^ (L1 * L2) = 1 →
         ∑ j1 ∈ Finset.range L1, ∑ j2 ∈ Finset.range L2,
           x (L2 * j1 + j2) * ω ^ ((L2 * j1 + j2) * (t1 + L1 * t2)) =
         ∑ j2 ∈ Finset.range L2,
           ω ^ (L1 * j2 * t2) *
             (ω ^ (j2 * t1) * ∑ j1 ∈ Finset.range L1, ω ^ (L2 * j1 * t1) * x (L2 * j1 + j2)))) ∧
     (∀ (B m : ℕ) (c z κ : ℕ → ℕ),
        0 < B →
        κ 0 = 0 →
        (∀ ℓ < m, c ℓ + κ ℓ = z ℓ + B * κ (ℓ + 1) ∧ z ℓ < B) →
        (∀ ℓ < m, z ℓ = (c ℓ + κ ℓ) % B ∧ κ (ℓ + 1) = (c ℓ + κ ℓ) / B) ∧
        (∑ ℓ ∈ Finset.range m, c ℓ * B ^ ℓ) =
          (∑ ℓ ∈ Finset.range m, z ℓ * B ^ ℓ) + κ m * B ^ m ∧
        ((∑ ℓ ∈ Finset.range m, c ℓ * B ^ ℓ) < B ^ m →
          κ m = 0 ∧ (∑ ℓ ∈ Finset.range m, z ℓ * B ^ ℓ) = ∑ ℓ ∈ Finset.range m, c ℓ * B ^ ℓ))) →
    ∃ (E : PrimitiveMachine) (outE : Fin E.tapeCount) (K : ℕ),
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
            bitsToNat (fun i : Fin (2 * d) => x ⟨2 * d + i.val, by omega⟩)) := by
  intro _
  obtain ⟨E,outE,K,h⟩ := w4_M5QueryBridge.machine_of_query f f_poly (fun _ hd => tensor hd) f_spec
  refine ⟨E,outE,K,?_⟩
  intro d hd
  obtain ⟨hv,heval⟩ := h d hd
  exact ⟨graph d hd, tensor hd, w4_M5PortTensor.ext hd, graph_edge_bound hd, graph_maxDeg_bound hd,
    hv, heval, parsimonious hd⟩

#print axioms solution
