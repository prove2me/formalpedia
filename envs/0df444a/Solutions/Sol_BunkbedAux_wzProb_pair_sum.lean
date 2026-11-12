-- Prove2me | solution 1 for BunkbedAux.wzProb_pair_sum
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T02:41:02.317908+00:00
-- url     : https://prove2.me/submissions/95866e98-279f-4128-ba6a-5342f9398051

import Definitions.Def_BunkbedHypergraph
open Bunkbed Bunkbed.Hyper Finset SimpleGraph

private def pairEq {ι : Type*} : (ι → WZ × WZ) ≃ (ι × Fin 2 → WZ) where
  toFun φ := fun p => if p.2 = 0 then (φ p.1).1 else (φ p.1).2
  invFun ψ := fun i => (ψ (i, 0), ψ (i, 1))
  left_inv φ := by funext i; simp
  right_inv ψ := by funext p; obtain ⟨i, j⟩ := p; fin_cases j <;> simp

/-- **`wzProb` as a sum over pair configurations.** -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → (V × V × V)) (T : Finset V) (P : WZ → ℚ) (x y : V × Fin 2) :
    wzProb t T P x y
      = ∑ φ : ι → WZ × WZ, (∏ i, P (φ i).1 * P (φ i).2) *
          (if (wzGraph t T (fun p => if p.2 = 0 then (φ p.1).1 else (φ p.1).2)).Reachable x y
            then (1 : ℚ) else 0) := by
  rw [wzProb, ← Equiv.sum_comp pairEq]
  refine Finset.sum_congr rfl (fun φ _ => ?_)
  rw [mul_comm]
  congr 1
  · rw [Fintype.prod_prod_type]
    simp only [pairEq, Equiv.coe_fn_mk, Fin.prod_univ_two]
    norm_num
