-- Prove2me | solution 1 for BunkbedAux.wzProb_level_split
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T00:34:32.582273+00:00
-- url     : https://prove2.me/submissions/85f49ff2-e45b-4621-8bc7-c853a059526f

import Definitions.Def_BunkbedHypergraph

open Bunkbed Bunkbed.Hyper Finset SimpleGraph

/-- Assembling a WZ configuration from its two level-restrictions. -/
private def glue {ι : Type*} (c : (ι → WZ) × (ι → WZ)) : ι × Fin 2 → WZ :=
  fun p => if p.2 = 0 then c.1 p.1 else c.2 p.1

private def levelEquiv {ι : Type*} : ((ι → WZ) × (ι → WZ)) ≃ (ι × Fin 2 → WZ) where
  toFun := glue
  invFun ψ := (fun i => ψ (i, 0), fun i => ψ (i, 1))
  left_inv c := by
    obtain ⟨c₀, c₁⟩ := c
    simp only [glue, Prod.mk.injEq]
    constructor <;> funext i <;> simp
  right_inv ψ := by
    funext p
    obtain ⟨i, j⟩ := p
    fin_cases j <;> simp [glue]

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t : ι → (V × V × V)) (T : Finset V) (P : WZ → ℚ) (x y : V × Fin 2) :
    wzProb t T P x y
      = ∑ c : (ι → WZ) × (ι → WZ),
          (if (wzGraph t T (fun p => if p.2 = 0 then c.1 p.1 else c.2 p.1)).Reachable x y
            then (1 : ℚ) else 0) * ((∏ i, P (c.1 i)) * (∏ i, P (c.2 i))) := by
  rw [wzProb, ← Equiv.sum_comp levelEquiv]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  congr 1
  rw [Fintype.prod_prod_type]
  simp only [levelEquiv, Equiv.coe_fn_mk, glue, Fin.prod_univ_two]
  norm_num
  rw [Finset.prod_mul_distrib]
