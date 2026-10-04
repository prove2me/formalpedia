-- Prove2me | solution 1 for Disjunctive.RayCGLP.lp_pivot_corresponds_to_cglp_pivot_sequence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:36:03.592966+00:00
-- url     : https://prove2.me/submissions/c96974c8-fc82-4294-bb80-8b279226763d

import Mathlib
import Definitions.Def_Disjunctive_RayCGLP_Cglp
import Definitions.Def_Disjunctive_RayCGLP_Tableau

open Disjunctive.RayCGLP

theorem solution {n : ℕ} {M : Type*} [Fintype M]
    [DecidableEq M] [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ)
    (ι : Fin n → M) (k i : Fin n) (J : Finset (Fin n)) (j1 jt : Fin n) (middle : List (Fin n))
    (hnodup : (j1 :: (middle ++ [jt])).Nodup) (hsub : (j1 :: (middle ++ [jt])).toFinset ⊆ J)
    (hchain : (j1 :: (middle ++ [jt])).IsChain (IsSignFlipStep Atil ι k))
    (ι' : Fin n → M) (hι'_inj : Function.Injective ι')
    (hι'_image : Finset.image ι' Finset.univ = Finset.image ι ((insert i J) \ {jt}))
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ)
    (M1' M2' : Finset (Fin n))
    (hfeas : IsCGLPKFeasible Atil btil k α u u0 v v0 β) (hu0 : 0 < u0) (hv0 : 0 < v0)
    (hu_supp : ∀ l : Fin n, l ∉ M1' → u (ι' l) = 0)
    (hv_supp : ∀ l : Fin n, l ∉ M2' → v (ι' l) = 0) (hM1'M2' : M1' ∪ M2' = Finset.univ) :
    CombinedCutSet Atil btil ι k i J (GammaOf Atil ι k i jt) = {x | β ≤ dotProduct α x} := by
  classical
  exfalso
  have hjt : jt ∈ J := hsub (by simp)
  have hcard1 : (Finset.image ι' Finset.univ).card = n := by
    rw [Finset.card_image_of_injective _ hι'_inj, Finset.card_univ, Fintype.card_fin]
  have hsubS : (insert i J) \ {jt} ⊆ Finset.univ.erase jt := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_singleton] at hx
    exact Finset.mem_erase.mpr ⟨hx.2, Finset.mem_univ x⟩
  have hcard2 : (Finset.image ι ((insert i J) \ {jt})).card ≤ n - 1 := by
    calc (Finset.image ι ((insert i J) \ {jt})).card ≤ ((insert i J) \ {jt}).card :=
          Finset.card_image_le
      _ ≤ (Finset.univ.erase jt).card := Finset.card_le_card hsubS
      _ = n - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin]
  rw [hι'_image] at hcard1
  have hn : 0 < n := Fin.pos jt
  omega

#print axioms solution
