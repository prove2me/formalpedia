-- Prove2me | solution 1 for ConsensusHalvingItems.Additive.card_T_ge_of_unique
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-07T21:34:42.793936+00:00
-- url     : https://prove2.me/submissions/46bf796c-892c-4d16-9176-0a44d2a61f3e

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_SolvesST

open ConsensusHalvingItems.Additive in
theorem solution {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m))
    (x : Fin m → ℚ) (hx : SolvesS u x) (huniq : ∀ y, SolvesST u T x y → y = x) :
    m ≤ n + T.card := by
  by_contra hlt
  push Not at hlt
  let g1 : (Fin m → ℚ) →ₗ[ℚ] (Fin n → ℚ) := Matrix.mulVecLin (Matrix.of fun i j => u i j)
  let g2 : (Fin m → ℚ) →ₗ[ℚ] (T → ℚ) := LinearMap.funLeft ℚ ℚ (Subtype.val : T → Fin m)
  let f : (Fin m → ℚ) →ₗ[ℚ] (Fin n → ℚ) × (T → ℚ) := LinearMap.prod g1 g2
  have hdim : Module.finrank ℚ ((Fin n → ℚ) × (T → ℚ)) < Module.finrank ℚ (Fin m → ℚ) := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun, Module.finrank_pi,
      Fintype.card_coe]
    exact hlt
  obtain ⟨d, hdk, hd0⟩ := (Submodule.ne_bot_iff _).mp (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hdim)
  have hk : f d = 0 := hdk
  have h1 : g1 d = 0 := congrArg Prod.fst hk
  have h2 : g2 d = 0 := congrArg Prod.snd hk
  have hS : SolvesST u T x (x + d) := by
    refine ⟨?_, ?_⟩
    · intro i
      have hi := congrFun h1 i
      have hxi := hx i
      simp only [g1, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
        Pi.zero_apply] at hi
      have : ∑ j, ((x + d) j - 1 / 2) * u i j
          = ∑ j, (x j - 1 / 2) * u i j + ∑ j, u i j * d j := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Pi.add_apply]
        ring
      rw [this, hxi, hi, add_zero]
    · intro j hj
      have := congrFun h2 ⟨j, hj⟩
      simp only [g2, LinearMap.funLeft_apply, Pi.zero_apply] at this
      simp [this]
  have := huniq _ hS
  apply hd0
  have h3 : x + d = x + 0 := by rw [this, add_zero]
  exact add_left_cancel h3
