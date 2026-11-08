-- Prove2me | solution 2 for ConsensusHalvingItems.Additive.card_T_ge_of_unique
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:25:04.456557+00:00
-- url     : https://prove2.me/submissions/139bd598-b3bc-4846-9f90-4814bf78f7fb

import Mathlib
import Definitions.Def_ConsensusHalvingItems_Additive_SolvesST

open ConsensusHalvingItems.Additive in
theorem solution {n m : ℕ} (u : Fin n → Fin m → ℚ) (T : Finset (Fin m))
    (x : Fin m → ℚ) (hx : SolvesS u x) (huniq : ∀ y, SolvesST u T x y → y = x) :
    m ≤ n + T.card := by
  by_contra hlt
  push_neg at hlt
  let L1 : (Fin m → ℚ) →ₗ[ℚ] (Fin n → ℚ) := Matrix.mulVecLin (Matrix.of u)
  let L2 : (Fin m → ℚ) →ₗ[ℚ] (T → ℚ) := LinearMap.funLeft ℚ ℚ (fun j : T => (j : Fin m))
  let L := L1.prod L2
  have hdim : Module.finrank ℚ ((Fin n → ℚ) × (T → ℚ)) < Module.finrank ℚ (Fin m → ℚ) := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fin_fun, Fintype.card_coe]
    exact hlt
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := L) hdim
  obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).mp hker
  rw [LinearMap.mem_ker] at hz
  have hz1 : L1 z = 0 := congrArg Prod.fst hz
  have hz2 : L2 z = 0 := congrArg Prod.snd hz
  have hrow : ∀ i, ∑ j, u i j * z j = 0 := by
    intro i
    have := congrFun hz1 i
    simpa [L1, Matrix.mulVec, dotProduct] using this
  have hT : ∀ j ∈ T, z j = 0 := by
    intro j hj
    have := congrFun hz2 ⟨j, hj⟩
    simpa [L2, LinearMap.funLeft_apply] using this
  have hsol : SolvesST u T x (x + z) := by
    refine ⟨?_, ?_⟩
    · intro i
      have h1 := hx i
      have : ∑ j, ((x + z) j - 1 / 2) * u i j =
          ∑ j, (x j - 1 / 2) * u i j + ∑ j, u i j * z j := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        simp only [Pi.add_apply]
        ring
      rw [this, h1, hrow i, add_zero]
    · intro j hj
      simp [hT j hj]
  have := huniq _ hsol
  apply hz0
  have h := congrArg (fun f => f - x) this
  simpa using h
