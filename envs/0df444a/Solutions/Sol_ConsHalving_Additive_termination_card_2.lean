-- Prove2me | solution 2 for ConsHalving.Additive.termination_card
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:25:12.250342+00:00
-- url     : https://prove2.me/submissions/853ebbbc-757b-4625-8d7a-b9c27482bfbe

import Mathlib
import Definitions.Def_ConsHalving_Additive_Setting

set_option autoImplicit false
open ConsHalving.Additive

theorem solution {n m : ℕ} (u : Fin n → Fin m → ℝ) (T : Finset (Fin m))
    (x : Fin m → ℝ) (hx : SolvesS u x) (huniq : ∀ y, SolvesST u T x y → y = x) :
    m ≤ n + T.card := by
  classical
  let L : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) × (T → ℝ) :=
    { toFun := fun d => (fun i => ∑ j, d j * u i j, fun t => d t)
      map_add' := by
        intro a b
        ext <;> simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        ext <;> simp [Finset.mul_sum, mul_assoc] }
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro d hd
    have hd1 : ∀ i, ∑ j, d j * u i j = 0 := fun i => by
      have := congrArg (fun p => p.1 i) hd
      simpa [L] using this
    have hd2 : ∀ j ∈ T, d j = 0 := fun j hj => by
      have := congrArg (fun p => p.2 ⟨j, hj⟩) hd
      simpa [L] using this
    have hy : SolvesST u T x (fun j => x j + d j) := by
      refine ⟨fun i => ?_, fun j hj => ?_⟩
      · have h1 := hx i
        have h2 := hd1 i
        have : ∑ j, (x j + d j - 1 / 2) * u i j
            = ∑ j, (x j - 1 / 2) * u i j + ∑ j, d j * u i j := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [this, h1, h2]; ring
      · simp [hd2 j hj]
    have := huniq _ hy
    funext j
    have := congrFun this j
    simpa using this
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa using this
