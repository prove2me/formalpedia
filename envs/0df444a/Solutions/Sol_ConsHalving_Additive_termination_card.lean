-- Prove2me | solution 1 for ConsHalving.Additive.termination_card
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T14:59:22.75799+00:00
-- url     : https://prove2.me/submissions/e1567d9f-2292-4463-a49a-93c325a96cb3

import Mathlib
import Definitions.Def_ConsHalving_Additive_Setting

open ConsHalving.Additive

theorem solution {n m : ℕ} (u : Fin n → Fin m → ℝ) (T : Finset (Fin m))
    (x : Fin m → ℝ) (hx : SolvesS u x) (huniq : ∀ y, SolvesST u T x y → y = x) :
    m ≤ n + T.card := by
  by_contra hlt
  push_neg at hlt
  let A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Matrix.mulVecLin (Matrix.of fun i j => u i j)
  let B : (Fin m → ℝ) →ₗ[ℝ] (T → ℝ) := LinearMap.funLeft ℝ ℝ (Subtype.val : T → Fin m)
  let L := A.prod B
  have hrank : Module.finrank ℝ ((Fin n → ℝ) × (T → ℝ)) < Module.finrank ℝ (Fin m → ℝ) := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun,
      Module.finrank_fintype_fun_eq_card]
    simpa using hlt
  have hker := LinearMap.ker_ne_bot_of_finrank_lt (f := L) hrank
  obtain ⟨d, hd, hd0⟩ := (Submodule.ne_bot_iff _).1 hker
  rw [LinearMap.mem_ker] at hd
  have hA : A d = 0 := congrArg Prod.fst hd
  have hB : B d = 0 := congrArg Prod.snd hd
  have hAi : ∀ i, ∑ j, u i j * d j = 0 := by
    intro i
    have := congrFun hA i
    simpa [A, Matrix.mulVec, dotProduct] using this
  have hBj : ∀ j ∈ T, d j = 0 := by
    intro j hj
    have := congrFun hB ⟨j, hj⟩
    simpa [B, LinearMap.funLeft] using this
  have hy : SolvesST u T x (x + d) := by
    refine ⟨fun i => ?_, fun j hj => ?_⟩
    · have h1 := hx i
      have h2 := hAi i
      have : ∑ j, ((x + d) j - 1 / 2) * u i j =
          ∑ j, (x j - 1 / 2) * u i j + ∑ j, u i j * d j := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Pi.add_apply]
        ring
      rw [this, h1, h2]
      ring
    · simp [hBj j hj]
  have := huniq _ hy
  apply hd0
  have h' : x + d = x + 0 := by simpa using this
  exact add_left_cancel h'
