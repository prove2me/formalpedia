-- Prove2me | solution 1 for Dubey1986.Inefficiency.Dmap_linear_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:56:30.614577+00:00
-- url     : https://prove2.me/submissions/4dc77541-5b24-4387-abcf-947c191a26b1

import Mathlib
import Definitions.Def_Dubey1986_Inefficiency_Setting
import Definitions.Def_Dubey1986_Inefficiency_Derivative

set_option autoImplicit false
open Dubey1986.Inefficiency

theorem solution {n : ℕ} (k : Fin n → ℕ)
    (V : ∀ i, Set (Fin (k i) → ℝ)) (hVo : ∀ i, IsOpen (V i))
    (u₀ : Fin n → Strat k → ℝ) (hu₀ : IsGame V u₀) (s₀ : Strat k) (hs₀ : s₀ ∈ Vset V)
    (y : Fin n → (Strat k →L[ℝ] ℝ)) :
    (∀ t : ℝ, Dmap (fun i x => u₀ i x + t * y i x) s₀ = Dmap u₀ s₀ + t • y) ∧
    HasDerivAt (fun t : ℝ => Dmap (fun i x => u₀ i x + t * y i x) s₀) y 0 := by
  have hopen : IsOpen (Vset V) := isOpen_set_pi Set.finite_univ (fun i _ => hVo i)
  have hdiff : ∀ i, DifferentiableAt ℝ (u₀ i) s₀ := fun i =>
    ((hu₀ i).1.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hs₀)
  have hD : ∀ t : ℝ, Dmap (fun i x => u₀ i x + t * y i x) s₀ = Dmap u₀ s₀ + t • y := by
    intro t
    funext i
    simp only [Dmap, Pi.add_apply, Pi.smul_apply]
    have h2 : HasFDerivAt (fun x => u₀ i x + t * y i x) (fderiv ℝ (u₀ i) s₀ + t • y i) s₀ :=
      (hdiff i).hasFDerivAt.add ((y i).hasFDerivAt.const_mul t)
    rw [h2.fderiv]
  refine ⟨hD, ?_⟩
  have : (fun t : ℝ => Dmap (fun i x => u₀ i x + t * y i x) s₀) = fun t : ℝ => Dmap u₀ s₀ + t • y := by
    funext t; exact hD t
  rw [this]
  have h1 : HasDerivAt (fun t : ℝ => t • y) ((1 : ℝ) • y) 0 := (hasDerivAt_id (0 : ℝ)).smul_const y
  simpa using h1.const_add (Dmap u₀ s₀)
