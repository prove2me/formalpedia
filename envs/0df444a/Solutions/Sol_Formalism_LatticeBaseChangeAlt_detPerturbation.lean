-- Prove2me | solution 1 for Formalism.LatticeBaseChangeAlt.detPerturbation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:35:26.102842+00:00
-- url     : https://prove2.me/submissions/64bb7d4d-c51e-47a5-9076-fa2e6d489da3

import Definitions.Def_Formalism_FilteredPoleLength_ReducedBasisBounds_ParameterInequalities
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_DetMulEqSumPrincipal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LatticeBaseChangeAlt
open Finset Matrix Polynomial
namespace Formalism.LatticeBaseChangeAlt
theorem _root_.solution : DetPerturbation := by
  intro 𝕜 _ i κ _ w σ₀ ε Δmax hΔ
  classical
  have hΔ0 : 0 ≤ Δmax := (norm_nonneg _).trans (hΔ σ₀)
  have hdet : ∀ v : Fin i → Fin i → 𝕜,
      (Matrix.of fun a j => v j a).det = Matrix.detRowAlternating v := by
    intro v
    rw [← Matrix.det_transpose]
    rfl
  let c : Fin i → Option κ → 𝕜 := fun j o => Option.elim o 1 (ε j)
  let τ : Fin i → Option κ → κ := fun j o => Option.elim o (σ₀ j) id
  have hcol : (fun j => w (σ₀ j) + ∑ k, ε j k • w k) = fun j => ∑ o, c j o • w (τ j o) := by
    funext j
    rw [Fintype.sum_option]
    simp [c, τ]
  have h1 := (Matrix.detRowAlternating (n := Fin i) (R := 𝕜)).toMultilinearMap.map_sum
    (fun j o => c j o • w (τ j o))
  have h2 : ∀ r : Fin i → Option κ,
      (Matrix.detRowAlternating (n := Fin i) (R := 𝕜)).toMultilinearMap
        (fun j => c j (r j) • w (τ j (r j)))
      = (∏ j, c j (r j)) * Matrix.detRowAlternating (fun j => w (τ j (r j))) := by
    intro r
    rw [MultilinearMap.map_smul_univ, smul_eq_mul]
    rfl
  have hpert : (Matrix.of fun a j => (w (σ₀ j) + ∑ k, ε j k • w k) a).det
      = ∑ r : Fin i → Option κ, (∏ j, c j (r j)) * Matrix.detRowAlternating (fun j => w (τ j (r j))) := by
    rw [hdet (fun j => w (σ₀ j) + ∑ k, ε j k • w k), hcol]
    exact h1.trans (Finset.sum_congr rfl (fun r _ => h2 r))
  have hbase : (Matrix.of fun a j => w (σ₀ j) a).det = Matrix.detRowAlternating (fun j => w (σ₀ j)) :=
    hdet _
  let r0 : Fin i → Option κ := fun _ => none
  have hr0 : (∏ j, c j (r0 j)) * Matrix.detRowAlternating (fun j => w (τ j (r0 j)))
      = Matrix.detRowAlternating (fun j => w (σ₀ j)) := by
    simp [c, τ, r0]
  rw [hpert, hbase, ← Finset.add_sum_erase _ _ (Finset.mem_univ r0), hr0, add_sub_cancel_left]
  have hb : ∀ r : Fin i → Option κ,
      ‖(∏ j, c j (r j)) * Matrix.detRowAlternating (fun j => w (τ j (r j)))‖
        ≤ (∏ j, ‖c j (r j)‖) * Δmax := by
    intro r
    rw [norm_mul, norm_prod]
    apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    have := hΔ (fun j => τ j (r j))
    rwa [hdet] at this
  have hsum : ∏ j, (1 + ∑ k, ‖ε j k‖) = ∑ r : Fin i → Option κ, ∏ j, ‖c j (r j)‖ := by
    have e : ∀ j, (1 + ∑ k, ‖ε j k‖) = ∑ o, ‖c j o‖ := by
      intro j
      rw [Fintype.sum_option]
      simp [c]
    simp_rw [e]
    rw [Finset.prod_univ_sum]
    try rw [Fintype.piFinset_univ]
  have hr0n : ∏ j, ‖c j (r0 j)‖ = 1 := by simp [c, r0]
  calc ‖∑ r ∈ Finset.univ.erase r0, (∏ j, c j (r j)) * Matrix.detRowAlternating (fun j => w (τ j (r j)))‖
      ≤ ∑ r ∈ Finset.univ.erase r0, ‖(∏ j, c j (r j)) * Matrix.detRowAlternating (fun j => w (τ j (r j)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ r ∈ Finset.univ.erase r0, (∏ j, ‖c j (r j)‖) * Δmax := Finset.sum_le_sum (fun r _ => hb r)
    _ = ((∏ j, (1 + ∑ k, ‖ε j k‖)) - 1) * Δmax := by
        rw [← Finset.sum_mul, Finset.sum_erase_eq_sub (Finset.mem_univ r0), hr0n, hsum]
end Formalism.LatticeBaseChangeAlt
