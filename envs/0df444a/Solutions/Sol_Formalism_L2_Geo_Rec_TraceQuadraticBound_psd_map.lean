-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.TraceQuadraticBound.psd_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:02:21.807006+00:00
-- url     : https://prove2.me/submissions/36c51b33-7a9c-40bc-a3a8-feff76279ea1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Rec Formalism.L2.Geo.Rec.TraceQuadraticBound
variable {n : Type} [Fintype n] [DecidableEq n]
variable {K : Type} [Field K]
namespace Formalism.L2.Geo.Rec.TraceQuadraticBound
theorem _root_.solution {m : ℕ} (cj : K → K) (σ : K →+* ℂ) (hσ : ∀ z, σ (cj z) = star (σ z)) (hd : DenseRange σ)
    (A : Matrix (Fin m) (Fin m) K) (hH : ∀ i k, A k i = cj (A i k))
    (hP : ∀ l : Fin m → K, l ≠ 0 → 0 < (σ (∑ i, ∑ k, l i * A i k * cj (l k))).re) :
    (A.map σ).PosSemidef ∧ (A.map σ).det ≠ 0 := by
  have hHm : (A.map σ).IsHermitian := by
    ext i k
    simp only [conjTranspose_apply, map_apply]
    rw [hH, hσ, star_star]
  have key : ∀ l : Fin m → K, σ (∑ i, ∑ k, l i * A i k * cj (l k)) =
      star (fun k => star (σ (l k))) ⬝ᵥ (A.map σ) *ᵥ (fun k => star (σ (l k))) := by
    intro l
    simp only [map_sum, map_mul, hσ, dotProduct, mulVec, map_apply, Pi.star_apply, star_star, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have hden : DenseRange (fun l : Fin m → K => fun k => star (σ (l k))) := by
    have h1 : DenseRange (fun z : K => star (σ z)) :=
      (Function.RightInverse.surjective (f := (star : ℂ → ℂ)) (g := star) star_star).denseRange.comp hd
        continuous_star
    exact DenseRange.piMap (f := fun _ : Fin m => fun z : K => star (σ z)) (fun _ => h1)
  have hre : ∀ x : Fin m → ℂ, 0 ≤ (star x ⬝ᵥ (A.map σ) *ᵥ x).re := by
    intro x
    refine hden.induction_on (p := fun x => 0 ≤ (star x ⬝ᵥ (A.map σ) *ᵥ x).re) x ?_ ?_
    · apply isClosed_le continuous_const
      simp only [dotProduct, mulVec, Pi.star_apply]
      fun_prop
    · intro l
      show 0 ≤ (star (fun k => star (σ (l k))) ⬝ᵥ (A.map σ) *ᵥ (fun k => star (σ (l k)))).re
      by_cases hl : l = 0
      · subst hl
        rw [show (fun k : Fin m => star (σ ((0 : Fin m → K) k))) = 0 by funext k; simp]
        simp
      · rw [← key]; exact (hP l hl).le
  refine ⟨PosSemidef.of_dotProduct_mulVec_nonneg hHm fun x => ?_, ?_⟩
  · rw [Complex.nonneg_iff]
    exact ⟨hre x, (hHm.im_star_dotProduct_mulVec_self x).symm⟩
  · rw [show (A.map σ).det = σ A.det from (RingHom.map_det σ A).symm]
    intro h0
    apply (map_eq_zero_iff σ σ.injective).not.mpr ?_ h0
    intro hdet
    obtain ⟨l, hl, hlA⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    have := hP l hl
    have e : ∑ i, ∑ k, l i * A i k * cj (l k) = ∑ k, (l ᵥ* A) k * cj (l k) := by
      simp only [vecMul, dotProduct, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [e, hlA] at this
    simp at this
end Formalism.L2.Geo.Rec.TraceQuadraticBound
