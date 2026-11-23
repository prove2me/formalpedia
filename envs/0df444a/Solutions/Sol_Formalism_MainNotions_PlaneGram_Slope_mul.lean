-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.Slope.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:01:53.327732+00:00
-- url     : https://prove2.me/submissions/b1250250-ddd1-4671-a643-696851b25c7a

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Theorems.Thm_Formalism_MainNotions_PlaneGram_val_nonneg_of_pow_six
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_sum_nonneg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_mul_nonneg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_mul_ge_left
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_mul_ge_right
import Theorems.Thm_Formalism_MainNotions_PlaneGram_v_add_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) {σ : Type}
variable {v}
open Formalism.MainNotions.PlaneGram.Slope
variable {TotallyRealRoots : ℕ → ((σ →₀ ℕ) → K) → Prop} {c : ℕ}
namespace Formalism.MainNotions.PlaneGram.Slope
theorem _root_.solution (hmul : ∀ m n f g, TotallyRealRoots m f → TotallyRealRoots n g → TotallyRealRoots (m + n) (fun α => f α * g α))
    {f g : (σ →₀ ℕ) → K} (_hf : ∀ α, 0 ≤ v (f α)) (hg : ∀ α, 0 ≤ v (g α))
    (sf : Slope v TotallyRealRoots c f) (sg : Slope v TotallyRealRoots c g) : Slope v TotallyRealRoots c (fun α => f α * g α) := by
  obtain ⟨ι, hι, lam, n, b, h1, h2, h3, h4⟩ := sf
  obtain ⟨ι', hι', mu, n', d, h1', h2', h3', h4'⟩ := sg
  refine ⟨ι × ι', inferInstance, fun p => lam p.1 * mu p.2, fun p => n p.1 + n' p.2,
    fun p α => b p.1 α * d p.2 α, ?_, ?_, ?_, ?_⟩
  · intro p
    show (((n p.1 + n' p.2 : ℕ)) : WithTop ℚ) ≤ v ((lam p.1 * mu p.2) ^ 6)
    rw [mul_pow, AddValuation.map_mul, Nat.cast_add]
    exact add_le_add (h1 p.1) (h1' p.2)
  · intro p
    exact hmul _ _ _ _ (h2 p.1) (h2' p.2)
  · intro p α
    exact v_mul_nonneg (h3 p.1 α) (h3' p.2 α)
  · intro α
    show (c : WithTop ℚ) ≤
      v (f α * g α - ∑ p : ι × ι', lam p.1 * mu p.2 * (b p.1 α * d p.2 α))
    have hs : ∑ p : ι × ι', lam p.1 * mu p.2 * (b p.1 α * d p.2 α) =
        (∑ k, lam k * b k α) * (∑ l, mu l * d l α) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => by ring))
    rw [hs]
    have hP : 0 ≤ v (∑ k, lam k * b k α) :=
      v_sum_nonneg _ _ (fun k _ => v_mul_nonneg (val_nonneg_of_pow_six _ _ (h1 k)) (h3 k α))
    have e : f α * g α - (∑ k, lam k * b k α) * (∑ l, mu l * d l α) =
        (f α - ∑ k, lam k * b k α) * g α + (∑ k, lam k * b k α) * (g α - ∑ l, mu l * d l α) := by
      ring
    rw [e]
    exact v_add_ge (v_mul_ge_left (h4 α) (hg α)) (v_mul_ge_right hP (h4' α))
end Formalism.MainNotions.PlaneGram.Slope
