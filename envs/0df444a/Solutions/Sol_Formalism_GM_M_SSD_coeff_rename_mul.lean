-- Prove2me | solution 1 for Formalism.GM.M.SSD.coeff_rename_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:43.342498+00:00
-- url     : https://prove2.me/submissions/a7af2f68-4779-4e6a-bd8c-8c041f5f0b8a

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.SSD
open MvPolynomial Finset
variable {σ τ K : Type} [Field K] [DecidableEq σ]
variable (e : τ → σ)
namespace Formalism.GM.M.SSD
theorem _root_.solution (he : Function.Injective e) (n : τ →₀ ℕ) (μ : σ →₀ ℕ) (hμ : ∀ x, μ (e x) = 0) (y : MvPolynomial τ K)
    (g : MvPolynomial σ K) (hg : ∀ w ∈ g.support, ∀ x, w (e x) = 0) :
    coeff (Finsupp.mapDomain e n + μ) (rename e y * g) = coeff n y * coeff μ g := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (Finsupp.mapDomain e n, μ)]
  · rw [coeff_rename_mapDomain e he]
  · rintro ⟨u, w⟩ huw hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at huw
    simp only at huw
    by_contra hc
    have hu : coeff u (rename e y) ≠ 0 := left_ne_zero_of_mul hc
    have hw : coeff w g ≠ 0 := right_ne_zero_of_mul hc
    have hu' := mem_support_iff.mpr hu
    rw [support_rename_of_injective he, Finset.mem_image] at hu'
    obtain ⟨u0, _, rfl⟩ := hu'
    have hw0 := hg w (mem_support_iff.mpr hw)
    have h1 : Finsupp.mapDomain e u0 = Finsupp.mapDomain e n := by
      ext v
      by_cases hv : v ∈ Set.range e
      · obtain ⟨x, rfl⟩ := hv
        have hx := DFunLike.congr_fun huw (e x)
        rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.mapDomain_apply he, Finsupp.mapDomain_apply he,
          hμ x, hw0 x] at hx
        rw [Finsupp.mapDomain_apply he, Finsupp.mapDomain_apply he]
        omega
      · rw [Finsupp.mapDomain_of_notMem_range _ _ hv, Finsupp.mapDomain_of_notMem_range _ _ hv]
    rw [h1] at huw
    have h2 : w = μ := add_left_cancel huw
    exact hne (by rw [h1, h2])
  · intro h; exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by dsimp only)) h
end Formalism.GM.M.SSD
