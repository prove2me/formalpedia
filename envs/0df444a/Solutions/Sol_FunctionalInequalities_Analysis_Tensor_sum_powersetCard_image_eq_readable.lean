-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.sum_powersetCard_image_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:29:06.623442+00:00
-- url     : https://prove2.me/submissions/e93fc3c6-3f36-4a8c-b04e-ff5767fdf7a4

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization

noncomputable section
open Finset
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
omit [Fintype Ω] in
/-- Equivariance of subset sums: if `ρ g (T F) = T (F.image g)` for every `F`, then the sum of
`T` over the `k`-subsets of `g(Q)` is `ρ g` applied to the sum over the `k`-subsets of `Q`. -/
theorem solution (ρ : Equiv.Perm Ω →* (V ≃ₗᵢ[ℝ] V)) (g : Equiv.Perm Ω)
    (T : Finset Ω → V) (hT : ∀ F, ρ g (T F) = T (F.image g)) (Q : Finset Ω) (k : ℕ) :
    ∑ F ∈ (Q.image g).powersetCard k, T F = ρ g (∑ F ∈ Q.powersetCard k, T F) := by
    have hpow :
        (Q.image g).powersetCard k =
          (Q.powersetCard k).map (Finset.mapEmbedding g.toEmbedding).toEmbedding := by
      simpa [Finset.map_eq_image] using
        (Finset.powersetCard_map g.toEmbedding k Q)
    calc
      ∑ F ∈ (Q.image g).powersetCard k, T F =
          ∑ F ∈ Q.powersetCard k, T (F.image g) := by
            rw [hpow, Finset.sum_map]
            simp [Finset.map_eq_image]
      _ = ∑ F ∈ Q.powersetCard k, ρ g (T F) := by
            apply Finset.sum_congr rfl
            intro F hF
            exact (hT F).symm
      _ = ρ g (∑ F ∈ Q.powersetCard k, T F) := by
            rw [map_sum]
