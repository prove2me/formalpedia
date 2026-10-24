-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Tensor.sum_powersetCard_image_eq_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:59:57.096721+00:00
-- url     : https://prove2.me/submissions/99ce6c84-a29e-4f93-a5b7-818997ae58aa

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Tensor_Symmetrization
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.GroupTheory.Perm.Basic

noncomputable section
open Finset
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.Tensor
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
namespace FunctionalInequalities.Analysis.Tensor
end FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Analysis.Tensor in
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
