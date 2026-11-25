-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.max_cusps_rank_one_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:35:43.323244+00:00
-- url     : https://prove2.me/submissions/2c0d3ed0-2c13-401b-9544-bb263c6ab20d

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMeanContinuity
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_MaximalCuspKernels_MaxCuspsPfA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.FD NumberField Matrix Formalism.L2.Pj.FJ Complex
open scoped ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
namespace Formalism.L2.Pj.QAt
theorem _root_.solution {R : Type} [CommRing R] (σ : R →+* R) {r ρ : ℕ}
    (G : Matrix (Fin r) (Fin r) R) (η : Fin ρ → R) (e : Fin ρ → Fin r → R) (α : R) (a b : Fin r) :
    α * (∑ a', η a' * e a' a) * ∑ k, G b k * σ (∑ b', η b' * e b' k) =
      ∑ a', ∑ b', α * (η a' * σ (η b')) * e a' a * ∑ k, G b k * σ (e b' k) := by
  have hσ : ∀ k, σ (∑ b', η b' * e b' k) = ∑ b', σ (η b') * σ (e b' k) := fun k => by
    simp only [map_sum, map_mul]
  have hin : (∑ k, G b k * σ (∑ b', η b' * e b' k)) =
      ∑ b', σ (η b') * ∑ k, G b k * σ (e b' k) := by
    simp_rw [hσ, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hin, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b' _ => by ring
end Formalism.L2.Pj.QAt
