-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.maxCuspsA_zMatC_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:42:41.013694+00:00
-- url     : https://prove2.me/submissions/5b67d6a2-dfda-48fb-8f40-08b21783093a

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
namespace Formalism.L2.Pj.QAt
theorem _root_.solution (X : Data E r) (cu : CuspFD X ρ) (τ : E →+* ℂ)
    (β β' : Matrix (Fin ρ) (Fin ρ) ℂ) :
    zMatC X cu.e τ (β + β') = zMatC X cu.e τ β * zMatC X cu.e τ β' := by
  have hτ : ∀ x : E, τ (cc x) = (starRingEnd ℂ) (τ x) := fun x => by
    first
    | exact IsCMField.complexEmbedding_complexConj τ x
    | exact IsCMField.complexEmbedding_complexConj (K := E) τ x
    | simp [cc, IsCMField.complexEmbedding_complexConj]
    | simp [cc]
  obtain ⟨U, hU⟩ : ∃ U : Matrix (Fin r) (Fin ρ) ℂ, U = Matrix.of fun k a => τ (cu.e a k) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin ρ) (Fin r) ℂ,
      V = Matrix.of fun b l => ∑ k', τ (X.Gm l k') * (starRingEnd ℂ) (τ (cu.e b k')) := ⟨_, rfl⟩
  have hZ : ∀ γ, zMatC X cu.e τ γ = 1 + U * γ * V := by
    intro γ
    ext k l
    simp only [zMatC, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, hU, hV]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hVU : V * U = 0 := by
    ext b c
    have h0 := congrArg τ (cu.3 c b)
    simp only [herm, map_sum, map_mul, hτ, map_zero] at h0
    simp only [Matrix.mul_apply, hU, hV, Matrix.of_apply, Matrix.zero_apply, Finset.sum_mul]
    rw [← h0]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k' _ => by ring
  have key : U * β * V * (U * β' * V) = 0 := by
    calc U * β * V * (U * β' * V) = U * β * (V * U) * β' * V := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hVU]; simp
  rw [hZ, hZ, hZ]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, key, add_zero]
  abel
end Formalism.L2.Pj.QAt
