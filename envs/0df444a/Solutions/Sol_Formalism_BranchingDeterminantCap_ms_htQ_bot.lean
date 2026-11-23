-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.ms_htQ_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:15.063041+00:00
-- url     : https://prove2.me/submissions/4bd10c2c-7555-400a-a81e-16658e2eee40

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Theorems.Thm_Formalism_BranchingDeterminantCap_ms_rkK_bot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.HN
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (A : Submodule (𝓞 K) V) : htQ b X A ⊥ = ht b X A := by
  have hz : zl (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) = ⊥ := by
    unfold Formalism.HN.zl
    simp
  have hq : ∀ L : Submodule ℤ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)),
      Formalism.F.quot L ⊥ = L := by
    intro L
    unfold Formalism.F.quot
    have hp : ∀ y : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2),
        (Submodule.span ℝ ((⊥ : Submodule ℤ (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) :
          Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))))ᗮ.starProjection y = y := by
      intro y
      simp only [Submodule.bot_coe, Submodule.span_zero_singleton, Submodule.bot_orthogonal_eq_top]
      first
        | (rw [Submodule.starProjection_eq_self_iff]; exact Submodule.mem_top)
        | simp [Submodule.starProjection_top]
        | exact Submodule.starProjection_top_apply y
    ext x
    simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, ContinuousLinearMap.coe_coe, hp]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  unfold Formalism.HN.htQ Formalism.HN.ht
  rw [ms_rkK_bot, hz, hq]
  simp only [Nat.cast_zero, sub_zero]
  congr 2
  rw [← Real.rpow_natCast, Nat.cast_mul]
end Formalism.BranchingDeterminantCap
