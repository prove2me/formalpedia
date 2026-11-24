-- Prove2me | solution 1 for Formalism.HN.QuotientRealization.proj_eq_tv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:50.943944+00:00
-- url     : https://prove2.me/submissions/a551a168-047a-43db-98d3-df01cef77774

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SlopeIneqMean
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_QuotRealize
import Theorems.Thm_Formalism_HN_QuotientRealization_sub_mem_of_lift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField Matrix
noncomputable section
namespace Formalism.HN
namespace QuotientRealization
section Covol
variable {E F M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [AddCommGroup M]
end Covol
section Psi
variable {P ι : Type*} [Fintype P] [DecidableEq P] [Fintype ι]
end Psi
section Main
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
private theorem fcoord_smul_harder_narasimhan (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (a : K) (x : V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (a • x) = v.embedding a • Formalism.HermitianLatticesTheory.fcoord b X v x := by
  have h1 : Formalism.HermitianLatticesTheory.vecAt b v (a • x) = v.embedding a • Formalism.HermitianLatticesTheory.vecAt b v x := by
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  simp only [Formalism.HermitianLatticesTheory.fcoord, h1, Matrix.mulVec_smul]
private theorem fcoord_finset_sum_smul {κ : Type} (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (s : Finset κ) (r : κ → K) (c : κ → V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (∑ k ∈ s, r k • c k) =
      ∑ k ∈ s, v.embedding (r k) • Formalism.HermitianLatticesTheory.fcoord b X v (c k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Formalism.HermitianLatticesTheory.fcoord_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Formalism.HermitianLatticesTheory.fcoord_add, ih, fcoord_smul_harder_narasimhan]
section Lift
variable (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (U : Submodule K V)
  {κ : Type} [Fintype κ] [DecidableEq κ] (b'' : Basis κ K (V ⧸ U)) (c : κ → V)
end Lift
end Main
end QuotientRealization
end Formalism.HN
end
end

set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.QuotientRealization
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
variable (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (U : Submodule K V)
  {κ : Type} [Fintype κ] [DecidableEq κ] (b'' : Basis κ K (V ⧸ U)) (c : κ → V)
namespace Formalism.HN.QuotientRealization
theorem _root_.solution (hc : ∀ k, U.mkQ (c k) = b'' k) (v : InfinitePlace K) (x : V) :
    (pv b X U v)ᗮ.starProjection (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x)) =
      tv b X U c v (fun k => v.embedding (b''.repr (U.mkQ x) k)) := by
  set r := b''.repr (U.mkQ x) with hr
  let L : (ι → ℂ) →ₗ[ℂ] EuclideanSpace ℂ ι := ((pv b X U v)ᗮ.starProjection).toLinearMap ∘ₗ
    (WithLp.linearEquiv 2 ℂ (ι → ℂ)).symm.toLinearMap
  have hL : ∀ w, L w = (pv b X U v)ᗮ.starProjection (WithLp.toLp 2 w) := fun w => rfl
  have hm : WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v (x - ∑ k, r k • c k)) ∈ pv b X U v :=
    Submodule.subset_span ⟨_, sub_mem_of_lift U b'' c hc x, rfl⟩
  have h0 : L (Formalism.HermitianLatticesTheory.fcoord b X v (x - ∑ k, r k • c k)) = 0 := by
    rw [hL]
    first
      | exact (Submodule.starProjection_apply_eq_zero_iff _).mpr (Submodule.le_orthogonal_orthogonal _ hm)
      | exact (Submodule.starProjection_eq_zero_iff _).mpr (Submodule.le_orthogonal_orthogonal _ hm)
      | simp [Submodule.le_orthogonal_orthogonal _ hm]
      | simpa using Submodule.le_orthogonal_orthogonal _ hm
  have hsplit : Formalism.HermitianLatticesTheory.fcoord b X v x = Formalism.HermitianLatticesTheory.fcoord b X v (x - ∑ k, r k • c k) +
      ∑ k, v.embedding (r k) • Formalism.HermitianLatticesTheory.fcoord b X v (c k) := by
    rw [← fcoord_finset_sum_smul, ← Formalism.HermitianLatticesTheory.fcoord_add, sub_add_cancel]
  rw [← hL, hsplit, map_add, h0, zero_add, map_sum, tv, Fintype.linearCombination_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, hL]
end Formalism.HN.QuotientRealization
