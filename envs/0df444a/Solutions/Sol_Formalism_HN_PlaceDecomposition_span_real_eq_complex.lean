-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.span_real_eq_complex
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:57.372495+00:00
-- url     : https://prove2.me/submissions/a0e8794f-30dc-47d7-9855-a90b1ed934ed

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Theorems.Thm_Formalism_HN_PlaceDecomposition_dense_comb
import Theorems.Thm_Formalism_HN_PlaceDecomposition_fcoord_osmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PlaceDecomposition
variable {K V ι : Type*} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HN.PlaceDecomposition
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (N : Submodule (𝓞 K) V) (v : InfinitePlace K) :
    (Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V))).restrictScalars ℝ =
      Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V)) := by
  have hmul : ∀ (c : 𝓞 K) (w : ι → ℂ), w ∈ Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V)) →
      v.embedding (c : K) • w ∈ Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V)) := by
    intro c w hw
    have key : Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V)) ≤
        (Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V))).comap
          (DistribMulAction.toLinearMap ℝ (ι → ℂ) (v.embedding (c : K))) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      show v.embedding (c : K) • Formalism.HermitianLatticesTheory.fcoord b X v x ∈
        Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V))
      rw [← fcoord_osmul]
      exact Submodule.subset_span ⟨c • x, N.smul_mem c hx, rfl⟩
    exact key hw
  have hC : ∀ (z : ℂ) (w : ι → ℂ), w ∈ Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V)) →
      z • w ∈ Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V)) := by
    intro z w hw
    obtain ⟨r, hr⟩ := dense_comb K (fun _ => z)
    have hz : ∑ k, (r k : ℂ) * v.embedding ((RingOfIntegers.basis K k : 𝓞 K) : K) = z := hr v
    rw [← hz, Finset.sum_smul]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [mul_smul, Complex.coe_smul]
    exact Submodule.smul_mem _ _ (hmul _ w hw)
  let W : Submodule ℂ (ι → ℂ) :=
    { carrier := (Submodule.span ℝ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V)) : Set (ι → ℂ))
      add_mem' := fun ha hb => Submodule.add_mem _ ha hb
      zero_mem' := Submodule.zero_mem _
      smul_mem' := fun z w hw => hC z w hw }
  apply le_antisymm
  · intro w hw
    have hle : Submodule.span ℂ (Formalism.HermitianLatticesTheory.fcoord b X v '' (N : Set V)) ≤ W :=
      Submodule.span_le.2 (fun x hx => Submodule.subset_span hx)
    exact hle hw
  · exact Submodule.span_le_restrictScalars ℝ ℂ _
end Formalism.HN.PlaceDecomposition
