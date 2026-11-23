-- Prove2me | solution 1 for Formalism.DimensionVariation.column_paths
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:59.069804+00:00
-- url     : https://prove2.me/submissions/b1db843a-1b9b-49de-ab6f-17d49b87a93b

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementCB
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_PerEmbeddingCoupledBound
import Theorems.Thm_Formalism_DimensionVariation_sharp_entries
import Theorems.Thm_Formalism_DimensionVariation_path_sum_alt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues (fnorm chainFun chainMat)
open CB
namespace Formalism.DimensionVariation
theorem _root_.solution : ColPaths := by
  intro m AA _ _ Cl _ W _ _ γ ε T G
  have hA : ∀ i : Fin (m + 1), (fun (a : AA i) (L : Cl i a) =>
      chainFun (C := fun i => (Σ a, Cl i a) → W i) (fun j => liftOp (γ j.castSucc) (ε j) (T j)) i G ⟨a, L⟩) =
      chainFun (C := fun i => ∀ a, Cl i a → W i)
        (fun j => blockMap (entryHom (γ j.castSucc) (ε j) (T j))) i (fun a L => G ⟨a, L⟩) := by
    intro i
    induction i using Fin.induction with
    | zero => rfl
    | succ j ih =>
      funext b L'
      change liftOp (γ j.castSucc) (ε j) (T j) (chainFun (C := fun i => (Σ a, Cl i a) → W i)
        (fun j => liftOp (γ j.castSucc) (ε j) (T j)) j.castSucc G) ⟨b, L'⟩ =
        blockMap (entryHom (γ j.castSucc) (ε j) (T j)) (chainFun (C := fun i => ∀ a, Cl i a → W i)
        (fun j => blockMap (entryHom (γ j.castSucc) (ε j) (T j))) j.castSucc (fun a L => G ⟨a, L⟩)) b L'
      rw [← ih]
      exact (sharp_entries _ _ _ _ _ _ _ _ _ _).1 b L'
  rw [hA]
  exact path_sum_alt m AA (fun i a => Cl i a → W i)
    (fun j a b => entryHom (γ j.castSucc) (ε j) (T j) a b) (fun a L => G ⟨a, L⟩)
end Formalism.DimensionVariation
