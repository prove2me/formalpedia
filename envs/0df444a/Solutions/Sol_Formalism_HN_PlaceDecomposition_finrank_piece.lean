-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.finrank_piece
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:09.948702+00:00
-- url     : https://prove2.me/submissions/e1f94f8b-1eee-4178-82f9-e662bfaf9519

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Theorems.Thm_Formalism_HN_PlaceDecomposition_psi_injective
import Theorems.Thm_Formalism_HN_PlaceDecomposition_finrank_real_span
import Theorems.Thm_Formalism_HN_PlaceDecomposition_piece_eq_map

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
  [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace K)]
namespace Formalism.HN.PlaceDecomposition
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (N : Submodule (𝓞 K) V) (v : InfinitePlace K) :
    Module.finrank ℝ (Submodule.span ℝ (zl (Formalism.HermitianLatticesTheory.realize b X) N :
        Set (EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2))) ⊓ placePart v : Submodule ℝ _) =
      2 * rkK N := by
  rw [piece_eq_map, ← (Submodule.equivMapOfInjective (psi v) (psi_injective (ι := ι) v) _).finrank_eq]
  exact finrank_real_span b X hX N v
end Formalism.HN.PlaceDecomposition
