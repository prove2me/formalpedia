-- Prove2me | solution 1 for Formalism.HN.PlaceDecomposition.dense_comb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:55:55.658828+00:00
-- url     : https://prove2.me/submissions/f1304bb6-2001-43f0-a462-11d6fe7c4dea

import Definitions.Def_Formalism_HarderNarasimhan_DefsPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit

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
namespace Formalism.HN.PlaceDecomposition
theorem _root_.solution (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]
    (t : InfinitePlace K → ℂ) :
    ∃ r : Free.ChooseBasisIndex ℤ (𝓞 K) → ℝ, ∀ u : InfinitePlace K,
      ∑ k, (r k : ℂ) * u.embedding ((RingOfIntegers.basis K k : 𝓞 K) : K) = t u := by
  obtain ⟨y, hy0⟩ : ∃ y : mixedEmbedding.mixedSpace K,
      ∀ w : {w : InfinitePlace K // w.IsComplex}, y.2 w = t w.1 :=
    ⟨(0, fun w => t w.1), fun _ => rfl⟩
  refine ⟨fun k => (mixedEmbedding.latticeBasis K).repr y k, fun u => ?_⟩
  have hu : u.IsComplex := by
    first
      | exact IsTotallyComplex.isComplex u
      | exact NumberField.IsTotallyComplex.isComplex u
  have hy := congrArg (fun z : mixedEmbedding.mixedSpace K => z.2 ⟨u, hu⟩)
    ((mixedEmbedding.latticeBasis K).sum_repr y)
  simp only [Prod.snd_sum, Finset.sum_apply, Prod.smul_snd, Pi.smul_apply,
    mixedEmbedding.latticeBasis_apply, hy0] at hy
  rw [← hy]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.real_smul]
  congr 1
  rw [NumberField.integralBasis_apply]
  rfl
end Formalism.HN.PlaceDecomposition
