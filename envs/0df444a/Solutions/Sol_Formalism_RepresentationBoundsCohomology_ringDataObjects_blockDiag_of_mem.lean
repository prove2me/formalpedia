-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.blockDiag_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:36:37.997891+00:00
-- url     : https://prove2.me/submissions/27c24781-7b3f-4f44-afd5-88748e77fc91

import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_FinrankRangeEq
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdemFactor
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_IdempotentImageSurjective
import Definitions.Def_Formalism_WachLatticeTwists_RamifiedBlockRings_RamifiedBlockProofs_DensityPointOfCornerSimple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.RepresentationBoundsCohomology Formalism.RepresentationBoundsCohomology.ringDataObjects
open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
variable {O : Type} [CommRing O] [IsDomain O] {X : Type} (T : Subalgebra O (X → O)) {d : Type} [Fintype d]
  [DecidableEq d] {G : Type} [Group G] (r : G →* (X → Matrix d d O))
namespace Formalism.RepresentationBoundsCohomology.ringDataObjects
theorem _root_.solution (x : X) {m : ℕ} (c : d → Fin m) (P : Matrix d d (FractionRing O))
    (h : ∀ g i j, c i ≠ c j → (P * (r g x).map (algebraMap O (FractionRing O)) * P⁻¹) i j = 0)
    (a : X → Matrix d d O) (ha : a ∈ tSpan T r) :
    ∀ i j, c i ≠ c j → (P * (a x).map (algebraMap O (FractionRing O)) * P⁻¹) i j = 0 := by
  intro i j hij
  obtain ⟨s, cc, hcc, rfl⟩ := ha
  have hN : ((∑ g ∈ s, fun y => algebraMap O O (cc g y) • r g y) x).map (algebraMap O (FractionRing O)) =
      ∑ g ∈ s, algebraMap O (FractionRing O) (cc g x) • (r g x).map (algebraMap O (FractionRing O)) := by
    ext k l
    simp [Finset.sum_apply, Matrix.sum_apply, map_sum, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Algebra.smul_def]
  rw [hN, Finset.mul_sum, Finset.sum_mul, Matrix.sum_apply]
  exact Finset.sum_eq_zero fun g _ => by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, h g i j hij, smul_zero]
end Formalism.RepresentationBoundsCohomology.ringDataObjects
