-- Prove2me | solution 1 for Formalism.RepresentationBoundsCohomology.ringDataObjects.clearDen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:36:44.270459+00:00
-- url     : https://prove2.me/submissions/bbd93ac4-93b5-48b0-890c-50decd425813

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
theorem _root_.solution (x : X) (A : Matrix d d (FractionRing O))
    (hA : A ∈ Submodule.span (FractionRing O)
      (Set.range fun g => (r g x).map (algebraMap O (FractionRing O)))) :
    ∃ b : O, b ≠ 0 ∧ ∃ a ∈ tSpan T r,
      (a x).map (algebraMap O (FractionRing O)) = algebraMap O (FractionRing O) b • A := by
  classical
  obtain ⟨cf, hcf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hA
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (R := O) (M := nonZeroDivisors O)
    cf.support cf
  have hint : ∀ g, ∃ y : O, algebraMap O (FractionRing O) y = (b : O) • cf g := by
    intro g
    by_cases hg : g ∈ cf.support
    · exact RingHom.mem_rangeS.mp (hb g hg)
    · rw [Finsupp.mem_support_iff, not_not] at hg
      exact ⟨0, by simp [hg]⟩
  choose o ho using hint
  refine ⟨b, nonZeroDivisors.ne_zero b.2,
    ∑ g ∈ cf.support, fun y => algebraMap O O ((fun g (_ : X) => o g) g y) • r g y, ?_, ?_⟩
  · unfold tSpan
    exact ⟨cf.support, fun g _ => o g, fun g => T.algebraMap_mem (o g), rfl⟩
  · have ho' : ∀ g, algebraMap O (FractionRing O) (o g) =
        algebraMap O (FractionRing O) (b : O) * cf g := fun g => by rw [ho, Algebra.smul_def]
    ext i j
    rw [← hcf]
    simp only [Finsupp.sum, Finset.sum_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, Algebra.algebraMap_self_apply, map_sum, map_mul, ho', Finset.mul_sum, mul_assoc]
end Formalism.RepresentationBoundsCohomology.ringDataObjects
