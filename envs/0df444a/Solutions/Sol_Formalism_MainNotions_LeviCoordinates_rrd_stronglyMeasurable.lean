-- Prove2me | solution 1 for Formalism.MainNotions.LeviCoordinates.rrd_stronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:06:50.329412+00:00
-- url     : https://prove2.me/submissions/14049fa3-f66c-4348-9a7d-7c4dbfd56718

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_UnimodularSchurMeasures_RrdStronglyMeasurable
import Theorems.Thm_Formalism_MainNotions_LeviCoordinates_rrd_countable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.LeviCoordinates
open MeasureTheory Filter Topology Set TopologicalSpace
open scoped InnerProductSpace
namespace Formalism.MainNotions.LeviCoordinates
theorem _root_.solution {α : Type*} [MeasurableSpace α] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [SeparableSpace H] (F : α → H)
    (hF : ∀ x, StronglyMeasurable fun a => ⟪x, F a⟫_ℂ) : StronglyMeasurable F := by
  classical
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ H
  haveI : Countable w := rrd_countable b.orthonormal
  haveI : Encodable w := Encodable.ofCountable w
  have hterm : ∀ i : w, StronglyMeasurable fun a => ⟪b i, F a⟫_ℂ • b i := by
    intro i
    first
    | exact (hF (b i)).smul_const (b i)
    | exact (hF (b i)).smul stronglyMeasurable_const
  have hfin : ∀ s : Finset w, StronglyMeasurable fun a => ∑ i ∈ s, ⟪b i, F a⟫_ℂ • b i := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simp only [Finset.sum_empty]
      exact stronglyMeasurable_const
    · intro i t hi ih
      simp only [Finset.sum_insert hi]
      exact (hterm i).add ih
  have hlim : Tendsto (fun (s : Finset w) (a : α) => ∑ i ∈ s, ⟪b i, F a⟫_ℂ • b i) atTop (𝓝 F) := by
    rw [tendsto_pi_nhds]
    intro a
    have h := b.hasSum_repr (F a)
    simp only [HilbertBasis.repr_apply_apply] at h
    exact h
  first
  | exact stronglyMeasurable_of_tendsto atTop hfin hlim
  | exact StronglyMeasurable.of_tendsto atTop hfin hlim
end Formalism.MainNotions.LeviCoordinates
