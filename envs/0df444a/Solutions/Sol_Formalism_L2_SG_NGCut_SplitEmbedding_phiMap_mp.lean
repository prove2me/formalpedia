-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.SplitEmbedding.phiMap_mp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:23:48.777477+00:00
-- url     : https://prove2.me/submissions/4449df79-44d3-455f-8717-b3d54ca328af

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MassSplit
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_PhiMapAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical
open MeasureTheory NumberField NumberField.mixedEmbedding
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.SplitEmbedding
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  (σ : ι ≃ {w : InfinitePlace K // w.IsComplex}) (cj : ι → Prop) [DecidablePred cj]
namespace Formalism.L2.SG.NGCut.SplitEmbedding
theorem _root_.solution [IsEmpty {w : InfinitePlace K // w.IsReal}] :
    MeasurePreserving (phiMap σ cj) volume volume := by
  have hu : (volume : Measure ({w : InfinitePlace K // w.IsReal} → ℝ)) Set.univ = 1 := by
    first
    | (rw [volume_pi, Measure.pi_of_empty]; simp)
    | (rw [volume_pi, Measure.pi_univ]; simp)
    | simp [volume_pi, Measure.pi_univ]
    | (erw [Measure.pi_univ]; simp)
  have h1 : MeasurePreserving (Prod.snd : mixedSpace K → ({w : InfinitePlace K // w.IsComplex} → ℂ))
      volume volume := by
    refine ⟨measurable_snd, ?_⟩
    rw [Measure.volume_eq_prod, Measure.map_snd_prod]
    first
    | rw [hu, one_smul]
    | simp only [hu, one_smul]
    | (convert one_smul ENNReal (volume : Measure ({w : InfinitePlace K // w.IsComplex} → ℂ)); exact hu)
  have h2 : MeasurePreserving (fun (y : {w : InfinitePlace K // w.IsComplex} → ℂ) (i : ι) => y (σ i))
      volume volume :=
    MeasurePreserving.symm _
      (measurePreserving_piCongrLeft (fun _ : {w : InfinitePlace K // w.IsComplex} => (volume : Measure ℂ)) σ)
  have hc : MeasurePreserving (starRingEnd ℂ) (volume : Measure ℂ) volume := by
    have := Complex.conjLIE.measurePreserving
    convert this using 2
    all_goals first | rfl | (funext z; simp) | (ext z; simp)
  have h3 : MeasurePreserving (fun (z : ι → ℂ) (i : ι) => if cj i then starRingEnd ℂ (z i) else z i)
      (Measure.pi fun _ => (volume : Measure ℂ)) (Measure.pi fun _ => (volume : Measure ℂ)) := by
    refine measurePreserving_pi (fun _ => (volume : Measure ℂ)) (fun _ => (volume : Measure ℂ))
      (f := fun i c => if cj i then starRingEnd ℂ c else c) (fun i => ?_)
    by_cases h : cj i
    · first
      | (simp only [if_pos h]; exact hc)
      | simpa [h] using hc
    · first
      | (simp only [if_neg h]; exact MeasurePreserving.id _)
      | simp [h, MeasurePreserving.id]
  first
  | exact h3.comp (h2.comp h1)
  | (rw [volume_pi]; exact h3.comp (h2.comp h1))
end Formalism.L2.SG.NGCut.SplitEmbedding
