-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.SplitEmbedding.idealLattice_fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:38.083938+00:00
-- url     : https://prove2.me/submissions/e652530d-0ce4-4a08-b923-f4d3f7610a2a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CosetFd
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MeasurablePhiInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped Classical Pointwise
open MeasureTheory NumberField NumberField.mixedEmbedding
namespace Formalism.L2.SG.NGCut.SplitEmbedding
section Inv
variable {K : Type} [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}] {ι : Type} [Fintype ι]
  (σ : ι ≃ {w : InfinitePlace K // w.IsComplex}) (cj : ι → Prop) [DecidablePred cj]
end Inv
private theorem mem_idealLattice_iff' (K : Type) [Field K] [NumberField K]
    (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) (x : mixedSpace K) :
    x ∈ idealLattice K I ↔ ∃ a : K, a ∈ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ∧ mixedEmbedding K a = x := by
  first
  | (rw [mem_idealLattice]; rfl)
  | exact mem_idealLattice K I
  | simp [idealLattice]
end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
open MeasureTheory NumberField NumberField.mixedEmbedding
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.SplitEmbedding
namespace Formalism.L2.SG.NGCut.SplitEmbedding
theorem _root_.solution (K : Type) [Field K] [NumberField K] (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) :
    ∃ FL : Set (mixedSpace K), MeasurableSet FL ∧
      (∀ x, ∃! l : (idealLattice K I).toAddSubgroup, (l : mixedSpace K) + x ∈ FL) := by
  let b := fractionalIdealLatticeBasis K I
  have hmem : ∀ y : mixedSpace K, y ∈ (idealLattice K I).toAddSubgroup ↔ y ∈ Submodule.span ℤ (Set.range b) := by
    intro y
    rw [Submodule.mem_toAddSubgroup, mem_idealLattice_iff', mem_span_fractionalIdealLatticeBasis, Set.mem_image]
    rfl
  refine ⟨ZSpan.fundamentalDomain b, ZSpan.fundamentalDomain_measurableSet b, fun x => ?_⟩
  obtain ⟨l, hl, hu⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b x
  refine ⟨⟨l, (hmem l).2 l.2⟩, by simpa [Submodule.vadd_def, vadd_eq_add] using hl, ?_⟩
  rintro ⟨m, hm⟩ hm'
  have h2 := hu ⟨m, (hmem m).1 hm⟩ (by simpa [Submodule.vadd_def, vadd_eq_add] using hm')
  have h3 : m = (l : mixedSpace K) := congrArg Subtype.val h2
  exact Subtype.ext h3
end Formalism.L2.SG.NGCut.SplitEmbedding
