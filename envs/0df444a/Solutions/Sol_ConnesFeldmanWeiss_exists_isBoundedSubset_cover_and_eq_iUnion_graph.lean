-- Prove2me | solution 1 for ConnesFeldmanWeiss.exists_isBoundedSubset_cover_and_eq_iUnion_graph
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T15:49:08.064026+00:00
-- url     : https://prove2.me/submissions/fa2c6c22-f3d2-42b2-af21-3568a8fccab9

import Theorems.Thm_LusinNovikov_exists_disjoint_injOn_fst_iUnion_eq_of_countable_sections
import Theorems.Thm_LusinNovikov_measurableSet_image_fst_of_countable_sections
import Mathlib
import Definitions.Def_Monod_PiecewiseProjective
import Theorems.Thm_ConnesFeldmanWeiss_exists_seq_measurableEquiv_of_countable_classes
import Definitions.Def_ConnesFeldmanWeiss

section
section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
/-!
# Route to Lusin–Novikov and Feldman–Moore (lemma list, all `sorry`)

Each lemma's docstring gives the proof idea, the Mathlib API (every name checked with `#check`
against Mathlib `0df444a3`), and a size estimate in lines of Lean. See `PLAN.md` for the
narrative.

* §A: **Shinko's Lusin–Novikov theorem**, metric form (F. Shinko, *Lusin–Novikov via σ-ideals*,
  2024; local copy `sources/shinko-lusin-novikov-via-sigma-ideals.pdf`). A continuous map from a
  complete separable metric space with countable fibres is covered by countably many Borel
  partial sections. The proof uses no analytic sets, only closed sets, Borel sets, and Cantor's
  intersection theorem.
* §B: glue to standard Borel spaces, giving (LN-1)…(LN-5) of `Statements.lean`.
* §C: Feldman–Moore, giving (FM) and (FM-group) of `Statements.lean`.
* §D: the CFW-facing consequences: the counting measure `m`, CFW Lemma 3(a), CFW Lemma 3(b), and
  the left-to-right mean swap. These are downstream, not part of LN/FM.
-/
/-! ## §A. Shinko's theorem (metric form) -/

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
/-!
# §A of the Lusin–Novikov route: Shinko's theorem (metric form), proved

Proofs of every theorem in §A (`section Shinko`) of `Solutions.LN.Blueprint`, restated verbatim
in the namespace `CFWPlan.Route.PartA`. The definitions `IsBorelSection`, `InI` and `IsNullFam`
are the Blueprint's (`CFWPlan.Route.*`). The argument follows F. Shinko, *Lusin–Novikov via
σ-ideals* (2024).

Note on names: inside this namespace an unqualified `InI.mono` resolves to
`CFWPlan.Route.PartA.InI.mono` (innermost namespace first), but dot notation `h.mono` on
`h : InI f A` would resolve to the Blueprint's unproved stub `CFWPlan.Route.InI.mono`, so the proofs
below never use dot notation on `InI` / `IsNullFam` hypotheses.
-/
/-! ### A1. The σ-ideal `I` -/

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-! ### A2–A5. Null families -/

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
/-! ### A6–A7. Shinko's two observations -/

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
/-! ### A8. One level of the Cantor scheme -/

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
/-! ### A9–A11. The Cantor scheme and the theorem -/

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Route.PartA
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route.PartA
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route.PartB
/-!
# §B of the Lusin–Novikov route: glue to standard Borel spaces

Proofs of the four §B targets of `Solutions/LN/Blueprint.lean` (section `Glue`), from the metric
form `CFWPlan.Route.inI_univ_of_countable_fibers` (§A11), following the template of Mathlib's
proof of `MeasurableSet.image_of_measurable_injOn`.
-/

end CFWPlan.Route.PartB
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route.PartB
variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]

end CFWPlan.Route.PartB
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]
/-! ## §B. Glue to standard Borel spaces -/

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route.PartB
variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]
/-- **B2 = (LN-2).** -/
theorem lusinNovikov {P : Set (X × Y)} (hP : MeasurableSet P)
    (hcount : ∀ x, {y | (x, y) ∈ P}.Countable) :
    ∃ G : ℕ → Set (X × Y), (∀ n, MeasurableSet (G n)) ∧ (∀ n, InjOn Prod.fst (G n)) ∧
      Pairwise (Disjoint on G) ∧ ⋃ n, G n = P :=
  by
  try haveI := hP; try haveI := hcount; first
    | exact LusinNovikov.exists_disjoint_injOn_fst_iUnion_eq_of_countable_sections hP hcount
    | exact LusinNovikov.exists_disjoint_injOn_fst_iUnion_eq_of_countable_sections
    | exact LusinNovikov.exists_disjoint_injOn_fst_iUnion_eq_of_countable_sections ..
    | (apply LusinNovikov.exists_disjoint_injOn_fst_iUnion_eq_of_countable_sections <;> first | assumption | infer_instance)
    | simpa using LusinNovikov.exists_disjoint_injOn_fst_iUnion_eq_of_countable_sections

end CFWPlan.Route.PartB
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]
alias lusinNovikov := CFWPlan.Route.PartB.lusinNovikov

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route.PartB
variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]
/-- **B3 = (LN-3).** -/
theorem measurableSet_image_fst {P : Set (X × Y)} (hP : MeasurableSet P)
    (hcount : ∀ x, {y | (x, y) ∈ P}.Countable) : MeasurableSet (Prod.fst '' P) :=
  by
  try haveI := hP; try haveI := hcount; first
    | exact LusinNovikov.measurableSet_image_fst_of_countable_sections hP hcount
    | exact LusinNovikov.measurableSet_image_fst_of_countable_sections
    | exact LusinNovikov.measurableSet_image_fst_of_countable_sections ..
    | (apply LusinNovikov.measurableSet_image_fst_of_countable_sections <;> first | assumption | infer_instance)
    | simpa using LusinNovikov.measurableSet_image_fst_of_countable_sections

end CFWPlan.Route.PartB
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]
alias measurableSet_image_fst := CFWPlan.Route.PartB.measurableSet_image_fst

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route.PartB
variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]

end CFWPlan.Route.PartB
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §C. Feldman–Moore -/
/-- The graph of a partial transformation (same as `CFWPlan.ptGraph` in `Statements.lean`). -/
def ptGraph {R : Set (X × X)} (φ : Monod.PartialTransformation R) : Set (X × X) :=
  range fun a : φ.dom => ((a : X), (φ.e a : X))

end CFWPlan.Route
end

section
open MeasureTheory Set Function
namespace CFWPlan.Route.PartC
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-!
# §C. Feldman–Moore (proofs of the Blueprint §C lemmas) and the CFW milestone

The §C lemmas of `Solutions.LN.Blueprint`, restated verbatim in `CFWPlan.Route.PartC` and proved
from the §B stub `CFWPlan.Route.lusinNovikov` (Lusin–Novikov) and Mathlib's Lusin–Souslin
theorem. The CFW milestone `exists_seq_measurableEquiv_of_countable_classes` (Feldman–Moore,
involution form) is then proved as `ConnesFeldmanWeiss.chk_exists_seq_measurableEquiv_of_countable_classes`.
-/
/-- On a Borel set `G ⊆ X × X` on which `Prod.fst` is injective, `Prod.fst ∘ val` is a measurable
embedding (Lusin–Souslin). -/
theorem measurableEmbedding_fst_of_injOn {G : Set (X × X)} (hG : MeasurableSet G)
    (h₁ : InjOn Prod.fst G) :
    MeasurableEmbedding (fun p : G => (p : X × X).1) := by
  have := hG.standardBorel
  exact (measurable_fst.comp measurable_subtype_coe).measurableEmbedding
    fun p q h => Subtype.ext (h₁ p.2 q.2 h)

/-- On a Borel set `G ⊆ X × X` on which `Prod.snd` is injective, `Prod.snd ∘ val` is a measurable
embedding (Lusin–Souslin). -/
theorem measurableEmbedding_snd_of_injOn {G : Set (X × X)} (hG : MeasurableSet G)
    (h₂ : InjOn Prod.snd G) :
    MeasurableEmbedding (fun p : G => (p : X × X).2) := by
  have := hG.standardBorel
  exact (measurable_snd.comp measurable_subtype_coe).measurableEmbedding
    fun p q h => Subtype.ext (h₂ p.2 q.2 h)

/-- **C1. Bi-injective cover.** -/
theorem exists_biInjOn_cover {R : Set (X × X)} (hR : MeasurableSet R)
    (hcount : ∀ x, {y | (x, y) ∈ R}.Countable) (hcount' : ∀ y, {x | (x, y) ∈ R}.Countable) :
    ∃ G : ℕ → Set (X × X), (∀ n, MeasurableSet (G n)) ∧ (∀ n, InjOn Prod.fst (G n)) ∧
      (∀ n, InjOn Prod.snd (G n)) ∧ Pairwise (Disjoint on G) ∧ ⋃ n, G n = R := by
  obtain ⟨A, hAm, hAi, hAd, hAU⟩ := CFWPlan.Route.lusinNovikov hR hcount
  obtain ⟨B, hBm, hBi, hBd, hBU⟩ := CFWPlan.Route.lusinNovikov (X := X) (Y := X)
    (P := Prod.swap ⁻¹' R) (measurable_swap hR) (fun y => by simpa using hcount' y)
  refine ⟨fun n => A n.unpair.1 ∩ Prod.swap ⁻¹' B n.unpair.2, fun n =>
    (hAm _).inter (measurable_swap (hBm _)), fun n => (hAi _).mono inter_subset_left, ?_, ?_, ?_⟩
  · intro n p hp q hq h
    exact Prod.swap_injective (hBi n.unpair.2 hp.2 hq.2 h)
  · intro m n hmn
    have hne : m.unpair ≠ n.unpair := fun h => hmn (by
      rw [← Nat.pair_unpair m, ← Nat.pair_unpair n, h])
    by_cases h1 : m.unpair.1 = n.unpair.1
    · have h2 : m.unpair.2 ≠ n.unpair.2 := fun h2 => hne (Prod.ext h1 h2)
      exact Disjoint.mono inter_subset_right inter_subset_right ((hBd h2).preimage _)
    · exact Disjoint.mono inter_subset_left inter_subset_left (hAd h1)
  · apply Subset.antisymm
    · exact iUnion_subset fun n => inter_subset_left.trans (hAU ▸ subset_iUnion A _)
    · intro p hp
      have hpA : p ∈ ⋃ i, A i := hAU ▸ hp
      have hpB : Prod.swap p ∈ ⋃ j, B j := hBU ▸ hp
      obtain ⟨i, hi⟩ := mem_iUnion.1 hpA
      obtain ⟨j, hj⟩ := mem_iUnion.1 hpB
      refine mem_iUnion.2 ⟨Nat.pair i j, ?_, ?_⟩
      · simpa [Nat.unpair_pair] using hi
      · simpa [Nat.unpair_pair] using hj

end CFWPlan.Route.PartC
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias exists_biInjOn_cover := CFWPlan.Route.PartC.exists_biInjOn_cover

end CFWPlan.Route
end

section
open MeasureTheory Set Function
namespace CFWPlan.Route.PartC
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-- **C2. A bi-injective Borel subset of `R` is the graph of a `Monod.PartialTransformation`.** -/
theorem exists_partialTransformation_of_biInjOn {R G : Set (X × X)} (hG : MeasurableSet G)
    (hGR : G ⊆ R) (h₁ : InjOn Prod.fst G) (h₂ : InjOn Prod.snd G) :
    ∃ φ : Monod.PartialTransformation R, ptGraph φ = G := by
  have := hG.standardBorel
  have e₁ := measurableEmbedding_fst_of_injOn hG h₁
  have e₂ := measurableEmbedding_snd_of_injOn hG h₂
  have key : ∀ p : G, (e₁.equivRange.symm.trans e₂.equivRange) (e₁.equivRange p) =
      e₂.equivRange p := fun p => by simp
  refine ⟨⟨range (fun p : G => (p : X × X).1), range (fun p : G => (p : X × X).2),
    e₁.measurableSet_range, e₂.measurableSet_range, e₁.equivRange.symm.trans e₂.equivRange, ?_⟩,
    ?_⟩
  · intro a
    obtain ⟨p, rfl⟩ := e₁.equivRange.surjective a
    rw [key]
    simpa [MeasurableEmbedding.equivRange_apply] using hGR p.2
  · ext q
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨p, rfl⟩ := e₁.equivRange.surjective a
      simp only
      rw [key]
      simp [MeasurableEmbedding.equivRange_apply]
    · intro hq
      refine ⟨e₁.equivRange ⟨q, hq⟩, ?_⟩
      simp only
      rw [key]
      simp [MeasurableEmbedding.equivRange_apply]

end CFWPlan.Route.PartC
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias exists_partialTransformation_of_biInjOn := CFWPlan.Route.PartC.exists_partialTransformation_of_biInjOn

end CFWPlan.Route
end

section
open MeasureTheory Set Function
namespace CFWPlan.Route.PartC
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Route.PartC
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Route
end

section
open MeasureTheory Set Function
namespace CFWPlan.Route.PartC
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Route.PartC
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route.PartD
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-!
# §D of the Lusin–Novikov route: the CFW-facing consequences

Proofs of the five §D targets of `Solutions/LN/Blueprint.lean` (section `Downstream`), from the
§B/§C statements of the Blueprint (`lusinNovikov`, `measurableSet_image_fst`,
`exists_biInjOn_cover`, `exists_partialTransformation_of_biInjOn`) and Mathlib's
Lusin–Souslin theorem `MeasurableSet.image_of_measurable_injOn`.

* D1 `exists_leftCountingMeasure`: `m = ∑ₙ (μ.comap (fst ∘ val)).map val` over the B2 pieces.
* D2 `relNull_iff`: B3 makes `fst '' (S ∩ R)` Borel.
* D3 `cfw_lemma3a`: C1 pieces, an everywhere positive finite Radon–Nikodym density of
  `A ↦ μ (snd '' (G ∩ fst⁻¹' A))` on each piece, the level sets of the density, C2.
* D4 `cfw_lemma3b`: C1 pieces `Gₙ`; the point `(x, y) ∈ Gₙ` gets the pair of ranks
  `(#{m < n | x ∈ fst '' Gₘ}, #{m < n | y ∈ snd '' Gₘ}) ∈ Fin N × Fin N`; each rank class is
  bi-injective, then C2.
* D5 `relNull_swap`: direct from symmetry and `hqi`.
-/
/-! ### Graphs of partial transformations -/

/-! ### D1 -/
/-- The counting function of a section, split along disjoint pieces on which `fst` is
injective. -/
theorem encard_section_eq_tsum {G : ℕ → Set (X × X)} (hGm : ∀ n, MeasurableSet (G n))
    (hinj : ∀ n, InjOn Prod.fst (G n)) (hdisj : Pairwise (Disjoint on G))
    {E : Set (X × X)} (hE : MeasurableSet E) (x : X) :
    (({y | (x, y) ∈ E ∩ ⋃ n, G n}.encard : ℕ∞) : ℝ≥0∞) =
      ∑' n, (Prod.fst '' (E ∩ G n)).indicator 1 x := by
  have hsec : ∀ n, MeasurableSet {y | (x, y) ∈ E ∩ G n} := fun n =>
    measurable_prodMk_left (hE.inter (hGm n))
  have hU : {y | (x, y) ∈ E ∩ ⋃ n, G n} = ⋃ n, {y | (x, y) ∈ E ∩ G n} := by
    ext y
    simp [inter_iUnion]
  have hd : Pairwise (Disjoint on fun n => {y | (x, y) ∈ E ∩ G n}) := by
    intro i j hij
    exact Set.disjoint_left.2 fun y hi hj => Set.disjoint_left.1 (hdisj hij) hi.2 hj.2
  rw [hU, ← Measure.count_apply (MeasurableSet.iUnion hsec), measure_iUnion hd hsec]
  congr 1
  ext n
  by_cases hx : x ∈ Prod.fst '' (E ∩ G n)
  · obtain ⟨⟨x', y⟩, hp, rfl⟩ := hx
    have hs : {y' | (x', y') ∈ E ∩ G n} = {y} := by
      ext y'
      constructor
      · intro hy'
        have := hinj n hy'.2 hp.2 rfl
        simp only [Prod.mk.injEq, true_and] at this
        exact this
      · rintro rfl
        exact hp
    rw [hs, Measure.count_singleton,
      indicator_of_mem (show x' ∈ Prod.fst '' (E ∩ G n) from ⟨_, hp, rfl⟩)]
    rfl
  · rw [indicator_of_notMem hx]
    have hs : {y | (x, y) ∈ E ∩ G n} = ∅ := by
      ext y
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro h
      exact hx ⟨(x, y), h, rfl⟩
    rw [hs, measure_empty]

end CFWPlan.Route.PartD
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §D. CFW-facing consequences (downstream of FM; statements only)

These are where FM's output is consumed. They are listed so that the FM form is checked against
its users. They are **not** part of the LN/FM work. -/

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route.PartD
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ### D2 -/
set_option linter.unusedVariables false in
/-- **D2. `Monod.RelNull` is `m`-nullness** (for Borel `S`). -/
theorem relNull_iff (μ : Measure X) {R : Set (X × X)} (hR : MeasurableSet R)
    (hcount : ∀ x, {y | (x, y) ∈ R}.Countable) (hcount' : ∀ y, {x | (x, y) ∈ R}.Countable)
    {S : Set (X × X)} (hS : MeasurableSet S) :
    Monod.RelNull μ R S ↔ ∫⁻ x, (({y | (x, y) ∈ S ∩ R}.encard : ℕ∞) : ℝ≥0∞) ∂μ = 0 := by
  have hA : MeasurableSet (Prod.fst '' (S ∩ R)) :=
    CFWPlan.Route.measurableSet_image_fst (hS.inter hR)
      fun x => (hcount x).mono fun _ hy => hy.2
  unfold Monod.RelNull
  constructor
  · intro h
    have hae : (fun x => (({y | (x, y) ∈ S ∩ R}.encard : ℕ∞) : ℝ≥0∞)) =ᵐ[μ] 0 := by
      rw [Filter.EventuallyEq, ae_iff]
      refine measure_mono_null ?_ h
      intro x hx
      by_contra hx'
      apply hx
      have he : {y | (x, y) ∈ S ∩ R} = ∅ := by
        ext y
        simp only [mem_empty_iff_false, iff_false]
        exact fun hy => hx' ⟨(x, y), hy, rfl⟩
      show (({y | (x, y) ∈ S ∩ R}.encard : ℕ∞) : ℝ≥0∞) = 0
      rw [he, encard_empty]
      simp
    rw [lintegral_congr_ae hae]
    simp
  · intro h
    refine le_antisymm ?_ bot_le
    rw [← h, ← lintegral_indicator_one hA]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ Prod.fst '' (S ∩ R)
    · rw [indicator_of_mem hx]
      obtain ⟨p, hp, rfl⟩ := hx
      have h1 : 1 ≤ {y | (p.1, y) ∈ S ∩ R}.encard := one_le_encard_iff_nonempty.2 ⟨p.2, hp⟩
      have h1' : ((1 : ℕ∞) : ℝ≥0∞) ≤ (({y | (p.1, y) ∈ S ∩ R}.encard : ℕ∞) : ℝ≥0∞) := by
        exact_mod_cast h1
      simpa using h1'
    · rw [indicator_of_notMem hx]
      exact bot_le

end CFWPlan.Route.PartD
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias relNull_iff := CFWPlan.Route.PartD.relNull_iff

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route.PartD
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ### D3 -/

end CFWPlan.Route.PartD
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route.PartD
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ### D4 -/
/-- The rank of `x` before stage `n` along a sequence of sets: the number of `m < n` with
`x ∈ D m`. -/
noncomputable def rank (D : ℕ → Set X) (n : ℕ) (x : X) : ℕ :=
  ∑ m ∈ Finset.range n, (D m).indicator 1 x

omit [MeasurableSpace X] [StandardBorelSpace X] in
theorem rank_succ (D : ℕ → Set X) (n : ℕ) (x : X) :
    rank D (n + 1) x = rank D n x + (D n).indicator 1 x := by
  simp [rank, Finset.sum_range_succ]

omit [MeasurableSpace X] [StandardBorelSpace X] in
theorem rank_mono (D : ℕ → Set X) {n n' : ℕ} (h : n ≤ n') (x : X) :
    rank D n x ≤ rank D n' x :=
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 h)

omit [MeasurableSpace X] [StandardBorelSpace X] in
theorem rank_lt_rank (D : ℕ → Set X) {n n' : ℕ} (h : n < n') {x : X} (hx : x ∈ D n) :
    rank D n x < rank D n' x := by
  have := rank_mono D (Nat.succ_le_of_lt h) x
  rw [rank_succ, indicator_of_mem hx] at this
  simp only [Pi.one_apply] at this
  omega

omit [StandardBorelSpace X] in
theorem measurable_rank {D : ℕ → Set X} (hD : ∀ m, MeasurableSet (D m)) (n : ℕ) :
    Measurable (rank D n) :=
  Finset.measurable_sum _ fun m _ => measurable_one.indicator (hD m)

omit [MeasurableSpace X] [StandardBorelSpace X] in
/-- The rank is bounded by the size of the section: the indices `m < n` with `x ∈ fst '' Gₘ`
inject into the section of `K` at `x` when the `Gₘ` are disjoint pieces of `K`. -/
theorem rank_le_encard {K : Set (X × X)} {G : ℕ → Set (X × X)} (hdisj : Pairwise (Disjoint on G))
    (hGK : ∀ m, G m ⊆ K) (n : ℕ) (x : X) :
    (rank (fun m => Prod.fst '' G m) n x : ℕ∞) ≤ {y | (x, y) ∈ K}.encard := by
  classical
  have hr : rank (fun m => Prod.fst '' G m) n x =
      ((Finset.range n).filter fun m => x ∈ Prod.fst '' G m).card := by
    simp only [rank, indicator_apply, Pi.one_apply]
    rw [Finset.sum_boole, Nat.cast_id]
  rw [hr, ← encard_coe_eq_coe_finsetCard]
  let g : ℕ → X := fun m => if h : x ∈ Prod.fst '' G m then (Classical.choose h).2 else x
  have hg : ∀ m, x ∈ Prod.fst '' G m → (x, g m) ∈ G m := by
    intro m h
    simp only [g, dif_pos h]
    obtain ⟨hmem, heq⟩ := Classical.choose_spec h
    have hp : (x, (Classical.choose h).2) = Classical.choose h := Prod.ext heq.symm rfl
    rw [hp]
    exact hmem
  refine encard_le_encard_of_injOn (f := g) ?_ ?_
  · intro m hm
    simp only [Finset.coe_filter, mem_ofPred_eq] at hm
    exact hGK m (hg m hm.2)
  · intro m hm m' hm' hmm'
    simp only [Finset.coe_filter, mem_ofPred_eq] at hm hm'
    by_contra hne
    have h1 := hg m hm.2
    have h2 := hg m' hm'.2
    rw [hmm'] at h1
    exact Set.disjoint_left.1 (hdisj hne) h1 h2

omit [MeasurableSpace X] [StandardBorelSpace X] in
/-- A point of the piece `Gₙ` has rank `< N` when the sections of `K` have at most `N`
points. -/
theorem rank_lt {K : Set (X × X)} {G : ℕ → Set (X × X)} (hdisj : Pairwise (Disjoint on G))
    (hGK : ∀ m, G m ⊆ K) {N : ℕ} (hN : ∀ x, {y | (x, y) ∈ K}.encard ≤ N) {n : ℕ}
    {p : X × X} (hp : p ∈ G n) : rank (fun m => Prod.fst '' G m) n p.1 < N := by
  have h := (rank_le_encard hdisj hGK (n + 1) p.1).trans (hN p.1)
  rw [rank_succ, indicator_of_mem (show p.1 ∈ Prod.fst '' G n from ⟨p, hp, rfl⟩),
    Pi.one_apply] at h
  have h' : rank (fun m => Prod.fst '' G m) n p.1 + 1 ≤ N := by exact_mod_cast h
  omega

set_option linter.unusedVariables false in
/-- **D4. CFW Lemma 3(b)** (graph part). -/
theorem cfw_lemma3b {E K : Set (X × X)} (hE : MeasurableSet E) (hK : MeasurableSet K)
    (hKE : K ⊆ E) (N : ℕ) (hN : ∀ x, {y | (x, y) ∈ K}.encard ≤ N)
    (hN' : ∀ y, {x | (x, y) ∈ K}.encard ≤ N) :
    ∃ (k : ℕ) (φ : Fin k → Monod.PartialTransformation E), K = ⋃ i, ptGraph (φ i) := by
  have hc : ∀ x, {y | (x, y) ∈ K}.Countable := fun x =>
    (finite_of_encard_le_coe (hN x)).countable
  have hc' : ∀ y, {x | (x, y) ∈ K}.Countable := fun y =>
    (finite_of_encard_le_coe (hN' y)).countable
  obtain ⟨G, hGm, h1, h2, hdisj, hU⟩ := CFWPlan.Route.exists_biInjOn_cover hK hc hc'
  have hGK : ∀ n, G n ⊆ K := fun n => hU ▸ subset_iUnion G n
  set D1 : ℕ → Set X := fun m => Prod.fst '' G m with hD1def
  set D2 : ℕ → Set X := fun m => Prod.snd '' G m with hD2def
  have hD1 : ∀ m, MeasurableSet (D1 m) := fun m =>
    (hGm m).image_of_measurable_injOn measurable_fst (h1 m)
  have hD2 : ∀ m, MeasurableSet (D2 m) := fun m =>
    (hGm m).image_of_measurable_injOn measurable_snd (h2 m)
  -- the column ranks are the row ranks of the flipped pieces
  have hD2' : D2 = fun m => Prod.fst '' (Prod.swap ⁻¹' G m) := by
    funext m
    ext y
    simp [hD2def]
  have hb1 : ∀ {n} {p : X × X}, p ∈ G n → rank D1 n p.1 < N := fun hp =>
    rank_lt hdisj hGK hN hp
  have hb2 : ∀ {n} {p : X × X}, p ∈ G n → rank D2 n p.2 < N := by
    intro n p hp
    rw [hD2']
    exact rank_lt (K := Prod.swap ⁻¹' K) (G := fun m => Prod.swap ⁻¹' G m)
      (fun i j hij => (hdisj hij).preimage _) (fun m => preimage_mono (hGK m)) hN'
      (p := p.swap) hp
  let H : ℕ → ℕ → Set (X × X) := fun i j =>
    ⋃ n, G n ∩ ((fun p : X × X => rank D1 n p.1) ⁻¹' {i} ∩
      (fun p : X × X => rank D2 n p.2) ⁻¹' {j})
  have hHm : ∀ i j, MeasurableSet (H i j) := fun i j => MeasurableSet.iUnion fun n =>
    (hGm n).inter ((((measurable_rank hD1 n).comp measurable_fst) (measurableSet_singleton i)).inter
      (((measurable_rank hD2 n).comp measurable_snd) (measurableSet_singleton j)))
  have hHK : ∀ i j, H i j ⊆ K := fun i j =>
    iUnion_subset fun n => inter_subset_left.trans (hGK n)
  have hinj1 : ∀ i j, InjOn Prod.fst (H i j) := by
    intro i j p hp q hq hpq
    simp only [H, mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff] at hp hq
    obtain ⟨n, hpG, hpi, -⟩ := hp
    obtain ⟨n', hqG, hqi, -⟩ := hq
    rcases lt_trichotomy n n' with h | rfl | h
    · have := rank_lt_rank D1 h (x := p.1) ⟨p, hpG, rfl⟩
      rw [hpq] at this hpi
      omega
    · exact h1 n hpG hqG hpq
    · have := rank_lt_rank D1 h (x := q.1) ⟨q, hqG, rfl⟩
      rw [← hpq] at this hqi
      omega
  have hinj2 : ∀ i j, InjOn Prod.snd (H i j) := by
    intro i j p hp q hq hpq
    simp only [H, mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff] at hp hq
    obtain ⟨n, hpG, -, hpj⟩ := hp
    obtain ⟨n', hqG, -, hqj⟩ := hq
    rcases lt_trichotomy n n' with h | rfl | h
    · have := rank_lt_rank D2 h (x := p.2) ⟨p, hpG, rfl⟩
      rw [hpq] at this hpj
      omega
    · exact h2 n hpG hqG hpq
    · have := rank_lt_rank D2 h (x := q.2) ⟨q, hqG, rfl⟩
      rw [← hpq] at this hqj
      omega
  choose ψ hψ using fun ij : Fin N × Fin N =>
    CFWPlan.Route.exists_partialTransformation_of_biInjOn (hHm ij.1 ij.2)
      ((hHK ij.1 ij.2).trans hKE) (hinj1 ij.1 ij.2) (hinj2 ij.1 ij.2)
  refine ⟨N * N, fun i => ψ (finProdFinEquiv.symm i), ?_⟩
  ext p
  simp only [mem_iUnion, hψ]
  constructor
  · intro hp
    rw [← hU, mem_iUnion] at hp
    obtain ⟨n, hn⟩ := hp
    refine ⟨finProdFinEquiv (⟨rank D1 n p.1, hb1 hn⟩, ⟨rank D2 n p.2, hb2 hn⟩), ?_⟩
    rw [Equiv.symm_apply_apply]
    exact mem_iUnion.2 ⟨n, hn, rfl, rfl⟩
  · rintro ⟨i, hi⟩
    exact hHK _ _ hi

end CFWPlan.Route.PartD
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias cfw_lemma3b := CFWPlan.Route.PartD.cfw_lemma3b

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route.PartD
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ### D5 -/
set_option linter.unusedSectionVars false in
/-- **D5. Flipping preserves `Monod.RelNull`.** -/
theorem relNull_swap (μ : Measure X) {E : Set (X × X)}
    (hequiv : Equivalence fun x y => (x, y) ∈ E)
    (hqi : ∀ A : Set X, μ A = 0 → μ {y | ∃ x ∈ A, (x, y) ∈ E} = 0) {S : Set (X × X)}
    (hS : Monod.RelNull μ E S) : Monod.RelNull μ E (Prod.swap ⁻¹' S) := by
  unfold Monod.RelNull at hS ⊢
  refine measure_mono_null ?_ (hqi _ hS)
  rintro _ ⟨⟨x, y⟩, ⟨hxyS, hxyE⟩, rfl⟩
  exact ⟨y, ⟨(y, x), ⟨hxyS, hequiv.symm hxyE⟩, rfl⟩, hequiv.symm hxyE⟩

end CFWPlan.Route.PartD
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias relNull_swap := CFWPlan.Route.PartD.relNull_swap

end CFWPlan.Route
end

section
open MeasureTheory Set Function
namespace ConnesFeldmanWeiss

end ConnesFeldmanWeiss
end
end

section
section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
/-!
# Route to Connes–Feldman–Weiss (1981): lemma blueprint

A. Connes, J. Feldman, B. Weiss, *An amenable equivalence relation is generated by a single
transformation*, Ergodic Theory Dynam. Systems 1 (1981) 431–450 ("CFW"). Page numbers are the
journal's (PDF page = journal page − 430).

Every lemma below is a proof obligation for a prover. Each docstring gives the source (CFW page and
line, or an outside reference), a proof idea, the Mathlib / LN API it needs (every name checked
with `#check` against the workspace Mathlib pin `0df444a3`), and a size estimate in lines of Lean.
The `chk_<name>` theorems at the end restate the 16 mission statements verbatim and derive them
from the route. See `PLAN.md` (same folder) for the narrative, the DAG and the work packages.

Already available (imported, 0 sorries): `Solutions.LN.Assembled` — Lusin–Novikov
(`CFWPlan.Route.lusinNovikov`, `…_fun`, `measurableSet_image_fst`,
`exists_injOn_cover_of_countable_fibers`), Feldman–Moore (`exists_biInjOn_cover`,
`exists_partialTransformation_of_biInjOn`, and the involution form
`ConnesFeldmanWeiss.chk_exists_seq_measurableEquiv_of_countable_classes`), and the §D lemmas
`exists_leftCountingMeasure`, `relNull_iff`, `cfw_lemma3a`, `cfw_lemma3b`, `relNull_swap`.

Naming. Lemmas about the bundle's structures are named like `IsDiscreteMeasured.qi` but live in
`CFWPlan.Main`, so dot notation on `hR : ConnesFeldmanWeiss.IsDiscreteMeasured μ R` does not find
them: call them by name (`IsDiscreteMeasured.qi hR`).

Conventions. `m = relMeasure μ R` integrates `μ` over the FIRST coordinate and counts the second
(CFW p. 434, `m = ∫ νˣ dμ(x)`); `m⁻¹ = m.map Prod.swap` integrates over the second coordinate;
`δ = module μ R = dm/dm⁻¹`, so `dm⁻¹ = δ⁻¹ dm`. CFW's range/source maps are `r(y, x) = y = γ.1`
and `s(y, x) = x = γ.2`.
-/
/-! ## §0. Preliminaries: quasi-invariance, saturations, measure classes -/
/-- The left-to-right form of quasi-invariance used in LN (`hqi` there): for an *arbitrary* null
set `A`, the set of points equivalent to a point of `A` is null.
*Source:* CFW p. 433 (quasi-invariance). *Proof:* `A ⊆ toMeasurable μ A`, which is measurable and
null; by symmetry the set is contained in its saturation. *API:* `subset_toMeasurable`,
`measure_toMeasurable`, `measure_mono_null`. *Size:* 8 (proved). -/
theorem IsDiscreteMeasured.qi {μ : Measure X} {R : Set (X × X)} (hR : IsDiscreteMeasured μ R) :
    ∀ A : Set X, μ A = 0 → μ {y | ∃ x ∈ A, (x, y) ∈ R} = 0 := by
  intro A hA
  have h := hR.quasiInvariant (toMeasurable μ A) (measurableSet_toMeasurable μ A)
    (by rw [measure_toMeasurable]; exact hA)
  refine measure_mono_null ?_ h
  rintro y ⟨x, hx, hxy⟩
  exact ⟨x, subset_toMeasurable μ A hx, hR.equivalence.symm hxy⟩

/-- Countable vertical sections, from countable classes and symmetry. *Size:* 3 (proved). -/
theorem IsDiscreteMeasured.countable_left {μ : Measure X} {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (y : X) : {x | (x, y) ∈ R}.Countable :=
  (hR.countable_classes y).mono fun _ hx => hR.equivalence.symm hx

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]
/-- **Feldman–Moore generators** (the mission milestone
`exists_seq_measurableEquiv_of_countable_classes`, proved in LN as
`ConnesFeldmanWeiss.chk_exists_seq_measurableEquiv_of_countable_classes`). In final solutions this
call is replaced by an import of the milestone statement. *Size:* 2 (proved). -/
theorem IsDiscreteMeasured.exists_generators {μ : Measure X} {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) : ∃ φ : ℕ → X ≃ᵐ X, ∀ x y, (x, y) ∈ R ↔ ∃ n, φ n x = y :=
  ConnesFeldmanWeiss.exists_seq_measurableEquiv_of_countable_classes R hR.measurableSet
    hR.equivalence hR.countable_classes

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]
/-!
# CFW route, package P1 (Foundations)

Proofs of the Route lemmas of §0 (preliminaries), §1 (partial transformations as total maps),
§2 (the measure `m` on `R`), §3 (the module `δ`) and, from §4, `IsFiniteSubrelation.union_diagonal`
and `exists_selector`. Each Route lemma `CFWPlan.Main.foo` is restated verbatim here as
`CFWPlan.Main.P1.foo`.
-/
/-! ## §0. Preliminaries: quasi-invariance, saturations, measure classes -/

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]
/-! ### Measure classes. All four notions only see null sets. -/

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
/-! ## §1. Partial transformations as total maps -/
open Classical in
/-- A partial transformation as a total map: `φ` on its domain, the identity elsewhere. -/
noncomputable def ptFun {R : Set (X × X)} (φ : Monod.PartialTransformation R) (x : X) : X :=
  if h : x ∈ φ.dom then (φ.e ⟨x, h⟩ : X) else x

open Classical in
/-- The inverse of a partial transformation as a total map: `φ⁻¹` on its image, the identity
elsewhere. -/
noncomputable def ptInv {R : Set (X × X)} (φ : Monod.PartialTransformation R) (y : X) : X :=
  if h : y ∈ φ.cod then (φ.e.symm ⟨y, h⟩ : X) else y

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X]
/-! ## §1. Partial transformations as total maps -/
theorem ptFun_of_mem {R : Set (X × X)} (φ : Monod.PartialTransformation R) {x : X}
    (hx : x ∈ φ.dom) : ptFun φ x = (φ.e ⟨x, hx⟩ : X) := by
  classical
  unfold ptFun
  rw [dif_pos hx]

theorem ptInv_of_mem {R : Set (X × X)} (φ : Monod.PartialTransformation R) {y : X}
    (hy : y ∈ φ.cod) : ptInv φ y = (φ.e.symm ⟨y, hy⟩ : X) := by
  classical
  unfold ptInv
  rw [dif_pos hy]

theorem measurable_ptFun {R : Set (X × X)} (φ : Monod.PartialTransformation R) :
    Measurable (ptFun φ) ∧ Measurable (ptInv φ) := by
  classical
  constructor
  · exact Measurable.dite (measurable_subtype_coe.comp φ.e.measurable) measurable_subtype_coe
      φ.measurableSet_dom
  · exact Measurable.dite (measurable_subtype_coe.comp φ.e.symm.measurable) measurable_subtype_coe
      φ.measurableSet_cod

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
alias measurable_ptFun := CFWPlan.Main.P1.measurable_ptFun

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X]
theorem ptFun_spec {R : Set (X × X)} (φ : Monod.PartialTransformation R) :
    (∀ x ∈ φ.dom, ptFun φ x ∈ φ.cod ∧ ptInv φ (ptFun φ x) = x ∧ (x, ptFun φ x) ∈ R) ∧
    (∀ y ∈ φ.cod, ptInv φ y ∈ φ.dom ∧ ptFun φ (ptInv φ y) = y) ∧ InjOn (ptFun φ) φ.dom := by
  have key : ∀ x (hx : x ∈ φ.dom), ptFun φ x ∈ φ.cod ∧ ptInv φ (ptFun φ x) = x := by
    intro x hx
    have h1 := ptFun_of_mem φ hx
    have h2 : ptFun φ x ∈ φ.cod := h1 ▸ (φ.e ⟨x, hx⟩).2
    refine ⟨h2, ?_⟩
    rw [ptInv_of_mem φ h2]
    have : (⟨ptFun φ x, h2⟩ : φ.cod) = φ.e ⟨x, hx⟩ := Subtype.ext h1
    rw [this, MeasurableEquiv.symm_apply_apply]
  refine ⟨fun x hx => ⟨(key x hx).1, (key x hx).2, ?_⟩, fun y hy => ?_, fun x hx x' hx' h => ?_⟩
  · rw [ptFun_of_mem φ hx]
    exact φ.graph_subset ⟨x, hx⟩
  · have h1 := ptInv_of_mem φ hy
    have h2 : ptInv φ y ∈ φ.dom := h1 ▸ (φ.e.symm ⟨y, hy⟩).2
    refine ⟨h2, ?_⟩
    rw [ptFun_of_mem φ h2]
    have : (⟨ptInv φ y, h2⟩ : φ.dom) = φ.e.symm ⟨y, hy⟩ := Subtype.ext h1
    rw [this, MeasurableEquiv.apply_symm_apply]
  · rw [← (key x hx).2, ← (key x' hx').2, h]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X]
theorem ptGraph_eq {R : Set (X × X)} (φ : Monod.PartialTransformation R) :
    CFWPlan.Route.ptGraph φ = {p | p.1 ∈ φ.dom ∧ ptFun φ p.1 = p.2} := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨a, ha⟩
    simp only [Prod.mk.injEq] at ha
    obtain ⟨rfl, rfl⟩ := ha
    exact ⟨a.2, ptFun_of_mem φ a.2⟩
  · rintro ⟨hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    simp only [Prod.mk.injEq, true_and]
    rw [← ptFun_of_mem φ hx]
    exact hxy

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X]
theorem measurableSet_ptGraph [StandardBorelSpace X] {R : Set (X × X)}
    (φ : Monod.PartialTransformation R) : MeasurableSet (CFWPlan.Route.ptGraph φ) := by
  rw [ptGraph_eq]
  exact (φ.measurableSet_dom.preimage measurable_fst).inter
    (measurableSet_eq_fun ((measurable_ptFun φ).1.comp measurable_fst) measurable_snd)

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
alias measurableSet_ptGraph := CFWPlan.Main.P1.measurableSet_ptGraph

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §2. The measure `m` on `R` (CFW p. 434) -/
/-- The kernel `x ↦ νˣ` of `relMeasure`: counting measure on the section `Rₓ`, placed on
`{x} × Rₓ`. -/
noncomputable def relKer (R : Set (X × X)) (x : X) : Measure (X × X) :=
  (Measure.count.restrict {y | (x, y) ∈ R}).map (Prod.mk x)

omit [StandardBorelSpace X] in
theorem relMeasure_eq_bind (μ : Measure X) (R : Set (X × X)) :
    relMeasure μ R = μ.bind (relKer R) := rfl

theorem relKer_apply {R : Set (X × X)} (hR : MeasurableSet R) (x : X) {E : Set (X × X)}
    (hE : MeasurableSet E) :
    relKer R x E = (({y | (x, y) ∈ E ∩ R}.encard : ℕ∞) : ℝ≥0∞) := by
  unfold relKer
  rw [Measure.map_apply measurable_prodMk_left hE,
    Measure.restrict_apply (measurable_prodMk_left hE),
    Measure.count_apply (show MeasurableSet (Prod.mk x ⁻¹' E ∩ {y | (x, y) ∈ R}) from
      (measurable_prodMk_left hE).inter (measurable_prodMk_left hR))]
  rfl

theorem lintegral_relKer {R : Set (X × X)} (hR : MeasurableSet R) (x : X) {g : X × X → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ p, g p ∂relKer R x = ∑' y : {y : X // (x, y) ∈ R}, g (x, y) := by
  unfold relKer
  rw [lintegral_map hg measurable_prodMk_left,
    ← lintegral_indicator (show MeasurableSet {y | (x, y) ∈ R} from measurable_prodMk_left hR),
    lintegral_count]
  exact (tsum_subtype {y | (x, y) ∈ R} (fun y => g (x, y))).symm

theorem measurable_encard_section {E : Set (X × X)} (hE : MeasurableSet E)
    (hcount : ∀ x, {y | (x, y) ∈ E}.Countable) :
    Measurable fun x => (({y | (x, y) ∈ E}.encard : ℕ∞) : ℝ≥0∞) := by
  obtain ⟨G, hGm, hinj, hdisj, hU⟩ := CFWPlan.Route.lusinNovikov hE hcount
  have h : ∀ x, (({y | (x, y) ∈ E}.encard : ℕ∞) : ℝ≥0∞) =
      ∑' n, (Prod.fst '' (univ ∩ G n)).indicator 1 x := by
    intro x
    rw [← CFWPlan.Route.PartD.encard_section_eq_tsum hGm hinj hdisj MeasurableSet.univ x, hU]
    simp only [univ_inter]
  simp_rw [h]
  refine Measurable.tsum fun n => measurable_one.indicator ?_
  exact (MeasurableSet.univ.inter (hGm n)).image_of_measurable_injOn measurable_fst
    ((hinj n).mono inter_subset_right)

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §2. The measure `m` on `R` (CFW p. 434) -/

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
theorem measurable_relKer {R : Set (X × X)} (hR : MeasurableSet R)
    (hcount : ∀ x, {y | (x, y) ∈ R}.Countable) : Measurable (relKer R) := by
  refine Measure.measurable_of_measurable_coe _ fun E hE => ?_
  simp_rw [relKer_apply hR _ hE]
  exact measurable_encard_section (hE.inter hR) fun x => (hcount x).mono fun y hy => hy.2

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
theorem relMeasure_apply {μ : Measure X} {R : Set (X × X)} (hR : MeasurableSet R)
    (hcount : ∀ x, {y | (x, y) ∈ R}.Countable) {E : Set (X × X)} (hE : MeasurableSet E) :
    relMeasure μ R E = ∫⁻ x, (({y | (x, y) ∈ E ∩ R}.encard : ℕ∞) : ℝ≥0∞) ∂μ := by
  rw [relMeasure_eq_bind, Measure.bind_apply hE (measurable_relKer hR hcount).aemeasurable]
  simp_rw [relKer_apply hR _ hE]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
theorem lintegral_relMeasure {μ : Measure X} {R : Set (X × X)} (hR : MeasurableSet R)
    (hcount : ∀ x, {y | (x, y) ∈ R}.Countable) {g : X × X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, g p ∂relMeasure μ R = ∫⁻ x, ∑' y : {y : X // (x, y) ∈ R}, g (x, y) ∂μ := by
  rw [relMeasure_eq_bind, Measure.lintegral_bind (measurable_relKer hR hcount).aemeasurable
    hg.aemeasurable]
  simp_rw [lintegral_relKer hR _ hg]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
theorem lintegral_relMeasure_swap {μ : Measure X} {R : Set (X × X)} (hR : IsDiscreteMeasured μ R)
    {g : X × X → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ p, g p ∂((relMeasure μ R).map Prod.swap) =
      ∫⁻ y, ∑' x : {x : X // (x, y) ∈ R}, g (x, y) ∂μ := by
  rw [lintegral_map hg measurable_swap,
    lintegral_relMeasure hR.measurableSet hR.countable_classes (g := fun p => g p.swap)
      (hg.comp measurable_swap)]
  refine lintegral_congr fun y => ?_
  exact ((Equiv.subtypeEquivRight (p := fun x => (x, y) ∈ R) (q := fun x => (y, x) ∈ R)
    fun x => ⟨hR.equivalence.symm, hR.equivalence.symm⟩).tsum_eq
      (fun x : {x : X // (y, x) ∈ R} => g ((x : X), y))).symm

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
theorem ae_relMeasure_iff {μ : Measure X} {R : Set (X × X)} (hR : MeasurableSet R)
    (hcount : ∀ x, {y | (x, y) ∈ R}.Countable) {p : X × X → Prop}
    (hp : MeasurableSet {q | p q}) :
    (∀ᵐ q ∂relMeasure μ R, p q) ↔ ∀ᵐ x ∂μ, ∀ y, (x, y) ∈ R → p (x, y) := by
  have hpc : MeasurableSet {q | ¬ p q} := hp.compl
  rw [ae_iff, relMeasure_apply hR hcount hpc,
    lintegral_eq_zero_iff (measurable_encard_section (hpc.inter hR)
      fun x => (hcount x).mono fun y hy => hy.2)]
  refine eventually_congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.zero_apply, ENat.toENNReal_eq_zero, encard_eq_zero]
  constructor
  · intro h y hy
    by_contra hpy
    have : y ∈ ({y | (x, y) ∈ {q | ¬p q} ∩ R} : Set X) := ⟨hpy, hy⟩
    rw [h] at this
    exact this
  · intro h
    ext y
    simp only [mem_ofPred_eq, mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hpy hy
    exact hpy (h y hy)

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
theorem relMeasure_compl {μ : Measure X} {R : Set (X × X)} (hR : MeasurableSet R)
    (hcount : ∀ x, {y | (x, y) ∈ R}.Countable) : relMeasure μ R Rᶜ = 0 := by
  rw [relMeasure_apply hR hcount hR.compl]
  simp

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
omit [StandardBorelSpace X] in
/-- A section that is a single point under a condition. -/
theorem encard_section_eq_ite {S : Set (X × X)} {x c : X} {P : Prop} [Decidable P]
    (h : ∀ y, (x, y) ∈ S ↔ P ∧ y = c) :
    (({y | (x, y) ∈ S}.encard : ℕ∞) : ℝ≥0∞) = if P then 1 else 0 := by
  by_cases hP : P
  · have : {y | (x, y) ∈ S} = {c} := by
      ext y
      simp only [mem_ofPred_eq, mem_singleton_iff, h y, hP, true_and]
    rw [this, encard_singleton, if_pos hP]
    simp
  · have : {y | (x, y) ∈ S} = ∅ := by
      ext y
      simp only [mem_ofPred_eq, mem_empty_iff_false, h y, hP, false_and]
    rw [this, encard_empty, if_neg hP]
    simp

theorem relMeasure_restrict_ptGraph {μ : Measure X} {R : Set (X × X)} (hR : IsDiscreteMeasured μ R)
    (φ : Monod.PartialTransformation R) :
    (relMeasure μ R).restrict (CFWPlan.Route.ptGraph φ) =
        (μ.restrict φ.dom).map (fun x => (x, ptFun φ x)) ∧
      ((relMeasure μ R).map Prod.swap).restrict (CFWPlan.Route.ptGraph φ) =
        (μ.restrict φ.cod).map (fun y => (ptInv φ y, y)) := by
  classical
  have hG := measurableSet_ptGraph φ
  have hf := (measurable_ptFun φ).1
  have hg := (measurable_ptFun φ).2
  have hsp := ptFun_spec φ
  constructor
  · ext E hE
    have hF : Measurable fun x => (x, ptFun φ x) := measurable_id.prodMk hf
    rw [Measure.restrict_apply hE, Measure.map_apply hF hE, Measure.restrict_apply (hF hE),
      relMeasure_apply hR.measurableSet hR.countable_classes (hE.inter hG),
      ← lintegral_indicator_one ((hF hE).inter φ.measurableSet_dom)]
    refine lintegral_congr fun x => ?_
    rw [encard_section_eq_ite (P := x ∈ (fun x => (x, ptFun φ x)) ⁻¹' E ∩ φ.dom)
      (c := ptFun φ x)]
    · simp only [indicator, Pi.one_apply]
    · intro y
      rw [ptGraph_eq]
      simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage]
      constructor
      · rintro ⟨⟨hxy, hx, rfl⟩, -⟩
        exact ⟨⟨hxy, hx⟩, rfl⟩
      · rintro ⟨⟨hxy, hx⟩, rfl⟩
        exact ⟨⟨hxy, hx, rfl⟩, (hsp.1 x hx).2.2⟩
  · ext E hE
    have hF : Measurable fun y => (ptInv φ y, y) := hg.prodMk measurable_id
    rw [Measure.restrict_apply hE, Measure.map_apply measurable_swap (hE.inter hG),
      Measure.map_apply hF hE, Measure.restrict_apply (hF hE),
      relMeasure_apply hR.measurableSet hR.countable_classes (measurable_swap (hE.inter hG)),
      ← lintegral_indicator_one ((hF hE).inter φ.measurableSet_cod)]
    refine lintegral_congr fun x => ?_
    rw [encard_section_eq_ite (P := x ∈ (fun y => (ptInv φ y, y)) ⁻¹' E ∩ φ.cod)
      (c := ptInv φ x)]
    · simp only [indicator, Pi.one_apply]
    · intro y
      rw [ptGraph_eq]
      simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, Prod.swap_prod_mk]
      constructor
      · rintro ⟨⟨hxy, hy, rfl⟩, -⟩
        exact ⟨⟨by rwa [(hsp.1 y hy).2.1], (hsp.1 y hy).1⟩, ((hsp.1 y hy).2.1).symm⟩
      · rintro ⟨⟨hxy, hx⟩, rfl⟩
        refine ⟨⟨hxy, (hsp.2.1 x hx).1, (hsp.2.1 x hx).2⟩, ?_⟩
        have := (hsp.1 _ (hsp.2.1 x hx).1).2.2
        rw [(hsp.2.1 x hx).2] at this
        exact hR.equivalence.symm this

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias relMeasure_restrict_ptGraph := CFWPlan.Main.P1.relMeasure_restrict_ptGraph

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
theorem sigmaFinite_relMeasure {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) : SigmaFinite (relMeasure μ R) := by
  classical
  obtain ⟨φ, hφ⟩ := IsDiscreteMeasured.exists_generators hR
  let S : ℕ × ℕ → Set (X × X) := fun nj => {p | p.1 ∈ spanningSets μ nj.2 ∧ φ nj.1 p.1 = p.2}
  have hS : ∀ nj, MeasurableSet (S nj) := fun nj =>
    ((measurableSet_spanningSets μ nj.2).preimage measurable_fst).inter
      (measurableSet_eq_fun ((φ nj.1).measurable.comp measurable_fst) measurable_snd)
  refine Measure.sigmaFinite_of_countable (S := insert Rᶜ (range S))
    ((countable_range S).insert _) ?_ ?_
  · rintro s (rfl | ⟨⟨n, j⟩, rfl⟩)
    · rw [relMeasure_compl hR.measurableSet hR.countable_classes]
      exact ENNReal.zero_lt_top
    · rw [relMeasure_apply hR.measurableSet hR.countable_classes (hS _)]
      have h : ∀ x, (({y | (x, y) ∈ S (n, j) ∩ R}.encard : ℕ∞) : ℝ≥0∞) =
          (spanningSets μ j).indicator 1 x := by
        intro x
        rw [encard_section_eq_ite (P := x ∈ spanningSets μ j) (c := φ n x)]
        · simp only [indicator, Pi.one_apply]
        · intro y
          simp only [S, mem_inter_iff, mem_ofPred_eq]
          constructor
          · rintro ⟨⟨hx, rfl⟩, -⟩
            exact ⟨hx, rfl⟩
          · rintro ⟨hx, rfl⟩
            exact ⟨⟨hx, rfl⟩, (hφ x _).2 ⟨n, rfl⟩⟩
      simp_rw [h]
      rw [lintegral_indicator_one (measurableSet_spanningSets μ j)]
      exact measure_spanningSets_lt_top μ j
  · ext p
    simp only [sUnion_insert, sUnion_range, mem_union, mem_compl_iff, mem_iUnion, mem_univ,
      iff_true]
    by_cases hp : p ∈ R
    · right
      obtain ⟨n, hn⟩ := (hφ p.1 p.2).1 hp
      have hj : p.1 ∈ ⋃ j, spanningSets μ j := by rw [iUnion_spanningSets]; trivial
      obtain ⟨j, hj⟩ := mem_iUnion.1 hj
      exact ⟨(n, j), hj, hn⟩
    · left
      exact hp

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
theorem relMeasure_null_swap {μ : Measure X} {R : Set (X × X)} (hR : IsDiscreteMeasured μ R)
    {E : Set (X × X)} (hE : MeasurableSet E) (h0 : relMeasure μ R E = 0) :
    relMeasure μ R (Prod.swap ⁻¹' E) = 0 := by
  have hc' : ∀ y, {x | (x, y) ∈ R}.Countable := IsDiscreteMeasured.countable_left hR
  have h1 : Monod.RelNull μ R E :=
    (CFWPlan.Route.relNull_iff μ hR.measurableSet hR.countable_classes hc' hE).2
      (by rw [← relMeasure_apply hR.measurableSet hR.countable_classes hE]; exact h0)
  have h2 := CFWPlan.Route.relNull_swap μ hR.equivalence (IsDiscreteMeasured.qi hR) h1
  rw [relMeasure_apply hR.measurableSet hR.countable_classes (measurable_swap hE)]
  exact (CFWPlan.Route.relNull_iff μ hR.measurableSet hR.countable_classes hc'
    (measurable_swap hE)).1 h2

theorem relMeasure_ac_swap {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) :
    relMeasure μ R ≪ (relMeasure μ R).map Prod.swap ∧
      (relMeasure μ R).map Prod.swap ≪ relMeasure μ R := by
  constructor
  · refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
    rw [Measure.map_apply measurable_swap hs] at h0
    have h := relMeasure_null_swap hR (measurable_swap hs) h0
    have hss : Prod.swap ⁻¹' (Prod.swap ⁻¹' s) = s := by
      ext p
      simp
    rwa [hss] at h
  · refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
    rw [Measure.map_apply measurable_swap hs]
    exact relMeasure_null_swap hR hs h0

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §3. The module `δ` (CFW p. 434) -/
omit [StandardBorelSpace X] in
theorem measurableEmbedding_swap :
    MeasurableEmbedding (Prod.swap : X × X → X × X) :=
  (MeasurableEquiv.prodComm : X × X ≃ᵐ X × X).measurableEmbedding

theorem sigmaFinite_relMeasure_swap {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) : SigmaFinite ((relMeasure μ R).map Prod.swap) := by
  haveI := sigmaFinite_relMeasure hR
  exact measurableEmbedding_swap.sigmaFinite_map

omit [StandardBorelSpace X] in
theorem measurable_module (μ : Measure X) (R : Set (X × X)) : Measurable (module μ R) :=
  Measure.measurable_rnDeriv _ _

theorem module_pos_lt_top {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) :
    ∀ᵐ p ∂relMeasure μ R, 0 < module μ R p ∧ module μ R p < ∞ := by
  haveI := sigmaFinite_relMeasure hR
  haveI := sigmaFinite_relMeasure_swap hR
  have hac := relMeasure_ac_swap hR
  filter_upwards [Measure.rnDeriv_pos hac.1,
    hac.1.ae_le (Measure.rnDeriv_lt_top (relMeasure μ R) ((relMeasure μ R).map Prod.swap))]
    with p h1 h2
  exact ⟨h1, h2⟩

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §3. The module `δ` (CFW p. 434) -/
alias module_pos_lt_top := CFWPlan.Main.P1.module_pos_lt_top

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
theorem relMeasure_swap_eq_withDensity {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) :
    (relMeasure μ R).map Prod.swap = (relMeasure μ R).withDensity fun p => (module μ R p)⁻¹ := by
  haveI := sigmaFinite_relMeasure hR
  haveI := sigmaFinite_relMeasure_swap hR
  have hac := relMeasure_ac_swap hR
  calc (relMeasure μ R).map Prod.swap
      = (relMeasure μ R).withDensity (((relMeasure μ R).map Prod.swap).rnDeriv (relMeasure μ R)) :=
        (Measure.withDensity_rnDeriv_eq _ _ hac.2).symm
    _ = (relMeasure μ R).withDensity fun p => (module μ R p)⁻¹ :=
        withDensity_congr_ae (Measure.inv_rnDeriv hac.1).symm

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
theorem module_swap {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) :
    ∀ᵐ p ∂relMeasure μ R, module μ R p.swap = (module μ R p)⁻¹ := by
  haveI := sigmaFinite_relMeasure hR
  haveI := sigmaFinite_relMeasure_swap hR
  have hac := relMeasure_ac_swap hR
  have h1 := measurableEmbedding_swap.rnDeriv_map ((relMeasure μ R).map Prod.swap)
    (relMeasure μ R)
  have e1 : ((relMeasure μ R).map Prod.swap).map Prod.swap = relMeasure μ R := by
    rw [Measure.map_map measurable_swap measurable_swap, Prod.swap_swap_eq, Measure.map_id]
  rw [e1] at h1
  filter_upwards [h1, Measure.inv_rnDeriv hac.1] with p hp hq
  unfold module
  rw [hp, ← hq]
  rfl

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias module_swap := CFWPlan.Main.P1.module_swap

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-- For `μ`-a.e. `x`, at every `y ~ x`: `0 < δ(x, y) < ∞` and `δ(y, x) = δ(x, y)⁻¹`. -/
theorem ae_module_good {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) :
    ∀ᵐ x ∂μ, ∀ y, (x, y) ∈ R → 0 < module μ R (x, y) ∧ module μ R (x, y) < ∞ ∧
      module μ R (y, x) = (module μ R (x, y))⁻¹ := by
  have hδ := measurable_module μ R
  have hall : ∀ᵐ p ∂relMeasure μ R, 0 < module μ R p ∧ module μ R p < ∞ ∧
      module μ R p.swap = (module μ R p)⁻¹ := by
    filter_upwards [module_pos_lt_top hR, module_swap hR] with p hp hp'
    exact ⟨hp.1, hp.2, hp'⟩
  have hmeas : MeasurableSet {p : X × X | 0 < module μ R p ∧ module μ R p < ∞ ∧
      module μ R p.swap = (module μ R p)⁻¹} :=
    (measurableSet_lt measurable_const hδ).inter ((measurableSet_lt hδ measurable_const).inter
      (measurableSet_eq_fun (hδ.comp measurable_swap) hδ.inv))
  exact (ae_relMeasure_iff hR.measurableSet hR.countable_classes hmeas).1 hall

/-- **Change of variables** along a Borel injection `f : D → X` whose graph lies in `R`:
`∫_{f D} h dμ = ∫_D h(f x) δ(f x, x) dμ(x)`. -/
theorem lintegral_image_eq {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) {D : Set X} (hD : MeasurableSet D) {f : X → X}
    (hf : Measurable f) (hinj : InjOn f D) (hfR : ∀ x ∈ D, (x, f x) ∈ R) {h : X → ℝ≥0∞}
    (hh : Measurable h) :
    ∫⁻ y in f '' D, h y ∂μ = ∫⁻ x in D, h (f x) * module μ R (f x, x) ∂μ := by
  classical
  set G : Set (X × X) := {p | p.1 ∈ D ∧ f p.1 = p.2} with hGdef
  have hG : MeasurableSet G := (hD.preimage measurable_fst).inter
    (measurableSet_eq_fun (hf.comp measurable_fst) measurable_snd)
  have hδ := measurable_module μ R
  set k : X × X → ℝ≥0∞ := G.indicator fun p => h p.2 with hkdef
  have hk : Measurable k := (hh.comp measurable_snd).indicator hG
  have hfD : MeasurableSet (f '' D) := hD.image_of_measurable_injOn hf hinj
  have e1 : ∫⁻ p, k p ∂((relMeasure μ R).map Prod.swap) = ∫⁻ y in f '' D, h y ∂μ := by
    rw [lintegral_relMeasure_swap hR hk, ← lintegral_indicator hfD]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ f '' D
    · obtain ⟨x₀, hx₀, rfl⟩ := hy
      rw [indicator_of_mem (mem_image_of_mem f hx₀), tsum_eq_single ⟨x₀, hfR x₀ hx₀⟩]
      · rw [hkdef, indicator_of_mem (show (x₀, f x₀) ∈ G from ⟨hx₀, rfl⟩)]
      · intro b hb
        rw [hkdef, indicator_of_notMem]
        rintro ⟨hb1, hb2⟩
        exact hb (Subtype.ext (hinj hb1 hx₀ hb2))
    · rw [indicator_of_notMem hy]
      refine ENNReal.tsum_eq_zero.2 fun b => ?_
      rw [hkdef, indicator_of_notMem]
      rintro ⟨hb1, hb2⟩
      exact hy ⟨b, hb1, hb2⟩
  have e2 : ∫⁻ p, k p ∂((relMeasure μ R).map Prod.swap) =
      ∫⁻ x in D, h (f x) * (module μ R (x, f x))⁻¹ ∂μ := by
    have hδi : Measurable fun p => (module μ R p)⁻¹ := hδ.inv
    rw [relMeasure_swap_eq_withDensity hR, lintegral_withDensity_eq_lintegral_mul _ hδi hk,
      lintegral_relMeasure hR.measurableSet hR.countable_classes (hδi.mul hk),
      ← lintegral_indicator hD]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ D
    · rw [indicator_of_mem hx, tsum_eq_single ⟨f x, hfR x hx⟩]
      · simp only [Pi.mul_apply, hkdef]
        rw [indicator_of_mem (show (x, f x) ∈ G from ⟨hx, rfl⟩), mul_comm]
      · intro b hb
        simp only [Pi.mul_apply, hkdef]
        rw [indicator_of_notMem, mul_zero]
        rintro ⟨-, hb2⟩
        exact hb (Subtype.ext hb2.symm)
    · rw [indicator_of_notMem hx]
      refine ENNReal.tsum_eq_zero.2 fun b => ?_
      simp only [Pi.mul_apply, hkdef]
      rw [indicator_of_notMem, mul_zero]
      rintro ⟨hb1, -⟩
      exact hx hb1
  rw [← e1, e2]
  refine setLIntegral_congr_fun_ae hD ?_
  filter_upwards [ae_module_good hR] with x hx hxD
  rw [(hx (f x) (hfR x hxD)).2.2]

theorem rnDeriv_eq_module {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (φ : Monod.PartialTransformation R) :
    ∀ᵐ a ∂(μ.comap ((↑) : φ.dom → X)),
      ((μ.comap ((↑) : φ.cod → X)).map φ.e.symm).rnDeriv (μ.comap ((↑) : φ.dom → X)) a =
        module μ R ((φ.e a : X), (a : X)) := by
  have hembD := MeasurableEmbedding.subtype_coe φ.measurableSet_dom
  have hembC := MeasurableEmbedding.subtype_coe φ.measurableSet_cod
  haveI : SigmaFinite (μ.comap ((↑) : φ.dom → X)) := by
    refine SigmaFinite.of_map _ hembD.measurable.aemeasurable ?_
    rw [hembD.map_comap]
    infer_instance
  set H : φ.dom → ℝ≥0∞ := fun a => module μ R ((φ.e a : X), (a : X)) with hHdef
  have hH : Measurable H := (measurable_module μ R).comp
    ((measurable_subtype_coe.comp φ.e.measurable).prodMk measurable_subtype_coe)
  have hsp := ptFun_spec φ
  have heq : (μ.comap ((↑) : φ.cod → X)).map φ.e.symm =
      (μ.comap ((↑) : φ.dom → X)).withDensity H := by
    ext B hB
    rw [Measure.map_apply φ.e.symm.measurable hB, hembC.comap_apply, withDensity_apply _ hB]
    have h1 : ∫⁻ a in B, H a ∂(μ.comap ((↑) : φ.dom → X)) =
        ∫⁻ x in ((↑) : φ.dom → X) '' B, module μ R (ptFun φ x, x) ∂μ := by
      rw [← setLIntegral_subtype φ.measurableSet_dom B (fun x => module μ R (ptFun φ x, x))]
      refine setLIntegral_congr_fun hB fun a _ => ?_
      simp only [hHdef]
      rw [ptFun_of_mem φ a.2]
    have h2 : ((↑) : φ.cod → X) '' (φ.e.symm ⁻¹' B) = ptFun φ '' (((↑) : φ.dom → X) '' B) := by
      ext y
      constructor
      · rintro ⟨b, hb, rfl⟩
        refine ⟨φ.e.symm b, ⟨φ.e.symm b, hb, rfl⟩, ?_⟩
        rw [ptFun_of_mem φ (φ.e.symm b).2]
        simp
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        refine ⟨φ.e a, by simpa using ha, (ptFun_of_mem φ a.2).symm⟩
    have hBD : MeasurableSet (((↑) : φ.dom → X) '' B) :=
      MeasurableSet.subtype_image φ.measurableSet_dom hB
    have h3 := lintegral_image_eq hR hBD (measurable_ptFun φ).1
      (hsp.2.2.mono (Subtype.coe_image_subset _ _))
      (fun x hx => (hsp.1 x (Subtype.coe_image_subset _ _ hx)).2.2) (h := fun _ => 1)
      measurable_const
    simp only [one_mul, setLIntegral_const, one_mul] at h3
    rw [h1, h2, ← h3]
  rw [heq]
  exact Measure.rnDeriv_withDensity _ hH

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias rnDeriv_eq_module := CFWPlan.Main.P1.rnDeriv_eq_module

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §4. Finite equivalence relations: selectors -/

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §4. Finite equivalence relations: selectors and class sums -/

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P1
open ConnesFeldmanWeiss
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace CFWPlan.Main.P2
open ConnesFeldmanWeiss
/-!
# CFW work package P2: descriptive set theory, Lemmas 1–4

Proofs of the Route lemmas of `Solutions/CFW/Route.lean` §4 (`isTypeI_of_finite_classes`), §5
(Lemma 1 in relative form, subrelations, normal form of hyperfiniteness), §6 (Lemma 2), §7
(Lemma 3 and the bounded-set algebra) and §8 (Lemma 4). Each theorem restates the Route
statement verbatim in the namespace `CFWPlan.Main.P2`.
-/
/-! ## Helpers -/

/-- A set with at most one element has `encard ≤ 1` (as a cast natural number). -/
theorem encard_le_one_cast {α : Type*} {s : Set α} (h : ∀ a b, a ∈ s → b ∈ s → a = b) :
    s.encard ≤ ((1 : ℕ) : ℕ∞) := by
  rw [Nat.cast_one]
  exact encard_le_one_iff.2 h

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace CFWPlan.Main.P2
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §5. Type I relations: Lemma 1 (CFW p. 434), subrelations, normal form -/

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §5. Type I relations: Lemma 1 (CFW p. 434), subrelations, normal form of hyperfiniteness -/

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace CFWPlan.Main.P2
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace CFWPlan.Main.P2
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace CFWPlan.Main.P2
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace CFWPlan.Main.P2
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace CFWPlan.Main.P2
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

/-! ## §4. Finite equivalence relations are of type I -/

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

/-! ## §6. Lemma 2: disintegration over the fibres of an f.s.r. (CFW p. 435) -/

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace CFWPlan.Main.P2
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §6. Lemma 2: disintegration over the fibres of an f.s.r. (CFW p. 435) -/

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace CFWPlan.Main.P2
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace CFWPlan.Main.P2
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace CFWPlan.Main.P2
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace CFWPlan.Main.P2
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §7. Lemma 3: bounded subsets (CFW p. 435–436) and their algebra -/
/-- The total map of a partial transformation agrees with `φ.e` on the domain. -/
theorem ptFun_coe {R : Set (X × X)} (φ : Monod.PartialTransformation R) (a : φ.dom) :
    ptFun φ (a : X) = (φ.e a : X) := by
  unfold ptFun
  exact dif_pos a.2

/-- "`m`-a.e. on the graph of `φ`" is "`μ`-a.e. on the domain of `φ`" (for Borel properties). -/
theorem ae_ptGraph_iff {μ : Measure X} {R : Set (X × X)} (hR : IsDiscreteMeasured μ R)
    (φ : Monod.PartialTransformation R) {P : X × X → Prop} (hP : MeasurableSet {p | P p}) :
    (∀ᵐ p ∂relMeasure μ R, p ∈ CFWPlan.Route.ptGraph φ → P p) ↔
      ∀ᵐ x ∂μ, x ∈ φ.dom → P (x, ptFun φ x) := by
  have hG := CFWPlan.Main.measurableSet_ptGraph φ
  have hf : Measurable fun x => (x, ptFun φ x) :=
    measurable_id.prodMk (CFWPlan.Main.measurable_ptFun φ).1
  rw [← ae_restrict_iff' hG, (CFWPlan.Main.relMeasure_restrict_ptGraph hR φ).1,
    ae_map_iff hf.aemeasurable hP, ae_restrict_iff' φ.measurableSet_dom]

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §7. Lemma 3: bounded subsets (CFW p. 435–436) and their algebra -/

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace CFWPlan.Main.P2
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-- The module bound on a bounded `K ⊇ graph φ` gives the Radon–Nikodym bound. -/
theorem rnDeriv_bounds_of_ptGraph_subset {μ : Measure X} [SigmaFinite μ] {R K : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (hK : IsBoundedSubset μ R K) (φ : Monod.PartialTransformation R)
    (hφK : CFWPlan.Route.ptGraph φ ⊆ K) :
    ∃ c : ℝ≥0, 0 < c ∧
      (∀ᵐ a ∂(μ.comap ((↑) : φ.dom → X)),
        (c : ℝ≥0∞) ≤ ((μ.comap ((↑) : φ.cod → X)).map φ.e.symm).rnDeriv
            (μ.comap ((↑) : φ.dom → X)) a ∧
          ((μ.comap ((↑) : φ.cod → X)).map φ.e.symm).rnDeriv
            (μ.comap ((↑) : φ.dom → X)) a ≤ (c : ℝ≥0∞)⁻¹) ∧
      ∀ᵐ a ∂μ, a ∈ φ.dom → (c : ℝ≥0∞) ≤ module μ R (a, ptFun φ a) ∧
        module μ R (a, ptFun φ a) ≤ (c : ℝ≥0∞)⁻¹ := by
  obtain ⟨c, hc, hKδ⟩ := hK.bdd_module
  have hδm : Measurable (module μ R) := Measure.measurable_rnDeriv _ _
  have h1 : ∀ᵐ a ∂μ, a ∈ φ.dom → (c : ℝ≥0∞) ≤ module μ R (a, ptFun φ a) ∧
      module μ R (a, ptFun φ a) ≤ (c : ℝ≥0∞)⁻¹ := by
    refine (ae_ptGraph_iff hR φ (P := fun p => (c : ℝ≥0∞) ≤ module μ R p ∧
      module μ R p ≤ (c : ℝ≥0∞)⁻¹)
      ((measurableSet_le measurable_const hδm).inter (measurableSet_le hδm measurable_const))).1 ?_
    filter_upwards [hKδ] with p hp hpG using hp (hφK hpG)
  have hsw : ∀ᵐ a ∂μ, a ∈ φ.dom → module μ R (ptFun φ a, a) = (module μ R (a, ptFun φ a))⁻¹ := by
    refine (ae_ptGraph_iff hR φ (P := fun p => module μ R p.swap = (module μ R p)⁻¹)
      (measurableSet_eq_fun (hδm.comp measurable_swap) hδm.inv)).1 ?_
    filter_upwards [CFWPlan.Main.module_swap hR] with p hp _ using hp
  refine ⟨c, hc, ?_, h1⟩
  have h2 : ∀ᵐ a ∂μ, a ∈ φ.dom → (c : ℝ≥0∞) ≤ module μ R (ptFun φ a, a) ∧
      module μ R (ptFun φ a, a) ≤ (c : ℝ≥0∞)⁻¹ := by
    filter_upwards [h1, hsw] with a h1a h2a ha
    rw [h2a ha]
    obtain ⟨l, u⟩ := h1a ha
    exact ⟨ENNReal.le_inv_iff_le_inv.2 u, ENNReal.inv_le_inv.2 l⟩
  have h3 : ∀ᵐ a : φ.dom ∂(μ.comap ((↑) : φ.dom → X)),
      (c : ℝ≥0∞) ≤ module μ R (ptFun φ (a : X), (a : X)) ∧
        module μ R (ptFun φ (a : X), (a : X)) ≤ (c : ℝ≥0∞)⁻¹ := by
    have := (ae_restrict_iff' φ.measurableSet_dom).2 h2
    rw [← map_comap_subtype_coe φ.measurableSet_dom,
      (MeasurableEmbedding.subtype_coe φ.measurableSet_dom).ae_map_iff] at this
    exact this
  filter_upwards [h3, CFWPlan.Main.rnDeriv_eq_module hR φ] with a ha hrn
  rw [hrn, ← ptFun_coe]
  exact ha

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace CFWPlan.Main.P2
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-- **Lemma 3(a)** (CFW p. 435): `R` is a countable union of bounded sets. -/
theorem exists_isBoundedSubset_cover {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) :
    ∃ K : ℕ → Set (X × X), (∀ n, IsBoundedSubset μ R (K n)) ∧ R = ⋃ n, K n := by
  obtain ⟨φ, hφ⟩ := IsDiscreteMeasured.exists_generators hR
  have hδm : Measurable (module μ R) := Measure.measurable_rnDeriv _ _
  set c : ℕ → ℝ≥0 := fun k => ((k : ℝ≥0) + 1)⁻¹ with hc_def
  have hcpos : ∀ k, 0 < c k := fun k => inv_pos.2 (by positivity)
  set K : ℕ → Set (X × X) := fun m => {p | φ m.unpair.1 p.1 = p.2} ∩
    ({p | module μ R p = 0 ∨ module μ R p = ∞} ∪
      {p | (c m.unpair.2 : ℝ≥0∞) ≤ module μ R p ∧ module μ R p ≤ (c m.unpair.2 : ℝ≥0∞)⁻¹})
    with hK_def
  refine ⟨K, fun m => ?_, ?_⟩
  · refine ⟨?_, ?_, ⟨1, fun x => ?_⟩, ⟨1, fun y => ?_⟩, ⟨c m.unpair.2, hcpos _, ?_⟩⟩
    · refine (measurableSet_eq_fun ((φ _).measurable.comp measurable_fst) measurable_snd).inter
        (MeasurableSet.union ?_ ?_)
      · exact (hδm (measurableSet_singleton 0)).union (hδm (measurableSet_singleton ∞))
      · exact (measurableSet_le measurable_const hδm).inter (measurableSet_le hδm measurable_const)
    · rintro ⟨x, y⟩ hp
      exact (hφ x y).2 ⟨_, hp.1⟩
    · refine encard_le_one_cast fun y₁ y₂ h₁ h₂ => ?_
      have e₁ : φ m.unpair.1 y₁ = x := h₁.1
      have e₂ : φ m.unpair.1 y₂ = x := h₂.1
      exact (φ m.unpair.1).injective (e₁.trans e₂.symm)
    · refine encard_le_one_cast fun x₁ x₂ h₁ h₂ => ?_
      have e₁ : φ m.unpair.1 y = x₁ := h₁.1
      have e₂ : φ m.unpair.1 y = x₂ := h₂.1
      exact e₁.symm.trans e₂
    · filter_upwards [CFWPlan.Main.module_pos_lt_top hR] with p hp hpK
      rcases hpK.2 with h | h
      · rcases h with h | h
        · exact absurd h hp.1.ne'
        · exact absurd h hp.2.ne
      · exact h
  · ext ⟨x, y⟩
    constructor
    · intro hxy
      obtain ⟨n, hn⟩ := (hφ x y).1 hxy
      by_cases hbad : module μ R (x, y) = 0 ∨ module μ R (x, y) = ∞
      · exact mem_iUnion.2 ⟨Nat.pair n 0, by simp only [hK_def, Nat.unpair_pair]; exact ⟨hn, Or.inl hbad⟩⟩
      · simp only [not_or] at hbad
        set t := module μ R (x, y)
        have hmax : max t t⁻¹ ≠ ∞ := max_ne_top hbad.2 (ENNReal.inv_ne_top.2 hbad.1)
        obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hmax
        have hck : (c k : ℝ≥0∞) = ((k : ℝ≥0∞) + 1)⁻¹ := by
          rw [hc_def, ENNReal.coe_inv (by positivity)]
          push_cast
          rfl
        have hk1 : t ≤ (k : ℝ≥0∞) + 1 := ((le_max_left _ _).trans hk.le).trans le_self_add
        have hk2 : t⁻¹ ≤ (k : ℝ≥0∞) + 1 := ((le_max_right _ _).trans hk.le).trans le_self_add
        refine mem_iUnion.2 ⟨Nat.pair n k, ?_⟩
        simp only [hK_def, Nat.unpair_pair]
        refine ⟨hn, Or.inr ⟨?_, ?_⟩⟩
        · rw [hck]
          exact ENNReal.inv_le_iff_inv_le.2 hk2
        · rw [hck, inv_inv]
          exact hk1
    · intro hp
      obtain ⟨m, hm⟩ := mem_iUnion.1 hp
      exact (hφ x y).2 ⟨_, hm.1⟩

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace CFWPlan.Main.P2
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-- **Lemma 3 = milestone `exists_isBoundedSubset_cover_and_eq_iUnion_graph`** (CFW p. 435–436). -/
theorem lemma3 {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)} (hR : IsDiscreteMeasured μ R) :
    (∃ K : ℕ → Set (X × X), (∀ n, IsBoundedSubset μ R (K n)) ∧ R = ⋃ n, K n) ∧
    ∀ K, IsBoundedSubset μ R K → ∃ (n : ℕ) (φ : Fin n → Monod.PartialTransformation R),
      (∀ i, ∃ c : NNReal, 0 < c ∧ ∀ᵐ a ∂(μ.comap ((↑) : (φ i).dom → X)),
        (c : ENNReal) ≤ ((μ.comap ((↑) : (φ i).cod → X)).map (φ i).e.symm).rnDeriv
            (μ.comap ((↑) : (φ i).dom → X)) a ∧
          ((μ.comap ((↑) : (φ i).cod → X)).map (φ i).e.symm).rnDeriv
            (μ.comap ((↑) : (φ i).dom → X)) a ≤ (c : ENNReal)⁻¹) ∧
      K = ⋃ i, {p | ∃ a : (φ i).dom, p = ((a : X), ((φ i).e a : X))} := by
  refine ⟨exists_isBoundedSubset_cover hR, fun K hK => ?_⟩
  obtain ⟨n₁, h₁⟩ := hK.bdd_fst
  obtain ⟨n₂, h₂⟩ := hK.bdd_snd
  obtain ⟨k, φ, hKφ⟩ := CFWPlan.Route.cfw_lemma3b hR.measurableSet hK.measurableSet hK.subset
    (max n₁ n₂) (fun x => (h₁ x).trans (by exact_mod_cast le_max_left _ _))
    (fun y => (h₂ y).trans (by exact_mod_cast le_max_right _ _))
  refine ⟨k, φ, fun i => ?_, ?_⟩
  · have hsub : CFWPlan.Route.ptGraph (φ i) ⊆ K := by
      rw [hKφ]
      exact subset_iUnion (fun i => CFWPlan.Route.ptGraph (φ i)) i
    obtain ⟨c, hc, hrn, -⟩ := rnDeriv_bounds_of_ptGraph_subset hR hK (φ i) hsub
    exact ⟨c, hc, hrn⟩
  · rw [hKφ]
    refine iUnion_congr fun i => ?_
    ext p
    exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias lemma3 := CFWPlan.Main.P2.lemma3

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace CFWPlan.Main.P2
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ### The algebra of bounded sets -/

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ### The algebra of bounded sets (used in Lemma 8 for `K' ⊇ Δ` and `K₁ = K' ∪ K'K⁻¹`) -/

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace CFWPlan.Main.P2
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace CFWPlan.Main.P2
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace CFWPlan.Main.P2
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace CFWPlan.Main.P2
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace CFWPlan.Main.P2
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace CFWPlan.Main.P2
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §8. Lemma 4: local triviality (CFW p. 436) -/

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §8. Lemma 4: local triviality (CFW p. 436) -/

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace CFWPlan.Main.P2
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Main.P3
open ConnesFeldmanWeiss
variable {Ω : Type*} [MeasurableSpace Ω]
variable {ν : Measure Ω} {Λ : (Ω → ℝ) → ℝ}
/-!
# CFW work package P3: functional analysis and means

Proofs of the Route lemmas of §9 (`(L¹)* = L∞`, Hahn–Banach separation, weak* limits), §10 (means
in Monod's form), the mean constructions `isAmenableRel_of_isFinHyp` (§13) and
`isAmenableRel_of_generator` (§14), and Corollary 12's means `exists_fiberedMean`,
`isAmenableRel_tailRel` (§16). Every theorem whose name is a Route lemma restates that lemma
verbatim; helper lemmas have names of their own.

Deviations from the Route's proof sketches (statements unchanged):
* `(L¹)* = L∞` (finite measure) goes through the signed measure `E ↦ Λ 1_E` and
  `SignedMeasure.withDensityᵥ_rnDeriv_eq`; the σ-finite case passes to the equivalent finite
  measure `w ν` (`w > 0`) instead of gluing over spanning sets.
* `mul_fst` approximates `g` on the level sets `{⌊(n+1) g⌋ = k}` (countably many, each handled
  by the invariance under `id_A`) instead of by simple functions.
* The fibred means are built from a Borel partition on whose pieces the base map is injective
  (`Pieces`, `fmean`); `isAmenableRel_tailRel` uses them directly, together with their row
  locality (`fmean_local`), which `exists_fiberedMean` does not export.
-/
/-! ## §9. Functional analysis -/

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Main.P3
open ConnesFeldmanWeiss
variable {Ω : Type*} [MeasurableSpace Ω]

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {Ω : Type*} [MeasurableSpace Ω]
/-! ## §9. Functional analysis: `(L¹)* = L∞`, Hahn–Banach separation, weak* limits

Mathlib has Hahn–Banach separation (`geometric_hahn_banach_open`) and the map `L∞ → (L¹)*`
(`Function/Holder.lean`), but not the representation `(L¹)* → L∞`. These lemmas are stated for
functions (not `Lp` classes) because their users build functionals by hand. -/

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Main.P3
open ConnesFeldmanWeiss
variable {Ω : Type*} [MeasurableSpace Ω]

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {Ω : Type*} [MeasurableSpace Ω]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Main.P3
open ConnesFeldmanWeiss
variable {Ω : Type*} [MeasurableSpace Ω]

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {Ω : Type*} [MeasurableSpace Ω]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Main.P3
open ConnesFeldmanWeiss
variable {Ω : Type*} [MeasurableSpace Ω]

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {Ω : Type*} [MeasurableSpace Ω]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Main.P3
open ConnesFeldmanWeiss
variable {Ω : Type*} [MeasurableSpace Ω]

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {Ω : Type*} [MeasurableSpace Ω]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Main.P3
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
variable {R : Set (X × X)}
/-! ## §10. Means on `R` -/

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Main.P3
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Main.P3
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §10. Means on `R` (CFW Def. 5–6, p. 437, in Monod's form) -/

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Main.P3
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Main.P3
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Main.P3
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

/-! ## §11. Lemma 8: the Følner condition (CFW pp. 440–442) -/

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
namespace CFWPlan.Main.P4
open ConnesFeldmanWeiss
/-!
# CFW route, package P4 (Lemma 8 and restriction)

Proofs of the Route lemmas of §11 (Lemma 8: the Reiter step, the Følner set, good rows, the
f.s.r. from rows, the boundary estimate via Lemma 2, Lemma 8 itself) and of the first eight
lemmas of §12 (the normalized restriction `(μ_A, R_A)`, its amenability, `exists_fsr_in`). Each
Route lemma `CFWPlan.Main.foo` is restated verbatim here as `CFWPlan.Main.P4.foo`.
-/
/-! ## Helpers -/

end CFWPlan.Main.P4
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
namespace CFWPlan.Main.P4
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P4
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
namespace CFWPlan.Main.P4
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P4
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
namespace CFWPlan.Main.P4
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P4
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
namespace CFWPlan.Main.P4
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P4
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

/-! ## §12. Restriction to a Borel set, and Lemma 9 (CFW pp. 442–444) -/

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
namespace CFWPlan.Main.P4
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §12. Restriction to a Borel set -/

end CFWPlan.Main.P4
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
namespace CFWPlan.Main.P4
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P4
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
namespace CFWPlan.Main.P4
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P4
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
namespace CFWPlan.Main.P4
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P4
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
namespace CFWPlan.Main.P4
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P4
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
namespace CFWPlan.Main.P4
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P4
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
namespace CFWPlan.Main.P5
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-!
# CFW route, package P5 (Lemma 9, Theorem 10, Dye glue, the goal; tail relations)

Proofs of the Route lemmas of §12 (the last five: the countable exhaustion replacing Zorn, unions
of extensions, the chain and step lemmas of Lemma 9, Lemma 9 itself), §13 (the liminf argument,
finite relations are hyperfinite, finite exhaustion of type I relations, hyperfinite ⇒ finite
union, both halves of Theorem 10; `isAmenableRel_of_isFinHyp` is package P3), §14
(`exists_generator_of_finite_union`, `exists_generator_of_isHyperfinite`), §15
(`isNonsingular_of_generator`) and §16 (all but P3's `exists_fiberedMean`,
`isAmenableRel_tailRel`). Each Route lemma `CFWPlan.Main.foo` is restated verbatim here as
`CFWPlan.Main.P5.foo`. The two tail-relation mission statements are restated verbatim as
`chk_isHyperfinite_tailRel_of_isHyperfinite` and `chk_isHyperfinite_tailRel_of_isNonsingular`
and proved for the bundle's `IsNonsingular` (preimages only) through
`isHyperfinite_tailRel_core`.

Deviations from the Route's proof sketches (statements unchanged):
* `isFinHyp_of_approx` uses Borel–Cantelli (`measure_limsup_atTop_eq_zero`) for the bad sets
  `Kₖ \ Tₖ` instead of summing tails.
* `exists_finite_exhaustion_of_isTypeI` uses the sets `Gₖ = X₀ ∩ ⋃_{j ≤ k} {x | ψⱼ (s x) = x}`
  instead of an index function.
* `IsHyperfinite.isFinHyp` gets its approximations by continuity from above in two steps
  (first `m(Kⱼ \ Sₙ) → 0`, then the finite exhaustion of `Sₙ`).
* `exists_generator_of_isHyperfinite` applies the Borel core to the `Fₙ` of `IsFinHyp` directly
  (they cannot cross the saturated null set, being inside `R`).
-/
/-! ## Helpers -/

/-! ## §12. Lemma 9 (CFW pp. 442–444) -/

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
namespace CFWPlan.Main.P5
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
namespace CFWPlan.Main.P5
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
namespace CFWPlan.Main.P5
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
namespace CFWPlan.Main.P5
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

/-! ## §13. Hyperfinite = increasing union of finite relations; Theorem 10 (CFW p. 444) -/

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
namespace CFWPlan.Main.P5
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §13. Hyperfinite = increasing union of finite relations; Theorem 10 (CFW p. 444) -/

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
namespace CFWPlan.Main.P5
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
namespace CFWPlan.Main.P5
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
namespace CFWPlan.Main.P5
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
namespace CFWPlan.Main.P5
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Main.P3
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §13. Theorem 10 "⇒": finite unions give means -/

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
namespace CFWPlan.Main.P5
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P6
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-!
# CFW route, work package P6: Dye's Borel core

Proofs of the three Route lemmas of §14 that make up the Borel combinatorial core of Dye's theorem
("an increasing union of finite Borel equivalence relations is the orbit relation of one Borel
automorphism"; Slaman–Steel 1988, Weiss 1984, Dougherty–Jackson–Kechris 1994 Thm 5.1):

* `exists_cycle_sequence` (D1, nested cycles by cutting and stacking): `cycle_step` links the
  blocks of each new class in the order of the key `embeddingReal X` of their last points; Borel by
  the Lusin–Novikov argmin `exists_argmin`; single-cycle bookkeeping by `next_reach`.
* `exists_successor_map` (D2a, the limit successor map).
* `exists_generator_of_successor` (D2b): the successor data are put in the symmetric form
  `ChainData` (with the Borel inverse `ρ` of `τ`); `omega_part` handles classes of type `ω` (and,
  by `ChainData.symm`, of type `ω*`) with the zig-zag `zz`, `fin_part` the finite and `ℤ` classes;
  `goodOn_piecewise` glues the three pieces.

No measure theory is used.

Phase 2 (§17, Zimmer and Corollary 14): `polishSpace_of_lcsc` (via `polishSpace_of_lcsc_space`,
the one-point compactification), `countable_of_discrete_subgroup`, `standardBorelSpace_quotient`,
`exists_descent`, `exists_equivariant_index` (a Borel fundamental domain from right translates of a
small neighbourhood, disjointified modulo `Γ`), `isDiscreteMeasured_orbit`,
`exists_strict_invariant_version` (essential supremum over cosets, in `ℝ≥0∞`),
`exists_relative_density` (via `integral_mul_right_haar` and `convol_props`),
`exists_equivariant_expectation` and `zimmer`. The last three use the §9 Route lemmas
`exists_bounded_density_of_functional` and `ae_eq_of_forall_integral_mul_eq` (package P3).
-/
/-! ### A Borel argmin over finite sections -/

end CFWPlan.Main.P6
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P6
open ConnesFeldmanWeiss
variable {X : Type*}
/-! ### The cyclic successor on a finite set ordered by a key -/

end CFWPlan.Main.P6
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P6
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P6
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §14. Dye's theorem (external: Dye 1959; CFW p. 434 "cf. [9]")

CFW only cite Dye. The route proves "⇒" by reducing hyperfiniteness to an a.e. increasing union of
finite Borel relations (§13, which already contains the type I → finite reduction via Lemma 1) and
then the Borel combinatorial lemma "an increasing union of finite Borel equivalence relations is
the orbit relation of one Borel automorphism" (Slaman–Steel 1988, Weiss 1984; Dougherty–Jackson–
Kechris, Trans. AMS 341 (1994), Thm 5.1; Kechris–Miller, *Topics in orbit equivalence*, LNM 1852,
2004, §6). "⇐" goes through amenability (`ℤ` is amenable) and Theorem 10. -/

end CFWPlan.Main
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P6
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P6
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P6
open ConnesFeldmanWeiss
variable {X : Type*}
/-! ### From a successor map to one automorphism -/

end CFWPlan.Main.P6
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P6
open ConnesFeldmanWeiss
variable {X : Type*}
namespace ChainData
variable {E : Set (X × X)} {A B : Set X} {α β : X → X}

end ChainData
end CFWPlan.Main.P6
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P6
open ConnesFeldmanWeiss
variable {X : Type*}

end CFWPlan.Main.P6
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P6
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P6
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
namespace CFWPlan.Main.P5
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §14. Dye's theorem: the glue around P6's Borel core -/

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
namespace CFWPlan.Main.P5
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Main.P3
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §14. A relation generated by one automorphism is amenable -/

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
namespace CFWPlan.Main.P5
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §15. The goal (CFW p. 431) -/

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §15. The goal (CFW p. 431) -/

/-! ## §16. Corollaries 12 and 13: tail relations (CFW pp. 444–445)

Planned for the strengthened bundle: `IsNonsingular` also requiring that images of null Borel sets
are null (`IsNonsingular'` below), and conclusions that also assert discreteness/quasi-invariance.
Without the image condition the tail relation need not be quasi-invariant (audit near-misses in
`readbacks/isHyperfinite_tailRel_*.coverage.md`), Theorem 10 does not apply, and this route does
not prove the current statements (see `PLAN.md` §3). -/

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
namespace CFWPlan.Main.P5
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §16. Corollaries 12 and 13: tail relations (CFW pp. 444–445)

The mission statements use the bundle's `IsNonsingular` (preimages of null sets are null), not the
Route's `IsNonsingular'` (images too). Route: a conull Borel set `X₀`, forward invariant under `θ`,
on which `θ` sends null sets to null sets (`exists_forward_invariant`: Lusin–Novikov pieces on which
`θ` is injective, and on each the part of `μ` singular to `θ_*(μ|piece)`, a Lebesgue
decomposition); then `θ' = θ` on `X₀`, `id` off `X₀`, and `R' = cutOff R X₀ᶜ` satisfy the
hypotheses of the Route's `cor12`, and the tail relations of `(θ', R')` and `(θ, R)` agree on
`X₀ × X₀` (`isHyperfinite_tailRel_core`). -/

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
namespace CFWPlan.Main.P5
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Main.P3
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §16. Fibred means (CFW p. 445) -/

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Main.P3
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
namespace Pieces
variable {g : X → X}

end Pieces
end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Main.P3
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Main.P3
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
variable {μ : Measure X} {R : Set (X × X)} {P : (X × X → ℝ) → X → ℝ} {g : X → X}

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Main.P3
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Main.P3
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §16. Corollary 12's means: the tail relation is amenable -/

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
namespace CFWPlan.Main.P5
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
namespace CFWPlan.Main.P5
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
namespace CFWPlan.Main.P5
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
/-! ## §17. Zimmer's theorem and Corollary 14 (CFW p. 446; external: Zimmer 1977/78)

Route without Reiter's condition, measurable sections or Weil's formula: the amenable mean `M` of
`P` is pushed into `L∞(G, Haar)` by `L¹`-duality (`Λ_F(c) = M(p ↦ ∫ c(g) F(g p) dg)`), made strictly
right-`P`-invariant by an essential supremum over cosets, and descended to `G ⧸ P`; the relation
mean is `F_f(g) = f(gP, κ(g)⁻¹ gP)` for a Borel `Γ`-equivariant `κ : G → Γ`. -/

end CFWPlan.Main
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P6
open ConnesFeldmanWeiss

end CFWPlan.Main.P6
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P6
open ConnesFeldmanWeiss
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

end CFWPlan.Main.P6
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

end CFWPlan.Main
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P6
open ConnesFeldmanWeiss
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

end CFWPlan.Main.P6
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

end CFWPlan.Main
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P6
open ConnesFeldmanWeiss
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

end CFWPlan.Main.P6
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

end CFWPlan.Main
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P6
open ConnesFeldmanWeiss
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

end CFWPlan.Main.P6
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

end CFWPlan.Main
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P6
open ConnesFeldmanWeiss
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

end CFWPlan.Main.P6
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

end CFWPlan.Main
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P6
open ConnesFeldmanWeiss
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

end CFWPlan.Main.P6
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
/-! ## §18. The sixteen mission statements, verbatim, derived from the route

Each `chk_<name>` has the statement of `cfw-mission/statements/Thm_ConnesFeldmanWeiss_<name>.lean`
copied character for character (inside `open ConnesFeldmanWeiss`). -/

end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
namespace CFWPlan.Main.P5
open ConnesFeldmanWeiss
/-! ## The two tail-relation mission statements (Route §18), verbatim -/

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
end CFWPlan.Main
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
namespace CFWPlan.Main.P5
open ConnesFeldmanWeiss

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss

end CFWPlan.Main
end
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
open CFWPlan
open CFWPlan.Main
open ConnesFeldmanWeiss
theorem solution {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite μ]
    (R : Set (X × X)) (hR : IsDiscreteMeasured μ R) :
    (∃ K : ℕ → Set (X × X), (∀ n, IsBoundedSubset μ R (K n)) ∧ R = ⋃ n, K n) ∧
    ∀ K, IsBoundedSubset μ R K → ∃ (n : ℕ) (φ : Fin n → Monod.PartialTransformation R),
      (∀ i, ∃ c : NNReal, 0 < c ∧ ∀ᵐ a ∂(μ.comap ((↑) : (φ i).dom → X)),
        (c : ENNReal) ≤ ((μ.comap ((↑) : (φ i).cod → X)).map (φ i).e.symm).rnDeriv
            (μ.comap ((↑) : (φ i).dom → X)) a ∧
          ((μ.comap ((↑) : (φ i).cod → X)).map (φ i).e.symm).rnDeriv
            (μ.comap ((↑) : (φ i).dom → X)) a ≤ (c : ENNReal)⁻¹) ∧
      K = ⋃ i, {p | ∃ a : (φ i).dom, p = ((a : X), ((φ i).e a : X))} :=
  lemma3 hR
end
