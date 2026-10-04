-- Prove2me | solution 1 for ConnesFeldmanWeiss.exists_finiteSubrelation_measure_diff_lt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T21:03:28.445625+00:00
-- url     : https://prove2.me/submissions/dbc8095f-09b5-46fe-bbf3-e64b9e58bbba

import Theorems.Thm_LusinNovikov_exists_disjoint_injOn_fst_iUnion_eq_of_countable_sections
import Theorems.Thm_LusinNovikov_measurableSet_image_fst_of_countable_sections
import Mathlib
import Definitions.Def_Monod_PiecewiseProjective
import Theorems.Thm_ConnesFeldmanWeiss_exists_finiteSubrelation_boundary_lt
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

/-- The saturation of an arbitrary null set is null (outer measure).
*Proof:* monotonicity from the measurable hull. *Size:* 8 (proved). -/
theorem IsDiscreteMeasured.saturation_null {μ : Measure X} {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) {A : Set X} (hA : μ A = 0) : μ (saturation R A) = 0 := by
  have h := hR.quasiInvariant (toMeasurable μ A) (measurableSet_toMeasurable μ A)
    (by rw [measure_toMeasurable]; exact hA)
  refine measure_mono_null ?_ h
  rintro x ⟨y, hy, hxy⟩
  exact ⟨y, subset_toMeasurable μ A hy, hxy⟩

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
theorem measurableSet_saturation {R : Set (X × X)} (hR : MeasurableSet R)
    (hequiv : Equivalence fun x y => (x, y) ∈ R) (hcount : ∀ x, {y | (x, y) ∈ R}.Countable)
    {A : Set X} (hA : MeasurableSet A) : MeasurableSet (saturation R A) := by
  obtain ⟨φ, hφ⟩ :=
    ConnesFeldmanWeiss.exists_seq_measurableEquiv_of_countable_classes R hR hequiv hcount
  have h : saturation R A = ⋃ n, (φ n) ⁻¹' A := by
    ext x
    simp only [saturation, mem_ofPred_eq, mem_iUnion, mem_preimage]
    constructor
    · rintro ⟨y, hy, hxy⟩
      obtain ⟨n, rfl⟩ := (hφ x y).1 hxy
      exact ⟨n, hy⟩
    · rintro ⟨n, hn⟩
      exact ⟨φ n x, hn, (hφ x _).2 ⟨n, rfl⟩⟩
  rw [h]
  exact MeasurableSet.iUnion fun n => (φ n).measurable hA

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]
alias measurableSet_saturation := CFWPlan.Main.P1.measurableSet_saturation

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

/-- The identity partial transformation on a measurable set `A` (needs `R` reflexive).
`shiftRel` by it multiplies a function by `1_A` of the first coordinate (CFW p. 436 with
`φ = id_A`); this is the source of the `L∞(X)`-module property of means. -/
def ptId {R : Set (X × X)} (hR : ∀ x, (x, x) ∈ R) (A : Set X)
    (hA : MeasurableSet A) : Monod.PartialTransformation R where
  dom := A
  cod := A
  measurableSet_dom := hA
  measurableSet_cod := hA
  e := MeasurableEquiv.refl A
  graph_subset := fun a => hR (a : X)

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
alias ptFun_spec := CFWPlan.Main.P1.ptFun_spec

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
theorem exists_pt_of_injOn [StandardBorelSpace X] {R : Set (X × X)} {D : Set X}
    (hD : MeasurableSet D) {f : X → X} (hf : Measurable f) (hinj : InjOn f D)
    (hR : ∀ x ∈ D, (x, f x) ∈ R) :
    ∃ ψ : Monod.PartialTransformation R, ψ.dom = D ∧ ψ.cod = f '' D ∧ ∀ x ∈ D, ptFun ψ x = f x := by
  set G : Set (X × X) := {p | p.1 ∈ D ∧ f p.1 = p.2} with hGdef
  have hG : MeasurableSet G := (hD.preimage measurable_fst).inter
    (measurableSet_eq_fun (hf.comp measurable_fst) measurable_snd)
  have hGR : G ⊆ R := by
    rintro ⟨x, y⟩ ⟨hx, hxy⟩
    simp only at hx hxy
    subst hxy
    exact hR x hx
  have h₁ : InjOn Prod.fst G := by
    rintro ⟨x, y⟩ ⟨hx, hxy⟩ ⟨x', y'⟩ ⟨hx', hxy'⟩ (h : x = x')
    simp only at hx hxy hx' hxy'
    subst hxy hxy' h
    rfl
  have h₂ : InjOn Prod.snd G := by
    rintro ⟨x, y⟩ ⟨hx, hxy⟩ ⟨x', y'⟩ ⟨hx', hxy'⟩ (h : y = y')
    simp only at hx hxy hx' hxy'
    subst hxy hxy'
    rw [hinj hx hx' h]
  obtain ⟨ψ, hψ⟩ := CFWPlan.Route.exists_partialTransformation_of_biInjOn hG hGR h₁ h₂
  have hmem : ∀ p, p ∈ G ↔ p.1 ∈ ψ.dom ∧ ptFun ψ p.1 = p.2 := by
    intro p
    rw [← hψ, ptGraph_eq]
    rfl
  have hdom : ψ.dom = D := by
    ext x
    constructor
    · intro hx
      exact ((hmem (x, ptFun ψ x)).2 ⟨hx, rfl⟩).1
    · intro hx
      exact ((hmem (x, f x)).1 ⟨hx, rfl⟩).1
  have hfun : ∀ x ∈ D, ptFun ψ x = f x := fun x hx => ((hmem (x, f x)).1 ⟨hx, rfl⟩).2
  refine ⟨ψ, hdom, ?_, hfun⟩
  ext y
  constructor
  · intro hy
    have h := (ptFun_spec ψ).2.1 y hy
    have hx : ptInv ψ y ∈ D := hdom ▸ h.1
    exact ⟨ptInv ψ y, hx, by rw [← hfun _ hx, h.2]⟩
  · rintro ⟨x, hx, rfl⟩
    rw [← hfun x hx]
    exact ((ptFun_spec ψ).1 x (hdom ▸ hx)).1

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
alias exists_pt_of_injOn := CFWPlan.Main.P1.exists_pt_of_injOn

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
open Classical in
theorem shiftRel_eq {R : Set (X × X)} (φ : Monod.PartialTransformation R) (f : X × X → ℝ) :
    φ.shiftRel f = fun p => if p.1 ∈ φ.cod then f (ptInv φ p.1, p.2) else 0 := by
  funext p
  by_cases h : p.1 ∈ φ.cod
  · rw [if_pos h, ptInv_of_mem φ h]
    unfold Monod.PartialTransformation.shiftRel
    rw [dif_pos h]
  · rw [if_neg h]
    unfold Monod.PartialTransformation.shiftRel
    rw [dif_neg h]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
alias shiftRel_eq := CFWPlan.Main.P1.shiftRel_eq

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
open Classical in
theorem shiftBase_eq {R : Set (X × X)} (φ : Monod.PartialTransformation R) (F : X → ℝ) :
    φ.shiftBase F = fun y => if y ∈ φ.cod then F (ptInv φ y) else 0 := by
  funext y
  by_cases h : y ∈ φ.cod
  · rw [if_pos h, ptInv_of_mem φ h]
    unfold Monod.PartialTransformation.shiftBase
    rw [dif_pos h]
  · rw [if_neg h]
    unfold Monod.PartialTransformation.shiftBase
    rw [dif_neg h]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
alias shiftBase_eq := CFWPlan.Main.P1.shiftBase_eq

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
alias relMeasure_apply := CFWPlan.Main.P1.relMeasure_apply

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
alias sigmaFinite_relMeasure := CFWPlan.Main.P1.sigmaFinite_relMeasure

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

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §3. The module `δ` (CFW p. 434) -/

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
alias relMeasure_swap_eq_withDensity := CFWPlan.Main.P1.relMeasure_swap_eq_withDensity

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
/-! ### The algebra of bounded sets -/
/-- Measurable subsets of bounded sets are bounded. -/
theorem IsBoundedSubset.mono' {μ : Measure X} {R K K' : Set (X × X)} (hK : IsBoundedSubset μ R K)
    (hK' : MeasurableSet K') (h : K' ⊆ K) : IsBoundedSubset μ R K' := by
  obtain ⟨n₁, h₁⟩ := hK.bdd_snd
  obtain ⟨n₂, h₂⟩ := hK.bdd_fst
  obtain ⟨c, hc, hδ⟩ := hK.bdd_module
  exact ⟨hK', h.trans hK.subset,
    ⟨n₁, fun x => (encard_le_encard (s := {y | (y, x) ∈ K'}) (t := {y | (y, x) ∈ K})
      fun y hy => h hy).trans (h₁ x)⟩,
    ⟨n₂, fun y => (encard_le_encard (s := {x | (y, x) ∈ K'}) (t := {x | (y, x) ∈ K})
      fun x hx => h hx).trans (h₂ y)⟩,
    ⟨c, hc, hδ.mono fun p hp hpK' => hp (h hpK')⟩⟩

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ### The algebra of bounded sets (used in Lemma 8 for `K' ⊇ Δ` and `K₁ = K' ∪ K'K⁻¹`) -/
alias IsBoundedSubset.mono' := CFWPlan.Main.P2.IsBoundedSubset.mono'

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
/-- `R_A` of CFW p. 443, made an equivalence relation on `X` by adding the diagonal. -/
def restrictRel (R : Set (X × X)) (A : Set X) : Set (X × X) :=
  (R ∩ A ×ˢ A) ∪ {p | p.1 = p.2}

/-- The normalized restriction `μ_A = μ(A)⁻¹ μ|_A`. With it, points outside `A` are null, so an
f.s.r. of `R_A` given by Lemma 8 can be cut down to `A` without changing any measure. -/
noncomputable def restrictMeasure (μ : Measure X) (A : Set X) : Measure X :=
  (μ A)⁻¹ • μ.restrict A

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
/-- `μ_A` is a probability measure. -/
theorem isProbabilityMeasure_restrictMeasure {μ : Measure X} [IsFiniteMeasure μ] {A : Set X}
    (hA : μ A ≠ 0) : IsProbabilityMeasure (restrictMeasure μ A) := by
  constructor
  rw [restrictMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hA (measure_ne_top μ A)

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
theorem restrictMeasure_apply {μ : Measure X} {A : Set X} (hA : MeasurableSet A) (S : Set X) :
    restrictMeasure μ A S = (μ A)⁻¹ * μ (S ∩ A) := by
  rw [restrictMeasure, Measure.smul_apply, Measure.restrict_apply' hA, smul_eq_mul]

theorem ae_restrictMeasure_mem {μ : Measure X} {A : Set X} (hA : MeasurableSet A) :
    ∀ᵐ x ∂(restrictMeasure μ A), x ∈ A :=
  Measure.ae_smul_measure (ae_restrict_mem hA) _

/-- `R_A` is discrete measured for `μ_A`. -/
theorem isDiscreteMeasured_restrict {μ : Measure X} {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) {A : Set X} (hA : MeasurableSet A) :
    IsDiscreteMeasured (restrictMeasure μ A) (restrictRel R A) := by
  have hRe := hR.equivalence
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hR.measurableSet.inter (hA.prod hA)).union (measurableSet_diagonal (α := X))
  · refine ⟨fun x => Or.inr rfl, ?_, ?_⟩
    · rintro x y (⟨hxy, hx, hy⟩ | h)
      · exact Or.inl ⟨hRe.symm hxy, hy, hx⟩
      · exact Or.inr (Eq.symm h)
    · rintro x y z (⟨hxy, hx, hy⟩ | hxy) (⟨hyz, hy', hz⟩ | hyz)
      · exact Or.inl ⟨hRe.trans hxy hyz, hx, hz⟩
      · have hyz' : y = z := hyz
        subst hyz'
        exact Or.inl ⟨hxy, hx, hy⟩
      · have hxy' : x = y := hxy
        subst hxy'
        exact Or.inl ⟨hyz, hy', hz⟩
      · have hxy' : x = y := hxy
        have hyz' : y = z := hyz
        exact Or.inr (hxy'.trans hyz')
  · intro x
    refine ((hR.countable_classes x).union (countable_singleton x)).mono ?_
    rintro y (⟨hxy, -, -⟩ | hxy)
    · exact Or.inl hxy
    · exact Or.inr (Eq.symm hxy)
  · intro B hB hB0
    rw [restrictMeasure_apply hA] at hB0 ⊢
    rcases mul_eq_zero.1 hB0 with h | h
    · rw [h, zero_mul]
    · refine mul_eq_zero.2 (Or.inr (measure_mono_null ?_
        (IsDiscreteMeasured.saturation_null hR h)))
      rintro x ⟨⟨y, hy, (⟨hxy, -, hyA⟩ | hxy)⟩, hx⟩
      · exact ⟨y, ⟨hy, hyA⟩, hxy⟩
      · have hxy' : x = y := hxy
        subst hxy'
        exact ⟨x, ⟨hy, hx⟩, hRe.refl x⟩

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
/-- `m` for `(μ_A, R_A)` is `μ(A)⁻¹ m` on subsets of `A × A`. -/
theorem relMeasure_restrict_eq {μ : Measure X} {R : Set (X × X)} (hR : IsDiscreteMeasured μ R)
    {A : Set X} (hA : MeasurableSet A) {E : Set (X × X)} (hE : MeasurableSet E)
    (hEA : E ⊆ A ×ˢ A) :
    relMeasure (restrictMeasure μ A) (restrictRel R A) E = (μ A)⁻¹ * relMeasure μ R E := by
  have hRA := isDiscreteMeasured_restrict hR hA
  have hER : E ∩ restrictRel R A = E ∩ R := by
    ext ⟨x, y⟩
    constructor
    · rintro ⟨hE', (⟨hxy, -⟩ | hxy)⟩
      · exact ⟨hE', hxy⟩
      · have hxy' : x = y := hxy
        subst hxy'
        exact ⟨hE', hR.equivalence.refl x⟩
    · rintro ⟨hE', hxy⟩
      exact ⟨hE', Or.inl ⟨hxy, hEA hE'⟩⟩
  rw [CFWPlan.Main.relMeasure_apply hRA.measurableSet hRA.countable_classes hE,
    CFWPlan.Main.relMeasure_apply hR.measurableSet hR.countable_classes hE, hER, restrictMeasure,
    lintegral_smul_measure, smul_eq_mul, ← lintegral_indicator hA]
  congr 1
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ A
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx]
    have : {y | (x, y) ∈ E ∩ R} = ∅ := by
      ext y
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨hE', -⟩
      exact hx (hEA hE').1
    rw [this, encard_empty]
    simp

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
/-- Cutting an f.s.r. of `R_A` down to `A` gives an f.s.r. of `R`. -/
theorem IsFiniteSubrelation.inter_restrict {R T : Set (X × X)} (hRrefl : ∀ x, (x, x) ∈ R)
    {A : Set X} (hA : MeasurableSet A) (hT : IsFiniteSubrelation (restrictRel R A) T) :
    IsFiniteSubrelation R (T ∩ A ×ˢ A) ∧ unitSpace (T ∩ A ×ˢ A) = unitSpace T ∩ A := by
  refine ⟨⟨hT.measurableSet.inter (hA.prod hA), ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rintro ⟨x, y⟩ ⟨hT', hxA, hyA⟩
    rcases hT.subset hT' with ⟨h, -⟩ | h
    · exact h
    · have h' : x = y := h
      subst h'
      exact hRrefl x
  · rintro ⟨x, y⟩ ⟨hT', hxA, hyA⟩
    obtain ⟨hx, hy⟩ := hT.mem_unitSpace _ hT'
    exact ⟨⟨hx, hxA, hxA⟩, ⟨hy, hyA, hyA⟩⟩
  · rintro x y ⟨hT', hxA, hyA⟩
    exact ⟨hT.symm _ _ hT', hyA, hxA⟩
  · rintro x y z ⟨h1, hxA, -⟩ ⟨h2, -, hzA⟩
    exact ⟨hT.trans _ _ _ h1 h2, hxA, hzA⟩
  · intro x
    exact (hT.finite_classes x).subset fun y hy => hy.1
  · ext x
    simp only [unitSpace, mem_inter_iff, mem_ofPred_eq, mem_prod, and_self]

/-- A Borel retraction of the saturation of `A` onto `A` along `R` (FM generators, `Nat.find`). -/
theorem exists_measurable_retraction {μ : Measure X} {R : Set (X × X)} (hR : IsDiscreteMeasured μ R)
    {A : Set X} (hA : MeasurableSet A) :
    ∃ ρ : X → X, Measurable ρ ∧ (∀ x ∈ saturation R A, ρ x ∈ A ∧ (x, ρ x) ∈ R) ∧
      ∀ x ∈ A, ρ x = x := by
  classical
  obtain ⟨φ, hφ⟩ := IsDiscreteMeasured.exists_generators hR
  set ψ : ℕ → X → X := fun n => Nat.casesOn n id (fun k => φ k) with hψdef
  have hψ0 : ∀ x, ψ 0 x = x := fun x => rfl
  have hψS : ∀ k x, ψ (k + 1) x = φ k x := fun k x => rfl
  have hψm : ∀ n, Measurable (ψ n) := by
    intro n
    cases n with
    | zero => exact measurable_id
    | succ k => exact (φ k).measurable
  have hψR : ∀ n x, (x, ψ n x) ∈ R := by
    intro n x
    cases n with
    | zero => exact hR.equivalence.refl x
    | succ k => exact (hφ x _).2 ⟨k, rfl⟩
  have hsat : MeasurableSet (saturation R A) :=
    CFWPlan.Main.measurableSet_saturation hR.measurableSet hR.equivalence hR.countable_classes hA
  set p : ℕ → X → Prop := fun n x => x ∈ saturation R A → ψ n x ∈ A with hpdef
  have hex : ∀ x, ∃ n, p n x := by
    intro x
    by_cases hx : x ∈ saturation R A
    · obtain ⟨y, hy, hxy⟩ := hx
      obtain ⟨k, hk⟩ := (hφ x y).1 hxy
      exact ⟨k + 1, fun _ => by rw [hψS, hk]; exact hy⟩
    · exact ⟨0, fun h => absurd h hx⟩
  have hpm : ∀ n, MeasurableSet {x | p n x} := fun n => hsat.compl.union (hψm n hA) |>.congr
    (by ext x; simp only [hpdef, mem_union, mem_compl_iff, mem_preimage, mem_ofPred_eq]; tauto)
  refine ⟨fun x => ψ (Nat.find (hex x)) x, Measurable.find hψm hpm hex, ?_, ?_⟩
  · intro x hx
    exact ⟨Nat.find_spec (hex x) hx, hψR _ x⟩
  · intro x hx
    have h0 : Nat.find (hex x) = 0 := (Nat.find_eq_zero (hex x)).2 fun _ => by rw [hψ0]; exact hx
    simp only [h0, hψ0]

/-- Bounded subsets restrict (the two modules agree `m_A`-a.e., via
`withDensity_eq_iff_of_sigmaFinite`). -/
theorem isBoundedSubset_restrict {μ : Measure X} [IsFiniteMeasure μ] {R K : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) {A : Set X} (hA : MeasurableSet A) (hμA : μ A ≠ 0)
    (hK : IsBoundedSubset μ R K) :
    IsBoundedSubset (restrictMeasure μ A) (restrictRel R A) (K ∩ A ×ˢ A) := by
  have hRA := isDiscreteMeasured_restrict hR hA
  haveI := isProbabilityMeasure_restrictMeasure (μ := μ) hμA
  have hS : MeasurableSet (A ×ˢ A) := hA.prod hA
  set c : ℝ≥0∞ := (μ A)⁻¹ with hcdef
  set m := relMeasure μ R with hmdef
  set mA := relMeasure (restrictMeasure μ A) (restrictRel R A) with hmAdef
  -- `m_A = c • m|_{A × A}`
  have hmA : mA = c • m.restrict (A ×ˢ A) := by
    ext E hE
    rw [Measure.smul_apply, Measure.restrict_apply hE, smul_eq_mul,
      ← relMeasure_restrict_eq hR hA (hE.inter hS) inter_subset_right,
      CFWPlan.Main.relMeasure_apply hRA.measurableSet hRA.countable_classes hE,
      CFWPlan.Main.relMeasure_apply hRA.measurableSet hRA.countable_classes (hE.inter hS)]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrictMeasure_mem (μ := μ) hA] with x hx
    congr 3
    ext y
    simp only [mem_ofPred_eq, mem_inter_iff, mem_prod]
    constructor
    · rintro ⟨hE', hxy⟩
      refine ⟨⟨hE', hx, ?_⟩, hxy⟩
      rcases hxy with ⟨-, -, hy⟩ | hxy
      · exact hy
      · have hxy' : x = y := hxy
        exact hxy' ▸ hx
    · rintro ⟨⟨hE', -⟩, hxy⟩
      exact ⟨hE', hxy⟩
  have hmAswap : mA.map Prod.swap = c • (m.map Prod.swap).restrict (A ×ˢ A) := by
    rw [hmA, Measure.map_smul, Measure.restrict_map measurable_swap hS, preimage_swap_prod]
  -- the two modules agree `m_A`-a.e.
  have hδ : Measurable (module μ R) := Measure.measurable_rnDeriv _ _
  have hδA : Measurable (module (restrictMeasure μ A) (restrictRel R A)) :=
    Measure.measurable_rnDeriv _ _
  haveI : SigmaFinite mA := CFWPlan.Main.sigmaFinite_relMeasure hRA
  have hwd : mA.withDensity (fun p => (module μ R p)⁻¹) =
      mA.withDensity (fun p => (module (restrictMeasure μ A) (restrictRel R A) p)⁻¹) := by
    rw [← CFWPlan.Main.relMeasure_swap_eq_withDensity hRA, hmAswap,
      CFWPlan.Main.relMeasure_swap_eq_withDensity hR, hmA, withDensity_smul_measure,
      restrict_withDensity hS]
  have hae := (withDensity_eq_iff_of_sigmaFinite hδ.inv.aemeasurable
    hδA.inv.aemeasurable).1 hwd
  refine ⟨hK.measurableSet.inter hS, fun p hp => Or.inl ⟨hK.subset hp.1, hp.2⟩, ?_, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hK.bdd_snd
    exact ⟨k, fun x => (encard_le_encard fun y hy => hy.1).trans (hk x)⟩
  · obtain ⟨k, hk⟩ := hK.bdd_fst
    exact ⟨k, fun y => (encard_le_encard fun x hx => hx.1).trans (hk y)⟩
  · obtain ⟨c₀, hc₀, hK'⟩ := hK.bdd_module
    refine ⟨c₀, hc₀, ?_⟩
    have hK'' : ∀ᵐ p ∂mA, p ∈ K → (c₀ : ℝ≥0∞) ≤ module μ R p ∧ module μ R p ≤ (c₀ : ℝ≥0∞)⁻¹ := by
      rw [hmA]
      exact Measure.ae_smul_measure (ae_restrict_of_ae hK') c
    filter_upwards [hK'', hae] with p hp hpe
    intro hpK
    have he : module (restrictMeasure μ A) (restrictRel R A) p = module μ R p := by
      have := congrArg (·⁻¹) hpe
      simp only [Pi.inv_apply, inv_inv] at this
      exact this.symm
    rw [he]
    exact hp hpK.1

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
/-- **"As `R_A` is amenable"** (CFW p. 443): `P_A f = P (1_A(y) f(y, ρ x))` with the retraction
`ρ`; a partial transformation of `R_A` restricted to `A` is one of `R`. -/
theorem isAmenableRel_restrict {μ : Measure X} [IsFiniteMeasure μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (hamen : Monod.IsAmenableRel μ R) {A : Set X}
    (hA : MeasurableSet A) (hμA : μ A ≠ 0) :
    Monod.IsAmenableRel (restrictMeasure μ A) (restrictRel R A) := by
  classical
  obtain ⟨P, hP⟩ := hamen
  obtain ⟨ρ, hρm, hρ, hρA⟩ := exists_measurable_retraction hR hA
  have hRe := hR.equivalence
  set tl : (X × X → ℝ) → X × X → ℝ := fun f p => A.indicator 1 p.1 * f (p.1, ρ p.2) with htl
  have hkey : ∀ y x, (y, x) ∈ R → y ∈ A → (y, ρ x) ∈ restrictRel R A := by
    intro y x hyx hy
    have hx : x ∈ saturation R A := ⟨y, hy, hRe.symm hyx⟩
    obtain ⟨hρx, hxρ⟩ := hρ x hx
    exact Or.inl ⟨hRe.trans hyx hxρ, hy, hρx⟩
  have hbdd : ∀ f, Monod.IsBddMeasOn (restrictRel R A) f → Monod.IsBddMeasOn R (tl f) := by
    rintro f ⟨hfm, C, hC⟩
    refine ⟨?_, max C 0, ?_⟩
    · exact ((measurable_one.indicator hA).comp measurable_fst).mul
        (hfm.comp (measurable_fst.prodMk (hρm.comp measurable_snd)))
    · rintro ⟨y, x⟩ hyx
      by_cases hy : y ∈ A
      · simp only [htl, indicator_of_mem hy, Pi.one_apply, one_mul]
        exact (hC _ (hkey y x hyx hy)).trans (le_max_left _ _)
      · simp only [htl, indicator_of_notMem hy, zero_mul, abs_zero]
        exact le_max_right _ _
  have hAe : ∀ᵐ x ∂(restrictMeasure μ A), x ∈ A := ae_restrictMeasure_mem hA
  have hac : restrictMeasure μ A ≪ μ :=
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).smul_left _
  refine ⟨fun f => P (tl f), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro f hf
    exact (hP.aemeasurable _ (hbdd f hf)).mono_ac hac
  · intro f g hf hg hnull
    refine hac.ae_le (hP.congr _ _ (hbdd f hf) (hbdd g hg) ?_)
    unfold Monod.RelNull at hnull ⊢
    rw [restrictMeasure_apply hA] at hnull
    have hμA' : (μ A)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (measure_ne_top μ A)
    have h1 := (mul_eq_zero.1 hnull).resolve_left hμA'
    refine measure_mono_null ?_ h1
    rintro y ⟨⟨y', x⟩, ⟨hne, hyx⟩, rfl⟩
    by_cases hy : y' ∈ A
    · refine ⟨⟨(y', ρ x), ⟨?_, hkey y' x hyx hy⟩, rfl⟩, hy⟩
      intro heq
      apply hne
      simp only [htl, indicator_of_mem hy, Pi.one_apply, one_mul]
      exact heq
    · exfalso
      apply hne
      simp only [htl, indicator_of_notMem hy, zero_mul]
  · intro f g hf hg
    have h : tl (f + g) = tl f + tl g := by
      funext p
      simp only [htl, Pi.add_apply, mul_add]
    show P (tl (f + g)) =ᵐ[restrictMeasure μ A] P (tl f) + P (tl g)
    rw [h]
    exact hac.ae_le (hP.add _ _ (hbdd f hf) (hbdd g hg))
  · intro c f hf
    have h : tl (c • f) = c • tl f := by
      funext p
      simp only [htl, Pi.smul_apply, smul_eq_mul]
      ring
    show P (tl (c • f)) =ᵐ[restrictMeasure μ A] c • P (tl f)
    rw [h]
    exact hac.ae_le (hP.smul c _ (hbdd f hf))
  · intro f hf hnn
    refine hac.ae_le (hP.nonneg _ (hbdd f hf) ?_)
    rintro ⟨y, x⟩ hyx
    by_cases hy : y ∈ A
    · simp only [htl, indicator_of_mem hy, Pi.one_apply, one_mul]
      exact hnn _ (hkey y x hyx hy)
    · simp only [htl, indicator_of_notMem hy, zero_mul, le_refl]
  · -- `P (1_A ∘ fst) = 1_A`, from the invariance under `id_A`
    set ι := ptId (fun x => hRe.refl x) A hA with hιdef
    have h1 : tl 1 = ι.shiftRel 1 := by
      rw [CFWPlan.Main.shiftRel_eq]
      funext p
      by_cases hp : p.1 ∈ A
      · simp only [htl, indicator_of_mem hp, Pi.one_apply, one_mul]
        rw [if_pos (show p.1 ∈ ι.cod from hp)]
      · simp only [htl, indicator_of_notMem hp, zero_mul]
        rw [if_neg (show p.1 ∉ ι.cod from hp)]
    have hb1 : Monod.IsBddMeasOn R (1 : X × X → ℝ) := ⟨measurable_const, 1, fun _ _ => by simp⟩
    have h2 := hP.invariant ι 1 hb1
    rw [CFWPlan.Main.shiftBase_eq] at h2
    show P (tl 1) =ᵐ[restrictMeasure μ A] 1
    rw [h1]
    filter_upwards [hac.ae_le h2, hac.ae_le hP.one, hAe] with x hx hx1 hxA
    rw [hx, if_pos (show x ∈ ι.cod from hxA)]
    have hinv : ptInv ι x = x := by
      unfold ptInv
      rw [dif_pos (show x ∈ ι.cod from hxA)]
      rfl
    rw [hinv]
    exact hx1
  · intro ψ f hf
    have hψsp := CFWPlan.Main.ptFun_spec ψ
    have hψm := CFWPlan.Main.measurable_ptFun ψ
    -- `ψ` maps `dom ψ ∩ A` into `A`, along `R`
    have hdomA : ∀ x ∈ ψ.dom, x ∈ A → ptFun ψ x ∈ A ∧ (x, ptFun ψ x) ∈ R := by
      intro x hx hxA
      rcases (hψsp.1 x hx).2.2 with ⟨h, -, h'⟩ | h
      · exact ⟨h', h⟩
      · have h' : x = ptFun ψ x := h
        rw [← h']
        exact ⟨hxA, hRe.refl x⟩
    have hcodA : ∀ y ∈ ψ.cod, y ∈ A → ptInv ψ y ∈ A := by
      intro y hy hyA
      have h1 := hψsp.2.1 y hy
      have h2 := (hψsp.1 _ h1.1).2.2
      rw [h1.2] at h2
      rcases h2 with ⟨-, h, -⟩ | h
      · exact h
      · have h' : ptInv ψ y = y := h
        rw [h']
        exact hyA
    obtain ⟨ψ', hψ'dom, hψ'cod, hψ'fun⟩ := CFWPlan.Main.exists_pt_of_injOn (R := R)
      (ψ.measurableSet_dom.inter hA) hψm.1 (hψsp.2.2.mono inter_subset_left)
      (fun x hx => (hdomA x hx.1 hx.2).2)
    have hcod' : ψ'.cod = ψ.cod ∩ A := by
      rw [hψ'cod]
      ext y
      constructor
      · rintro ⟨x, ⟨hx, hxA⟩, rfl⟩
        exact ⟨(hψsp.1 x hx).1, (hdomA x hx hxA).1⟩
      · rintro ⟨hy, hyA⟩
        exact ⟨ptInv ψ y, ⟨(hψsp.2.1 y hy).1, hcodA y hy hyA⟩, (hψsp.2.1 y hy).2⟩
    have hinv' : ∀ y ∈ ψ'.cod, ptInv ψ' y = ptInv ψ y := by
      intro y hy
      have hψ'sp := CFWPlan.Main.ptFun_spec ψ'
      obtain ⟨h1, h2⟩ := hψ'sp.2.1 y hy
      rw [hψ'dom] at h1
      have h3 : ptFun ψ (ptInv ψ' y) = y := by rw [← hψ'fun _ h1]; exact h2
      have hy' : y ∈ ψ.cod := (hcod' ▸ hy).1
      exact hψsp.2.2 h1.1 (hψsp.2.1 y hy').1 (h3.trans (hψsp.2.1 y hy').2.symm)
    have heq : tl (ψ.shiftRel f) = ψ'.shiftRel (tl f) := by
      rw [CFWPlan.Main.shiftRel_eq, CFWPlan.Main.shiftRel_eq]
      funext p
      obtain ⟨y, x⟩ := p
      by_cases hyA : y ∈ A
      · by_cases hy : y ∈ ψ.cod
        · have hy' : y ∈ ψ'.cod := hcod' ▸ ⟨hy, hyA⟩
          simp only [htl, indicator_of_mem hyA, Pi.one_apply, one_mul]
          rw [if_pos hy, if_pos hy', hinv' y hy',
            indicator_of_mem (hcodA y hy hyA), Pi.one_apply, one_mul]
        · have hy' : y ∉ ψ'.cod := fun h => hy (hcod' ▸ h).1
          simp only [htl, indicator_of_mem hyA, Pi.one_apply, one_mul]
          rw [if_neg hy, if_neg hy']
      · have hy' : y ∉ ψ'.cod := fun h => hyA (hcod' ▸ h).2
        simp only [htl, indicator_of_notMem hyA, zero_mul]
        rw [if_neg hy']
    show P (tl (ψ.shiftRel f)) =ᵐ[restrictMeasure μ A] ψ.shiftBase (P (tl f))
    rw [heq]
    have h2 := hP.invariant ψ' (tl f) (hbdd f hf)
    filter_upwards [hac.ae_le h2, hAe] with y hy hyA
    rw [hy, CFWPlan.Main.shiftBase_eq, CFWPlan.Main.shiftBase_eq]
    by_cases hyc : y ∈ ψ.cod
    · have hy' : y ∈ ψ'.cod := hcod' ▸ ⟨hyc, hyA⟩
      simp only
      rw [if_pos hy', if_pos hyc, hinv' y hy']
    · have hy' : y ∉ ψ'.cod := fun h => hyc (hcod' ▸ h).1
      simp only
      rw [if_neg hy', if_neg hyc]

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
/-- **The Lemma 9 step** (CFW p. 443): Lemma 8 (`lemma8`) for `(μ_A, R_A, H ∩ A × A)`, cut to `A`. -/
theorem exists_fsr_in {μ : Measure X} [IsProbabilityMeasure μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (hamen : Monod.IsAmenableRel μ R) {H : Set (X × X)}
    (hH : IsBoundedSubset μ R H) {A : Set X} (hA : MeasurableSet A) (hμA : μ A ≠ 0) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ T₁, IsFiniteSubrelation R T₁ ∧ unitSpace T₁ ⊆ A ∧
      relMeasure μ R {γ ∈ H ∩ A ×ˢ A | (γ.2 ∈ unitSpace T₁ ∨ γ.1 ∈ unitSpace T₁) ∧ γ ∉ T₁} <
        ENNReal.ofReal ε * μ (unitSpace T₁) ∧ μ (unitSpace T₁) ≠ 0 := by
  haveI := isProbabilityMeasure_restrictMeasure (μ := μ) hμA
  have hRA := isDiscreteMeasured_restrict hR hA
  obtain ⟨T, hT, hlt, hne⟩ := ConnesFeldmanWeiss.exists_finiteSubrelation_boundary_lt _ _ hRA (isAmenableRel_restrict hR hamen hA hμA)
    _ (isBoundedSubset_restrict hR hA hμA hH) _ hε
  obtain ⟨hT₁, hU₁⟩ := IsFiniteSubrelation.inter_restrict (fun x => hR.equivalence.refl x) hA hT
  have hS : MeasurableSet (A ×ˢ A) := hA.prod hA
  have hUm : MeasurableSet (unitSpace T) :=
    (measurable_id.prodMk measurable_id) hT.measurableSet
  refine ⟨T ∩ A ×ˢ A, hT₁, hU₁ ▸ inter_subset_right, ?_, ?_⟩
  · set B := {γ ∈ H ∩ A ×ˢ A | (γ.2 ∈ unitSpace T ∨ γ.1 ∈ unitSpace T) ∧ γ ∉ T} with hBdef
    have hBeq : {γ ∈ H ∩ A ×ˢ A | (γ.2 ∈ unitSpace (T ∩ A ×ˢ A) ∨
        γ.1 ∈ unitSpace (T ∩ A ×ˢ A)) ∧ γ ∉ T ∩ A ×ˢ A} = B := by
      rw [hU₁]
      ext γ
      simp only [hBdef, mem_ofPred_eq, mem_inter_iff, mem_prod]
      constructor
      · rintro ⟨⟨hH', h1, h2⟩, h3, h4⟩
        refine ⟨⟨hH', h1, h2⟩, ?_, fun h => h4 ⟨h, h1, h2⟩⟩
        rcases h3 with h | h
        · exact Or.inl h.1
        · exact Or.inr h.1
      · rintro ⟨⟨hH', h1, h2⟩, h3, h4⟩
        refine ⟨⟨hH', h1, h2⟩, ?_, fun h => h4 h.1⟩
        rcases h3 with h | h
        · exact Or.inl ⟨h, h2⟩
        · exact Or.inr ⟨h, h1⟩
    have hBm : MeasurableSet B :=
      (hH.measurableSet.inter hS).inter (((measurable_snd hUm).union (measurable_fst hUm)).inter
        hT.measurableSet.compl)
    have hBS : B ⊆ A ×ˢ A := fun γ hγ => hγ.1.2
    rw [hBeq, hU₁]
    rw [relMeasure_restrict_eq hR hA hBm hBS, restrictMeasure_apply hA] at hlt
    have hc0 : (μ A)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 (measure_ne_top μ A)
    have hct : (μ A)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hμA
    rw [mul_left_comm] at hlt
    exact (ENNReal.mul_lt_mul_iff_right hc0 hct).1 hlt
  · rw [hU₁]
    rw [restrictMeasure_apply hA] at hne
    exact right_ne_zero_of_mul hne

end CFWPlan.Main.P4
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias exists_fsr_in := CFWPlan.Main.P4.exists_fsr_in

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
/-- The unit space of a measurable set is measurable (copied from P2). -/
theorem measurableSet_unitSpace {T : Set (X × X)} (hT : MeasurableSet T) :
    MeasurableSet (unitSpace T) :=
  (measurable_id.prodMk measurable_id) hT

/-- `m` does not see pairs whose first point lies in a `μ`-null set. -/
theorem relMeasure_eq_zero_of_fst {μ : Measure X} {R : Set (X × X)} (hR : IsDiscreteMeasured μ R)
    {A : Set X} (hA0 : μ A = 0) {E : Set (X × X)} (hE : ∀ γ ∈ E, γ.1 ∈ A) :
    relMeasure μ R E = 0 := by
  refine measure_mono_null (t := toMeasurable μ A ×ˢ univ)
    (fun γ hγ => ⟨subset_toMeasurable μ A (hE γ hγ), trivial⟩) ?_
  rw [CFWPlan.Main.relMeasure_apply hR.measurableSet hR.countable_classes
    ((measurableSet_toMeasurable μ A).prod MeasurableSet.univ)]
  have h : ∀ᵐ x ∂μ, x ∉ toMeasurable μ A := by
    rw [← measure_eq_zero_iff_ae_notMem, measure_toMeasurable]
    exact hA0
  have h0 : (fun x => (({y | (x, y) ∈ (toMeasurable μ A ×ˢ univ) ∩ R}.encard : ℕ∞) : ℝ≥0∞))
      =ᵐ[μ] 0 := by
    filter_upwards [h] with x hx
    have : {y | (x, y) ∈ (toMeasurable μ A ×ˢ univ) ∩ R} = ∅ := by
      ext y
      simp [hx]
    rw [this]
    simp
  rw [lintegral_congr_ae h0]
  simp

/-! ## §12. Lemma 9 (CFW pp. 442–444) -/
theorem exists_eq_one_of_exhaustion {C : Type*} (le : C → C → Prop) (v : C → ℝ≥0∞) (c₀ : C)
    (hrefl : ∀ a, le a a) (htrans : ∀ a b c, le a b → le b c → le a c)
    (hmono : ∀ a b, le a b → v a ≤ v b) (hle1 : ∀ a, v a ≤ 1)
    (hchain : ∀ c : ℕ → C, (∀ n, le (c n) (c (n + 1))) →
      ∃ b, (∀ n, le (c n) b) ∧ v b ≤ ⨆ n, v (c n))
    (hstep : ∀ a, v a < 1 → ∃ b, le a b ∧ v a < v b) : ∃ a, le c₀ a ∧ v a = 1 := by
  classical
  let s : C → ℝ≥0∞ := fun a => ⨆ b : {b // le a b}, v b
  have hs_ne_top : ∀ a, s a ≠ ∞ := fun a =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun b => hle1 b)
  have hgood : ∀ (a : C) (n : ℕ), ∃ b, le a b ∧ s a < v b + (n : ℝ≥0∞)⁻¹ := by
    intro a n
    haveI : Nonempty {b // le a b} := ⟨⟨a, hrefl a⟩⟩
    have h1 : s a < s a + (n : ℝ≥0∞)⁻¹ :=
      ENNReal.lt_add_right (hs_ne_top a) (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n))
    have h2 : s a + (n : ℝ≥0∞)⁻¹ = ⨆ b : {b // le a b}, (v b + (n : ℝ≥0∞)⁻¹) :=
      ENNReal.iSup_add _
    rw [h2] at h1
    obtain ⟨b, hb⟩ := lt_iSup_iff.1 h1
    exact ⟨b.1, b.2, hb⟩
  choose next hnext_le hnext_lt using hgood
  let c : ℕ → C := fun n => Nat.rec c₀ (fun k ck => next ck k) n
  have hcs : ∀ n, c (n + 1) = next (c n) n := fun n => rfl
  obtain ⟨b, hb, -⟩ := hchain c (fun n => by rw [hcs]; exact hnext_le _ _)
  refine ⟨b, hb 0, le_antisymm (hle1 b) ?_⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨b', hbb', hvb'⟩ := hstep b hlt
  have key : ∀ n : ℕ, v b' ≤ v b + (n : ℝ≥0∞)⁻¹ := by
    intro n
    have h1 : v b' ≤ s (c n) :=
      le_iSup (fun x : {x // le (c n) x} => v x) ⟨b', htrans _ _ _ (hb n) hbb'⟩
    have h2 := hnext_lt (c n) n
    rw [← hcs] at h2
    calc v b' ≤ s (c n) := h1
      _ ≤ v (c (n + 1)) + (n : ℝ≥0∞)⁻¹ := h2.le
      _ ≤ v b + (n : ℝ≥0∞)⁻¹ := add_le_add (hmono _ _ (hb (n + 1))) le_rfl
  have : v b' ≤ v b := by
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (a := (ε : ℝ≥0∞)) (by exact_mod_cast hε.ne')
    exact (key n).trans (add_le_add le_rfl hn.le)
  exact absurd hvb' (not_lt.2 this)

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

/-- `T'` is an extension of `T` (CFW p. 435). -/
def IsExtension (T T' : Set (X × X)) : Prop :=
  T ⊆ T' ∧ ∀ x y, (x, y) ∈ T' → (x ∈ unitSpace T ∨ y ∈ unitSpace T) → (x, y) ∈ T

/-- The class `𝒞` of CFW p. 442: conditions (1) and (2) on a pair `(T, H)`. -/
structure L9Good (μ : Measure X) (R K : Set (X × X)) (ε : ℝ≥0∞) (TH : Set (X × X) × Set (X × X)) :
    Prop where
  fsr : IsFiniteSubrelation R TH.1
  meas : MeasurableSet TH.2
  sub : TH.2 ⊆ K
  small : relMeasure μ R (K \ TH.2) ≤ ε * μ (unitSpace TH.1)
  closed : ∀ γ ∈ TH.2, (γ.2 ∈ unitSpace TH.1 ∨ γ.1 ∈ unitSpace TH.1) → γ ∈ TH.1

/-- The order on `𝒞` of CFW p. 443: (a) extension, (b) `H' ⊆ H`, `m(H \ H') ≤ ε μ(T'⁽⁰⁾ \ T⁽⁰⁾)`. -/
def L9Le (μ : Measure X) (R : Set (X × X)) (ε : ℝ≥0∞) (a b : Set (X × X) × Set (X × X)) : Prop :=
  IsExtension a.1 b.1 ∧ b.2 ⊆ a.2 ∧ relMeasure μ R (a.2 \ b.2) ≤ ε * μ (unitSpace b.1 \ unitSpace a.1)

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
theorem isExtension_refl (T : Set (X × X)) : IsExtension T T :=
  ⟨subset_rfl, fun _ _ h _ => h⟩

theorem isExtension_unitSpace_subset {T T' : Set (X × X)} (h : IsExtension T T') :
    unitSpace T ⊆ unitSpace T' := fun _ hx => h.1 hx

theorem isExtension_trans {T T' T'' : Set (X × X)} (h₁ : IsExtension T T')
    (h₂ : IsExtension T' T'') : IsExtension T T'' := by
  refine ⟨h₁.1.trans h₂.1, fun x y hxy hx => h₁.2 x y (h₂.2 x y hxy ?_) hx⟩
  rcases hx with hx | hx
  · exact Or.inl (isExtension_unitSpace_subset h₁ hx)
  · exact Or.inr (isExtension_unitSpace_subset h₁ hx)

theorem IsFiniteSubrelation.iUnion_of_extension {R : Set (X × X)} {T : ℕ → Set (X × X)}
    (hT : ∀ n, IsFiniteSubrelation R (T n)) (hext : ∀ n, IsExtension (T n) (T (n + 1))) :
    IsFiniteSubrelation R (⋃ n, T n) ∧ ∀ n, IsExtension (T n) (⋃ n, T n) := by
  have hmono : Monotone T := monotone_nat_of_le_succ fun n => (hext n).1
  have hext' : ∀ n m, n ≤ m → IsExtension (T n) (T m) := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact isExtension_refl _
    | succ m hnm ih => exact isExtension_trans ih (hext m)
  have hExt : ∀ n, IsExtension (T n) (⋃ n, T n) := by
    intro n
    refine ⟨subset_iUnion T n, fun x y hxy hx => ?_⟩
    obtain ⟨m, hm⟩ := mem_iUnion.1 hxy
    rcases le_total m n with h | h
    · exact hmono h hm
    · exact (hext' n m h).2 x y hm hx
  refine ⟨⟨MeasurableSet.iUnion fun n => (hT n).measurableSet,
    iUnion_subset fun n => (hT n).subset, ?_, ?_, ?_, ?_⟩, hExt⟩
  · intro p hp
    obtain ⟨n, hn⟩ := mem_iUnion.1 hp
    obtain ⟨h1, h2⟩ := (hT n).mem_unitSpace p hn
    exact ⟨mem_iUnion.2 ⟨n, h1⟩, mem_iUnion.2 ⟨n, h2⟩⟩
  · intro x y hxy
    obtain ⟨n, hn⟩ := mem_iUnion.1 hxy
    exact mem_iUnion.2 ⟨n, (hT n).symm x y hn⟩
  · intro x y z hxy hyz
    obtain ⟨n, hn⟩ := mem_iUnion.1 hxy
    obtain ⟨m, hm⟩ := mem_iUnion.1 hyz
    exact mem_iUnion.2 ⟨max n m, (hT _).trans x y z (hmono (le_max_left n m) hn)
      (hmono (le_max_right n m) hm)⟩
  · intro x
    by_cases hx : ∃ n, x ∈ unitSpace (T n)
    · obtain ⟨n, hn⟩ := hx
      exact ((hT n).finite_classes x).subset fun y hy => (hExt n).2 x y hy (Or.inl hn)
    · push Not at hx
      refine Set.finite_empty.subset fun y hy => ?_
      obtain ⟨n, hn⟩ := mem_iUnion.1 hy
      exact hx n ((hT n).mem_unitSpace _ hn).1

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
theorem l9Le_refl (μ : Measure X) (R : Set (X × X)) (ε : ℝ≥0∞)
    (a : Set (X × X) × Set (X × X)) : L9Le μ R ε a a :=
  ⟨isExtension_refl _, subset_rfl, by simp⟩

theorem l9Le_trans {μ : Measure X} {R K : Set (X × X)} {ε : ℝ≥0∞}
    {a b c : Set (X × X) × Set (X × X)} (ha : L9Good μ R K ε a) (hb : L9Good μ R K ε b)
    (hc : L9Good μ R K ε c) (hab : L9Le μ R ε a b) (hbc : L9Le μ R ε b c) : L9Le μ R ε a c := by
  refine ⟨isExtension_trans hab.1 hbc.1, hbc.2.1.trans hab.2.1, ?_⟩
  have hUa := measurableSet_unitSpace ha.fsr.measurableSet
  have hUb := measurableSet_unitSpace hb.fsr.measurableSet
  have hab' := isExtension_unitSpace_subset hab.1
  have hbc' := isExtension_unitSpace_subset hbc.1
  have hsplit : unitSpace c.1 \ unitSpace a.1 =
      (unitSpace b.1 \ unitSpace a.1) ∪ (unitSpace c.1 \ unitSpace b.1) := by
    ext x
    constructor
    · rintro ⟨hc, ha⟩
      by_cases hb : x ∈ unitSpace b.1
      · exact Or.inl ⟨hb, ha⟩
      · exact Or.inr ⟨hc, hb⟩
    · rintro (⟨hb, ha⟩ | ⟨hc, hb⟩)
      · exact ⟨hbc' hb, ha⟩
      · exact ⟨hc, fun ha => hb (hab' ha)⟩
  have hdisj : Disjoint (unitSpace b.1 \ unitSpace a.1) (unitSpace c.1 \ unitSpace b.1) :=
    disjoint_left.2 fun x hx hx' => hx'.2 hx.1
  calc relMeasure μ R (a.2 \ c.2)
      ≤ relMeasure μ R ((a.2 \ b.2) ∪ (b.2 \ c.2)) := by
        refine measure_mono fun γ hγ => ?_
        by_cases hγb : γ ∈ b.2
        · exact Or.inr ⟨hγb, hγ.2⟩
        · exact Or.inl ⟨hγ.1, hγb⟩
    _ ≤ relMeasure μ R (a.2 \ b.2) + relMeasure μ R (b.2 \ c.2) := measure_union_le _ _
    _ ≤ ε * μ (unitSpace b.1 \ unitSpace a.1) + ε * μ (unitSpace c.1 \ unitSpace b.1) :=
        add_le_add hab.2.2 hbc.2.2
    _ = ε * μ (unitSpace c.1 \ unitSpace a.1) := by
        rw [hsplit, measure_union hdisj (measurableSet_unitSpace hc.fsr.measurableSet |>.diff hUb),
          mul_add]

theorem l9_chain {μ : Measure X} [IsProbabilityMeasure μ] {R K : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (hK : IsBoundedSubset μ R K) {ε : ℝ≥0∞}
    (c : ℕ → Set (X × X) × Set (X × X)) (hc : ∀ n, L9Good μ R K ε (c n))
    (hle : ∀ n, L9Le μ R ε (c n) (c (n + 1))) :
    ∃ b, L9Good μ R K ε b ∧ (∀ n, L9Le μ R ε (c n) b) ∧
      μ (unitSpace b.1) ≤ ⨆ n, μ (unitSpace (c n).1) := by
  obtain ⟨hfsr, hext⟩ :=
    IsFiniteSubrelation.iUnion_of_extension (fun n => (hc n).fsr) (fun n => (hle n).1)
  have hU : unitSpace (⋃ n, (c n).1) = ⋃ n, unitSpace (c n).1 := by
    ext x
    simp only [unitSpace, mem_ofPred_eq, mem_iUnion]
  have hHanti : Antitone fun n => (c n).2 := antitone_nat_of_succ_le fun n => (hle n).2.1
  have hUmono : Monotone fun n => unitSpace (c n).1 :=
    monotone_nat_of_le_succ fun n => isExtension_unitSpace_subset (hle n).1
  have hle' : ∀ n m, n ≤ m → L9Le μ R ε (c n) (c m) := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact l9Le_refl μ R ε _
    | succ m hnm ih => exact l9Le_trans (hc n) (hc m) (hc (m + 1)) ih (hle m)
  have hTU : ∀ n, unitSpace (c n).1 ⊆ unitSpace (⋃ n, (c n).1) :=
    fun n => isExtension_unitSpace_subset (hext n)
  refine ⟨(⋃ n, (c n).1, ⋂ n, (c n).2), ⟨hfsr, MeasurableSet.iInter fun n => (hc n).meas,
    (iInter_subset _ 0).trans (hc 0).sub, ?_, ?_⟩, fun n => ⟨hext n, iInter_subset _ n, ?_⟩, ?_⟩
  · show relMeasure μ R (K \ ⋂ n, (c n).2) ≤ ε * μ (unitSpace (⋃ n, (c n).1))
    rw [sdiff_iInter, Monotone.measure_iUnion (fun n m h => sdiff_subset_sdiff_right (hHanti h))]
    exact iSup_le fun n => (hc n).small.trans (by gcongr; exact hTU n)
  · rintro γ hγ hγT
    rw [hU] at hγT
    have hγn : ∀ n, γ ∈ (c n).2 := mem_iInter.1 hγ
    rcases hγT with h | h
    · obtain ⟨n, hn⟩ := mem_iUnion.1 h
      exact mem_iUnion.2 ⟨n, (hc n).closed γ (hγn n) (Or.inl hn)⟩
    · obtain ⟨n, hn⟩ := mem_iUnion.1 h
      exact mem_iUnion.2 ⟨n, (hc n).closed γ (hγn n) (Or.inr hn)⟩
  · show relMeasure μ R ((c n).2 \ ⋂ n, (c n).2) ≤
      ε * μ (unitSpace (⋃ n, (c n).1) \ unitSpace (c n).1)
    rw [sdiff_iInter, Monotone.measure_iUnion (fun m m' h => sdiff_subset_sdiff_right (hHanti h))]
    refine iSup_le fun m => ?_
    rcases le_total m n with h | h
    · rw [sdiff_eq_empty.2 (hHanti h), measure_empty]
      exact zero_le
    · exact (hle' n m h).2.2.trans
        (by gcongr; exact hTU m)
  · show μ (unitSpace (⋃ n, (c n).1)) ≤ ⨆ n, μ (unitSpace (c n).1)
    rw [hU, Monotone.measure_iUnion hUmono]

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
theorem l9_step {μ : Measure X} [IsProbabilityMeasure μ] {R K : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (hamen : Monod.IsAmenableRel μ R) (hK : IsBoundedSubset μ R K)
    {ε : ℝ} (hε : 0 < ε) (a : Set (X × X) × Set (X × X)) (ha : L9Good μ R K (ENNReal.ofReal ε) a)
    (hlt : μ (unitSpace a.1) < 1) :
    ∃ b, L9Good μ R K (ENNReal.ofReal ε) b ∧ L9Le μ R (ENNReal.ofReal ε) a b ∧
      μ (unitSpace a.1) < μ (unitSpace b.1) := by
  obtain ⟨T, H⟩ := a
  simp only at ha hlt ⊢
  have hUm : MeasurableSet (unitSpace T) := measurableSet_unitSpace ha.fsr.measurableSet
  have hA : MeasurableSet (unitSpace T)ᶜ := hUm.compl
  have hμA : μ (unitSpace T)ᶜ ≠ 0 := by
    rw [measure_compl hUm (measure_ne_top _ _), measure_univ]
    exact (tsub_pos_of_lt hlt).ne'
  have hH : IsBoundedSubset μ R H := CFWPlan.Main.IsBoundedSubset.mono' hK ha.meas ha.sub
  obtain ⟨T₁, hT₁, hT₁A, hD, hT₁0⟩ := CFWPlan.Main.exists_fsr_in hR hamen hH hA hμA hε
  set U := unitSpace T with hUdef
  set U₁ := unitSpace T₁ with hU₁def
  set D := {γ ∈ H ∩ Uᶜ ×ˢ Uᶜ | (γ.2 ∈ U₁ ∨ γ.1 ∈ U₁) ∧ γ ∉ T₁} with hDdef
  have hU₁m : MeasurableSet U₁ := measurableSet_unitSpace hT₁.measurableSet
  have hDm : MeasurableSet D := by
    refine (ha.meas.inter (hA.prod hA)).inter ?_
    exact ((measurable_snd hU₁m).union (measurable_fst hU₁m)).inter hT₁.measurableSet.compl
  have hdisj : Disjoint U U₁ := disjoint_left.2 fun x hx hx₁ => hT₁A hx₁ hx
  have hU' : unitSpace (T ∪ T₁) = U ∪ U₁ := Set.ext fun _ => Iff.rfl
  have hfsr' : IsFiniteSubrelation R (T ∪ T₁) := by
    refine ⟨ha.fsr.measurableSet.union hT₁.measurableSet,
      union_subset ha.fsr.subset hT₁.subset, ?_, ?_, ?_, ?_⟩
    · rintro p (hp | hp)
      · exact ⟨Or.inl (ha.fsr.mem_unitSpace p hp).1, Or.inl (ha.fsr.mem_unitSpace p hp).2⟩
      · exact ⟨Or.inr (hT₁.mem_unitSpace p hp).1, Or.inr (hT₁.mem_unitSpace p hp).2⟩
    · rintro x y (h | h)
      · exact Or.inl (ha.fsr.symm x y h)
      · exact Or.inr (hT₁.symm x y h)
    · rintro x y z (h | h) (h' | h')
      · exact Or.inl (ha.fsr.trans x y z h h')
      · exact absurd (hT₁.mem_unitSpace _ h').1
          (disjoint_left.1 hdisj (ha.fsr.mem_unitSpace _ h).2)
      · exact absurd (hT₁.mem_unitSpace _ h).2
          (disjoint_left.1 hdisj (ha.fsr.mem_unitSpace _ h').1)
      · exact Or.inr (hT₁.trans x y z h h')
    · intro x
      exact ((ha.fsr.finite_classes x).union (hT₁.finite_classes x)).subset fun y hy => hy
  have hext' : IsExtension T (T ∪ T₁) := by
    refine ⟨subset_union_left, fun x y hxy hx => ?_⟩
    rcases hxy with h | h
    · exact h
    · exfalso
      rcases hx with hx | hx
      · exact disjoint_left.1 hdisj hx (hT₁.mem_unitSpace _ h).1
      · exact disjoint_left.1 hdisj hx (hT₁.mem_unitSpace _ h).2
  have hdiff : (U ∪ U₁) \ U = U₁ := by
    ext x
    constructor
    · rintro ⟨hx | hx, hxU⟩
      · exact absurd hx hxU
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, fun hxU => disjoint_left.1 hdisj hxU hx⟩
  have hμU' : μ (U ∪ U₁) = μ U + μ U₁ := measure_union hdisj hU₁m
  refine ⟨(T ∪ T₁, H \ D), ⟨hfsr', ha.meas.diff hDm, sdiff_subset.trans ha.sub, ?_, ?_⟩,
    ⟨hext', sdiff_subset, ?_⟩, ?_⟩
  · show relMeasure μ R (K \ (H \ D)) ≤ ENNReal.ofReal ε * μ (unitSpace (T ∪ T₁))
    rw [hU', hμU', mul_add]
    calc relMeasure μ R (K \ (H \ D)) ≤ relMeasure μ R ((K \ H) ∪ D) := by
          refine measure_mono fun γ hγ => ?_
          by_cases hγH : γ ∈ H
          · exact Or.inr (not_not.1 fun h => hγ.2 ⟨hγH, h⟩)
          · exact Or.inl ⟨hγ.1, hγH⟩
      _ ≤ relMeasure μ R (K \ H) + relMeasure μ R D := measure_union_le _ _
      _ ≤ ENNReal.ofReal ε * μ U + ENNReal.ofReal ε * μ U₁ := add_le_add ha.small hD.le
  · rintro γ ⟨hγH, hγD⟩ hγU
    rw [hU'] at hγU
    by_cases h : γ.2 ∈ U ∨ γ.1 ∈ U
    · exact Or.inl (ha.closed γ hγH h)
    · push Not at h
      have h₁ : γ.2 ∈ U₁ ∨ γ.1 ∈ U₁ := by
        rcases hγU with (h' | h') | (h' | h')
        · exact absurd h' h.1
        · exact Or.inl h'
        · exact absurd h' h.2
        · exact Or.inr h'
      by_contra hγT
      exact hγD ⟨⟨hγH, h.2, h.1⟩, h₁, fun h' => hγT (Or.inr h')⟩
  · show relMeasure μ R (H \ (H \ D)) ≤ ENNReal.ofReal ε * μ (unitSpace (T ∪ T₁) \ U)
    rw [hU', hdiff]
    refine (measure_mono fun γ hγ => ?_).trans hD.le
    exact not_not.1 fun h => hγ.2 ⟨hγ.1, h⟩
  · show μ U < μ (unitSpace (T ∪ T₁))
    rw [hU', hμU']
    exact ENNReal.lt_add_right (measure_ne_top _ _) hT₁0

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
theorem lemma9 {μ : Measure X} [IsProbabilityMeasure μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (hamen : Monod.IsAmenableRel μ R) {K : Set (X × X)}
    (hK : IsBoundedSubset μ R K) {ε : ℝ} (hε : 0 < ε) :
    ∃ T, IsFiniteSubrelation R T ∧ relMeasure μ R (K \ T) < ENNReal.ofReal ε := by
  have hε2 : 0 < ε / 2 := half_pos hε
  let C := {a : Set (X × X) × Set (X × X) // L9Good μ R K (ENNReal.ofReal (ε / 2)) a}
  have hempty : IsFiniteSubrelation R (∅ : Set (X × X)) :=
    ⟨MeasurableSet.empty, empty_subset _, by simp, by simp, by simp, by simp⟩
  have c₀good : L9Good μ R K (ENNReal.ofReal (ε / 2)) (∅, K) :=
    ⟨hempty, hK.measurableSet, subset_rfl, by simp, by simp [unitSpace]⟩
  obtain ⟨⟨⟨T, H⟩, hgood⟩, -, hv⟩ := exists_eq_one_of_exhaustion (C := C)
    (fun a b => L9Le μ R (ENNReal.ofReal (ε / 2)) a.1 b.1) (fun a => μ (unitSpace a.1.1))
    ⟨(∅, K), c₀good⟩ (fun a => l9Le_refl μ R _ a.1)
    (fun a b c hab hbc => l9Le_trans a.2 b.2 c.2 hab hbc)
    (fun a b h => measure_mono (isExtension_unitSpace_subset h.1)) (fun a => prob_le_one)
    (fun c hc => by
      obtain ⟨b, hb, hbn, hbv⟩ := l9_chain hR hK (fun n => (c n).1) (fun n => (c n).2) hc
      exact ⟨⟨b, hb⟩, hbn, hbv⟩)
    (fun a ha => by
      obtain ⟨b, hb, hab, hv⟩ := l9_step hR hamen hK hε2 a.1 a.2 ha
      exact ⟨⟨b, hb⟩, hab, hv⟩)
  simp only at hv
  refine ⟨T, hgood.fsr, ?_⟩
  have hU0 : μ (unitSpace T)ᶜ = 0 :=
    (prob_compl_eq_zero_iff (measurableSet_unitSpace hgood.fsr.measurableSet)).2 hv
  have h1 : relMeasure μ R (H \ T) = 0 :=
    relMeasure_eq_zero_of_fst hR hU0 fun γ hγ hγU => hγ.2 (hgood.closed γ hγ.1 (Or.inr hγU))
  calc relMeasure μ R (K \ T) ≤ relMeasure μ R ((K \ H) ∪ (H \ T)) := by
        refine measure_mono fun γ hγ => ?_
        by_cases hH : γ ∈ H
        · exact Or.inr ⟨hH, hγ.2⟩
        · exact Or.inl ⟨hγ.1, hH⟩
    _ ≤ relMeasure μ R (K \ H) + relMeasure μ R (H \ T) := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε / 2) * μ (unitSpace T) + 0 := add_le_add hgood.small h1.le
    _ = ENNReal.ofReal (ε / 2) := by rw [hv, mul_one, add_zero]
    _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).2 (half_lt_self hε)

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias lemma9 := CFWPlan.Main.P5.lemma9

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
    [StandardBorelSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (R : Set (X × X)) (hR : IsDiscreteMeasured μ R) (hamen : Monod.IsAmenableRel μ R)
    (K : Set (X × X)) (hK : IsBoundedSubset μ R K) (ε : ℝ) (hε : 0 < ε) :
    ∃ T, IsFiniteSubrelation R T ∧ relMeasure μ R (K \ T) < ENNReal.ofReal ε :=
  lemma9 hR hamen hK hε
end
