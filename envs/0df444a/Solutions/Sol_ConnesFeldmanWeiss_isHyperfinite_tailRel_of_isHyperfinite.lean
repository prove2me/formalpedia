-- Prove2me | solution 1 for ConnesFeldmanWeiss.isHyperfinite_tailRel_of_isHyperfinite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T21:03:28.605035+00:00
-- url     : https://prove2.me/submissions/7a01518e-d649-47a0-bae0-2491829e9a4f

import Theorems.Thm_LusinNovikov_exists_injOn_cover_of_countable_fibers
import Theorems.Thm_LusinNovikov_exists_disjoint_injOn_fst_iUnion_eq_of_countable_sections
import Theorems.Thm_LusinNovikov_measurableSet_image_fst_of_countable_sections
import Theorems.Thm_LusinNovikov_measurableSet_image_of_countable_fibers
import Mathlib
import Definitions.Def_Monod_PiecewiseProjective
import Theorems.Thm_ConnesFeldmanWeiss_isHyperfinite_iff_isAmenableRel
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
/-- **B1 = (LN-1).** -/
theorem exists_injOn_cover_of_countable_fibers {f : X → Y} (hf : Measurable f)
    (hfib : ∀ y, (f ⁻¹' {y}).Countable) :
    ∃ S : ℕ → Set X, (∀ n, MeasurableSet (S n)) ∧ (∀ n, InjOn f (S n)) ∧ ⋃ n, S n = univ :=
  by
  try haveI := hf; try haveI := hfib; first
    | exact LusinNovikov.exists_injOn_cover_of_countable_fibers hf hfib
    | exact LusinNovikov.exists_injOn_cover_of_countable_fibers
    | exact LusinNovikov.exists_injOn_cover_of_countable_fibers ..
    | (apply LusinNovikov.exists_injOn_cover_of_countable_fibers <;> first | assumption | infer_instance)
    | simpa using LusinNovikov.exists_injOn_cover_of_countable_fibers

end CFWPlan.Route.PartB
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]
/-! ## §B. Glue to standard Borel spaces -/
alias exists_injOn_cover_of_countable_fibers := CFWPlan.Route.PartB.exists_injOn_cover_of_countable_fibers

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

/-- Making the points of a measurable set `M` singletons keeps a discrete measured relation discrete
measured (no nullness of `M` is needed). -/
theorem isDiscreteMeasured_cutOff {μ : Measure X} {E : Set (X × X)}
    (hE : IsDiscreteMeasured μ E) {M : Set X} (hM : MeasurableSet M) :
    IsDiscreteMeasured μ (cutOff E M) := by
  refine ⟨?_, ⟨fun x => Or.inr rfl, ?_, ?_⟩, fun x => ?_, fun A hA hA0 => ?_⟩
  · have h : cutOff E M = (E ∩ (Mᶜ ×ˢ Mᶜ)) ∪ {p | p.1 = p.2} := by
      ext p
      simp only [cutOff, mem_ofPred_eq, mem_union, mem_inter_iff, mem_prod, mem_compl_iff]
    rw [h]
    exact (hE.measurableSet.inter (hM.compl.prod hM.compl)).union measurableSet_diagonal
  · rintro x y (⟨h, hx, hy⟩ | h)
    · exact Or.inl ⟨hE.equivalence.symm h, hy, hx⟩
    · exact Or.inr (h : x = y).symm
  · rintro x y z (⟨h, hx, hy⟩ | h) (⟨h', hy', hz⟩ | h')
    · exact Or.inl ⟨hE.equivalence.trans h h', hx, hz⟩
    · have hyz : y = z := h'
      subst hyz
      exact Or.inl ⟨h, hx, hy⟩
    · have hxy : x = y := h
      subst hxy
      exact Or.inl ⟨h', hy', hz⟩
    · exact Or.inr ((h : x = y).trans h')
  · refine ((hE.countable_classes x).union (countable_singleton x)).mono ?_
    rintro y (⟨h, -, -⟩ | h)
    · exact Or.inl h
    · exact Or.inr (h : x = y).symm
  · refine measure_mono_null ?_ (measure_union_null hA0 (hE.quasiInvariant A hA hA0))
    rintro x ⟨y, hy, (⟨h, -, -⟩ | h)⟩
    · exact Or.inr ⟨y, hy, h⟩
    · have hxy : x = y := h
      rw [hxy]
      exact Or.inl hy

omit [StandardBorelSpace X] in
theorem cutOff_cutOff {R : Set (X × X)} {N N' : Set X} (h : N ⊆ N') :
    cutOff (cutOff R N) N' = cutOff R N' := by
  ext p
  simp only [cutOff, mem_ofPred_eq]
  constructor
  · rintro (⟨(⟨hR, -, -⟩ | hd), h1, h2⟩ | hd)
    · exact Or.inl ⟨hR, h1, h2⟩
    · exact Or.inr hd
    · exact Or.inr hd
  · rintro (⟨hR, h1, h2⟩ | hd)
    · exact Or.inl ⟨Or.inl ⟨hR, fun h' => h1 (h h'), fun h' => h2 (h h')⟩, h1, h2⟩
    · exact Or.inr hd

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
theorem IsHyperfinite.congr_null {μ : Measure X} {R R' : Set (X × X)} (h : IsHyperfinite μ R)
    {N : Set X} (hN : MeasurableSet N) (hN0 : μ N = 0)
    (hRR' : ∀ x y, x ∉ N → y ∉ N → ((x, y) ∈ R ↔ (x, y) ∈ R')) : IsHyperfinite μ R' := by
  obtain ⟨N₁, hN₁, hN₁0, hdisc, S, hmono, hS, hN₁R⟩ := h
  have hagree : ∀ x y, x ∉ N₁ ∪ N → y ∉ N₁ ∪ N → ((x, y) ∈ R ↔ (x, y) ∈ R') :=
    fun x y hx hy => hRR' x y (fun h => hx (Or.inr h)) (fun h => hy (Or.inr h))
  have hcut : cutOff R' (N₁ ∪ N) = cutOff R (N₁ ∪ N) := by
    ext ⟨x, y⟩
    simp only [cutOff, mem_ofPred_eq]
    constructor
    · rintro (⟨h, hx, hy⟩ | h)
      · exact Or.inl ⟨(hagree x y hx hy).2 h, hx, hy⟩
      · exact Or.inr h
    · rintro (⟨h, hx, hy⟩ | h)
      · exact Or.inl ⟨(hagree x y hx hy).1 h, hx, hy⟩
      · exact Or.inr h
  refine ⟨N₁ ∪ N, hN₁.union hN, measure_union_null hN₁0 hN0, ?_, S, hmono, hS,
    fun x y hx hy => ?_⟩
  · rw [hcut, ← cutOff_cutOff (subset_union_left : N₁ ⊆ N₁ ∪ N)]
    exact isDiscreteMeasured_cutOff hdisc (hN₁.union hN)
  · rw [← hagree x y hx hy]
    exact hN₁R x y (fun h => hx (Or.inl h)) (fun h => hy (Or.inl h))

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]
alias IsHyperfinite.congr_null := CFWPlan.Main.P1.IsHyperfinite.congr_null

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

theorem ptFun_image_dom {R : Set (X × X)} (φ : Monod.PartialTransformation R) :
    ptFun φ '' φ.dom = φ.cod := by
  have hsp := ptFun_spec φ
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hsp.1 x hx).1
  · intro hy
    exact ⟨ptInv φ y, (hsp.2.1 y hy).1, (hsp.2.1 y hy).2⟩

theorem lintegral_comp_ptInv {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (φ : Monod.PartialTransformation R) {g : X → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ y in φ.cod, g (ptInv φ y) ∂μ = ∫⁻ x in φ.dom, g x * module μ R (ptFun φ x, x) ∂μ := by
  have hsp := ptFun_spec φ
  rw [← ptFun_image_dom φ, lintegral_image_eq hR φ.measurableSet_dom (measurable_ptFun φ).1
    hsp.2.2 (fun x hx => (hsp.1 x hx).2.2) (h := fun y => g (ptInv φ y))
    (hg.comp (measurable_ptFun φ).2)]
  refine setLIntegral_congr_fun φ.measurableSet_dom fun x hx => ?_
  rw [(hsp.1 x hx).2.1]

/-- The image of `μ|cod` under `φ⁻¹` is `δ(φ x, x) dμ|dom`. -/
theorem map_restrict_ptInv {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (φ : Monod.PartialTransformation R) :
    (μ.restrict φ.cod).map (ptInv φ) =
      (μ.restrict φ.dom).withDensity fun x => module μ R (ptFun φ x, x) := by
  ext B hB
  have hinv := (measurable_ptFun φ).2
  rw [Measure.map_apply hinv hB, withDensity_apply _ hB, ← lintegral_indicator_one (hinv hB)]
  have h := lintegral_comp_ptInv hR φ (g := B.indicator 1) (measurable_one.indicator hB)
  convert h using 1
  · rfl
  · rw [← lintegral_indicator hB]
    congr 1
    funext x
    by_cases hx : x ∈ B
    · simp [indicator_of_mem hx]
    · simp [indicator_of_notMem hx]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

alias lintegral_comp_ptInv := CFWPlan.Main.P1.lintegral_comp_ptInv

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
theorem integral_comp_ptInv {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (φ : Monod.PartialTransformation R) {g : X → ℝ}
    (hg : Integrable (φ.dom.indicator fun x => g x * (module μ R (ptFun φ x, x)).toReal) μ) :
    ∫ y in φ.cod, g (ptInv φ y) ∂μ = ∫ x in φ.dom, g x * (module μ R (ptFun φ x, x)).toReal ∂μ := by
  set w : X → ℝ≥0∞ := fun x => module μ R (ptFun φ x, x) with hwdef
  have hw : Measurable w :=
    (measurable_module μ R).comp ((measurable_ptFun φ).1.prodMk measurable_id)
  have hsp := ptFun_spec φ
  have hwpos : ∀ᵐ x ∂μ.restrict φ.dom, 0 < w x ∧ w x < ∞ := by
    rw [ae_restrict_iff' φ.measurableSet_dom]
    filter_upwards [ae_module_good hR] with x hx hxD
    obtain ⟨h0, ht, hswap⟩ := hx (ptFun φ x) (hsp.1 x hxD).2.2
    simp only [hwdef]
    rw [hswap]
    exact ⟨ENNReal.inv_pos.2 ht.ne, ENNReal.inv_lt_top.2 h0⟩
  have hint : IntegrableOn (fun x => g x * (w x).toReal) φ.dom μ :=
    (integrable_indicator_iff φ.measurableSet_dom).1 hg
  have hgm : AEStronglyMeasurable g (μ.restrict φ.dom) := by
    have h1 : AEMeasurable (fun x => g x * (w x).toReal) (μ.restrict φ.dom) :=
      hint.aestronglyMeasurable.aemeasurable
    have h2 : AEMeasurable (fun x => (w x).toReal) (μ.restrict φ.dom) :=
      hw.ennreal_toReal.aemeasurable
    refine (h1.div h2).aestronglyMeasurable.congr ?_
    filter_upwards [hwpos] with x hx
    have : (w x).toReal ≠ 0 := (ENNReal.toReal_pos hx.1.ne' hx.2.ne).ne'
    simp only [Pi.div_apply]
    field_simp
  have hmap := map_restrict_ptInv hR φ
  have hL : ∫ y in φ.cod, g (ptInv φ y) ∂μ = ∫ y, g y ∂((μ.restrict φ.cod).map (ptInv φ)) := by
    refine (integral_map (measurable_ptFun φ).2.aemeasurable ?_).symm
    rw [hmap]
    exact hgm.mono_ac (withDensity_absolutelyContinuous _ _)
  rw [hL, hmap, integral_withDensity_eq_integral_toReal_smul hw
    (hwpos.mono fun x hx => hx.2) g]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, hwdef]
  ring

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias integral_comp_ptInv := CFWPlan.Main.P1.integral_comp_ptInv

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
lemma lin_zero (hsmul : ∀ (c : ℝ) (f : Ω → ℝ), Integrable f ν → Λ (c • f) = c * Λ f) :
    Λ 0 = 0 := by
  have := hsmul 0 0 (integrable_zero _ _ _)
  simpa using this

lemma lin_sub (hadd : ∀ f g, Integrable f ν → Integrable g ν → Λ (f + g) = Λ f + Λ g)
    (hsmul : ∀ (c : ℝ) (f : Ω → ℝ), Integrable f ν → Λ (c • f) = c * Λ f)
    {f g : Ω → ℝ} (hf : Integrable f ν) (hg : Integrable g ν) : Λ (f - g) = Λ f - Λ g := by
  have h1 : f - g = f + (-1 : ℝ) • g := by ext x; simp [sub_eq_add_neg]
  rw [h1, hadd _ _ hf (hg.smul _), hsmul _ _ hg]; ring

lemma lin_congr (hadd : ∀ f g, Integrable f ν → Integrable g ν → Λ (f + g) = Λ f + Λ g)
    (hsmul : ∀ (c : ℝ) (f : Ω → ℝ), Integrable f ν → Λ (c • f) = c * Λ f) {C : ℝ}
    (hbdd : ∀ f, Integrable f ν → |Λ f| ≤ C * ∫ x, |f x| ∂ν)
    {f g : Ω → ℝ} (hf : Integrable f ν) (hg : Integrable g ν) (hfg : f =ᵐ[ν] g) : Λ f = Λ g := by
  have h := hbdd (f - g) (hf.sub hg)
  have h0 : ∫ x, |(f - g) x| ∂ν = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hfg] with x hx
    simp [hx]
  rw [h0, mul_zero, lin_sub hadd hsmul hf hg] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

lemma lin_sum (hadd : ∀ f g, Integrable f ν → Integrable g ν → Λ (f + g) = Λ f + Λ g)
    (hsmul : ∀ (c : ℝ) (f : Ω → ℝ), Integrable f ν → Λ (c • f) = c * Λ f)
    {ι : Type*} (s : Finset ι) (h : ι → Ω → ℝ) (hi : ∀ i ∈ s, Integrable (h i) ν) :
    Λ (∑ i ∈ s, h i) = ∑ i ∈ s, Λ (h i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lin_zero hsmul]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      hadd _ _ (hi a (Finset.mem_insert_self a s))
        (integrable_finsetSum' s fun i hi' => hi i (Finset.mem_insert_of_mem hi')),
      ih fun i hi' => hi i (Finset.mem_insert_of_mem hi')]

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Main.P3
open ConnesFeldmanWeiss
variable {Ω : Type*} [MeasurableSpace Ω]
/-- `|Λ 1_A| ≤ C ν(A)`. -/
lemma abs_lin_indicator_le {ν : Measure Ω} {Λ : (Ω → ℝ) → ℝ} {C : ℝ}
    (hbdd : ∀ f, Integrable f ν → |Λ f| ≤ C * ∫ x, |f x| ∂ν) {A : Set Ω} (hA : MeasurableSet A)
    (hA' : ν A < ∞) : |Λ (A.indicator 1)| ≤ C * ν.real A := by
  have hi : Integrable (A.indicator (1 : Ω → ℝ)) ν :=
    (integrableOn_const hA'.ne : IntegrableOn (fun _ : Ω => (1 : ℝ)) A ν).integrable_indicator hA
  have h := hbdd _ hi
  have : ∫ x, |A.indicator (1 : Ω → ℝ) x| ∂ν = ν.real A := by
    have : (fun x => |A.indicator (1 : Ω → ℝ) x|) = A.indicator 1 := by
      ext x; by_cases hx : x ∈ A <;> simp [hx]
    rw [this, integral_indicator_one hA]
  rwa [this] at h

/-- The set function `E ↦ Λ 1_E` is countably additive (finite measure). -/
lemma hasSum_indicator (ν : Measure Ω) [IsFiniteMeasure ν] (Λ : (Ω → ℝ) → ℝ) {C : ℝ}
    (hadd : ∀ f g, Integrable f ν → Integrable g ν → Λ (f + g) = Λ f + Λ g)
    (hsmul : ∀ (c : ℝ) (f : Ω → ℝ), Integrable f ν → Λ (c • f) = c * Λ f)
    (hbdd : ∀ f, Integrable f ν → |Λ f| ≤ C * ∫ x, |f x| ∂ν)
    {E : ℕ → Set Ω} (hE : ∀ i, MeasurableSet (E i)) (hdisj : Pairwise (Disjoint on E)) :
    HasSum (fun i => Λ ((E i).indicator 1)) (Λ ((⋃ i, E i).indicator 1)) := by
  classical
  have hint : ∀ A : Set Ω, MeasurableSet A → Integrable (A.indicator (1 : Ω → ℝ)) ν :=
    fun A hA => (integrable_const (1 : ℝ)).indicator hA
  have hpd : ∀ n, ((Finset.range n : Finset ℕ) : Set ℕ).PairwiseDisjoint E :=
    fun n i _ j _ hij => hdisj hij
  have hmU : ∀ n, MeasurableSet (⋃ i ∈ Finset.range n, E i) :=
    fun n => Finset.measurableSet_biUnion _ fun i _ => hE i
  have hpart : ∀ n, ∑ i ∈ Finset.range n, Λ ((E i).indicator 1) =
      Λ ((⋃ i ∈ Finset.range n, E i).indicator 1) := by
    intro n
    rw [Finset.indicator_biUnion _ _ (hpd n)]
    have : (fun a => ∑ i ∈ Finset.range n, (E i).indicator (1 : Ω → ℝ) a) =
        ∑ i ∈ Finset.range n, (E i).indicator (1 : Ω → ℝ) := by
      ext a; simp [Finset.sum_apply]
    rw [this, lin_sum hadd hsmul _ _ fun i _ => hint _ (hE i)]
  have habs : ∀ A : Set Ω, MeasurableSet A → |Λ (A.indicator 1)| ≤ C * ν.real A :=
    fun A hA => abs_lin_indicator_le hbdd hA (measure_lt_top ν A)
  have hsum : Summable (fun i => Λ ((E i).indicator 1)) := by
    refine Summable.of_norm_bounded (g := fun i => C * ν.real (E i)) ?_ fun i => habs _ (hE i)
    refine Summable.mul_left C (summable_of_sum_range_le (c := ν.real univ)
      (fun n => measureReal_nonneg) fun n => ?_)
    rw [← measureReal_biUnion_finset (hpd n) fun i _ => hE i]
    exact measureReal_mono (subset_univ _)
  rw [hsum.hasSum_iff_tendsto_nat]
  simp_rw [hpart]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  -- dominated convergence for `∫ |1_{⋃_{<n}} - 1_⋃|`
  set F : ℕ → Ω → ℝ := fun n x =>
    |(⋃ i ∈ Finset.range n, E i).indicator (1 : Ω → ℝ) x - (⋃ i, E i).indicator 1 x| with hF
  have hFlim : Tendsto (fun n => ∫ x, F n x ∂ν) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := ν) (F := F) (f := fun _ => 0)
      (fun _ => 1) (fun n => ?_) (integrable_const _) (fun n => ?_) ?_
    · simpa using this
    · exact (((measurable_const.indicator (hmU n)).sub
        (measurable_const.indicator (MeasurableSet.iUnion hE))).abs).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      simp only [hF, Real.norm_eq_abs, abs_abs]
      rw [indicator_apply, indicator_apply]
      split_ifs <;> norm_num
    · refine Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ ⋃ i, E i
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_gt_atTop i] with n hn
        have h1 : x ∈ ⋃ i ∈ Finset.range n, E i :=
          mem_biUnion (Finset.mem_coe.mpr (Finset.mem_range.mpr hn)) hi
        simp only [hF]
        rw [indicator_of_mem h1, indicator_of_mem hx]; simp
      · refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
        have h1 : x ∉ ⋃ i ∈ Finset.range n, E i := fun h => hx (by
          obtain ⟨i, -, hi⟩ := mem_iUnion₂.mp h
          exact mem_iUnion.mpr ⟨i, hi⟩)
        simp only [hF]
        rw [indicator_of_notMem h1, indicator_of_notMem hx]; simp
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using hFlim.const_mul C)
  rw [Real.norm_eq_abs, ← lin_sub hadd hsmul (hint _ (hmU n)) (hint _ (MeasurableSet.iUnion hE))]
  exact hbdd _ ((hint _ (hmU n)).sub (hint _ (MeasurableSet.iUnion hE)))

/-- A linear functional bounded for the `L¹` norm is continuous on `L¹`. -/
lemma continuous_lin_L1 {ν : Measure Ω} {Λ : (Ω → ℝ) → ℝ}
    (hadd : ∀ f g, Integrable f ν → Integrable g ν → Λ (f + g) = Λ f + Λ g)
    (hsmul : ∀ (c : ℝ) (f : Ω → ℝ), Integrable f ν → Λ (c • f) = c * Λ f) {C : ℝ} (hC : 0 ≤ C)
    (hbdd : ∀ f, Integrable f ν → |Λ f| ≤ C * ∫ x, |f x| ∂ν) :
    Continuous fun F : Ω →₁[ν] ℝ => Λ F := by
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal C) fun F G => ?_).continuous
  rw [Real.coe_toNNReal _ hC, Real.dist_eq, dist_eq_norm, L1.norm_eq_integral_norm,
    ← lin_sub hadd hsmul (L1.integrable_coeFn F) (L1.integrable_coeFn G)]
  refine (hbdd _ ((L1.integrable_coeFn F).sub (L1.integrable_coeFn G))).trans_eq ?_
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub F G] with x hx
  rw [hx, Real.norm_eq_abs, Pi.sub_apply]

/-- Two linear functionals bounded for the `L¹` norm that agree on indicators of sets of finite
measure agree on all integrable functions. -/
lemma lin_eq_of_indicator {ν : Measure Ω} {Λ₁ Λ₂ : (Ω → ℝ) → ℝ}
    (hadd₁ : ∀ f g, Integrable f ν → Integrable g ν → Λ₁ (f + g) = Λ₁ f + Λ₁ g)
    (hsmul₁ : ∀ (c : ℝ) (f : Ω → ℝ), Integrable f ν → Λ₁ (c • f) = c * Λ₁ f) {C₁ : ℝ}
    (hC₁ : 0 ≤ C₁) (hbdd₁ : ∀ f, Integrable f ν → |Λ₁ f| ≤ C₁ * ∫ x, |f x| ∂ν)
    (hadd₂ : ∀ f g, Integrable f ν → Integrable g ν → Λ₂ (f + g) = Λ₂ f + Λ₂ g)
    (hsmul₂ : ∀ (c : ℝ) (f : Ω → ℝ), Integrable f ν → Λ₂ (c • f) = c * Λ₂ f) {C₂ : ℝ}
    (hC₂ : 0 ≤ C₂) (hbdd₂ : ∀ f, Integrable f ν → |Λ₂ f| ≤ C₂ * ∫ x, |f x| ∂ν)
    (h : ∀ E, MeasurableSet E → ν E < ∞ → Λ₁ (E.indicator 1) = Λ₂ (E.indicator 1)) :
    ∀ f, Integrable f ν → Λ₁ f = Λ₂ f := by
  intro f hf
  refine Integrable.induction (fun f => Λ₁ f = Λ₂ f) ?_ ?_ ?_ ?_ hf
  · intro c E hE hE'
    have h1 : (E.indicator fun _ => c) = c • E.indicator (1 : Ω → ℝ) := by
      ext x; by_cases hx : x ∈ E <;> simp [hx]
    have hi : Integrable (E.indicator (1 : Ω → ℝ)) ν :=
      (integrableOn_const hE'.ne : IntegrableOn (fun _ : Ω => (1 : ℝ)) E ν).integrable_indicator hE
    rw [h1, hsmul₁ _ _ hi, hsmul₂ _ _ hi, h E hE hE']
  · intro f f' _ hf hf' h1 h2
    rw [hadd₁ _ _ hf hf', hadd₂ _ _ hf hf', h1, h2]
  · exact isClosed_eq (continuous_lin_L1 hadd₁ hsmul₁ hC₁ hbdd₁)
      (continuous_lin_L1 hadd₂ hsmul₂ hC₂ hbdd₂)
  · intro f f' hff' hf h'
    rw [← lin_congr hadd₁ hsmul₁ hbdd₁ hf (hf.congr hff') hff',
      ← lin_congr hadd₂ hsmul₂ hbdd₂ hf (hf.congr hff') hff', h']

/-- Integration against a function bounded by `C` is linear and `L¹`-bounded. -/
lemma integral_mul_props {ν : Measure Ω} {g : Ω → ℝ} (hg : AEStronglyMeasurable g ν) {C : ℝ}
    (hgC : ∀ᵐ x ∂ν, |g x| ≤ C) :
    (∀ f f', Integrable f ν → Integrable f' ν →
      ∫ x, (f + f') x * g x ∂ν = ∫ x, f x * g x ∂ν + ∫ x, f' x * g x ∂ν) ∧
    (∀ (c : ℝ) (f : Ω → ℝ), Integrable f ν → ∫ x, (c • f) x * g x ∂ν = c * ∫ x, f x * g x ∂ν) ∧
    (∀ f, Integrable f ν → |∫ x, f x * g x ∂ν| ≤ C * ∫ x, |f x| ∂ν) ∧
    (∀ f, Integrable f ν → Integrable (fun x => f x * g x) ν) := by
  have hmul : ∀ f, Integrable f ν → Integrable (fun x => f x * g x) ν := fun f hf =>
    hf.mul_bdd hg (by filter_upwards [hgC] with x hx; rwa [Real.norm_eq_abs])
  refine ⟨fun f f' hf hf' => ?_, fun c f hf => ?_, fun f hf => ?_, hmul⟩
  · rw [← integral_add (hmul f hf) (hmul f' hf')]
    congr 1; ext x; simp [add_mul]
  · rw [← integral_const_mul]
    congr 1; ext x; simp [mul_assoc]
  · rw [← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono_ae (hmul f hf).abs
      (hf.abs.const_mul C) ?_)
    filter_upwards [hgC] with x hx
    rw [abs_mul, mul_comm C]
    exact mul_le_mul_of_nonneg_left hx (abs_nonneg _)

/-- **`(L¹)* = L∞`, finite measure.** A linear functional on integrable functions with
`|Λ f| ≤ C ‖f‖₁` is integration against a measurable `g` with `|g| ≤ C`. -/
theorem exists_bounded_density_of_functional_finite (ν : Measure Ω) [IsFiniteMeasure ν]
    (Λ : (Ω → ℝ) → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hadd : ∀ f g, Integrable f ν → Integrable g ν → Λ (f + g) = Λ f + Λ g)
    (hsmul : ∀ (c : ℝ) (f : Ω → ℝ), Integrable f ν → Λ (c • f) = c * Λ f)
    (hbdd : ∀ f, Integrable f ν → |Λ f| ≤ C * ∫ x, |f x| ∂ν) :
    ∃ g : Ω → ℝ, Measurable g ∧ (∀ x, |g x| ≤ C) ∧ ∀ f, Integrable f ν → Λ f = ∫ x, f x * g x ∂ν := by
  classical
  let s : SignedMeasure Ω :=
    { measureOf' := fun E => if MeasurableSet E then Λ (E.indicator 1) else 0
      empty' := by simp only [indicator_empty, MeasurableSet.empty, if_true]; exact lin_zero hsmul
      not_measurable' := fun E hE => if_neg hE
      m_iUnion' := fun E hE hdisj => by
        simp only [hE, MeasurableSet.iUnion hE, if_true]
        exact hasSum_indicator ν Λ hadd hsmul hbdd hE hdisj }
  have hs : ∀ E, MeasurableSet E → s E = Λ (E.indicator 1) := fun E hE => if_pos hE
  have hac : s ≪ᵥ ν.toENNRealVectorMeasure := by
    refine VectorMeasure.AbsolutelyContinuous.mk fun E hE h0 => ?_
    rw [Measure.toENNRealVectorMeasure_apply_measurable hE] at h0
    rw [hs E hE]
    have := abs_lin_indicator_le hbdd hE (measure_lt_top ν E)
    rw [measureReal_def, h0, ENNReal.toReal_zero, mul_zero] at this
    exact abs_nonpos_iff.mp this
  set g₀ := s.rnDeriv ν
  have hg₀int : Integrable g₀ ν := SignedMeasure.integrable_rnDeriv s ν
  have hg₀meas : Measurable g₀ := SignedMeasure.measurable_rnDeriv s ν
  have hset : ∀ E, MeasurableSet E → Λ (E.indicator 1) = ∫ x in E, g₀ x ∂ν := by
    intro E hE
    rw [← hs E hE, ← withDensityᵥ_apply hg₀int hE, SignedMeasure.withDensityᵥ_rnDeriv_eq s ν hac]
  have hup : g₀ ≤ᵐ[ν] fun _ => C := by
    refine ae_le_of_forall_setIntegral_le hg₀int (integrable_const C) fun E hE _ => ?_
    rw [← hset E hE, setIntegral_const, smul_eq_mul, mul_comm]
    exact (le_abs_self _).trans (abs_lin_indicator_le hbdd hE (measure_lt_top ν E))
  have hlo : (fun _ => -C) ≤ᵐ[ν] g₀ := by
    refine ae_le_of_forall_setIntegral_le (integrable_const (-C)) hg₀int fun E hE _ => ?_
    rw [← hset E hE, setIntegral_const, smul_eq_mul]
    have h1 := neg_abs_le (Λ (E.indicator 1))
    have h2 := abs_lin_indicator_le hbdd hE (measure_lt_top ν E)
    linarith
  set g : Ω → ℝ := fun x => max (-C) (min C (g₀ x)) with hg_def
  have hgg₀ : g =ᵐ[ν] g₀ := by
    filter_upwards [hup, hlo] with x h1 h2
    simp only [hg_def]; rw [min_eq_right h1, max_eq_right h2]
  have hgmeas : Measurable g := measurable_const.max (measurable_const.min hg₀meas)
  have hgC : ∀ x, |g x| ≤ C := fun x =>
    abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  refine ⟨g, hgmeas, hgC, ?_⟩
  obtain ⟨hadd₂, hsmul₂, hbdd₂, -⟩ :=
    integral_mul_props (ν := ν) hgmeas.aestronglyMeasurable (Eventually.of_forall hgC)
  refine lin_eq_of_indicator hadd hsmul hC hbdd hadd₂ hsmul₂ hC hbdd₂ fun E hE _ => ?_
  have h2 : (fun x => E.indicator (1 : Ω → ℝ) x * g x) = E.indicator g := by
    ext x; by_cases hx : x ∈ E <;> simp [hx]
  rw [h2, integral_indicator hE, hset E hE]
  exact setIntegral_congr_ae hE (by filter_upwards [hgg₀] with x hx _; exact hx.symm)

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
/-- **`(L¹)* = L∞`, σ-finite measure.** Reduction to the finite case through an equivalent finite
measure `ν' = w ν` with `w > 0` (instead of the Route's gluing over spanning sets). -/
theorem exists_bounded_density_of_functional (ν : Measure Ω) [SigmaFinite ν]
    (Λ : (Ω → ℝ) → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hadd : ∀ f g, Integrable f ν → Integrable g ν → Λ (f + g) = Λ f + Λ g)
    (hsmul : ∀ (c : ℝ) (f : Ω → ℝ), Integrable f ν → Λ (c • f) = c * Λ f)
    (hbdd : ∀ f, Integrable f ν → |Λ f| ≤ C * ∫ x, |f x| ∂ν) :
    ∃ g : Ω → ℝ, Measurable g ∧ (∀ x, |g x| ≤ C) ∧ ∀ f, Integrable f ν → Λ f = ∫ x, f x * g x ∂ν := by
  obtain ⟨w, hwpos, hwmeas, hwint⟩ := exists_pos_lintegral_lt_of_sigmaFinite ν one_ne_zero
  set ν' := ν.withDensity fun x => (w x : ℝ≥0∞) with hν'
  have : IsFiniteMeasure ν' := isFiniteMeasure_withDensity (hwint.trans ENNReal.one_lt_top).ne
  have hw0 : ∀ x, (w x : ℝ) ≠ 0 := fun x => (NNReal.coe_pos.mpr (hwpos x)).ne'
  have hint' : ∀ f : Ω → ℝ, Integrable f ν' ↔ Integrable (fun x => (w x : ℝ) * f x) ν := fun f => by
    rw [hν', integrable_withDensity_iff_integrable_smul hwmeas]
    simp only [NNReal.smul_def, smul_eq_mul]
  have hintg' : ∀ f : Ω → ℝ, ∫ x, f x ∂ν' = ∫ x, (w x : ℝ) * f x ∂ν := fun f => by
    rw [hν', integral_withDensity_eq_integral_smul hwmeas]
    simp only [NNReal.smul_def, smul_eq_mul]
  set Λ' : (Ω → ℝ) → ℝ := fun f => Λ (fun x => (w x : ℝ) * f x) with hΛ'
  have hadd' : ∀ f g, Integrable f ν' → Integrable g ν' → Λ' (f + g) = Λ' f + Λ' g := by
    intro f f' hf hf'
    simp only [hΛ']
    rw [← hadd _ _ ((hint' f).1 hf) ((hint' f').1 hf')]
    congr 1; ext x; simp [mul_add]
  have hsmul' : ∀ (c : ℝ) (f : Ω → ℝ), Integrable f ν' → Λ' (c • f) = c * Λ' f := by
    intro c f hf
    simp only [hΛ']
    rw [← hsmul _ _ ((hint' f).1 hf)]
    congr 1; ext x; simp only [Pi.smul_apply, smul_eq_mul]; ring
  have hbdd' : ∀ f, Integrable f ν' → |Λ' f| ≤ C * ∫ x, |f x| ∂ν' := by
    intro f hf
    simp only [hΛ']
    refine (hbdd _ ((hint' f).1 hf)).trans_eq ?_
    rw [hintg']
    congr 2; ext x; rw [abs_mul, abs_of_nonneg (NNReal.coe_nonneg _)]
  obtain ⟨g, hgm, hgC, hg⟩ :=
    exists_bounded_density_of_functional_finite ν' Λ' hC hadd' hsmul' hbdd'
  refine ⟨g, hgm, hgC, fun f hf => ?_⟩
  have hf' : Integrable (fun x => f x / w x) ν' := by
    rw [hint']
    refine hf.congr (Eventually.of_forall fun x => ?_)
    simp only
    field_simp [hw0 x]
  have h1 := hg _ hf'
  have e : (fun x => (w x : ℝ) * (f x / w x)) = f := by
    ext x; field_simp [hw0 x]
  simp only [hΛ', e] at h1
  rw [h1, hintg']
  congr 1; ext x; field_simp [hw0 x]

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
/-- Bounded densities are determined by their integrals against integrable functions. -/
theorem ae_eq_of_forall_integral_mul_eq (ν : Measure Ω) [SigmaFinite ν] {g₁ g₂ : Ω → ℝ}
    (h₁ : AEStronglyMeasurable g₁ ν) (h₂ : AEStronglyMeasurable g₂ ν) {C : ℝ}
    (hb₁ : ∀ᵐ x ∂ν, |g₁ x| ≤ C) (hb₂ : ∀ᵐ x ∂ν, |g₂ x| ≤ C)
    (h : ∀ f, Integrable f ν → ∫ x, f x * g₁ x ∂ν = ∫ x, f x * g₂ x ∂ν) : g₁ =ᵐ[ν] g₂ := by
  have hind : ∀ s, MeasurableSet s → ν s < ∞ → Integrable (s.indicator (1 : Ω → ℝ)) ν :=
    fun s hs hs' =>
      (integrableOn_const hs'.ne : IntegrableOn (fun _ : Ω => (1 : ℝ)) s ν).integrable_indicator hs
  have key : ∀ g : Ω → ℝ, ∀ s, MeasurableSet s →
      ∫ x, s.indicator (1 : Ω → ℝ) x * g x ∂ν = ∫ x in s, g x ∂ν := by
    intro g s hs
    rw [← integral_indicator hs]; congr 1; ext x; by_cases hx : x ∈ s <;> simp [hx]
  have hon : ∀ g : Ω → ℝ, AEStronglyMeasurable g ν → (∀ᵐ x ∂ν, |g x| ≤ C) →
      ∀ s, MeasurableSet s → ν s < ∞ → IntegrableOn g s ν := by
    intro g hg hb s hs hs'
    have := (hind s hs hs').mul_bdd hg (c := C) (by filter_upwards [hb] with x hx; rwa [Real.norm_eq_abs])
    rw [← integrable_indicator_iff hs]
    refine this.congr (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ s <;> simp [hx]
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (hon g₁ h₁ hb₁) (hon g₂ h₂ hb₂)
    fun s hs hs' => ?_
  rw [← key g₁ s hs, ← key g₂ s hs]
  exact h _ (hind s hs hs')

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
/-- **Weak* limits in `L∞` along an ultrafilter** (Banach–Alaoglu, concrete form). -/
theorem exists_weakStar_limit {ι : Type*} (ν : Measure Ω) [SigmaFinite ν] (U : Ultrafilter ι)
    (g : ι → Ω → ℝ) {C : ℝ} (hC : 0 ≤ C) (hg : ∀ i, AEStronglyMeasurable (g i) ν)
    (hgC : ∀ i, ∀ᵐ x ∂ν, |g i x| ≤ C) :
    ∃ h : Ω → ℝ, Measurable h ∧ (∀ x, |h x| ≤ C) ∧ ∀ f, Integrable f ν →
      Tendsto (fun i => ∫ x, f x * g i x ∂ν) (U : Filter ι) (𝓝 (∫ x, f x * h x ∂ν)) := by
  have hprops := fun i => integral_mul_props (hg i) (hgC i)
  have hmem : ∀ f, Integrable f ν → ∀ i,
      ∫ x, f x * g i x ∂ν ∈ Icc (-(C * ∫ x, |f x| ∂ν)) (C * ∫ x, |f x| ∂ν) :=
    fun f hf i => abs_le.mp ((hprops i).2.2.1 f hf)
  have hlim : ∀ f, Integrable f ν →
      ∃ a, Tendsto (fun i => ∫ x, f x * g i x ∂ν) (U : Filter ι) (𝓝 a) := by
    intro f hf
    obtain ⟨a, -, ha⟩ := (isCompact_Icc (a := -(C * ∫ x, |f x| ∂ν))
      (b := C * ∫ x, |f x| ∂ν)).ultrafilter_le_nhds (U.map fun i => ∫ x, f x * g i x ∂ν) (by
        rw [Ultrafilter.coe_map, le_principal_iff, Filter.mem_map]
        exact Filter.univ_mem' (hmem f hf))
    refine ⟨a, ?_⟩
    rw [Ultrafilter.coe_map] at ha
    exact ha
  set Λ : (Ω → ℝ) → ℝ := fun f => limUnder (U : Filter ι) (fun i => ∫ x, f x * g i x ∂ν)
    with hΛdef
  have hΛ : ∀ f, Integrable f ν →
      Tendsto (fun i => ∫ x, f x * g i x ∂ν) (U : Filter ι) (𝓝 (Λ f)) :=
    fun f hf => tendsto_nhds_limUnder (hlim f hf)
  have hadd : ∀ f f', Integrable f ν → Integrable f' ν → Λ (f + f') = Λ f + Λ f' := by
    intro f f' hf hf'
    refine tendsto_nhds_unique (hΛ _ (hf.add hf')) ?_
    exact ((hΛ f hf).add (hΛ f' hf')).congr fun i => ((hprops i).1 f f' hf hf').symm
  have hsmul : ∀ (c : ℝ) (f : Ω → ℝ), Integrable f ν → Λ (c • f) = c * Λ f := by
    intro c f hf
    refine tendsto_nhds_unique (hΛ _ (hf.smul c)) ?_
    exact ((hΛ f hf).const_mul c).congr fun i => ((hprops i).2.1 c f hf).symm
  have hbdd : ∀ f, Integrable f ν → |Λ f| ≤ C * ∫ x, |f x| ∂ν := fun f hf =>
    abs_le.mpr (isClosed_Icc.mem_of_tendsto (hΛ f hf) (Eventually.of_forall (hmem f hf)))
  obtain ⟨h, hm, hhC, hh⟩ := exists_bounded_density_of_functional ν Λ hC hadd hsmul hbdd
  exact ⟨h, hm, hhC, fun f hf => (hh f hf) ▸ hΛ f hf⟩

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
lemma bdd_add {f g : X × X → ℝ} (hf : Monod.IsBddMeasOn R f) (hg : Monod.IsBddMeasOn R g) :
    Monod.IsBddMeasOn R (f + g) := by
  obtain ⟨hfm, C, hC⟩ := hf
  obtain ⟨hgm, D, hD⟩ := hg
  exact ⟨hfm.add hgm, C + D, fun p hp => (abs_add_le _ _).trans (add_le_add (hC p hp) (hD p hp))⟩

lemma bdd_smul (c : ℝ) {f : X × X → ℝ} (hf : Monod.IsBddMeasOn R f) :
    Monod.IsBddMeasOn R (c • f) := by
  obtain ⟨hfm, C, hC⟩ := hf
  refine ⟨hfm.const_smul c, |c| * C, fun p hp => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC p hp) (abs_nonneg _)

lemma bdd_one : Monod.IsBddMeasOn R (1 : X × X → ℝ) :=
  ⟨measurable_const, 1, fun _ _ => by simp⟩

lemma bdd_mul_fst {g : X → ℝ} (hg : Measurable g) {C : ℝ} (hgC : ∀ x, |g x| ≤ C)
    {f : X × X → ℝ} (hf : Monod.IsBddMeasOn R f) :
    Monod.IsBddMeasOn R (fun p => g p.1 * f p) := by
  obtain ⟨hfm, D, hD⟩ := hf
  refine ⟨(hg.comp measurable_fst).mul hfm, C * D, fun p hp => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hgC _) (hD p hp) (abs_nonneg _) ((abs_nonneg _).trans (hgC p.1))

/-- A bounded measurable function admits a nonnegative bound. -/
lemma IsBddMeasOn.exists_nonneg {f : X × X → ℝ} (hf : Monod.IsBddMeasOn R f) :
    ∃ C, 0 ≤ C ∧ ∀ p ∈ R, |f p| ≤ C := by
  obtain ⟨-, C, hC⟩ := hf
  exact ⟨max C 0, le_max_right _ _, fun p hp => (hC p hp).trans (le_max_left _ _)⟩

lemma ptInv_mem_R (φ : Monod.PartialTransformation R) {y : X} (hy : y ∈ φ.cod) :
    (ptInv φ y, y) ∈ R := by
  obtain ⟨h1, h2⟩ := (ptFun_spec φ).2.1 y hy
  have h3 := ((ptFun_spec φ).1 _ h1).2.2
  rwa [h2] at h3

lemma bdd_shiftRel (hRe : Equivalence fun x y => (x, y) ∈ R) (φ : Monod.PartialTransformation R)
    {f : X × X → ℝ} (hf : Monod.IsBddMeasOn R f) : Monod.IsBddMeasOn R (φ.shiftRel f) := by
  classical
  obtain ⟨hfm, C, hC⟩ := hf
  rw [shiftRel_eq]
  refine ⟨Measurable.ite (measurable_fst φ.measurableSet_cod)
    (hfm.comp (((measurable_ptFun φ).2.comp measurable_fst).prodMk measurable_snd))
    measurable_const, C, fun p hp => ?_⟩
  dsimp only
  by_cases h : p.1 ∈ φ.cod
  · rw [if_pos h]
    exact hC _ (hRe.trans (ptInv_mem_R φ h) hp)
  · rw [if_neg h, abs_zero]
    exact (abs_nonneg _).trans (hC p hp)

lemma measurable_shiftBase (φ : Monod.PartialTransformation R) {G : X → ℝ} (hG : Measurable G) :
    Measurable (φ.shiftBase G) := by
  classical
  rw [shiftBase_eq]
  exact Measurable.ite φ.measurableSet_cod (hG.comp (measurable_ptFun φ).2) measurable_const

/-- A property holding a.e. holds a.e. at `φ⁻¹ y` for `y ∈ cod φ` (quasi-invariance). -/
lemma ae_ptInv {μ : Measure X} (hR : IsDiscreteMeasured μ R) (φ : Monod.PartialTransformation R)
    {p : X → Prop} (h : ∀ᵐ x ∂μ, p x) : ∀ᵐ y ∂μ, y ∈ φ.cod → p (ptInv φ y) := by
  rw [ae_iff] at h ⊢
  refine measure_mono_null ?_ (IsDiscreteMeasured.qi hR _ h)
  intro y hy
  simp only [Classical.not_imp, mem_ofPred_eq] at hy
  exact ⟨ptInv φ y, hy.2, ptInv_mem_R φ hy.1⟩

lemma ae_abs_shiftBase_le {μ : Measure X} (hR : IsDiscreteMeasured μ R)
    (φ : Monod.PartialTransformation R) {G : X → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hG : ∀ᵐ x ∂μ, |G x| ≤ C) : ∀ᵐ y ∂μ, |φ.shiftBase G y| ≤ C := by
  classical
  filter_upwards [ae_ptInv hR φ hG] with y hy
  rw [shiftBase_eq]
  dsimp only
  by_cases h : y ∈ φ.cod
  · rw [if_pos h]; exact hy h
  · rw [if_neg h, abs_zero]; exact hC

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
set_option linter.unusedSectionVars false
namespace CFWPlan.Main.P3
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
lemma integral_indicator_one_mul {μ : Measure X} {s : Set X} (hs : MeasurableSet s) (u : X → ℝ) :
    ∫ x, s.indicator (1 : X → ℝ) x * u x ∂μ = ∫ x in s, u x ∂μ := by
  rw [← integral_indicator hs]
  congr 1; ext x
  by_cases hx : x ∈ s
  · rw [indicator_of_mem hx, indicator_of_mem hx, Pi.one_apply, one_mul]
  · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]

lemma integrable_indicator_one {μ : Measure X} {s : Set X} (hs : MeasurableSet s)
    (hs' : μ s < ∞) : Integrable (s.indicator (1 : X → ℝ)) μ :=
  (integrableOn_const hs'.ne : IntegrableOn (fun _ : X => (1 : ℝ)) s μ).integrable_indicator hs

lemma integrableOn_of_ae_bdd {μ : Measure X} {u : X → ℝ} (hu : AEStronglyMeasurable u μ) {C : ℝ}
    (hC : ∀ᵐ x ∂μ, |u x| ≤ C) {s : Set X} (hs : MeasurableSet s) (hs' : μ s < ∞) :
    IntegrableOn u s μ := by
  have := (integrable_indicator_one hs hs').mul_bdd hu (c := C)
    (by filter_upwards [hC] with x hx; rwa [Real.norm_eq_abs])
  rw [← integrable_indicator_iff hs]
  refine this.congr (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ s
  · simp only
    rw [indicator_of_mem hx, indicator_of_mem hx, Pi.one_apply, one_mul]
  · simp only
    rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]

lemma integrable_mul_bdd {μ : Measure X} {c : X → ℝ} (hc : Integrable c μ) {u : X → ℝ}
    (hu : AEStronglyMeasurable u μ) {C : ℝ} (hC : ∀ᵐ x ∂μ, |u x| ≤ C) :
    Integrable (fun x => c x * u x) μ :=
  hc.mul_bdd hu (by filter_upwards [hC] with x hx; rwa [Real.norm_eq_abs])

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
/-- Means are contractions: `|f| ≤ C` on `R` gives `|P f| ≤ C` a.e. -/
theorem IsLeftInvariantMean.ae_abs_le {μ : Measure X} {R : Set (X × X)}
    {P : (X × X → ℝ) → X → ℝ} (hP : Monod.IsLeftInvariantMean μ R P) {f : X × X → ℝ}
    (hf : Monod.IsBddMeasOn R f) {C : ℝ} (hC : ∀ p ∈ R, |f p| ≤ C) : ∀ᵐ x ∂μ, |P f x| ≤ C := by
  have h1 : Monod.IsBddMeasOn R (C • (1 : X × X → ℝ)) := bdd_smul C bdd_one
  have h2 : Monod.IsBddMeasOn R ((-1 : ℝ) • f) := bdd_smul _ hf
  have n1 := hP.nonneg _ (bdd_add h1 h2) fun p hp => by
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
    linarith [(abs_le.mp (hC p hp)).2]
  have n2 := hP.nonneg _ (bdd_add h1 hf) fun p hp => by
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
    linarith [(abs_le.mp (hC p hp)).1]
  filter_upwards [n1, n2, hP.add _ _ h1 h2, hP.add _ _ h1 hf, hP.smul C 1 bdd_one,
    hP.smul (-1) f hf, hP.one] with x a1 a2 a3 a4 a5 a6 a7
  rw [a3] at a1
  rw [a4] at a2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at a1 a2 a5 a6
  rw [a5, a6, a7, Pi.one_apply] at a1
  rw [a5, a7, Pi.one_apply] at a2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

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
/-- Modularity for an indicator: the invariance of `P` under `id_A`. -/
lemma mul_fst_indicator {μ : Measure X} {R : Set (X × X)} (hR : ∀ x, (x, x) ∈ R)
    {P : (X × X → ℝ) → X → ℝ} (hP : Monod.IsLeftInvariantMean μ R P) {f : X × X → ℝ}
    (hf : Monod.IsBddMeasOn R f) {A : Set X} (hA : MeasurableSet A) :
    P (fun p => A.indicator 1 p.1 * f p) =ᵐ[μ] fun x => A.indicator 1 x * P f x := by
  have h := hP.invariant (ptId hR A hA) f hf
  have e1 : (ptId hR A hA).shiftRel f = fun p => A.indicator 1 p.1 * f p := by
    ext p
    simp only [Monod.PartialTransformation.shiftRel]
    by_cases hp : p.1 ∈ A
    · have hp' : p.1 ∈ (ptId hR A hA).cod := hp
      rw [dif_pos hp', indicator_of_mem hp, Pi.one_apply, one_mul]
      rfl
    · have hp' : p.1 ∉ (ptId hR A hA).cod := hp
      rw [dif_neg hp', indicator_of_notMem hp, zero_mul]
  have e2 : (ptId hR A hA).shiftBase (P f) = fun x => A.indicator 1 x * P f x := by
    ext x
    simp only [Monod.PartialTransformation.shiftBase]
    by_cases hx : x ∈ A
    · have hx' : x ∈ (ptId hR A hA).cod := hx
      rw [dif_pos hx', indicator_of_mem hx, Pi.one_apply, one_mul]
      rfl
    · have hx' : x ∉ (ptId hR A hA).cod := hx
      rw [dif_neg hx', indicator_of_notMem hx, zero_mul]
  rw [e1, e2] at h
  exact h

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

/-- **Means from asymptotically invariant sequences (the weak-limit device).** -/
theorem isAmenableRel_of_asymptotic {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (Q : ℕ → (X × X → ℝ) → X → ℝ)
    (hmeas : ∀ k f, Monod.IsBddMeasOn R f → Measurable (Q k f))
    (hbdd : ∀ k f C, Monod.IsBddMeasOn R f → (∀ p ∈ R, |f p| ≤ C) → ∀ᵐ x ∂μ, |Q k f x| ≤ C)
    (hadd : ∀ k f g, Monod.IsBddMeasOn R f → Monod.IsBddMeasOn R g →
      Q k (f + g) =ᵐ[μ] Q k f + Q k g)
    (hsmul : ∀ k (c : ℝ) f, Monod.IsBddMeasOn R f → Q k (c • f) =ᵐ[μ] c • Q k f)
    (hnonneg : ∀ k f, Monod.IsBddMeasOn R f → (∀ p ∈ R, 0 ≤ f p) → ∀ᵐ x ∂μ, 0 ≤ Q k f x)
    (hone : ∀ k, Q k 1 =ᵐ[μ] 1)
    (hcongr : ∀ k f g, Monod.IsBddMeasOn R f → Monod.IsBddMeasOn R g →
      Monod.RelNull μ R {p | f p ≠ g p} → Q k f =ᵐ[μ] Q k g)
    (hinv : ∀ (φ : Monod.PartialTransformation R) f, Monod.IsBddMeasOn R f →
      ∀ᵐ x ∂μ, Tendsto (fun k => Q k (φ.shiftRel f) x - φ.shiftBase (Q k f) x) atTop (𝓝 0)) :
    Monod.IsAmenableRel μ R := by
  classical
  have hRe := hR.equivalence
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  have hU : (U : Filter ℕ) ≤ atTop := by
    rw [← Nat.cofinite_eq_atTop]; exact hyperfilter_le_cofinite
  have key : ∀ f, Monod.IsBddMeasOn R f → ∃ h : X → ℝ, Measurable h ∧
      (∃ C, 0 ≤ C ∧ (∀ x, |h x| ≤ C) ∧ ∀ k, ∀ᵐ x ∂μ, |Q k f x| ≤ C) ∧
      ∀ c, Integrable c μ →
        Tendsto (fun k => ∫ x, c x * Q k f x ∂μ) (U : Filter ℕ) (𝓝 (∫ x, c x * h x ∂μ)) := by
    intro f hf
    obtain ⟨C, hC0, hC⟩ := IsBddMeasOn.exists_nonneg hf
    obtain ⟨h, hm, hhC, hlim⟩ := exists_weakStar_limit μ U (fun k => Q k f) hC0
      (fun k => (hmeas k f hf).aestronglyMeasurable) (fun k => hbdd k f C hf hC)
    exact ⟨h, hm, ⟨C, hC0, hhC, fun k => hbdd k f C hf hC⟩, hlim⟩
  choose! H hHm hHC hHlim using key
  refine ⟨H, ⟨fun f hf => (hHm f hf).aemeasurable, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · -- congr
    intro f g hf hg hfg
    obtain ⟨Cf, -, hCf, -⟩ := hHC f hf
    obtain ⟨Cg, -, hCg, -⟩ := hHC g hg
    refine ae_eq_of_forall_integral_mul_eq μ (C := max Cf Cg) (hHm f hf).aestronglyMeasurable
      (hHm g hg).aestronglyMeasurable
      (Eventually.of_forall fun x => (hCf x).trans (le_max_left _ _))
      (Eventually.of_forall fun x => (hCg x).trans (le_max_right _ _)) fun c hc => ?_
    refine tendsto_nhds_unique (hHlim f hf c hc) ((hHlim g hg c hc).congr fun k => ?_)
    exact integral_congr_ae (by filter_upwards [hcongr k f g hf hg hfg] with x hx; rw [hx])
  · -- add
    intro f g hf hg
    have hfg := bdd_add hf hg
    obtain ⟨Cf, hCf0, hCf, hQf⟩ := hHC f hf
    obtain ⟨Cg, hCg0, hCg, hQg⟩ := hHC g hg
    obtain ⟨Cfg, hCfg0, hCfg, -⟩ := hHC _ hfg
    refine ae_eq_of_forall_integral_mul_eq μ (C := Cfg + (Cf + Cg))
      (hHm _ hfg).aestronglyMeasurable ((hHm f hf).add (hHm g hg)).aestronglyMeasurable
      (Eventually.of_forall fun x => (hCfg x).trans (by linarith))
      (Eventually.of_forall fun x => (abs_add_le _ _).trans
        ((add_le_add (hCf x) (hCg x)).trans (by linarith))) fun c hc => ?_
    refine tendsto_nhds_unique (hHlim _ hfg c hc) ?_
    have e : ∫ x, c x * (H f + H g) x ∂μ = ∫ x, c x * H f x ∂μ + ∫ x, c x * H g x ∂μ := by
      rw [← integral_add (integrable_mul_bdd hc (hHm f hf).aestronglyMeasurable
        (Eventually.of_forall hCf)) (integrable_mul_bdd hc (hHm g hg).aestronglyMeasurable
        (Eventually.of_forall hCg))]
      congr 1; ext x; simp [mul_add]
    rw [e]
    refine ((hHlim f hf c hc).add (hHlim g hg c hc)).congr fun k => ?_
    rw [← integral_add (integrable_mul_bdd hc (hmeas k f hf).aestronglyMeasurable (hQf k))
      (integrable_mul_bdd hc (hmeas k g hg).aestronglyMeasurable (hQg k))]
    refine integral_congr_ae ?_
    filter_upwards [hadd k f g hf hg] with x hx
    rw [hx, Pi.add_apply, mul_add]
  · -- smul
    intro a f hf
    have haf := bdd_smul a hf
    obtain ⟨Cf, hCf0, hCf, hQf⟩ := hHC f hf
    obtain ⟨Caf, hCaf0, hCaf, -⟩ := hHC _ haf
    refine ae_eq_of_forall_integral_mul_eq μ (C := Caf + |a| * Cf)
      (hHm _ haf).aestronglyMeasurable ((hHm f hf).const_smul a).aestronglyMeasurable
      (Eventually.of_forall fun x => (hCaf x).trans (by
        have := mul_nonneg (abs_nonneg a) hCf0; linarith))
      (Eventually.of_forall fun x => by
        rw [Pi.smul_apply, smul_eq_mul, abs_mul]
        have := mul_le_mul_of_nonneg_left (hCf x) (abs_nonneg a)
        linarith) fun c hc => ?_
    refine tendsto_nhds_unique (hHlim _ haf c hc) ?_
    have e : ∫ x, c x * (a • H f) x ∂μ = a * ∫ x, c x * H f x ∂μ := by
      rw [← integral_const_mul]
      congr 1; ext x; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    refine ((hHlim f hf c hc).const_mul a).congr fun k => ?_
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hsmul k a f hf] with x hx
    rw [hx, Pi.smul_apply, smul_eq_mul]; ring
  · -- nonneg
    intro f hf hnn
    obtain ⟨Cf, hCf0, hCf, -⟩ := hHC f hf
    refine ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite
      (fun s hs hs' => integrableOn_of_ae_bdd (hHm f hf).aestronglyMeasurable
        (Eventually.of_forall hCf) hs hs') fun s hs hs' => ?_
    rw [← integral_indicator_one_mul hs]
    refine ge_of_tendsto (hHlim f hf _ (integrable_indicator_one hs hs'))
      (Eventually.of_forall fun k => integral_nonneg_of_ae ?_)
    filter_upwards [hnonneg k f hf hnn] with x hx
    refine mul_nonneg ?_ hx
    by_cases h : x ∈ s
    · rw [indicator_of_mem h, Pi.one_apply]; exact zero_le_one
    · rw [indicator_of_notMem h]
  · -- one
    obtain ⟨C1, hC10, hC1, -⟩ := hHC 1 bdd_one
    refine ae_eq_of_forall_integral_mul_eq μ (C := max C1 1) (hHm 1 bdd_one).aestronglyMeasurable
      aestronglyMeasurable_const (Eventually.of_forall fun x => (hC1 x).trans (le_max_left _ _))
      (Eventually.of_forall fun x => by simp) fun c hc => ?_
    refine tendsto_nhds_unique (hHlim 1 bdd_one c hc) (tendsto_const_nhds.congr fun k => ?_)
    exact integral_congr_ae (by filter_upwards [hone k] with x hx; rw [hx])
  · -- invariance
    intro φ f hf
    have hF := bdd_shiftRel hRe φ hf
    obtain ⟨Cf, hCf0, hCf, hQf⟩ := hHC f hf
    obtain ⟨CF, hCF0, hCF, hQF⟩ := hHC _ hF
    have hsbH : Measurable (φ.shiftBase (H f)) := measurable_shiftBase φ (hHm f hf)
    have hsbHb : ∀ᵐ x ∂μ, |φ.shiftBase (H f) x| ≤ Cf :=
      ae_abs_shiftBase_le hR φ hCf0 (Eventually.of_forall hCf)
    refine ae_eq_of_forall_integral_mul_eq μ (C := CF + Cf) (hHm _ hF).aestronglyMeasurable
      hsbH.aestronglyMeasurable (Eventually.of_forall fun x => (hCF x).trans (by linarith))
      (by filter_upwards [hsbHb] with x hx; linarith) fun c hc => ?_
    -- a measurable version of the test function
    obtain ⟨c', hc'm, hcc'⟩ : ∃ c' : X → ℝ, Measurable c' ∧ c =ᵐ[μ] c' :=
      ⟨hc.1.mk c, hc.1.stronglyMeasurable_mk.measurable, hc.1.ae_eq_mk⟩
    have hc' : Integrable c' μ := hc.congr hcc'
    have hrw : ∀ u : X → ℝ, ∫ x, c x * u x ∂μ = ∫ x, c' x * u x ∂μ := fun u =>
      integral_congr_ae (by filter_upwards [hcc'] with x hx; rw [hx])
    rw [hrw, hrw]
    -- the transported test function `w = 1_dom · (c' ∘ φ) · δ(φ ·, ·)`
    have hmod : Measurable (module μ R) := Measure.measurable_rnDeriv _ _
    set w : X → ℝ := φ.dom.indicator fun x =>
      c' (ptFun φ x) * (module μ R (ptFun φ x, x)).toReal with hw
    have hwm : Measurable w :=
      ((hc'm.comp (measurable_ptFun φ).1).mul
        (hmod.comp ((measurable_ptFun φ).1.prodMk measurable_id)).ennreal_toReal).indicator
        φ.measurableSet_dom
    have hwint : Integrable w μ := by
      refine ⟨hwm.aestronglyMeasurable, ?_⟩
      have hlin := lintegral_comp_ptInv hR φ (g := fun x => ‖c' (ptFun φ x)‖ₑ)
        (hc'm.comp (measurable_ptFun φ).1).enorm
      show ∫⁻ x, ‖w x‖ₑ ∂μ < ∞
      calc ∫⁻ x, ‖w x‖ₑ ∂μ
          = ∫⁻ x in φ.dom, ‖c' (ptFun φ x) * (module μ R (ptFun φ x, x)).toReal‖ₑ ∂μ := by
            rw [← lintegral_indicator φ.measurableSet_dom]
            congr 1; ext x
            rw [hw, enorm_indicator_eq_indicator_enorm]
        _ ≤ ∫⁻ x in φ.dom, ‖c' (ptFun φ x)‖ₑ * module μ R (ptFun φ x, x) ∂μ := by
            refine lintegral_mono fun x => ?_
            rw [enorm_mul, Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
            gcongr
            exact ENNReal.ofReal_toReal_le
        _ = ∫⁻ y in φ.cod, ‖c' (ptFun φ (ptInv φ y))‖ₑ ∂μ := hlin.symm
        _ = ∫⁻ y in φ.cod, ‖c' y‖ₑ ∂μ :=
            setLIntegral_congr_fun φ.measurableSet_cod fun y hy => by
              simp only [((ptFun_spec φ).2.1 y hy).2]
        _ ≤ ∫⁻ y, ‖c' y‖ₑ ∂μ := setLIntegral_le_lintegral _ _
        _ < ∞ := hc'.2
    -- change of variables
    have claimA : ∀ G : X → ℝ, Measurable G → ∀ C, (∀ᵐ x ∂μ, |G x| ≤ C) →
        ∫ x, c' x * φ.shiftBase G x ∂μ = ∫ x, w x * G x ∂μ := by
      intro G hG C hGC
      have e1 : (fun x => c' x * φ.shiftBase G x) =
          φ.cod.indicator (fun y => c' y * G (ptInv φ y)) := by
        ext y; rw [shiftBase_eq]
        dsimp only
        by_cases h : y ∈ φ.cod
        · rw [indicator_of_mem h, if_pos h]
        · rw [indicator_of_notMem h, if_neg h, mul_zero]
      have e2 : (fun x => w x * G x) = φ.dom.indicator (fun x =>
          (fun x => c' (ptFun φ x) * G x) x * (module μ R (ptFun φ x, x)).toReal) := by
        ext x; simp only [hw]
        by_cases h : x ∈ φ.dom
        · rw [indicator_of_mem h, indicator_of_mem h]; ring
        · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]
      have hint : Integrable (φ.dom.indicator (fun x =>
          (fun x => c' (ptFun φ x) * G x) x * (module μ R (ptFun φ x, x)).toReal)) μ := by
        rw [← e2]; exact integrable_mul_bdd hwint hG.aestronglyMeasurable hGC
      rw [e1, integral_indicator φ.measurableSet_cod, e2, integral_indicator φ.measurableSet_dom,
        ← integral_comp_ptInv hR φ hint]
      refine setIntegral_congr_fun φ.measurableSet_cod fun y hy => ?_
      simp only [((ptFun_spec φ).2.1 y hy).2]
    refine tendsto_nhds_unique (hHlim _ hF c' hc') ?_
    rw [claimA (H f) (hHm f hf) Cf (Eventually.of_forall hCf)]
    have hlim1 := hHlim f hf w hwint
    have hlim2 : Tendsto (fun k => ∫ x, c' x * Q k (φ.shiftRel f) x ∂μ -
        ∫ x, w x * Q k f x ∂μ) (U : Filter ℕ) (𝓝 0) := by
      refine Tendsto.mono_left ?_ hU
      have hdc := tendsto_integral_of_dominated_convergence (μ := μ)
        (F := fun k x => c' x * (Q k (φ.shiftRel f) x - φ.shiftBase (Q k f) x))
        (f := fun _ => 0) (fun x => |c' x| * (CF + Cf))
        (fun k => (hc'm.mul ((hmeas k _ hF).sub
          (measurable_shiftBase φ (hmeas k f hf)))).aestronglyMeasurable)
        (hc'.abs.mul_const _) (fun k => ?_) ?_
      · simp only [integral_zero] at hdc
        refine hdc.congr fun k => ?_
        rw [← claimA (Q k f) (hmeas k f hf) Cf (hQf k), ← integral_sub
          (integrable_mul_bdd hc' (hmeas k _ hF).aestronglyMeasurable (hQF k))
          (integrable_mul_bdd hc' (measurable_shiftBase φ (hmeas k f hf)).aestronglyMeasurable
            (ae_abs_shiftBase_le hR φ hCf0 (hQf k)))]
        congr 1; ext x; ring
      · filter_upwards [hQF k, ae_abs_shiftBase_le hR φ hCf0 (hQf k)] with x h1 h2
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add h1 h2)) (abs_nonneg _)
      · filter_upwards [hinv φ f hf] with x hx
        simpa using hx.const_mul (c' x)
    have h3 := hlim2.add hlim1
    rw [zero_add] at h3
    exact h3.congr fun k => sub_add_cancel _ _

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

/-- Making the points of a measurable set `M` singletons keeps a discrete measured relation discrete
measured (copied from P1). -/
theorem isDiscreteMeasured_cutOff {μ : Measure X} {E : Set (X × X)}
    (hE : IsDiscreteMeasured μ E) {M : Set X} (hM : MeasurableSet M) :
    IsDiscreteMeasured μ (cutOff E M) := by
  refine ⟨?_, ⟨fun x => Or.inr rfl, ?_, ?_⟩, fun x => ?_, fun A hA hA0 => ?_⟩
  · have h : cutOff E M = (E ∩ (Mᶜ ×ˢ Mᶜ)) ∪ {p | p.1 = p.2} := by
      ext p
      simp only [cutOff, mem_ofPred_eq, mem_union, mem_inter_iff, mem_prod, mem_compl_iff]
    rw [h]
    exact (hE.measurableSet.inter (hM.compl.prod hM.compl)).union measurableSet_diagonal
  · rintro x y (⟨h, hx, hy⟩ | h)
    · exact Or.inl ⟨hE.equivalence.symm h, hy, hx⟩
    · exact Or.inr (h : x = y).symm
  · rintro x y z (⟨h, hx, hy⟩ | h) (⟨h', hy', hz⟩ | h')
    · exact Or.inl ⟨hE.equivalence.trans h h', hx, hz⟩
    · have hyz : y = z := h'
      subst hyz
      exact Or.inl ⟨h, hx, hy⟩
    · have hxy : x = y := h
      subst hxy
      exact Or.inl ⟨h', hy', hz⟩
    · exact Or.inr ((h : x = y).trans h')
  · refine ((hE.countable_classes x).union (countable_singleton x)).mono ?_
    rintro y (⟨h, -, -⟩ | h)
    · exact Or.inl h
    · exact Or.inr (h : x = y).symm
  · refine measure_mono_null ?_ (measure_union_null hA0 (hE.quasiInvariant A hA hA0))
    rintro x ⟨y, hy, (⟨h, -, -⟩ | h)⟩
    · exact Or.inr ⟨y, hy, h⟩
    · have hxy : x = y := h
      rw [hxy]
      exact Or.inl hy

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
/-- Shifting a sum of a bounded sequence by `d` changes it by at most `2 |d| C`. -/
lemma abs_sum_shift_le (a : ℤ → ℝ) {C : ℝ} (ha : ∀ j, |a j| ≤ C) (K : ℕ) (d : ℤ) :
    |∑ j ∈ Finset.range K, a ((j : ℤ) + d) - ∑ j ∈ Finset.range K, a (j : ℤ)| ≤
      2 * |(d : ℝ)| * C := by
  have hC : 0 ≤ C := (abs_nonneg _).trans (ha 0)
  set S : ℤ → ℝ := fun d => ∑ j ∈ Finset.range K, a ((j : ℤ) + d) with hS
  have hstep : ∀ d : ℤ, |S (d + 1) - S d| ≤ 2 * C := by
    intro d
    have e := Finset.sum_range_sub (fun i : ℕ => a ((i : ℤ) + d)) K
    have e2 : S (d + 1) - S d =
        ∑ i ∈ Finset.range K, (a (((i + 1 : ℕ) : ℤ) + d) - a ((i : ℤ) + d)) := by
      simp only [hS]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast; ring_nf
    rw [e2, e]
    simp only [Nat.cast_zero, zero_add]
    calc |a ((K : ℤ) + d) - a d| ≤ |a ((K : ℤ) + d)| + |a d| := abs_sub _ _
      _ ≤ C + C := add_le_add (ha _) (ha _)
      _ = 2 * C := by ring
  have hpos : ∀ n : ℕ, |S n - S 0| ≤ 2 * n * C := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc |S ((n + 1 : ℕ) : ℤ) - S 0| ≤ |S ((n : ℤ) + 1) - S n| + |S n - S 0| := by
            push_cast; exact abs_sub_le _ _ _
        _ ≤ 2 * C + 2 * n * C := add_le_add (hstep n) ih
        _ = 2 * ((n + 1 : ℕ) : ℝ) * C := by push_cast; ring
  have hneg : ∀ n : ℕ, |S (-(n : ℤ)) - S 0| ≤ 2 * n * C := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := hstep (-((n + 1 : ℕ) : ℤ))
      have e : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by push_cast; ring
      rw [e, abs_sub_comm] at h1
      calc |S (-((n + 1 : ℕ) : ℤ)) - S 0| ≤ |S (-((n + 1 : ℕ) : ℤ)) - S (-(n : ℤ))| +
            |S (-(n : ℤ)) - S 0| := abs_sub_le _ _ _
        _ ≤ 2 * C + 2 * n * C := add_le_add h1 ih
        _ = 2 * ((n + 1 : ℕ) : ℝ) * C := by push_cast; ring
  have h0 : S 0 = ∑ j ∈ Finset.range K, a (j : ℤ) := by simp [hS]
  rw [← h0]
  show |S d - S 0| ≤ 2 * |(d : ℝ)| * C
  have hcast : ((d.natAbs : ℕ) : ℝ) = |(d : ℝ)| := by simp
  rcases Int.natAbs_eq d with hd | hd
  · have h1 := hpos d.natAbs
    rw [← hd, hcast] at h1
    exact h1
  · have h1 := hneg d.natAbs
    rw [← hd, hcast] at h1
    exact h1

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
/-- Non-singular in the strong sense: the bundle's `IsNonsingular` plus "images of null Borel sets
are null" (the planned bundle change). -/
def IsNonsingular' (μ : Measure X) (θ : X → X) : Prop :=
  IsNonsingular μ θ ∧ ∀ A, MeasurableSet A → μ A = 0 → μ (θ '' A) = 0

/-- The relation `R_θ` of Cor. 12: `(y, x) ∈ R_θ ⟺ ∃ n m, θⁿ x ~ θᵐ y`, as in the statement. -/
def tailRel (θ : X → X) (R : Set (X × X)) : Set (X × X) :=
  {p | ∃ n m : ℕ, (θ^[n] p.2, θ^[m] p.1) ∈ R}

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
theorem measurableSet_image_of_countable_fibers {θ : X → X} (hθ : Measurable θ)
    (hcount : ∀ x, (θ ⁻¹' {x}).Countable) {A : Set X} (hA : MeasurableSet A) :
    MeasurableSet (θ '' A) :=
  by
  try haveI := hθ; try haveI := hcount; try haveI := hA; first
    | exact LusinNovikov.measurableSet_image_of_countable_fibers hA
    | exact LusinNovikov.measurableSet_image_of_countable_fibers
    | exact LusinNovikov.measurableSet_image_of_countable_fibers ..
    | (apply LusinNovikov.measurableSet_image_of_countable_fibers <;> first | assumption | infer_instance)
    | simpa using LusinNovikov.measurableSet_image_of_countable_fibers

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
/-- A relation respected by `θ` is respected by its iterates. -/
theorem iterate_mem_of_resp {R : Set (X × X)} {θ : X → X}
    (hresp : ∀ x y, (x, y) ∈ R → (θ x, θ y) ∈ R) (k : ℕ) {x y : X} (h : (x, y) ∈ R) :
    (θ^[k] x, θ^[k] y) ∈ R := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact hresp _ _ ih

/-- Preimages of countable sets under a map with countable fibres are countable. -/
theorem countable_preimage_of_fibers {θ : X → X} (hcount : ∀ x, (θ ⁻¹' {x}).Countable)
    {s : Set X} (hs : s.Countable) : (θ ⁻¹' s).Countable := by
  have h : θ ⁻¹' s = ⋃ y ∈ s, θ ⁻¹' {y} := by
    ext x
    simp
  rw [h]
  exact hs.biUnion fun y _ => hcount y

theorem countable_preimage_iterate {θ : X → X} (hcount : ∀ x, (θ ⁻¹' {x}).Countable) (k : ℕ)
    {s : Set X} (hs : s.Countable) : (θ^[k] ⁻¹' s).Countable := by
  induction k with
  | zero => simpa using hs
  | succ k ih =>
    rw [Function.iterate_succ, preimage_comp]
    exact countable_preimage_of_fibers hcount ih

/-- Preimages of null Borel sets under the iterates of a non-singular map are null. -/
theorem measure_preimage_iterate_null {μ : Measure X} {θ : X → X} (hθ : IsNonsingular μ θ)
    (k : ℕ) {B : Set X} (hB : MeasurableSet B) (hB0 : μ B = 0) : μ (θ^[k] ⁻¹' B) = 0 := by
  induction k with
  | zero => simpa using hB0
  | succ k ih =>
    rw [Function.iterate_succ, preimage_comp]
    exact (hθ.2 _ ((hθ.1.iterate k) hB)).2 ih

theorem isDiscreteMeasured_tailRel {μ : Measure X} {R : Set (X × X)} (hR : IsDiscreteMeasured μ R)
    {θ : X → X} (hθ : IsNonsingular' μ θ) (hcount : ∀ x, (θ ⁻¹' {x}).Countable)
    (hresp : ∀ x y, (x, y) ∈ R → (θ x, θ y) ∈ R) : IsDiscreteMeasured μ (tailRel θ R) := by
  have hθm : Measurable θ := hθ.1.1
  have hRe := hR.equivalence
  refine ⟨?_, ⟨fun x => ⟨0, 0, hRe.refl x⟩, ?_, ?_⟩, fun x => ?_, fun A hA hA0 => ?_⟩
  · have h : tailRel θ R =
        ⋃ n, ⋃ m, (fun p : X × X => (θ^[n] p.2, θ^[m] p.1)) ⁻¹' R := by
      ext p
      simp [tailRel]
    rw [h]
    exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun m =>
      (((hθm.iterate n).comp measurable_snd).prodMk ((hθm.iterate m).comp measurable_fst))
        hR.measurableSet
  · rintro x y ⟨n, m, h⟩
    exact ⟨m, n, hRe.symm h⟩
  · rintro x y z ⟨n, m, h⟩ ⟨a, b, h'⟩
    have h1 := iterate_mem_of_resp hresp b h
    have h2 := iterate_mem_of_resp hresp n h'
    rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at h1 h2
    rw [Nat.add_comm n b] at h2
    exact ⟨n + a, b + m, hRe.trans h2 h1⟩
  · refine (countable_iUnion fun n => countable_iUnion fun m =>
      countable_preimage_iterate hcount n
        (CFWPlan.Main.IsDiscreteMeasured.countable_left hR (θ^[m] x))).mono ?_
    rintro y ⟨n, m, h⟩
    exact mem_iUnion₂.2 ⟨n, m, h⟩
  · have himg : ∀ n, MeasurableSet (θ^[n] '' A) ∧ μ (θ^[n] '' A) = 0 := by
      intro n
      induction n with
      | zero => simpa using ⟨hA, hA0⟩
      | succ n ih =>
        rw [Function.iterate_succ', image_comp]
        exact ⟨measurableSet_image_of_countable_fibers hθm hcount ih.1, hθ.2 _ ih.1 ih.2⟩
    refine measure_mono_null (t := ⋃ n, ⋃ m, θ^[m] ⁻¹' saturation R (θ^[n] '' A)) ?_
      (measure_iUnion_null fun n => measure_iUnion_null fun m => ?_)
    · rintro x ⟨y, hy, n, m, h⟩
      exact mem_iUnion₂.2 ⟨n, m, θ^[n] y, mem_image_of_mem _ hy, hRe.symm h⟩
    · exact measure_preimage_iterate_null hθ.1 m
        (CFWPlan.Main.measurableSet_saturation hR.measurableSet hRe hR.countable_classes
          (himg n).1)
        (hR.quasiInvariant _ (himg n).1 (himg n).2)

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias isDiscreteMeasured_tailRel := CFWPlan.Main.P5.isDiscreteMeasured_tailRel

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
/-- Piece data for a countable-to-one Borel map `g`: a Borel partition on whose pieces `g` is
injective, with Borel inverses and Borel images. -/
structure Pieces (g : X → X) where
  S : ℕ → Set X
  ψ : ℕ → X → X
  meas_S : ∀ n, MeasurableSet (S n)
  disj : Pairwise (Disjoint on S)
  cover : ∀ x, ∃ n, x ∈ S n
  meas_ψ : ∀ n, Measurable (ψ n)
  inv : ∀ n, ∀ x ∈ S n, ψ n (g x) = x
  meas_img : ∀ n, MeasurableSet (g '' S n)

lemma exists_pieces {g : X → X} (hg : Measurable g) (hcount : ∀ x, (g ⁻¹' {x}).Countable) :
    Nonempty (Pieces g) := by
  obtain ⟨S', hS'm, hS'inj, hS'U⟩ :=
    CFWPlan.Route.exists_injOn_cover_of_countable_fibers hg hcount
  have hSm : ∀ n, MeasurableSet (disjointed S' n) := MeasurableSet.disjointed hS'm
  have hSinj : ∀ n, InjOn g (disjointed S' n) := fun n =>
    (hS'inj n).mono (disjointed_subset S' n)
  have hpt : ∀ n, ∃ ρ : Monod.PartialTransformation (univ : Set (X × X)),
      ρ.dom = disjointed S' n ∧ ρ.cod = g '' disjointed S' n ∧
        ∀ x ∈ disjointed S' n, ptFun ρ x = g x :=
    fun n => exists_pt_of_injOn (hSm n) hg (hSinj n) (fun _ _ => mem_univ _)
  choose ρ hρd hρc hρf using hpt
  refine ⟨⟨disjointed S', (fun n => ptInv (ρ n)), hSm, disjoint_disjointed S', (fun x => ?_),
    (fun n => (measurable_ptFun (ρ n)).2), (fun n x hx => ?_), (fun n => ?_)⟩⟩
  · have : x ∈ ⋃ n, disjointed S' n := by rw [iUnion_disjointed, hS'U]; exact mem_univ x
    exact mem_iUnion.mp this
  · have hx' : x ∈ (ρ n).dom := by rw [hρd]; exact hx
    rw [← hρf n x hx]
    exact ((ptFun_spec (ρ n)).1 x hx').2.1
  · rw [← hρc]; exact (ρ n).measurableSet_cod

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
variable {g : X → X} (D : Pieces g)
open Classical in
/-- The index of the piece containing `x`. -/
noncomputable def idx (x : X) : ℕ := Nat.find (D.cover x)

lemma mem_idx (x : X) : x ∈ D.S (D.idx x) := by
  classical
  exact Nat.find_spec (D.cover x)

lemma idx_eq {x : X} {n : ℕ} (hx : x ∈ D.S n) : D.idx x = n := by
  by_contra h
  exact Set.disjoint_left.mp (D.disj h) (D.mem_idx x) hx

lemma iUnion_eq : ⋃ n, D.S n = univ :=
  eq_univ_of_forall fun x => mem_iUnion.mpr (D.cover x)

/-- The row of `x ∈ S n` moved to the base point `g x`. -/
noncomputable def pull (n : ℕ) (F : X × X → ℝ) : X × X → ℝ :=
  fun p => (g '' D.S n).indicator 1 p.1 * F (D.ψ n p.1, p.2)

lemma pull_mem {n : ℕ} {x : X} (hx : x ∈ D.S n) (F : X × X → ℝ) (z : X) :
    D.pull n F (g x, z) = F (x, z) := by
  simp only [pull]
  rw [indicator_of_mem (mem_image_of_mem g hx), Pi.one_apply, one_mul, D.inv n x hx]

lemma pull_add (n : ℕ) (F F' : X × X → ℝ) : D.pull n (F + F') = D.pull n F + D.pull n F' := by
  ext p; simp only [pull, Pi.add_apply]; ring

lemma pull_smul (n : ℕ) (c : ℝ) (F : X × X → ℝ) : D.pull n (c • F) = c • D.pull n F := by
  ext p; simp only [pull, Pi.smul_apply, smul_eq_mul]; ring

lemma measurable_pull (n : ℕ) {F : X × X → ℝ} (hF : Measurable F) : Measurable (D.pull n F) :=
  ((measurable_const.indicator (D.meas_img n)).comp measurable_fst).mul
    (hF.comp (((D.meas_ψ n).comp measurable_fst).prodMk measurable_snd))

lemma abs_pull_le (n : ℕ) {F : X × X → ℝ} {C : ℝ} (hC : 0 ≤ C) (hF : ∀ p, |F p| ≤ C) (p : X × X) :
    |D.pull n F p| ≤ C := by
  simp only [pull]
  by_cases h : p.1 ∈ g '' D.S n
  · rw [indicator_of_mem h, Pi.one_apply, one_mul]; exact hF _
  · rw [indicator_of_notMem h, zero_mul, abs_zero]; exact hC

lemma bdd_pull {R : Set (X × X)} (n : ℕ) {F : X × X → ℝ} (hF : Measurable F)
    (hFb : ∃ C, ∀ p, |F p| ≤ C) : Monod.IsBddMeasOn R (D.pull n F) := by
  obtain ⟨C, hC⟩ := hFb
  exact ⟨D.measurable_pull n hF, max C 0, fun p _ =>
    D.abs_pull_le n (le_max_right _ _) (fun q => (hC q).trans (le_max_left _ _)) p⟩

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
/-- The fibred mean `x ↦ p_{g x}(F(x, ·))` built from the pieces of `g` (CFW p. 445,
`α_k(x) = p_{θᵏ x}(F)`). -/
noncomputable def fmean (P : (X × X → ℝ) → X → ℝ) {g : X → X} (D : Pieces g)
    (F : X × X → ℝ) : X → ℝ :=
  fun x => P (D.pull (D.idx x) F) (g x)

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
lemma fmean_eq (D : Pieces g) {n : ℕ} {x : X} (hx : x ∈ D.S n) (F : X × X → ℝ) :
    fmean P D F x = P (D.pull n F) (g x) := by
  simp only [fmean, D.idx_eq hx]

/-- Transfer of a.e. statements about `P (pull n ·)` to the fibred mean. -/
lemma ae_idx (D : Pieces g) (hgq : Measure.QuasiMeasurePreserving g μ μ) {q : ℕ → X → Prop}
    (h : ∀ n, ∀ᵐ w ∂μ, q n w) : ∀ᵐ x ∂μ, q (D.idx x) (g x) := by
  have : ∀ᵐ x ∂μ, ∀ n, q n (g x) := ae_all_iff.mpr fun n => hgq.ae (h n)
  filter_upwards [this] with x hx using hx _

lemma aemeasurable_fmean (hP : Monod.IsLeftInvariantMean μ R P) (D : Pieces g)
    (hgq : Measure.QuasiMeasurePreserving g μ μ) {F : X × X → ℝ} (hF : Measurable F)
    (hFb : ∃ C, ∀ p, |F p| ≤ C) : AEMeasurable (fmean P D F) μ := by
  rw [← Measure.restrict_univ (μ := μ), ← D.iUnion_eq, aemeasurable_iUnion_iff]
  intro n
  have h1 : AEMeasurable (P (D.pull n F) ∘ g) (μ.restrict (D.S n)) :=
    ((hP.aemeasurable _ (D.bdd_pull n hF hFb)).comp_quasiMeasurePreserving hgq).restrict
  refine h1.congr ?_
  filter_upwards [ae_restrict_mem (D.meas_S n)] with x hx
  simp only [Function.comp, fmean_eq D hx]

lemma fmean_add (hP : Monod.IsLeftInvariantMean μ R P) (D : Pieces g)
    (hgq : Measure.QuasiMeasurePreserving g μ μ) {F F' : X × X → ℝ} (hF : Measurable F)
    (hF' : Measurable F') (hFb : ∃ C, ∀ p, |F p| ≤ C) (hF'b : ∃ C, ∀ p, |F' p| ≤ C) :
    fmean P D (F + F') =ᵐ[μ] fmean P D F + fmean P D F' := by
  filter_upwards [ae_idx D hgq (q := fun n w => P (D.pull n (F + F')) w =
      P (D.pull n F) w + P (D.pull n F') w) fun n => by
    rw [D.pull_add]
    exact hP.add _ _ (D.bdd_pull n hF hFb) (D.bdd_pull n hF' hF'b)] with x hx
  exact hx

lemma fmean_smul (hP : Monod.IsLeftInvariantMean μ R P) (D : Pieces g)
    (hgq : Measure.QuasiMeasurePreserving g μ μ) (c : ℝ) {F : X × X → ℝ} (hF : Measurable F)
    (hFb : ∃ C, ∀ p, |F p| ≤ C) : fmean P D (c • F) =ᵐ[μ] c • fmean P D F := by
  filter_upwards [ae_idx D hgq (q := fun n w => P (D.pull n (c • F)) w = c * P (D.pull n F) w)
    fun n => by
      rw [D.pull_smul]
      filter_upwards [hP.smul c _ (D.bdd_pull n hF hFb)] with w hw
      rw [hw]; rfl] with x hx
  exact hx

lemma fmean_abs_le (hP : Monod.IsLeftInvariantMean μ R P) (D : Pieces g)
    (hgq : Measure.QuasiMeasurePreserving g μ μ) {F : X × X → ℝ} (hF : Measurable F) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ p, |F p| ≤ C) : ∀ᵐ x ∂μ, |fmean P D F x| ≤ C := by
  filter_upwards [ae_idx D hgq (q := fun n w => |P (D.pull n F) w| ≤ C) fun n =>
    IsLeftInvariantMean.ae_abs_le hP (D.bdd_pull n hF ⟨C, hC⟩)
      fun p _ => D.abs_pull_le n hC0 hC p] with x hx
  exact hx

lemma fmean_nonneg (hP : Monod.IsLeftInvariantMean μ R P) (D : Pieces g)
    (hgq : Measure.QuasiMeasurePreserving g μ μ) {F : X × X → ℝ} (hF : Measurable F)
    (hFb : ∃ C, ∀ p, |F p| ≤ C) (hnn : ∀ x z, (g x, z) ∈ R → 0 ≤ F (x, z)) :
    ∀ᵐ x ∂μ, 0 ≤ fmean P D F x := by
  filter_upwards [ae_idx D hgq (q := fun n w => 0 ≤ P (D.pull n F) w) fun n =>
    hP.nonneg _ (D.bdd_pull n hF hFb) fun p hp => by
      simp only [Pieces.pull]
      by_cases h : p.1 ∈ g '' D.S n
      · rw [indicator_of_mem h, Pi.one_apply, one_mul]
        obtain ⟨y, hy, hyp⟩ := h
        rw [← hyp, D.inv n y hy]
        exact hnn y p.2 (by rw [hyp]; exact hp)
      · rw [indicator_of_notMem h, zero_mul]] with x hx
  exact hx

lemma fmean_one (hR : ∀ x, (x, x) ∈ R) (hP : Monod.IsLeftInvariantMean μ R P) (D : Pieces g)
    (hgq : Measure.QuasiMeasurePreserving g μ μ) : fmean P D 1 =ᵐ[μ] 1 := by
  filter_upwards [ae_idx D hgq (q := fun n w => w ∈ g '' D.S n → P (D.pull n 1) w = 1) fun n => by
    have e : D.pull n 1 = fun p => (g '' D.S n).indicator 1 p.1 * (1 : X × X → ℝ) p := by
      ext p; simp [Pieces.pull]
    filter_upwards [mul_fst_indicator hR hP bdd_one (D.meas_img n), hP.one] with w h1 h2 hw
    rw [e, h1, h2, indicator_of_mem hw]; simp] with x hx
  exact hx (mem_image_of_mem g (D.mem_idx x))

/-- **Row locality**: the fibred mean at `x` only depends on the row `F (x, ·)` on the class of
`g x`. -/
lemma fmean_local (hR : ∀ x, (x, x) ∈ R) (hP : Monod.IsLeftInvariantMean μ R P) (D : Pieces g)
    (hgq : Measure.QuasiMeasurePreserving g μ μ) {F F' : X × X → ℝ} (hF : Measurable F)
    (hF' : Measurable F') (hFb : ∃ C, ∀ p, |F p| ≤ C) (hF'b : ∃ C, ∀ p, |F' p| ≤ C)
    {A : Set X} (hA : MeasurableSet A) (h : ∀ x ∈ A, ∀ z, (g x, z) ∈ R → F (x, z) = F' (x, z)) :
    ∀ᵐ x ∂μ, x ∈ A → fmean P D F x = fmean P D F' x := by
  have key : ∀ n, ∀ᵐ w ∂μ, w ∈ (g '' D.S n) ∩ D.ψ n ⁻¹' A →
      P (D.pull n F) w = P (D.pull n F') w := by
    intro n
    set B := (g '' D.S n) ∩ D.ψ n ⁻¹' A with hBdef
    have hB : MeasurableSet B := (D.meas_img n).inter (D.meas_ψ n hA)
    have hb := D.bdd_pull (R := R) n hF hFb
    have hb' := D.bdd_pull (R := R) n hF' hF'b
    have hc := hP.congr _ _ (bdd_mul_fst (g := B.indicator (1 : X → ℝ))
      (measurable_const.indicator hB) (C := 1) (fun x => by
        by_cases hx : x ∈ B
        · rw [indicator_of_mem hx, Pi.one_apply, abs_one]
        · rw [indicator_of_notMem hx, abs_zero]; exact zero_le_one) hb)
      (bdd_mul_fst (g := B.indicator (1 : X → ℝ))
      (measurable_const.indicator hB) (C := 1) (fun x => by
        by_cases hx : x ∈ B
        · rw [indicator_of_mem hx, Pi.one_apply, abs_one]
        · rw [indicator_of_notMem hx, abs_zero]; exact zero_le_one) hb') (by
        unfold Monod.RelNull
        convert measure_empty (μ := μ)
        rw [image_eq_empty, eq_empty_iff_forall_notMem]
        rintro ⟨w, z⟩ ⟨hne, hwz⟩
        apply hne
        simp only
        by_cases hw : w ∈ B
        · obtain ⟨⟨y, hy, hyw⟩, hψ⟩ := hw
          subst hyw
          rw [D.pull_mem hy, D.pull_mem hy]
          rw [mem_preimage, D.inv n y hy] at hψ
          rw [h y hψ z hwz]
        · rw [indicator_of_notMem hw, zero_mul, zero_mul])
    filter_upwards [hc, mul_fst_indicator hR hP hb hB, mul_fst_indicator hR hP hb' hB]
      with w h1 h2 h3 hw
    rw [h2, h3, indicator_of_mem hw, Pi.one_apply, one_mul, one_mul] at h1
    exact h1
  filter_upwards [ae_idx D hgq key] with x hx hxA
  refine hx ⟨mem_image_of_mem g (D.mem_idx x), ?_⟩
  rw [mem_preimage, D.inv _ x (D.mem_idx x)]
  exact hxA

lemma fmean_zero (hP : Monod.IsLeftInvariantMean μ R P) (D : Pieces g)
    (hgq : Measure.QuasiMeasurePreserving g μ μ) : fmean P D 0 =ᵐ[μ] 0 := by
  have h := fmean_smul hP D hgq 0 (F := 0) measurable_const ⟨(0 : ℝ), fun _ => by simp⟩
  simp only [zero_smul] at h
  exact h

/-- **Transport of fibred means** between equivalent base points (the invariance of `P` under
partial transformations of `R`, applied piece by piece). -/
lemma fmean_transport (hR : IsDiscreteMeasured μ R) (hP : Monod.IsLeftInvariantMean μ R P)
    {g' : X → X} (D : Pieces g) (D' : Pieces g')
    (hg'q : Measure.QuasiMeasurePreserving g' μ μ) {h : X → X} {A : Set X} (hh : Measurable h)
    (hA : MeasurableSet A) (hhq : Measure.QuasiMeasurePreserving h (μ.restrict A) μ)
    (hgg : ∀ x ∈ A, (g x, g' (h x)) ∈ R) {F : X × X → ℝ} (hF : Measurable F)
    (hFb : ∃ C, ∀ p, |F p| ≤ C) :
    fmean P D (fun p => F (h p.1, p.2)) =ᵐ[μ.restrict A] fun x => fmean P D' F (h x) := by
  classical
  have hRe := hR.equivalence
  have hrefl : ∀ x, (x, x) ∈ R := hRe.refl
  set Fh : X × X → ℝ := fun p => F (h p.1, p.2) with hFh
  have hFhm : Measurable Fh := hF.comp ((hh.comp measurable_fst).prodMk measurable_snd)
  have hFhb : ∃ C, ∀ p, |Fh p| ≤ C := by
    obtain ⟨C, hC⟩ := hFb; exact ⟨C, fun p => hC _⟩
  have key : ∀ n i, ∀ᵐ x ∂μ.restrict A, x ∈ D.S n → h x ∈ D'.S i →
      P (D.pull n Fh) (g x) = P (D'.pull i F) (g' (h x)) := by
    intro n i
    set W : Set X := (g '' D.S n) ∩ D.ψ n ⁻¹' (A ∩ h ⁻¹' D'.S i) with hW
    have hWm : MeasurableSet W :=
      (D.meas_img n).inter (D.meas_ψ n (hA.inter (hh (D'.meas_S i))))
    set θ : X → X := fun w => if w ∈ W then g' (h (D.ψ n w)) else w with hθ
    have hθm : Measurable θ :=
      Measurable.ite hWm (hg'q.measurable.comp (hh.comp (D.meas_ψ n))) measurable_id
    have hθR : ∀ w, (w, θ w) ∈ R := by
      intro w
      simp only [hθ]
      split_ifs with hw
      · obtain ⟨⟨y, hy, hyw⟩, hψ⟩ := hw
        subst hyw
        rw [mem_preimage, D.inv n y hy] at hψ
        rw [D.inv n y hy]
        exact hgg y hψ.1
      · exact hrefl w
    have hθc : ∀ y, (θ ⁻¹' {y}).Countable := fun y =>
      (IsDiscreteMeasured.countable_left hR y).mono fun w hw => by
        simp only [mem_preimage, mem_singleton_iff] at hw
        have := hθR w
        rw [hw] at this
        exact this
    obtain ⟨T, hTm, hTinj, hTU⟩ :=
      CFWPlan.Route.exists_injOn_cover_of_countable_fibers hθm hθc
    have hk : ∀ k, ∀ᵐ x ∂μ.restrict A, x ∈ D.S n → h x ∈ D'.S i → g x ∈ T k →
        P (D.pull n Fh) (g x) = P (D'.pull i F) (g' (h x)) := by
      intro k
      obtain ⟨ρ, hρd, hρc, hρf⟩ := exists_pt_of_injOn (R := R) (hWm.inter (hTm k)) hθm
        ((hTinj k).mono inter_subset_right) (fun w _ => hθR w)
      have hfb : Monod.IsBddMeasOn R (D.pull n Fh) := D.bdd_pull n hFhm hFhb
      have hf'b : Monod.IsBddMeasOn R (D'.pull i F) := D'.bdd_pull i hF hFb
      have erow : (fun p : X × X => ρ.cod.indicator (1 : X → ℝ) p.1 *
          ρ.shiftRel (D.pull n Fh) p) =
          fun p => ρ.cod.indicator (1 : X → ℝ) p.1 * D'.pull i F p := by
        ext ⟨y, z⟩
        by_cases hy : y ∈ ρ.cod
        · rw [indicator_of_mem hy, Pi.one_apply, one_mul, one_mul, shiftRel_eq]
          dsimp only
          rw [if_pos hy]
          obtain ⟨hwdom, hfw⟩ := (ptFun_spec ρ).2.1 y hy
          rw [hρd] at hwdom
          obtain ⟨⟨⟨x, hx, hxw⟩, hψ⟩, hT⟩ := hwdom
          have hwW : ptInv ρ y ∈ W := ⟨⟨x, hx, hxw⟩, hψ⟩
          rw [mem_preimage, ← hxw, D.inv n x hx] at hψ
          have hθw : θ (ptInv ρ y) = g' (h x) := by
            simp only [hθ, if_pos hwW]
            rw [← hxw, D.inv n x hx]
          have hy' : y = g' (h x) := by rw [← hfw, hρf _ ⟨hwW, hT⟩, hθw]
          rw [← hxw, D.pull_mem hx, hy', D'.pull_mem hψ.2]
        · rw [indicator_of_notMem hy, zero_mul, zero_mul]
      have h1 := mul_fst_indicator hrefl hP (bdd_shiftRel hRe ρ hfb) ρ.measurableSet_cod
      have h2 := mul_fst_indicator hrefl hP hf'b ρ.measurableSet_cod
      have h3 := hP.invariant ρ _ hfb
      have hy : ∀ᵐ y ∂μ, y ∈ ρ.cod → P (D'.pull i F) y = P (D.pull n Fh) (ptInv ρ y) := by
        filter_upwards [h1, h2, h3] with y e1 e2 e3 hy
        rw [erow, e2, indicator_of_mem hy, Pi.one_apply, one_mul, one_mul] at e1
        rw [e1, e3, shiftBase_eq]
        dsimp only
        rw [if_pos hy]
      have hq : Measure.QuasiMeasurePreserving (fun x => g' (h x)) (μ.restrict A) μ :=
        hg'q.comp hhq
      filter_upwards [hq.ae hy, ae_restrict_mem hA] with x hx hxA hxS hhx hgx
      have hgxW : g x ∈ W :=
        ⟨mem_image_of_mem g hxS, by rw [mem_preimage, D.inv n x hxS]; exact ⟨hxA, hhx⟩⟩
      have hgxd : g x ∈ ρ.dom := by rw [hρd]; exact ⟨hgxW, hgx⟩
      have hpf : ptFun ρ (g x) = g' (h x) := by
        rw [hρf _ ⟨hgxW, hgx⟩]
        simp only [hθ, if_pos hgxW, D.inv n x hxS]
      have hcod : g' (h x) ∈ ρ.cod := by rw [← hpf]; exact ((ptFun_spec ρ).1 _ hgxd).1
      have hinv : ptInv ρ (g' (h x)) = g x := by
        rw [← hpf]; exact ((ptFun_spec ρ).1 _ hgxd).2.1
      rw [hx hcod, hinv]
    filter_upwards [ae_all_iff.mpr hk] with x hx hxS hhx
    have : g x ∈ ⋃ k, T k := by rw [hTU]; exact mem_univ _
    obtain ⟨k, hk'⟩ := mem_iUnion.mp this
    exact hx k hxS hhx hk'
  filter_upwards [ae_all_iff.mpr fun n => ae_all_iff.mpr (key n)] with x hx
  rw [fmean_eq D (D.mem_idx x), fmean_eq D' (D'.mem_idx (h x))]
  exact hx _ _ (D.mem_idx x) (D'.mem_idx (h x))

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
/-- Averages of a sequence bounded by `C` are bounded by `C`. -/
lemma abs_avg_le (t : ℕ → ℝ) {C : ℝ} (ht : ∀ j, |t j| ≤ C) (k : ℕ) :
    |(∑ j ∈ Finset.range (k + 1), t j) / ((k : ℝ) + 1)| ≤ C := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [abs_div, abs_of_pos hk, div_le_iff₀ hk]
  calc |∑ j ∈ Finset.range (k + 1), t j| ≤ ∑ j ∈ Finset.range (k + 1), |t j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (k + 1), C := Finset.sum_le_sum fun j _ => ht j
    _ = C * ((k : ℝ) + 1) := by simp; ring

/-- Two bounded sequences with `a j = b (j - n + m)` for `j ≥ n` have partial sums at bounded
distance ("the sequence `α` is shifted", CFW p. 445). -/
lemma abs_sum_shift_nat (a b : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C) (ha : ∀ j, |a j| ≤ C)
    (hb : ∀ j, |b j| ≤ C) (n m : ℕ) (hab : ∀ j, n ≤ j → a j = b (j - n + m)) (K : ℕ) :
    |∑ j ∈ Finset.range K, a j - ∑ j ∈ Finset.range K, b j| ≤
      2 * n * C + 2 * |(m : ℝ) - n| * C := by
  set b' : ℤ → ℝ := fun i => if 0 ≤ i then b i.toNat else 0 with hb'def
  have hb' : ∀ i, |b' i| ≤ C := fun i => by
    simp only [hb'def]
    split_ifs
    · exact hb _
    · rw [abs_zero]; exact hC
  set d : ℤ := (m : ℤ) - n with hd
  have hshift := abs_sum_shift_le b' hb' K d
  have hb'0 : ∀ j : ℕ, b' j = b j := fun j => by simp [hb'def]
  have hb'd : ∀ j : ℕ, n ≤ j → b' ((j : ℤ) + d) = b (j - n + m) := by
    intro j hj
    have e : (j : ℤ) + d = ((j - n + m : ℕ) : ℤ) := by
      rw [hd]; push_cast [Nat.cast_sub hj]; ring
    simp only [hb'def]
    rw [e, if_pos (Nat.cast_nonneg _), Int.toNat_natCast]
  have hfirst : ∀ K : ℕ, |∑ j ∈ Finset.range K, (a j - b' ((j : ℤ) + d))| ≤
      2 * ((min K n : ℕ) : ℝ) * C := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ]
      by_cases hK : n ≤ K
      · rw [hab K hK, ← hb'd K hK, sub_self, add_zero]
        refine ih.trans ?_
        gcongr
        exact Nat.le_succ K
      · have e : min (K + 1) n = min K n + 1 := by omega
        rw [e, Nat.cast_succ]
        calc |∑ j ∈ Finset.range K, (a j - b' ((j : ℤ) + d)) + (a K - b' ((K : ℤ) + d))|
            ≤ |∑ j ∈ Finset.range K, (a j - b' ((j : ℤ) + d))| + |a K - b' ((K : ℤ) + d)| :=
              abs_add_le _ _
          _ ≤ 2 * ((min K n : ℕ) : ℝ) * C + (C + C) :=
              add_le_add ih ((abs_sub _ _).trans (add_le_add (ha K) (hb' _)))
          _ = 2 * (((min K n : ℕ) : ℝ) + 1) * C := by ring
  have hsplit : ∑ j ∈ Finset.range K, a j - ∑ j ∈ Finset.range K, b j =
      ∑ j ∈ Finset.range K, (a j - b' ((j : ℤ) + d)) +
        (∑ j ∈ Finset.range K, b' ((j : ℤ) + d) - ∑ j ∈ Finset.range K, b' (j : ℤ)) := by
    rw [Finset.sum_sub_distrib]
    simp only [hb'0]
    ring
  have hdc : |(d : ℝ)| = |(m : ℝ) - n| := by rw [hd]; push_cast; rfl
  rw [hsplit]
  calc _ ≤ |∑ j ∈ Finset.range K, (a j - b' ((j : ℤ) + d))| +
        |∑ j ∈ Finset.range K, b' ((j : ℤ) + d) - ∑ j ∈ Finset.range K, b' (j : ℤ)| :=
        abs_add_le _ _
    _ ≤ 2 * n * C + 2 * |(m : ℝ) - n| * C := by
        refine add_le_add ((hfirst K).trans ?_) (hdc ▸ hshift)
        gcongr
        exact_mod_cast min_le_right K n

/-- `φ⁻¹` is non-singular on the codomain of a partial transformation. -/
lemma qmp_ptInv {μ : Measure X} {R : Set (X × X)} (hR : IsDiscreteMeasured μ R)
    (φ : Monod.PartialTransformation R) {A : Set X} (hAc : A ⊆ φ.cod) :
    Measure.QuasiMeasurePreserving (ptInv φ) (μ.restrict A) μ := by
  refine ⟨(measurable_ptFun φ).2, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.map_apply (measurable_ptFun φ).2 hs,
    Measure.restrict_apply ((measurable_ptFun φ).2 hs)]
  refine measure_mono_null ?_ (IsDiscreteMeasured.qi hR s h0)
  rintro y ⟨hy1, hy2⟩
  exact ⟨ptInv φ y, hy1, ptInv_mem_R φ (hAc hy2)⟩

/-- **`R_θ` is amenable** (CFW p. 445: `p'_x(F) = ρ(α)`, `α_k = p_{θᵏ x}(F)`, with the invariant
mean `ρ` on `ℓ∞(ℕ)` replaced by Cesàro averages and a weak limit). -/
theorem isAmenableRel_tailRel {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (hamen : Monod.IsAmenableRel μ R) {θ : X → X}
    (hθ : IsNonsingular' μ θ) (hcount : ∀ x, (θ ⁻¹' {x}).Countable)
    (hresp : ∀ x y, (x, y) ∈ R → (θ x, θ y) ∈ R) : Monod.IsAmenableRel μ (tailRel θ R) := by
  classical
  obtain ⟨P, hP⟩ := hamen
  have hRe := hR.equivalence
  have hrefl : ∀ x, (x, x) ∈ R := hRe.refl
  have hT := isDiscreteMeasured_tailRel hR hθ hcount hresp
  set T := tailRel θ R with hTdef
  have hTe := hT.equivalence
  have hTm := hT.measurableSet
  have hθm : Measurable θ := hθ.1.1
  have hθq : Measure.QuasiMeasurePreserving θ μ μ := by
    refine ⟨hθm, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
    rw [Measure.map_apply hθm hs]
    exact (hθ.1.2 s hs).mpr h0
  have hit_q : ∀ j, Measure.QuasiMeasurePreserving θ^[j] μ μ := hθq.iterate
  have hit_m : ∀ j, Measurable θ^[j] := fun j => hθm.iterate j
  have hit_c : ∀ j x, (θ^[j] ⁻¹' {x}).Countable := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [Function.iterate_succ, Set.preimage_comp]
      have e : θ ⁻¹' (θ^[j] ⁻¹' {x}) = ⋃ y ∈ θ^[j] ⁻¹' {x}, θ ⁻¹' {y} := by
        ext w; simp
      rw [e]
      exact (ih x).biUnion fun y _ => hcount y
  have hit_R : ∀ j x y, (x, y) ∈ R → (θ^[j] x, θ^[j] y) ∈ R := by
    intro j
    induction j with
    | zero => intro x y h; simpa using h
    | succ j ih =>
      intro x y h
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact hresp _ _ (ih x y h)
  have hRT : ∀ j x z, (θ^[j] x, z) ∈ R → (x, z) ∈ T := fun j x z h => ⟨0, j, hRe.symm h⟩
  have hk : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  -- the fibred means along the iterates
  have hD : ∀ j, Nonempty (Pieces (θ^[j])) := fun j => exists_pieces (hit_m j) (hit_c j)
  let D : ∀ j, Pieces (θ^[j]) := fun j => Classical.choice (hD j)
  let F0 : (X × X → ℝ) → X × X → ℝ := fun F => T.indicator F
  let α : ℕ → (X × X → ℝ) → X → ℝ := fun j F => fmean P (D j) (F0 F)
  let avg : ℕ → (X × X → ℝ) → X → ℝ := fun k F x =>
    (∑ j ∈ Finset.range (k + 1), α j F x) / ((k : ℝ) + 1)
  have hF0m : ∀ F, Monod.IsBddMeasOn T F → Measurable (F0 F) := fun F hF => hF.1.indicator hTm
  have hF0b : ∀ F C, 0 ≤ C → (∀ p ∈ T, |F p| ≤ C) → ∀ p, |F0 F p| ≤ C := by
    intro F C hC0 hC p
    simp only [F0]
    by_cases hp : p ∈ T
    · rw [indicator_of_mem hp]; exact hC p hp
    · rw [indicator_of_notMem hp, abs_zero]; exact hC0
  have hF0b' : ∀ F, Monod.IsBddMeasOn T F → ∃ C, ∀ p, |F0 F p| ≤ C := fun F hF => by
    obtain ⟨C, hC0, hC⟩ := IsBddMeasOn.exists_nonneg hF
    exact ⟨C, hF0b F C hC0 hC⟩
  have havg_ae : ∀ k F, Monod.IsBddMeasOn T F → AEMeasurable (avg k F) μ := by
    intro k F hF
    have h1 : AEMeasurable (∑ j ∈ Finset.range (k + 1), α j F) μ :=
      Finset.aemeasurable_sum _ fun j _ =>
        aemeasurable_fmean hP (D j) (hit_q j) (hF0m F hF) (hF0b' F hF)
    refine (h1.div_const ((k : ℝ) + 1)).congr (Eventually.of_forall fun x => ?_)
    simp only [avg, Finset.sum_apply]
  let Q : ℕ → (X × X → ℝ) → X → ℝ := fun k F =>
    if h : Monod.IsBddMeasOn T F then (havg_ae k F h).mk _ else 0
  have hQ : ∀ k F (h : Monod.IsBddMeasOn T F), Q k F =ᵐ[μ] avg k F := fun k F h => by
    simp only [Q, dif_pos h]; exact (havg_ae k F h).ae_eq_mk.symm
  refine isAmenableRel_of_asymptotic hT Q ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- measurability
    intro k F hF
    simp only [Q, dif_pos hF]
    exact (havg_ae k F hF).measurable_mk
  · -- bounds
    intro k F C hF hC
    rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
    · exact Eventually.of_forall fun x => isEmptyElim x
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (x₀, x₀) (hTe.refl x₀))
    filter_upwards [hQ k F hF, ae_all_iff.mpr fun j =>
      fmean_abs_le hP (D j) (hit_q j) (hF0m F hF) hC0 (hF0b F C hC0 hC)] with x h1 h2
    rw [h1]
    exact abs_avg_le (fun j => α j F x) h2 k
  · -- additivity
    intro k F F' hF hF'
    have hFF := bdd_add hF hF'
    have e : F0 (F + F') = F0 F + F0 F' := Set.indicator_add' T F F'
    filter_upwards [hQ k _ hFF, hQ k F hF, hQ k F' hF', ae_all_iff.mpr fun j =>
      fmean_add hP (D j) (hit_q j) (hF0m F hF) (hF0m F' hF') (hF0b' F hF) (hF0b' F' hF')]
      with x h1 h2 h3 h4
    rw [Pi.add_apply, h1, h2, h3]
    simp only [avg]
    rw [← add_div, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [α]
    rw [e]
    exact h4 j
  · -- homogeneity
    intro k c F hF
    have hcF := bdd_smul c hF
    have e : F0 (c • F) = c • F0 F := by
      ext p; simp only [F0, Pi.smul_apply]
      by_cases hp : p ∈ T
      · rw [indicator_of_mem hp, indicator_of_mem hp]; rfl
      · rw [indicator_of_notMem hp, indicator_of_notMem hp, smul_zero]
    filter_upwards [hQ k _ hcF, hQ k F hF, ae_all_iff.mpr fun j =>
      fmean_smul hP (D j) (hit_q j) c (hF0m F hF) (hF0b' F hF)] with x h1 h2 h3
    rw [Pi.smul_apply, h1, h2, smul_eq_mul]
    simp only [avg]
    rw [mul_div_assoc', Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [α]
    rw [e]
    exact h3 j
  · -- positivity
    intro k F hF hnn
    filter_upwards [hQ k F hF, ae_all_iff.mpr fun j =>
      fmean_nonneg hP (D j) (hit_q j) (hF0m F hF) (hF0b' F hF) fun x z _ => by
        simp only [F0]
        by_cases hp : (x, z) ∈ T
        · rw [indicator_of_mem hp]; exact hnn _ hp
        · rw [indicator_of_notMem hp]] with x h1 h2
    rw [h1]
    exact div_nonneg (Finset.sum_nonneg fun j _ => h2 j) (hk k).le
  · -- unit
    intro k
    have hloc : ∀ j, ∀ᵐ x ∂μ, α j 1 x = 1 := by
      intro j
      have h1 := fmean_local hrefl hP (D j) (hit_q j) (F := F0 1) (F' := 1)
        (hF0m 1 bdd_one) measurable_const (hF0b' 1 bdd_one) ⟨1, fun _ => by simp⟩
        MeasurableSet.univ fun x _ z hz => by
          simp only [F0]
          rw [indicator_of_mem (hRT j x z hz)]
      filter_upwards [h1, fmean_one hrefl hP (D j) (hit_q j)] with x h2 h3
      simp only [α]
      rw [h2 (mem_univ x), h3, Pi.one_apply]
    filter_upwards [hQ k 1 bdd_one, ae_all_iff.mpr hloc] with x h1 h2
    rw [h1, Pi.one_apply]
    simp only [avg]
    rw [Finset.sum_congr rfl fun j _ => h2 j, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one]
    push_cast
    exact div_self (hk k).ne'
  · -- null sets
    intro k F F' hF hF' hnull
    set E := Prod.fst '' ({p | F p ≠ F' p} ∩ T) with hE
    have hEc : ∀ᵐ x ∂μ, x ∈ (toMeasurable μ E)ᶜ := by
      rw [ae_iff]
      simp only [mem_compl_iff, not_not, ofPred_mem_eq]
      rw [measure_toMeasurable]
      exact hnull
    have hloc : ∀ j, ∀ᵐ x ∂μ, x ∈ (toMeasurable μ E)ᶜ → α j F x = α j F' x := fun j =>
      fmean_local hrefl hP (D j) (hit_q j) (hF0m F hF) (hF0m F' hF') (hF0b' F hF) (hF0b' F' hF')
        (measurableSet_toMeasurable μ E).compl fun x hx z hz => by
          have hxz : (x, z) ∈ T := hRT j x z hz
          simp only [F0]
          rw [indicator_of_mem hxz, indicator_of_mem hxz]
          by_contra hne
          exact hx (subset_toMeasurable μ E ⟨(x, z), ⟨hne, hxz⟩, rfl⟩)
    filter_upwards [hQ k F hF, hQ k F' hF', hEc, ae_all_iff.mpr hloc] with x h1 h2 h3 h4
    rw [h1, h2]
    simp only [avg]
    congr 1
    exact Finset.sum_congr rfl fun j _ => h4 j h3
  · -- asymptotic invariance
    intro φ F hF
    have hG := bdd_shiftRel hTe φ hF
    obtain ⟨C, hC0, hC⟩ := IsBddMeasOn.exists_nonneg hF
    have hGC : ∀ p ∈ T, |φ.shiftRel F p| ≤ C := by
      intro p hp
      rw [shiftRel_eq]
      dsimp only
      split_ifs with h
      · exact hC _ (hTe.trans (ptInv_mem_R φ h) hp)
      · rw [abs_zero]; exact hC0
    have hQG : ∀ᵐ x ∂μ, ∀ k, Q k (φ.shiftRel F) x = avg k (φ.shiftRel F) x :=
      ae_all_iff.mpr fun k => hQ k _ hG
    have hQF : ∀ᵐ x ∂μ, x ∈ φ.cod → ∀ k, Q k F (ptInv φ x) = avg k F (ptInv φ x) :=
      ae_ptInv hT φ (ae_all_iff.mpr fun k => hQ k F hF)
    have hbG : ∀ᵐ x ∂μ, ∀ j, |α j (φ.shiftRel F) x| ≤ C := ae_all_iff.mpr fun j =>
      fmean_abs_le hP (D j) (hit_q j) (hF0m _ hG) hC0 (hF0b _ C hC0 hGC)
    have hbF : ∀ᵐ x ∂μ, x ∈ φ.cod → ∀ j, |α j F (ptInv φ x)| ≤ C := ae_ptInv hT φ
      (ae_all_iff.mpr fun j => fmean_abs_le hP (D j) (hit_q j) (hF0m F hF) hC0 (hF0b F C hC0 hC))
    -- off the codomain, the means of `F^φ` vanish
    have hoff : ∀ᵐ x ∂μ, ∀ j, x ∉ φ.cod → α j (φ.shiftRel F) x = 0 := by
      refine ae_all_iff.mpr fun j => ?_
      have h1 := fmean_local hrefl hP (D j) (hit_q j) (F := F0 (φ.shiftRel F)) (F' := 0)
        (hF0m _ hG) measurable_const (hF0b' _ hG) ⟨0, fun _ => by simp⟩
        φ.measurableSet_cod.compl fun x hx z _ => by
          simp only [F0, Pi.zero_apply]
          by_cases hp : (x, z) ∈ T
          · rw [indicator_of_mem hp, shiftRel_eq]
            dsimp only
            rw [if_neg hx]
          · rw [indicator_of_notMem hp]
      filter_upwards [h1, fmean_zero hP (D j) (hit_q j)] with x h2 h3 hx
      simp only [α]
      rw [h2 hx, h3, Pi.zero_apply]
    -- on the codomain, the means of `F^φ` are those of `F`, shifted
    have hon : ∀ n m j : ℕ, ∀ᵐ x ∂μ, n ≤ j → x ∈ φ.cod →
        (θ^[n] x, θ^[m] (ptInv φ x)) ∈ R → α j (φ.shiftRel F) x = α (j - n + m) F (ptInv φ x) := by
      intro n m j
      by_cases hnj : n ≤ j
      swap
      · exact Eventually.of_forall fun x h => absurd h hnj
      set A : Set X := {x | x ∈ φ.cod ∧ (θ^[n] x, θ^[m] (ptInv φ x)) ∈ R} with hAdef
      have hAm : MeasurableSet A := φ.measurableSet_cod.inter (hR.measurableSet.preimage
        ((hit_m n).prodMk ((hit_m m).comp (measurable_ptFun φ).2)))
      have hhq : Measure.QuasiMeasurePreserving (ptInv φ) (μ.restrict A) μ :=
        qmp_ptInv hT φ fun x hx => hx.1
      have hgg : ∀ x ∈ A, (θ^[j] x, θ^[j - n + m] (ptInv φ x)) ∈ R := by
        intro x hx
        have h1 := hit_R (j - n) _ _ hx.2
        rw [← Function.iterate_add_apply, ← Function.iterate_add_apply,
          Nat.sub_add_cancel hnj] at h1
        exact h1
      have htr := fmean_transport hR hP (D j) (D (j - n + m)) (hit_q _)
        (measurable_ptFun φ).2 hAm hhq hgg (hF0m F hF) (hF0b' F hF)
      have hFhm : Measurable fun p : X × X => F0 F (ptInv φ p.1, p.2) :=
        (hF0m F hF).comp (((measurable_ptFun φ).2.comp measurable_fst).prodMk measurable_snd)
      have hFhb : ∃ C, ∀ p : X × X, |F0 F (ptInv φ p.1, p.2)| ≤ C := by
        obtain ⟨C', hC'⟩ := hF0b' F hF; exact ⟨C', fun p => hC' _⟩
      have hloc := fmean_local hrefl hP (D j) (hit_q j) (F := F0 (φ.shiftRel F))
        (F' := fun p : X × X => F0 F (ptInv φ p.1, p.2)) (hF0m _ hG) hFhm (hF0b' _ hG) hFhb
        φ.measurableSet_cod fun x hx z hz => by
          have hxz : (x, z) ∈ T := hRT j x z hz
          have hxz' : (ptInv φ x, z) ∈ T := hTe.trans (ptInv_mem_R φ hx) hxz
          simp only [F0]
          rw [indicator_of_mem hxz, indicator_of_mem hxz', shiftRel_eq]
          dsimp only
          rw [if_pos hx]
      rw [Filter.EventuallyEq, ae_restrict_iff' hAm] at htr
      filter_upwards [htr, hloc] with x h1 h2 _ hxc hxR
      simp only [α]
      rw [h2 hxc, h1 ⟨hxc, hxR⟩]
    have hon' : ∀ᵐ x ∂μ, ∀ n m j : ℕ, n ≤ j → x ∈ φ.cod →
        (θ^[n] x, θ^[m] (ptInv φ x)) ∈ R → α j (φ.shiftRel F) x = α (j - n + m) F (ptInv φ x) :=
      ae_all_iff.mpr fun n => ae_all_iff.mpr fun m => ae_all_iff.mpr fun j => hon n m j
    filter_upwards [hQG, hQF, hbG, hbF, hoff, hon'] with x hQGx hQFx hbGx hbFx hoffx honx
    by_cases hxc : x ∈ φ.cod
    · obtain ⟨n, m, hnm⟩ : (ptInv φ x, x) ∈ T := ptInv_mem_R φ hxc
      have hab : ∀ j, n ≤ j → α j (φ.shiftRel F) x = α (j - n + m) F (ptInv φ x) :=
        fun j hj => honx n m j hj hxc hnm
      refine squeeze_zero_norm
        (a := fun k : ℕ => (2 * n * C + 2 * |(m : ℝ) - n| * C) / ((k : ℝ) + 1)) (fun k => ?_) ?_
      · rw [hQGx k, shiftBase_eq]
        dsimp only
        rw [if_pos hxc, hQFx hxc k]
        simp only [avg]
        rw [← sub_div, Real.norm_eq_abs, abs_div, abs_of_pos (hk k)]
        exact div_le_div_of_nonneg_right (abs_sum_shift_nat (fun j => α j (φ.shiftRel F) x)
          (fun j => α j F (ptInv φ x)) hC0 hbGx (hbFx hxc) n m hab (k + 1)) (hk k).le
      · have := (tendsto_const_div_atTop_nhds_zero_nat
          (2 * n * C + 2 * |(m : ℝ) - n| * C)).comp (tendsto_add_atTop_nat 1)
        refine this.congr fun k => ?_
        simp
    · refine tendsto_const_nhds.congr fun k => ?_
      rw [hQGx k, shiftBase_eq]
      dsimp only
      rw [if_neg hxc, sub_zero]
      simp only [avg]
      rw [Finset.sum_eq_zero fun j _ => hoffx j hxc, zero_div]

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias isAmenableRel_tailRel := CFWPlan.Main.P3.isAmenableRel_tailRel

/-- **Corollary 12, strengthened** (CFW p. 444–445). *Proof:* **Theorem 10** both ways (milestone
`isHyperfinite_iff_isAmenableRel`): `R` amenable, `isAmenableRel_tailRel`, then hyperfinite.
*Size:* 10 (proved). -/
theorem cor12 {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)} (hR : IsDiscreteMeasured μ R)
    (hhyp : IsHyperfinite μ R) {θ : X → X} (hθ : IsNonsingular' μ θ)
    (hcount : ∀ x, (θ ⁻¹' {x}).Countable) (hresp : ∀ x y, (x, y) ∈ R → (θ x, θ y) ∈ R) :
    IsHyperfinite μ (tailRel θ R) ∧ IsDiscreteMeasured μ (tailRel θ R) := by
  have hD := isDiscreteMeasured_tailRel hR hθ hcount hresp
  exact ⟨(ConnesFeldmanWeiss.isHyperfinite_iff_isAmenableRel _ _ hD).2 (isAmenableRel_tailRel hR ((ConnesFeldmanWeiss.isHyperfinite_iff_isAmenableRel _ _ hR).1 hhyp) hθ hcount hresp), hD⟩

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
/-- For a finite measure: a null Borel set `D ⊇ B ∪ θ⁻¹ B` off which `θ` sends null sets to null
sets (fibres of `θ` countable over the complement of `B`). Lusin–Novikov pieces on which `θ` is
injective, and on each the singular part of `μ` against `θ_*(μ|piece)`. -/
theorem exists_null_image_good_finite {μ : Measure X} [IsFiniteMeasure μ] {θ : X → X}
    (hθ : Measurable θ) {B : Set X} (hB : MeasurableSet B) (hB0 : μ B = 0)
    (hθB : μ (θ ⁻¹' B) = 0) (hcount : ∀ y, y ∉ B → (θ ⁻¹' {y}).Countable) :
    ∃ D : Set X, MeasurableSet D ∧ μ D = 0 ∧ B ⊆ D ∧ θ ⁻¹' B ⊆ D ∧
      ∀ A : Set X, A ∩ D = ∅ → μ A = 0 → μ (θ '' A) = 0 := by
  classical
  let θ₁ : X → X := (θ ⁻¹' B).piecewise id θ
  have hθ₁ : Measurable θ₁ := Measurable.piecewise (hθ hB) measurable_id hθ
  have hθ₁c : ∀ y, (θ₁ ⁻¹' {y}).Countable := by
    intro y
    by_cases hy : y ∈ B
    · refine (countable_singleton y).mono fun x hx => ?_
      have hx' : θ₁ x = y := hx
      by_cases hxB : θ x ∈ B
      · have : θ₁ x = x := piecewise_eq_of_mem _ _ _ hxB
        rw [this] at hx'
        exact hx'
      · have : θ₁ x = θ x := piecewise_eq_of_notMem _ _ _ hxB
        rw [this] at hx'
        exact absurd (hx' ▸ hy) hxB
    · refine ((hcount y hy).union (countable_singleton y)).mono fun x hx => ?_
      have hx' : θ₁ x = y := hx
      by_cases hxB : θ x ∈ B
      · have : θ₁ x = x := piecewise_eq_of_mem _ _ _ hxB
        rw [this] at hx'
        exact Or.inr hx'
      · have : θ₁ x = θ x := piecewise_eq_of_notMem _ _ _ hxB
        rw [this] at hx'
        exact Or.inl hx'
  obtain ⟨S, hS, hinj, hcov⟩ :=
    CFWPlan.Route.PartB.exists_injOn_cover_of_countable_fibers hθ₁ hθ₁c
  let S' : ℕ → Set X := fun k => S k ∩ (θ ⁻¹' B)ᶜ
  have hS' : ∀ k, MeasurableSet (S' k) := fun k => (hS k).inter (hθ hB).compl
  have hinj' : ∀ k, InjOn θ (S' k) := by
    intro k x hx y hy hxy
    have h1 : θ₁ x = θ x := piecewise_eq_of_notMem _ _ _ hx.2
    have h2 : θ₁ y = θ y := piecewise_eq_of_notMem _ _ _ hy.2
    exact hinj k hx.1 hy.1 (by rw [h1, h2, hxy])
  have hsing : ∀ k, μ.singularPart ((μ.restrict (S' k)).map θ) ⟂ₘ (μ.restrict (S' k)).map θ :=
    fun k => Measure.mutuallySingular_singularPart _ _
  have hZm : ∀ k, MeasurableSet (hsing k).nullSet := fun k => (hsing k).measurableSet_nullSet
  have hDk0 : ∀ k, μ (S' k ∩ θ ⁻¹' ((hsing k).nullSet)ᶜ) = 0 := by
    intro k
    have h := (hsing k).measure_compl_nullSet
    rw [Measure.map_apply hθ (hZm k).compl, Measure.restrict_apply (hθ (hZm k).compl)] at h
    rw [inter_comm]
    exact h
  refine ⟨B ∪ θ ⁻¹' B ∪ ⋃ k, (S' k ∩ θ ⁻¹' ((hsing k).nullSet)ᶜ), ?_, ?_,
    fun x hx => Or.inl (Or.inl hx), fun x hx => Or.inl (Or.inr hx), ?_⟩
  · exact (hB.union (hθ hB)).union
      (MeasurableSet.iUnion fun k => (hS' k).inter (hθ (hZm k).compl))
  · exact measure_union_null (measure_union_null hB0 hθB) (measure_iUnion_null hDk0)
  intro A hAD hA0
  have hAD' : ∀ x ∈ A, x ∉ B ∪ θ ⁻¹' B ∪ ⋃ k, (S' k ∩ θ ⁻¹' ((hsing k).nullSet)ᶜ) :=
    fun x hx hxD => (eq_empty_iff_forall_notMem.1 hAD) x ⟨hx, hxD⟩
  have hAcov : A ⊆ ⋃ k, A ∩ S' k := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.1 (hcov ▸ mem_univ x : x ∈ ⋃ k, S k)
    exact mem_iUnion.2 ⟨k, hx, hk, fun h => hAD' x hx (Or.inl (Or.inr h))⟩
  refine measure_mono_null (image_mono hAcov) ?_
  rw [image_iUnion]
  refine measure_iUnion_null fun k => ?_
  set Z := (hsing k).nullSet
  set H := toMeasurable μ (A ∩ S' k) ∩ S' k ∩ (θ ⁻¹' Zᶜ)ᶜ with hHdef
  have hHm : MeasurableSet H :=
    ((measurableSet_toMeasurable _ _).inter (hS' k)).inter (hθ (hZm k).compl).compl
  have hAH : A ∩ S' k ⊆ H := fun x hx =>
    ⟨⟨subset_toMeasurable _ _ hx, hx.2⟩,
      fun h => hAD' x hx.1 (Or.inr (mem_iUnion.2 ⟨k, hx.2, h⟩))⟩
  have hH0 : μ H = 0 := measure_mono_null (inter_subset_left.trans inter_subset_left)
    (by rw [measure_toMeasurable]; exact measure_mono_null inter_subset_left hA0)
  have hHS : H ⊆ S' k := inter_subset_left.trans inter_subset_right
  have hθH : MeasurableSet (θ '' H) := hHm.image_of_measurable_injOn hθ ((hinj' k).mono hHS)
  have hθHZ : θ '' H ⊆ Z := by
    rintro _ ⟨x, hx, rfl⟩
    by_contra h
    exact hx.2 h
  have hνH : ((μ.restrict (S' k)).map θ) (θ '' H) = 0 := by
    rw [Measure.map_apply hθ hθH, Measure.restrict_apply (hθ hθH)]
    refine measure_mono_null ?_ hH0
    rintro x ⟨⟨y, hy, hyx⟩, hxS⟩
    have : y = x := hinj' k (hHS hy) hxS hyx
    exact this ▸ hy
  refine measure_mono_null (image_mono hAH) ?_
  calc μ (θ '' H) = (μ.singularPart ((μ.restrict (S' k)).map θ) +
        ((μ.restrict (S' k)).map θ).withDensity (μ.rnDeriv ((μ.restrict (S' k)).map θ)))
          (θ '' H) :=
        congrArg (fun m : Measure X => m (θ '' H))
          (Measure.haveLebesgueDecomposition_add μ ((μ.restrict (S' k)).map θ))
    _ = 0 := by
        rw [Measure.add_apply, measure_mono_null hθHZ (hsing k).measure_nullSet,
          withDensity_absolutelyContinuous _ _ hνH, add_zero]

/-- The same for a σ-finite measure, through the equivalent finite measure `μ.toFinite`. -/
theorem exists_null_image_good {μ : Measure X} [SigmaFinite μ] {θ : X → X}
    (hθ : IsNonsingular μ θ) {B : Set X} (hB : MeasurableSet B) (hB0 : μ B = 0)
    (hcount : ∀ y, y ∉ B → (θ ⁻¹' {y}).Countable) :
    ∃ D : Set X, MeasurableSet D ∧ μ D = 0 ∧ B ⊆ D ∧ θ ⁻¹' B ⊆ D ∧
      ∀ A : Set X, A ∩ D = ∅ → μ A = 0 → μ (θ '' A) = 0 := by
  have h1 := absolutelyContinuous_toFinite μ
  have h2 := toFinite_absolutelyContinuous μ
  obtain ⟨D, hD, hD0, hBD, hθBD, hgood⟩ := exists_null_image_good_finite (μ := μ.toFinite) hθ.1 hB
    (h2 hB0) (h2 ((hθ.2 B hB).2 hB0)) hcount
  exact ⟨D, hD, h1 hD0, hBD, hθBD, fun A hAD hA0 => h1 (hgood A hAD (h2 hA0))⟩

/-- **A conull forward-invariant Borel set on which `θ` sends null sets to null sets**, and whose
image avoids a given null set `B` (over whose complement the fibres of `θ` are countable). -/
theorem exists_forward_invariant {μ : Measure X} [SigmaFinite μ] {θ : X → X}
    (hθ : IsNonsingular μ θ) {B : Set X} (hB : MeasurableSet B) (hB0 : μ B = 0)
    (hcount : ∀ y, y ∉ B → (θ ⁻¹' {y}).Countable) :
    ∃ X₀ : Set X, MeasurableSet X₀ ∧ μ X₀ᶜ = 0 ∧ (∀ x ∈ X₀, θ x ∈ X₀) ∧
      (∀ x ∈ X₀, θ x ∉ B) ∧ ∀ A ⊆ X₀, μ A = 0 → μ (θ '' A) = 0 := by
  obtain ⟨D, hD, hD0, hBD, hθBD, hgood⟩ := exists_null_image_good hθ hB hB0 hcount
  refine ⟨⋂ j, θ^[j] ⁻¹' Dᶜ, MeasurableSet.iInter fun j => (hθ.1.iterate j) hD.compl, ?_, ?_,
    ?_, ?_⟩
  · rw [compl_iInter]
    refine measure_iUnion_null fun j => ?_
    rw [preimage_compl, compl_compl]
    exact measure_preimage_iterate_null hθ j hD hD0
  · intro x hx
    refine mem_iInter.2 fun j => ?_
    exact mem_iInter.1 hx (j + 1)
  · intro x hx hθx
    exact (mem_iInter.1 hx 0) (hθBD hθx)
  · intro A hA hA0
    refine hgood A (eq_empty_iff_forall_notMem.2 fun x hx => ?_) hA0
    exact (mem_iInter.1 (hA hx.1) 0) hx.2

/-- **Corollary 12 for the bundle's `IsNonsingular`, with fibres countable off a null set `B`.** -/
theorem isHyperfinite_tailRel_core {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (hhyp : IsHyperfinite μ R) {θ : X → X}
    (hθ : IsNonsingular μ θ) {B : Set X} (hB : MeasurableSet B) (hB0 : μ B = 0)
    (hcount : ∀ y, y ∉ B → (θ ⁻¹' {y}).Countable)
    (hresp : ∀ x y, (x, y) ∈ R → (θ x, θ y) ∈ R) : IsHyperfinite μ (tailRel θ R) := by
  classical
  obtain ⟨X₀, hX₀, hX₀c, hfwd, hB', himg⟩ := exists_forward_invariant hθ hB hB0 hcount
  let θ' : X → X := X₀.piecewise θ id
  have hθ'X : ∀ x ∈ X₀, θ' x = θ x := fun x hx => piecewise_eq_of_mem _ _ _ hx
  have hθ'n : ∀ x ∉ X₀, θ' x = x := fun x hx => piecewise_eq_of_notMem _ _ _ hx
  have hiter : ∀ n, ∀ x ∈ X₀, θ'^[n] x = θ^[n] x ∧ θ^[n] x ∈ X₀ := by
    intro n
    induction n with
    | zero => exact fun x hx => ⟨rfl, hx⟩
    | succ n ih =>
      intro x hx
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', (ih x hx).1,
        hθ'X _ (ih x hx).2]
      exact ⟨rfl, hfwd _ (ih x hx).2⟩
  have hR' : IsDiscreteMeasured μ (cutOff R X₀ᶜ) := isDiscreteMeasured_cutOff hR hX₀.compl
  have hagree : ∀ x y, x ∉ X₀ᶜ → y ∉ X₀ᶜ → ((x, y) ∈ R ↔ (x, y) ∈ cutOff R X₀ᶜ) := by
    intro x y hx hy
    constructor
    · intro h
      exact Or.inl ⟨h, hx, hy⟩
    · rintro (⟨h, -, -⟩ | h)
      · exact h
      · have hxy : x = y := h
        subst hxy
        exact hR.equivalence.refl x
  have hhyp' : IsHyperfinite μ (cutOff R X₀ᶜ) :=
    CFWPlan.Main.IsHyperfinite.congr_null hhyp hX₀.compl hX₀c hagree
  have hθ'm : Measurable θ' := Measurable.piecewise hX₀ hθ.1 measurable_id
  have hpre : ∀ C, θ' ⁻¹' C = (θ ⁻¹' C ∩ X₀) ∪ (C \ X₀) := by
    intro C
    ext x
    by_cases hx : x ∈ X₀
    · simp only [mem_preimage, hθ'X x hx, mem_union, mem_inter_iff, hx, and_true, Set.mem_sdiff,
        not_true_eq_false, and_false, or_false]
    · simp only [mem_preimage, hθ'n x hx, mem_union, mem_inter_iff, hx, and_false, Set.mem_sdiff,
        not_false_eq_true, and_true, false_or]
  have himg' : ∀ A, θ' '' A ⊆ θ '' (A ∩ X₀) ∪ (A \ X₀) := by
    rintro A _ ⟨x, hx, rfl⟩
    by_cases hxX : x ∈ X₀
    · exact Or.inl ⟨x, ⟨hx, hxX⟩, (hθ'X x hxX).symm⟩
    · rw [hθ'n x hxX]
      exact Or.inr ⟨hx, hxX⟩
  have hcompl : ∀ C : Set X, μ (C \ X₀) = 0 := fun C =>
    measure_mono_null (fun x hx => hx.2) hX₀c
  have hθ' : IsNonsingular' μ θ' := by
    refine ⟨⟨hθ'm, fun C hC => ⟨fun h => ?_, fun h => ?_⟩⟩, fun A hA hA0 => ?_⟩
    · rw [hpre] at h
      have h1 : μ (θ ⁻¹' C ∩ X₀) = 0 := measure_mono_null subset_union_left h
      have h2 : μ (θ ⁻¹' C) = 0 := by
        refine measure_mono_null (t := (θ ⁻¹' C ∩ X₀) ∪ (θ ⁻¹' C \ X₀)) ?_
          (measure_union_null h1 (hcompl _))
        intro x hx
        by_cases hxX : x ∈ X₀
        · exact Or.inl ⟨hx, hxX⟩
        · exact Or.inr ⟨hx, hxX⟩
      exact (hθ.2 C hC).1 h2
    · rw [hpre]
      exact measure_union_null (measure_mono_null inter_subset_left ((hθ.2 C hC).2 h))
        (hcompl _)
    · exact measure_mono_null (himg' A) (measure_union_null
        (himg _ inter_subset_right (measure_mono_null inter_subset_left hA0)) (hcompl _))
  have hcount' : ∀ y, (θ' ⁻¹' {y}).Countable := by
    intro y
    by_cases hy : y ∈ B
    · refine (countable_singleton y).mono fun x hx => ?_
      have hx' : θ' x = y := hx
      by_cases hxX : x ∈ X₀
      · rw [hθ'X x hxX] at hx'
        exact absurd (hx' ▸ hy) (hB' x hxX)
      · rw [hθ'n x hxX] at hx'
        exact hx'
    · refine ((hcount y hy).union (countable_singleton y)).mono fun x hx => ?_
      have hx' : θ' x = y := hx
      by_cases hxX : x ∈ X₀
      · rw [hθ'X x hxX] at hx'
        exact Or.inl hx'
      · rw [hθ'n x hxX] at hx'
        exact Or.inr hx'
  have hresp' : ∀ x y, (x, y) ∈ cutOff R X₀ᶜ → (θ' x, θ' y) ∈ cutOff R X₀ᶜ := by
    rintro x y (⟨hxy, hx, hy⟩ | hxy)
    · have hx' : x ∈ X₀ := not_not.1 hx
      have hy' : y ∈ X₀ := not_not.1 hy
      rw [hθ'X x hx', hθ'X y hy']
      exact Or.inl ⟨hresp x y hxy, fun h => h (hfwd x hx'), fun h => h (hfwd y hy')⟩
    · have h : x = y := hxy
      subst h
      exact Or.inr rfl
  have hmain := (CFWPlan.Main.cor12 hR' hhyp' hθ' hcount' hresp').1
  refine CFWPlan.Main.IsHyperfinite.congr_null hmain hX₀.compl hX₀c fun x y hx hy => ?_
  have hx' : x ∈ X₀ := not_not.1 hx
  have hy' : y ∈ X₀ := not_not.1 hy
  simp only [tailRel, mem_ofPred_eq]
  constructor
  · rintro ⟨n, m, h⟩
    rw [(hiter n y hy').1, (hiter m x hx').1] at h
    rcases h with ⟨h, -, -⟩ | h
    · exact ⟨n, m, h⟩
    · have h' : θ^[n] y = θ^[m] x := h
      exact ⟨n, m, by rw [h']; exact hR.equivalence.refl _⟩
  · rintro ⟨n, m, h⟩
    refine ⟨n, m, ?_⟩
    rw [(hiter n y hy').1, (hiter m x hx').1]
    exact Or.inl ⟨h, fun h' => h' (hiter n y hy').2, fun h' => h' (hiter m x hx').2⟩

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
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
open CFWPlan
open CFWPlan.Main
open CFWPlan.Main.P5
open ConnesFeldmanWeiss
theorem solution {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite μ]
    (R : Set (X × X)) (hR : IsDiscreteMeasured μ R) (hhyp : IsHyperfinite μ R)
    (θ : X → X) (hθ : IsNonsingular μ θ) (hcount : ∀ x, (θ ⁻¹' {x}).Countable)
    (hresp : ∀ x y, (x, y) ∈ R → (θ x, θ y) ∈ R) :
    IsHyperfinite μ {p : X × X | ∃ n m : ℕ, (θ^[n] p.2, θ^[m] p.1) ∈ R} :=
  isHyperfinite_tailRel_core hR hhyp hθ MeasurableSet.empty measure_empty
    (fun y _ => hcount y) hresp
end
