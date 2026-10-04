-- Prove2me | solution 1 for ConnesFeldmanWeiss.exists_finiteSubrelation_boundary_lt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T15:49:08.391114+00:00
-- url     : https://prove2.me/submissions/8642ef72-a89f-464d-94a9-80a63431f24a

import Theorems.Thm_LusinNovikov_exists_disjoint_injOn_fst_iUnion_eq_of_countable_sections
import Theorems.Thm_LusinNovikov_measurableSet_image_fst_of_countable_sections
import Mathlib
import Definitions.Def_Monod_PiecewiseProjective
import Theorems.Thm_ConnesFeldmanWeiss_measure_eq_lintegral_fibreMeasure
import Theorems.Thm_ConnesFeldmanWeiss_exists_isBoundedSubset_cover_and_eq_iUnion_graph
import Theorems.Thm_ConnesFeldmanWeiss_exists_subset_pairwise_disjoint_sections
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
theorem exists_saturated_null {μ : Measure X} {R : Set (X × X)} (hR : IsDiscreteMeasured μ R)
    {N : Set X} (hN : μ N = 0) :
    ∃ N' : Set X, N ⊆ N' ∧ MeasurableSet N' ∧ μ N' = 0 ∧
      ∀ x y, (x, y) ∈ R → (x ∈ N' ↔ y ∈ N') := by
  refine ⟨saturation R (toMeasurable μ N),
    fun x hx => ⟨x, subset_toMeasurable μ N hx, hR.equivalence.refl x⟩,
    measurableSet_saturation hR.measurableSet hR.equivalence hR.countable_classes
      (measurableSet_toMeasurable μ N),
    hR.quasiInvariant _ (measurableSet_toMeasurable μ N) (by rw [measure_toMeasurable]; exact hN),
    ?_⟩
  intro x y hxy
  constructor
  · rintro ⟨z, hz, hxz⟩
    exact ⟨z, hz, hR.equivalence.trans (hR.equivalence.symm hxy) hxz⟩
  · rintro ⟨z, hz, hyz⟩
    exact ⟨z, hz, hR.equivalence.trans hxy hyz⟩

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

theorem measurable_tsum_section {E : Set (X × X)} (hE : MeasurableSet E)
    (hcount : ∀ x, {y | (x, y) ∈ E}.Countable) {g : X × X → ℝ≥0∞} (hg : Measurable g) :
    Measurable fun x => ∑' y : {y : X // (x, y) ∈ E}, g (x, y) := by
  have h : (fun x => ∑' y : {y : X // (x, y) ∈ E}, g (x, y)) =
      fun x => ∫⁻ p, g p ∂relKer E x := funext fun x => (lintegral_relKer hE x hg).symm
  rw [h]
  exact (Measure.measurable_lintegral hg).comp (measurable_relKer hE hcount)

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias measurable_tsum_section := CFWPlan.Main.P1.measurable_tsum_section

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
alias lintegral_relMeasure := CFWPlan.Main.P1.lintegral_relMeasure

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
alias lintegral_relMeasure_swap := CFWPlan.Main.P1.lintegral_relMeasure_swap

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
alias ae_relMeasure_iff := CFWPlan.Main.P1.ae_relMeasure_iff

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
alias relMeasure_compl := CFWPlan.Main.P1.relMeasure_compl

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
alias relMeasure_ac_swap := CFWPlan.Main.P1.relMeasure_ac_swap

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
/-- The chain rule for the module along two Borel automorphisms with graphs in `R`. -/
theorem ae_module_chain {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (α β : X ≃ᵐ X) (hα : ∀ x, (x, α x) ∈ R)
    (hβ : ∀ x, (x, β x) ∈ R) :
    ∀ᵐ x ∂μ, module μ R (β (α x), x) = module μ R (β (α x), α x) * module μ R (α x, x) := by
  have hδ := measurable_module μ R
  have hγR : ∀ x, (x, β (α x)) ∈ R := fun x => hR.equivalence.trans (hα x) (hβ (α x))
  have hγ : Measurable fun x => β (α x) := β.measurable.comp α.measurable
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
    (f := fun x => module μ R (β (α x), x))
    (g := fun x => module μ R (β (α x), α x) * module μ R (α x, x))
    (hδ.comp (hγ.prodMk measurable_id))
    ((hδ.comp (hγ.prodMk α.measurable)).mul (hδ.comp (α.measurable.prodMk measurable_id)))
    fun T hT _ => ?_
  have hαT : MeasurableSet (α '' T) := α.measurableSet_image.2 hT
  have h1 := lintegral_image_eq hR hT hγ (β.injective.comp α.injective).injOn
    (fun x _ => hγR x) (h := fun _ => 1) measurable_const
  have h2 := lintegral_image_eq hR hαT β.measurable β.injective.injOn
    (fun x _ => hβ x) (h := fun _ => 1) measurable_const
  have h3 := lintegral_image_eq hR hT α.measurable α.injective.injOn
    (fun x _ => hα x) (h := fun y => module μ R (β y, y))
    (hδ.comp (β.measurable.prodMk measurable_id))
  have himg : (fun x => β (α x)) '' T = β '' (α '' T) := (image_image _ _ _).symm
  simp only [one_mul] at h1 h2
  rw [← h1, himg, h2, h3]

theorem exists_module_cocycle {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) :
    ∃ N : Set X, MeasurableSet N ∧ μ N = 0 ∧ (∀ x y, (x, y) ∈ R → (x ∈ N ↔ y ∈ N)) ∧
      ∀ x y z, x ∉ N → (x, y) ∈ R → (y, z) ∈ R →
        module μ R (x, z) = module μ R (x, y) * module μ R (y, z) ∧
          0 < module μ R (x, y) ∧ module μ R (x, y) < ∞ := by
  obtain ⟨φ, hφ⟩ := IsDiscreteMeasured.exists_generators hR
  have hφR : ∀ n x, (x, φ n x) ∈ R := fun n x => (hφ x _).2 ⟨n, rfl⟩
  have hchain : ∀ᵐ x ∂μ, ∀ n k : ℕ, module μ R (φ k (φ n x), x) =
      module μ R (φ k (φ n x), φ n x) * module μ R (φ n x, x) := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro k
    exact ae_module_chain hR (φ n) (φ k) (hφR n) (hφR k)
  have hall := hchain.and (ae_module_good hR)
  obtain ⟨N, hNsub, hN, hN0, hNsat⟩ := exists_saturated_null hR (ae_iff.1 hall)
  refine ⟨N, hN, hN0, hNsat, fun x y z hx hxy hyz => ?_⟩
  have hPx := not_not.1 fun h => hx (hNsub h)
  have hy : y ∉ N := fun h => hx ((hNsat x y hxy).2 h)
  have hPy := not_not.1 fun h => hy (hNsub h)
  obtain ⟨hxy0, hxyt, hyx⟩ := hPx.2 y hxy
  obtain ⟨-, -, hzx⟩ := hPx.2 z (hR.equivalence.trans hxy hyz)
  obtain ⟨hyz0, -, hzy⟩ := hPy.2 z hyz
  refine ⟨?_, hxy0, hxyt⟩
  obtain ⟨n, rfl⟩ := (hφ x y).1 hxy
  obtain ⟨k, rfl⟩ := (hφ _ z).1 hyz
  have hc := hPx.1 n k
  rw [hzx, hzy, hyx] at hc
  have hc' := congrArg (·⁻¹) hc
  simp only [inv_inv] at hc'
  rw [hc', ENNReal.mul_inv (Or.inr (ENNReal.inv_ne_top.2 hxy0.ne'))
    (Or.inl (ENNReal.inv_ne_top.2 hyz0.ne')), inv_inv, inv_inv, mul_comm]

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias exists_module_cocycle := CFWPlan.Main.P1.exists_module_cocycle

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

/-- The bound for a "composition" of two sets with bounded sections. -/
theorem encard_comp_le {α : Type*} {S₁ : Set α} {S₂ : α → Set α} {b₁ b₂ : ℕ}
    (h₁ : S₁.encard ≤ b₁) (h₂ : ∀ z, (S₂ z).encard ≤ b₂) :
    {y | ∃ z ∈ S₁, y ∈ S₂ z}.encard ≤ ((b₁ * b₂ : ℕ) : ℕ∞) := by
  have hfin : S₁.Finite := finite_of_encard_le_coe h₁
  have hsub : {y | ∃ z ∈ S₁, y ∈ S₂ z} ⊆ ⋃ z ∈ hfin.toFinset, S₂ z := by
    rintro y ⟨z, hz, hy⟩
    exact mem_iUnion₂.2 ⟨z, hfin.mem_toFinset.2 hz, hy⟩
  calc {y | ∃ z ∈ S₁, y ∈ S₂ z}.encard ≤ (⋃ z ∈ hfin.toFinset, S₂ z).encard := encard_le_encard hsub
    _ ≤ ∑ z ∈ hfin.toFinset, (S₂ z).encard := Finset.set_encard_biUnion_le _ _
    _ ≤ hfin.toFinset.card • (b₂ : ℕ∞) := Finset.sum_le_card_nsmul _ _ _ fun z _ => h₂ z
    _ = (hfin.toFinset.card : ℕ∞) * b₂ := nsmul_eq_mul _ _
    _ ≤ (b₁ : ℕ∞) * b₂ := by
        rw [← hfin.encard_eq_coe_toFinset_card]
        exact mul_le_mul' h₁ le_rfl
    _ = ((b₁ * b₂ : ℕ) : ℕ∞) := by push_cast; rfl

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
/-- The fibre measure `ν_F(A)` of CFW p. 435 computed from the base point `a ∈ F`:
`(∑_{x ∈ F ∩ A} δ⁻¹(a, x)) / ∑_{x ∈ F} δ⁻¹(a, x)`. The Lemma 2 statement integrates
`fibreRatio μ R T A (Quot.out F)` (definitionally). -/
noncomputable def fibreRatio (μ : Measure X) (R T : Set (X × X)) (A : Set X) (a : X) : ℝ≥0∞ :=
  (∑' x : {x : X // (a, x) ∈ T ∧ x ∈ A}, (module μ R (a, x))⁻¹) /
    ∑' x : {x : X // (a, x) ∈ T}, (module μ R (a, x))⁻¹

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
/-- **Base-point independence of the fibre ratio** (CFW p. 435: "`∀ y ∈ F`"). -/
theorem fibreRatio_congr {μ : Measure X} [SigmaFinite μ] {R T : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (hT : IsFiniteSubrelation R T) {N : Set X}
    (hN : ∀ x y z, x ∉ N → (x, y) ∈ R → (y, z) ∈ R →
      module μ R (x, z) = module μ R (x, y) * module μ R (y, z) ∧
        0 < module μ R (x, y) ∧ module μ R (x, y) < ∞)
    (hNsat : ∀ x y, (x, y) ∈ R → (x ∈ N ↔ y ∈ N)) (A : Set X) {a b : X} (ha : a ∉ N)
    (hab : (a, b) ∈ T) : fibreRatio μ R T A a = fibreRatio μ R T A b := by
  have habR := hT.subset hab
  have hRe := hR.equivalence
  obtain ⟨-, hpos, hlt⟩ := hN a b b ha habR (hRe.refl b)
  set c := (module μ R (a, b))⁻¹ with hc_def
  have hc0 : c ≠ 0 := ENNReal.inv_ne_zero.2 hlt.ne
  have hctop : c ≠ ∞ := ENNReal.inv_ne_top.2 hpos.ne'
  have hmod : ∀ x, (b, x) ∈ T → (module μ R (a, x))⁻¹ = c * (module μ R (b, x))⁻¹ := by
    intro x hbx
    rw [(hN a b x ha habR (hT.subset hbx)).1, ENNReal.mul_inv (Or.inl hpos.ne') (Or.inl hlt.ne)]
  have hiff : ∀ x, (a, x) ∈ T ↔ (b, x) ∈ T := fun x =>
    ⟨fun h => hT.trans _ _ _ (hT.symm _ _ hab) h, fun h => hT.trans _ _ _ hab h⟩
  have hnum : ∑' x : {x : X // (a, x) ∈ T ∧ x ∈ A}, (module μ R (a, (x : X)))⁻¹ =
      c * ∑' x : {x : X // (b, x) ∈ T ∧ x ∈ A}, (module μ R (b, (x : X)))⁻¹ := by
    rw [← ENNReal.tsum_mul_left,
      ← (Equiv.subtypeEquivRight fun x => and_congr_left' (hiff x)).tsum_eq]
    exact tsum_congr fun x => hmod x ((hiff x).1 x.2.1)
  have hden : ∑' x : {x : X // (a, x) ∈ T}, (module μ R (a, (x : X)))⁻¹ =
      c * ∑' x : {x : X // (b, x) ∈ T}, (module μ R (b, (x : X)))⁻¹ := by
    rw [← ENNReal.tsum_mul_left, ← (Equiv.subtypeEquivRight hiff).tsum_eq]
    exact tsum_congr fun x => hmod x ((hiff x).1 x.2)
  unfold fibreRatio
  rw [hnum, hden, ENNReal.mul_div_mul_left _ _ hc0 hctop]

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias fibreRatio_congr := CFWPlan.Main.P2.fibreRatio_congr

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

/-- The set where a function obeys the two-sided bound `c ≤ f ≤ c⁻¹` on `K` is measurable. -/
theorem measurableSet_bound {K : Set (X × X)} (hK : MeasurableSet K) (c : ℝ≥0)
    {f : X × X → ℝ≥0∞} (hf : Measurable f) :
    MeasurableSet {p | p ∈ K → (c : ℝ≥0∞) ≤ f p ∧ f p ≤ (c : ℝ≥0∞)⁻¹} :=
  MeasurableSet.imp hK
    ((measurableSet_le measurable_const hf).inter (measurableSet_le hf measurable_const))

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
/-- Unions of two bounded sets are bounded. -/
theorem IsBoundedSubset.union {μ : Measure X} {R K₁ K₂ : Set (X × X)}
    (h₁ : IsBoundedSubset μ R K₁) (h₂ : IsBoundedSubset μ R K₂) : IsBoundedSubset μ R (K₁ ∪ K₂) := by
  obtain ⟨a₁, ha₁⟩ := h₁.bdd_snd
  obtain ⟨a₂, ha₂⟩ := h₂.bdd_snd
  obtain ⟨b₁, hb₁⟩ := h₁.bdd_fst
  obtain ⟨b₂, hb₂⟩ := h₂.bdd_fst
  obtain ⟨c₁, hc₁, hδ₁⟩ := h₁.bdd_module
  obtain ⟨c₂, hc₂, hδ₂⟩ := h₂.bdd_module
  refine ⟨h₁.measurableSet.union h₂.measurableSet, union_subset h₁.subset h₂.subset,
    ⟨a₁ + a₂, fun x => ?_⟩, ⟨b₁ + b₂, fun y => ?_⟩, ⟨min c₁ c₂, lt_min hc₁ hc₂, ?_⟩⟩
  · calc {y | (y, x) ∈ K₁ ∪ K₂}.encard = ({y | (y, x) ∈ K₁} ∪ {y | (y, x) ∈ K₂}).encard := rfl
      _ ≤ {y | (y, x) ∈ K₁}.encard + {y | (y, x) ∈ K₂}.encard := encard_union_le _ _
      _ ≤ (a₁ : ℕ∞) + a₂ := add_le_add (ha₁ x) (ha₂ x)
      _ = ((a₁ + a₂ : ℕ) : ℕ∞) := by push_cast; rfl
  · calc {x | (y, x) ∈ K₁ ∪ K₂}.encard = ({x | (y, x) ∈ K₁} ∪ {x | (y, x) ∈ K₂}).encard := rfl
      _ ≤ {x | (y, x) ∈ K₁}.encard + {x | (y, x) ∈ K₂}.encard := encard_union_le _ _
      _ ≤ (b₁ : ℕ∞) + b₂ := add_le_add (hb₁ y) (hb₂ y)
      _ = ((b₁ + b₂ : ℕ) : ℕ∞) := by push_cast; rfl
  · have hm₁ : ((min c₁ c₂ : ℝ≥0) : ℝ≥0∞) ≤ c₁ := ENNReal.coe_le_coe.2 (min_le_left _ _)
    have hm₂ : ((min c₁ c₂ : ℝ≥0) : ℝ≥0∞) ≤ c₂ := ENNReal.coe_le_coe.2 (min_le_right _ _)
    filter_upwards [hδ₁, hδ₂] with p hp₁ hp₂ hp
    rcases hp with hp | hp
    · obtain ⟨l, u⟩ := hp₁ hp
      exact ⟨hm₁.trans l, u.trans (ENNReal.inv_le_inv.2 hm₁)⟩
    · obtain ⟨l, u⟩ := hp₂ hp
      exact ⟨hm₂.trans l, u.trans (ENNReal.inv_le_inv.2 hm₂)⟩

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias IsBoundedSubset.union := CFWPlan.Main.P2.IsBoundedSubset.union

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
/-- The diagonal is bounded. -/
theorem isBoundedSubset_diagonal {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) : IsBoundedSubset μ R {p | p.1 = p.2} := by
  have hRe := hR.equivalence
  have hδm : Measurable (module μ R) := Measure.measurable_rnDeriv _ _
  have hD : MeasurableSet {p : X × X | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  obtain ⟨N, -, hN0, -, hN⟩ := CFWPlan.Main.exists_module_cocycle hR
  refine ⟨hD, fun p hp => ?_, ⟨1, fun x => ?_⟩, ⟨1, fun y => ?_⟩, ⟨1, one_pos, ?_⟩⟩
  · obtain ⟨x, y⟩ := p
    have hxy : x = y := hp
    rw [hxy]
    exact hRe.refl y
  · refine encard_le_one_cast fun y₁ y₂ h₁ h₂ => ?_
    have e₁ : y₁ = x := h₁
    have e₂ : y₂ = x := h₂
    rw [e₁, e₂]
  · refine encard_le_one_cast fun x₁ x₂ h₁ h₂ => ?_
    have e₁ : y = x₁ := h₁
    have e₂ : y = x₂ := h₂
    rw [← e₁, ← e₂]
  · refine (CFWPlan.Main.ae_relMeasure_iff hR.measurableSet hR.countable_classes
      (measurableSet_bound hD 1 hδm)).2 ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with x hx y _ hxy
    have hxy' : x = y := hxy
    subst hxy'
    obtain ⟨h1, h2, h3⟩ := hN x x x hx (hRe.refl x) (hRe.refl x)
    have hone : module μ R (x, x) = 1 :=
      ((ENNReal.mul_right_inj h2.ne' h3.ne).1 (by rw [mul_one]; exact h1)).symm
    rw [hone, ENNReal.coe_one, inv_one]
    exact ⟨le_rfl, le_rfl⟩

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias isBoundedSubset_diagonal := CFWPlan.Main.P2.isBoundedSubset_diagonal

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
/-- The inverse `K⁻¹ = swap⁻¹' K` of a bounded set is bounded. -/
theorem IsBoundedSubset.swap {μ : Measure X} [SigmaFinite μ] {R K : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (hK : IsBoundedSubset μ R K) :
    IsBoundedSubset μ R (Prod.swap ⁻¹' K) := by
  obtain ⟨a, ha⟩ := hK.bdd_snd
  obtain ⟨b, hb⟩ := hK.bdd_fst
  obtain ⟨c, hc, hδ⟩ := hK.bdd_module
  have hRe := hR.equivalence
  have hδm : Measurable (module μ R) := Measure.measurable_rnDeriv _ _
  refine ⟨measurable_swap hK.measurableSet, fun p hp => hRe.symm (hK.subset hp),
    ⟨b, fun x => hb x⟩, ⟨a, fun y => ha y⟩, ⟨c, hc, ?_⟩⟩
  have hac := (CFWPlan.Main.relMeasure_ac_swap hR).2
  have h1 : ∀ᵐ p ∂(relMeasure μ R).map Prod.swap,
      p ∈ K → (c : ℝ≥0∞) ≤ module μ R p ∧ module μ R p ≤ (c : ℝ≥0∞)⁻¹ := hac.ae_le hδ
  rw [ae_map_iff measurable_swap.aemeasurable (measurableSet_bound hK.measurableSet c hδm)] at h1
  filter_upwards [h1, CFWPlan.Main.module_swap hR] with p hp hsw hpK
  obtain ⟨l, u⟩ := hp hpK
  rw [hsw] at l u
  exact ⟨ENNReal.inv_le_inv.1 u, ENNReal.le_inv_iff_le_inv.1 l⟩

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias IsBoundedSubset.swap := CFWPlan.Main.P2.IsBoundedSubset.swap

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
/-- The composition of bounded sets is bounded. -/
theorem IsBoundedSubset.comp {μ : Measure X} [SigmaFinite μ] {R K₁ K₂ : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (h₁ : IsBoundedSubset μ R K₁) (h₂ : IsBoundedSubset μ R K₂) :
    IsBoundedSubset μ R {p | ∃ z, (p.1, z) ∈ K₁ ∧ (z, p.2) ∈ K₂} := by
  have hRe := hR.equivalence
  have hδm : Measurable (module μ R) := Measure.measurable_rnDeriv _ _
  obtain ⟨a₁, ha₁⟩ := h₁.bdd_snd
  obtain ⟨a₂, ha₂⟩ := h₂.bdd_snd
  obtain ⟨b₁, hb₁⟩ := h₁.bdd_fst
  obtain ⟨b₂, hb₂⟩ := h₂.bdd_fst
  -- measurability: a projection with finite sections
  set W : Set ((X × X) × X) := {q | (q.1.1, q.2) ∈ K₁ ∧ (q.2, q.1.2) ∈ K₂} with hW_def
  have hWm : MeasurableSet W :=
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd h₁.measurableSet).inter
      ((measurable_snd.prodMk (measurable_snd.comp measurable_fst)) h₂.measurableSet)
  have hWc : ∀ p : X × X, {z | (p, z) ∈ W}.Countable := fun p =>
    (finite_of_encard_le_coe (hb₁ p.1)).countable.mono fun z hz => hz.1
  have hWimg : Prod.fst '' W = {p | ∃ z, (p.1, z) ∈ K₁ ∧ (z, p.2) ∈ K₂} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.2, hq⟩
    · rintro ⟨z, hz⟩
      exact ⟨(p, z), hz, rfl⟩
  refine ⟨hWimg ▸ CFWPlan.Route.measurableSet_image_fst hWm hWc, ?_, ⟨a₂ * a₁, fun x => ?_⟩,
    ⟨b₁ * b₂, fun y => ?_⟩, ?_⟩
  · rintro ⟨x, y⟩ ⟨z, hxz, hzy⟩
    exact hRe.trans (h₁.subset hxz) (h₂.subset hzy)
  · refine (encard_le_encard ?_).trans (encard_comp_le (S₁ := {z | (z, x) ∈ K₂})
      (S₂ := fun z => {y | (y, z) ∈ K₁}) (ha₂ x) fun z => ha₁ z)
    rintro y ⟨z, hyz, hzx⟩
    exact ⟨z, hzx, hyz⟩
  · exact encard_comp_le (S₁ := {z | (y, z) ∈ K₁}) (S₂ := fun z => {x | (z, x) ∈ K₂}) (hb₁ y)
      fun z => hb₂ z
  · obtain ⟨c₁, hc₁, hδ₁⟩ := h₁.bdd_module
    obtain ⟨c₂, hc₂, hδ₂⟩ := h₂.bdd_module
    obtain ⟨N, -, hN0, -, hN⟩ := CFWPlan.Main.exists_module_cocycle hR
    have hcount := hR.countable_classes
    have hδ₁' := (CFWPlan.Main.ae_relMeasure_iff hR.measurableSet hcount
      (measurableSet_bound h₁.measurableSet c₁ hδm)).1 hδ₁
    have hδ₂' := (CFWPlan.Main.ae_relMeasure_iff hR.measurableSet hcount
      (measurableSet_bound h₂.measurableSet c₂ hδm)).1 hδ₂
    rw [ae_iff] at hδ₂'
    have hB₂ := IsDiscreteMeasured.saturation_null hR hδ₂'
    refine ⟨c₁ * c₂, mul_pos hc₁ hc₂, ?_⟩
    refine (CFWPlan.Main.ae_relMeasure_iff hR.measurableSet hcount
      (measurableSet_bound (hWimg ▸ CFWPlan.Route.measurableSet_image_fst hWm hWc)
        (c₁ * c₂) hδm)).2 ?_
    filter_upwards [hδ₁', measure_eq_zero_iff_ae_notMem.1 hN0,
      measure_eq_zero_iff_ae_notMem.1 hB₂] with x hx₁ hxN hxB y _ hxy
    obtain ⟨z, hxz, hzy⟩ := hxy
    have hz : ∀ y, (z, y) ∈ R → (z, y) ∈ K₂ →
        (c₂ : ℝ≥0∞) ≤ module μ R (z, y) ∧ module μ R (z, y) ≤ (c₂ : ℝ≥0∞)⁻¹ := by
      by_contra hcon
      exact hxB ⟨z, hcon, h₁.subset hxz⟩
    obtain ⟨l₁, u₁⟩ := hx₁ z (h₁.subset hxz) hxz
    obtain ⟨l₂, u₂⟩ := hz y (h₂.subset hzy) hzy
    rw [(hN x z y hxN (h₁.subset hxz) (h₂.subset hzy)).1, ENNReal.coe_mul,
      ENNReal.mul_inv (Or.inl (ENNReal.coe_ne_zero.2 hc₁.ne')) (Or.inl ENNReal.coe_ne_top)]
    exact ⟨mul_le_mul' l₁ l₂, mul_le_mul' u₁ u₂⟩

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias IsBoundedSubset.comp := CFWPlan.Main.P2.IsBoundedSubset.comp

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
/-- Finite unions of the Lemma 3(a) pieces are bounded and increase to `R`. -/
theorem exists_isBoundedSubset_mono_cover {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) :
    ∃ K : ℕ → Set (X × X), Monotone K ∧ (∀ n, IsBoundedSubset μ R (K n)) ∧ R = ⋃ n, K n := by
  obtain ⟨K, hK, hKR⟩ := exists_isBoundedSubset_cover hR
  refine ⟨Set.accumulate K, monotone_accumulate, fun n => ?_, ?_⟩
  · induction n with
    | zero => rw [accumulate_zero_nat]; exact hK 0
    | succ n ih => rw [accumulate_succ]; exact IsBoundedSubset.union ih (hK _)
  · rw [iUnion_accumulate]
    exact hKR

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias exists_isBoundedSubset_mono_cover := CFWPlan.Main.P2.exists_isBoundedSubset_mono_cover

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
/-- **Hahn–Banach separation in `L¹` with an `L∞` witness** (replaces the paper's Goldstine +
Mazur argument, CFW p. 440). -/
theorem exists_separating_bounded (ν : Measure Ω) [SigmaFinite ν] (D : Set (Ω → ℝ))
    (hD : Convex ℝ D) (hint : ∀ c ∈ D, Integrable c ν) {ε : ℝ} (hε : 0 < ε)
    (hfar : ∀ c ∈ D, ε ≤ ∫ x, |c x| ∂ν) :
    ∃ g : Ω → ℝ, Measurable g ∧ (∀ x, |g x| ≤ 1) ∧ ∀ c ∈ D, ε ≤ ∫ x, c x * g x ∂ν := by
  classical
  rcases D.eq_empty_or_nonempty with hDe | ⟨c₀, hc₀⟩
  · exact ⟨0, measurable_const, by simp, by simp [hDe]⟩
  let T : (Ω → ℝ) → (Ω →₁[ν] ℝ) := fun c => if hc : Integrable c ν then hc.toL1 c else 0
  have hT : ∀ c (hc : Integrable c ν), T c = hc.toL1 c := fun c hc => dif_pos hc
  have hTnorm : ∀ c, Integrable c ν → ‖T c‖ = ∫ x, |c x| ∂ν := by
    intro c hc
    rw [hT c hc, L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [hc.coeFn_toL1] with x hx; rw [hx, Real.norm_eq_abs]
  have ht : Convex ℝ (T '' D) := by
    rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩ a b ha hb hab
    refine ⟨a • c₁ + b • c₂, hD hc₁ hc₂ ha hb hab, ?_⟩
    have i₁ := hint c₁ hc₁
    have i₂ := hint c₂ hc₂
    rw [hT _ ((i₁.smul a).add (i₂.smul b)), hT _ i₁, hT _ i₂,
      Integrable.toL1_add _ _ (i₁.smul a) (i₂.smul b), Integrable.toL1_smul' _ i₁,
      Integrable.toL1_smul' _ i₂]
  have hdisj : Disjoint (Metric.ball (0 : Ω →₁[ν] ℝ) ε) (T '' D) := by
    rw [Set.disjoint_left]
    rintro F hF ⟨c, hc, rfl⟩
    rw [mem_ball_zero_iff, hTnorm c (hint c hc)] at hF
    exact (hfar c hc).not_gt hF
  obtain ⟨φ, u, hφu, huφ⟩ :=
    geometric_hahn_banach_open (convex_ball _ _) Metric.isOpen_ball ht hdisj
  have hεφ : ε * ‖φ‖ ≤ u := by
    by_contra hlt
    replace hlt := not_le.mp hlt
    obtain ⟨x, hx1, hx2⟩ := φ.exists_lt_apply_of_lt_opNorm (r := u / ε)
      (by rwa [div_lt_iff₀ hε, mul_comm])
    obtain ⟨y, hy1, hy2⟩ : ∃ y : Ω →₁[ν] ℝ, ‖y‖ < 1 ∧ u / ε < φ y := by
      rcases le_or_gt 0 (φ x) with h | h
      · exact ⟨x, hx1, by rwa [Real.norm_eq_abs, abs_of_nonneg h] at hx2⟩
      · refine ⟨-x, by rwa [norm_neg], ?_⟩
        rw [map_neg]
        rwa [Real.norm_eq_abs, abs_of_neg h] at hx2
    have hmem : ε • y ∈ Metric.ball (0 : Ω →₁[ν] ℝ) ε := by
      rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
      exact mul_lt_of_lt_one_right hε hy1
    have h1 := hφu _ hmem
    rw [map_smul, smul_eq_mul] at h1
    rw [div_lt_iff₀ hε] at hy2
    linarith
  have hφpos : 0 < ‖φ‖ := by
    have hu0 : 0 < u := by simpa using hφu 0 (Metric.mem_ball_self hε)
    have h1 := huφ (T c₀) ⟨c₀, hc₀, rfl⟩
    have h2 := φ.le_opNorm (T c₀)
    have h3 := le_abs_self (φ (T c₀))
    rw [← Real.norm_eq_abs] at h3
    by_contra h
    replace h := not_lt.mp h
    have : ‖φ‖ = 0 := le_antisymm h (norm_nonneg _)
    rw [this, zero_mul] at h2
    linarith
  set Λ : (Ω → ℝ) → ℝ := fun c => φ (T c) / ‖φ‖ with hΛ
  have hadd : ∀ f g, Integrable f ν → Integrable g ν → Λ (f + g) = Λ f + Λ g := by
    intro f g hf hg
    simp only [hΛ]
    rw [hT _ (hf.add hg), hT _ hf, hT _ hg, Integrable.toL1_add _ _ hf hg, map_add, add_div]
  have hsmul : ∀ (c : ℝ) (f : Ω → ℝ), Integrable f ν → Λ (c • f) = c * Λ f := by
    intro c f hf
    simp only [hΛ]
    rw [hT _ (hf.smul c), hT _ hf, Integrable.toL1_smul' _ hf, map_smul, smul_eq_mul,
      mul_div_assoc]
  have hbdd : ∀ f, Integrable f ν → |Λ f| ≤ 1 * ∫ x, |f x| ∂ν := by
    intro f hf
    simp only [hΛ]
    rw [abs_div, abs_of_pos hφpos, div_le_iff₀ hφpos, one_mul, ← hTnorm f hf, mul_comm,
      ← Real.norm_eq_abs]
    exact φ.le_opNorm _
  obtain ⟨g, hgm, hg1, hg⟩ := exists_bounded_density_of_functional ν Λ zero_le_one hadd hsmul hbdd
  refine ⟨g, hgm, hg1, fun c hc => ?_⟩
  rw [← hg c (hint c hc)]
  simp only [hΛ]
  rw [le_div_iff₀ hφpos]
  exact hεφ.trans (huφ _ ⟨c, hc, rfl⟩)

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {Ω : Type*} [MeasurableSpace Ω]
alias exists_separating_bounded := CFWPlan.Main.P3.exists_separating_bounded

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

lemma bdd_swap (hR : Equivalence fun x y => (x, y) ∈ R) {f : X × X → ℝ}
    (hf : Monod.IsBddMeasOn R f) : Monod.IsBddMeasOn R (fun p => f p.swap) := by
  obtain ⟨hfm, C, hC⟩ := hf
  exact ⟨hfm.comp measurable_swap, C, fun p hp => hC _ (hR.symm hp)⟩

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

lemma floor_approx (n : ℕ) (t : ℝ) :
    |t - (⌊((n : ℝ) + 1) * t⌋ : ℝ) / ((n : ℝ) + 1)| ≤ 1 / ((n : ℝ) + 1) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have h1 := Int.floor_le (((n : ℝ) + 1) * t)
  have h2 := Int.lt_floor_add_one (((n : ℝ) + 1) * t)
  have e : t - (⌊((n : ℝ) + 1) * t⌋ : ℝ) / ((n : ℝ) + 1) =
      (((n : ℝ) + 1) * t - ⌊((n : ℝ) + 1) * t⌋) / ((n : ℝ) + 1) := by
    field_simp
  rw [e, abs_div, abs_of_pos hn]
  apply div_le_div_of_nonneg_right _ hn.le
  rw [abs_le]; constructor <;> linarith

/-- **Means are `L∞(X)`-modular in the first coordinate**: `P (g(y) f(y, x)) = g · P f`. -/
theorem IsLeftInvariantMean.mul_fst {μ : Measure X} {R : Set (X × X)} (hR : ∀ x, (x, x) ∈ R)
    {P : (X × X → ℝ) → X → ℝ} (hP : Monod.IsLeftInvariantMean μ R P) {f : X × X → ℝ}
    (hf : Monod.IsBddMeasOn R f) {g : X → ℝ} (hg : Measurable g) {C : ℝ} (hgC : ∀ x, |g x| ≤ C) :
    P (fun p => g p.1 * f p) =ᵐ[μ] fun x => g x * P f x := by
  obtain ⟨M, hM0, hM⟩ := IsBddMeasOn.exists_nonneg hf
  have hgf : Monod.IsBddMeasOn R (fun p => g p.1 * f p) := bdd_mul_fst hg hgC hf
  have hPf : ∀ᵐ x ∂μ, |P f x| ≤ M := IsLeftInvariantMean.ae_abs_le hP hf hM
  have key : ∀ (n : ℕ) (k : ℤ), ∀ᵐ x ∂μ, ⌊((n : ℝ) + 1) * g x⌋ = k →
      |P (fun p => g p.1 * f p) x - (k / ((n : ℝ) + 1)) * P f x| ≤ M / ((n : ℝ) + 1) := by
    intro n k
    have hn : (0 : ℝ) < n + 1 := by positivity
    set a : ℝ := k / ((n : ℝ) + 1) with ha
    set A : Set X := {x | ⌊((n : ℝ) + 1) * g x⌋ = k} with hAdef
    have hA : MeasurableSet A :=
      (measurable_const.mul hg).floor (measurableSet_singleton k)
    have hga : Measurable fun x => g x - a := hg.sub measurable_const
    have hgaC : ∀ x, |g x - a| ≤ C + |a| := fun x =>
      (abs_sub _ _).trans (add_le_add (hgC x) le_rfl)
    have hb : Monod.IsBddMeasOn R (fun p => (g p.1 - a) * f p) := bdd_mul_fst hga hgaC hf
    have hb' : Monod.IsBddMeasOn R (fun p => A.indicator 1 p.1 * ((g p.1 - a) * f p)) :=
      bdd_mul_fst (g := A.indicator (1 : X → ℝ))
        (measurable_const.indicator hA : Measurable (A.indicator (1 : X → ℝ))) (C := 1)
        (fun x => by
          by_cases hx : x ∈ A
          · rw [indicator_of_mem hx, Pi.one_apply, abs_one]
          · rw [indicator_of_notMem hx, abs_zero]; exact zero_le_one) hb
    have hbound : ∀ p ∈ R, |A.indicator 1 p.1 * ((g p.1 - a) * f p)| ≤ M / ((n : ℝ) + 1) := by
      intro p hp
      by_cases hpA : p.1 ∈ A
      · rw [indicator_of_mem hpA, Pi.one_apply, one_mul, abs_mul]
        have h1 : |g p.1 - a| ≤ 1 / ((n : ℝ) + 1) := by
          have := floor_approx n (g p.1)
          rw [show (⌊((n : ℝ) + 1) * g p.1⌋ : ℝ) = k from by
            rw [show ⌊((n : ℝ) + 1) * g p.1⌋ = k from hpA]] at this
          exact this
        calc |g p.1 - a| * |f p| ≤ 1 / ((n : ℝ) + 1) * M :=
              mul_le_mul h1 (hM p hp) (abs_nonneg _) (by positivity)
          _ = M / ((n : ℝ) + 1) := by ring
      · rw [indicator_of_notMem hpA, zero_mul, abs_zero]; positivity
    have e1 := IsLeftInvariantMean.ae_abs_le hP hb' hbound
    have e2 := mul_fst_indicator hR hP hb hA
    have e3 := hP.add (fun p => g p.1 * f p) ((-a) • f) hgf (bdd_smul _ hf)
    have e4 := hP.smul (-a) f hf
    have e5 : (fun p => (g p.1 - a) * f p) = (fun p => g p.1 * f p) + (-a) • f := by
      ext p; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    filter_upwards [e1, e2, e3, e4] with x h1 h2 h3 h4 hxA
    rw [h2, indicator_of_mem (show x ∈ A from hxA), Pi.one_apply, one_mul, e5, h3] at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h4
    rw [h4] at h1
    calc |P (fun p => g p.1 * f p) x - a * P f x|
        = |P (fun p => g p.1 * f p) x + -a * P f x| := by ring_nf
      _ ≤ M / ((n : ℝ) + 1) := h1
  have key' : ∀ᵐ x ∂μ, ∀ n : ℕ, ∀ k : ℤ, ⌊((n : ℝ) + 1) * g x⌋ = k →
      |P (fun p => g p.1 * f p) x - (k / ((n : ℝ) + 1)) * P f x| ≤ M / ((n : ℝ) + 1) := by
    rw [ae_all_iff]; intro n; rw [ae_all_iff]; exact key n
  filter_upwards [key', hPf] with x hx hPx
  have hbd : ∀ n : ℕ, |P (fun p => g p.1 * f p) x - g x * P f x| ≤ 2 * M / ((n : ℝ) + 1) := by
    intro n
    have h1 := hx n _ rfl
    have h2 := floor_approx n (g x)
    set a : ℝ := (⌊((n : ℝ) + 1) * g x⌋ : ℝ) / ((n : ℝ) + 1)
    have h3 : |(a - g x) * P f x| ≤ 1 / ((n : ℝ) + 1) * M := by
      rw [abs_mul, abs_sub_comm]
      exact mul_le_mul h2 hPx (abs_nonneg _) (by positivity)
    calc |P (fun p => g p.1 * f p) x - g x * P f x|
        = |(P (fun p => g p.1 * f p) x - a * P f x) + (a - g x) * P f x| := by ring_nf
      _ ≤ |P (fun p => g p.1 * f p) x - a * P f x| + |(a - g x) * P f x| := abs_add_le _ _
      _ ≤ M / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) * M := add_le_add h1 h3
      _ = 2 * M / ((n : ℝ) + 1) := by ring
  have hlim : Tendsto (fun n : ℕ => 2 * M / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (2 * M) |>.comp (tendsto_add_atTop_nat 1) |>.congr
      fun n => by simp
  have h0 : |P (fun p => g p.1 * f p) x - g x * P f x| ≤ 0 :=
    ge_of_tendsto' hlim hbd
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h0)

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
lemma relNull_mono {μ : Measure X} {R S S' : Set (X × X)} (h : S' ⊆ S)
    (hS : Monod.RelNull μ R S) : Monod.RelNull μ R S' :=
  measure_mono_null (image_mono (inter_subset_inter_left _ h)) hS

/-- Bounded measurable functions have integrable means (finite `μ`). -/
lemma integrable_mean {μ : Measure X} [IsFiniteMeasure μ] {R : Set (X × X)}
    {P : (X × X → ℝ) → X → ℝ} (hP : Monod.IsLeftInvariantMean μ R P) {f : X × X → ℝ}
    (hf : Monod.IsBddMeasOn R f) : Integrable (P f) μ := by
  obtain ⟨C, -, hC⟩ := IsBddMeasOn.exists_nonneg hf
  exact Integrable.of_bound (hP.aemeasurable f hf).aestronglyMeasurable C
    (by filter_upwards [IsLeftInvariantMean.ae_abs_le hP hf hC] with x hx; rwa [Real.norm_eq_abs])

/-- `δ(x, y) δ(y, x) = 1` for `μ`-a.e. `x` and all `y ~ x`. -/
lemma ae_module_mul_swap {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) :
    ∀ᵐ x ∂μ, ∀ y, (x, y) ∈ R → (module μ R (x, y)).toReal * (module μ R (y, x)).toReal = 1 := by
  have hmod : Measurable (module μ R) := Measure.measurable_rnDeriv _ _
  have hm : ∀ᵐ q ∂relMeasure μ R, (module μ R q).toReal * (module μ R q.swap).toReal = 1 := by
    filter_upwards [module_swap hR, module_pos_lt_top hR] with q h1 h2
    rw [h1, ENNReal.toReal_inv, mul_inv_cancel₀]
    exact (ENNReal.toReal_pos h2.1.ne' h2.2.ne).ne'
  exact (ae_relMeasure_iff hR.measurableSet hR.countable_classes
    (p := fun q => (module μ R q).toReal * (module μ R q.swap).toReal = 1)
    (measurableSet_eq_fun (hmod.ennreal_toReal.mul (hmod.comp measurable_swap).ennreal_toReal)
      measurable_const)).mp hm

open Classical in
/-- **The invariant state of CFW p. 440**, `L f = ∫ P (f ∘ swap) dμ`. -/
theorem exists_invariant_state {μ : Measure X} [IsProbabilityMeasure μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (hamen : Monod.IsAmenableRel μ R) :
    ∃ L : (X × X → ℝ) → ℝ,
      (∀ f g, Monod.IsBddMeasOn R f → Monod.IsBddMeasOn R g → L (f + g) = L f + L g) ∧
      (∀ (c : ℝ) f, Monod.IsBddMeasOn R f → L (c • f) = c * L f) ∧
      (∀ f, Monod.IsBddMeasOn R f → (∀ᵐ p ∂relMeasure μ R, 0 ≤ f p) → 0 ≤ L f) ∧
      L 1 = 1 ∧
      ∀ (φ : Monod.PartialTransformation R) (β : X → ℝ), Measurable β → (∃ C, ∀ x, |β x| ≤ C) →
        (∀ᵐ x ∂μ, x ∈ φ.cod → β x = (module μ R (ptInv φ x, x)).toReal) →
        ∀ f, Monod.IsBddMeasOn R f →
          L (fun p => if p.2 ∈ φ.cod then β p.2 * f (p.1, ptInv φ p.2) else 0) =
            L (fun p => φ.dom.indicator 1 p.2 * f p) := by
  obtain ⟨P, hP⟩ := hamen
  have hRe := hR.equivalence
  have hrefl : ∀ x, (x, x) ∈ R := fun x => hRe.refl x
  refine ⟨fun f => ∫ x, P (fun p => f p.swap) x ∂μ, ?_, ?_, ?_, ?_, ?_⟩
  · intro f g hf hg
    have hf' := bdd_swap hRe hf
    have hg' := bdd_swap hRe hg
    have e : (fun p : X × X => (f + g) p.swap) = (fun p => f p.swap) + (fun p => g p.swap) := rfl
    simp only
    rw [e, ← integral_add (integrable_mean hP hf') (integrable_mean hP hg')]
    exact integral_congr_ae (hP.add _ _ hf' hg')
  · intro c f hf
    have hf' := bdd_swap hRe hf
    have e : (fun p : X × X => (c • f) p.swap) = c • (fun p => f p.swap) := rfl
    simp only
    rw [e, ← integral_const_mul]
    exact integral_congr_ae (by filter_upwards [hP.smul c _ hf'] with x hx; rw [hx]; rfl)
  · intro f hf hnn
    have hf' := bdd_swap hRe hf
    obtain ⟨hfm, C, hC⟩ := hf
    set fp : X × X → ℝ := fun p => max (f p) 0 with hfp_def
    have hfp : Monod.IsBddMeasOn R fp := ⟨hfm.max measurable_const, max C 0, fun p hp => by
      simp only [hfp_def]
      rw [abs_of_nonneg (le_max_right _ _)]
      exact max_le_max ((le_abs_self _).trans (hC p hp)) le_rfl⟩
    have hfp' := bdd_swap hRe hfp
    have hnull : Monod.RelNull μ R {p | f p < 0} := by
      have h := (ae_relMeasure_iff hR.measurableSet hR.countable_classes (p := fun q => 0 ≤ f q)
        (measurableSet_le measurable_const hfm)).mp hnn
      unfold Monod.RelNull
      rw [ae_iff] at h
      refine measure_mono_null ?_ h
      rintro x ⟨q, ⟨hq1, hq2⟩, rfl⟩
      simp only [mem_ofPred_eq, not_forall]
      exact ⟨q.2, hq2, not_le.mpr hq1⟩
    have hnull' := CFWPlan.Route.relNull_swap μ hRe (IsDiscreteMeasured.qi hR) hnull
    have hcg := hP.congr _ _ hf' hfp' (relNull_mono (fun p hp => by
      simp only [mem_ofPred_eq, mem_preimage, hfp_def] at hp ⊢
      by_contra h
      exact hp (max_eq_left (not_lt.mp h)).symm) hnull')
    have hnn' := hP.nonneg _ hfp' (fun p _ => le_max_right _ _)
    simp only
    refine integral_nonneg_of_ae ?_
    filter_upwards [hcg, hnn'] with x h1 h2
    rw [h1]; exact h2
  · simp only
    have e : (fun p : X × X => (1 : X × X → ℝ) p.swap) = 1 := rfl
    rw [e, integral_congr_ae hP.one]
    simp
  · intro φ β hβm hβb hβ f hf
    obtain ⟨Cβ, hβC⟩ := hβb
    simp only
    have hf' := bdd_swap hRe hf
    set G := P (fun p => f p.swap) with hG
    have hGi : Integrable G μ := integrable_mean hP hf'
    have hdomR : ∀ x ∈ φ.dom, (x, ptFun φ x) ∈ R := fun x hx => ((ptFun_spec φ).1 x hx).2.2
    -- the left side
    have eL : (fun p : X × X => (fun p : X × X =>
        if p.2 ∈ φ.cod then β p.2 * f (p.1, ptInv φ p.2) else 0) p.swap) =
        fun p => β p.1 * φ.shiftRel (fun q => f q.swap) p := by
      ext p
      rw [shiftRel_eq]
      simp only [Prod.fst_swap, Prod.snd_swap]
      split_ifs <;> simp
    have hsh := bdd_shiftRel hRe φ hf'
    have h1 := IsLeftInvariantMean.mul_fst hrefl hP hsh hβm hβC
    have h2 := hP.invariant φ _ hf'
    have hL : ∫ x, P (fun p : X × X => (fun p : X × X =>
        if p.2 ∈ φ.cod then β p.2 * f (p.1, ptInv φ p.2) else 0) p.swap) x ∂μ =
        ∫ y in φ.cod, β y * G (ptInv φ y) ∂μ := by
      rw [eL, integral_congr_ae h1, ← integral_indicator φ.measurableSet_cod]
      refine integral_congr_ae ?_
      filter_upwards [h2] with x hx
      rw [hx, shiftBase_eq]
      by_cases h : x ∈ φ.cod
      · simp [h, hG]
      · simp [h]
    -- the right side
    have eR : (fun p : X × X => (fun p : X × X => φ.dom.indicator 1 p.2 * f p) p.swap) =
        fun p => φ.dom.indicator (1 : X → ℝ) p.1 * (fun q => f q.swap) p := by
      ext p; rfl
    have h3 := IsLeftInvariantMean.mul_fst hrefl hP hf' (g := φ.dom.indicator (1 : X → ℝ))
      (measurable_const.indicator φ.measurableSet_dom : Measurable (φ.dom.indicator (1 : X → ℝ)))
      (C := 1) (fun x => by
        by_cases hx : x ∈ φ.dom
        · rw [indicator_of_mem hx, Pi.one_apply, abs_one]
        · rw [indicator_of_notMem hx, abs_zero]; exact zero_le_one)
    have hR' : ∫ x, P (fun p : X × X => (fun p : X × X => φ.dom.indicator 1 p.2 * f p) p.swap) x ∂μ
        = ∫ x in φ.dom, G x ∂μ := by
      rw [eR, integral_congr_ae h3, ← integral_indicator φ.measurableSet_dom]
      congr 1; ext x
      by_cases hx : x ∈ φ.dom
      · rw [indicator_of_mem hx, indicator_of_mem hx, Pi.one_apply, one_mul]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
    rw [hL, hR']
    have hδ : ∀ᵐ x ∂μ, x ∈ φ.dom →
        (module μ R (x, ptFun φ x)).toReal * (module μ R (ptFun φ x, x)).toReal = 1 := by
      filter_upwards [ae_module_mul_swap hR] with x hx hxd
      exact hx _ (hdomR x hxd)
    have hint : Integrable (φ.dom.indicator fun x =>
        (module μ R (x, ptFun φ x)).toReal * G x * (module μ R (ptFun φ x, x)).toReal) μ := by
      refine (hGi.indicator φ.measurableSet_dom).congr ?_
      filter_upwards [hδ] with x hx
      by_cases hxd : x ∈ φ.dom
      · rw [indicator_of_mem hxd, indicator_of_mem hxd, mul_comm _ (G x), mul_assoc, hx hxd,
          mul_one]
      · rw [indicator_of_notMem hxd, indicator_of_notMem hxd]
    calc ∫ y in φ.cod, β y * G (ptInv φ y) ∂μ
        = ∫ y in φ.cod, (fun x => (module μ R (x, ptFun φ x)).toReal * G x) (ptInv φ y) ∂μ := by
          refine setIntegral_congr_ae φ.measurableSet_cod ?_
          filter_upwards [hβ] with y hy hyc
          rw [hy hyc, ((ptFun_spec φ).2.1 y hyc).2]
      _ = ∫ x in φ.dom, (module μ R (x, ptFun φ x)).toReal * G x *
            (module μ R (ptFun φ x, x)).toReal ∂μ := integral_comp_ptInv hR φ hint
      _ = ∫ x in φ.dom, G x ∂μ := by
          refine setIntegral_congr_ae φ.measurableSet_dom ?_
          filter_upwards [hδ] with x hx hxd
          rw [mul_comm _ (G x), mul_assoc, hx hxd, mul_one]

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias exists_invariant_state := CFWPlan.Main.P3.exists_invariant_state

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
/-- The f.s.r. "with fibres `F_y = {x | (y, x) ∈ G}`, `y ∈ Ω`" of CFW p. 442
(`T = {(x', x) | x', x ∈ F_y for some y ∈ Ω'}`). -/
def rowRel (Ω : Set X) (G : Set (X × X)) : Set (X × X) :=
  {p | ∃ y ∈ Ω, (y, p.1) ∈ G ∧ (y, p.2) ∈ G}

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
/-- Two subtype sums agree when the zero-extended summands agree (copied from P2). -/
theorem tsum_subtype_congr {α : Type*} {p q : α → Prop} {f g : α → ℝ≥0∞}
    (h : ∀ x, {x | p x}.indicator f x = {x | q x}.indicator g x) :
    ∑' x : {x // p x}, f x = ∑' x : {x // q x}, g x :=
  (tsum_subtype {x | p x} f).trans ((tsum_congr h).trans (tsum_subtype {x | q x} g).symm)

/-- Two subtype sums of the same function agree when the predicates agree. -/
theorem tsum_subtype_eq_of_iff {α : Type*} {p q : α → Prop} {f : α → ℝ≥0∞}
    (h : ∀ x, p x ↔ q x) :
    ∑' x : {x // p x}, f x = ∑' x : {x // q x}, f x :=
  (Equiv.subtypeEquivRight h).tsum_eq (fun x : {x // q x} => f x)

/-- Finite sums of lower integrals are below the lower integral of the sum (no measurability). -/
theorem sum_lintegral_le {α ι : Type*} [MeasurableSpace α] {μ : Measure α} (s : Finset ι)
    (f : ι → α → ℝ≥0∞) : ∑ i ∈ s, ∫⁻ a, f i a ∂μ ≤ ∫⁻ a, ∑ i ∈ s, f i a ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    calc ∫⁻ a, f j a ∂μ + ∑ i ∈ s, ∫⁻ a, f i a ∂μ
        ≤ ∫⁻ a, f j a ∂μ + ∫⁻ a, ∑ i ∈ s, f i a ∂μ := add_le_add le_rfl ih
      _ ≤ ∫⁻ a, f j a + ∑ i ∈ s, f i a ∂μ := le_lintegral_add _ _
      _ = ∫⁻ a, ∑ i ∈ insert j s, f i a ∂μ := by
          congr 1
          funext a
          rw [Finset.sum_insert hj]

/-- In the quotient by an equivalence relation, `Quot.mk` identifies exactly related points
(copied from P2). -/
theorem quot_mk_eq_iff {α : Type*} {r : α → α → Prop} (hr : Equivalence r) {a b : α} :
    Quot.mk r a = Quot.mk r b ↔ r a b :=
  ⟨fun h => hr.eqvGen_iff.1 (Quot.eqvGen_exact h), fun h => Quot.sound h⟩

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
theorem ptFun_of_mem' {R : Set (X × X)} (φ : Monod.PartialTransformation R) {x : X}
    (hx : x ∈ φ.dom) : ptFun φ x = (φ.e ⟨x, hx⟩ : X) := by
  unfold ptFun
  exact dif_pos hx

theorem mem_ptGraph {R : Set (X × X)} (φ : Monod.PartialTransformation R) {x : X}
    (hx : x ∈ φ.dom) : (x, ptFun φ x) ∈ CFWPlan.Route.ptGraph φ :=
  ⟨⟨x, hx⟩, by rw [ptFun_of_mem' φ hx]⟩

theorem mem_ptGraph_iff {R : Set (X × X)} (φ : Monod.PartialTransformation R) {p : X × X} :
    p ∈ CFWPlan.Route.ptGraph φ ↔ p.1 ∈ φ.dom ∧ ptFun φ p.1 = p.2 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a.2, ptFun_of_mem' φ a.2⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨a, b⟩ := p
    simp only at h1 h2
    subst h2
    exact mem_ptGraph φ h1

/-- "`m`-a.e. on the graph of `φ`" is "`μ`-a.e. on the domain of `φ`" (copied from P2). -/
theorem ae_ptGraph_iff {μ : Measure X} {R : Set (X × X)} (hR : IsDiscreteMeasured μ R)
    (φ : Monod.PartialTransformation R) {P : X × X → Prop} (hP : MeasurableSet {p | P p}) :
    (∀ᵐ p ∂relMeasure μ R, p ∈ CFWPlan.Route.ptGraph φ → P p) ↔
      ∀ᵐ x ∂μ, x ∈ φ.dom → P (x, ptFun φ x) := by
  have hG := CFWPlan.Main.measurableSet_ptGraph φ
  have hf : Measurable fun x => (x, ptFun φ x) :=
    measurable_id.prodMk (CFWPlan.Main.measurable_ptFun φ).1
  rw [← ae_restrict_iff' hG, (CFWPlan.Main.relMeasure_restrict_ptGraph hR φ).1,
    ae_map_iff hf.aemeasurable hP, ae_restrict_iff' φ.measurableSet_dom]

/-- `m (graph φ ∩ fst⁻¹ B) ≤ μ B`. -/
theorem relMeasure_ptGraph_inter_le {μ : Measure X} {R : Set (X × X)} (hR : IsDiscreteMeasured μ R)
    (φ : Monod.PartialTransformation R) {B : Set X} (hB : MeasurableSet B) :
    relMeasure μ R (Prod.fst ⁻¹' B ∩ CFWPlan.Route.ptGraph φ) ≤ μ B := by
  have hf : Measurable fun x => (x, ptFun φ x) :=
    measurable_id.prodMk (CFWPlan.Main.measurable_ptFun φ).1
  rw [← Measure.restrict_apply (measurable_fst hB), (CFWPlan.Main.relMeasure_restrict_ptGraph hR φ).1,
    Measure.map_apply hf (measurable_fst hB)]
  exact (Measure.restrict_apply_le _ _).trans (measure_mono fun x hx => hx)

/-- **Step 4a (CFW p. 442).** Pairwise disjoint finite rows define an f.s.r. -/
theorem isFiniteSubrelation_rowRel {R G : Set (X × X)} (hRe : Equivalence fun x y => (x, y) ∈ R)
    (hG : MeasurableSet G) (hGR : G ⊆ R) {Ω : Set X} (hΩ : MeasurableSet Ω)
    (hfin : ∀ y, {x | (y, x) ∈ G}.Finite)
    (hdisj : ∀ y ∈ Ω, ∀ y' ∈ Ω, y ≠ y' → Disjoint {x | (y, x) ∈ G} {x | (y', x) ∈ G}) :
    IsFiniteSubrelation R (rowRel Ω G) ∧ unitSpace (rowRel Ω G) = {x | ∃ y ∈ Ω, (y, x) ∈ G} := by
  have huniq : ∀ y ∈ Ω, ∀ y' ∈ Ω, ∀ x, (y, x) ∈ G → (y', x) ∈ G → y = y' := by
    intro y hy y' hy' x hx hx'
    by_contra hne
    exact Set.disjoint_left.1 (hdisj y hy y' hy' hne) hx hx'
  have hmeas : MeasurableSet (rowRel Ω G) := by
    set P : Set ((X × X) × X) := {q | q.2 ∈ Ω ∧ (q.2, q.1.1) ∈ G ∧ (q.2, q.1.2) ∈ G} with hPdef
    have hP : MeasurableSet P :=
      (measurable_snd hΩ).inter (((measurable_snd.prodMk (measurable_fst.comp measurable_fst)) hG).inter
        ((measurable_snd.prodMk (measurable_snd.comp measurable_fst)) hG))
    have himg : Prod.fst '' P = rowRel Ω G := by
      ext ⟨a, b⟩
      constructor
      · rintro ⟨⟨⟨a', b'⟩, y⟩, ⟨hy, ha, hb⟩, he⟩
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨y, hy, ha, hb⟩
      · rintro ⟨y, hy, ha, hb⟩
        exact ⟨((a, b), y), ⟨hy, ha, hb⟩, rfl⟩
    rw [← himg]
    refine CFWPlan.Route.measurableSet_image_fst hP fun q => ?_
    refine Set.Subsingleton.countable ?_
    intro y hy y' hy'
    exact huniq y hy.1 y' hy'.1 q.1 hy.2.1 hy'.2.1
  refine ⟨⟨hmeas, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rintro ⟨a, b⟩ ⟨y, hy, ha, hb⟩
    exact hRe.trans (hRe.symm (hGR ha)) (hGR hb)
  · rintro ⟨a, b⟩ ⟨y, hy, ha, hb⟩
    exact ⟨⟨y, hy, ha, ha⟩, ⟨y, hy, hb, hb⟩⟩
  · rintro a b ⟨y, hy, ha, hb⟩
    exact ⟨y, hy, hb, ha⟩
  · rintro a b c ⟨y, hy, ha, hb⟩ ⟨y', hy', hb', hc⟩
    have := huniq y hy y' hy' b hb hb'
    subst this
    exact ⟨y, hy, ha, hc⟩
  · intro a
    by_cases h : ∃ y ∈ Ω, (y, a) ∈ G
    · obtain ⟨y, hy, ha⟩ := h
      refine (hfin y).subset ?_
      rintro b ⟨y', hy', ha', hb'⟩
      have := huniq y hy y' hy' a ha ha'
      subst this
      exact hb'
    · convert Set.finite_empty
      ext b
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨y, hy, ha, -⟩
      exact h ⟨y, hy, ha⟩
  · ext x
    simp only [unitSpace, rowRel, mem_ofPred_eq, and_self]

/-- `m⁻¹` of a Borel subset of `R` as an integral of row sums of `δ⁻¹`. -/
theorem relMeasure_swap_apply_rows {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) {S : Set (X × X)} (hS : MeasurableSet S) (hSR : S ⊆ R) :
    (relMeasure μ R).map Prod.swap S =
      ∫⁻ y, ∑' x : {x : X // (y, x) ∈ S}, (module μ R (y, x))⁻¹ ∂μ := by
  have hδi : Measurable fun p => (module μ R p)⁻¹ := (Measure.measurable_rnDeriv _ _).inv
  rw [CFWPlan.Main.relMeasure_swap_eq_withDensity hR, withDensity_apply _ hS,
    ← lintegral_indicator hS,
    CFWPlan.Main.lintegral_relMeasure hR.measurableSet hR.countable_classes (hδi.indicator hS)]
  refine lintegral_congr fun y => ?_
  refine tsum_subtype_congr (p := fun x => (y, x) ∈ R) (q := fun x => (y, x) ∈ S)
    (f := fun x => S.indicator (fun p => (module μ R p)⁻¹) (y, x))
    (g := fun x => (module μ R (y, x))⁻¹) fun x => ?_
  by_cases hx : (y, x) ∈ S
  · rw [indicator_of_mem (show x ∈ {x | (y, x) ∈ R} from hSR hx),
      indicator_of_mem (show x ∈ {x | (y, x) ∈ S} from hx), indicator_of_mem hx]
  · rw [indicator_of_notMem (show x ∉ {x | (y, x) ∈ S} from hx)]
    by_cases hxR : (y, x) ∈ R
    · rw [indicator_of_mem (show x ∈ {x | (y, x) ∈ R} from hxR), indicator_of_notMem hx]
    · rw [indicator_of_notMem (show x ∉ {x | (y, x) ∈ R} from hxR)]

/-- **Step 3 (CFW p. 441: "the set `Ω` … is non-negligible").** -/
theorem exists_good_rows {μ : Measure X} [IsProbabilityMeasure μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) {n : ℕ} (φ : Fin n → Monod.PartialTransformation R)
    {L : Set (X × X)} (hL : MeasurableSet L) (hLR : L ⊆ R) {ε : ℝ} (hε : 0 < ε)
    (hineq : ∑ i, (relMeasure μ R).map Prod.swap
        {p | p.2 ∈ (φ i).dom ∧ ((p.1, ptFun (φ i) p.2) ∈ L ↔ p ∉ L)} <
      ENNReal.ofReal ε * (relMeasure μ R).map Prod.swap L) :
    ∃ Ω : Set X, MeasurableSet Ω ∧ 0 < μ Ω ∧ ∀ y ∈ Ω,
      ∑ i, ∑' x : {x : X // x ∈ (φ i).dom ∧ ((y, ptFun (φ i) x) ∈ L ↔ (y, x) ∉ L)},
          (module μ R (y, x))⁻¹ <
        ENNReal.ofReal ε * ∑' x : {x : X // (y, x) ∈ L}, (module μ R (y, x))⁻¹ := by
  have hRe := hR.equivalence
  have hδi : Measurable fun p => (module μ R p)⁻¹ := (Measure.measurable_rnDeriv _ _).inv
  set E : Fin n → Set (X × X) :=
    fun i => {p | p.2 ∈ (φ i).dom ∧ ((p.1, ptFun (φ i) p.2) ∈ L ↔ p ∉ L)} with hEdef
  have hφm : ∀ i, Measurable (ptFun (φ i)) := fun i => (CFWPlan.Main.measurable_ptFun (φ i)).1
  have hE : ∀ i, MeasurableSet (E i) := by
    intro i
    refine (measurable_snd (φ i).measurableSet_dom).inter ?_
    have h1 : MeasurableSet {p : X × X | (p.1, ptFun (φ i) p.2) ∈ L} :=
      (measurable_fst.prodMk ((hφm i).comp measurable_snd)) hL
    exact (h1.iff hL.compl)
  have hER : ∀ i, E i ⊆ R := by
    rintro i ⟨y, x⟩ ⟨hx, hiff⟩
    by_cases hyx : (y, x) ∈ L
    · exact hLR hyx
    · have h2 : (y, ptFun (φ i) x) ∈ L := hiff.2 hyx
      have h3 : (x, ptFun (φ i) x) ∈ R := ((CFWPlan.Main.ptFun_spec (φ i)).1 x hx).2.2
      exact hRe.trans (hLR h2) (hRe.symm h3)
  have hcount : ∀ (S : Set (X × X)), S ⊆ R → ∀ y, {x | (y, x) ∈ S}.Countable :=
    fun S hS y => (hR.countable_classes y).mono fun x hx => hS hx
  set f : Fin n → X → ℝ≥0∞ := fun i y => ∑' x : {x : X // (y, x) ∈ E i}, (module μ R (y, x))⁻¹
    with hfdef
  set g : X → ℝ≥0∞ := fun y => ∑' x : {x : X // (y, x) ∈ L}, (module μ R (y, x))⁻¹ with hgdef
  have hf : ∀ i, Measurable (f i) := fun i =>
    CFWPlan.Main.measurable_tsum_section (hE i) (hcount _ (hER i)) hδi
  have hg : Measurable g := CFWPlan.Main.measurable_tsum_section hL (hcount _ hLR) hδi
  set Ω : Set X := {y | ∑ i, f i y < ENNReal.ofReal ε * g y} with hΩdef
  have hΩ : MeasurableSet Ω :=
    measurableSet_lt (Finset.measurable_sum _ fun i _ => hf i) (hg.const_mul _)
  refine ⟨Ω, hΩ, ?_, fun y hy => hy⟩
  rw [pos_iff_ne_zero]
  intro h0
  have hae : ∀ᵐ y ∂μ, ENNReal.ofReal ε * g y ≤ ∑ i, f i y := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with y hy
    exact not_lt.1 hy
  have h1 : ∑ i, (relMeasure μ R).map Prod.swap (E i) = ∫⁻ y, ∑ i, f i y ∂μ := by
    rw [lintegral_finsetSum _ fun i _ => hf i]
    exact Finset.sum_congr rfl fun i _ => relMeasure_swap_apply_rows hR (hE i) (hER i)
  have h2 : (relMeasure μ R).map Prod.swap L = ∫⁻ y, g y ∂μ := relMeasure_swap_apply_rows hR hL hLR
  have h3 : ENNReal.ofReal ε * ∫⁻ y, g y ∂μ ≤ ∫⁻ y, ∑ i, f i y ∂μ := by
    rw [← lintegral_const_mul _ hg]
    exact lintegral_mono_ae hae
  rw [h1, h2] at hineq
  exact absurd hineq (not_lt.2 h3)

/-- For `μ`-a.e. `a ∈ dom φ`, `δ(φ a, a) = δ(a, φ a)⁻¹`. -/
theorem ae_module_swap_graph {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (φ : Monod.PartialTransformation R) :
    ∀ᵐ a ∂μ, a ∈ φ.dom → module μ R (ptFun φ a, a) = (module μ R (a, ptFun φ a))⁻¹ := by
  have hδ : Measurable (module μ R) := Measure.measurable_rnDeriv _ _
  refine (ae_ptGraph_iff hR φ (P := fun p => module μ R p.swap = (module μ R p)⁻¹)
    (measurableSet_eq_fun (hδ.comp measurable_swap) hδ.inv)).1 ?_
  filter_upwards [CFWPlan.Main.module_swap hR] with p hp _ using hp

/-- **The transposition bound** (CFW p. 441): moving the second coordinate along `φ` costs at most
the factor `c⁻¹` in `m⁻¹`. -/
theorem lintegral_transpose_le {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (φ : Monod.PartialTransformation R) {c : ℝ≥0} (hc : 0 < c)
    (hφ : ∀ᵐ a ∂μ, a ∈ φ.dom → (c : ℝ≥0∞) ≤ module μ R (a, ptFun φ a) ∧
      module μ R (a, ptFun φ a) ≤ (c : ℝ≥0∞)⁻¹)
    {h : X × X → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ p, φ.dom.indicator (fun x => h (p.1, ptFun φ x)) p.2 ∂((relMeasure μ R).map Prod.swap) ≤
      (c : ℝ≥0∞)⁻¹ * ∫⁻ p, h p ∂((relMeasure μ R).map Prod.swap) := by
  have hRe := hR.equivalence
  have hsp := CFWPlan.Main.ptFun_spec φ
  have hφm := (CFWPlan.Main.measurable_ptFun φ).1
  have hδ : Measurable (module μ R) := Measure.measurable_rnDeriv _ _
  set H : X → ℝ≥0∞ := fun x => ∑' y : {y : X // (y, x) ∈ R}, h (y, x) with hHdef
  have hH : Measurable H := by
    have := CFWPlan.Main.measurable_tsum_section (E := Prod.swap ⁻¹' R)
      (measurable_swap hR.measurableSet) (fun x => IsDiscreteMeasured.countable_left hR x)
      (g := fun p => h p.swap) (hh.comp measurable_swap)
    exact this
  have hmeas1 : Measurable fun p : X × X => φ.dom.indicator (fun x => h (p.1, ptFun φ x)) p.2 := by
    have : (fun p : X × X => φ.dom.indicator (fun x => h (p.1, ptFun φ x)) p.2) =
        (Prod.snd ⁻¹' φ.dom).indicator (fun p => h (p.1, ptFun φ p.2)) := by
      funext p
      by_cases hp : p.2 ∈ φ.dom
      · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ Prod.snd ⁻¹' φ.dom from hp)]
      · rw [indicator_of_notMem hp, indicator_of_notMem (show p ∉ Prod.snd ⁻¹' φ.dom from hp)]
    rw [this]
    exact (hh.comp (measurable_fst.prodMk (hφm.comp measurable_snd))).indicator
      (measurable_snd φ.measurableSet_dom)
  have eL : ∫⁻ p, φ.dom.indicator (fun x => h (p.1, ptFun φ x)) p.2
      ∂((relMeasure μ R).map Prod.swap) = ∫⁻ x in φ.dom, H (ptFun φ x) ∂μ := by
    rw [CFWPlan.Main.lintegral_relMeasure_swap hR hmeas1, ← lintegral_indicator φ.measurableSet_dom]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ φ.dom
    · rw [indicator_of_mem hx]
      simp only [indicator_of_mem hx, hHdef]
      have hxφ := (hsp.1 x hx).2.2
      exact tsum_subtype_eq_of_iff (f := fun y => h (y, ptFun φ x)) fun y =>
        ⟨fun h1 => hRe.trans h1 hxφ, fun h1 => hRe.trans h1 (hRe.symm hxφ)⟩
    · rw [indicator_of_notMem hx]
      simp only [indicator_of_notMem hx, tsum_zero]
  have eR : ∫⁻ p, h p ∂((relMeasure μ R).map Prod.swap) = ∫⁻ x, H x ∂μ :=
    CFWPlan.Main.lintegral_relMeasure_swap hR hh
  have hcv := CFWPlan.Main.lintegral_comp_ptInv hR φ (g := fun x => H (ptFun φ x)) (hH.comp hφm)
  have hcod : ∫⁻ y in φ.cod, H (ptFun φ (ptInv φ y)) ∂μ = ∫⁻ y in φ.cod, H y ∂μ :=
    setLIntegral_congr_fun φ.measurableSet_cod fun y hy => by rw [(hsp.2.1 y hy).2]
  have hlow : (c : ℝ≥0∞) * ∫⁻ x in φ.dom, H (ptFun φ x) ∂μ ≤
      ∫⁻ x in φ.dom, H (ptFun φ x) * module μ R (ptFun φ x, x) ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
    refine setLIntegral_mono_ae ((hH.comp hφm).mul (hδ.comp (hφm.prodMk measurable_id))).aemeasurable ?_
    filter_upwards [hφ, ae_module_swap_graph hR φ] with x hx1 hx2 hxd
    rw [mul_comm]
    gcongr
    rw [hx2 hxd]
    have := (hx1 hxd).2
    calc (c : ℝ≥0∞) = ((c : ℝ≥0∞)⁻¹)⁻¹ := (inv_inv _).symm
      _ ≤ (module μ R (x, ptFun φ x))⁻¹ := ENNReal.inv_le_inv.2 this
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  calc ∫⁻ p, φ.dom.indicator (fun x => h (p.1, ptFun φ x)) p.2 ∂((relMeasure μ R).map Prod.swap)
      = ∫⁻ x in φ.dom, H (ptFun φ x) ∂μ := eL
    _ = (c : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) * ∫⁻ x in φ.dom, H (ptFun φ x) ∂μ) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top, one_mul]
    _ ≤ (c : ℝ≥0∞)⁻¹ * ∫⁻ x in φ.dom, H (ptFun φ x) * module μ R (ptFun φ x, x) ∂μ :=
        by gcongr
    _ = (c : ℝ≥0∞)⁻¹ * ∫⁻ y in φ.cod, H y ∂μ := by rw [← hcv, hcod]
    _ ≤ (c : ℝ≥0∞)⁻¹ * ∫⁻ p, h p ∂((relMeasure μ R).map Prod.swap) := by
        rw [eR]
        gcongr
        exact Measure.restrict_le_self

/-- Layer cake for one value: `t = ∫₀^∞ 1[a ≤ t] da`. -/
theorem volume_Ioi_le_eq (t : ℝ) (ht : 0 ≤ t) :
    (volume.restrict (Ioi (0 : ℝ))) {a : ℝ | a ≤ t} = ENNReal.ofReal t := by
  rw [show {a : ℝ | a ≤ t} = Iic t from rfl, Measure.restrict_apply measurableSet_Iic,
    Iic_inter_Ioi, Real.volume_Ioc, sub_zero]

/-- Layer cake for a difference: `|t - t'| = ∫₀^∞ |1[a ≤ t] - 1[a ≤ t']| da` for `t, t' ≥ 0`. -/
theorem volume_Ioi_xor_eq (t t' : ℝ) (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    (volume.restrict (Ioi (0 : ℝ))) {a : ℝ | (a ≤ t ↔ ¬ a ≤ t')} = ENNReal.ofReal |t - t'| := by
  have hm : MeasurableSet {a : ℝ | (a ≤ t ↔ ¬ a ≤ t')} :=
    (measurableSet_Iic (a := t)).iff (measurableSet_Iic (a := t')).compl
  rw [Measure.restrict_apply hm]
  have hset : {a : ℝ | (a ≤ t ↔ ¬ a ≤ t')} ∩ Ioi 0 = Ioc (min t t') (max t t') := by
    ext a
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, mem_Ioc, min_lt_iff, le_max_iff]
    constructor
    · rintro ⟨h, ha⟩
      by_cases h1 : a ≤ t
      · have h2 := h.1 h1
        exact ⟨Or.inr (lt_of_not_ge h2), Or.inl h1⟩
      · have h2 : a ≤ t' := by
          by_contra h3
          exact h1 (h.2 h3)
        exact ⟨Or.inl (lt_of_not_ge h1), Or.inr h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact absurd h2 (not_le.2 h1)
        · exact ⟨fun h => absurd h (not_le.2 h1), fun h => absurd h2 h⟩
        · exact ⟨fun _ => not_le.2 h1, fun _ => h2⟩
        · exact absurd h2 (not_le.2 h1)
      · rcases h1 with h1 | h1
        · exact lt_of_le_of_lt ht h1
        · exact lt_of_le_of_lt ht' h1
  rw [hset, Real.volume_Ioc, max_sub_min_eq_abs, abs_sub_comm]

/-- **The level-set step** (CFW p. 441, Namioka's trick): if a nonnegative `g` is almost invariant
in the `L¹` sense, then so is one of its level sets `{g ≥ a}`, `a > 0`. -/
theorem exists_level_set {M : Measure (X × X)} [SFinite M] {n : ℕ} (f : Fin n → X → X)
    (hf : ∀ i, Measurable (f i)) (D : Fin n → Set X) (hD : ∀ i, MeasurableSet (D i))
    {g : X × X → ℝ} (hg : Measurable g) (hg0 : ∀ p, 0 ≤ g p) (ε : ℝ≥0∞)
    (hlt : ∑ i, ∫⁻ p, ENNReal.ofReal ((D i).indicator
        (fun x => |g (p.1, f i x) - g (p.1, x)|) p.2) ∂M < ε * ∫⁻ p, ENNReal.ofReal (g p) ∂M) :
    ∃ a : ℝ, 0 < a ∧ ∑ i, M {p | p.2 ∈ D i ∧
        ((p.1, f i p.2) ∈ {q | a ≤ g q} ↔ p ∉ {q | a ≤ g q})} < ε * M {q | a ≤ g q} := by
  set ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hνdef
  set S : Fin n → Set ((X × X) × ℝ) := fun i =>
    {z | z.1.2 ∈ D i ∧ (z.2 ≤ g (z.1.1, f i z.1.2) ↔ ¬ z.2 ≤ g z.1)} with hSdef
  set S₀ : Set ((X × X) × ℝ) := {z | z.2 ≤ g z.1} with hS₀def
  have hS : ∀ i, MeasurableSet (S i) := by
    intro i
    refine (measurable_snd.comp measurable_fst (hD i)).inter ?_
    refine (measurableSet_le measurable_snd
      (hg.comp ((measurable_fst.comp measurable_fst).prodMk
        ((hf i).comp (measurable_snd.comp measurable_fst))))).iff
      (measurableSet_le measurable_snd (hg.comp measurable_fst)).compl
  have hS₀ : MeasurableSet S₀ := measurableSet_le measurable_snd (hg.comp measurable_fst)
  -- pointwise layer cake
  have hpt : ∀ i p, ENNReal.ofReal ((D i).indicator (fun x => |g (p.1, f i x) - g (p.1, x)|) p.2) =
      ∫⁻ a, (S i).indicator 1 (p, a) ∂ν := by
    intro i p
    have hm : MeasurableSet ((fun a : ℝ => (p, a)) ⁻¹' S i) := measurable_prodMk_left (hS i)
    have : (fun a => (S i).indicator (1 : (X × X) × ℝ → ℝ≥0∞) (p, a)) =
        ((fun a : ℝ => (p, a)) ⁻¹' S i).indicator 1 := by
      funext a
      by_cases ha : (p, a) ∈ S i
      · rw [indicator_of_mem ha, indicator_of_mem (show a ∈ (fun a : ℝ => (p, a)) ⁻¹' S i from ha)]
        rfl
      · rw [indicator_of_notMem ha,
          indicator_of_notMem (show a ∉ (fun a : ℝ => (p, a)) ⁻¹' S i from ha)]
    rw [this, lintegral_indicator_one hm]
    by_cases hp : p.2 ∈ D i
    · rw [indicator_of_mem hp, ← volume_Ioi_xor_eq _ _ (hg0 _) (hg0 _)]
      congr 1
      ext a
      simp only [hSdef, mem_preimage, mem_ofPred_eq]
      exact ⟨fun h => ⟨hp, h⟩, fun h => h.2⟩
    · rw [indicator_of_notMem hp, ENNReal.ofReal_zero]
      symm
      convert measure_empty (μ := ν)
      ext a
      simp only [hSdef, mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h => hp h.1
  have hpt₀ : ∀ p, ENNReal.ofReal (g p) = ∫⁻ a, S₀.indicator 1 (p, a) ∂ν := by
    intro p
    have hm : MeasurableSet ((fun a : ℝ => (p, a)) ⁻¹' S₀) := measurable_prodMk_left hS₀
    have : (fun a => S₀.indicator (1 : (X × X) × ℝ → ℝ≥0∞) (p, a)) =
        ((fun a : ℝ => (p, a)) ⁻¹' S₀).indicator 1 := by
      funext a
      by_cases ha : (p, a) ∈ S₀
      · rw [indicator_of_mem ha, indicator_of_mem (show a ∈ (fun a : ℝ => (p, a)) ⁻¹' S₀ from ha)]
        rfl
      · rw [indicator_of_notMem ha,
          indicator_of_notMem (show a ∉ (fun a : ℝ => (p, a)) ⁻¹' S₀ from ha)]
    rw [this, lintegral_indicator_one hm, ← volume_Ioi_le_eq _ (hg0 p)]
    rfl
  -- Tonelli
  set F : Fin n → ℝ → ℝ≥0∞ := fun i a => ∫⁻ p, (S i).indicator 1 (p, a) ∂M with hFdef
  set G : ℝ → ℝ≥0∞ := fun a => ∫⁻ p, S₀.indicator 1 (p, a) ∂M with hGdef
  have hF : ∀ i, Measurable (F i) := fun i =>
    Measurable.lintegral_prod_left' (measurable_one.indicator (hS i))
  have hG : Measurable G := Measurable.lintegral_prod_left' (measurable_one.indicator hS₀)
  have hTi : ∀ i, ∫⁻ p, ENNReal.ofReal ((D i).indicator
      (fun x => |g (p.1, f i x) - g (p.1, x)|) p.2) ∂M = ∫⁻ a, F i a ∂ν := by
    intro i
    simp only [hpt i]
    exact lintegral_lintegral_swap (measurable_one.indicator (hS i)).aemeasurable
  have hT₀ : ∫⁻ p, ENNReal.ofReal (g p) ∂M = ∫⁻ a, G a ∂ν := by
    simp only [hpt₀]
    exact lintegral_lintegral_swap (measurable_one.indicator hS₀).aemeasurable
  rw [hT₀] at hlt
  simp only [hTi] at hlt
  rw [← lintegral_finsetSum _ fun i _ => hF i, ← lintegral_const_mul _ hG] at hlt
  by_contra hcon
  push Not at hcon
  have hae : ∀ᵐ a ∂ν, ε * G a ≤ ∑ i, F i a := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun a ha => ?_
    have h := hcon a ha
    have e1 : ∀ i, F i a = M {p | p.2 ∈ D i ∧
        ((p.1, f i p.2) ∈ {q | a ≤ g q} ↔ p ∉ {q | a ≤ g q})} := by
      intro i
      calc F i a = ∫⁻ p, ((fun x : X × X => (x, a)) ⁻¹' S i).indicator 1 p ∂M := rfl
        _ = M ((fun x : X × X => (x, a)) ⁻¹' S i) :=
            lintegral_indicator_one (measurable_prodMk_right (hS i))
        _ = _ := rfl
    have e2 : G a = M {q | a ≤ g q} := by
      calc G a = ∫⁻ p, ((fun x : X × X => (x, a)) ⁻¹' S₀).indicator 1 p ∂M := rfl
        _ = M ((fun x : X × X => (x, a)) ⁻¹' S₀) :=
            lintegral_indicator_one (measurable_prodMk_right hS₀)
        _ = _ := rfl
    simp only [e1, e2]
    exact h
  exact absurd (lintegral_mono_ae hae) (not_le.2 hlt)

omit [StandardBorelSpace X] in
theorem measurableEmbedding_swap' : MeasurableEmbedding (Prod.swap : X × X → X × X) :=
  (MeasurableEquiv.prodComm : X × X ≃ᵐ X × X).measurableEmbedding

/-- The almost-invariance integrand of `exists_reiter` is measurable. -/
theorem measurable_diff_integrand {R : Set (X × X)} (φ : Monod.PartialTransformation R)
    {g : X × X → ℝ} (hg : Measurable g) :
    Measurable fun p : X × X =>
      ENNReal.ofReal (φ.dom.indicator (fun x => |g (p.1, ptFun φ x) - g (p.1, x)|) p.2) := by
  have hφm := (CFWPlan.Main.measurable_ptFun φ).1
  have : (fun p : X × X => φ.dom.indicator (fun x => |g (p.1, ptFun φ x) - g (p.1, x)|) p.2) =
      (Prod.snd ⁻¹' φ.dom).indicator (fun p => |g (p.1, ptFun φ p.2) - g p|) := by
    funext p
    by_cases hp : p.2 ∈ φ.dom
    · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ Prod.snd ⁻¹' φ.dom from hp)]
    · rw [indicator_of_notMem hp, indicator_of_notMem (show p ∉ Prod.snd ⁻¹' φ.dom from hp)]
  have h : Measurable fun p : X × X =>
      φ.dom.indicator (fun x => |g (p.1, ptFun φ x) - g (p.1, x)|) p.2 := by
    rw [this]
    exact (((hg.comp (measurable_fst.prodMk (hφm.comp measurable_snd))).sub hg).abs).indicator
      (measurable_snd φ.measurableSet_dom)
  exact ENNReal.measurable_ofReal.comp h

/-- Changing `g` changes the almost-invariance integral by at most `(c⁻¹ + 1) ‖g - g'‖₁`. -/
theorem lintegral_diff_le {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (φ : Monod.PartialTransformation R) {c : ℝ≥0} (hc : 0 < c)
    (hφ : ∀ᵐ a ∂μ, a ∈ φ.dom → (c : ℝ≥0∞) ≤ module μ R (a, ptFun φ a) ∧
      module μ R (a, ptFun φ a) ≤ (c : ℝ≥0∞)⁻¹)
    {g g' : X × X → ℝ} (hg : Measurable g) (hg' : Measurable g') :
    ∫⁻ p, ENNReal.ofReal (φ.dom.indicator (fun x => |g (p.1, ptFun φ x) - g (p.1, x)|) p.2)
        ∂((relMeasure μ R).map Prod.swap) ≤
      ∫⁻ p, ENNReal.ofReal (φ.dom.indicator (fun x => |g' (p.1, ptFun φ x) - g' (p.1, x)|) p.2)
        ∂((relMeasure μ R).map Prod.swap) +
      ((c : ℝ≥0∞)⁻¹ + 1) * ∫⁻ p, ENNReal.ofReal |g p - g' p| ∂((relMeasure μ R).map Prod.swap) := by
  set M := (relMeasure μ R).map Prod.swap with hMdef
  have hφm := (CFWPlan.Main.measurable_ptFun φ).1
  set e : X × X → ℝ≥0∞ := fun p => ENNReal.ofReal |g p - g' p| with hedef
  have he : Measurable e := ENNReal.measurable_ofReal.comp (hg.sub hg').abs
  have hpt : ∀ p : X × X,
      ENNReal.ofReal (φ.dom.indicator (fun x => |g (p.1, ptFun φ x) - g (p.1, x)|) p.2) ≤
        ENNReal.ofReal (φ.dom.indicator (fun x => |g' (p.1, ptFun φ x) - g' (p.1, x)|) p.2) +
        (φ.dom.indicator (fun x => e (p.1, ptFun φ x)) p.2 + e p) := by
    intro p
    by_cases hp : p.2 ∈ φ.dom
    · simp only [indicator_of_mem hp, hedef]
      set q : X × X := (p.1, ptFun φ p.2)
      have h1 : |g q - g (p.1, p.2)| ≤ |g' q - g' (p.1, p.2)| + (|g q - g' q| + |g p - g' p|) := by
        have : |g q - g (p.1, p.2)| = |(g' q - g' (p.1, p.2)) + ((g q - g' q) - (g p - g' p))| := by
          congr 1
          ring
        rw [this]
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        exact abs_sub _ _
      calc ENNReal.ofReal |g q - g (p.1, p.2)|
          ≤ ENNReal.ofReal (|g' q - g' (p.1, p.2)| + (|g q - g' q| + |g p - g' p|)) :=
            ENNReal.ofReal_le_ofReal h1
        _ ≤ _ := by
            rw [ENNReal.ofReal_add (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _)),
              ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    · simp only [indicator_of_notMem hp, ENNReal.ofReal_zero, zero_add]
      exact bot_le
  have hm1 := measurable_diff_integrand φ hg'
  have hm2 : Measurable fun p : X × X => φ.dom.indicator (fun x => e (p.1, ptFun φ x)) p.2 := by
    have : (fun p : X × X => φ.dom.indicator (fun x => e (p.1, ptFun φ x)) p.2) =
        (Prod.snd ⁻¹' φ.dom).indicator (fun p => e (p.1, ptFun φ p.2)) := by
      funext p
      by_cases hp : p.2 ∈ φ.dom
      · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ Prod.snd ⁻¹' φ.dom from hp)]
      · rw [indicator_of_notMem hp, indicator_of_notMem (show p ∉ Prod.snd ⁻¹' φ.dom from hp)]
    rw [this]
    exact (he.comp (measurable_fst.prodMk (hφm.comp measurable_snd))).indicator
      (measurable_snd φ.measurableSet_dom)
  calc _ ≤ ∫⁻ p, ENNReal.ofReal (φ.dom.indicator (fun x => |g' (p.1, ptFun φ x) - g' (p.1, x)|) p.2) +
        (φ.dom.indicator (fun x => e (p.1, ptFun φ x)) p.2 + e p) ∂M := lintegral_mono hpt
    _ = ∫⁻ p, ENNReal.ofReal (φ.dom.indicator (fun x => |g' (p.1, ptFun φ x) - g' (p.1, x)|) p.2) ∂M +
        (∫⁻ p, φ.dom.indicator (fun x => e (p.1, ptFun φ x)) p.2 ∂M + ∫⁻ p, e p ∂M) := by
        rw [lintegral_add_left hm1, lintegral_add_left hm2]
    _ ≤ _ := by
        gcongr
        calc ∫⁻ p, φ.dom.indicator (fun x => e (p.1, ptFun φ x)) p.2 ∂M + ∫⁻ p, e p ∂M
            ≤ (c : ℝ≥0∞)⁻¹ * ∫⁻ p, e p ∂M + ∫⁻ p, e p ∂M := by
              gcongr
              exact lintegral_transpose_le hR φ hc hφ he
          _ = ((c : ℝ≥0∞)⁻¹ + 1) * ∫⁻ p, e p ∂M := by ring

/-- The inverse of a partial transformation of a symmetric relation. -/
def ptSymm {R : Set (X × X)} (hRs : ∀ x y, (x, y) ∈ R → (y, x) ∈ R)
    (φ : Monod.PartialTransformation R) : Monod.PartialTransformation R where
  dom := φ.cod
  cod := φ.dom
  measurableSet_dom := φ.measurableSet_cod
  measurableSet_cod := φ.measurableSet_dom
  e := φ.e.symm
  graph_subset := fun b => by
    have h := φ.graph_subset (φ.e.symm b)
    rw [MeasurableEquiv.apply_symm_apply] at h
    exact hRs _ _ h

theorem ptFun_ptSymm {R : Set (X × X)} (hRs : ∀ x y, (x, y) ∈ R → (y, x) ∈ R)
    (φ : Monod.PartialTransformation R) : ptFun (ptSymm hRs φ) = ptInv φ := rfl

theorem ptInv_ptSymm {R : Set (X × X)} (hRs : ∀ x y, (x, y) ∈ R → (y, x) ∈ R)
    (φ : Monod.PartialTransformation R) : ptInv (ptSymm hRs φ) = ptFun φ := by
  funext y
  unfold ptInv ptFun
  by_cases h : y ∈ φ.dom
  · rw [dif_pos (show y ∈ (ptSymm hRs φ).cod from h), dif_pos h]
    rfl
  · rw [dif_neg (show y ∉ (ptSymm hRs φ).cod from h), dif_neg h]

/-- "a.e. on `dom φ`" transfers to "a.e. on `cod φ` at `φ⁻¹ y`" (images of null sets are null). -/
theorem ae_cod_of_ae_dom {μ : Measure X} {R : Set (X × X)} (hR : IsDiscreteMeasured μ R)
    (φ : Monod.PartialTransformation R) {P : X → Prop} (h : ∀ᵐ a ∂μ, a ∈ φ.dom → P a) :
    ∀ᵐ y ∂μ, y ∈ φ.cod → P (ptInv φ y) := by
  have hsp := CFWPlan.Main.ptFun_spec φ
  rw [ae_iff] at h ⊢
  refine measure_mono_null ?_ (IsDiscreteMeasured.qi hR _ h)
  intro y hy
  simp only [mem_ofPred_eq, Classical.not_imp] at hy
  obtain ⟨hyc, hP⟩ := hy
  obtain ⟨h1, h2⟩ := hsp.2.1 y hyc
  refine ⟨ptInv φ y, ?_, ?_⟩
  · simp only [mem_ofPred_eq, Classical.not_imp]
    exact ⟨h1, hP⟩
  · have := (hsp.1 _ h1).2.2
    rw [h2] at this
    exact this

/-- `μ`-a.e. in the second coordinate is `m⁻¹`-a.e. -/
theorem ae_swap_of_ae {μ : Measure X} {R : Set (X × X)} (hR : IsDiscreteMeasured μ R)
    {P : X → Prop} (h : ∀ᵐ x ∂μ, P x) : ∀ᵐ p ∂((relMeasure μ R).map Prod.swap), P p.2 := by
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 h)
  have h1 : ∀ᵐ p ∂((relMeasure μ R).map Prod.swap), p.2 ∉ N := by
    rw [ae_map_iff (p := fun q : X × X => q.2 ∉ N) measurable_swap.aemeasurable
      (measurable_snd hNm).compl]
    rw [CFWPlan.Main.ae_relMeasure_iff (p := fun q : X × X => q.swap.2 ∉ N) hR.measurableSet
      hR.countable_classes (measurable_fst hNm).compl]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with x hx y _ using hx
  filter_upwards [h1] with p hp
  by_contra hP
  exact hp (hNsub hP)

/-- Integrals over `m⁻¹` of functions supported on `S × X`-type sets in the second coordinate. -/
theorem lintegral_swap_indicator_eq {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) {S : Set X} (hS : MeasurableSet S) {w : X → ℝ≥0∞}
    (hw : Measurable w) {k : X × X → ℝ≥0∞} (hk : Measurable k) :
    ∫⁻ p, S.indicator (fun x => w x * k (p.1, x)) p.2 ∂((relMeasure μ R).map Prod.swap) =
      ∫⁻ x in S, w x * ∑' y : {y : X // (y, x) ∈ R}, k (y, x) ∂μ := by
  have hm : Measurable fun p : X × X => S.indicator (fun x => w x * k (p.1, x)) p.2 := by
    have : (fun p : X × X => S.indicator (fun x => w x * k (p.1, x)) p.2) =
        (Prod.snd ⁻¹' S).indicator (fun p => w p.2 * k p) := by
      funext p
      by_cases hp : p.2 ∈ S
      · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ Prod.snd ⁻¹' S from hp)]
      · rw [indicator_of_notMem hp, indicator_of_notMem (show p ∉ Prod.snd ⁻¹' S from hp)]
    rw [this]
    exact ((hw.comp measurable_snd).mul hk).indicator (measurable_snd hS)
  rw [CFWPlan.Main.lintegral_relMeasure_swap hR hm, ← lintegral_indicator hS]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ S
  · simp only [indicator_of_mem hx]
    rw [ENNReal.tsum_mul_left]
  · simp only [indicator_of_notMem hx, tsum_zero]

/-- Integrals over `m⁻¹` of `k (y, φ x)` on `x ∈ dom φ`. -/
theorem lintegral_swap_dom_eq {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (φ : Monod.PartialTransformation R) {k : X × X → ℝ≥0∞}
    (hk : Measurable k) :
    ∫⁻ p, φ.dom.indicator (fun x => k (p.1, ptFun φ x)) p.2 ∂((relMeasure μ R).map Prod.swap) =
      ∫⁻ x in φ.dom, ∑' y : {y : X // (y, ptFun φ x) ∈ R}, k (y, ptFun φ x) ∂μ := by
  have hRe := hR.equivalence
  have hsp := CFWPlan.Main.ptFun_spec φ
  have hφm := (CFWPlan.Main.measurable_ptFun φ).1
  have hm : Measurable fun p : X × X => φ.dom.indicator (fun x => k (p.1, ptFun φ x)) p.2 := by
    have : (fun p : X × X => φ.dom.indicator (fun x => k (p.1, ptFun φ x)) p.2) =
        (Prod.snd ⁻¹' φ.dom).indicator (fun p => k (p.1, ptFun φ p.2)) := by
      funext p
      by_cases hp : p.2 ∈ φ.dom
      · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ Prod.snd ⁻¹' φ.dom from hp)]
      · rw [indicator_of_notMem hp, indicator_of_notMem (show p ∉ Prod.snd ⁻¹' φ.dom from hp)]
    rw [this]
    exact (hk.comp (measurable_fst.prodMk (hφm.comp measurable_snd))).indicator
      (measurable_snd φ.measurableSet_dom)
  rw [CFWPlan.Main.lintegral_relMeasure_swap hR hm, ← lintegral_indicator φ.measurableSet_dom]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ φ.dom
  · simp only [indicator_of_mem hx]
    have hxφ := (hsp.1 x hx).2.2
    exact tsum_subtype_eq_of_iff (f := fun y => k (y, ptFun φ x)) fun y =>
      ⟨fun h1 => hRe.trans h1 hxφ, fun h1 => hRe.trans h1 (hRe.symm hxφ)⟩
  · simp only [indicator_of_notMem hx, tsum_zero]

/-- **Transposition along `φ`, lower-integral form** (CFW p. 441, "`dm(y, φᵢ(x)) = dm(y, x)`"):
`∫ 1_{dom}(x) k(y, φ x) dm⁻¹ = ∫ 1_{cod}(x) δ(φ⁻¹ x, x) k(y, x) dm⁻¹`. -/
theorem lintegral_transpose_eq {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (φ : Monod.PartialTransformation R) {k : X × X → ℝ≥0∞}
    (hk : Measurable k) :
    ∫⁻ p, φ.dom.indicator (fun x => k (p.1, ptFun φ x)) p.2 ∂((relMeasure μ R).map Prod.swap) =
      ∫⁻ p, φ.cod.indicator (fun x => module μ R (ptInv φ x, x) * k (p.1, x)) p.2
        ∂((relMeasure μ R).map Prod.swap) := by
  have hRs : ∀ x y, (x, y) ∈ R → (y, x) ∈ R := fun x y h => hR.equivalence.symm h
  have hδ : Measurable (module μ R) := Measure.measurable_rnDeriv _ _
  have hinvm := (CFWPlan.Main.measurable_ptFun φ).2
  set H : X → ℝ≥0∞ := fun x => ∑' y : {y : X // (y, x) ∈ R}, k (y, x) with hHdef
  have hH : Measurable H := by
    have := CFWPlan.Main.measurable_tsum_section (E := Prod.swap ⁻¹' R)
      (measurable_swap hR.measurableSet) (fun x => IsDiscreteMeasured.countable_left hR x)
      (g := fun p => k p.swap) (hk.comp measurable_swap)
    exact this
  rw [lintegral_swap_dom_eq hR φ hk,
    lintegral_swap_indicator_eq hR φ.measurableSet_cod (w := fun x => module μ R (ptInv φ x, x))
      (hδ.comp (hinvm.prodMk measurable_id)) hk]
  have h := CFWPlan.Main.lintegral_comp_ptInv hR (ptSymm hRs φ) hH
  rw [ptInv_ptSymm, ptFun_ptSymm] at h
  have e1 : ∫⁻ x in φ.dom, ∑' y : {y : X // (y, ptFun φ x) ∈ R}, k (y, ptFun φ x) ∂μ =
      ∫⁻ y in (ptSymm hRs φ).cod, H (ptFun φ y) ∂μ := rfl
  rw [e1, h]
  refine setLIntegral_congr_fun φ.measurableSet_cod fun x _ => ?_
  rw [mul_comm]

/-- **The measure form of the transposition**: the image of `m⁻¹|_{x ∈ dom φ}` under
`(y, x) ↦ (y, φ x)` is `δ(φ⁻¹ x, x) dm⁻¹|_{x ∈ cod φ}`. -/
theorem map_transpose_eq {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (φ : Monod.PartialTransformation R) :
    (((relMeasure μ R).map Prod.swap).restrict (Prod.snd ⁻¹' φ.dom)).map
        (fun p => (p.1, ptFun φ p.2)) =
      (((relMeasure μ R).map Prod.swap).restrict (Prod.snd ⁻¹' φ.cod)).withDensity
        (fun p => module μ R (ptInv φ p.2, p.2)) := by
  have hφm := (CFWPlan.Main.measurable_ptFun φ).1
  have hinvm := (CFWPlan.Main.measurable_ptFun φ).2
  have hδ : Measurable (module μ R) := Measure.measurable_rnDeriv _ _
  have hΦ : Measurable fun p : X × X => (p.1, ptFun φ p.2) :=
    measurable_fst.prodMk (hφm.comp measurable_snd)
  ext E hE
  rw [Measure.map_apply hΦ hE, Measure.restrict_apply (hΦ hE), withDensity_apply _ hE,
    Measure.restrict_restrict hE, ← lintegral_indicator_one ((hΦ hE).inter (measurable_snd
      φ.measurableSet_dom)), ← lintegral_indicator (hE.inter (measurable_snd φ.measurableSet_cod))]
  have h := lintegral_transpose_eq hR φ (k := E.indicator 1) (measurable_one.indicator hE)
  convert h using 2
  · funext p
    by_cases hp : p.2 ∈ φ.dom
    · rw [indicator_of_mem hp]
      by_cases hpE : (p.1, ptFun φ p.2) ∈ E
      · rw [indicator_of_mem (show p ∈ (fun p : X × X => (p.1, ptFun φ p.2)) ⁻¹' E ∩
          Prod.snd ⁻¹' φ.dom from ⟨hpE, hp⟩), indicator_of_mem hpE]
        rfl
      · rw [indicator_of_notMem (show p ∉ (fun p : X × X => (p.1, ptFun φ p.2)) ⁻¹' E ∩
          Prod.snd ⁻¹' φ.dom from fun h => hpE h.1), indicator_of_notMem hpE]
    · rw [indicator_of_notMem hp, indicator_of_notMem (show p ∉ (fun p : X × X =>
        (p.1, ptFun φ p.2)) ⁻¹' E ∩ Prod.snd ⁻¹' φ.dom from fun h => hp h.2)]
  · funext p
    by_cases hp : p.2 ∈ φ.cod
    · rw [indicator_of_mem hp]
      by_cases hpE : p ∈ E
      · rw [indicator_of_mem (show p ∈ E ∩ Prod.snd ⁻¹' φ.cod from ⟨hpE, hp⟩),
          indicator_of_mem (show (p.1, p.2) ∈ E from hpE), Pi.one_apply, mul_one]
      · rw [indicator_of_notMem (show p ∉ E ∩ Prod.snd ⁻¹' φ.cod from fun h => hpE h.1),
          indicator_of_notMem (show (p.1, p.2) ∉ E from hpE), mul_zero]
    · rw [indicator_of_notMem hp, indicator_of_notMem (show p ∉ E ∩ Prod.snd ⁻¹' φ.cod from
        fun h => hp h.2)]

/-- **Transposition along `φ`, Bochner form**: `∫ 1_{dom}(x) F(y, φ x) dm⁻¹ =
∫ 1_{cod}(x) β(x) F(y, x) dm⁻¹` for `β = δ(φ⁻¹ ·, ·)` a.e. on `cod`. -/
theorem integral_transpose_eq {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (φ : Monod.PartialTransformation R) {F : X × X → ℝ}
    (hF : Measurable F) {β : X → ℝ}
    (hβ : ∀ᵐ x ∂μ, x ∈ φ.cod → module μ R (ptInv φ x, x) < ∞ ∧
      β x = (module μ R (ptInv φ x, x)).toReal) :
    ∫ p, φ.dom.indicator (fun x => F (p.1, ptFun φ x)) p.2 ∂((relMeasure μ R).map Prod.swap) =
      ∫ p, φ.cod.indicator (fun x => β x * F (p.1, x)) p.2 ∂((relMeasure μ R).map Prod.swap) := by
  set M := (relMeasure μ R).map Prod.swap with hMdef
  have hφm := (CFWPlan.Main.measurable_ptFun φ).1
  have hinvm := (CFWPlan.Main.measurable_ptFun φ).2
  have hδ : Measurable (module μ R) := Measure.measurable_rnDeriv _ _
  have hΦ : Measurable fun p : X × X => (p.1, ptFun φ p.2) :=
    measurable_fst.prodMk (hφm.comp measurable_snd)
  have hdom : MeasurableSet (Prod.snd ⁻¹' φ.dom : Set (X × X)) := measurable_snd φ.measurableSet_dom
  have hcod : MeasurableSet (Prod.snd ⁻¹' φ.cod : Set (X × X)) := measurable_snd φ.measurableSet_cod
  have e1 : (fun p : X × X => φ.dom.indicator (fun x => F (p.1, ptFun φ x)) p.2) =
      (Prod.snd ⁻¹' φ.dom).indicator (fun p => F (p.1, ptFun φ p.2)) := by
    funext p
    by_cases hp : p.2 ∈ φ.dom
    · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ Prod.snd ⁻¹' φ.dom from hp)]
    · rw [indicator_of_notMem hp, indicator_of_notMem (show p ∉ Prod.snd ⁻¹' φ.dom from hp)]
  have e2 : (fun p : X × X => φ.cod.indicator (fun x => β x * F (p.1, x)) p.2) =
      (Prod.snd ⁻¹' φ.cod).indicator (fun p => β p.2 * F p) := by
    funext p
    by_cases hp : p.2 ∈ φ.cod
    · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ Prod.snd ⁻¹' φ.cod from hp)]
    · rw [indicator_of_notMem hp, indicator_of_notMem (show p ∉ Prod.snd ⁻¹' φ.cod from hp)]
  have hβ' := ae_swap_of_ae hR hβ
  rw [e1, e2, integral_indicator hdom, integral_indicator hcod]
  have hmap := map_transpose_eq hR φ
  calc ∫ p in Prod.snd ⁻¹' φ.dom, F (p.1, ptFun φ p.2) ∂M
      = ∫ q, F q ∂((M.restrict (Prod.snd ⁻¹' φ.dom)).map fun p => (p.1, ptFun φ p.2)) :=
        (integral_map hΦ.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ q, F q ∂((M.restrict (Prod.snd ⁻¹' φ.cod)).withDensity
          fun p => module μ R (ptInv φ p.2, p.2)) := by rw [hmap]
    _ = ∫ q, (module μ R (ptInv φ q.2, q.2)).toReal • F q ∂(M.restrict (Prod.snd ⁻¹' φ.cod)) := by
        refine integral_withDensity_eq_integral_toReal_smul
          (hδ.comp ((hinvm.comp measurable_snd).prodMk measurable_snd)) ?_ F
        rw [ae_restrict_iff' hcod]
        filter_upwards [hβ'] with q hq hqc
        exact (hq hqc).1
    _ = ∫ p in Prod.snd ⁻¹' φ.cod, β p.2 * F p ∂M := by
        refine setIntegral_congr_ae hcod ?_
        filter_upwards [hβ'] with q hq hqc
        rw [smul_eq_mul, (hq hqc).2]

/-- The transposed function is integrable. -/
theorem integrable_transpose {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (φ : Monod.PartialTransformation R) {c : ℝ≥0} (hc : 0 < c)
    (hφ : ∀ᵐ a ∂μ, a ∈ φ.dom → (c : ℝ≥0∞) ≤ module μ R (a, ptFun φ a) ∧
      module μ R (a, ptFun φ a) ≤ (c : ℝ≥0∞)⁻¹)
    {l : X × X → ℝ} (hlm : Measurable l) (hl : Integrable l ((relMeasure μ R).map Prod.swap)) :
    Integrable (fun p => φ.dom.indicator (fun x => l (p.1, ptFun φ x)) p.2)
      ((relMeasure μ R).map Prod.swap) := by
  have hφm := (CFWPlan.Main.measurable_ptFun φ).1
  have e1 : (fun p : X × X => φ.dom.indicator (fun x => l (p.1, ptFun φ x)) p.2) =
      (Prod.snd ⁻¹' φ.dom).indicator (fun p => l (p.1, ptFun φ p.2)) := by
    funext p
    by_cases hp : p.2 ∈ φ.dom
    · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ Prod.snd ⁻¹' φ.dom from hp)]
    · rw [indicator_of_notMem hp, indicator_of_notMem (show p ∉ Prod.snd ⁻¹' φ.dom from hp)]
  refine ⟨?_, ?_⟩
  · rw [e1]
    exact ((hlm.comp (measurable_fst.prodMk (hφm.comp measurable_snd))).indicator
      (measurable_snd φ.measurableSet_dom)).aestronglyMeasurable
  · unfold HasFiniteIntegral
    simp only [enorm_indicator_eq_indicator_enorm]
    refine lt_of_le_of_lt (lintegral_transpose_le hR φ hc hφ (h := fun p => ‖l p‖ₑ)
      hlm.enorm) ?_
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (by exact_mod_cast hc)) hl.2

/-- Integrals over `count ⊗ M` on `Fin n × Y` are finite sums of slice integrals. -/
theorem integral_count_prod {Y : Type*} [MeasurableSpace Y] {M : Measure Y} [SFinite M] {n : ℕ}
    {F : Fin n × Y → ℝ} (hF : ∀ i, Measurable fun y => F (i, y))
    (hint : ∀ i, Integrable (fun y => F (i, y)) M) :
    Integrable F ((Measure.count : Measure (Fin n)).prod M) ∧
      ∫ z, F z ∂((Measure.count : Measure (Fin n)).prod M) = ∑ i, ∫ y, F (i, y) ∂M := by
  have hFm : Measurable F := measurable_from_prod_countable_right hF
  have hI : Integrable F ((Measure.count : Measure (Fin n)).prod M) := by
    rw [integrable_prod_iff hFm.aestronglyMeasurable]
    exact ⟨Eventually.of_forall hint, Integrable.of_finite⟩
  refine ⟨hI, ?_⟩
  rw [integral_prod F hI, integral_fintype Integrable.of_finite]
  simp

theorem bdd_add' {R : Set (X × X)} {f g : X × X → ℝ} (hf : Monod.IsBddMeasOn R f)
    (hg : Monod.IsBddMeasOn R g) : Monod.IsBddMeasOn R (f + g) := by
  obtain ⟨hfm, C1, hC1⟩ := hf
  obtain ⟨hgm, C2, hC2⟩ := hg
  exact ⟨hfm.add hgm, C1 + C2, fun p hp => (abs_add_le _ _).trans (add_le_add (hC1 p hp) (hC2 p hp))⟩

theorem bdd_smul' {R : Set (X × X)} (c : ℝ) {f : X × X → ℝ} (hf : Monod.IsBddMeasOn R f) :
    Monod.IsBddMeasOn R (c • f) := by
  obtain ⟨hfm, C, hC⟩ := hf
  refine ⟨hfm.const_smul c, |c| * C, fun p hp => ?_⟩
  rw [Pi.smul_apply, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC p hp) (abs_nonneg c)

/-- **Step 1 (Reiter / Day, CFW pp. 440–441).** By contradiction: Hahn–Banach separation in
`L¹(count ⊗ m⁻¹)` (`exists_separating_bounded`) gives bounded `gᵢ`; transposing along `φᵢ`
(`integral_transpose_eq`) yields a bounded `h = ∑ (Tᵢ gᵢ - αᵢ gᵢ)` with `∫ l h dm⁻¹ ≥ ε` for every
probability density `l`, hence `h ≥ ε/2` a.e.; but the invariant state of `exists_invariant_state`
kills `h`. -/
theorem exists_reiter {μ : Measure X} [IsProbabilityMeasure μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (hamen : Monod.IsAmenableRel μ R) {n : ℕ}
    (φ : Fin n → Monod.PartialTransformation R) {c : ℝ≥0} (hc : 0 < c)
    (hφ : ∀ i, ∀ᵐ a ∂μ, a ∈ (φ i).dom → (c : ℝ≥0∞) ≤ module μ R (a, ptFun (φ i) a) ∧
      module μ R (a, ptFun (φ i) a) ≤ (c : ℝ≥0∞)⁻¹)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ l : X × X → ℝ, Measurable l ∧ (∀ p, 0 ≤ l p) ∧ (∀ p, p ∉ R → l p = 0) ∧
      Integrable l ((relMeasure μ R).map Prod.swap) ∧
      ∫ p, l p ∂((relMeasure μ R).map Prod.swap) = 1 ∧
      ∑ i, ∫ p, (φ i).dom.indicator (fun x => |l (p.1, ptFun (φ i) x) - l (p.1, x)|) p.2
        ∂((relMeasure μ R).map Prod.swap) < ε := by
  classical
  set M := (relMeasure μ R).map Prod.swap with hMdef
  haveI : SigmaFinite (relMeasure μ R) := CFWPlan.Main.sigmaFinite_relMeasure hR
  haveI : SigmaFinite M := measurableEmbedding_swap'.sigmaFinite_map
  have hRe := hR.equivalence
  have hφm : ∀ i, Measurable (ptFun (φ i)) := fun i => (CFWPlan.Main.measurable_ptFun (φ i)).1
  have hinvm : ∀ i, Measurable (ptInv (φ i)) := fun i => (CFWPlan.Main.measurable_ptFun (φ i)).2
  have hδ : Measurable (module μ R) := Measure.measurable_rnDeriv _ _
  by_contra hcon
  push Not at hcon
  set Dens : Set (X × X → ℝ) := {l | Measurable l ∧ (∀ p, 0 ≤ l p) ∧ (∀ p, p ∉ R → l p = 0) ∧
    Integrable l M ∧ ∫ p, l p ∂M = 1} with hDensdef
  -- bounded versions `βᵢ` of `δ(φᵢ⁻¹ x, x)` on the codomains
  set Cb : ℝ := ((c : ℝ))⁻¹ with hCbdef
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  have hCb : 0 < Cb := inv_pos.2 (by exact_mod_cast hc)
  set β : Fin n → X → ℝ := fun i x => min (module μ R (ptInv (φ i) x, x)).toReal Cb with hβdef
  have hβm : ∀ i, Measurable (β i) := fun i =>
    ((hδ.comp ((hinvm i).prodMk measurable_id)).ennreal_toReal).min measurable_const
  have hβb : ∀ i x, |β i x| ≤ Cb := by
    intro i x
    rw [abs_of_nonneg (le_min ENNReal.toReal_nonneg hCb.le)]
    exact min_le_right _ _
  have hβae : ∀ i, ∀ᵐ x ∂μ, x ∈ (φ i).cod → module μ R (ptInv (φ i) x, x) < ∞ ∧
      β i x = (module μ R (ptInv (φ i) x, x)).toReal := by
    intro i
    filter_upwards [ae_cod_of_ae_dom hR (φ i) (hφ i)] with x hx hxc
    have hsp := ((CFWPlan.Main.ptFun_spec (φ i)).2.1 x hxc).2
    have h2 := (hx hxc).2
    rw [hsp] at h2
    refine ⟨lt_of_le_of_lt h2 (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hc0)), ?_⟩
    simp only [hβdef]
    refine min_eq_left ?_
    have := ENNReal.toReal_mono (ENNReal.inv_ne_top.2 hc0) h2
    rwa [ENNReal.toReal_inv, ENNReal.coe_toReal] at this
  -- the product space `Fin n × (X × X)` and the map `l ↦ (l·Tᵢ - l·αᵢ)ᵢ`
  set ν : Measure (Fin n × (X × X)) := (Measure.count : Measure (Fin n)).prod M with hνdef
  set cmap : (X × X → ℝ) → Fin n × (X × X) → ℝ := fun l z =>
    (φ z.1).dom.indicator (fun x => l (z.2.1, ptFun (φ z.1) x) - l (z.2.1, x)) z.2.2
    with hcmapdef
  have hslice : ∀ l i p, cmap l (i, p) = (φ i).dom.indicator (fun x => l (p.1, ptFun (φ i) x)) p.2 -
      (Prod.snd ⁻¹' (φ i).dom).indicator l p := by
    intro l i p
    by_cases hp : p.2 ∈ (φ i).dom
    · simp only [hcmapdef, indicator_of_mem hp,
        indicator_of_mem (show p ∈ Prod.snd ⁻¹' (φ i).dom from hp)]
    · simp only [hcmapdef, indicator_of_notMem hp,
        indicator_of_notMem (show p ∉ Prod.snd ⁻¹' (φ i).dom from hp), sub_zero]
  have hdomind : ∀ i (k : X × X → ℝ), Measurable k →
      Measurable fun p : X × X => (φ i).dom.indicator (fun x => k (p.1, ptFun (φ i) x)) p.2 := by
    intro i k hk
    have : (fun p : X × X => (φ i).dom.indicator (fun x => k (p.1, ptFun (φ i) x)) p.2) =
        (Prod.snd ⁻¹' (φ i).dom).indicator (fun p => k (p.1, ptFun (φ i) p.2)) := by
      funext p
      by_cases hp : p.2 ∈ (φ i).dom
      · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ Prod.snd ⁻¹' (φ i).dom from hp)]
      · rw [indicator_of_notMem hp, indicator_of_notMem (show p ∉ Prod.snd ⁻¹' (φ i).dom from hp)]
    rw [this]
    exact (hk.comp (measurable_fst.prodMk ((hφm i).comp measurable_snd))).indicator
      (measurable_snd (φ i).measurableSet_dom)
  have hslm : ∀ l, Measurable l → ∀ i, Measurable fun p => cmap l (i, p) := by
    intro l hl i
    simp only [hslice]
    exact (hdomind i l hl).sub (hl.indicator (measurable_snd (φ i).measurableSet_dom))
  have hslint : ∀ l ∈ Dens, ∀ i, Integrable (fun p => cmap l (i, p)) M := by
    rintro l ⟨hlm, hl0, hlR, hli, hl1⟩ i
    simp only [hslice]
    exact (integrable_transpose hR (φ i) hc (hφ i) hlm hli).sub
      (hli.indicator (measurable_snd (φ i).measurableSet_dom))
  have hDint : ∀ c ∈ cmap '' Dens, Integrable c ν := by
    rintro _ ⟨l, hl, rfl⟩
    exact (integral_count_prod (hslm l hl.1) (hslint l hl)).1
  have hfar : ∀ c ∈ cmap '' Dens, ε ≤ ∫ z, |c z| ∂ν := by
    rintro _ ⟨l, hl, rfl⟩
    obtain ⟨hlm, hl0, hlR, hli, hl1⟩ := hl
    have h := hcon l hlm hl0 hlR hli hl1
    have habs : ∀ i p, |cmap l (i, p)| =
        (φ i).dom.indicator (fun x => |l (p.1, ptFun (φ i) x) - l (p.1, x)|) p.2 := by
      intro i p
      by_cases hp : p.2 ∈ (φ i).dom
      · simp only [hcmapdef, indicator_of_mem hp]
      · simp only [hcmapdef, indicator_of_notMem hp, abs_zero]
    rw [(integral_count_prod (F := fun z => |cmap l z|) (fun i => (hslm l hlm i).abs)
      (fun i => (hslint l ⟨hlm, hl0, hlR, hli, hl1⟩ i).abs)).2]
    simp only [habs]
    exact h
  have hDconv : Convex ℝ (cmap '' Dens) := by
    rintro _ ⟨l₁, hl₁, rfl⟩ _ ⟨l₂, hl₂, rfl⟩ a b ha hb hab
    obtain ⟨m1, p1, z1, i1, n1⟩ := hl₁
    obtain ⟨m2, p2, z2, i2, n2⟩ := hl₂
    refine ⟨a • l₁ + b • l₂, ⟨(m1.const_smul a).add (m2.const_smul b), fun p => ?_, fun p hp => ?_,
      (i1.smul a).add (i2.smul b), ?_⟩, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact add_nonneg (mul_nonneg ha (p1 p)) (mul_nonneg hb (p2 p))
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, z1 p hp, z2 p hp, mul_zero, add_zero]
    · simp only [Pi.add_apply, Pi.smul_apply]
      rw [integral_add (f := fun p => a • l₁ p) (g := fun p => b • l₂ p) (i1.smul a) (i2.smul b),
        integral_smul, integral_smul, n1, n2, smul_eq_mul, smul_eq_mul, mul_one, mul_one, hab]
    · funext z
      simp only [hcmapdef, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hz : z.2.2 ∈ (φ z.1).dom
      · simp only [indicator_of_mem hz]
        ring
      · simp only [indicator_of_notMem hz]
        ring
  -- Hahn–Banach
  obtain ⟨g, hgm, hg1, hsep⟩ :=
    CFWPlan.Main.exists_separating_bounded ν (cmap '' Dens) hDconv hDint hε hfar
  have hgi : ∀ i, Measurable fun p : X × X => g (i, p) := fun i => hgm.comp measurable_prodMk_left
  set Tg : Fin n → X × X → ℝ := fun i p =>
    if p.2 ∈ (φ i).cod then β i p.2 * g (i, (p.1, ptInv (φ i) p.2)) else 0 with hTgdef
  set Ag : Fin n → X × X → ℝ := fun i p => (φ i).dom.indicator 1 p.2 * g (i, p) with hAgdef
  set h : X × X → ℝ := fun p => ∑ i, (Tg i p - Ag i p) with hhdef
  have hTgm : ∀ i, Measurable (Tg i) := by
    intro i
    refine Measurable.ite (measurable_snd (φ i).measurableSet_cod) ?_ measurable_const
    exact ((hβm i).comp measurable_snd).mul
      ((hgi i).comp (measurable_fst.prodMk ((hinvm i).comp measurable_snd)))
  have hAgm : ∀ i, Measurable (Ag i) := fun i =>
    ((measurable_one.indicator (φ i).measurableSet_dom).comp measurable_snd).mul (hgi i)
  have hTgb : ∀ i p, |Tg i p| ≤ Cb := by
    intro i p
    simp only [hTgdef]
    split_ifs
    · rw [abs_mul]
      exact (mul_le_mul (hβb i _) (hg1 _) (abs_nonneg _) hCb.le).trans_eq (mul_one _)
    · rw [abs_zero]
      exact hCb.le
  have hAgb : ∀ i p, |Ag i p| ≤ 1 := by
    intro i p
    simp only [hAgdef]
    by_cases hp : p.2 ∈ (φ i).dom
    · rw [indicator_of_mem hp, Pi.one_apply, one_mul]
      exact hg1 _
    · rw [indicator_of_notMem hp, zero_mul, abs_zero]
      exact zero_le_one
  have hhm : Measurable h := Finset.measurable_sum _ fun i _ => (hTgm i).sub (hAgm i)
  have hhb : ∀ p, |h p| ≤ n * (Cb + 1) := by
    intro p
    calc |h p| ≤ ∑ i, |Tg i p - Ag i p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, (Cb + 1) := Finset.sum_le_sum fun i _ =>
          (abs_sub _ _).trans (add_le_add (hTgb i p) (hAgb i p))
      _ = n * (Cb + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the key identity `∫ c_l g dν = ∫ l h dm⁻¹`
  have hkey : ∀ l ∈ Dens, ∫ z, cmap l z * g z ∂ν = ∫ p, l p * h p ∂M := by
    intro l hl
    obtain ⟨hlm, hl0, hlR, hli, hl1⟩ := hl
    have hsl : ∀ i, Integrable (fun p => cmap l (i, p) * g (i, p)) M := fun i =>
      (hslint l ⟨hlm, hl0, hlR, hli, hl1⟩ i).abs.mono' ((hslm l hlm i).mul (hgi i)).aestronglyMeasurable
        (Eventually.of_forall fun p => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hg1 _))
    rw [(integral_count_prod (F := fun z => cmap l z * g z) (fun i => (hslm l hlm i).mul (hgi i))
      hsl).2]
    have hTl : ∀ i, Integrable (fun p => l p * Tg i p) M := fun i =>
      (hli.abs.const_mul Cb).mono' (hlm.mul (hTgm i)).aestronglyMeasurable
        (Eventually.of_forall fun p => by
          rw [Real.norm_eq_abs, abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hTgb i p) (abs_nonneg _))
    have hAl : ∀ i, Integrable (fun p => l p * Ag i p) M := fun i =>
      hli.abs.mono' (hlm.mul (hAgm i)).aestronglyMeasurable
        (Eventually.of_forall fun p => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hAgb i p))
    have hslice_eq : ∀ i, ∫ p, cmap l (i, p) * g (i, p) ∂M =
        ∫ p, l p * Tg i p ∂M - ∫ p, l p * Ag i p ∂M := by
      intro i
      have hsp := CFWPlan.Main.ptFun_spec (φ i)
      have hpt : ∀ p, cmap l (i, p) * g (i, p) = (φ i).dom.indicator
          (fun x => l (p.1, ptFun (φ i) x) * g (i, (p.1, x))) p.2 - l p * Ag i p := by
        intro p
        by_cases hp : p.2 ∈ (φ i).dom
        · simp only [hcmapdef, hAgdef, indicator_of_mem hp, Pi.one_apply, one_mul]
          ring
        · simp only [hcmapdef, hAgdef, indicator_of_notMem hp, zero_mul, mul_zero, sub_zero]
      have hint1 : Integrable (fun p => (φ i).dom.indicator
          (fun x => l (p.1, ptFun (φ i) x) * g (i, (p.1, x))) p.2) M := by
        refine (integrable_transpose hR (φ i) hc (hφ i) hlm hli).abs.mono' ?_ ?_
        · have e : (fun p : X × X => (φ i).dom.indicator
              (fun x => l (p.1, ptFun (φ i) x) * g (i, (p.1, x))) p.2) =
              (Prod.snd ⁻¹' (φ i).dom).indicator (fun p => l (p.1, ptFun (φ i) p.2) * g (i, p)) := by
            funext p
            by_cases hp : p.2 ∈ (φ i).dom
            · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ Prod.snd ⁻¹' (φ i).dom from hp)]
            · rw [indicator_of_notMem hp,
                indicator_of_notMem (show p ∉ Prod.snd ⁻¹' (φ i).dom from hp)]
          rw [e]
          exact (((hlm.comp (measurable_fst.prodMk ((hφm i).comp measurable_snd))).mul
            (hgi i)).indicator (measurable_snd (φ i).measurableSet_dom)).aestronglyMeasurable
        · refine Eventually.of_forall fun p => ?_
          by_cases hp : p.2 ∈ (φ i).dom
          · rw [indicator_of_mem hp, indicator_of_mem hp, Real.norm_eq_abs, abs_mul]
            exact mul_le_of_le_one_right (abs_nonneg _) (hg1 _)
          · rw [indicator_of_notMem hp, indicator_of_notMem hp, norm_zero, abs_zero]
      simp only [hpt]
      rw [integral_sub hint1 (hAl i)]
      congr 1
      have htr := integral_transpose_eq hR (φ i)
        (F := fun q => l q * g (i, (q.1, ptInv (φ i) q.2)))
        (hlm.mul ((hgi i).comp (measurable_fst.prodMk ((hinvm i).comp measurable_snd))))
        (hβae i)
      calc ∫ p, (φ i).dom.indicator (fun x => l (p.1, ptFun (φ i) x) * g (i, (p.1, x))) p.2 ∂M
          = ∫ p, (φ i).dom.indicator (fun x => (fun q => l q * g (i, (q.1, ptInv (φ i) q.2)))
              (p.1, ptFun (φ i) x)) p.2 ∂M := by
            congr 1
            funext p
            by_cases hp : p.2 ∈ (φ i).dom
            · simp only [indicator_of_mem hp, (hsp.1 _ hp).2.1]
            · simp only [indicator_of_notMem hp]
        _ = ∫ p, (φ i).cod.indicator (fun x => β i x * (fun q => l q * g (i, (q.1, ptInv (φ i) q.2)))
              (p.1, x)) p.2 ∂M := htr
        _ = ∫ p, l p * Tg i p ∂M := by
            congr 1
            funext p
            by_cases hp : p.2 ∈ (φ i).cod
            · simp only [indicator_of_mem hp, hTgdef, if_pos hp]
              ring
            · simp only [indicator_of_notMem hp, hTgdef, if_neg hp, mul_zero]
    simp only [hslice_eq]
    have hpt2 : ∀ p, l p * h p = ∑ i, (l p * Tg i p - l p * Ag i p) := by
      intro p
      simp only [hhdef, Finset.mul_sum, mul_sub]
    simp only [hpt2]
    rw [integral_finsetSum (f := fun i p => l p * Tg i p - l p * Ag i p) _
      fun i _ => (hTl i).sub (hAl i)]
    exact Finset.sum_congr rfl fun i _ => (integral_sub (hTl i) (hAl i)).symm
  have hstep : ∀ l ∈ Dens, ε ≤ ∫ p, l p * h p ∂M := fun l hl =>
    (hsep (cmap l) ⟨l, hl, rfl⟩).trans_eq (hkey l hl)
  -- hence `h ≥ ε / 2` almost everywhere on `R`
  have hhε : ∀ᵐ p ∂(relMeasure μ R), ε / 2 ≤ h p := by
    set E : Set (X × X) := {p | p ∈ R ∧ h p < ε / 2} with hEdef
    have hEm : MeasurableSet E := hR.measurableSet.inter (measurableSet_lt hhm measurable_const)
    have hE0 : M E = 0 := by
      by_contra hpos
      obtain ⟨E', hE'm, hE'E, hE'pos, hE'fin⟩ :=
        Measure.exists_subset_measure_lt_top hEm (pos_iff_ne_zero.2 hpos)
      set t : ℝ := (M E').toReal with htdef
      have ht : 0 < t := ENNReal.toReal_pos hE'pos.ne' hE'fin.ne
      set l : X × X → ℝ := E'.indicator (fun _ => t⁻¹) with hldef
      have hlm : Measurable l := measurable_const.indicator hE'm
      have hl0 : ∀ p, 0 ≤ l p := fun p => indicator_nonneg (fun _ _ => (inv_pos.2 ht).le) p
      have hlR : ∀ p, p ∉ R → l p = 0 := fun p hp =>
        indicator_of_notMem (fun h' => hp (hE'E h').1) _
      have hli : Integrable l M := (integrableOn_const hE'fin.ne).integrable_indicator hE'm
      have hl1 : ∫ p, l p ∂M = 1 := by
        rw [hldef, integral_indicator hE'm, setIntegral_const, smul_eq_mul, measureReal_def,
          ← htdef, mul_inv_cancel₀ ht.ne']
      have h1 := hstep l ⟨hlm, hl0, hlR, hli, hl1⟩
      have h2 : ∫ p, l p * h p ∂M = t⁻¹ * ∫ p in E', h p ∂M := by
        rw [← integral_const_mul, ← integral_indicator hE'm]
        congr 1
        funext p
        by_cases hp : p ∈ E'
        · simp only [hldef, indicator_of_mem hp]
        · simp only [hldef, indicator_of_notMem hp, zero_mul, mul_zero]
      have h3 : ∫ p in E', h p ∂M ≤ ∫ p in E', ε / 2 ∂M := by
        haveI : IsFiniteMeasure (M.restrict E') := isFiniteMeasure_restrict.2 hE'fin.ne
        refine setIntegral_mono_on ?_ ?_ hE'm fun p hp => (hE'E hp).2.le
        · exact (integrable_const ((n : ℝ) * (Cb + 1))).mono' hhm.aestronglyMeasurable
            (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hhb p)
        · exact integrable_const _
      rw [setIntegral_const, smul_eq_mul, measureReal_def, ← htdef] at h3
      have h4 : ∫ p, l p * h p ∂M ≤ ε / 2 := by
        rw [h2]
        calc t⁻¹ * ∫ p in E', h p ∂M ≤ t⁻¹ * (t * (ε / 2)) :=
              mul_le_mul_of_nonneg_left h3 (inv_pos.2 ht).le
          _ = ε / 2 := by field_simp
      linarith
    have hae1 : ∀ᵐ p ∂M, p ∉ E := measure_eq_zero_iff_ae_notMem.1 hE0
    have hac := (CFWPlan.Main.relMeasure_ac_swap hR).1
    have hae2 : ∀ᵐ p ∂(relMeasure μ R), p ∉ E := hac.ae_le hae1
    have hae3 : ∀ᵐ p ∂(relMeasure μ R), p ∉ Rᶜ := measure_eq_zero_iff_ae_notMem.1
      (CFWPlan.Main.relMeasure_compl hR.measurableSet hR.countable_classes)
    filter_upwards [hae2, hae3] with p hp1 hp2
    have hpR : p ∈ R := by simpa using hp2
    by_contra hlt
    exact hp1 ⟨hpR, not_le.1 hlt⟩
  -- the invariant state kills `h`
  obtain ⟨L, hLadd, hLsmul, hLpos, hL1, hLinv⟩ := CFWPlan.Main.exists_invariant_state hR hamen
  have hbddT : ∀ i, Monod.IsBddMeasOn R (Tg i) := fun i => ⟨hTgm i, Cb, fun p _ => hTgb i p⟩
  have hbddA : ∀ i, Monod.IsBddMeasOn R (Ag i) := fun i => ⟨hAgm i, 1, fun p _ => hAgb i p⟩
  have hbdd1 : Monod.IsBddMeasOn R (1 : X × X → ℝ) := ⟨measurable_const, 1, fun p _ => by simp⟩
  have hinvi : ∀ i, L (Tg i) = L (Ag i) := fun i =>
    hLinv (φ i) (β i) (hβm i) ⟨Cb, hβb i⟩ ((hβae i).mono fun x hx hxc => (hx hxc).2)
      (fun p => g (i, p)) ⟨hgi i, 1, fun p _ => hg1 _⟩
  set u : Fin n → X × X → ℝ := fun i => Tg i + (-1 : ℝ) • Ag i with hudef
  have hbddu : ∀ i, Monod.IsBddMeasOn R (u i) := fun i => bdd_add' (hbddT i) (bdd_smul' _ (hbddA i))
  have hLu : ∀ i, L (u i) = 0 := by
    intro i
    rw [hudef]
    simp only
    rw [hLadd _ _ (hbddT i) (bdd_smul' _ (hbddA i)), hLsmul _ _ (hbddA i), hinvi i]
    ring
  have hL0 : L 0 = 0 := by
    have := hLsmul 0 1 hbdd1
    rw [zero_smul, zero_mul] at this
    exact this
  have hLsum : ∀ s : Finset (Fin n), Monod.IsBddMeasOn R (∑ i ∈ s, u i) ∧ L (∑ i ∈ s, u i) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty]
      exact ⟨⟨measurable_const, 0, fun p _ => by simp⟩, hL0⟩
    | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      exact ⟨bdd_add' (hbddu j) ih.1, by rw [hLadd _ _ (hbddu j) ih.1, hLu j, ih.2, add_zero]⟩
  have hhu : h = ∑ i, u i := by
    funext p
    simp only [hhdef, hudef, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hbddh : Monod.IsBddMeasOn R h := hhu ▸ (hLsum Finset.univ).1
  have hLh : L h = 0 := hhu ▸ (hLsum Finset.univ).2
  have hpos := hLpos (h + (-(ε / 2)) • 1) (bdd_add' hbddh (bdd_smul' _ hbdd1)) (by
    filter_upwards [hhε] with p hp
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
    linarith)
  rw [hLadd _ _ hbddh (bdd_smul' _ hbdd1), hLsmul _ _ hbdd1, hL1, hLh] at hpos
  linarith

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
/-- **Step 2 (CFW p. 441).** Truncate the Reiter density to the bounded sets
`K_N ∪ Δ` (`exists_isBoundedSubset_mono_cover`, the error is controlled by `lintegral_diff_le`), then
pick a level set by Namioka's layer-cake argument (`exists_level_set`). -/
theorem exists_folner_set {μ : Measure X} [IsProbabilityMeasure μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (hamen : Monod.IsAmenableRel μ R) {n : ℕ}
    (φ : Fin n → Monod.PartialTransformation R) {c : ℝ≥0} (hc : 0 < c)
    (hφ : ∀ i, ∀ᵐ a ∂μ, a ∈ (φ i).dom → (c : ℝ≥0∞) ≤ module μ R (a, ptFun (φ i) a) ∧
      module μ R (a, ptFun (φ i) a) ≤ (c : ℝ≥0∞)⁻¹)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K' L : Set (X × X), IsBoundedSubset μ R K' ∧ {p : X × X | p.1 = p.2} ⊆ K' ∧
      MeasurableSet L ∧ L ⊆ K' ∧ 0 < (relMeasure μ R).map Prod.swap L ∧
      (relMeasure μ R).map Prod.swap L < ∞ ∧
      ∑ i, (relMeasure μ R).map Prod.swap
          {p | p.2 ∈ (φ i).dom ∧ ((p.1, ptFun (φ i) p.2) ∈ L ↔ p ∉ L)} <
        ENNReal.ofReal ε * (relMeasure μ R).map Prod.swap L := by
  set M := (relMeasure μ R).map Prod.swap with hMdef
  haveI : SigmaFinite (relMeasure μ R) := CFWPlan.Main.sigmaFinite_relMeasure hR
  haveI : SigmaFinite M := measurableEmbedding_swap'.sigmaFinite_map
  have hφm : ∀ i, Measurable (ptFun (φ i)) := fun i => (CFWPlan.Main.measurable_ptFun (φ i)).1
  obtain ⟨l, hlm, hl0, hlR, hlint, hl1, hlε⟩ := exists_reiter hR hamen φ hc hφ hε
  set C : ℝ≥0∞ := (c : ℝ≥0∞)⁻¹ + 1 with hCdef
  have hCtop : C ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.inv_ne_top.2 (by exact_mod_cast hc.ne'), ENNReal.one_ne_top⟩
  have hlL : ∫⁻ p, ENNReal.ofReal (l p) ∂M = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hlint (Eventually.of_forall hl0), hl1,
      ENNReal.ofReal_one]
  set Dl : Fin n → X × X → ℝ := fun i p =>
    (φ i).dom.indicator (fun x => |l (p.1, ptFun (φ i) x) - l (p.1, x)|) p.2 with hDldef
  have hDl0 : ∀ i p, 0 ≤ Dl i p := fun i p => indicator_nonneg (fun _ _ => abs_nonneg _) _
  -- (1) the almost invariance of `l` in lower-integral form
  have hA : ∑ i, ∫⁻ p, ENNReal.ofReal (Dl i p) ∂M < ENNReal.ofReal ε := by
    have hint : ∀ i, Integrable (Dl i) M := by
      intro i
      have hmeas : Measurable (Dl i) := by
        have : (Dl i) = (Prod.snd ⁻¹' (φ i).dom).indicator
            (fun p => |l (p.1, ptFun (φ i) p.2) - l p|) := by
          funext p
          by_cases hp : p.2 ∈ (φ i).dom
          · simp only [hDldef]
            rw [indicator_of_mem hp, indicator_of_mem (show p ∈ Prod.snd ⁻¹' (φ i).dom from hp)]
          · simp only [hDldef]
            rw [indicator_of_notMem hp,
              indicator_of_notMem (show p ∉ Prod.snd ⁻¹' (φ i).dom from hp)]
        rw [this]
        exact (((hlm.comp (measurable_fst.prodMk ((hφm i).comp measurable_snd))).sub hlm).abs).indicator
          (measurable_snd (φ i).measurableSet_dom)
      refine ⟨hmeas.aestronglyMeasurable, ?_⟩
      unfold HasFiniteIntegral
      have he : ∀ p, ‖Dl i p‖ₑ = ENNReal.ofReal (Dl i p) := fun p =>
        (Real.enorm_eq_ofReal_abs _).trans (by rw [abs_of_nonneg (hDl0 i p)])
      simp only [he]
      have h := lintegral_diff_le hR (φ i) hc (hφ i) hlm (measurable_const (a := (0 : ℝ)))
      simp only [sub_self, abs_zero, indicator_zero', Pi.zero_apply, ENNReal.ofReal_zero,
        lintegral_zero, zero_add, sub_zero] at h
      refine lt_of_le_of_lt h ?_
      have : ∫⁻ p, ENNReal.ofReal |l p| ∂M = 1 := by
        simp only [abs_of_nonneg (hl0 _)]
        exact hlL
      rw [this]
      have h0 : ∀ p : X × X, (φ i).dom.indicator (fun _ : X => (0 : ℝ)) p.2 = 0 := fun p =>
        indicator_apply_eq_zero.2 fun _ => rfl
      simp only [h0, ENNReal.ofReal_zero, lintegral_zero, zero_add, mul_one]
      exact lt_top_iff_ne_top.2 hCtop
    have e1 : ∀ i, ∫⁻ p, ENNReal.ofReal (Dl i p) ∂M = ENNReal.ofReal (∫ p, Dl i p ∂M) := fun i =>
      (ofReal_integral_eq_lintegral_ofReal (hint i) (Eventually.of_forall (hDl0 i))).symm
    simp only [e1]
    rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => integral_nonneg (hDl0 i)]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).2 hlε
  -- (2) the truncations
  obtain ⟨Kn, hKmono, hKb, hRK⟩ := CFWPlan.Main.exists_isBoundedSubset_mono_cover hR
  set K' : ℕ → Set (X × X) := fun N => Kn N ∪ {p : X × X | p.1 = p.2} with hK'def
  have hK'm : ∀ N, MeasurableSet (K' N) := fun N =>
    (hKb N).measurableSet.union (measurableSet_diagonal (α := X))
  set lN : ℕ → X × X → ℝ := fun N => (K' N).indicator l with hlNdef
  set rN : ℕ → X × X → ℝ := fun N => (K' N)ᶜ.indicator l with hrNdef
  have hlNm : ∀ N, Measurable (lN N) := fun N => hlm.indicator (hK'm N)
  have hrNm : ∀ N, Measurable (rN N) := fun N => hlm.indicator (hK'm N).compl
  have hlN0 : ∀ N p, 0 ≤ lN N p := fun N p => indicator_nonneg (fun p _ => hl0 p) p
  have hrN0 : ∀ N p, 0 ≤ rN N p := fun N p => indicator_nonneg (fun p _ => hl0 p) p
  have hsplit : ∀ N p, ENNReal.ofReal (l p) = ENNReal.ofReal (lN N p) + ENNReal.ofReal (rN N p) := by
    intro N p
    rw [← ENNReal.ofReal_add (hlN0 N p) (hrN0 N p)]
    congr 1
    have := congrFun (indicator_self_add_compl (K' N) l) p
    simp only [Pi.add_apply] at this
    exact this.symm
  have habs : ∀ N p, |lN N p - l p| = rN N p := by
    intro N p
    by_cases hp : p ∈ K' N
    · simp only [hlNdef, hrNdef, indicator_of_mem hp, sub_self, abs_zero,
        indicator_of_notMem (show p ∉ (K' N)ᶜ from fun h => h hp)]
    · simp only [hlNdef, hrNdef, indicator_of_notMem hp, zero_sub, abs_neg,
        indicator_of_mem (show p ∈ (K' N)ᶜ from hp), abs_of_nonneg (hl0 p)]
  set ρ : ℕ → ℝ≥0∞ := fun N => ∫⁻ p, ENNReal.ofReal (rN N p) ∂M with hρdef
  set sN : ℕ → ℝ≥0∞ := fun N => ∫⁻ p, ENNReal.ofReal (lN N p) ∂M with hsNdef
  have hsρ : ∀ N, sN N + ρ N = 1 := by
    intro N
    rw [← hlL, hsNdef, hρdef]
    simp only
    rw [← lintegral_add_left (f := fun p => ENNReal.ofReal (lN N p))
      (ENNReal.measurable_ofReal.comp (hlNm N))]
    exact lintegral_congr fun p => (hsplit N p).symm
  have hρtop : ∀ N, ρ N ≠ ∞ := fun N =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_of_le_of_eq le_add_self (hsρ N))
  have hsN : ∀ N, sN N = 1 - ρ N := fun N => ENNReal.eq_sub_of_add_eq (hρtop N) (hsρ N)
  have hDN : ∀ N, ∑ i, ∫⁻ p, ENNReal.ofReal ((φ i).dom.indicator
      (fun x => |lN N (p.1, ptFun (φ i) x) - lN N (p.1, x)|) p.2) ∂M ≤
      ∑ i, ∫⁻ p, ENNReal.ofReal (Dl i p) ∂M + (n * C) * ρ N := by
    intro N
    calc _ ≤ ∑ i, (∫⁻ p, ENNReal.ofReal (Dl i p) ∂M + C * ρ N) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h := lintegral_diff_le hR (φ i) hc (hφ i) (hlNm N) hlm
          simp only [habs] at h
          exact h
      _ = ∑ i, ∫⁻ p, ENNReal.ofReal (Dl i p) ∂M + (n * C) * ρ N := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, mul_assoc]
  -- (3) `ρ N → 0`
  have hρlim : Tendsto ρ atTop (𝓝 0) := by
    have h := tendsto_lintegral_of_dominated_convergence (μ := M)
      (F := fun N p => ENNReal.ofReal (rN N p)) (f := fun _ => 0) (fun p => ENNReal.ofReal (l p))
      (fun N => ENNReal.measurable_ofReal.comp (hrNm N))
      (fun N => Eventually.of_forall fun p => by
        simp only
        rw [hsplit N p]
        exact le_add_self)
      (by rw [hlL]; exact ENNReal.one_ne_top)
      (Eventually.of_forall fun p => by
        refine tendsto_const_nhds.congr' ?_
        by_cases hp : p ∈ R
        · rw [hRK, mem_iUnion] at hp
          obtain ⟨N₀, hN₀⟩ := hp
          filter_upwards [eventually_ge_atTop N₀] with N hN
          have : p ∈ K' N := Or.inl (hKmono hN hN₀)
          simp only [hrNdef, indicator_of_notMem (show p ∉ (K' N)ᶜ from fun h => h this),
            ENNReal.ofReal_zero]
        · refine Eventually.of_forall fun N => ?_
          simp only [hrNdef]
          by_cases hpK : p ∈ (K' N)ᶜ
          · rw [indicator_of_mem hpK, hlR p hp, ENNReal.ofReal_zero]
          · rw [indicator_of_notMem hpK, ENNReal.ofReal_zero])
    simpa only [lintegral_zero] using h
  -- (4) choose `N`
  set A := ∑ i, ∫⁻ p, ENNReal.ofReal (Dl i p) ∂M with hAdef
  have hf : Tendsto (fun N => A + (n * C) * ρ N) atTop (𝓝 A) := by
    have := (ENNReal.Tendsto.const_mul hρlim (Or.inr (ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top n) hCtop))).const_add A
    simpa only [mul_zero, add_zero] using this
  have hg : Tendsto (fun N => ENNReal.ofReal ε * (1 - ρ N)) atTop (𝓝 (ENNReal.ofReal ε)) := by
    have h1 : Tendsto (fun N => 1 - ρ N) atTop (𝓝 (1 - 0)) :=
      ENNReal.Tendsto.sub tendsto_const_nhds hρlim (Or.inl ENNReal.one_ne_top)
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ε) h1 (Or.inr ENNReal.ofReal_ne_top)
    simpa only [tsub_zero, mul_one] using this
  obtain ⟨N, hN⟩ := (hf.eventually_lt hg hA).exists
  -- (5) the inequality for `lN N`
  have hineqN : ∑ i, ∫⁻ p, ENNReal.ofReal ((φ i).dom.indicator
      (fun x => |lN N (p.1, ptFun (φ i) x) - lN N (p.1, x)|) p.2) ∂M <
      ENNReal.ofReal ε * ∫⁻ p, ENNReal.ofReal (lN N p) ∂M := by
    have : ∫⁻ p, ENNReal.ofReal (lN N p) ∂M = 1 - ρ N := hsN N
    rw [this]
    exact lt_of_le_of_lt (hDN N) hN
  -- (6) a level set
  obtain ⟨a, ha, hlev⟩ := exists_level_set (M := M) (fun i => ptFun (φ i)) hφm
    (fun i => (φ i).dom) (fun i => (φ i).measurableSet_dom) (hlNm N) (hlN0 N) _ hineqN
  set L : Set (X × X) := {q | a ≤ lN N q} with hLdef
  have hLm : MeasurableSet L := measurableSet_le measurable_const (hlNm N)
  have hLK : L ⊆ K' N := by
    intro q hq
    by_contra hqK
    have : lN N q = 0 := indicator_of_notMem hqK _
    rw [hLdef, mem_ofPred_eq, this] at hq
    exact absurd hq (not_le.2 ha)
  refine ⟨K' N, L, CFWPlan.Main.IsBoundedSubset.union (hKb N)
    (CFWPlan.Main.isBoundedSubset_diagonal hR), subset_union_right, hLm, hLK, ?_, ?_, hlev⟩
  · rw [pos_iff_ne_zero]
    intro h0
    rw [h0, mul_zero] at hlev
    exact absurd hlev (not_lt_zero)
  · have hmk := mul_meas_ge_le_lintegral₀ (μ := M)
      (ENNReal.measurable_ofReal.comp (hlNm N)).aemeasurable (ENNReal.ofReal a)
    have hset : {x | ENNReal.ofReal a ≤ ENNReal.ofReal (lN N x)} = L := by
      ext x
      simp only [hLdef, mem_ofPred_eq]
      exact ENNReal.ofReal_le_ofReal_iff (hlN0 N x)
    simp only [Function.comp_apply] at hmk
    rw [hset] at hmk
    have h1 : ENNReal.ofReal a * M L ≤ 1 :=
      hmk.trans (le_of_le_of_eq le_self_add (hsρ N))
    rw [lt_top_iff_ne_top]
    intro htop
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 ha).ne'] at h1
    exact absurd h1 (by simp)

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
/-- **Step 4b (CFW p. 442).** The boundary estimate, by **Lemma 2**
(`measure_eq_lintegral_fibreMeasure'`) applied to the f.s.r. `rowRel Ω K₁`, after moving the
row inequality from the base point `y` to `Quot.out F` with `fibreRatio_congr`. -/
theorem boundary_le_of_rows {μ : Measure X} [IsProbabilityMeasure μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) {n : ℕ} (φ : Fin n → Monod.PartialTransformation R)
    {K L K₁ : Set (X × X)} (hKφ : K = ⋃ i, CFWPlan.Route.ptGraph (φ i)) (hL : MeasurableSet L)
    (hK₁ : MeasurableSet K₁) (hK₁R : K₁ ⊆ R) (hLK₁ : L ⊆ K₁) (hdiag : ∀ x, (x, x) ∈ K₁)
    (hK₁fin : ∀ y, {x | (y, x) ∈ K₁}.Finite)
    (hK₁φ : ∀ i y x, x ∈ (φ i).dom → (y, ptFun (φ i) x) ∈ L → (y, x) ∈ K₁)
    {Ω : Set X} (hΩ : MeasurableSet Ω)
    (hdisj : ∀ y ∈ Ω, ∀ y' ∈ Ω, y ≠ y' → Disjoint {x | (y, x) ∈ K₁} {x | (y', x) ∈ K₁})
    {ε : ℝ} (hε : 0 < ε)
    (hrows : ∀ y ∈ Ω,
      ∑ i, ∑' x : {x : X // x ∈ (φ i).dom ∧ ((y, ptFun (φ i) x) ∈ L ↔ (y, x) ∉ L)},
          (module μ R (y, x))⁻¹ <
        ENNReal.ofReal ε * ∑' x : {x : X // (y, x) ∈ L}, (module μ R (y, x))⁻¹) :
    relMeasure μ R {γ ∈ K | (γ.2 ∈ unitSpace (rowRel Ω L) ∨ γ.1 ∈ unitSpace (rowRel Ω L)) ∧
        γ ∉ rowRel Ω L} ≤ ENNReal.ofReal ε * μ (unitSpace (rowRel Ω L)) := by
  have hRe := hR.equivalence
  have huniq : ∀ y ∈ Ω, ∀ y' ∈ Ω, ∀ x, (y, x) ∈ K₁ → (y', x) ∈ K₁ → y = y' := by
    intro y hy y' hy' x hx hx'
    by_contra hne
    exact Set.disjoint_left.1 (hdisj y hy y' hy' hne) hx hx'
  have hdisjL : ∀ y ∈ Ω, ∀ y' ∈ Ω, y ≠ y' → Disjoint {x | (y, x) ∈ L} {x | (y', x) ∈ L} :=
    fun y hy y' hy' hne => (hdisj y hy y' hy' hne).mono (fun x hx => hLK₁ hx) (fun x hx => hLK₁ hx)
  obtain ⟨hT, hTU⟩ := isFiniteSubrelation_rowRel hRe hL (hLK₁.trans hK₁R) hΩ
    (fun y => (hK₁fin y).subset fun x hx => hLK₁ hx) hdisjL
  obtain ⟨hT', hT'U⟩ := isFiniteSubrelation_rowRel hRe hK₁ hK₁R hΩ hK₁fin hdisj
  set T := rowRel Ω L with hTdef
  set T' := rowRel Ω K₁ with hT'def
  set U := unitSpace T with hUdef
  have hUm : MeasurableSet U := (measurable_id.prodMk measurable_id) hT.measurableSet
  have hφm : ∀ i, Measurable (ptFun (φ i)) := fun i => (CFWPlan.Main.measurable_ptFun (φ i)).1
  set B : Fin n → Set X := fun i =>
    {a | a ∈ (φ i).dom ∧ (a ∈ U ∨ ptFun (φ i) a ∈ U) ∧ (a, ptFun (φ i) a) ∉ T} with hBdef
  have hBm : ∀ i, MeasurableSet (B i) := by
    intro i
    refine (φ i).measurableSet_dom.inter ((hUm.union ((hφm i) hUm)).inter ?_)
    exact ((measurable_id.prodMk (hφm i)) hT.measurableSet).compl
  -- Step 1: the boundary lies in the union of the graphs over the `B i`
  have step1 : relMeasure μ R {γ ∈ K | (γ.2 ∈ U ∨ γ.1 ∈ U) ∧ γ ∉ T} ≤ ∑ i, μ (B i) := by
    calc relMeasure μ R {γ ∈ K | (γ.2 ∈ U ∨ γ.1 ∈ U) ∧ γ ∉ T}
        ≤ relMeasure μ R (⋃ i, Prod.fst ⁻¹' B i ∩ CFWPlan.Route.ptGraph (φ i)) := by
          refine measure_mono ?_
          rintro γ ⟨hγK, hγU, hγT⟩
          rw [hKφ, mem_iUnion] at hγK
          obtain ⟨i, hi⟩ := hγK
          obtain ⟨h1, h2⟩ := (mem_ptGraph_iff (φ i)).1 hi
          refine mem_iUnion.2 ⟨i, ⟨⟨h1, ?_, ?_⟩, hi⟩⟩
          · rw [h2]
            exact hγU.symm
          · rw [h2]
            exact hγT
      _ ≤ ∑ i, relMeasure μ R (Prod.fst ⁻¹' B i ∩ CFWPlan.Route.ptGraph (φ i)) :=
          measure_iUnion_fintype_le _ _
      _ ≤ ∑ i, μ (B i) :=
          Finset.sum_le_sum fun i _ => relMeasure_ptGraph_inter_le hR (φ i) (hBm i)
  -- Step 2: the fibres of `T'`
  have hT'mem : ∀ y ∈ Ω, ∀ x, (y, x) ∈ T' ↔ (y, x) ∈ K₁ := by
    intro y hy x
    constructor
    · rintro ⟨y'', hy'', h1, h2⟩
      have := huniq y'' hy'' y hy y h1 (hdiag y)
      subst this
      exact h2
    · intro h
      exact ⟨y, hy, hdiag y, h⟩
  have hUiff : ∀ y ∈ Ω, ∀ x, (y, x) ∈ K₁ → (x ∈ U ↔ (y, x) ∈ L) := by
    intro y hy x hK
    rw [hTU]
    constructor
    · rintro ⟨y', hy', h⟩
      have := huniq y' hy' y hy x (hLK₁ h) hK
      subst this
      exact h
    · intro h
      exact ⟨y, hy, h⟩
  have hφUiff : ∀ y ∈ Ω, ∀ i x, (y, x) ∈ K₁ → x ∈ (φ i).dom →
      (ptFun (φ i) x ∈ U ↔ (y, ptFun (φ i) x) ∈ L) := by
    intro y hy i x hK hxd
    rw [hTU]
    constructor
    · rintro ⟨y', hy', h⟩
      have := huniq y' hy' y hy x (hK₁φ i y' x hxd h) hK
      subst this
      exact h
    · intro h
      exact ⟨y, hy, h⟩
  have hTiff : ∀ y ∈ Ω, ∀ i x, (y, x) ∈ K₁ → x ∈ (φ i).dom →
      ((x, ptFun (φ i) x) ∈ T ↔ ((y, x) ∈ L ∧ (y, ptFun (φ i) x) ∈ L)) := by
    intro y hy i x hK hxd
    constructor
    · rintro ⟨y', hy', h1, h2⟩
      have := huniq y' hy' y hy x (hLK₁ h1) hK
      subst this
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨y, hy, h1, h2⟩
  have hBiff : ∀ y ∈ Ω, ∀ i x, ((y, x) ∈ T' ∧ x ∈ B i) ↔
      (x ∈ (φ i).dom ∧ ((y, ptFun (φ i) x) ∈ L ↔ (y, x) ∉ L)) := by
    intro y hy i x
    rw [hT'mem y hy x]
    constructor
    · rintro ⟨hK, hxd, hU', hnT⟩
      refine ⟨hxd, ?_⟩
      rw [hUiff y hy x hK, hφUiff y hy i x hK hxd] at hU'
      rw [hTiff y hy i x hK hxd] at hnT
      tauto
    · rintro ⟨hxd, hiff⟩
      have hK : (y, x) ∈ K₁ := by
        by_cases h : (y, x) ∈ L
        · exact hLK₁ h
        · exact hK₁φ i y x hxd (hiff.2 h)
      refine ⟨hK, hxd, ?_, ?_⟩
      · rw [hUiff y hy x hK, hφUiff y hy i x hK hxd]
        tauto
      · rw [hTiff y hy i x hK hxd]
        tauto
  have hUiff' : ∀ y ∈ Ω, ∀ x, ((y, x) ∈ T' ∧ x ∈ U) ↔ (y, x) ∈ L := by
    intro y hy x
    rw [hT'mem y hy x]
    constructor
    · rintro ⟨hK, hU'⟩
      exact (hUiff y hy x hK).1 hU'
    · intro h
      exact ⟨hLK₁ h, (hUiff y hy x (hLK₁ h)).2 h⟩
  -- the row inequality at every base point `y ∈ Ω`
  have hrow' : ∀ y ∈ Ω, ∑ i, fibreRatio μ R T' (B i) y ≤
      ENNReal.ofReal ε * fibreRatio μ R T' U y := by
    intro y hy
    unfold fibreRatio
    simp only [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← mul_assoc]
    gcongr ?_ * _
    have e1 : ∀ i, ∑' x : {x : X // (y, x) ∈ T' ∧ x ∈ B i}, (module μ R (y, x))⁻¹ =
        ∑' x : {x : X // x ∈ (φ i).dom ∧ ((y, ptFun (φ i) x) ∈ L ↔ (y, x) ∉ L)},
          (module μ R (y, x))⁻¹ := fun i =>
      tsum_subtype_eq_of_iff (f := fun x => (module μ R (y, x))⁻¹) (hBiff y hy i)
    have e2 : ∑' x : {x : X // (y, x) ∈ T' ∧ x ∈ U}, (module μ R (y, x))⁻¹ =
        ∑' x : {x : X // (y, x) ∈ L}, (module μ R (y, x))⁻¹ :=
      tsum_subtype_eq_of_iff (f := fun x => (module μ R (y, x))⁻¹) (hUiff' y hy)
    simp only [e1, e2]
    exact (hrows y hy).le
  -- Step 3: Lemma 2 on `T'`
  set ν := (μ.comap ((↑) : unitSpace T' → X)).map
    (Quot.mk fun a b : unitSpace T' => ((a : X), (b : X)) ∈ T') with hνdef
  have hL2 : ∀ A, MeasurableSet A → A ⊆ unitSpace T' →
      μ A = ∫⁻ F, fibreRatio μ R T' A ((Quot.out F : unitSpace T') : X) ∂ν :=
    fun A hA hAT => ConnesFeldmanWeiss.measure_eq_lintegral_fibreMeasure _ _ _ hR hT' A hA hAT
  have hBT' : ∀ i, B i ⊆ unitSpace T' := by
    rintro i a ⟨hxd, hU', -⟩
    rw [hT'U]
    rcases hU' with h | h
    · rw [hTU] at h
      obtain ⟨y, hy, h⟩ := h
      exact ⟨y, hy, hLK₁ h⟩
    · rw [hTU] at h
      obtain ⟨y, hy, h⟩ := h
      exact ⟨y, hy, hK₁φ i y a hxd h⟩
  have hUT' : U ⊆ unitSpace T' := by
    intro x hx
    rw [hTU] at hx
    obtain ⟨y, hy, h⟩ := hx
    rw [hT'U]
    exact ⟨y, hy, hLK₁ h⟩
  -- the a.e. row inequality on the quotient
  obtain ⟨N, hNm, hN0, hNsat, hN⟩ := CFWPlan.Main.exists_module_cocycle hR
  have hU' : MeasurableSet (unitSpace T') :=
    (measurable_id.prodMk measurable_id) hT'.measurableSet
  have hr : Equivalence fun a b : unitSpace T' => ((a : X), (b : X)) ∈ T' :=
    ⟨fun a => a.2, fun h => hT'.symm _ _ h, fun h₁ h₂ => hT'.trans _ _ _ h₁ h₂⟩
  have hout : ∀ a : unitSpace T',
      (((Quot.out (Quot.mk (fun a b : unitSpace T' => ((a : X), (b : X)) ∈ T') a) :
        unitSpace T') : X), (a : X)) ∈ T' := fun a =>
    (quot_mk_eq_iff hr).1 (Quot.out_eq _)
  have hpre : Quot.mk (fun a b : unitSpace T' => ((a : X), (b : X)) ∈ T') ⁻¹'
      {F | ((Quot.out F : unitSpace T') : X) ∈ N} = Subtype.val ⁻¹' N := by
    ext a
    exact hNsat _ _ (hT'.subset (hout a))
  have hBad : MeasurableSet
      {F : Quot (fun a b : unitSpace T' => ((a : X), (b : X)) ∈ T') |
        ((Quot.out F : unitSpace T') : X) ∈ N} := by
    have hm : MeasurableSet (Quot.mk (fun a b : unitSpace T' => ((a : X), (b : X)) ∈ T') ⁻¹'
        {F | ((Quot.out F : unitSpace T') : X) ∈ N}) := by
      rw [hpre]
      exact measurable_subtype_coe hNm
    exact hm
  have hBad0 : ν {F | ((Quot.out F : unitSpace T') : X) ∈ N} = 0 := by
    rw [hνdef, Measure.map_apply measurable_quot_mk hBad, hpre,
      (MeasurableEmbedding.subtype_coe hU').comap_apply]
    exact measure_mono_null (image_preimage_subset _ _) hN0
  have hae : ∀ᵐ F ∂ν, ∑ i, fibreRatio μ R T' (B i) ((Quot.out F : unitSpace T') : X) ≤
      ENNReal.ofReal ε * fibreRatio μ R T' U ((Quot.out F : unitSpace T') : X) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hBad0] with F hF
    set a : X := ((Quot.out F : unitSpace T') : X) with hadef
    have ha : a ∈ unitSpace T' := (Quot.out F).2
    rw [hT'U] at ha
    obtain ⟨y, hy, hya⟩ := ha
    have hyaT : (y, a) ∈ T' := ⟨y, hy, hdiag y, hya⟩
    have hyN : y ∉ N := fun h => hF ((hNsat y a (hK₁R hya)).1 h)
    have hcongr : ∀ A, fibreRatio μ R T' A y = fibreRatio μ R T' A a := fun A =>
      CFWPlan.Main.fibreRatio_congr hR hT' hN hNsat A hyN hyaT
    simp only [← hcongr]
    exact hrow' y hy
  -- Step 4: assemble
  calc relMeasure μ R {γ ∈ K | (γ.2 ∈ U ∨ γ.1 ∈ U) ∧ γ ∉ T}
      ≤ ∑ i, μ (B i) := step1
    _ = ∑ i, ∫⁻ F, fibreRatio μ R T' (B i) ((Quot.out F : unitSpace T') : X) ∂ν :=
        Finset.sum_congr rfl fun i _ => hL2 (B i) (hBm i) (hBT' i)
    _ ≤ ∫⁻ F, ∑ i, fibreRatio μ R T' (B i) ((Quot.out F : unitSpace T') : X) ∂ν :=
        sum_lintegral_le _ _
    _ ≤ ∫⁻ F, ENNReal.ofReal ε * fibreRatio μ R T' U ((Quot.out F : unitSpace T') : X) ∂ν :=
        lintegral_mono_ae hae
    _ = ENNReal.ofReal ε * μ U := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← hL2 U hUm hUT']

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
/-- **Lemma 8 = milestone `exists_finiteSubrelation_boundary_lt`** (CFW p. 440): assembled from
Lemma 3 (`lemma3`), `exists_folner_set`, `exists_good_rows`, Lemma 4 (`lemma4`) for
`K₁ = K' ∪ K' ∘ K⁻¹`, `isFiniteSubrelation_rowRel` and `boundary_le_of_rows`. -/
theorem lemma8 {μ : Measure X} [IsProbabilityMeasure μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (hamen : Monod.IsAmenableRel μ R) {K : Set (X × X)}
    (hK : IsBoundedSubset μ R K) {ε : ℝ} (hε : 0 < ε) :
    ∃ T, IsFiniteSubrelation R T ∧
      relMeasure μ R {γ ∈ K | (γ.2 ∈ unitSpace T ∨ γ.1 ∈ unitSpace T) ∧ γ ∉ T} <
        ENNReal.ofReal ε * μ (unitSpace T) ∧ μ (unitSpace T) ≠ 0 := by
  have hRe := hR.equivalence
  obtain ⟨-, h3b⟩ := ConnesFeldmanWeiss.exists_isBoundedSubset_cover_and_eq_iUnion_graph _ _ hR
  obtain ⟨n, φ, -, hKeq⟩ := h3b K hK
  have hKφ : K = ⋃ i, CFWPlan.Route.ptGraph (φ i) := by
    rw [hKeq]
    congr 1
    funext i
    ext p
    simp only [CFWPlan.Route.ptGraph, mem_range, mem_ofPred_eq]
    exact exists_congr fun a => eq_comm
  have hδm : Measurable (module μ R) := Measure.measurable_rnDeriv _ _
  obtain ⟨c, hc, hcK⟩ := hK.bdd_module
  have hφ : ∀ i, ∀ᵐ a ∂μ, a ∈ (φ i).dom → (c : ℝ≥0∞) ≤ module μ R (a, ptFun (φ i) a) ∧
      module μ R (a, ptFun (φ i) a) ≤ (c : ℝ≥0∞)⁻¹ := by
    intro i
    have hsub : CFWPlan.Route.ptGraph (φ i) ⊆ K := fun p hp => hKφ ▸ mem_iUnion.2 ⟨i, hp⟩
    refine (ae_ptGraph_iff hR (φ i) (P := fun p => (c : ℝ≥0∞) ≤ module μ R p ∧
      module μ R p ≤ (c : ℝ≥0∞)⁻¹)
      ((measurableSet_le measurable_const hδm).inter (measurableSet_le hδm measurable_const))).1 ?_
    filter_upwards [hcK] with p hp hpG using hp (hsub hpG)
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨K', L, hK'b, hΔK', hLm, hLK', -, -, hineq⟩ :=
    exists_folner_set hR hamen φ hc hφ hε2
  have hLR : L ⊆ R := hLK'.trans hK'b.subset
  obtain ⟨Ω, hΩm, hΩpos, hrows⟩ := exists_good_rows hR φ hLm hLR hε2 hineq
  set K₁ := K' ∪ {p : X × X | ∃ z, (p.1, z) ∈ K' ∧ (z, p.2) ∈ Prod.swap ⁻¹' K} with hK₁def
  have hK₁b : IsBoundedSubset μ R K₁ := CFWPlan.Main.IsBoundedSubset.union hK'b
    (CFWPlan.Main.IsBoundedSubset.comp hR hK'b (CFWPlan.Main.IsBoundedSubset.swap hR hK))
  obtain ⟨Ω', hΩ'Ω, hΩ'm, hΩ'pos, hdisj⟩ := ConnesFeldmanWeiss.exists_subset_pairwise_disjoint_sections _ _ _ hR hK₁b _ hΩm hΩpos
  have hK₁fin : ∀ y, {x | (y, x) ∈ K₁}.Finite := by
    obtain ⟨k, hk⟩ := hK₁b.bdd_fst
    exact fun y => finite_of_encard_le_coe (hk y)
  have hLK₁ : L ⊆ K₁ := fun p hp => Or.inl (hLK' hp)
  have hK₁φ : ∀ i y x, x ∈ (φ i).dom → (y, ptFun (φ i) x) ∈ L → (y, x) ∈ K₁ := by
    intro i y x hx hyL
    refine Or.inr ⟨ptFun (φ i) x, hLK' hyL, ?_⟩
    show (x, ptFun (φ i) x) ∈ K
    rw [hKφ]
    exact mem_iUnion.2 ⟨i, mem_ptGraph (φ i) hx⟩
  have hbd := boundary_le_of_rows hR φ hKφ hLm hK₁b.measurableSet hK₁b.subset hLK₁
    (fun x => Or.inl (hΔK' (show (x, x).1 = (x, x).2 from rfl))) hK₁fin hK₁φ hΩ'm hdisj hε2
    (fun y hy => hrows y (hΩ'Ω hy))
  have hdisjL : ∀ y ∈ Ω', ∀ y' ∈ Ω', y ≠ y' → Disjoint {x | (y, x) ∈ L} {x | (y', x) ∈ L} :=
    fun y hy y' hy' hne => (hdisj y hy y' hy' hne).mono (fun x hx => hLK₁ hx)
      (fun x hx => hLK₁ hx)
  obtain ⟨hT, hTU⟩ := isFiniteSubrelation_rowRel hRe hLm hLR hΩ'm
    (fun y => (hK₁fin y).subset fun x hx => hLK₁ hx) hdisjL
  have hU0 : μ (unitSpace (rowRel Ω' L)) ≠ 0 := by
    intro h0
    have hsat := IsDiscreteMeasured.saturation_null hR h0
    apply hΩ'pos.ne'
    refine measure_mono_null ?_ hsat
    intro y hy
    have hpos := hrows y (hΩ'Ω hy)
    have hne : ∑' x : {x : X // (y, x) ∈ L}, (module μ R (y, x))⁻¹ ≠ 0 := by
      intro h
      rw [h, mul_zero] at hpos
      exact not_lt_zero hpos
    obtain ⟨⟨x, hx⟩, -⟩ := not_forall.1 fun h => hne (ENNReal.tsum_eq_zero.2 h)
    refine ⟨x, ?_, hLR hx⟩
    rw [hTU]
    exact ⟨y, hy, hx⟩
  refine ⟨rowRel Ω' L, hT, ?_, hU0⟩
  calc _ ≤ ENNReal.ofReal (ε / 2) * μ (unitSpace (rowRel Ω' L)) := hbd
    _ < ENNReal.ofReal ε * μ (unitSpace (rowRel Ω' L)) :=
        ENNReal.mul_lt_mul_left hU0 (measure_ne_top _ _)
          ((ENNReal.ofReal_lt_ofReal_iff hε).2 (half_lt_self hε))

end CFWPlan.Main.P4
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias lemma8 := CFWPlan.Main.P4.lemma8

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
    [StandardBorelSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (R : Set (X × X)) (hR : IsDiscreteMeasured μ R) (hamen : Monod.IsAmenableRel μ R)
    (K : Set (X × X)) (hK : IsBoundedSubset μ R K) (ε : ℝ) (hε : 0 < ε) :
    ∃ T, IsFiniteSubrelation R T ∧
      relMeasure μ R {γ ∈ K | (γ.2 ∈ unitSpace T ∨ γ.1 ∈ unitSpace T) ∧ γ ∉ T} <
        ENNReal.ofReal ε * μ (unitSpace T) ∧ μ (unitSpace T) ≠ 0 :=
  lemma8 hR hamen hK hε
end
