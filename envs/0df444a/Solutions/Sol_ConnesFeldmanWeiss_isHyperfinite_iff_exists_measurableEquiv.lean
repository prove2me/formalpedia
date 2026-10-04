-- Prove2me | solution 1 for ConnesFeldmanWeiss.isHyperfinite_iff_exists_measurableEquiv
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T15:49:08.256357+00:00
-- url     : https://prove2.me/submissions/3e344083-6b62-4af6-ba3b-c84dacdfee37

import Theorems.Thm_LusinNovikov_exists_injOn_cover_of_countable_fibers
import Theorems.Thm_LusinNovikov_exists_disjoint_injOn_fst_iUnion_eq_of_countable_sections
import Theorems.Thm_LusinNovikov_measurableSet_image_fst_of_countable_sections
import Mathlib
import Definitions.Def_Monod_PiecewiseProjective
import Theorems.Thm_ConnesFeldmanWeiss_isHyperfinite_iff_isAmenableRel
import Theorems.Thm_ConnesFeldmanWeiss_exists_seq_measurableEquiv_of_countable_classes
import Theorems.Thm_ConnesFeldmanWeiss_isTypeI_iff_exists_iUnion_trivial
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
/-- **B4 = (LN-4).** -/
theorem lusinNovikov_fun [Nonempty Y] {P : Set (X × Y)} (hP : MeasurableSet P)
    (hcount : ∀ x, {y | (x, y) ∈ P}.Countable) :
    ∃ (D : ℕ → Set X) (g : ℕ → X → Y), (∀ n, MeasurableSet (D n)) ∧ (∀ n, Measurable (g n)) ∧
      (∀ n, ∀ x ∈ D n, (x, g n x) ∈ P) ∧ ∀ p ∈ P, ∃ n, p.1 ∈ D n ∧ g n p.1 = p.2 := by
  obtain ⟨G, hGm, hGi, -, hGu⟩ := lusinNovikov hP hcount
  have he : ∀ n, MeasurableEmbedding (fun p : G n => p.1.1) := fun n => by
    have := (hGm n).standardBorel
    exact (measurable_fst.comp measurable_subtype_coe).measurableEmbedding
      (fun p q hpq => Subtype.ext (hGi n p.2 q.2 hpq))
  have hGP : ∀ n, G n ⊆ P := fun n => hGu ▸ subset_iUnion G n
  refine ⟨fun n => range (fun p : G n => p.1.1),
    fun n => extend (fun p : G n => p.1.1) (fun p => p.1.2) (fun _ => Classical.arbitrary Y),
    fun n => (he n).measurableSet_range,
    fun n => (he n).measurable_extend (measurable_snd.comp measurable_subtype_coe)
      measurable_const, ?_, ?_⟩
  · rintro n _ ⟨p, rfl⟩
    beta_reduce
    rw [(he n).injective.extend_apply (fun p : G n => p.1.2)]
    exact hGP n p.2
  · intro p hp
    rw [← hGu, mem_iUnion] at hp
    obtain ⟨n, hn⟩ := hp
    exact ⟨n, ⟨⟨p, hn⟩, rfl⟩, (he n).injective.extend_apply _ _ ⟨p, hn⟩⟩

end CFWPlan.Route.PartB
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Y] [StandardBorelSpace Y]
alias lusinNovikov_fun := CFWPlan.Route.PartB.lusinNovikov_fun

end CFWPlan.Route
end

section
open MeasureTheory Set Function Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal
namespace CFWPlan.Route
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-! ## §C. Feldman–Moore -/

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
alias exists_saturated_null := CFWPlan.Main.P1.exists_saturated_null

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
theorem IsDiscreteMeasured.mono {μ : Measure X} {R S : Set (X × X)} (hR : IsDiscreteMeasured μ R)
    (hS : MeasurableSet S) (hSeq : Equivalence fun x y => (x, y) ∈ S) (hSR : S ⊆ R) :
    IsDiscreteMeasured μ S := by
  refine ⟨hS, hSeq, fun x => (hR.countable_classes x).mono fun y hy => hSR hy, ?_⟩
  intro A hA hA0
  refine measure_mono_null ?_ (hR.quasiInvariant A hA hA0)
  rintro x ⟨y, hy, hxy⟩
  exact ⟨y, hy, hSR hxy⟩

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]
alias IsDiscreteMeasured.mono := CFWPlan.Main.P1.IsDiscreteMeasured.mono

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
theorem IsDiscreteMeasured.of_ac {μ ν : Measure X} {R : Set (X × X)} (hR : IsDiscreteMeasured μ R)
    (h₁ : μ ≪ ν) (h₂ : ν ≪ μ) : IsDiscreteMeasured ν R :=
  ⟨hR.measurableSet, hR.equivalence, hR.countable_classes,
    fun A hA hA0 => h₂ (hR.quasiInvariant A hA (h₁ hA0))⟩

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
alias IsDiscreteMeasured.of_ac := CFWPlan.Main.P1.IsDiscreteMeasured.of_ac

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
theorem IsHyperfinite.of_ac {μ ν : Measure X} {R : Set (X × X)} (h : IsHyperfinite μ R)
    (hνμ : ν ≪ μ) (hμν : μ ≪ ν) : IsHyperfinite ν R := by
  obtain ⟨N, hN, hN0, hdisc, S, hmono, hS, hNR⟩ := h
  refine ⟨N, hN, hνμ hN0, IsDiscreteMeasured.of_ac hdisc hμν hνμ, S, hmono,
    fun n => ⟨(hS n).1, (hS n).2.1, ?_⟩, hNR⟩
  obtain ⟨X₀, hX₀, hX₀c, hsat, hd, hstd⟩ := (hS n).2.2
  exact ⟨X₀, hX₀, hνμ hX₀c, hsat, IsDiscreteMeasured.of_ac hd hμν hνμ, hstd⟩

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]
alias IsHyperfinite.of_ac := CFWPlan.Main.P1.IsHyperfinite.of_ac

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
theorem exists_probability_equiv (μ : Measure X) [SigmaFinite μ] (hμ : μ ≠ 0) :
    ∃ ν : Measure X, IsProbabilityMeasure ν ∧ μ ≪ ν ∧ ν ≪ μ := by
  have h0 : μ.toFinite univ ≠ 0 := by
    rw [Ne, toFinite_apply_eq_zero_iff, Measure.measure_univ_eq_zero]
    exact hμ
  have hfin : μ.toFinite univ ≠ ∞ := measure_ne_top _ _
  refine ⟨(μ.toFinite univ)⁻¹ • μ.toFinite, ⟨?_⟩, ?_, ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 hfin]
  · exact (absolutelyContinuous_toFinite μ).trans
      (Measure.absolutelyContinuous_smul (ENNReal.inv_ne_zero.2 hfin))
  · exact Measure.smul_absolutelyContinuous.trans (toFinite_absolutelyContinuous μ)

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]
alias exists_probability_equiv := CFWPlan.Main.P1.exists_probability_equiv

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
omit [StandardBorelSpace X] in
theorem standardBorelSpace_of_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [StandardBorelSpace α] [MeasurableSpace β] (e : α ≃ᵐ β) : StandardBorelSpace β := by
  letI := upgradeStandardBorel α
  letI τ : TopologicalSpace β := TopologicalSpace.induced e.symm inferInstance
  have hemb : Topology.IsClosedEmbedding (e.symm : β → α) := by
    refine ⟨⟨⟨rfl⟩, e.symm.injective⟩, ?_⟩
    rw [e.symm.surjective.range_eq]
    exact isClosed_univ
  haveI : PolishSpace β := hemb.polishSpace
  haveI : BorelSpace β := ⟨by
    rw [borel_comap, ← eq_borel_upgradeStandardBorel α]
    exact e.symm.measurableEmbedding.comap_eq.symm⟩
  exact ⟨⟨τ, inferInstance, inferInstance⟩⟩

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X]
variable [StandardBorelSpace X]
alias standardBorelSpace_of_measurableEquiv := CFWPlan.Main.P1.standardBorelSpace_of_measurableEquiv

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
theorem IsBoundedSubset.relMeasure_lt_top {μ : Measure X} [IsFiniteMeasure μ] {R K : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (hK : IsBoundedSubset μ R K) : relMeasure μ R K < ∞ := by
  obtain ⟨n, hn⟩ := hK.bdd_fst
  rw [relMeasure_apply hR.measurableSet hR.countable_classes hK.measurableSet]
  calc ∫⁻ x, (({y | (x, y) ∈ K ∩ R}.encard : ℕ∞) : ℝ≥0∞) ∂μ ≤ ∫⁻ _, (n : ℝ≥0∞) ∂μ := by
        refine lintegral_mono fun x => ?_
        have h := (encard_mono (fun y hy => hy.1 :
          {y | (x, y) ∈ K ∩ R} ⊆ {y | (x, y) ∈ K})).trans (hn x)
        simpa using ENat.toENNReal_le.2 h
    _ = n * μ univ := lintegral_const _
    _ < ∞ := ENNReal.mul_lt_top (by simp) (measure_lt_top μ univ)

end CFWPlan.Main.P1
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias IsBoundedSubset.relMeasure_lt_top := CFWPlan.Main.P1.IsBoundedSubset.relMeasure_lt_top

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
/-- A map out of a quotient is measurable when its composition with `Quot.mk` is (the quotient
σ-algebra is the image σ-algebra). -/
theorem measurable_of_quot_mk {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {r : α → α → Prop} {f : Quot r → β} (hf : Measurable (f ∘ Quot.mk r)) : Measurable f :=
  fun _ ht => hf ht

/-- In the quotient by an equivalence relation, `Quot.mk` identifies exactly related points. -/
theorem quot_mk_eq_iff {α : Type*} {r : α → α → Prop} (hr : Equivalence r) {a b : α} :
    Quot.mk r a = Quot.mk r b ↔ r a b :=
  ⟨fun h => hr.eqvGen_iff.1 (Quot.eqvGen_exact h), fun h => Quot.sound h⟩

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
/-- A discrete measured relation cut off outside a Borel set (points of `N` made singletons) is
discrete measured. -/
theorem isDiscreteMeasured_cutOff {μ : Measure X} {R : Set (X × X)} (hR : IsDiscreteMeasured μ R)
    {N : Set X} (hN : MeasurableSet N) : IsDiscreteMeasured μ (cutOff R N) := by
  have hRe := hR.equivalence
  refine ⟨?_, ⟨fun x => Or.inr rfl, ?_, ?_⟩, fun x => ?_, fun A hA hA0 => ?_⟩
  · unfold cutOff
    exact (hR.measurableSet.inter ((measurable_fst hN.compl).inter (measurable_snd hN.compl))).union
      (measurableSet_eq_fun measurable_fst measurable_snd)
  · rintro x y (⟨h, hx, hy⟩ | h)
    · exact Or.inl ⟨hRe.symm h, hy, hx⟩
    · exact Or.inr (Eq.symm h)
  · rintro x y z (⟨h, hx, hy⟩ | h) (⟨h', hy', hz⟩ | h')
    · exact Or.inl ⟨hRe.trans h h', hx, hz⟩
    · have hyz : y = z := h'
      subst hyz
      exact Or.inl ⟨h, hx, hy⟩
    · have hxy : x = y := h
      subst hxy
      exact Or.inl ⟨h', hy', hz⟩
    · exact Or.inr (Eq.trans h h')
  · refine ((hR.countable_classes x).union (countable_singleton x)).mono ?_
    rintro y (⟨h, -, -⟩ | h)
    · exact Or.inl h
    · exact Or.inr (Eq.symm h)
  · refine measure_mono_null ?_ (hR.quasiInvariant A hA hA0)
    rintro x ⟨y, hy, (⟨h, -, -⟩ | h)⟩
    · exact ⟨y, hy, h⟩
    · have hxy : x = y := h
      subst hxy
      exact ⟨x, hy, hRe.refl x⟩

/-- **Lemma 1, "⇒", relative form.** -/
theorem exists_partial_transversals_of_isTypeI {μ : Measure X} {S : Set (X × X)}
    (hS : MeasurableSet S) (hSeq : Equivalence fun x y => (x, y) ∈ S) (hI : IsTypeI μ S)
    {N : Set X} (hN : MeasurableSet N) (hN0 : μ N = 0)
    (hcount : ∀ x, x ∉ N → {y | y ∉ N ∧ (x, y) ∈ S}.Countable) :
    ∃ Y : ℕ → Set X, (∀ n, MeasurableSet (Y n)) ∧ μ (⋃ n, Y n)ᶜ = 0 ∧ (∀ n, Y n ∩ N = ∅) ∧
      ∀ n x y, x ∈ Y n → y ∈ Y n → (x, y) ∈ S → x = y := by
  obtain ⟨X₀, hX₀, hX₀c, -, -, hstd⟩ := hI
  have hZ : MeasurableSet (X₀ \ N) := hX₀.diff hN
  have : StandardBorelSpace (X₀ \ N : Set X) := hZ.standardBorel
  have hr : Equivalence fun a b : X₀ => ((a : X), (b : X)) ∈ S :=
    ⟨fun a => hSeq.refl _, fun h => hSeq.symm h, fun h₁ h₂ => hSeq.trans h₁ h₂⟩
  set q : (X₀ \ N : Set X) → Quot fun a b : X₀ => ((a : X), (b : X)) ∈ S :=
    fun z => Quot.mk _ ⟨z.1, z.2.1⟩ with hq_def
  have hq : Measurable q := measurable_quot_mk.comp measurable_subtype_coe.subtype_mk
  have hqeq : ∀ a b : (X₀ \ N : Set X), q a = q b ↔ ((a : X), (b : X)) ∈ S := fun a b =>
    quot_mk_eq_iff hr
  have hfib : ∀ c, (q ⁻¹' {c}).Countable := by
    intro c
    rcases (q ⁻¹' {c}).eq_empty_or_nonempty with h | ⟨z₀, hz₀⟩
    · rw [h]; exact countable_empty
    · refine MapsTo.countable_of_injOn (f := Subtype.val) ?_ Subtype.val_injective.injOn
        (hcount z₀ z₀.2.2)
      intro z hz
      simp only [mem_preimage, mem_singleton_iff] at hz hz₀
      exact ⟨z.2.2, (hqeq z₀ z).1 (hz₀.trans hz.symm)⟩
  obtain ⟨T, hTm, hTi, hTu⟩ := CFWPlan.Route.exists_injOn_cover_of_countable_fibers hq hfib
  refine ⟨fun n => Subtype.val '' T n,
    fun n => (MeasurableEmbedding.subtype_coe hZ).measurableSet_image.2 (hTm n), ?_, ?_, ?_⟩
  · have hU : (⋃ n, Subtype.val '' T n) = X₀ \ N := by
      rw [← image_iUnion, hTu, image_univ, Subtype.range_coe]
    rw [hU]
    refine measure_mono_null (t := X₀ᶜ ∪ N) ?_ (measure_union_null hX₀c hN0)
    intro x hx
    by_cases h : x ∈ X₀
    · exact Or.inr (by_contra fun hN' => hx ⟨h, hN'⟩)
    · exact Or.inl h
  · intro n
    ext x
    simp only [mem_inter_iff, mem_image, mem_empty_iff_false, iff_false, not_and]
    rintro ⟨z, -, rfl⟩
    exact z.2.2
  · rintro n _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ hab
    exact congrArg Subtype.val (hTi n ha hb ((hqeq a b).2 hab))

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
/-- A Borel transversal and selector from partial transversals. -/
theorem exists_transversal_of_partial_transversals {μ : Measure X} {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (Y : ℕ → Set X) (hY : ∀ n, MeasurableSet (Y n))
    (hcov : μ (⋃ n, Y n)ᶜ = 0) (htriv : ∀ n x y, x ∈ Y n → y ∈ Y n → (x, y) ∈ R → x = y) :
    ∃ (X₀ T₀ : Set X) (s : X → X), MeasurableSet X₀ ∧ μ X₀ᶜ = 0 ∧
      (∀ x y, (x, y) ∈ R → (x ∈ X₀ ↔ y ∈ X₀)) ∧ MeasurableSet T₀ ∧ T₀ ⊆ X₀ ∧ Measurable s ∧
      (∀ x ∈ X₀, s x ∈ T₀ ∧ (x, s x) ∈ R) ∧ (∀ x y, (x, y) ∈ R → s x = s y) ∧
      ∀ t ∈ T₀, s t = t := by
  classical
  have hRe := hR.equivalence
  have hsatm : ∀ A, MeasurableSet A → MeasurableSet (saturation R A) := fun A hA =>
    CFWPlan.Main.measurableSet_saturation hR.measurableSet hRe hR.countable_classes hA
  set Z : ℕ → Set X := fun n => Y n \ saturation R (⋃ k, ⋃ (_ : k < n), Y k) with hZ_def
  set T₀ : Set X := ⋃ n, Z n with hT₀_def
  set X₀ : Set X := saturation R (⋃ n, Y n) with hX₀_def
  have hZm : ∀ n, MeasurableSet (Z n) := fun n =>
    (hY n).diff (hsatm _ (MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => hY k))
  have hT₀m : MeasurableSet T₀ := MeasurableSet.iUnion hZm
  have hX₀m : MeasurableSet X₀ := hsatm _ (MeasurableSet.iUnion hY)
  -- every point of `X₀` is equivalent to a point of `T₀`
  have hex : ∀ x ∈ X₀, ∃ t ∈ T₀, (x, t) ∈ R := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hx
    have hE : ∃ n, ∃ y ∈ Y n, (x, y) ∈ R := by
      obtain ⟨n, hn⟩ := mem_iUnion.1 hy
      exact ⟨n, y, hn, hxy⟩
    obtain ⟨y₀, hy₀, hxy₀⟩ := Nat.find_spec hE
    refine ⟨y₀, mem_iUnion.2 ⟨Nat.find hE, hy₀, ?_⟩, hxy₀⟩
    rintro ⟨w, hw, hy₀w⟩
    obtain ⟨k, hk⟩ := mem_iUnion.1 hw
    obtain ⟨hkn, hwk⟩ := mem_iUnion.1 hk
    exact Nat.find_min hE hkn ⟨w, hwk, hRe.trans hxy₀ hy₀w⟩
  -- uniqueness of the representative
  have huniq : ∀ t ∈ T₀, ∀ t' ∈ T₀, (t, t') ∈ R → t = t' := by
    intro t ht t' ht' htt'
    obtain ⟨n, hnY, hnS⟩ := mem_iUnion.1 ht
    obtain ⟨m, hmY, hmS⟩ := mem_iUnion.1 ht'
    rcases lt_trichotomy n m with hnm | rfl | hmn
    · exact absurd ⟨t, mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨hnm, hnY⟩⟩, hRe.symm htt'⟩ hmS
    · exact htriv n t t' hnY hmY htt'
    · exact absurd ⟨t', mem_iUnion.2 ⟨m, mem_iUnion.2 ⟨hmn, hmY⟩⟩, htt'⟩ hnS
  have hT₀X₀ : T₀ ⊆ X₀ := by
    intro t ht
    obtain ⟨n, hnY, -⟩ := mem_iUnion.1 ht
    exact ⟨t, mem_iUnion.2 ⟨n, hnY⟩, hRe.refl t⟩
  have hX₀sat : ∀ x y, (x, y) ∈ R → (x ∈ X₀ ↔ y ∈ X₀) := by
    intro x y hxy
    constructor
    · rintro ⟨w, hw, hxw⟩
      exact ⟨w, hw, hRe.trans (hRe.symm hxy) hxw⟩
    · rintro ⟨w, hw, hyw⟩
      exact ⟨w, hw, hRe.trans hxy hyw⟩
  have hX₀c : μ X₀ᶜ = 0 := by
    refine measure_mono_null ?_ hcov
    refine compl_subset_compl.2 fun y hy => ⟨y, hy, hRe.refl y⟩
  -- the selector
  obtain ⟨φ, hφ⟩ := IsDiscreteMeasured.exists_generators hR
  have hp : ∀ x, ∃ n, x ∉ X₀ ∨ φ n x ∈ T₀ := by
    intro x
    by_cases hx : x ∈ X₀
    · obtain ⟨t, ht, hxt⟩ := hex x hx
      obtain ⟨n, hn⟩ := (hφ x t).1 hxt
      exact ⟨n, Or.inr (hn ▸ ht)⟩
    · exact ⟨0, Or.inl hx⟩
  have hpm : ∀ n, MeasurableSet {x | x ∉ X₀ ∨ φ n x ∈ T₀} := fun n =>
    hX₀m.compl.union ((φ n).measurable hT₀m)
  set g : X → X := fun x => φ (Nat.find (hp x)) x with hg_def
  have hgm : Measurable g := Measurable.find (fun n => (φ n).measurable) hpm hp
  set c : X → X := fun x => Classical.choice (⟨x⟩ : Nonempty X) with hc_def
  have hcm : Measurable c := measurable_const' fun _ _ => rfl
  set s : X → X := X₀.piecewise g c with hs_def
  have hsm : Measurable s := hgm.piecewise hX₀m hcm
  have hsX₀ : ∀ x ∈ X₀, s x ∈ T₀ ∧ (x, s x) ∈ R := by
    intro x hx
    have hsx : s x = g x := piecewise_eq_of_mem _ _ _ hx
    rw [hsx]
    refine ⟨?_, (hφ x _).2 ⟨_, rfl⟩⟩
    rcases Nat.find_spec (hp x) with h | h
    · exact absurd hx h
    · exact h
  refine ⟨X₀, T₀, s, hX₀m, hX₀c, hX₀sat, hT₀m, hT₀X₀, hsm, hsX₀, ?_, ?_⟩
  · intro x y hxy
    by_cases hx : x ∈ X₀
    · have hy : y ∈ X₀ := (hX₀sat x y hxy).1 hx
      refine huniq _ (hsX₀ x hx).1 _ (hsX₀ y hy).1 ?_
      exact hRe.trans (hRe.symm (hsX₀ x hx).2) (hRe.trans hxy (hsX₀ y hy).2)
    · have hy : y ∉ X₀ := fun hy => hx ((hX₀sat x y hxy).2 hy)
      rw [hs_def, piecewise_eq_of_notMem _ _ _ hx, piecewise_eq_of_notMem _ _ _ hy]
  · intro t ht
    have h := hsX₀ t (hT₀X₀ ht)
    exact (huniq t ht _ h.1 h.2).symm

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias exists_transversal_of_partial_transversals := CFWPlan.Main.P2.exists_transversal_of_partial_transversals

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
/-- **Lemma 1, "⇐"** (CFW p. 434). -/
theorem isTypeI_of_partial_transversals {μ : Measure X} {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (Y : ℕ → Set X) (hY : ∀ n, MeasurableSet (Y n))
    (hcov : μ (⋃ n, Y n)ᶜ = 0) (htriv : ∀ n x y, x ∈ Y n → y ∈ Y n → (x, y) ∈ R → x = y) :
    IsTypeI μ R := by
  obtain ⟨X₀, T₀, s, hX₀, hX₀c, hsat, hT₀, hT₀X₀, hs, hsT, hsc, hst⟩ :=
    exists_transversal_of_partial_transversals hR Y hY hcov htriv
  refine ⟨X₀, hX₀, hX₀c, hsat, isDiscreteMeasured_cutOff hR hX₀.compl, ?_⟩
  have : StandardBorelSpace T₀ := hT₀.standardBorel
  have hRe := hR.equivalence
  let e : T₀ ≃ᵐ Quot fun a b : X₀ => ((a : X), (b : X)) ∈ R :=
    { toFun := fun t => Quot.mk _ ⟨t, hT₀X₀ t.2⟩
      invFun := Quot.lift (fun a : X₀ => (⟨s a, (hsT a a.2).1⟩ : T₀))
        (fun a b hab => Subtype.ext (hsc _ _ hab))
      left_inv := fun t => Subtype.ext (hst t t.2)
      right_inv := by
        intro F
        induction F using Quot.ind with
        | mk a => exact Quot.sound (hRe.symm (hsT a a.2).2)
      measurable_toFun := measurable_quot_mk.comp measurable_subtype_coe.subtype_mk
      measurable_invFun := measurable_of_quot_mk
        ((hs.comp measurable_subtype_coe).subtype_mk) }
  exact standardBorelSpace_of_measurableEquiv e

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
/-- **Normal form of hyperfiniteness.** -/
theorem IsHyperfinite.normalForm {μ : Measure X} {R : Set (X × X)} (hR : IsDiscreteMeasured μ R)
    (h : IsHyperfinite μ R) :
    ∃ S : ℕ → Set (X × X), Monotone S ∧
      (∀ n, S n ⊆ R ∧ IsDiscreteMeasured μ (S n) ∧ IsTypeI μ (S n)) ∧
      ∃ N : Set X, MeasurableSet N ∧ μ N = 0 ∧ (∀ x y, (x, y) ∈ R → (x ∈ N ↔ y ∈ N)) ∧
        ∀ x, x ∉ N → ∀ y, ((x, y) ∈ R ↔ ∃ n, (x, y) ∈ S n) := by
  obtain ⟨N, hN, hN0, -, S, hSmono, hS, hSR⟩ := h
  obtain ⟨N', hNN', hN', hN'0, hN'sat⟩ := CFWPlan.Main.exists_saturated_null hR hN0
  refine ⟨fun n => S n ∩ R, fun m n hmn => inter_subset_inter_left _ (hSmono hmn),
    fun n => ?_, N', hN', hN'0, hN'sat, ?_⟩
  · have hSRm : MeasurableSet (S n ∩ R) := (hS n).1.inter hR.measurableSet
    have hSReq : Equivalence fun x y => (x, y) ∈ S n ∩ R :=
      ⟨fun x => ⟨(hS n).2.1.refl x, hR.equivalence.refl x⟩,
        fun h => ⟨(hS n).2.1.symm h.1, hR.equivalence.symm h.2⟩,
        fun h₁ h₂ => ⟨(hS n).2.1.trans h₁.1 h₂.1, hR.equivalence.trans h₁.2 h₂.2⟩⟩
    have hD : IsDiscreteMeasured μ (S n ∩ R) :=
      CFWPlan.Main.IsDiscreteMeasured.mono hR hSRm hSReq inter_subset_right
    refine ⟨inter_subset_right, hD, ?_⟩
    obtain ⟨Y, hY, hcov, -, htriv⟩ :=
      exists_partial_transversals_of_isTypeI (hS n).1 (hS n).2.1 (hS n).2.2 hN' hN'0 (by
        intro x hx
        refine (hR.countable_classes x).mono ?_
        rintro y ⟨hy, hxy⟩
        exact (hSR x y (fun h => hx (hNN' h)) (fun h => hy (hNN' h))).2 ⟨n, hxy⟩)
    exact isTypeI_of_partial_transversals hD Y hY hcov fun k x y hx hy hxy =>
      htriv k x y hx hy hxy.1
  · intro x hx y
    constructor
    · intro hxy
      have hy : y ∉ N' := fun h => hx ((hN'sat x y hxy).2 h)
      obtain ⟨n, hn⟩ := (hSR x y (fun h => hx (hNN' h)) (fun h => hy (hNN' h))).1 hxy
      exact ⟨n, hn, hxy⟩
    · rintro ⟨n, hn⟩
      exact hn.2

end CFWPlan.Main.P2
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias IsHyperfinite.normalForm := CFWPlan.Main.P2.IsHyperfinite.normalForm

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

/-- A measurable equivalence relation with finite classes inside `R` is an f.s.r. of `R` with unit
space `X`. -/
theorem isFiniteSubrelation_of_equivalence {R F : Set (X × X)} (hF : MeasurableSet F)
    (hFR : F ⊆ R) (heq : Equivalence fun x y => (x, y) ∈ F)
    (hfin : ∀ x, {y | (x, y) ∈ F}.Finite) : IsFiniteSubrelation R F :=
  ⟨hF, hFR, fun p _ => ⟨heq.refl p.1, heq.refl p.2⟩, fun _ _ => heq.symm,
    fun _ _ _ => heq.trans, hfin⟩

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
/-- `R` is, off a null `R`-saturated set, an increasing union of finite Borel equivalence relations
contained in `R`. The working form of hyperfiniteness for Theorem 10 and Dye. -/
def IsFinHyp (μ : Measure X) (R : Set (X × X)) : Prop :=
  ∃ F : ℕ → Set (X × X), Monotone F ∧
    (∀ n, MeasurableSet (F n) ∧ F n ⊆ R ∧ Equivalence (fun x y => (x, y) ∈ F n) ∧
      ∀ x, {y | (x, y) ∈ F n}.Finite) ∧
    ∃ N : Set X, MeasurableSet N ∧ μ N = 0 ∧ (∀ x y, (x, y) ∈ R → (x ∈ N ↔ y ∈ N)) ∧
      ∀ x, x ∉ N → ∀ y, ((x, y) ∈ R ↔ ∃ n, (x, y) ∈ F n)

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
theorem isFinHyp_of_approx {μ : Measure X} [IsFiniteMeasure μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (K : ℕ → Set (X × X)) (hKmono : Monotone K)
    (hK : ∀ n, IsBoundedSubset μ R (K n)) (hKR : R = ⋃ n, K n)
    (happrox : ∀ n (ε : ℝ), 0 < ε →
      ∃ T, IsFiniteSubrelation R T ∧ relMeasure μ R (K n \ T) < ENNReal.ofReal ε) :
    IsFinHyp μ R := by
  choose T hT hTK using fun n => happrox n ((1 / 2 : ℝ) ^ n) (by positivity)
  let F : ℕ → Set (X × X) := fun n => (⋂ k, ⋂ (_ : n ≤ k), T k) ∪ {p | p.1 = p.2}
  have hFmeas : ∀ n, MeasurableSet (F n) := fun n =>
    (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => (hT k).measurableSet).union
      measurableSet_diagonal
  have hFmono : Monotone F := by
    intro n n' h p hp
    rcases hp with hp | hp
    · exact Or.inl (mem_iInter₂.2 fun k hk => mem_iInter₂.1 hp k (h.trans hk))
    · exact Or.inr hp
  have hFR : ∀ n, F n ⊆ R := by
    rintro n ⟨x, y⟩ (hp | hp)
    · exact (hT n).subset (mem_iInter₂.1 hp n le_rfl)
    · have hxy : x = y := hp
      subst hxy
      exact hR.equivalence.refl x
  have hFeq : ∀ n, Equivalence fun x y => (x, y) ∈ F n := by
    intro n
    refine ⟨fun x => Or.inr rfl, ?_, ?_⟩
    · rintro x y (h | h)
      · exact Or.inl (mem_iInter₂.2 fun k hk => (hT k).symm x y (mem_iInter₂.1 h k hk))
      · exact Or.inr (h : x = y).symm
    · rintro x y z (h | h) (h' | h')
      · exact Or.inl (mem_iInter₂.2 fun k hk =>
          (hT k).trans x y z (mem_iInter₂.1 h k hk) (mem_iInter₂.1 h' k hk))
      · have hyz : y = z := h'
        subst hyz
        exact Or.inl h
      · have hxy : x = y := h
        subst hxy
        exact Or.inl h'
      · exact Or.inr ((h : x = y).trans h')
  have hFfin : ∀ n x, {y | (x, y) ∈ F n}.Finite := by
    intro n x
    refine (((hT n).finite_classes x).union (finite_singleton x)).subset ?_
    rintro y (h | h)
    · exact Or.inl (mem_iInter₂.1 h n le_rfl)
    · exact Or.inr (h : x = y).symm
  -- Borel–Cantelli for the bad sets `K k \ T k`
  have hsum : ∑' k, relMeasure μ R (K k \ T k) ≠ ∞ := by
    refine ne_top_of_le_ne_top (b := ∑' k, ENNReal.ofReal ((1 / 2 : ℝ) ^ k)) ?_
      (ENNReal.tsum_le_tsum fun k => (hTK k).le)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) summable_geometric_two]
    exact ENNReal.ofReal_ne_top
  have hlim := measure_limsup_atTop_eq_zero hsum
  have hEm : MeasurableSet (R \ ⋃ n, F n) := hR.measurableSet.diff (MeasurableSet.iUnion hFmeas)
  have hE0 : relMeasure μ R (R \ ⋃ n, F n) = 0 := by
    refine measure_mono_null (fun γ hγ => ?_) hlim
    rw [mem_limsup_iff_frequently_mem, Filter.frequently_atTop]
    intro a
    by_contra hcon
    push Not at hcon
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hKR ▸ hγ.1 : γ ∈ ⋃ n, K n)
    refine hγ.2 (mem_iUnion.2 ⟨max a j, Or.inl (mem_iInter₂.2 fun k hk => ?_)⟩)
    by_contra hTk
    exact hcon k ((le_max_left a j).trans hk)
      ⟨hKmono ((le_max_right a j).trans hk) hj, hTk⟩
  have hae : ∀ᵐ x ∂μ, ∀ y, (x, y) ∈ R → (x, y) ∈ (R \ ⋃ n, F n)ᶜ :=
    (CFWPlan.Main.ae_relMeasure_iff hR.measurableSet hR.countable_classes
      (p := fun q => q ∈ (R \ ⋃ n, F n)ᶜ) hEm.compl).1
      (measure_eq_zero_iff_ae_notMem.1 hE0)
  obtain ⟨N, hBN, hN, hN0, hNsat⟩ := CFWPlan.Main.exists_saturated_null hR (ae_iff.1 hae)
  refine ⟨F, hFmono, fun n => ⟨hFmeas n, hFR n, hFeq n, hFfin n⟩, N, hN, hN0, hNsat,
    fun x hx y => ⟨fun hxy => ?_, fun ⟨n, hn⟩ => hFR n hn⟩⟩
  have hxB : ∀ y, (x, y) ∈ R → (x, y) ∈ (R \ ⋃ n, F n)ᶜ := by
    by_contra h
    exact hx (hBN h)
  by_contra hne
  exact hxB y hxy ⟨hxy, fun h => hne (mem_iUnion.1 h)⟩

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
theorem exists_finite_exhaustion_of_isTypeI {μ : Measure X} [SigmaFinite μ] {S : Set (X × X)}
    (hS : IsDiscreteMeasured μ S) (hI : IsTypeI μ S) :
    ∃ (X₀ : Set X) (F : ℕ → Set (X × X)), MeasurableSet X₀ ∧ μ X₀ᶜ = 0 ∧
      (∀ x y, (x, y) ∈ S → (x ∈ X₀ ↔ y ∈ X₀)) ∧ Monotone F ∧
      (∀ n, MeasurableSet (F n) ∧ F n ⊆ S ∧ Equivalence (fun x y => (x, y) ∈ F n) ∧
        ∀ x, {y | (x, y) ∈ F n}.Finite) ∧
      ∀ x ∈ X₀, ∀ y, (x, y) ∈ S → ∃ n, (x, y) ∈ F n := by
  obtain ⟨Y, hY, hcov, htriv⟩ := (ConnesFeldmanWeiss.isTypeI_iff_exists_iUnion_trivial _ _ hS).1 hI
  obtain ⟨X₀, T₀, s, hX₀, hX₀c, hX₀sat, hT₀, hT₀X₀, hs, hsX₀, hsconst, hsT₀⟩ :=
    CFWPlan.Main.exists_transversal_of_partial_transversals hS Y hY hcov htriv
  obtain ⟨ψ, hψ⟩ := CFWPlan.Main.IsDiscreteMeasured.exists_generators hS
  let G : ℕ → Set X := fun k => X₀ ∩ ⋃ j ∈ Iic k, {x | ψ j (s x) = x}
  have hGm : ∀ k, MeasurableSet (G k) := fun k =>
    hX₀.inter (MeasurableSet.biUnion (to_countable _) fun j _ =>
      (((ψ j).measurable.comp hs).prodMk measurable_id) measurableSet_diagonal)
  have hGmono : Monotone G := by
    rintro k k' h x ⟨hx, hx'⟩
    obtain ⟨j, hj, hj'⟩ := mem_iUnion₂.1 hx'
    exact ⟨hx, mem_iUnion₂.2 ⟨j, mem_Iic.2 ((mem_Iic.1 hj).trans h), hj'⟩⟩
  have hmemG : ∀ x, x ∈ X₀ → ∃ j, x ∈ G j := by
    intro x hx
    obtain ⟨j, hj⟩ := (hψ (s x) x).1 (hS.equivalence.symm (hsX₀ x hx).2)
    exact ⟨j, hx, mem_iUnion₂.2 ⟨j, mem_Iic.2 le_rfl, hj⟩⟩
  let F : ℕ → Set (X × X) := fun k => {p | p.1 = p.2 ∨ (p ∈ S ∧ p.1 ∈ G k ∧ p.2 ∈ G k)}
  refine ⟨X₀, F, hX₀, hX₀c, hX₀sat, ?_, fun k => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro k k' h p hp
    rcases hp with hp | ⟨h1, h2, h3⟩
    · exact Or.inl hp
    · exact Or.inr ⟨h1, hGmono h h2, hGmono h h3⟩
  · have : F k = {p : X × X | p.1 = p.2} ∪ (S ∩ G k ×ˢ G k) := by
      ext p
      simp only [F, mem_ofPred_eq, mem_union, mem_inter_iff, mem_prod]
    rw [this]
    exact measurableSet_diagonal.union (hS.measurableSet.inter ((hGm k).prod (hGm k)))
  · rintro ⟨x, y⟩ (h | ⟨h, -, -⟩)
    · have hxy : x = y := h
      subst hxy
      exact hS.equivalence.refl x
    · exact h
  · refine ⟨fun x => Or.inl rfl, ?_, ?_⟩
    · rintro x y (h | ⟨h1, h2, h3⟩)
      · exact Or.inl (h : x = y).symm
      · exact Or.inr ⟨hS.equivalence.symm h1, h3, h2⟩
    · rintro x y z (h | ⟨h1, h2, h3⟩) (h' | ⟨h1', h2', h3'⟩)
      · exact Or.inl ((h : x = y).trans h')
      · have hxy : x = y := h
        subst hxy
        exact Or.inr ⟨h1', h2', h3'⟩
      · have hyz : y = z := h'
        subst hyz
        exact Or.inr ⟨h1, h2, h3⟩
      · exact Or.inr ⟨hS.equivalence.trans h1 h1', h2, h3'⟩
  · intro x
    refine ((finite_singleton x).union ((finite_Iic k).image fun j => ψ j (s x))).subset ?_
    rintro y (h | ⟨h1, -, -, h3⟩)
    · exact Or.inl (h : x = y).symm
    · obtain ⟨j, hj, hj'⟩ := mem_iUnion₂.1 h3
      refine Or.inr ⟨j, hj, ?_⟩
      have hsy : s x = s y := hsconst x y h1
      simp only [mem_ofPred_eq] at hj'
      rw [hsy]
      exact hj'
  · intro x hx y hxy
    have hy : y ∈ X₀ := (hX₀sat x y hxy).1 hx
    obtain ⟨j, hj⟩ := hmemG x hx
    obtain ⟨j', hj'⟩ := hmemG y hy
    exact ⟨max j j', Or.inr ⟨hxy, hGmono (le_max_left j j') hj, hGmono (le_max_right j j') hj'⟩⟩

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
theorem IsHyperfinite.isFinHyp {μ : Measure X} [IsFiniteMeasure μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (h : IsHyperfinite μ R) : IsFinHyp μ R := by
  obtain ⟨S, hSmono, hS, N, hN, hN0, hNsat, hNS⟩ := CFWPlan.Main.IsHyperfinite.normalForm hR h
  choose X₀ F hX₀ hX₀c hX₀sat hFmono hF hcov using
    fun n => exists_finite_exhaustion_of_isTypeI (hS n).2.1 (hS n).2.2
  obtain ⟨K, hKmono, hK, hKR⟩ := CFWPlan.Main.exists_isBoundedSubset_mono_cover hR
  refine isFinHyp_of_approx hR K hKmono hK hKR fun j ε hε => ?_
  have hKm : MeasurableSet (K j) := (hK j).measurableSet
  have hKfin : relMeasure μ R (K j) ≠ ∞ :=
    (CFWPlan.Main.IsBoundedSubset.relMeasure_lt_top hR (hK j)).ne
  have hSm : ∀ n, MeasurableSet (S n) := fun n => (hS n).2.1.measurableSet
  have hε2' : 0 < ε / 2 := half_pos hε
  have hε2 : 0 < ENNReal.ofReal (ε / 2) := ENNReal.ofReal_pos.2 hε2'
  have h1 : ⨅ n, relMeasure μ R (K j \ S n) = 0 := by
    rw [← Antitone.measure_iInter (fun a b hab => sdiff_subset_sdiff_right (hSmono hab))
      (fun n => (hKm.diff (hSm n)).nullMeasurableSet)
      ⟨0, ne_top_of_le_ne_top hKfin (measure_mono sdiff_subset)⟩]
    refine relMeasure_eq_zero_of_fst hR hN0 fun γ hγ => ?_
    by_contra hγN
    have hγ' := mem_iInter.1 hγ
    have hγR : γ ∈ R := hKR ▸ mem_iUnion.2 ⟨j, (hγ' 0).1⟩
    obtain ⟨n, hn⟩ := (hNS γ.1 hγN γ.2).1 hγR
    exact (hγ' n).2 hn
  obtain ⟨n, hn⟩ := iInf_lt_iff.1
    (by rw [h1]; exact hε2 : ⨅ n, relMeasure μ R (K j \ S n) < ENNReal.ofReal (ε / 2))
  have h2 : ⨅ k, relMeasure μ R ((K j ∩ S n ∩ X₀ n ×ˢ univ) \ F n k) = 0 := by
    rw [← Antitone.measure_iInter (fun a b hab => sdiff_subset_sdiff_right (hFmono n hab))
      (fun k => (((hKm.inter (hSm n)).inter ((hX₀ n).prod MeasurableSet.univ)).diff
        (hF n k).1).nullMeasurableSet)
      ⟨0, ne_top_of_le_ne_top hKfin
        (measure_mono (sdiff_subset.trans (inter_subset_left.trans inter_subset_left)))⟩]
    convert measure_empty (μ := relMeasure μ R)
    refine eq_empty_iff_forall_notMem.2 fun γ hγ => ?_
    have hγ' := mem_iInter.1 hγ
    obtain ⟨⟨⟨-, hγS⟩, hγX, -⟩, -⟩ := hγ' 0
    obtain ⟨k, hk⟩ := hcov n γ.1 hγX γ.2 hγS
    exact (hγ' k).2 hk
  obtain ⟨k, hk⟩ := iInf_lt_iff.1
    (by rw [h2]; exact hε2 :
      ⨅ k, relMeasure μ R ((K j ∩ S n ∩ X₀ n ×ˢ univ) \ F n k) < ENNReal.ofReal (ε / 2))
  have h3 : relMeasure μ R ((X₀ n)ᶜ ×ˢ univ) = 0 :=
    relMeasure_eq_zero_of_fst hR (hX₀c n) fun γ hγ => hγ.1
  refine ⟨F n k, isFiniteSubrelation_of_equivalence (hF n k).1 ((hF n k).2.1.trans (hS n).1)
    (hF n k).2.2.1 (hF n k).2.2.2, ?_⟩
  calc relMeasure μ R (K j \ F n k)
      ≤ relMeasure μ R ((K j \ S n) ∪ ((K j ∩ S n ∩ X₀ n ×ˢ univ) \ F n k) ∪
          (X₀ n)ᶜ ×ˢ univ) := by
        refine measure_mono fun γ hγ => ?_
        by_cases hγS : γ ∈ S n
        · by_cases hγX : γ.1 ∈ X₀ n
          · exact Or.inl (Or.inr ⟨⟨⟨hγ.1, hγS⟩, hγX, trivial⟩, hγ.2⟩)
          · exact Or.inr ⟨hγX, trivial⟩
        · exact Or.inl (Or.inl ⟨hγ.1, hγS⟩)
    _ ≤ relMeasure μ R (K j \ S n) + relMeasure μ R ((K j ∩ S n ∩ X₀ n ×ˢ univ) \ F n k) +
          relMeasure μ R ((X₀ n)ᶜ ×ˢ univ) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ = relMeasure μ R (K j \ S n) + relMeasure μ R ((K j ∩ S n ∩ X₀ n ×ˢ univ) \ F n k) := by
        rw [h3, add_zero]
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := ENNReal.add_lt_add hn hk
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add hε2'.le hε2'.le, add_halves]

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
/-- **Borel argmin.** For a Borel set `Q ⊆ X × X` with finite sections and a measurable key
`κ : X → ℝ`, there is a Borel map `s` with `s x` a `κ`-minimal point of the section `Q_x`
whenever that section is nonempty. *Proof:* Lusin–Novikov writes `Q` as a countable union of Borel
graphs `x ↦ gₙ x` over `Dₙ`; `s x = g_{n(x)} x` for the least `n` with `x ∈ Dₙ` and
`κ (gₙ x) ≤ κ (gₘ x)` for all `m` with `x ∈ Dₘ` (`Measurable.find`). -/
theorem exists_argmin {Q : Set (X × X)} (hQ : MeasurableSet Q)
    (hfin : ∀ x, {y | (x, y) ∈ Q}.Finite) {κ : X → ℝ} (hκ : Measurable κ) :
    ∃ s : X → X, Measurable s ∧ ∀ x, (∃ y, (x, y) ∈ Q) →
      (x, s x) ∈ Q ∧ ∀ y, (x, y) ∈ Q → κ (s x) ≤ κ y := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨id, measurable_id, fun x => (IsEmpty.false x).elim⟩
  obtain ⟨D, g, hD, hg, hgQ, hQg⟩ :=
    CFWPlan.Route.lusinNovikov_fun hQ (fun x => (hfin x).countable)
  set A : ℕ → Set X := fun n => D n ∩ ⋂ m, ((D m)ᶜ ∪ {x | κ (g n x) ≤ κ (g m x)}) with hA
  have hAm : ∀ n, MeasurableSet (A n) := fun n =>
    (hD n).inter (MeasurableSet.iInter fun m => (hD m).compl.union
      (measurableSet_le (hκ.comp (hg n)) (hκ.comp (hg m))))
  classical
  have hex : ∀ x, ∃ n, x ∈ A n ∨ x ∉ ⋃ m, A m := by
    intro x
    by_cases hx : x ∈ ⋃ m, A m
    · obtain ⟨n, hn⟩ := mem_iUnion.1 hx
      exact ⟨n, Or.inl hn⟩
    · exact ⟨0, Or.inr hx⟩
  refine ⟨fun x => g (Nat.find (hex x)) x,
    Measurable.find (p := fun n x => x ∈ A n ∨ x ∉ ⋃ m, A m) hg
      (fun n => (hAm n).union (MeasurableSet.iUnion hAm).compl) hex, ?_⟩
  rintro x ⟨y, hy⟩
  obtain ⟨y₀, hy₀, hmin⟩ := Set.exists_min_image {y | (x, y) ∈ Q} κ (hfin x) ⟨y, hy⟩
  obtain ⟨n, hn, hny⟩ := hQg (x, y₀) hy₀
  simp only at hn hny
  have hxA : x ∈ A n := by
    refine ⟨hn, mem_iInter.2 fun m => ?_⟩
    by_cases hm : x ∈ D m
    · exact Or.inr (show κ (g n x) ≤ κ (g m x) by rw [hny]; exact hmin _ (hgQ m x hm))
    · exact Or.inl hm
  have hxU : x ∈ ⋃ m, A m := mem_iUnion.2 ⟨n, hxA⟩
  have hk : x ∈ A (Nat.find (hex x)) := (Nat.find_spec (hex x)).resolve_right (not_not.2 hxU)
  refine ⟨hgQ _ x hk.1, fun z hz => ?_⟩
  obtain ⟨m, hm, hmz⟩ := hQg (x, z) hz
  simp only at hm hmz
  rcases mem_iInter.1 hk.2 m with h | h
  · exact absurd hm h
  · rw [← hmz]; exact h

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
/-- The cyclic "next" of a finite set (least strictly larger element, else the least element) is
injective. -/
theorem next_injOn {S : Set X} {κ : X → ℝ} (hκ : InjOn κ S) {nx : X → X}
    (hspec : ∀ a ∈ S, (κ a < κ (nx a) ∧ ∀ y ∈ S, κ a < κ y → κ (nx a) ≤ κ y) ∨
       ((∀ y ∈ S, κ y ≤ κ a) ∧ ∀ y ∈ S, κ (nx a) ≤ κ y)) :
    InjOn nx S := by
  have key : ∀ a ∈ S, ∀ b ∈ S, κ a < κ b → nx a = nx b → False := by
    intro a ha b hb hlt he
    rcases hspec a ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hspec b hb with ⟨h3, h4⟩ | ⟨h3, h4⟩
      · have := h2 b hb hlt
        rw [he] at this
        linarith
      · have := h4 a ha
        rw [← he] at this
        linarith
    · have := h1 b hb
      linarith
  intro a ha b hb hab
  by_contra hne
  rcases lt_or_gt_of_ne (fun h => hne (hκ ha hb h)) with h | h
  · exact key a ha b hb h hab
  · exact key b hb a ha h hab.symm

/-- The cyclic "next" of a finite set is a single cycle: every element reaches every other. -/
theorem next_reach {S : Set X} (hS : S.Finite) {κ : X → ℝ} (hκ : InjOn κ S) {nx : X → X}
    (hmaps : ∀ a ∈ S, nx a ∈ S)
    (hspec : ∀ a ∈ S, (κ a < κ (nx a) ∧ ∀ y ∈ S, κ a < κ y → κ (nx a) ≤ κ y) ∨
       ((∀ y ∈ S, κ y ≤ κ a) ∧ ∀ y ∈ S, κ (nx a) ≤ κ y)) :
    ∀ a ∈ S, ∀ b ∈ S, ∃ j : ℕ, nx^[j] a = b := by
  intro a ha b hb
  obtain ⟨m, hmS, hm⟩ := Set.exists_min_image S κ hS ⟨a, ha⟩
  have h1 : ∀ n : ℕ, ∀ a ∈ S, {y ∈ S | κ a < κ y}.ncard = n → ∃ j, nx^[j] a = m := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro a ha hn
      rcases hspec a ha with ⟨h1, -⟩ | ⟨-, h2⟩
      · have hsub : {y ∈ S | κ (nx a) < κ y} ⊂ {y ∈ S | κ a < κ y} := by
          refine ⟨fun y hy => ⟨hy.1, h1.trans hy.2⟩, fun h => ?_⟩
          exact lt_irrefl _ (h ⟨hmaps a ha, h1⟩).2
        have hlt := Set.ncard_lt_ncard hsub (hS.subset fun y hy => hy.1)
        obtain ⟨j, hj⟩ := ih _ (hn ▸ hlt) (nx a) (hmaps a ha) rfl
        exact ⟨j + 1, by rw [iterate_succ_apply]; exact hj⟩
      · refine ⟨1, ?_⟩
        simp only [iterate_one]
        exact hκ (hmaps a ha) hmS (le_antisymm (h2 m hmS) (hm _ (hmaps a ha)))
  have h2 : ∀ n : ℕ, ∀ b ∈ S, {y ∈ S | κ y < κ b}.ncard = n → ∃ j, nx^[j] m = b := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro b hb hn
      by_cases hne : {y ∈ S | κ y < κ b}.Nonempty
      · obtain ⟨p, hp, hpmax⟩ :=
          Set.exists_max_image _ κ (hS.subset fun y hy => hy.1) hne
        have hnp : nx p = b := by
          rcases hspec p hp.1 with ⟨h1, h2⟩ | ⟨h1, -⟩
          · rcases (h2 b hb hp.2).lt_or_eq with hlt | heq
            · have := hpmax (nx p) ⟨hmaps p hp.1, hlt⟩
              linarith
            · exact hκ (hmaps p hp.1) hb heq
          · have := h1 b hb
            linarith [hp.2]
        have hsub : {y ∈ S | κ y < κ p} ⊂ {y ∈ S | κ y < κ b} := by
          refine ⟨fun y hy => ⟨hy.1, hy.2.trans hp.2⟩, fun h => ?_⟩
          exact lt_irrefl _ (h hp).2
        have hlt := Set.ncard_lt_ncard hsub (hS.subset fun y hy => hy.1)
        obtain ⟨j, hj⟩ := ih _ (hn ▸ hlt) p hp.1 rfl
        exact ⟨j + 1, by rw [iterate_succ_apply', hj, hnp]⟩
      · refine ⟨0, ?_⟩
        simp only [iterate_zero, id]
        refine hκ hmS hb (le_antisymm (hm b hb) ?_)
        by_contra hlt
        exact hne ⟨m, hmS, lt_of_not_ge hlt⟩
  obtain ⟨j₁, hj₁⟩ := h1 _ a ha rfl
  obtain ⟨j₂, hj₂⟩ := h2 _ b hb rfl
  exact ⟨j₂ + j₁, by rw [iterate_add_apply, hj₁, hj₂]⟩

end CFWPlan.Main.P6
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P6
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-- Stage data of the cutting-and-stacking construction for a finite Borel equivalence relation
`F`: a Borel bijection `σ` that is a single cycle on every `F`-class, and a Borel "last point"
map `l`, constant on classes. -/
structure CycleStage (F : Set (X × X)) (σ l : X → X) : Prop where
  ms : Measurable σ
  ml : Measurable l
  bij : Bijective σ
  memσ : ∀ x, (x, σ x) ∈ F
  meml : ∀ x, (x, l x) ∈ F
  cls : ∀ x y, (x, y) ∈ F → l x = l y ∧ ∃ j : ℕ, σ^[j] x = y

/-- **One step of cutting and stacking.** The `F`-blocks of a `G`-class are ordered by the key
`κ = embeddingReal X` of their last points; the last point of each block is linked to the first
point of the next block, cyclically, and the new last point is the last point of the `κ`-largest
block. -/
theorem cycle_step {F G : Set (X × X)} (hFeq : Equivalence fun x y => (x, y) ∈ F)
    (hFG : F ⊆ G) (hG : MeasurableSet G)
    (hGeq : Equivalence fun x y => (x, y) ∈ G) (hGfin : ∀ x, {y | (x, y) ∈ G}.Finite)
    {σ l : X → X} (h : CycleStage F σ l) :
    ∃ σ' l' : X → X, CycleStage G σ' l' ∧ (∀ x, x ≠ l x → σ' x = σ x) ∧
      (∀ x, x ≠ l x → x ≠ l' x) ∧ (∀ x, x ≠ σ (l x) → x ≠ σ' (l' x)) := by
  classical
  set κ := embeddingReal X with hκdef
  have hκm : Measurable κ := (measurableEmbedding_embeddingReal X).measurable
  have hκi : Injective κ := (measurableEmbedding_embeddingReal X).injective
  have hll : ∀ x, l (l x) = l x := fun x => ((h.cls x (l x) (h.meml x)).1).symm
  have hlσ : ∀ x, l (σ x) = l x := fun x => ((h.cls x (σ x) (h.memσ x)).1).symm
  have hlσi : ∀ i x, l (σ^[i] x) = l x := by
    intro i
    induction i with
    | zero => intro x; rfl
    | succ i ih => intro x; rw [iterate_succ_apply', hlσ, ih]
  set P₁ : Set (X × X) := {p | l p.2 = p.2 ∧ κ p.1 < κ p.2} with hP₁def
  set P₂ : Set (X × X) := {p | l p.2 = p.2} with hP₂def
  have hP₂ : MeasurableSet P₂ := measurableSet_eq_fun (h.ml.comp measurable_snd) measurable_snd
  have hP₁ : MeasurableSet P₁ :=
    hP₂.inter (measurableSet_lt (hκm.comp measurable_fst) (hκm.comp measurable_snd))
  have hfin₁ : ∀ x, {y | (x, y) ∈ G ∩ P₁}.Finite := fun x => (hGfin x).subset fun y hy => hy.1
  have hfin₂ : ∀ x, {y | (x, y) ∈ G ∩ P₂}.Finite := fun x => (hGfin x).subset fun y hy => hy.1
  obtain ⟨s₁, hs₁m, hs₁⟩ := exists_argmin (hG.inter hP₁) hfin₁ hκm
  obtain ⟨s₂, hs₂m, hs₂⟩ := exists_argmin (hG.inter hP₂) hfin₂ hκm
  obtain ⟨s₃, hs₃m, hs₃⟩ := exists_argmin (hG.inter hP₂) hfin₂ hκm.neg
  set C : Set X := {x | (x, s₁ x) ∈ G ∩ P₁} with hCdef
  have hC : MeasurableSet C := (hG.inter hP₁).preimage (measurable_id.prodMk hs₁m)
  set nx : X → X := fun x => if x ∈ C then s₁ x else s₂ x with hnxdef
  have hnxm : Measurable nx := Measurable.ite hC hs₁m hs₂m
  -- the set of last points of `F`-blocks in the `G`-class of `x`
  set S : X → Set X := fun x => {y | (x, y) ∈ G ∧ l y = y} with hSdef
  have hSfin : ∀ x, (S x).Finite := fun x => (hGfin x).subset fun y hy => hy.1
  have hlS : ∀ x, l x ∈ S x := fun x => ⟨hFG (h.meml x), hll x⟩
  have hSeq : ∀ a b, (a, b) ∈ G → S a = S b := by
    intro a b hab
    ext y
    exact ⟨fun hy => ⟨hGeq.trans (hGeq.symm hab) hy.1, hy.2⟩,
      fun hy => ⟨hGeq.trans hab hy.1, hy.2⟩⟩
  have hnxS : ∀ x, nx x ∈ S x := by
    intro x
    by_cases hx : x ∈ C
    · simp only [hnxdef, hx, if_true]
      exact ⟨hx.1, hx.2.1⟩
    · simp only [hnxdef, hx, if_false]
      have := (hs₂ x ⟨l x, hFG (h.meml x), hll x⟩).1
      exact ⟨this.1, this.2⟩
  have hnxspec : ∀ x, (κ x < κ (nx x) ∧ ∀ y ∈ S x, κ x < κ y → κ (nx x) ≤ κ y) ∨
      ((∀ y ∈ S x, κ y ≤ κ x) ∧ ∀ y ∈ S x, κ (nx x) ≤ κ y) := by
    intro x
    by_cases hx : x ∈ C
    · left
      simp only [hnxdef, hx, if_true]
      refine ⟨hx.2.2, fun y hy hxy => ?_⟩
      exact (hs₁ x ⟨s₁ x, hx⟩).2 y ⟨hy.1, hy.2, hxy⟩
    · right
      simp only [hnxdef, hx, if_false]
      refine ⟨fun y hy => ?_, fun y hy => (hs₂ x ⟨l x, hFG (h.meml x), hll x⟩).2 y hy⟩
      by_contra hlt
      exact hx (hs₁ x ⟨y, hy.1, hy.2, lt_of_not_ge hlt⟩).1
  -- restated relative to a fixed class
  have hmapsS : ∀ x, ∀ a ∈ S x, nx a ∈ S x := by
    intro x a ha
    rw [hSeq x a ha.1]
    exact hnxS a
  have hspecS : ∀ x, ∀ a ∈ S x, (κ a < κ (nx a) ∧ ∀ y ∈ S x, κ a < κ y → κ (nx a) ≤ κ y) ∨
      ((∀ y ∈ S x, κ y ≤ κ a) ∧ ∀ y ∈ S x, κ (nx a) ≤ κ y) := by
    intro x a ha
    rw [hSeq x a ha.1]
    exact hnxspec a
  have hreachS : ∀ x, ∀ a ∈ S x, ∀ b ∈ S x, ∃ j : ℕ, nx^[j] a = b := fun x =>
    next_reach (hSfin x) hκi.injOn (hmapsS x) (hspecS x)
  have hiterS : ∀ x j, ∀ a ∈ S x, nx^[j] a ∈ S x := by
    intro x j
    induction j with
    | zero => intro a ha; exact ha
    | succ j ih => intro a ha; rw [iterate_succ_apply']; exact hmapsS x _ (ih a ha)
  have hpred : ∀ x, ∀ b ∈ S x, ∃ p ∈ S x, nx p = b := by
    intro x b hb
    obtain ⟨j, hj⟩ := hreachS x (nx b) (hmapsS x b hb) b hb
    cases j with
    | zero => exact ⟨b, hb, hj⟩
    | succ j =>
      refine ⟨nx^[j] (nx b), hiterS x j _ (hmapsS x b hb), ?_⟩
      rw [← iterate_succ_apply' nx j]
      exact hj
  -- the new maps
  set σ' : X → X := fun x => if l x = x then σ (nx x) else σ x with hσ'def
  set l' : X → X := s₃ with hl'def
  have hσ'L : ∀ x, l x = x → σ' x = σ (nx x) := fun x hx => by simp only [hσ'def, hx, if_true]
  have hσ'N : ∀ x, l x ≠ x → σ' x = σ x := fun x hx => by simp only [hσ'def, hx, if_false]
  have hl'S : ∀ x, l' x ∈ S x := by
    intro x
    have := (hs₃ x ⟨l x, hFG (h.meml x), hll x⟩).1
    exact ⟨this.1, this.2⟩
  have hl'max : ∀ x, ∀ y ∈ S x, κ y ≤ κ (l' x) := by
    intro x y hy
    have := (hs₃ x ⟨l x, hFG (h.meml x), hll x⟩).2 y hy
    simp only [Pi.neg_apply] at this
    linarith
  have hσ'G : ∀ x, (x, σ' x) ∈ G := by
    intro x
    by_cases hx : l x = x
    · rw [hσ'L x hx]
      exact hGeq.trans (hnxS x).1 (hFG (h.memσ _))
    · rw [hσ'N x hx]
      exact hFG (h.memσ x)
  -- `σ'` agrees with `σ` along `σ`-paths that avoid last points
  have hpath : ∀ z j, (∀ i < j, l (σ^[i] z) ≠ σ^[i] z) → σ'^[j] z = σ^[j] z := by
    intro z j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [iterate_succ_apply', iterate_succ_apply', ih (fun i hi => hj i (by omega)),
        hσ'N _ (hj j (by omega))]
  -- reachability under `σ'`
  have hR_trans : ∀ a b c, (∃ j : ℕ, σ'^[j] a = b) → (∃ j : ℕ, σ'^[j] b = c) →
      ∃ j : ℕ, σ'^[j] a = c := by
    rintro a b c ⟨j, rfl⟩ ⟨k, rfl⟩
    exact ⟨k + j, iterate_add_apply _ _ _ _⟩
  have hR_last : ∀ x, ∃ j : ℕ, σ'^[j] x = l x := by
    intro x
    have hex : ∃ j, σ^[j] x = l x := (h.cls x (l x) (h.meml x)).2
    refine ⟨Nat.find hex, ?_⟩
    rw [hpath x _ (fun i hi => ?_)]
    · exact Nat.find_spec hex
    · rw [hlσi]
      exact fun he => Nat.find_min hex hi he.symm
  have hR_first : ∀ y, ∃ j : ℕ, σ'^[j] (σ (l y)) = y := by
    intro y
    have hmem : (σ (l y), y) ∈ F :=
      hFeq.trans (hFeq.symm (h.memσ (l y))) (hFeq.symm (h.meml y))
    have hex : ∃ j, σ^[j] (σ (l y)) = y := (h.cls _ _ hmem).2
    obtain ⟨j₀, hj₀, hmin⟩ : ∃ j₀, σ^[j₀] (σ (l y)) = y ∧ ∀ m < j₀, σ^[m] (σ (l y)) ≠ y :=
      ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
    refine ⟨j₀, ?_⟩
    rw [hpath _ _ (fun i hi => ?_)]
    · exact hj₀
    · rw [hlσi, hlσ, hll]
      intro he
      refine hmin (j₀ - i - 1) (by omega) ?_
      calc σ^[j₀ - i - 1] (σ (l y)) = σ^[j₀ - i] (l y) := by
            rw [← iterate_succ_apply]; congr 1; omega
        _ = σ^[j₀ - i] (σ^[i] (σ (l y))) := by rw [← he]
        _ = σ^[j₀] (σ (l y)) := by rw [← iterate_add_apply]; congr 1; omega
        _ = y := hj₀
  have hR_next : ∀ a, l a = a → ∃ j : ℕ, σ'^[j] a = nx a := by
    intro a ha
    obtain ⟨j, hj⟩ := hR_last (σ (nx a))
    refine ⟨j + 1, ?_⟩
    rw [iterate_succ_apply, hσ'L a ha, hj, hlσ]
    exact (hnxS a).2
  have hR_iter : ∀ x j, ∀ a ∈ S x, ∃ i : ℕ, σ'^[i] a = nx^[j] a := by
    intro x j
    induction j with
    | zero => intro a _; exact ⟨0, rfl⟩
    | succ j ih =>
      intro a ha
      refine hR_trans _ _ _ (ih a ha) ?_
      rw [iterate_succ_apply']
      exact hR_next _ (hiterS x j a ha).2
  refine ⟨σ', l', ⟨?_, hs₃m, ?_, hσ'G, fun x => (hl'S x).1, ?_⟩, ?_, ?_, ?_⟩
  · exact Measurable.ite (measurableSet_eq_fun h.ml measurable_id) (h.ms.comp hnxm) h.ms
  · refine ⟨fun a b hab => ?_, fun z => ?_⟩
    · have hab' : (a, b) ∈ G :=
        hGeq.trans (hσ'G a) (by rw [hab]; exact hGeq.symm (hσ'G b))
      by_cases ha : l a = a <;> by_cases hb : l b = b
      · rw [hσ'L a ha, hσ'L b hb] at hab
        exact next_injOn hκi.injOn (hspecS a) ⟨hGeq.refl a, ha⟩ ⟨hab', hb⟩ (h.bij.1 hab)
      · rw [hσ'L a ha, hσ'N b hb] at hab
        have := h.bij.1 hab
        exact absurd (by rw [← this]; exact (hnxS a).2) hb
      · rw [hσ'N a ha, hσ'L b hb] at hab
        have := h.bij.1 hab
        exact absurd (by rw [this]; exact (hnxS b).2) ha
      · rw [hσ'N a ha, hσ'N b hb] at hab
        exact h.bij.1 hab
    · obtain ⟨w, rfl⟩ := h.bij.2 z
      by_cases hw : l w = w
      · obtain ⟨p, hp, hpw⟩ := hpred w w ⟨hGeq.refl w, hw⟩
        exact ⟨p, by rw [hσ'L p hp.2, hpw]⟩
      · exact ⟨w, hσ'N w hw⟩
  · intro x y hxy
    have hSxy := hSeq x y hxy
    refine ⟨hκi (le_antisymm (hl'max y (l' x) (hSxy ▸ hl'S x))
      (hl'max x (l' y) (hSxy.symm ▸ hl'S y))), ?_⟩
    have hly : l y ∈ S x := ⟨hGeq.trans hxy (hFG (h.meml y)), hll y⟩
    obtain ⟨p, hp, hpy⟩ := hpred x (l y) hly
    obtain ⟨j, hj⟩ := hreachS x (l x) (hlS x) p hp
    refine hR_trans x (l x) y (hR_last x)
      (hR_trans (l x) p y ?_ (hR_trans p (σ (l y)) y ?_ (hR_first y)))
    · rw [← hj]
      exact hR_iter x j (l x) (hlS x)
    · exact ⟨1, by rw [iterate_one, hσ'L p hp.2, hpy]⟩
  · exact fun x hx => hσ'N x (Ne.symm hx)
  · intro x hx he
    apply hx
    calc x = l' x := he
      _ = l (l' x) := (hl'S x).2.symm
      _ = l x := by rw [← he]
  · intro x hx he
    have hw : x = σ (nx (l' x)) := he.trans (hσ'L _ (hl'S x).2)
    have hlx : l x = nx (l' x) := by
      calc l x = l (σ (nx (l' x))) := congrArg l hw
        _ = nx (l' x) := by rw [hlσ, (hnxS _).2]
    apply hx
    rw [hlx]
    exact hw

/-- **Nested cycles (D1).** For finite Borel equivalence relations `F 0 = Δ ⊆ F 1 ⊆ …` there are
Borel bijections `σ k`, each a single cycle on every `F k`-class, and Borel "last point" maps,
such that `σ (k+1)` agrees with `σ k` except at last points, and "not last" / "not first"
(`first = σ (last x)`) persist. *Proof (cutting and stacking):* recursion on `k`; an
`F (k+1)`-class is a finite union of `F k`-blocks, ordered by `ι (first of block)`
(`embeddingReal`); link `last` of each block to `first` of the next, cyclically; Borel by the
argmin-over-finite-classes technique of `exists_selector`. *Size:* 280. -/
theorem exists_cycle_sequence {F : ℕ → Set (X × X)} (hmono : Monotone F)
    (hF : ∀ n, MeasurableSet (F n) ∧ Equivalence (fun x y => (x, y) ∈ F n) ∧
      ∀ x, {y | (x, y) ∈ F n}.Finite)
    (hF0 : ∀ x y, (x, y) ∈ F 0 → x = y) :
    ∃ σ last : ℕ → X → X, (∀ k, Measurable (σ k) ∧ Measurable (last k) ∧ Bijective (σ k)) ∧
      (∀ k x, (x, σ k x) ∈ F k ∧ (x, last k x) ∈ F k) ∧
      (∀ k x y, (x, y) ∈ F k → last k x = last k y ∧ ∃ j : ℕ, (σ k)^[j] x = y) ∧
      (∀ k x, x ≠ last k x → σ (k + 1) x = σ k x) ∧
      (∀ k x, x ≠ last k x → x ≠ last (k + 1) x) ∧
      (∀ k x, x ≠ σ k (last k x) → x ≠ σ (k + 1) (last (k + 1) x)) := by
  have h0 : CycleStage (F 0) id id :=
    { ms := measurable_id, ml := measurable_id, bij := bijective_id,
      memσ := fun x => (hF 0).2.1.refl x, meml := fun x => (hF 0).2.1.refl x,
      cls := fun x y hxy => by obtain rfl := hF0 x y hxy; exact ⟨rfl, 0, rfl⟩ }
  have hstep : ∀ k (p : {p : (X → X) × (X → X) // CycleStage (F k) p.1 p.2}),
      ∃ q : (X → X) × (X → X), CycleStage (F (k + 1)) q.1 q.2 ∧
        (∀ x, x ≠ p.1.2 x → q.1 x = p.1.1 x) ∧ (∀ x, x ≠ p.1.2 x → x ≠ q.2 x) ∧
        (∀ x, x ≠ p.1.1 (p.1.2 x) → x ≠ q.1 (q.2 x)) := by
    intro k p
    obtain ⟨σ', l', h1, h2, h3, h4⟩ := cycle_step (hF k).2.1 (hmono (Nat.le_succ k))
      (hF (k + 1)).1 (hF (k + 1)).2.1 (hF (k + 1)).2.2 p.2
    exact ⟨(σ', l'), h1, h2, h3, h4⟩
  choose g hg using hstep
  let seq : (k : ℕ) → {p : (X → X) × (X → X) // CycleStage (F k) p.1 p.2} := fun k =>
    Nat.rec (motive := fun k => {p : (X → X) × (X → X) // CycleStage (F k) p.1 p.2})
      ⟨(id, id), h0⟩ (fun k p => ⟨g k p, (hg k p).1⟩) k
  have hseq : ∀ k, (seq (k + 1)).1 = g k (seq k) := fun k => rfl
  refine ⟨fun k => (seq k).1.1, fun k => (seq k).1.2,
    fun k => ⟨(seq k).2.ms, (seq k).2.ml, (seq k).2.bij⟩,
    fun k x => ⟨(seq k).2.memσ x, (seq k).2.meml x⟩, fun k => (seq k).2.cls,
    fun k x hx => ?_, fun k x hx => ?_, fun k x hx => ?_⟩
  · simp only [hseq]
    exact (hg k (seq k)).2.1 x hx
  · simp only [hseq]
    exact (hg k (seq k)).2.2.1 x hx
  · simp only [hseq]
    exact (hg k (seq k)).2.2.2 x hx

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
/-- **The limit successor map (D2a).** From D1: `Lm = {x | ∀ k, x = last k x}` ("eventually
last", at most one per `E`-class), `Fm = {x | ∀ k, x = σ k (last k x)}` ("first"), and
`τ x = σ_{k(x)} x` for the least `k(x)` with `x ≠ last k x`. `τ` is a Borel injection on `Lmᶜ`
onto `Fmᶜ`, moves points inside their class, and the `τ`-chains connect every pair of
`E`-equivalent points, where `E = ⋃ F k`. *Size:* 220. -/
theorem exists_successor_map {F : ℕ → Set (X × X)} (hmono : Monotone F)
    (hF : ∀ n, MeasurableSet (F n) ∧ Equivalence (fun x y => (x, y) ∈ F n) ∧
      ∀ x, {y | (x, y) ∈ F n}.Finite)
    (hF0 : ∀ x y, (x, y) ∈ F 0 → x = y) :
    ∃ (Lm Fm : Set X) (τ : X → X), MeasurableSet Lm ∧ MeasurableSet Fm ∧ Measurable τ ∧
      InjOn τ Lmᶜ ∧ τ '' Lmᶜ = Fmᶜ ∧ (∀ x ∉ Lm, ∃ n, (x, τ x) ∈ F n) ∧
      (∀ x y, (∃ n, (x, y) ∈ F n) → x ∈ Lm → y ∈ Lm → x = y) ∧
      (∀ x y, (∃ n, (x, y) ∈ F n) → x ∈ Fm → y ∈ Fm → x = y) ∧
      ∀ x y, (∃ n, (x, y) ∈ F n) → ∃ j : ℕ,
        (τ^[j] x = y ∧ ∀ i < j, τ^[i] x ∉ Lm) ∨ (τ^[j] y = x ∧ ∀ i < j, τ^[i] y ∉ Lm) := by
  classical
  obtain ⟨σ, last, hm, hmem, hcls, h4, h5, h6⟩ :=
    CFWPlan.Main.P6.exists_cycle_sequence hmono hF hF0
  set Lm : Set X := {x | ∀ k, x = last k x} with hLmdef
  set Fm : Set X := {x | ∀ k, x = σ k (last k x)} with hFmdef
  have hLm : MeasurableSet Lm := by
    have : Lm = ⋂ k, {x | x = last k x} := by ext; simp [Lm]
    rw [this]
    exact MeasurableSet.iInter fun k => measurableSet_eq_fun measurable_id (hm k).2.1
  have hFm : MeasurableSet Fm := by
    have : Fm = ⋂ k, {x | x = σ k (last k x)} := by ext; simp [Fm]
    rw [this]
    exact MeasurableSet.iInter fun k =>
      measurableSet_eq_fun measurable_id ((hm k).1.comp (hm k).2.1)
  have hlσ : ∀ k x, last k (σ k x) = last k x := fun k x =>
    ((hcls k x (σ k x) (hmem k x).1).1).symm
  have hlσi : ∀ k i x, last k ((σ k)^[i] x) = last k x := by
    intro k i
    induction i with
    | zero => intro x; rfl
    | succ i ih => intro x; rw [iterate_succ_apply', hlσ, ih]
  have hpers : ∀ k x, x ≠ last k x → ∀ K, k ≤ K → x ≠ last K x ∧ σ K x = σ k x := by
    intro k x hx K hK
    induction K, hK using Nat.le_induction with
    | base => exact ⟨hx, rfl⟩
    | succ K hK ih => exact ⟨h5 K x ih.1, (h4 K x ih.1).trans ih.2⟩
  have hnotLm : ∀ x, x ∉ Lm ↔ ∃ K, x ≠ last K x := by
    intro x
    simp only [hLmdef, mem_ofPred_eq, not_forall]
  have hex : ∀ x, ∃ k, x ≠ last k x ∨ x ∈ Lm := by
    intro x
    by_cases hx : x ∈ Lm
    · exact ⟨0, Or.inr hx⟩
    · obtain ⟨k, hk⟩ := (hnotLm x).1 hx
      exact ⟨k, Or.inl hk⟩
  set τ : X → X := fun x => σ (Nat.find (hex x)) x with hτdef
  have hτm : Measurable τ :=
    Measurable.find (p := fun k x => x ≠ last k x ∨ x ∈ Lm) (fun k => (hm k).1)
      (fun k => (measurableSet_eq_fun measurable_id (hm k).2.1).compl.union hLm) hex
  have hτ : ∀ x K, x ≠ last K x → τ x = σ K x := by
    intro x K hK
    have hx : x ∉ Lm := fun h => hK (h K)
    have hspec := (Nat.find_spec (hex x)).resolve_right hx
    have hle := Nat.find_min' (hex x) (Or.inl hK)
    exact ((hpers _ x hspec K hle).2).symm
  -- paths inside an `F n`-class that avoid the last point
  have hpath : ∀ n z a, (∀ i < a, (σ n)^[i] z ≠ last n z) →
      (∀ i ≤ a, τ^[i] z = (σ n)^[i] z) ∧ ∀ i < a, τ^[i] z ∉ Lm := by
    intro n z a ha
    have h1 : ∀ i ≤ a, τ^[i] z = (σ n)^[i] z := by
      intro i
      induction i with
      | zero => intro _; rfl
      | succ i ih =>
        intro hi
        have hne : (σ n)^[i] z ≠ last n ((σ n)^[i] z) := by
          rw [hlσi]; exact ha i (by omega)
        rw [iterate_succ_apply', iterate_succ_apply', ih (by omega), hτ _ n hne]
    refine ⟨h1, fun i hi hL => ?_⟩
    rw [h1 i hi.le] at hL
    exact ha i hi (by rw [← hlσi n i z]; exact hL n)
  refine ⟨Lm, Fm, τ, hLm, hFm, hτm, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx x' hx' hxx'
    obtain ⟨K, hK⟩ := (hnotLm x).1 hx
    obtain ⟨K', hK'⟩ := (hnotLm x').1 hx'
    rw [hτ x (max K K') (hpers K x hK _ (le_max_left _ _)).1,
      hτ x' (max K K') (hpers K' x' hK' _ (le_max_right _ _)).1] at hxx'
    exact (hm _).2.2.1 hxx'
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ hy
      obtain ⟨K, hK⟩ := (hnotLm x).1 hx
      rw [hτ x K hK] at hy
      have := hy K
      rw [hlσ] at this
      exact hK ((hm K).2.2.1 this.symm).symm
    · intro hy
      simp only [hFmdef, mem_compl_iff, mem_ofPred_eq, not_forall] at hy
      obtain ⟨k, hk⟩ := hy
      obtain ⟨x, rfl⟩ := (hm k).2.2.2 y
      have hxl : x ≠ last k x := by
        intro he
        apply hk
        rw [hlσ, ← he]
      exact ⟨x, (hnotLm x).2 ⟨k, hxl⟩, hτ x k hxl⟩
  · intro x hx
    obtain ⟨K, hK⟩ := (hnotLm x).1 hx
    exact ⟨K, by rw [hτ x K hK]; exact (hmem K x).1⟩
  · rintro x y ⟨n, hn⟩ hx hy
    rw [hx n, hy n]
    exact (hcls n x y hn).1
  · rintro x y ⟨n, hn⟩ hx hy
    rw [hx n, hy n, (hcls n x y hn).1]
  · rintro x y ⟨n, hn⟩
    have hz : ∀ z, ∃ a, (σ n)^[a] z = last n z := fun z => (hcls n z _ (hmem n z).2).2
    obtain ⟨a, ha, hamin⟩ : ∃ a, (σ n)^[a] x = last n x ∧ ∀ i < a, (σ n)^[i] x ≠ last n x :=
      ⟨Nat.find (hz x), Nat.find_spec (hz x), fun i hi => Nat.find_min (hz x) hi⟩
    obtain ⟨b, hb, hbmin⟩ : ∃ b, (σ n)^[b] y = last n y ∧ ∀ i < b, (σ n)^[i] y ≠ last n y :=
      ⟨Nat.find (hz y), Nat.find_spec (hz y), fun i hi => Nat.find_min (hz y) hi⟩
    have hlxy := (hcls n x y hn).1
    rcases le_total b a with hba | hab
    · refine ⟨a - b, Or.inl ⟨?_, fun i hi => (hpath n x a hamin).2 i (by omega)⟩⟩
      rw [(hpath n x a hamin).1 _ (by omega)]
      apply ((hm n).2.2.1.iterate b)
      rw [← iterate_add_apply, Nat.add_sub_cancel' hba, ha, hb, hlxy]
    · refine ⟨b - a, Or.inr ⟨?_, fun i hi => (hpath n y b hbmin).2 i (by omega)⟩⟩
      rw [(hpath n y b hbmin).1 _ (by omega)]
      apply ((hm n).2.2.1.iterate a)
      rw [← iterate_add_apply, Nat.add_sub_cancel' hab, ha, hb, hlxy]

end CFWPlan.Main.P6
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias exists_successor_map := CFWPlan.Main.P6.exists_successor_map

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
/-- Symmetric form of the data of a successor map: `α` is injective off `A` ("last points"), with
inverse `β` off `B` ("first points"); `A` and `B` meet every `E`-class at most once, and any two
`E`-equivalent points are joined by an `α`-chain avoiding `A`. The data are symmetric under
`(A, B, α, β) ↦ (B, A, β, α)` (`ChainData.symm`). -/
structure ChainData (E : Set (X × X)) (A B : Set X) (α β : X → X) : Prop where
  equiv : Equivalence fun x y => (x, y) ∈ E
  fwd : ∀ x ∉ A, β (α x) = x ∧ α x ∉ B ∧ (x, α x) ∈ E
  bwd : ∀ y ∉ B, α (β y) = y ∧ β y ∉ A ∧ (y, β y) ∈ E
  uA : ∀ x y, (x, y) ∈ E → x ∈ A → y ∈ A → x = y
  uB : ∀ x y, (x, y) ∈ E → x ∈ B → y ∈ B → x = y
  chain : ∀ x y, (x, y) ∈ E → ∃ j : ℕ,
    (α^[j] x = y ∧ ∀ i < j, α^[i] x ∉ A) ∨ (α^[j] y = x ∧ ∀ i < j, α^[i] y ∉ A)

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
theorem fwd_mem (h : ChainData E A B α β) {x : X} {n : ℕ} (hn : ∀ i < n, α^[i] x ∉ A) :
    (x, α^[n] x) ∈ E := by
  induction n with
  | zero => exact h.equiv.refl x
  | succ n ih =>
    rw [iterate_succ_apply']
    exact h.equiv.trans (ih fun i hi => hn i (by omega)) (h.fwd _ (hn n (by omega))).2.2

theorem iter_back (h : ChainData E A B α β) {x : X} {j : ℕ} (hj : ∀ i < j, α^[i] x ∉ A) :
    (∀ i ≤ j, β^[i] (α^[j] x) = α^[j - i] x) ∧ ∀ i < j, β^[i] (α^[j] x) ∉ B := by
  have h1 : ∀ i ≤ j, β^[i] (α^[j] x) = α^[j - i] x := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      rw [iterate_succ_apply', ih (by omega)]
      have : j - i = (j - (i + 1)) + 1 := by omega
      rw [this, iterate_succ_apply']
      exact (h.fwd _ (hj _ (by omega))).1
  refine ⟨h1, fun i hi => ?_⟩
  rw [h1 i hi.le]
  have : j - i = (j - i - 1) + 1 := by omega
  rw [this, iterate_succ_apply']
  exact (h.fwd _ (hj _ (by omega))).2.1

theorem back_self (h : ChainData E A B α β) {x : X} {j : ℕ} (hj : ∀ i < j, α^[i] x ∉ A) :
    β^[j] (α^[j] x) = x := by
  rw [(h.iter_back hj).1 j le_rfl, Nat.sub_self, iterate_zero, id]

theorem symm (h : ChainData E A B α β) : ChainData E B A β α where
  equiv := h.equiv
  fwd := h.bwd
  bwd := h.fwd
  uA := h.uB
  uB := h.uA
  chain := by
    intro x y hxy
    obtain ⟨j, ⟨hj, hjA⟩ | ⟨hj, hjA⟩⟩ := h.chain x y hxy
    · refine ⟨j, Or.inr ⟨?_, ?_⟩⟩
      · rw [← hj]; exact h.back_self hjA
      · rw [← hj]; exact (h.iter_back hjA).2
    · refine ⟨j, Or.inl ⟨?_, ?_⟩⟩
      · rw [← hj]; exact h.back_self hjA
      · rw [← hj]; exact (h.iter_back hjA).2

theorem hitB_iff (h : ChainData E A B α β) (x : X) :
    (∃ n, β^[n] x ∈ B) ↔ ∃ f ∈ B, (x, f) ∈ E := by
  classical
  constructor
  · intro hex
    exact ⟨_, Nat.find_spec hex, h.symm.fwd_mem fun i hi => Nat.find_min hex hi⟩
  · rintro ⟨f, hf, hxf⟩
    obtain ⟨j, ⟨hj, hjA⟩ | ⟨hj, hjA⟩⟩ := h.chain x f hxf
    · cases j with
      | zero => exact ⟨0, by rw [iterate_zero, id]; rw [iterate_zero, id] at hj; rw [hj]; exact hf⟩
      | succ j =>
        rw [iterate_succ_apply'] at hj
        exact absurd (hj ▸ hf) (h.fwd _ (hjA j (by omega))).2.1
    · refine ⟨j, ?_⟩
      rw [← hj, h.back_self hjA]
      exact hf

theorem hitB_congr (h : ChainData E A B α β) {x y : X} (hxy : (x, y) ∈ E) :
    (∃ n, β^[n] x ∈ B) ↔ ∃ n, β^[n] y ∈ B := by
  rw [h.hitB_iff, h.hitB_iff]
  constructor
  · rintro ⟨f, hf, hxf⟩
    exact ⟨f, hf, h.equiv.trans (h.equiv.symm hxy) hxf⟩
  · rintro ⟨f, hf, hyf⟩
    exact ⟨f, hf, h.equiv.trans hxy hyf⟩

/-- Every point of the class of a first point `f` is `α^[n] f` along a chain avoiding `A`. -/
theorem pos_of_B (h : ChainData E A B α β) {f x : X} (hf : f ∈ B) (hfx : (f, x) ∈ E) :
    ∃ n, α^[n] f = x ∧ ∀ i < n, α^[i] f ∉ A := by
  obtain ⟨j, ⟨hj, hjA⟩ | ⟨hj, hjA⟩⟩ := h.chain f x hfx
  · exact ⟨j, hj, hjA⟩
  · cases j with
    | zero => exact ⟨0, hj.symm, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    | succ j =>
      rw [iterate_succ_apply'] at hj
      exact absurd (hj ▸ hf) (h.fwd _ (hjA j (by omega))).2.1

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
/-- `T` permutes the `E`-invariant set `S`, moves points inside their classes, and its forward
orbits connect any two equivalent points of `S`. -/
def GoodOn (E : Set (X × X)) (S : Set X) (T : X → X) : Prop :=
  (∀ x ∈ S, (x, T x) ∈ E) ∧ InjOn T S ∧ (∀ y ∈ S, ∃ x ∈ S, T x = y) ∧
    ∀ x ∈ S, ∀ y ∈ S, (x, y) ∈ E → ∃ j : ℕ, T^[j] x = y ∨ T^[j] y = x

theorem iterate_eq_of_eqOn {S : Set X} {T T₁ : X → X} (hT : ∀ z ∈ S, T z = T₁ z)
    (hmaps : ∀ z ∈ S, T₁ z ∈ S) : ∀ j : ℕ, ∀ z ∈ S, T^[j] z = T₁^[j] z ∧ T₁^[j] z ∈ S := by
  intro j
  induction j with
  | zero => intro z hz; exact ⟨rfl, hz⟩
  | succ j ih =>
    intro z hz
    rw [iterate_succ_apply', iterate_succ_apply', (ih z hz).1, hT _ (ih z hz).2]
    exact ⟨rfl, hmaps _ (ih z hz).2⟩

/-- Gluing two good maps along an invariant set. -/
theorem goodOn_piecewise {E : Set (X × X)} (heq : Equivalence fun x y => (x, y) ∈ E)
    {S P : Set X} [DecidablePred (· ∈ P)] (hS : ∀ x y, (x, y) ∈ E → x ∈ S → y ∈ S)
    (hP : ∀ x y, (x, y) ∈ E → x ∈ P → y ∈ P) {T₁ T₂ : X → X}
    (h₁ : GoodOn E (S ∩ P) T₁) (h₂ : GoodOn E (S ∩ Pᶜ) T₂) :
    GoodOn E S (P.piecewise T₁ T₂) := by
  have hPc : ∀ x y, (x, y) ∈ E → x ∉ P → y ∉ P := fun x y hxy hx hy =>
    hx (hP y x (heq.symm hxy) hy)
  have hm₁ : ∀ z ∈ S ∩ P, T₁ z ∈ S ∩ P := fun z hz =>
    ⟨hS _ _ (h₁.1 z hz) hz.1, hP _ _ (h₁.1 z hz) hz.2⟩
  have hm₂ : ∀ z ∈ S ∩ Pᶜ, T₂ z ∈ S ∩ Pᶜ := fun z hz =>
    ⟨hS _ _ (h₂.1 z hz) hz.1, hPc _ _ (h₂.1 z hz) hz.2⟩
  have it₁ := iterate_eq_of_eqOn (S := S ∩ P) (T := P.piecewise T₁ T₂)
    (fun z hz => piecewise_eq_of_mem _ _ _ hz.2) hm₁
  have it₂ := iterate_eq_of_eqOn (S := S ∩ Pᶜ) (T := P.piecewise T₁ T₂)
    (fun z hz => piecewise_eq_of_notMem _ _ _ hz.2) hm₂
  refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun y hy => ?_, fun x hx y hy hxy => ?_⟩
  · by_cases hxP : x ∈ P
    · rw [piecewise_eq_of_mem _ _ _ hxP]; exact h₁.1 x ⟨hx, hxP⟩
    · rw [piecewise_eq_of_notMem _ _ _ hxP]; exact h₂.1 x ⟨hx, hxP⟩
  · by_cases hxP : x ∈ P <;> by_cases hyP : y ∈ P
    · rw [piecewise_eq_of_mem _ _ _ hxP, piecewise_eq_of_mem _ _ _ hyP] at hxy
      exact h₁.2.1 ⟨hx, hxP⟩ ⟨hy, hyP⟩ hxy
    · rw [piecewise_eq_of_mem _ _ _ hxP, piecewise_eq_of_notMem _ _ _ hyP] at hxy
      exact absurd (hxy ▸ (hm₁ x ⟨hx, hxP⟩).2) (hm₂ y ⟨hy, hyP⟩).2
    · rw [piecewise_eq_of_notMem _ _ _ hxP, piecewise_eq_of_mem _ _ _ hyP] at hxy
      exact absurd (hxy ▸ (hm₂ x ⟨hx, hxP⟩).2) (not_not.2 (hm₁ y ⟨hy, hyP⟩).2)
    · rw [piecewise_eq_of_notMem _ _ _ hxP, piecewise_eq_of_notMem _ _ _ hyP] at hxy
      exact h₂.2.1 ⟨hx, hxP⟩ ⟨hy, hyP⟩ hxy
  · by_cases hyP : y ∈ P
    · obtain ⟨x, hx, hxy⟩ := h₁.2.2.1 y ⟨hy, hyP⟩
      exact ⟨x, hx.1, by rw [piecewise_eq_of_mem _ _ _ hx.2]; exact hxy⟩
    · obtain ⟨x, hx, hxy⟩ := h₂.2.2.1 y ⟨hy, hyP⟩
      exact ⟨x, hx.1, by rw [piecewise_eq_of_notMem _ _ _ hx.2]; exact hxy⟩
  · by_cases hxP : x ∈ P
    · have hyP := hP x y hxy hxP
      obtain ⟨j, hj⟩ := h₁.2.2.2 x ⟨hx, hxP⟩ y ⟨hy, hyP⟩ hxy
      refine ⟨j, ?_⟩
      rw [(it₁ j x ⟨hx, hxP⟩).1, (it₁ j y ⟨hy, hyP⟩).1]
      exact hj
    · have hyP := hPc x y hxy hxP
      obtain ⟨j, hj⟩ := h₂.2.2.2 x ⟨hx, hxP⟩ y ⟨hy, hyP⟩ hxy
      refine ⟨j, ?_⟩
      rw [(it₂ j x ⟨hx, hxP⟩).1, (it₂ j y ⟨hy, hyP⟩).1]
      exact hj

/-- The permutation `n ↦ n + 1` of `ℤ`, transported to `ℕ`: a single `ℤ`-orbit (the zig-zag). -/
def zz (n : ℕ) : ℕ := Equiv.intEquivNat (Equiv.intEquivNat.symm n + 1)

theorem zz_iterate (j n : ℕ) :
    zz^[j] n = Equiv.intEquivNat (Equiv.intEquivNat.symm n + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iterate_succ_apply', ih, zz, Equiv.symm_apply_apply]
    congr 1
    push_cast
    ring

theorem zz_bijective : Bijective zz :=
  Equiv.intEquivNat.bijective.comp
    ((Equiv.addRight (1 : ℤ)).bijective.comp Equiv.intEquivNat.symm.bijective)

theorem zz_reach (a b : ℕ) : ∃ j : ℕ, zz^[j] a = b ∨ zz^[j] b = a := by
  rcases le_total 0 (Equiv.intEquivNat.symm b - Equiv.intEquivNat.symm a) with hd | hd
  · refine ⟨(Equiv.intEquivNat.symm b - Equiv.intEquivNat.symm a).toNat, Or.inl ?_⟩
    rw [zz_iterate, Int.toNat_of_nonneg hd, add_sub_cancel, Equiv.apply_symm_apply]
  · refine ⟨(Equiv.intEquivNat.symm a - Equiv.intEquivNat.symm b).toNat, Or.inr ?_⟩
    rw [zz_iterate, Int.toNat_of_nonneg (by omega), add_sub_cancel, Equiv.apply_symm_apply]

theorem measurableSet_hit [MeasurableSpace X] {γ : X → X} (hγ : Measurable γ) {S : Set X}
    (hS : MeasurableSet S) : MeasurableSet {x | ∃ n, γ^[n] x ∈ S} := by
  have : {x | ∃ n, γ^[n] x ∈ S} = ⋃ n, (γ^[n]) ⁻¹' S := by ext; simp
  rw [this]
  exact MeasurableSet.iUnion fun n => (hγ.iterate n) hS

/-- **Classes with a first point and no last point (type `ω`)**: the zig-zag
`c₀ → c₂ → c₄ → ⋯`, `⋯ → c₃ → c₁ → c₀` along the chain `cₙ = α^[n] f`, in the form
`T (cₙ) = c_{zz n}` with the Borel position `n = ` first hitting time of `B` under `β`. -/
theorem omega_part [MeasurableSpace X] {E : Set (X × X)} {A B : Set X} {α β : X → X}
    (h : ChainData E A B α β) (hB : MeasurableSet B) (hα : Measurable α) (hβ : Measurable β) :
    ∃ T : X → X, Measurable T ∧
      GoodOn E {x | (∃ n, β^[n] x ∈ B) ∧ ¬ ∃ n, α^[n] x ∈ A} T := by
  classical
  have hSB := measurableSet_hit hβ hB
  have hex : ∀ x, ∃ n, β^[n] x ∈ B ∨ x ∉ {x | ∃ n, β^[n] x ∈ B} := by
    intro x
    by_cases hx : ∃ n, β^[n] x ∈ B
    · obtain ⟨n, hn⟩ := hx
      exact ⟨n, Or.inl hn⟩
    · exact ⟨0, Or.inr hx⟩
  set T : X → X := fun x => α^[zz (Nat.find (hex x))] (β^[Nat.find (hex x)] x) with hTdef
  have hTm : Measurable T :=
    Measurable.find (p := fun n x => β^[n] x ∈ B ∨ x ∉ {x | ∃ n, β^[n] x ∈ B})
      (f := fun n x => α^[zz n] (β^[n] x)) (fun n => (hα.iterate _).comp (hβ.iterate n))
      (fun n => ((hβ.iterate n) hB).union hSB.compl) hex
  set Ω : Set X := {x | (∃ n, β^[n] x ∈ B) ∧ ¬ ∃ n, α^[n] x ∈ A} with hΩdef
  have hΩinv : ∀ x y, (x, y) ∈ E → x ∈ Ω → y ∈ Ω := by
    intro x y hxy hx
    exact ⟨(h.hitB_congr hxy).1 hx.1, fun hy => hx.2 ((h.symm.hitB_congr hxy).2 hy)⟩
  have key : ∀ x ∈ Ω, ∃ f ∈ B, (x, f) ∈ E ∧ ∀ y, (f, y) ∈ E → y ∉ A := by
    intro x hx
    obtain ⟨f, hf, hxf⟩ := (h.hitB_iff x).1 hx.1
    refine ⟨f, hf, hxf, fun y hfy hy => hx.2 ?_⟩
    exact (h.symm.hitB_iff x).2 ⟨y, hy, h.equiv.trans hxf hfy⟩
  have struct : ∀ f ∈ B, (∀ y, (f, y) ∈ E → y ∉ A) →
      (∀ n, (f, α^[n] f) ∈ E) ∧ (∀ n, T (α^[n] f) = α^[zz n] f) ∧
      (∀ a b, α^[a] f = α^[b] f → a = b) ∧ (∀ x, (f, x) ∈ E → ∃ n, α^[n] f = x) := by
    intro f hf hnoA
    have hcE : ∀ n, (f, α^[n] f) ∈ E := by
      intro n
      induction n with
      | zero => exact h.equiv.refl f
      | succ n ih =>
        rw [iterate_succ_apply']
        exact h.equiv.trans ih (h.fwd _ (hnoA _ ih)).2.2
    have hcA : ∀ n, α^[n] f ∉ A := fun n => hnoA _ (hcE n)
    have hpos : ∀ n, Nat.find (hex (α^[n] f)) = n := by
      intro n
      have hb := h.iter_back (x := f) (j := n) (fun i _ => hcA i)
      have hn : β^[n] (α^[n] f) ∈ B := by rw [h.back_self (fun i _ => hcA i)]; exact hf
      rw [Nat.find_eq_iff]
      refine ⟨Or.inl hn, fun k hk hk' => ?_⟩
      rcases hk' with hk' | hk'
      · exact hb.2 k hk hk'
      · exact hk' ⟨n, hn⟩
    have hT : ∀ n, T (α^[n] f) = α^[zz n] f := by
      intro n
      simp only [hTdef, hpos]
      rw [h.back_self (fun i _ => hcA i)]
    refine ⟨hcE, hT, fun a b hab => ?_, fun x hfx => ?_⟩
    · rw [← hpos a, ← hpos b, hab]
    · obtain ⟨n, hn, -⟩ := h.pos_of_B hf hfx
      exact ⟨n, hn⟩
  have hTj : ∀ f ∈ B, (∀ y, (f, y) ∈ E → y ∉ A) →
      ∀ j n, T^[j] (α^[n] f) = α^[zz^[j] n] f := by
    intro f hf hnoA j
    induction j with
    | zero => intro n; rfl
    | succ j ih =>
      intro n
      rw [iterate_succ_apply', ih, (struct f hf hnoA).2.1, iterate_succ_apply']
  have hTE : ∀ x ∈ Ω, (x, T x) ∈ E := by
    intro x hx
    obtain ⟨f, hf, hxf, hnoA⟩ := key x hx
    obtain ⟨hcE, hT, -, hcls⟩ := struct f hf hnoA
    obtain ⟨n, rfl⟩ := hcls x (h.equiv.symm hxf)
    rw [hT]
    exact h.equiv.trans hxf (hcE _)
  refine ⟨T, hTm, hTE, fun x hx y hy hxy => ?_, fun y hy => ?_, fun x hx y hy hxy => ?_⟩
  · obtain ⟨f, hf, hxf, hnoA⟩ := key x hx
    obtain ⟨hcE, hT, hinj, hcls⟩ := struct f hf hnoA
    obtain ⟨a, rfl⟩ := hcls x (h.equiv.symm hxf)
    have hfy : (f, y) ∈ E := by
      refine h.equiv.trans (hcE (zz a)) ?_
      rw [← hT, hxy]
      exact h.equiv.symm (hTE y hy)
    obtain ⟨b, rfl⟩ := hcls y hfy
    rw [hT, hT] at hxy
    rw [zz_bijective.1 (hinj _ _ hxy)]
  · obtain ⟨f, hf, hyf, hnoA⟩ := key y hy
    obtain ⟨hcE, hT, -, hcls⟩ := struct f hf hnoA
    obtain ⟨b, rfl⟩ := hcls y (h.equiv.symm hyf)
    obtain ⟨a, rfl⟩ := zz_bijective.2 b
    exact ⟨α^[a] f, hΩinv _ _ (h.equiv.trans hyf (hcE a)) hy, hT a⟩
  · obtain ⟨f, hf, hxf, hnoA⟩ := key x hx
    obtain ⟨-, -, -, hcls⟩ := struct f hf hnoA
    obtain ⟨a, rfl⟩ := hcls x (h.equiv.symm hxf)
    obtain ⟨b, rfl⟩ := hcls y (h.equiv.trans (h.equiv.symm hxf) hxy)
    obtain ⟨j, hj | hj⟩ := zz_reach a b
    · exact ⟨j, Or.inl (by rw [hTj f hf hnoA, hj])⟩
    · exact ⟨j, Or.inr (by rw [hTj f hf hnoA, hj])⟩

/-- **Finite classes and classes of type `ℤ`**: `T = α` off `A`, and `T` sends the last point of a
finite class to its first point (`β` iterated up to the first hitting time of `B`). -/
theorem fin_part [MeasurableSpace X] {E : Set (X × X)} {A B : Set X} {α β : X → X}
    (h : ChainData E A B α β) (hA : MeasurableSet A) (hB : MeasurableSet B) (hα : Measurable α)
    (hβ : Measurable β) :
    ∃ T : X → X, Measurable T ∧
      GoodOn E {x | (∃ n, β^[n] x ∈ B) ↔ ∃ n, α^[n] x ∈ A} T := by
  classical
  have hSB := measurableSet_hit hβ hB
  have hex : ∀ x, ∃ n, β^[n] x ∈ B ∨ x ∉ {x | ∃ n, β^[n] x ∈ B} := by
    intro x
    by_cases hx : ∃ n, β^[n] x ∈ B
    · obtain ⟨n, hn⟩ := hx
      exact ⟨n, Or.inl hn⟩
    · exact ⟨0, Or.inr hx⟩
  set T : X → X := fun x => if x ∈ A then β^[Nat.find (hex x)] x else α x with hTdef
  have hTm : Measurable T := by
    refine Measurable.ite hA ?_ hα
    exact Measurable.find (p := fun n x => β^[n] x ∈ B ∨ x ∉ {x | ∃ n, β^[n] x ∈ B})
      (f := fun n x => β^[n] x) (fun n => hβ.iterate n)
      (fun n => ((hβ.iterate n) hB).union hSB.compl) hex
  set Z : Set X := {x | (∃ n, β^[n] x ∈ B) ↔ ∃ n, α^[n] x ∈ A} with hZdef
  have hZinv : ∀ x y, (x, y) ∈ E → x ∈ Z → y ∈ Z := by
    intro x y hxy hx
    show _ ↔ _
    rw [← h.hitB_congr hxy, ← h.symm.hitB_congr hxy]
    exact hx
  have hTN : ∀ x ∉ A, T x = α x := fun x hx => by simp only [hTdef, hx, if_false]
  have hTA : ∀ x ∈ Z, x ∈ A → T x ∈ B ∧ (x, T x) ∈ E := by
    intro x hxZ hxA
    have hhit : ∃ n, β^[n] x ∈ B := hxZ.2 ⟨0, hxA⟩
    simp only [hTdef, hxA, if_true]
    refine ⟨(Nat.find_spec (hex x)).resolve_right (not_not.2 hhit), ?_⟩
    exact h.symm.fwd_mem fun i hi hiB => Nat.find_min (hex x) hi (Or.inl hiB)
  have hTE : ∀ x ∈ Z, (x, T x) ∈ E := by
    intro x hx
    by_cases hxA : x ∈ A
    · exact (hTA x hx hxA).2
    · rw [hTN x hxA]; exact (h.fwd x hxA).2.2
  have hTα : ∀ x j, (∀ i < j, α^[i] x ∉ A) → T^[j] x = α^[j] x := by
    intro x j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [iterate_succ_apply', iterate_succ_apply', ih (fun i hi => hj i (by omega)),
        hTN _ (hj j (by omega))]
  refine ⟨T, hTm, hTE, fun x hx y hy hxy => ?_, fun y hy => ?_, fun x hx y hy hxy => ?_⟩
  · by_cases hxA : x ∈ A <;> by_cases hyA : y ∈ A
    · refine h.uA x y (h.equiv.trans (hTE x hx) ?_) hxA hyA
      rw [hxy]; exact h.equiv.symm (hTE y hy)
    · have h1 := (hTA x hx hxA).1
      rw [hxy, hTN y hyA] at h1
      exact absurd h1 (h.fwd y hyA).2.1
    · have h1 := (hTA y hy hyA).1
      rw [← hxy, hTN x hxA] at h1
      exact absurd h1 (h.fwd x hxA).2.1
    · rw [hTN x hxA, hTN y hyA] at hxy
      rw [← (h.fwd x hxA).1, hxy, (h.fwd y hyA).1]
  · by_cases hyB : y ∈ B
    · obtain ⟨l, hl, hyl⟩ := (h.symm.hitB_iff y).1 (hy.1 ⟨0, hyB⟩)
      have hlZ := hZinv _ _ hyl hy
      refine ⟨l, hlZ, h.uB _ _ ?_ (hTA l hlZ hl).1 hyB⟩
      exact h.equiv.symm (h.equiv.trans hyl (hTE l hlZ))
    · obtain ⟨h1, h2, h3⟩ := h.bwd y hyB
      exact ⟨β y, hZinv _ _ h3 hy, by rw [hTN _ h2, h1]⟩
  · obtain ⟨j, ⟨hj, hjA⟩ | ⟨hj, hjA⟩⟩ := h.chain x y hxy
    · exact ⟨j, Or.inl (by rw [hTα x j hjA, hj])⟩
    · exact ⟨j, Or.inr (by rw [hTα y j hjA, hj])⟩

end CFWPlan.Main.P6
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P6
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
/-- **From a successor map to a single automorphism (D2b).** Each `E`-class is a `τ`-chain of
type `ℤ`, `ω` (has a first point), `ω*` (has a last point), or finite (both). Put `T = τ` on
`ℤ`-classes; on finite classes `T = τ` except `T(last) = first`; on `ω`/`ω*` classes, with the
Borel position `pos x = #{steps from the endpoint}` (`measurable_encard_section` or iterate
counting), use the zig-zag `c₀ → c₂ → c₄ → …`, `… → c₃ → c₁ → c₀` (a bijection `ℕ ≃ ℤ`).
`T` is a Borel bijection, hence a `MeasurableEquiv` (`Measurable.measurableEmbedding` +
surjectivity); its `ℤ`-orbits are the classes. *Size:* 280. -/
theorem exists_generator_of_successor {E : Set (X × X)} (hE : MeasurableSet E)
    (hEeq : Equivalence fun x y => (x, y) ∈ E) (hEc : ∀ x, {y | (x, y) ∈ E}.Countable)
    {Lm Fm : Set X} {τ : X → X} (hLm : MeasurableSet Lm) (hFm : MeasurableSet Fm)
    (hτ : Measurable τ) (hinj : InjOn τ Lmᶜ) (himg : τ '' Lmᶜ = Fmᶜ)
    (hτE : ∀ x ∉ Lm, (x, τ x) ∈ E)
    (hLm1 : ∀ x y, (x, y) ∈ E → x ∈ Lm → y ∈ Lm → x = y)
    (hFm1 : ∀ x y, (x, y) ∈ E → x ∈ Fm → y ∈ Fm → x = y)
    (hchain : ∀ x y, (x, y) ∈ E → ∃ j : ℕ,
      (τ^[j] x = y ∧ ∀ i < j, τ^[i] x ∉ Lm) ∨ (τ^[j] y = x ∧ ∀ i < j, τ^[i] y ∉ Lm)) :
    ∃ T : X ≃ᵐ X, ∀ x y, (x, y) ∈ E ↔ ∃ k : ℤ, (T.toEquiv ^ k) x = y := by
  classical
  clear hE hEc
  -- the Borel inverse `ρ` of `τ`
  have : StandardBorelSpace (Lmᶜ : Set X) := hLm.compl.standardBorel
  have hemb : MeasurableEmbedding (fun x : (Lmᶜ : Set X) => τ x) :=
    (hτ.comp measurable_subtype_coe).measurableEmbedding
      (fun a b hab => Subtype.ext (hinj a.2 b.2 hab))
  obtain ⟨ρ, hρm, hρ⟩ :=
    hemb.exists_measurable_extend (g := Subtype.val) measurable_subtype_coe (fun a => ⟨a⟩)
  have hρτ : ∀ x ∉ Lm, ρ (τ x) = x := fun x hx => congrFun hρ ⟨x, hx⟩
  have hD : ChainData E Lm Fm τ ρ :=
    { equiv := hEeq
      fwd := fun x hx => ⟨hρτ x hx, by
        rw [← mem_compl_iff, ← himg]; exact mem_image_of_mem τ hx, hτE x hx⟩
      bwd := by
        intro y hy
        rw [← mem_compl_iff, ← himg] at hy
        obtain ⟨x, hx, rfl⟩ := hy
        rw [hρτ x hx]
        exact ⟨rfl, hx, hEeq.symm (hτE x hx)⟩
      uA := hLm1
      uB := hFm1
      chain := hchain }
  obtain ⟨T₁, hT₁m, hT₁⟩ := omega_part hD hFm hτ hρm
  obtain ⟨T₂, hT₂m, hT₂⟩ := omega_part hD.symm hLm hρm hτ
  obtain ⟨T₃, hT₃m, hT₃⟩ := fin_part hD hLm hFm hτ hρm
  set Ω₁ : Set X := {x | (∃ n, ρ^[n] x ∈ Fm) ∧ ¬ ∃ n, τ^[n] x ∈ Lm} with hΩ₁def
  set Ω₂ : Set X := {x | (∃ n, τ^[n] x ∈ Lm) ∧ ¬ ∃ n, ρ^[n] x ∈ Fm} with hΩ₂def
  have hΩ₁m : MeasurableSet Ω₁ :=
    (measurableSet_hit hρm hFm).inter (measurableSet_hit hτ hLm).compl
  have hΩ₂m : MeasurableSet Ω₂ :=
    (measurableSet_hit hτ hLm).inter (measurableSet_hit hρm hFm).compl
  have hΩ₁inv : ∀ x y, (x, y) ∈ E → x ∈ Ω₁ → y ∈ Ω₁ := fun x y hxy hx =>
    ⟨(hD.hitB_congr hxy).1 hx.1, fun hy => hx.2 ((hD.symm.hitB_congr hxy).2 hy)⟩
  have hΩ₂inv : ∀ x y, (x, y) ∈ E → x ∈ Ω₂ → y ∈ Ω₂ := fun x y hxy hx =>
    ⟨(hD.symm.hitB_congr hxy).1 hx.1, fun hy => hx.2 ((hD.hitB_congr hxy).2 hy)⟩
  set T : X → X := Ω₁.piecewise T₁ (Ω₂.piecewise T₂ T₃) with hTdef
  have hTm : Measurable T := hT₁m.piecewise hΩ₁m (hT₂m.piecewise hΩ₂m hT₃m)
  have hgood : GoodOn E univ T := by
    refine goodOn_piecewise (S := univ) (P := Ω₁) hEeq (fun _ _ _ _ => trivial) hΩ₁inv ?_ ?_
    · rw [univ_inter]; exact hT₁
    · refine goodOn_piecewise (S := univ ∩ Ω₁ᶜ) (P := Ω₂) hEeq
        (fun x y hxy hx => ⟨trivial, fun hy => hx.2
        (hΩ₁inv y x (hEeq.symm hxy) hy)⟩) hΩ₂inv ?_ ?_
      · have : univ ∩ Ω₁ᶜ ∩ Ω₂ = {x | (∃ n, τ^[n] x ∈ Lm) ∧ ¬ ∃ n, ρ^[n] x ∈ Fm} := by
          ext x
          simp only [hΩ₁def, hΩ₂def, mem_inter_iff, mem_univ, mem_compl_iff, mem_ofPred_eq]
          tauto
        rw [this]; exact hT₂
      · have : univ ∩ Ω₁ᶜ ∩ Ω₂ᶜ = {x | (∃ n, ρ^[n] x ∈ Fm) ↔ ∃ n, τ^[n] x ∈ Lm} := by
          ext x
          simp only [hΩ₁def, hΩ₂def, mem_inter_iff, mem_univ, mem_compl_iff, mem_ofPred_eq]
          tauto
        rw [this]; exact hT₃
  have hbij : Bijective T := ⟨injOn_univ.1 hgood.2.1, fun y => by
    obtain ⟨x, -, hx⟩ := hgood.2.2.1 y trivial
    exact ⟨x, hx⟩⟩
  have hTemb : MeasurableEmbedding T := hTm.measurableEmbedding hbij.1
  let Te : X ≃ᵐ X :=
    { toEquiv := Equiv.ofBijective T hbij
      measurable_toFun := hTm
      measurable_invFun := by
        intro s hs
        have : (Equiv.ofBijective T hbij).symm ⁻¹' s = T '' s := by
          rw [← Equiv.image_eq_preimage_symm]
          rfl
        exact this ▸ hTemb.measurableSet_image' hs }
  have hpow : ∀ n : ℕ, ∀ z, (Te.toEquiv ^ n) z = T^[n] z := by
    intro n z
    rw [Equiv.Perm.coe_pow]
    rfl
  have hstep : ∀ n : ℕ, ∀ z, (z, T^[n] z) ∈ E := by
    intro n
    induction n with
    | zero => intro z; exact hEeq.refl z
    | succ n ih =>
      intro z
      rw [iterate_succ_apply']
      exact hEeq.trans (ih z) (hgood.1 _ trivial)
  refine ⟨Te, fun x y => ⟨fun hxy => ?_, ?_⟩⟩
  · obtain ⟨j, hj | hj⟩ := hgood.2.2.2 x trivial y trivial hxy
    · exact ⟨j, by rw [zpow_natCast, hpow]; exact hj⟩
    · refine ⟨-j, ?_⟩
      rw [zpow_neg, zpow_natCast, Equiv.Perm.inv_eq_iff_eq, hpow]
      exact hj.symm
  · rintro ⟨k, hk⟩
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · rw [zpow_natCast, hpow] at hk
      rw [← hk]
      exact hstep n x
    · rw [zpow_neg, zpow_natCast, Equiv.Perm.inv_eq_iff_eq, hpow] at hk
      rw [hk]
      exact hEeq.symm (hstep n y)

end CFWPlan.Main.P6
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias exists_generator_of_successor := CFWPlan.Main.P6.exists_generator_of_successor

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
theorem exists_generator_of_finite_union {F : ℕ → Set (X × X)} (hmono : Monotone F)
    (hF : ∀ n, MeasurableSet (F n) ∧ Equivalence (fun x y => (x, y) ∈ F n) ∧
      ∀ x, {y | (x, y) ∈ F n}.Finite) :
    ∃ T : X ≃ᵐ X, ∀ x y, (∃ n, (x, y) ∈ F n) ↔ ∃ k : ℤ, (T.toEquiv ^ k) x = y := by
  let F' : ℕ → Set (X × X) := fun n => Nat.casesOn n {p | p.1 = p.2} fun m => F m
  have hF'0 : F' 0 = {p | p.1 = p.2} := rfl
  have hF's : ∀ m, F' (m + 1) = F m := fun m => rfl
  have hdiag : ∀ m x, (x, x) ∈ F m := fun m x => (hF m).2.1.refl x
  have hmono' : Monotone F' := by
    refine monotone_nat_of_le_succ fun n => ?_
    cases n with
    | zero =>
      rw [hF'0, hF's]
      rintro ⟨x, y⟩ (h : x = y)
      subst h
      exact hdiag 0 x
    | succ m => rw [hF's, hF's]; exact hmono (Nat.le_succ m)
  have hF' : ∀ n, MeasurableSet (F' n) ∧ Equivalence (fun x y => (x, y) ∈ F' n) ∧
      ∀ x, {y | (x, y) ∈ F' n}.Finite := by
    intro n
    cases n with
    | zero =>
      rw [hF'0]
      refine ⟨measurableSet_diagonal, ⟨fun x => rfl, fun h => (h : _ = _).symm,
        fun h h' => (h : _ = _).trans h'⟩, fun x => (finite_singleton x).subset ?_⟩
      intro y (hy : x = y)
      exact hy.symm
    | succ m => rw [hF's]; exact hF m
  have hF'0' : ∀ x y, (x, y) ∈ F' 0 → x = y := fun x y h => h
  have hiff : ∀ x y, (∃ n, (x, y) ∈ F' n) ↔ ∃ n, (x, y) ∈ F n := by
    intro x y
    constructor
    · rintro ⟨n, hn⟩
      cases n with
      | zero =>
        have hxy : x = y := hn
        subst hxy
        exact ⟨0, hdiag 0 x⟩
      | succ m => exact ⟨m, hn⟩
    · rintro ⟨n, hn⟩
      exact ⟨n + 1, hn⟩
  obtain ⟨Lm, Fm, τ, hLm, hFm, hτ, hinj, himg, hτE, hLm1, hFm1, hchain⟩ :=
    CFWPlan.Main.exists_successor_map hmono' hF' hF'0'
  have hEm : MeasurableSet (⋃ n, F' n) := MeasurableSet.iUnion fun n => (hF' n).1
  have hEeq : Equivalence fun x y => (x, y) ∈ ⋃ n, F' n := by
    refine ⟨fun x => mem_iUnion.2 ⟨0, rfl⟩, fun h => ?_, fun h h' => ?_⟩
    · obtain ⟨n, hn⟩ := mem_iUnion.1 h
      exact mem_iUnion.2 ⟨n, (hF' n).2.1.symm hn⟩
    · obtain ⟨n, hn⟩ := mem_iUnion.1 h
      obtain ⟨m, hm⟩ := mem_iUnion.1 h'
      exact mem_iUnion.2 ⟨max n m, (hF' _).2.1.trans (hmono' (le_max_left n m) hn)
        (hmono' (le_max_right n m) hm)⟩
  have hEc : ∀ x, {y | (x, y) ∈ ⋃ n, F' n}.Countable := by
    intro x
    have : {y | (x, y) ∈ ⋃ n, F' n} = ⋃ n, {y | (x, y) ∈ F' n} := by
      ext y
      simp only [mem_ofPred_eq, mem_iUnion]
    rw [this]
    exact countable_iUnion fun n => ((hF' n).2.2 x).countable
  obtain ⟨T, hT⟩ := CFWPlan.Main.exists_generator_of_successor hEm hEeq hEc hLm hFm hτ hinj himg
    (fun x hx => mem_iUnion.2 (hτE x hx)) (fun x y h => hLm1 x y (mem_iUnion.1 h))
    (fun x y h => hFm1 x y (mem_iUnion.1 h)) (fun x y h => hchain x y (mem_iUnion.1 h))
  exact ⟨T, fun x y => (hiff x y).symm.trans (mem_iUnion.symm.trans (hT x y))⟩

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
theorem exists_generator_of_isHyperfinite {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (h : IsHyperfinite μ R) :
    ∃ T : X ≃ᵐ X, ∃ N : Set X, MeasurableSet N ∧ μ N = 0 ∧
      ∀ x, x ∉ N → ∀ y, ((x, y) ∈ R ↔ ∃ n : ℤ, (T.toEquiv ^ n) x = y) := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · exact ⟨MeasurableEquiv.refl X, univ, MeasurableSet.univ, by simp,
      fun x hx => absurd (mem_univ x) hx⟩
  obtain ⟨ν, hν, hμν, hνμ⟩ := CFWPlan.Main.exists_probability_equiv μ hμ
  haveI := hν
  have hRν := CFWPlan.Main.IsDiscreteMeasured.of_ac hR hμν hνμ
  have hν' := CFWPlan.Main.IsHyperfinite.of_ac h hνμ hμν
  obtain ⟨F, hFmono, hF, N, hN, hN0, hNsat, hNR⟩ := IsHyperfinite.isFinHyp hRν hν'
  obtain ⟨T, hT⟩ := exists_generator_of_finite_union hFmono
    fun n => ⟨(hF n).1, (hF n).2.2.1, (hF n).2.2.2⟩
  exact ⟨T, N, hN, hμν hN0, fun x hx y => (hNR x hx y).trans (hT x y)⟩

end CFWPlan.Main.P5
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias exists_generator_of_isHyperfinite := CFWPlan.Main.P5.exists_generator_of_isHyperfinite

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

lemma measurable_zpow_apply (T : X ≃ᵐ X) (n : ℤ) : Measurable ⇑(T.toEquiv ^ n) := by
  induction n using Int.induction_on with
  | zero => simpa using measurable_id
  | succ n ih =>
    rw [zpow_add_one]
    exact ih.comp T.measurable
  | pred n ih =>
    rw [zpow_sub_one]
    exact ih.comp T.symm.measurable

set_option linter.unusedVariables false in
/-- **A relation generated by one automorphism is amenable**: Cesàro means along `T`. -/
theorem isAmenableRel_of_generator {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)}
    (hR : IsDiscreteMeasured μ R) (T : X ≃ᵐ X) {N : Set X} (hN : MeasurableSet N) (hN0 : μ N = 0)
    (hT : ∀ x, x ∉ N → ∀ y, ((x, y) ∈ R ↔ ∃ n : ℤ, (T.toEquiv ^ n) x = y)) :
    Monod.IsAmenableRel μ R := by
  classical
  have hRe := hR.equivalence
  set τ : ℤ → X → X := fun n => ⇑(T.toEquiv ^ n) with hτ
  have hτm : ∀ n, Measurable (τ n) := measurable_zpow_apply T
  have hτadd : ∀ (m n : ℤ) (x : X), τ (m + n) x = τ m (τ n x) := by
    intro m n x; simp only [hτ, zpow_add, Equiv.Perm.mul_apply]
  -- values clipped to `R`
  set v : (X × X → ℝ) → X → X → ℝ := fun f x z => if (x, z) ∈ R then f (x, z) else f (x, x)
    with hv
  set Q : ℕ → (X × X → ℝ) → X → ℝ := fun k f x =>
    (∑ j ∈ Finset.range (k + 1), v f x (τ j x)) / ((k : ℝ) + 1) with hQ
  have hk : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hv_bd : ∀ f C, (∀ p ∈ R, |f p| ≤ C) → ∀ x z, |v f x z| ≤ C := by
    intro f C hC x z; simp only [hv]
    split_ifs with h
    · exact hC _ h
    · exact hC _ (hRe.refl x)
  have hQ_bd : ∀ k f C, (∀ p ∈ R, |f p| ≤ C) → ∀ x, |Q k f x| ≤ C := by
    intro k f C hC x
    simp only [hQ]
    rw [abs_div, abs_of_pos (hk k), div_le_iff₀ (hk k)]
    calc |∑ j ∈ Finset.range (k + 1), v f x (τ j x)|
        ≤ ∑ j ∈ Finset.range (k + 1), |v f x (τ j x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range (k + 1), C := Finset.sum_le_sum fun j _ => hv_bd f C hC x _
      _ = C * ((k : ℝ) + 1) := by simp; ring
  have hv_eq : ∀ f g x, (∀ z, (x, z) ∈ R → f (x, z) = g (x, z)) → ∀ z, v f x z = v g x z := by
    intro f g x h z; simp only [hv]
    split_ifs with hz
    · exact h z hz
    · exact h x (hRe.refl x)
  refine isAmenableRel_of_asymptotic hR Q ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro k f hf
    refine Measurable.div_const (Finset.measurable_sum _ fun j _ => ?_) _
    simp only [hv]
    exact Measurable.ite (hR.measurableSet.preimage (measurable_id.prodMk (hτm j)))
      (hf.1.comp (measurable_id.prodMk (hτm j))) (hf.1.comp (measurable_id.prodMk measurable_id))
  · intro k f C _ hC; exact Eventually.of_forall (hQ_bd k f C hC)
  · intro k f g _ _
    refine Eventually.of_forall fun x => ?_
    simp only [hQ, Pi.add_apply]
    rw [← add_div, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hv]; split_ifs <;> rfl
  · intro k c f _
    refine Eventually.of_forall fun x => ?_
    simp only [hQ, Pi.smul_apply, smul_eq_mul]
    rw [mul_div_assoc', Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hv]; split_ifs <;> simp
  · intro k f _ hnn
    refine Eventually.of_forall fun x => ?_
    simp only [hQ]
    refine div_nonneg (Finset.sum_nonneg fun j _ => ?_) (hk k).le
    simp only [hv]
    split_ifs with h
    · exact hnn _ h
    · exact hnn _ (hRe.refl x)
  · intro k
    refine Eventually.of_forall fun x => ?_
    simp only [hQ, hv, Pi.one_apply, ite_self, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    rw [mul_one]
    exact div_self (hk k).ne'
  · intro k f g _ _ hfg
    rw [EventuallyEq, ae_iff]
    refine measure_mono_null ?_ hfg
    intro x hx
    by_contra hx'
    apply hx
    have h : ∀ z, (x, z) ∈ R → f (x, z) = g (x, z) := by
      intro z hz
      by_contra hne
      exact hx' ⟨(x, z), ⟨hne, hz⟩, rfl⟩
    simp only [hQ]
    congr 1
    exact Finset.sum_congr rfl fun j _ => hv_eq f g x h _
  · intro φ f hf
    obtain ⟨C, hC0, hC⟩ := IsBddMeasOn.exists_nonneg hf
    rw [ae_iff]
    refine measure_mono_null ?_ hN0
    intro y hy
    by_contra hyN
    apply hy
    by_cases hyc : y ∈ φ.cod
    · set x := ptInv φ y with hx
      have hyx : (y, x) ∈ R := hRe.symm (ptInv_mem_R φ hyc)
      obtain ⟨d, hd⟩ := (hT y hyN x).mp hyx
      have hyR : ∀ j : ℤ, (y, τ j y) ∈ R := fun j => (hT y hyN _).mpr ⟨j, rfl⟩
      have hxR : ∀ j : ℤ, (x, τ j y) ∈ R := fun j => hRe.trans (hRe.symm hyx) (hyR j)
      set a : ℤ → ℝ := fun j => f (x, τ j y) with ha
      have haC : ∀ j, |a j| ≤ C := fun j => hC _ (hxR j)
      have e1 : ∀ k, Q k (φ.shiftRel f) y = (∑ j ∈ Finset.range (k + 1), a j) / ((k : ℝ) + 1) := by
        intro k
        simp only [hQ]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hv, if_pos (hyR j), shiftRel_eq, if_pos hyc, ha, hx]
      have e2 : ∀ k, φ.shiftBase (Q k f) y =
          (∑ j ∈ Finset.range (k + 1), a ((j : ℤ) + d)) / ((k : ℝ) + 1) := by
        intro k
        rw [shiftBase_eq]
        simp only [if_pos hyc, hQ]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        have hd' : τ d y = x := hd
        have h1 : τ j x = τ ((j : ℤ) + d) y := by rw [hτadd, hd']
        have h2 : (x, τ j x) ∈ R := by rw [h1]; exact hxR _
        simp only [hv, ha]
        rw [if_pos h2, h1]
      refine squeeze_zero_norm (a := fun k : ℕ => 2 * |(d : ℝ)| * C / ((k : ℝ) + 1))
        (fun k => ?_) ?_
      · rw [e1, e2, ← sub_div, Real.norm_eq_abs, abs_div, abs_of_pos (hk k), abs_sub_comm]
        exact div_le_div_of_nonneg_right (abs_sum_shift_le a haC _ d) (hk k).le
      · have := (tendsto_const_div_atTop_nhds_zero_nat (2 * |(d : ℝ)| * C)).comp
          (tendsto_add_atTop_nat 1)
        refine this.congr fun k => ?_
        simp
    · refine tendsto_const_nhds.congr fun k => ?_
      rw [shiftBase_eq]
      simp only [if_neg hyc, sub_zero, hQ]
      symm
      refine div_eq_zero_iff.mpr (Or.inl (Finset.sum_eq_zero fun j _ => ?_))
      simp only [hv, shiftRel_eq, if_neg hyc, ite_self]

end CFWPlan.Main.P3
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]
alias isAmenableRel_of_generator := CFWPlan.Main.P3.isAmenableRel_of_generator

/-- **Dye = milestone `isHyperfinite_iff_exists_measurableEquiv`** (CFW p. 434, cf. [9]).
"⇐" is `isAmenableRel_of_generator` followed by **Theorem 10** (`isHyperfinite_of_isAmenableRel'`).
*Size:* 5 (proved). -/
theorem dye {μ : Measure X} [SigmaFinite μ] {R : Set (X × X)} (hR : IsDiscreteMeasured μ R) :
    IsHyperfinite μ R ↔ ∃ T : X ≃ᵐ X, ∃ N : Set X, MeasurableSet N ∧ μ N = 0 ∧
      ∀ x, x ∉ N → ∀ y, ((x, y) ∈ R ↔ ∃ n : ℤ, (T.toEquiv ^ n) x = y) := by
  refine ⟨exists_generator_of_isHyperfinite hR, ?_⟩
  rintro ⟨T, N, hN, hN0, hT⟩
  exact (ConnesFeldmanWeiss.isHyperfinite_iff_isAmenableRel _ _ hR).2 (isAmenableRel_of_generator hR T hN hN0 hT)

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
    IsHyperfinite μ R ↔ ∃ T : X ≃ᵐ X, ∃ N : Set X, MeasurableSet N ∧ μ N = 0 ∧
      ∀ x, x ∉ N → ∀ y, ((x, y) ∈ R ↔ ∃ n : ℤ, (T.toEquiv ^ n) x = y) :=
  dye hR
end
