-- Prove2me | solution 1 for ConnesFeldmanWeiss.exists_seq_measurableEquiv_of_countable_classes
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T15:49:07.870229+00:00
-- url     : https://prove2.me/submissions/f33d8ca8-d1b0-4cc8-81eb-04b591b213d0

import Theorems.Thm_LusinNovikov_exists_disjoint_injOn_fst_iUnion_eq_of_countable_sections
import Mathlib
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
set_option linter.unusedVariables false in
/-- **C3. Splitting off the diagonal into pieces with disjoint domain and codomain.** -/
theorem exists_disjoint_domCod_cover {G : Set (X × X)} (hG : MeasurableSet G)
    (h₁ : InjOn Prod.fst G) (h₂ : InjOn Prod.snd G) (hdiag : ∀ p ∈ G, p.1 ≠ p.2) :
    ∃ H : ℕ → Set (X × X), (∀ n, MeasurableSet (H n)) ∧ (∀ n, H n ⊆ G) ∧
      (∀ n, Disjoint (Prod.fst '' H n) (Prod.snd '' H n)) ∧ ⋃ n, H n = G := by
  obtain ⟨S, hSm, hS⟩ := exists_seq_separating X (p := MeasurableSet) MeasurableSet.empty univ
  let T : ℕ → Set X := fun n => if n % 2 = 0 then S (n / 2) else (S (n / 2))ᶜ
  have hTm : ∀ n, MeasurableSet (T n) := fun n => by
    simp only [T]; split_ifs
    exacts [hSm _, (hSm _).compl]
  refine ⟨fun n => G ∩ T n ×ˢ (T n)ᶜ, fun n => hG.inter ((hTm n).prod (hTm n).compl),
    fun n => inter_subset_left, ?_, ?_⟩
  · intro n
    rw [Set.disjoint_left]
    rintro x ⟨p, hp, rfl⟩ ⟨q, hq, hqx⟩
    exact hq.2.2 (hqx ▸ hp.2.1)
  · apply Subset.antisymm (iUnion_subset fun n => inter_subset_left)
    intro p hp
    obtain ⟨k, hk⟩ : ∃ k, ¬ (p.1 ∈ S k ↔ p.2 ∈ S k) := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hdiag p hp (hS _ (mem_univ _) _ (mem_univ _) h)
    by_cases h1 : p.1 ∈ S k
    · have h2 : p.2 ∉ S k := fun h2 => hk (iff_of_true h1 h2)
      have hT : T (2 * k) = S k := by
        simp only [T, if_pos (show 2 * k % 2 = 0 by omega), show 2 * k / 2 = k by omega]
      refine mem_iUnion.2 ⟨2 * k, hp, ?_⟩
      rw [hT]
      exact ⟨h1, h2⟩
    · have h2 : p.2 ∈ S k := by
        by_contra h2
        exact hk (iff_of_false h1 h2)
      have hT : T (2 * k + 1) = (S k)ᶜ := by
        simp only [T, if_neg (show ¬ (2 * k + 1) % 2 = 0 by omega),
          show (2 * k + 1) / 2 = k by omega]
      refine mem_iUnion.2 ⟨2 * k + 1, hp, ?_⟩
      rw [hT, compl_compl]
      exact ⟨h1, h2⟩

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
/-- **C4. Involution from a partial injection with disjoint domain and codomain.** -/
theorem exists_involution_of_biInjOn {G : Set (X × X)} (hG : MeasurableSet G)
    (h₁ : InjOn Prod.fst G) (h₂ : InjOn Prod.snd G)
    (hdisj : Disjoint (Prod.fst '' G) (Prod.snd '' G)) :
    ∃ g : X ≃ᵐ X, (∀ x, g (g x) = x) ∧ (∀ p ∈ G, g p.1 = p.2) ∧
      ∀ x, g x = x ∨ (x, g x) ∈ G ∨ (g x, x) ∈ G := by
  classical
  have := hG.standardBorel
  have e₁ := measurableEmbedding_fst_of_injOn hG h₁
  have e₂ := measurableEmbedding_snd_of_injOn hG h₂
  obtain ⟨a, ham, haG⟩ := e₁.exists_measurable_extend
    (g := fun p : G => (p : X × X).2) (measurable_snd.comp measurable_subtype_coe)
    (fun x => ⟨x⟩)
  obtain ⟨b, hbm, hbG⟩ := e₂.exists_measurable_extend
    (g := fun p : G => (p : X × X).1) (measurable_fst.comp measurable_subtype_coe)
    (fun x => ⟨x⟩)
  have ha : ∀ p ∈ G, a p.1 = p.2 := fun p hp => congrFun haG ⟨p, hp⟩
  have hb : ∀ p ∈ G, b p.2 = p.1 := fun p hp => congrFun hbG ⟨p, hp⟩
  set D := Prod.fst '' G with hD
  set C := Prod.snd '' G with hC
  have hDm : MeasurableSet D := hG.image_of_measurable_injOn measurable_fst h₁
  have hCm : MeasurableSet C := hG.image_of_measurable_injOn measurable_snd h₂
  let g : X → X := D.piecewise a (C.piecewise b id)
  have hgm : Measurable g := ham.piecewise hDm (hbm.piecewise hCm measurable_id)
  have hg₁ : ∀ p ∈ G, g p.1 = p.2 := fun p hp => by
    simp only [g]
    rw [piecewise_eq_of_mem _ _ _ (mem_image_of_mem _ hp), ha p hp]
  have hg₂ : ∀ p ∈ G, g p.2 = p.1 := fun p hp => by
    have hC' : p.2 ∈ C := mem_image_of_mem _ hp
    have hD' : p.2 ∉ D := fun h => disjoint_left.1 hdisj h hC'
    simp only [g]
    rw [piecewise_eq_of_notMem _ _ _ hD', piecewise_eq_of_mem _ _ _ hC', hb p hp]
  have hg₃ : ∀ x, x ∉ D → x ∉ C → g x = x := fun x hD' hC' => by
    simp only [g]
    rw [piecewise_eq_of_notMem _ _ _ hD', piecewise_eq_of_notMem _ _ _ hC']
    rfl
  have hcases : ∀ x, (∃ p ∈ G, p.1 = x) ∨ (∃ p ∈ G, p.2 = x) ∨ (x ∉ D ∧ x ∉ C) := by
    intro x
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · by_cases hxC : x ∈ C
      · exact Or.inr (Or.inl hxC)
      · exact Or.inr (Or.inr ⟨hxD, hxC⟩)
  have hinv : ∀ x, g (g x) = x := by
    intro x
    rcases hcases x with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨hxD, hxC⟩
    · rw [hg₁ p hp, hg₂ p hp]
    · rw [hg₂ p hp, hg₁ p hp]
    · rw [hg₃ x hxD hxC, hg₃ x hxD hxC]
  refine ⟨⟨⟨g, g, hinv, hinv⟩, hgm, hgm⟩, hinv, hg₁, ?_⟩
  intro x
  change g x = x ∨ (x, g x) ∈ G ∨ (g x, x) ∈ G
  rcases hcases x with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨hxD, hxC⟩
  · exact Or.inr (Or.inl (by rw [hg₁ p hp]; exact hp))
  · exact Or.inr (Or.inr (by rw [hg₂ p hp]; exact hp))
  · exact Or.inl (hg₃ x hxD hxC)

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
open MeasureTheory Set Function
namespace ConnesFeldmanWeiss
open CFWPlan.Route.PartC in
/-- **Feldman–Moore, involution form** (the CFW mission milestone, restated verbatim). -/
theorem chk_exists_seq_measurableEquiv_of_countable_classes {X : Type*} [MeasurableSpace X]
    [StandardBorelSpace X] (R : Set (X × X)) (hR : MeasurableSet R)
    (hequiv : Equivalence fun x y => (x, y) ∈ R) (hcount : ∀ x, {y | (x, y) ∈ R}.Countable) :
    ∃ φ : ℕ → X ≃ᵐ X, ∀ x y, (x, y) ∈ R ↔ ∃ n, φ n x = y := by
  set R' := R \ diagonal X with hR'def
  have hR' : MeasurableSet R' := hR.diff measurableSet_diagonal
  have hc1 : ∀ x, {y | (x, y) ∈ R'}.Countable := fun x => (hcount x).mono fun y hy => hy.1
  have hc2 : ∀ y, {x | (x, y) ∈ R'}.Countable := fun y =>
    (hcount y).mono fun x hx => hequiv.symm hx.1
  obtain ⟨G, hGm, hG1, hG2, -, hGU⟩ := exists_biInjOn_cover hR' hc1 hc2
  have hGR : ∀ n, G n ⊆ R' := fun n => hGU ▸ subset_iUnion G n
  choose H hHm hHG hHd hHU using fun n => exists_disjoint_domCod_cover (hGm n) (hG1 n) (hG2 n)
    (fun p hp => (hGR n hp).2)
  choose g hgg hgH hgx using fun n k => exists_involution_of_biInjOn (hHm n k)
    ((hG1 n).mono (hHG n k)) ((hG2 n).mono (hHG n k)) (hHd n k)
  have hHR : ∀ n k, H n k ⊆ R := fun n k => (hHG n k).trans ((hGR n).trans fun _ hp => hp.1)
  refine ⟨fun n => if n = 0 then MeasurableEquiv.refl X else
    g (n - 1).unpair.1 (n - 1).unpair.2, ?_⟩
  intro x y
  constructor
  · intro hxy
    by_cases hd : x = y
    · exact ⟨0, by simp [hd]⟩
    · have hxy' : (x, y) ∈ ⋃ n, G n := hGU ▸ ⟨hxy, hd⟩
      obtain ⟨n, hn⟩ := mem_iUnion.1 hxy'
      have hxy'' : (x, y) ∈ ⋃ k, H n k := (hHU n).symm ▸ hn
      obtain ⟨k, hk⟩ := mem_iUnion.1 hxy''
      refine ⟨Nat.pair n k + 1, ?_⟩
      simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, Nat.unpair_pair]
      exact hgH n k _ hk
  · rintro ⟨N, rfl⟩
    by_cases hN : N = 0
    · simp only [hN, if_true, MeasurableEquiv.refl_apply]
      exact hequiv.refl x
    · simp only [hN, if_false]
      rcases hgx (N - 1).unpair.1 (N - 1).unpair.2 x with h | h | h
      · rw [h]; exact hequiv.refl x
      · exact hHR _ _ h
      · exact hequiv.symm (hHR _ _ h)

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

end CFWPlan.Main
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
    [StandardBorelSpace X] (R : Set (X × X)) (hR : MeasurableSet R)
    (hequiv : Equivalence fun x y => (x, y) ∈ R) (hcount : ∀ x, {y | (x, y) ∈ R}.Countable) :
    ∃ φ : ℕ → X ≃ᵐ X, ∀ x y, (x, y) ∈ R ↔ ∃ n, φ n x = y :=
  ConnesFeldmanWeiss.chk_exists_seq_measurableEquiv_of_countable_classes R hR hequiv hcount
end
