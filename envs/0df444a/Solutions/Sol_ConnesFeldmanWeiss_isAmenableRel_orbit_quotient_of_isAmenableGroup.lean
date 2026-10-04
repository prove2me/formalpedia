-- Prove2me | solution 1 for ConnesFeldmanWeiss.isAmenableRel_orbit_quotient_of_isAmenableGroup
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T21:03:28.40529+00:00
-- url     : https://prove2.me/submissions/cd1acd61-934a-41b7-bbc2-959b0476e596

import Mathlib
import Definitions.Def_Monod_PiecewiseProjective
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
alias exists_bounded_density_of_functional := CFWPlan.Main.P3.exists_bounded_density_of_functional

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
alias ae_eq_of_forall_integral_mul_eq := CFWPlan.Main.P3.ae_eq_of_forall_integral_mul_eq

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
/-- Bounded measurable real functions. -/
def IsBddMeas {α : Type*} [MeasurableSpace α] (F : α → ℝ) : Prop :=
  Measurable F ∧ ∃ C, ∀ x, |F x| ≤ C

/-- The body of `IsAmenableGroup P` for a given functional `M` (so that `IsAmenableGroup P` is
`∃ M, IsInvMean M`, `isAmenableGroup_iff`). -/
def IsInvMean {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [LocallyCompactSpace P] [MeasurableSpace P] [BorelSpace P] (M : (P → ℝ) → ℝ) : Prop :=
  (∀ f g : P → ℝ, Measurable f → Measurable g → (∃ C, ∀ x, |f x| ≤ C) → (∃ C, ∀ x, |g x| ≤ C) →
      M (f + g) = M f + M g ∧ (f =ᵐ[Measure.haar] g → M f = M g)) ∧
    (∀ f : P → ℝ, Measurable f → (∃ C, ∀ x, |f x| ≤ C) →
      (∀ c : ℝ, M (c • f) = c * M f) ∧ ((∀ x, 0 ≤ f x) → 0 ≤ M f) ∧
      ∀ g : P, M (fun x => f (g * x)) = M f) ∧
    M 1 = 1

/-- *Size:* 1 (proved). -/
theorem isAmenableGroup_iff {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [LocallyCompactSpace P] [MeasurableSpace P] [BorelSpace P] :
    IsAmenableGroup P ↔ ∃ M : (P → ℝ) → ℝ, IsInvMean M :=
  Iff.rfl

end CFWPlan.Main
end

section
set_option linter.unusedSectionVars false
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main.P6
open ConnesFeldmanWeiss
/-- A locally compact, second countable, Hausdorff space is Polish: its one-point
compactification is second countable (basis: a countable basis of `Y` and the complements of a
compact exhaustion), hence compact metrizable, and `Y` is open in it. -/
theorem polishSpace_of_lcsc_space (Y : Type*) [TopologicalSpace Y] [LocallyCompactSpace Y]
    [SecondCountableTopology Y] [T2Space Y] : PolishSpace Y := by
  obtain ⟨B, hBc, -, hB⟩ := TopologicalSpace.exists_countable_basis Y
  let K := CompactExhaustion.choice Y
  have hbasis : TopologicalSpace.IsTopologicalBasis
      (((fun U : Set Y => ((↑) : Y → OnePoint Y) '' U) '' B) ∪
        range (fun n => (((↑) : Y → OnePoint Y) '' K n)ᶜ)) := by
    refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro _ (⟨U, hU, rfl⟩ | ⟨n, rfl⟩)
      · exact OnePoint.isOpenEmbedding_coe.isOpenMap _ (hB.isOpen hU)
      · exact ((K.isCompact n).image OnePoint.continuous_coe).isClosed.isOpen_compl
    · intro a u ha hu
      induction a using OnePoint.rec with
      | infty =>
        obtain ⟨n, hn⟩ :=
          K.exists_superset_of_isCompact ((OnePoint.isOpen_iff_of_mem' ha).1 hu).1
        refine ⟨_, Or.inr ⟨n, rfl⟩, ?_, ?_⟩
        · rintro ⟨y, -, hy⟩
          exact OnePoint.coe_ne_infty y hy
        · intro z hz
          induction z using OnePoint.rec with
          | infty => exact ha
          | coe y =>
            by_contra hyu
            exact hz ⟨y, hn hyu, rfl⟩
      | coe y =>
        have hu' : IsOpen (((↑) : Y → OnePoint Y) ⁻¹' u) := hu.preimage OnePoint.continuous_coe
        obtain ⟨b, hbB, hyb, hbu⟩ := hB.exists_subset_of_mem_open ha hu'
        exact ⟨_, Or.inl ⟨b, hbB, rfl⟩, ⟨y, hyb, rfl⟩, by rintro _ ⟨z, hz, rfl⟩; exact hbu hz⟩
  have : SecondCountableTopology (OnePoint Y) :=
    hbasis.secondCountableTopology ((hBc.image _).union (countable_range _))
  have : TopologicalSpace.MetrizableSpace (OnePoint Y) :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable _
  let := TopologicalSpace.metrizableSpaceMetric (OnePoint Y)
  have : PolishSpace (OnePoint Y) := inferInstance
  have := (OnePoint.isOpen_range_coe (X := Y)).polishSpace
  exact (OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph).isClosedEmbedding.polishSpace

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
/-- A discrete subgroup of a second countable group is countable
(`countable_of_Lindelof_of_discrete`). *Size:* 10. -/
theorem countable_of_discrete_subgroup (Γ : Subgroup G) [DiscreteTopology Γ] : Countable Γ := by
  exact countable_of_Lindelof_of_discrete

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
/-- The quotient by a closed subgroup is standard Borel (Polish: `polishSpace_of_lcsc` for the
lcsc Hausdorff space `G ⧸ P`, or `Continuous.map_borel_eq`). *Size:* 30. -/
theorem standardBorelSpace_quotient (P : Subgroup G) (hP : IsClosed (P : Set G))
    [MeasurableSpace (G ⧸ P)] [BorelSpace (G ⧸ P)] : StandardBorelSpace (G ⧸ P) := by
  have : IsClosed (P : Set G) := hP
  exact ⟨⟨inferInstance, inferInstance, polishSpace_of_lcsc_space (G ⧸ P)⟩⟩

/-- Strictly right-`P`-invariant Borel functions descend to Borel functions on `G ⧸ P`: the Borel
σ-algebra of `G ⧸ P` is the quotient σ-algebra (`Continuous.map_borel_eq` with
`polishSpace_of_lcsc`, `QuotientGroup.continuous_mk`, second countability and `T2` of the
quotient by a closed subgroup). *Size:* 40. -/
theorem exists_descent (P : Subgroup G) (hP : IsClosed (P : Set G)) [MeasurableSpace (G ⧸ P)]
    [BorelSpace (G ⧸ P)] {u : G → ℝ} (hu : Measurable u) (hinv : ∀ g (p : P), u (g * p) = u g) :
    ∃ v : G ⧸ P → ℝ, Measurable v ∧ ∀ g, v (QuotientGroup.mk g) = u g := by
  have : IsClosed (P : Set G) := hP
  have : PolishSpace G := polishSpace_of_lcsc_space G
  have : StandardBorelSpace G := ⟨⟨inferInstance, inferInstance, inferInstance⟩⟩
  have : StandardBorelSpace (G ⧸ P) := CFWPlan.Main.P6.standardBorelSpace_quotient P hP
  let v : G ⧸ P → ℝ := Quotient.lift u (by
    intro a b hab
    have hab' : a⁻¹ * b ∈ P := QuotientGroup.leftRel_apply.1 hab
    have := hinv a ⟨a⁻¹ * b, hab'⟩
    simp only [mul_inv_cancel_left] at this
    exact this.symm)
  refine ⟨v, ?_, fun g => rfl⟩
  have hmk : Measurable (QuotientGroup.mk : G → G ⧸ P) :=
    (QuotientGroup.continuous_mk).measurable
  exact (hmk.measurable_comp_iff_of_surjective QuotientGroup.mk_surjective).1 hu

/-- **A Borel `Γ`-equivariant index map** `κ : G → Γ`, `κ (γ g) = γ κ(g)`, i.e. a Borel fundamental
domain for the left action of `Γ` on `G`. *Proof:* `U ∋ 1` open with `U ∩ Γ = {1}`, `V` with
`V V⁻¹ ⊆ U`; the right translates `V gₖ` (`gₖ` dense) are partial transversals; disjointify
modulo `Γ` (`Γ` countable, `countable_of_discrete_subgroup`). *Size:* 130. -/
theorem exists_equivariant_index (Γ : Subgroup G) [DiscreteTopology Γ] :
    ∃ κ : G → Γ, Measurable κ ∧ ∀ (γ : Γ) (g : G), κ ((γ : G) * g) = γ * κ g := by
  classical
  have hΓc : Countable Γ := CFWPlan.Main.P6.countable_of_discrete_subgroup Γ
  -- `U ∩ Γ = {1}`
  obtain ⟨U, hUo, hU⟩ : ∃ U : Set G, IsOpen U ∧ ((↑) : Γ → G) ⁻¹' U = {1} :=
    isOpen_induced_iff.1 (isOpen_discrete ({1} : Set Γ))
  have hU1 : (1 : G) ∈ U := by
    have : (1 : Γ) ∈ ((↑) : Γ → G) ⁻¹' U := by rw [hU]; rfl
    exact this
  have hUΓ : ∀ γ ∈ Γ, γ ∈ U → γ = 1 := by
    intro γ hγ hγU
    have : (⟨γ, hγ⟩ : Γ) ∈ ((↑) : Γ → G) ⁻¹' U := hγU
    rw [hU] at this
    exact congrArg Subtype.val this
  obtain ⟨V, hV, hVU⟩ := exists_nhds_split_inv (hUo.mem_nhds hU1)
  set W := interior V with hWdef
  have hWo : IsOpen W := isOpen_interior
  have hW1 : (1 : G) ∈ W := mem_interior_iff_mem_nhds.2 hV
  -- countably many right translates `W g` cover `G`
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun g : G => (fun x => x * g⁻¹) ⁻¹' W) (fun g => hWo.preimage (continuous_mul_const _))
  have hTne : T.Nonempty := by
    by_contra hT
    rw [not_nonempty_iff_eq_empty] at hT
    have h1 : (1 : G) ∈ ⋃ g, (fun x => x * g⁻¹) ⁻¹' W :=
      mem_iUnion.2 ⟨1, by simp only [mem_preimage, inv_one, mul_one]; exact hW1⟩
    rw [← hTU, hT] at h1
    simp at h1
  obtain ⟨gs, hgs⟩ := hTc.exists_eq_range hTne
  set D : ℕ → Set G := fun k => (fun x => x * (gs k)⁻¹) ⁻¹' W with hDdef
  have hDm : ∀ k, MeasurableSet (D k) := fun k =>
    (hWo.preimage (continuous_mul_const _)).measurableSet
  have hDcov : ∀ x, ∃ k, x ∈ D k := by
    intro x
    have : x ∈ ⋃ g, (fun x => x * g⁻¹) ⁻¹' W :=
      mem_iUnion.2 ⟨x, by simp only [mem_preimage, mul_inv_cancel]; exact hW1⟩
    rw [← hTU, hgs] at this
    simp only [mem_iUnion, exists_prop, mem_range, exists_exists_eq_and] at this
    obtain ⟨k, hk⟩ := this
    exact ⟨k, hk⟩
  have hDtr : ∀ k x, ∀ γ ∈ Γ, x ∈ D k → γ * x ∈ D k → γ = 1 := by
    intro k x γ hγ hx hγx
    refine hUΓ γ hγ ?_
    have := hVU _ (interior_subset hγx) _ (interior_subset hx)
    simpa [div_eq_mul_inv, mul_assoc] using this
  -- the fundamental domain
  set Dom : Set G := ⋃ k, (D k \ {x | ∃ γ ∈ Γ, ∃ j < k, γ * x ∈ D j}) with hDomdef
  have hmulm : ∀ γ : G, Measurable (fun x : G => γ * x) := fun γ => measurable_const_mul γ
  have hDomm : MeasurableSet Dom := by
    refine MeasurableSet.iUnion fun k => (hDm k).diff ?_
    have : {x | ∃ γ ∈ Γ, ∃ j < k, γ * x ∈ D j} =
        ⋃ γ : Γ, ⋃ j : Fin k, (fun x => (γ : G) * x) ⁻¹' D j := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion, mem_preimage, Subtype.exists, exists_prop]
      constructor
      · rintro ⟨γ, hγ, j, hj, h⟩; exact ⟨γ, hγ, ⟨j, hj⟩, h⟩
      · rintro ⟨γ, hγ, j, h⟩; exact ⟨γ, hγ, j, j.2, h⟩
    rw [this]
    exact MeasurableSet.iUnion fun γ => MeasurableSet.iUnion fun j => hmulm _ (hDm _)
  have hE : ∀ x, ∃ γ ∈ Γ, γ * x ∈ Dom := by
    intro x
    have hex : ∃ k, ∃ γ ∈ Γ, γ * x ∈ D k := by
      obtain ⟨k, hk⟩ := hDcov x
      exact ⟨k, 1, Γ.one_mem, by rw [one_mul]; exact hk⟩
    obtain ⟨γ, hγ, hγx⟩ := Nat.find_spec hex
    refine ⟨γ, hγ, mem_iUnion.2 ⟨Nat.find hex, hγx, ?_⟩⟩
    rintro ⟨δ, hδ, j, hj, hδx⟩
    exact Nat.find_min hex hj ⟨δ * γ, Γ.mul_mem hδ hγ, by rw [mul_assoc]; exact hδx⟩
  have hUq : ∀ x, ∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, γ₁ * x ∈ Dom → γ₂ * x ∈ Dom → γ₁ = γ₂ := by
    intro x γ₁ h₁ γ₂ h₂ hx₁ hx₂
    obtain ⟨k₁, hk₁, hn₁⟩ := mem_iUnion.1 hx₁
    obtain ⟨k₂, hk₂, hn₂⟩ := mem_iUnion.1 hx₂
    rcases lt_trichotomy k₁ k₂ with hlt | heq | hgt
    · exact absurd ⟨γ₁ * γ₂⁻¹, Γ.mul_mem h₁ (Γ.inv_mem h₂), k₁, hlt,
        by rw [mul_assoc, inv_mul_cancel_left]; exact hk₁⟩ hn₂
    · subst heq
      have := hDtr k₁ (γ₁ * x) (γ₂ * γ₁⁻¹) (Γ.mul_mem h₂ (Γ.inv_mem h₁)) hk₁
        (by rw [mul_assoc, inv_mul_cancel_left]; exact hk₂)
      rw [mul_inv_eq_one] at this
      exact this.symm
    · exact absurd ⟨γ₂ * γ₁⁻¹, Γ.mul_mem h₂ (Γ.inv_mem h₁), k₂, hgt,
        by rw [mul_assoc, inv_mul_cancel_left]; exact hk₂⟩ hn₁
  choose δ hδΓ hδ using hE
  set κ : G → Γ := fun x => (⟨δ x, hδΓ x⟩ : Γ)⁻¹ with hκdef
  have hκ : ∀ x (γ : Γ), κ x = γ ↔ ((γ⁻¹ : Γ) : G) * x ∈ Dom := by
    intro x γ
    constructor
    · rintro rfl
      simpa [hκdef] using hδ x
    · intro h
      have := hUq x _ (hδΓ x) _ (γ⁻¹ : Γ).2 (hδ x) h
      rw [hκdef]
      ext
      simp [this]
  refine ⟨κ, measurable_to_countable' fun γ => ?_, fun γ g => ?_⟩
  · have : κ ⁻¹' {γ} = (fun x => ((γ⁻¹ : Γ) : G) * x) ⁻¹' Dom := by
      ext x
      simp only [mem_preimage, mem_singleton_iff]
      exact hκ x γ
    rw [this]
    exact hmulm _ hDomm
  · rw [hκ]
    have h := (hκ g (κ g)).1 rfl
    simpa [mul_assoc] using h

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
/-- The `Γ`-orbit relation on `G ⧸ P` is discrete measured for `ν` in the Haar class: Borel
(countable union of graphs of homeomorphisms), countable classes (`Γ` countable), quasi-invariant
(`haar (π⁻¹(γ A)) = haar (γ π⁻¹ A) = haar (π⁻¹ A)` by left invariance, and `hν`). *Size:* 110. -/
theorem isDiscreteMeasured_orbit (P : Subgroup G) (hP : IsClosed (P : Set G)) (Γ : Subgroup G)
    [DiscreteTopology Γ] [MeasurableSpace (G ⧸ P)] [BorelSpace (G ⧸ P)] (ν : Measure (G ⧸ P))
    (hν : ∀ A : Set (G ⧸ P), MeasurableSet A →
      (ν A = 0 ↔ Measure.haar ((QuotientGroup.mk : G → G ⧸ P) ⁻¹' A) = 0)) :
    IsDiscreteMeasured ν {p : (G ⧸ P) × (G ⧸ P) | ∃ γ ∈ Γ, γ • p.1 = p.2} := by
  have : IsClosed (P : Set G) := hP
  have hΓc : Countable Γ := CFWPlan.Main.P6.countable_of_discrete_subgroup Γ
  have hsm : ∀ γ : G, Measurable (fun y : G ⧸ P => γ • y) := fun γ =>
    (continuous_const_smul γ).measurable
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hR : {p : (G ⧸ P) × (G ⧸ P) | ∃ γ ∈ Γ, γ • p.1 = p.2} =
        ⋃ γ : Γ, {p | (γ : G) • p.1 = p.2} := by
      ext p
      simp only [mem_ofPred_eq, mem_iUnion, Subtype.exists, exists_prop]
    rw [hR]
    exact MeasurableSet.iUnion fun γ =>
      (isClosed_eq ((continuous_const_smul (γ : G)).comp continuous_fst)
        continuous_snd).measurableSet
  · refine ⟨fun x => ⟨1, Γ.one_mem, one_smul _ _⟩, ?_, ?_⟩
    · rintro x y ⟨γ, hγ, h⟩
      have h' : γ • x = y := h
      subst h'
      exact ⟨γ⁻¹, Γ.inv_mem hγ, inv_smul_smul γ x⟩
    · rintro x y z ⟨γ, hγ, h⟩ ⟨δ, hδ, h₂⟩
      have h' : γ • x = y := h
      have h₂' : δ • y = z := h₂
      subst h' h₂'
      exact ⟨δ * γ, Γ.mul_mem hδ hγ, mul_smul δ γ x⟩
  · intro x
    have : {y | ((x, y) : (G ⧸ P) × (G ⧸ P)) ∈
        {p : (G ⧸ P) × (G ⧸ P) | ∃ γ ∈ Γ, γ • p.1 = p.2}} =
        range (fun γ : Γ => (γ : G) • x) := by
      ext y
      simp only [mem_ofPred_eq, mem_range, Subtype.exists, exists_prop]
    rw [this]
    exact countable_range _
  · intro A hA hA0
    have hsat : saturation {p : (G ⧸ P) × (G ⧸ P) | ∃ γ ∈ Γ, γ • p.1 = p.2} A =
        ⋃ γ : Γ, (fun y : G ⧸ P => (γ : G) • y) ⁻¹' A := by
      ext x
      simp only [saturation, mem_ofPred_eq, mem_iUnion, mem_preimage, Subtype.exists,
        exists_prop]
      constructor
      · rintro ⟨y, hy, γ, hγ, rfl⟩; exact ⟨γ, hγ, hy⟩
      · rintro ⟨γ, hγ, h⟩; exact ⟨_, h, γ, hγ, rfl⟩
    have hsatm : MeasurableSet (saturation {p : (G ⧸ P) × (G ⧸ P) | ∃ γ ∈ Γ, γ • p.1 = p.2} A) :=
      hsat ▸ MeasurableSet.iUnion fun γ => hsm _ hA
    rw [hν _ hsatm, hsat, preimage_iUnion]
    refine measure_iUnion_null fun γ => ?_
    have : (QuotientGroup.mk : G → G ⧸ P) ⁻¹' ((fun y => (γ : G) • y) ⁻¹' A) =
        (fun g => (γ : G) * g) ⁻¹' ((QuotientGroup.mk : G → G ⧸ P) ⁻¹' A) := rfl
    rw [this, measure_preimage_mul]
    exact (hν A hA).1 hA0

/-- **Strictly invariant versions.** A bounded measurable `u` on `G` with `u(g q) = u(g)` for a.e.
`g`, for each `q ∈ P`, agrees a.e. with a bounded measurable strictly right-`P`-invariant `ũ`:
`ũ(g) = ess sup_{p ∈ P} u(g p)` for Haar measure on `P` (measurable via
`measurable_measure_prodMk_left` over rational levels; invariance by left invariance of Haar on
`P`; `ũ = u` a.e. by Fubini on `G × P`). *Size:* 130. -/
theorem exists_strict_invariant_version (P : Subgroup G) [LocallyCompactSpace P] {u : G → ℝ}
    (hu : IsBddMeas u) (hinv : ∀ q : P, ∀ᵐ g ∂(Measure.haar : Measure G), u (g * q) = u g) :
    ∃ ũ : G → ℝ, IsBddMeas ũ ∧ (∀ g (q : P), ũ (g * q) = ũ g) ∧
      ũ =ᵐ[(Measure.haar : Measure G)] u := by
  have : SecondCountableTopology P := TopologicalSpace.Subtype.secondCountableTopology (P : Set G)
  obtain ⟨hum, C₀, hC₀⟩ := hu
  set C := max C₀ 0 with hC
  have hC0 : 0 ≤ C := le_max_right _ _
  have hCu : ∀ g, |u g| ≤ C := fun g => (hC₀ g).trans (le_max_left _ _)
  set μP : Measure P := Measure.haar with hμPdef
  set μG : Measure G := Measure.haar with hμGdef
  have hmulm : Measurable (fun z : G × P => z.1 * (z.2 : G)) :=
    measurable_fst.mul (measurable_subtype_coe.comp measurable_snd)
  set f : G × P → ℝ≥0∞ := fun z => ENNReal.ofReal (u (z.1 * z.2) + C) with hfdef
  have hfm : Measurable f :=
    ENNReal.measurable_ofReal.comp ((hum.comp hmulm).add_const C)
  set w : G → ℝ≥0∞ := fun g => essSup (fun p => f (g, p)) μP with hwdef
  have hlev : ∀ (g : G) (r : ℝ≥0∞), r < w g ↔ μP {p | r < f (g, p)} ≠ 0 := by
    intro g r
    constructor
    · intro hr h0
      have hle : (fun p => f (g, p)) ≤ᵐ[μP] fun _ => r := by
        rw [Filter.EventuallyLE, ae_iff]
        simpa [not_le] using h0
      have : w g ≤ r := essSup_le_of_ae_le _ hle
      exact absurd hr (not_lt.2 this)
    · intro h
      by_contra hle
      push Not at hle
      apply h
      have := ENNReal.ae_le_essSup (μ := μP) (fun p => f (g, p))
      rw [ae_iff] at this
      refine measure_mono_null (fun p hp => ?_) this
      simp only [mem_ofPred_eq, not_le] at hp ⊢
      exact lt_of_le_of_lt hle hp
  have hwm : Measurable w := by
    refine measurable_of_Ioi fun r => ?_
    have : w ⁻¹' Ioi r = {g | μP (Prod.mk g ⁻¹' {z | r < f z}) ∈ ({0}ᶜ : Set ℝ≥0∞)} := by
      ext g
      simp only [mem_preimage, mem_Ioi, mem_ofPred_eq, mem_compl_iff, mem_singleton_iff]
      exact hlev g r
    rw [this]
    exact (measurable_measure_prodMk_left (measurableSet_lt measurable_const hfm))
      (measurableSet_singleton 0).compl
  have hwle : ∀ g, w g ≤ ENNReal.ofReal (2 * C) := by
    intro g
    have hle : (fun p => f (g, p)) ≤ᵐ[μP] fun _ => ENNReal.ofReal (2 * C) := by
      refine Filter.Eventually.of_forall fun p => ENNReal.ofReal_le_ofReal ?_
      have := hCu (g * p)
      rw [abs_le] at this
      linarith
    exact essSup_le_of_ae_le _ hle
  have hwinv : ∀ g (q : P), w (g * q) = w g := by
    intro g q
    simp only [hwdef]
    have h1 : (fun p : P => f (g * q, p)) = (fun p => f (g, p)) ∘ (fun p => q * p) := by
      funext p
      simp only [hfdef, comp_apply, Subgroup.coe_mul, mul_assoc]
    have h2 := (MeasurableEquiv.mulLeft q).measurableEmbedding.essSup_map_measure (μ := μP)
      (g := fun p => f (g, p))
    simp only [MeasurableEquiv.coe_mulLeft, hμPdef, map_mul_left_eq_self] at h2
    rw [h1, ← h2]
  set ũ : G → ℝ := fun g => (w g).toReal - C with hũdef
  refine ⟨ũ, ⟨hwm.ennreal_toReal.sub_const C, C, fun g => ?_⟩,
    fun g q => by simp only [hũdef, hwinv], ?_⟩
  · rw [abs_le]
    constructor
    · have := ENNReal.toReal_nonneg (a := w g)
      linarith
    · have := ENNReal.toReal_le_of_le_ofReal (by linarith) (hwle g)
      linarith
  · have hD : MeasurableSet {z : G × P | u (z.1 * z.2) ≠ u z.1} :=
      (measurableSet_eq_fun (hum.comp hmulm) (hum.comp measurable_fst)).compl
    have hsec : ∀ p : P, μG ((fun x => (x, p)) ⁻¹' {z : G × P | u (z.1 * z.2) ≠ u z.1}) = 0 := by
      intro p
      have := hinv p
      rw [ae_iff] at this
      simpa using this
    have hprod : (μG.prod μP) {z : G × P | u (z.1 * z.2) ≠ u z.1} = 0 := by
      rw [Measure.prod_apply_symm hD]
      have : ∀ p : P, μG {a | ¬u (a * ↑p) = u a} = 0 := fun p => by
        have := hinv p
        rw [ae_iff] at this
        exact this
      simp [this]
    have hae : ∀ᵐ z ∂(μG.prod μP), u (z.1 * z.2) = u z.1 := by
      rw [ae_iff]
      simpa using hprod
    filter_upwards [Measure.ae_ae_of_ae_prod hae] with g hg
    have hw : w g = ENNReal.ofReal (u g + C) := by
      simp only [hwdef]
      rw [essSup_congr_ae (g := fun _ => ENNReal.ofReal (u g + C))
        (by filter_upwards [hg] with p hp; simp only [hfdef]; rw [hp]), essSup_const']
    simp only [hũdef, hw]
    rw [ENNReal.toReal_ofReal (by have := hCu g; rw [abs_le] at this; linarith)]
    ring

/-- Right translation by `q` rescales Haar measure: `∫ h (x q) dx = k(q) ∫ h`. -/
theorem integral_mul_right_haar (q : G) :
    ∃ k : ℝ≥0, 0 < k ∧ ∀ h : G → ℝ, ∫ x, h (x * q) ∂(Measure.haar : Measure G) =
      (k : ℝ) * ∫ x, h x ∂(Measure.haar : Measure G) ∧
      (Integrable h (Measure.haar : Measure G) ↔
        Integrable (fun x => h (x * q)) (Measure.haar : Measure G)) := by
  set μG : Measure G := Measure.haar with hμGdef
  have : (Measure.map (· * q) μG).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right μG q
  set k := (Measure.map (· * q) μG).haarScalarFactor μG with hkdef
  have hk : Measure.map (· * q) μG = k • μG := Measure.isMulLeftInvariant_eq_smul _ _
  have hk0 : 0 < k := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  have he : ⇑(MeasurableEquiv.mulRight q) = (· * q) := rfl
  refine ⟨k, hk0, fun h => ⟨?_, ?_⟩⟩
  · have := integral_map_equiv (μ := μG) (MeasurableEquiv.mulRight q) h
    rw [he, hk, integral_smul_nnreal_measure] at this
    rw [← this]
    rfl
  · have h1 := integrable_map_equiv (μ := μG) (MeasurableEquiv.mulRight q) h
    rw [he, hk] at h1
    rw [← show (h ∘ (· * q)) = (fun x => h (x * q)) from rfl, ← h1]
    constructor
    · intro hh
      exact hh.smul_measure_nnreal
    · intro hh
      have := hh.smul_measure_nnreal (c := k⁻¹)
      rwa [smul_smul, inv_mul_cancel₀ hk0.ne', one_smul] at this

/-- **The relative mean in `L∞(G)`.** For bounded measurable `F` on `G`, the functional
`c ↦ M(p ↦ ∫ c(g) F(g p) dg)` on `L¹(G, haar)` (`M` the invariant mean of `P`; measurability in
`p` by Fubini, `StronglyMeasurable.integral_prod_right`) is bounded linear, so it is integration
against some `Φ̃ F` (`exists_bounded_density_of_functional`). By left invariance of `M`, for each
`q ∈ P`, `Φ̃ F (g q) = Φ̃ F (g)` for a.e. `g` (right translation of Haar is quasi-invariant,
`quasiMeasurePreserving_mul_right`). *Size:* 160. -/
theorem exists_relative_density (P : Subgroup G) [LocallyCompactSpace P]
    (M : (P → ℝ) → ℝ) (hM : IsInvMean M) :
    ∃ Φ : (G → ℝ) → G → ℝ, ∀ F : G → ℝ, IsBddMeas F → IsBddMeas (Φ F) ∧
      (∀ q : P, ∀ᵐ g ∂(Measure.haar : Measure G), Φ F (g * q) = Φ F g) ∧
      (∀ C, (∀ g, |F g| ≤ C) → ∀ g, |Φ F g| ≤ C) ∧
      ∀ c : G → ℝ, Integrable c (Measure.haar : Measure G) →
        ∫ g, c g * Φ F g ∂(Measure.haar : Measure G) =
          M (fun p => ∫ g, c g * F (g * p) ∂(Measure.haar : Measure G)) := by
  classical
  have : SecondCountableTopology P := TopologicalSpace.Subtype.secondCountableTopology (P : Set G)
  suffices h : ∀ F : G → ℝ, IsBddMeas F → ∃ φ : G → ℝ, IsBddMeas φ ∧
      (∀ q : P, ∀ᵐ g ∂(Measure.haar : Measure G), φ (g * q) = φ g) ∧
      (∀ C, (∀ g, |F g| ≤ C) → ∀ g, |φ g| ≤ C) ∧
      ∀ c : G → ℝ, Integrable c (Measure.haar : Measure G) →
        ∫ g, c g * φ g ∂(Measure.haar : Measure G) =
          M (fun p => ∫ g, c g * F (g * p) ∂(Measure.haar : Measure G)) by
    choose! Φ hΦ using h
    exact ⟨Φ, hΦ⟩
  intro F hF
  obtain ⟨hFm, C₀, hC₀⟩ := hF
  obtain ⟨hMadd, hMsm, hMone⟩ := hM
  set μG : Measure G := Measure.haar with hμGdef
  -- the sup norm of `F`
  have hbdd : BddAbove (range fun g => |F g|) := ⟨C₀, by rintro _ ⟨g, rfl⟩; exact hC₀ g⟩
  set B : ℝ := ⨆ g, |F g| with hBdef
  have hFB : ∀ g, |F g| ≤ B := fun g => le_ciSup hbdd g
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hFB 1)
  have hBle : ∀ C, (∀ g, |F g| ≤ C) → B ≤ C := fun C hC => ciSup_le hC
  -- `M` is bounded by the sup norm
  have hMb : ∀ f : P → ℝ, Measurable f → ∀ D, (∀ x, |f x| ≤ D) → |M f| ≤ D := by
    intro f hf D hD
    have hb1 : ∃ C, ∀ x : P, |(D • (1 : P → ℝ)) x| ≤ C := ⟨|D|, fun x => by simp⟩
    have hbf : ∃ C, ∀ x, |((-1 : ℝ) • f) x| ≤ C := ⟨D, fun x => by simpa using hD x⟩
    have hbf' : ∃ C, ∀ x, |f x| ≤ C := ⟨D, hD⟩
    have hD1m : Measurable (D • (1 : P → ℝ)) := measurable_one.const_smul D
    have h1 := (hMadd _ _ hD1m (hf.const_smul (-1 : ℝ)) hb1 hbf).1
    have h2 := (hMadd _ _ hD1m hf hb1 hbf').1
    have hD1 : M (D • (1 : P → ℝ)) = D := by
      rw [(hMsm 1 measurable_one ⟨1, fun x => by simp⟩).1 D, hMone, mul_one]
    have hmf : M ((-1 : ℝ) • f) = -M f := by
      rw [(hMsm f hf hbf').1 (-1)]; ring
    have hpos1 : 0 ≤ M (D • (1 : P → ℝ) + (-1 : ℝ) • f) := by
      refine (hMsm _ (hD1m.add (hf.const_smul _)) ?_).2.1 ?_
      · obtain ⟨C1, hC1⟩ := hb1
        obtain ⟨C2, hC2⟩ := hbf
        exact ⟨C1 + C2, fun x => (abs_add_le _ _).trans (add_le_add (hC1 x) (hC2 x))⟩
      · intro x
        have := hD x
        rw [abs_le] at this
        simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
        linarith
    have hpos2 : 0 ≤ M (D • (1 : P → ℝ) + f) := by
      refine (hMsm _ (hD1m.add hf) ?_).2.1 ?_
      · obtain ⟨C1, hC1⟩ := hb1
        exact ⟨C1 + D, fun x => (abs_add_le _ _).trans (add_le_add (hC1 x) (hD x))⟩
      · intro x
        have := hD x
        rw [abs_le] at this
        simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul]
        linarith
    rw [h1, hD1, hmf] at hpos1
    rw [h2, hD1] at hpos2
    rw [abs_le]
    constructor <;> linarith
  -- the functions `H c (p) = ∫ c(g) F(g p) dg`
  set H : (G → ℝ) → P → ℝ := fun c p => ∫ g, c g * F (g * p) ∂μG with hHdef
  have hint : ∀ c, Integrable c μG → ∀ p : P, Integrable (fun g => c g * F (g * p)) μG :=
    fun c hc p => hc.mul_bdd ((hFm.comp (measurable_mul_const (p : G))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun g => by rw [Real.norm_eq_abs]; exact hFB _)
  have hHm : ∀ c, Integrable c μG → Measurable (H c) := by
    intro c hc
    set c' := hc.1.mk c with hc'def
    have hc'm : StronglyMeasurable c' := hc.1.stronglyMeasurable_mk
    have heq : H c = fun p : P => ∫ g, c' g * F (g * p) ∂μG := by
      funext p
      refine integral_congr_ae ?_
      filter_upwards [hc.1.ae_eq_mk] with g hg
      rw [hg]
    rw [heq]
    refine (StronglyMeasurable.integral_prod_right (f := fun (p : P) (g : G) => c' g * F (g * p))
      ?_).measurable
    refine Measurable.stronglyMeasurable ?_
    exact (hc'm.measurable.comp measurable_snd).mul
      (hFm.comp (measurable_snd.mul (measurable_subtype_coe.comp measurable_fst)))
  have hHb : ∀ c, Integrable c μG → ∀ p, |H c p| ≤ B * ∫ g, |c g| ∂μG := by
    intro c hc p
    calc |H c p| ≤ ∫ g, |c g * F (g * p)| ∂μG := abs_integral_le_integral_abs
      _ ≤ ∫ g, B * |c g| ∂μG := by
          refine integral_mono (hint c hc p).abs (hc.abs.const_mul B) fun g => ?_
          rw [abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hFB _) (abs_nonneg _)
      _ = B * ∫ g, |c g| ∂μG := integral_const_mul _ _
  have hHbdd : ∀ c, Integrable c μG → ∃ C, ∀ p, |H c p| ≤ C := fun c hc => ⟨_, hHb c hc⟩
  -- the functional
  set Λ : (G → ℝ) → ℝ := fun c => M (H c) with hΛdef
  have hΛadd : ∀ c c', Integrable c μG → Integrable c' μG → Λ (c + c') = Λ c + Λ c' := by
    intro c c' hc hc'
    have : H (c + c') = H c + H c' := by
      funext p
      simp only [hHdef, Pi.add_apply, add_mul]
      exact integral_add (hint c hc p) (hint c' hc' p)
    simp only [hΛdef, this]
    exact (hMadd _ _ (hHm c hc) (hHm c' hc') (hHbdd c hc) (hHbdd c' hc')).1
  have hΛsmul : ∀ (a : ℝ) c, Integrable c μG → Λ (a • c) = a * Λ c := by
    intro a c hc
    have : H (a • c) = a • H c := by
      funext p
      simp only [hHdef, Pi.smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul _ _
    simp only [hΛdef, this]
    exact (hMsm _ (hHm c hc) (hHbdd c hc)).1 a
  have hΛbdd : ∀ c, Integrable c μG → |Λ c| ≤ B * ∫ g, |c g| ∂μG := fun c hc =>
    hMb _ (hHm c hc) _ (hHb c hc)
  obtain ⟨φ, hφm, hφB, hφ⟩ :=
    CFWPlan.Main.exists_bounded_density_of_functional μG Λ hB0 hΛadd hΛsmul hΛbdd
  refine ⟨φ, ⟨hφm, B, hφB⟩, fun q => ?_, fun C hC g => (hφB g).trans (hBle C hC),
    fun c hc => (hφ c hc).symm⟩
  -- a.e. right invariance
  obtain ⟨k, hk0, hk⟩ := integral_mul_right_haar (q : G)
  refine CFWPlan.Main.ae_eq_of_forall_integral_mul_eq μG
    (hφm.comp (measurable_mul_const _)).aestronglyMeasurable hφm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => hφB _) (Filter.Eventually.of_forall hφB) fun c hc => ?_
  set c' : G → ℝ := fun y => (k : ℝ) * c (y * (q : G)⁻¹) with hc'def
  have hc'int : Integrable c' μG := by
    refine Integrable.const_mul ?_ _
    rw [(hk fun y => c (y * (q : G)⁻¹)).2]
    simpa [mul_assoc] using hc
  have h1 : ∫ g, c g * φ (g * q) ∂μG = ∫ y, c' y * φ y ∂μG := by
    have := (hk fun y => c (y * (q : G)⁻¹) * φ y).1
    simp only [mul_inv_cancel_right] at this
    rw [this, ← integral_const_mul]
    simp only [hc'def, mul_assoc]
    rfl
  have h2 : H c' = fun p => H c (q * p) := by
    funext p
    have := (hk fun y => c (y * (q : G)⁻¹) * F (y * p)).1
    simp only [mul_inv_cancel_right] at this
    simp only [hHdef, hc'def, Subgroup.coe_mul, ← mul_assoc]
    rw [this, ← integral_const_mul]
    simp only [mul_assoc]
    rfl
  rw [h1, ← hφ c' hc'int, ← hφ c hc]
  simp only [hΛdef]
  rw [h2]
  exact (hMsm _ (hHm c hc) (hHbdd c hc)).2.2 q

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
/-- The functions `p ↦ ∫ c(g) F(g p) dg` on `P` are measurable and bounded. -/
theorem convol_props (P : Subgroup G) {F : G → ℝ} (hF : IsBddMeas F) {c : G → ℝ}
    (hc : Integrable c (Measure.haar : Measure G)) :
    (∀ p : P, Integrable (fun g => c g * F (g * p)) (Measure.haar : Measure G)) ∧
    Measurable (fun p : P => ∫ g, c g * F (g * p) ∂(Measure.haar : Measure G)) ∧
    ∃ C, ∀ p : P, |∫ g, c g * F (g * p) ∂(Measure.haar : Measure G)| ≤ C := by
  obtain ⟨hFm, B, hFB⟩ := hF
  set μG : Measure G := Measure.haar with hμGdef
  have hint : ∀ p : P, Integrable (fun g => c g * F (g * p)) μG :=
    fun p => hc.mul_bdd ((hFm.comp (measurable_mul_const (p : G))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun g => by rw [Real.norm_eq_abs]; exact hFB _)
  refine ⟨hint, ?_, B * ∫ g, |c g| ∂μG, fun p => ?_⟩
  · set c' := hc.1.mk c with hc'def
    have hc'm : StronglyMeasurable c' := hc.1.stronglyMeasurable_mk
    have heq : (fun p : P => ∫ g, c g * F (g * p) ∂μG) =
        fun p : P => ∫ g, c' g * F (g * p) ∂μG := by
      funext p
      refine integral_congr_ae ?_
      filter_upwards [hc.1.ae_eq_mk] with g hg
      rw [hg]
    rw [heq]
    refine (StronglyMeasurable.integral_prod_right (f := fun (p : P) (g : G) => c' g * F (g * p))
      ?_).measurable
    refine Measurable.stronglyMeasurable ?_
    exact (hc'm.measurable.comp measurable_snd).mul
      (hFm.comp (measurable_snd.mul (measurable_subtype_coe.comp measurable_fst)))
  · calc |∫ g, c g * F (g * p) ∂μG| ≤ ∫ g, |c g * F (g * p)| ∂μG := abs_integral_le_integral_abs
      _ ≤ ∫ g, B * |c g| ∂μG := by
          refine integral_mono (hint p).abs (hc.abs.const_mul B) fun g => ?_
          rw [abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hFB _) (abs_nonneg _)
      _ = B * ∫ g, |c g| ∂μG := integral_const_mul _ _

/-- **A `G`-equivariant positive conditional expectation onto right-`P`-invariant functions**
(the amenability of the `G`-space `G ⧸ P`, Zimmer [31], in the form needed here).
*Proof:* `isAmenableGroup_iff`, `exists_relative_density`, then `exists_strict_invariant_version`;
linearity, positivity,
unit, null-set congruence and modularity from the defining identity and
`ae_eq_of_forall_integral_mul_eq`; left `G`-equivariance by left invariance of Haar on `G`
(`measurePreserving_mul_left`). *Size:* 160. -/
theorem exists_equivariant_expectation (P : Subgroup G) (hP : IsClosed (P : Set G))
    [LocallyCompactSpace P] (hPamen : IsAmenableGroup P) :
    ∃ Φ : (G → ℝ) → G → ℝ,
      (∀ F, IsBddMeas F → IsBddMeas (Φ F) ∧ (∀ g (p : P), Φ F (g * p) = Φ F g) ∧
        ∀ C, (∀ g, |F g| ≤ C) → ∀ g, |Φ F g| ≤ C) ∧
      (∀ F F', IsBddMeas F → IsBddMeas F' →
        Φ (F + F') =ᵐ[(Measure.haar : Measure G)] Φ F + Φ F') ∧
      (∀ (c : ℝ) F, IsBddMeas F → Φ (c • F) =ᵐ[(Measure.haar : Measure G)] c • Φ F) ∧
      (∀ F, IsBddMeas F → (∀ g, 0 ≤ F g) → ∀ᵐ g ∂(Measure.haar : Measure G), 0 ≤ Φ F g) ∧
      Φ 1 =ᵐ[(Measure.haar : Measure G)] 1 ∧
      (∀ F F', IsBddMeas F → IsBddMeas F' → F =ᵐ[(Measure.haar : Measure G)] F' →
        Φ F =ᵐ[(Measure.haar : Measure G)] Φ F') ∧
      (∀ F u : G → ℝ, IsBddMeas F → IsBddMeas u → (∀ g (p : P), u (g * p) = u g) →
        Φ (u * F) =ᵐ[(Measure.haar : Measure G)] u * Φ F) ∧
      ∀ F (h : G), IsBddMeas F →
        Φ (fun g => F (h * g)) =ᵐ[(Measure.haar : Measure G)] fun g => Φ F (h * g) := by
  classical
  have : SecondCountableTopology P := TopologicalSpace.Subtype.secondCountableTopology (P : Set G)
  obtain ⟨M, hM⟩ := (isAmenableGroup_iff (P := P)).1 hPamen
  obtain ⟨Φ₀, hΦ₀⟩ := CFWPlan.Main.P6.exists_relative_density P M hM
  obtain ⟨hMadd, hMsm, hMone⟩ := hM
  set μG : Measure G := Measure.haar with hμGdef
  -- strictly invariant, clipped versions
  have hstrict : ∀ F : G → ℝ, IsBddMeas F → ∃ φ : G → ℝ, IsBddMeas φ ∧ (∀ g (p : P), φ (g * p) = φ g) ∧
      (∀ C, (∀ g, |F g| ≤ C) → ∀ g, |φ g| ≤ C) ∧ φ =ᵐ[μG] Φ₀ F := by
    intro F hF
    obtain ⟨h1, h2, h3, -⟩ := hΦ₀ F hF
    obtain ⟨ũ, hũ, hũinv, hũae⟩ := CFWPlan.Main.P6.exists_strict_invariant_version P h1 h2
    obtain ⟨-, C₀, hC₀⟩ := hF
    have hbdd : BddAbove (range fun g => |F g|) := ⟨C₀, by rintro _ ⟨g, rfl⟩; exact hC₀ g⟩
    set B : ℝ := ⨆ g, |F g| with hBdef
    have hFB : ∀ g, |F g| ≤ B := fun g => le_ciSup hbdd g
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hFB 1)
    refine ⟨fun g => max (-B) (min B (ũ g)), ⟨(measurable_const.max (measurable_const.min hũ.1)),
      B, fun g => ?_⟩, fun g p => by simp only [hũinv], fun C hC g => ?_, ?_⟩
    · rw [abs_le]
      constructor
      · exact le_max_left _ _
      · exact max_le (by linarith) (min_le_left _ _)
    · have hBC : B ≤ C := ciSup_le hC
      rw [abs_le]
      constructor
      · exact le_trans (by linarith) (le_max_left _ _)
      · exact max_le (by linarith) ((min_le_left _ _).trans hBC)
    · filter_upwards [hũae] with g hg
      rw [hg]
      have := h3 B hFB g
      rw [abs_le] at this
      rw [min_eq_right this.2, max_eq_right this.1]
  choose! Φ hΦ using hstrict
  -- uniqueness of densities
  have huniq : ∀ a b : G → ℝ, IsBddMeas a → IsBddMeas b →
      (∀ c, Integrable c μG → ∫ g, c g * a g ∂μG = ∫ g, c g * b g ∂μG) → a =ᵐ[μG] b := by
    rintro a b ⟨ham, Ca, hCa⟩ ⟨hbm, Cb, hCb⟩ h
    exact CFWPlan.Main.ae_eq_of_forall_integral_mul_eq μG ham.aestronglyMeasurable
      hbm.aestronglyMeasurable (C := max Ca Cb)
      (Filter.Eventually.of_forall fun g => (hCa g).trans (le_max_left _ _))
      (Filter.Eventually.of_forall fun g => (hCb g).trans (le_max_right _ _)) h
  have hint : ∀ c a : G → ℝ, Integrable c μG → IsBddMeas a → Integrable (fun g => c g * a g) μG := by
    rintro c a hc ⟨ham, Ca, hCa⟩
    exact hc.mul_bdd ham.aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => by rw [Real.norm_eq_abs]; exact hCa g)
  have hbddM : ∀ F : G → ℝ, IsBddMeas F → IsBddMeas (Φ₀ F) := fun F hF => (hΦ₀ F hF).1
  have hadd' : ∀ F F' : G → ℝ, IsBddMeas F → IsBddMeas F' → IsBddMeas (F + F') := by
    rintro F F' ⟨hm, C, hC⟩ ⟨hm', C', hC'⟩
    exact ⟨hm.add hm', C + C', fun g => (abs_add_le _ _).trans (add_le_add (hC g) (hC' g))⟩
  have hsmul' : ∀ (a : ℝ) (F : G → ℝ), IsBddMeas F → IsBddMeas (a • F) := by
    rintro a F ⟨hm, C, hC⟩
    refine ⟨hm.const_smul a, |a| * C, fun g => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hC g) (abs_nonneg a)
  have hmul' : ∀ u F : G → ℝ, IsBddMeas u → IsBddMeas F → IsBddMeas (u * F) := by
    rintro u F ⟨hm, C, hC⟩ ⟨hm', C', hC'⟩
    refine ⟨hm.mul hm', C * C', fun g => ?_⟩
    simp only [Pi.mul_apply, abs_mul]
    exact mul_le_mul (hC g) (hC' g) (abs_nonneg _) ((abs_nonneg _).trans (hC g))
  have hleft : ∀ (F : G → ℝ) (h : G), IsBddMeas F → IsBddMeas (fun g => F (h * g)) := by
    rintro F h ⟨hm, C, hC⟩
    exact ⟨hm.comp (measurable_const_mul h), C, fun g => hC _⟩
  have hbdd1 : IsBddMeas (1 : G → ℝ) := ⟨measurable_one, 1, fun g => by simp⟩
  -- transfer `Φ₀`-identities to `Φ`
  have hΦΦ₀ : ∀ F : G → ℝ, IsBddMeas F → Φ F =ᵐ[μG] Φ₀ F := fun F hF => (hΦ F hF).2.2.2
  refine ⟨Φ, fun F hF => ⟨(hΦ F hF).1, (hΦ F hF).2.1, (hΦ F hF).2.2.1⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- additivity
    intro F F' hF hF'
    have key : Φ₀ (F + F') =ᵐ[μG] Φ₀ F + Φ₀ F' := by
      refine huniq _ _ (hbddM _ (hadd' F F' hF hF')) (hadd' _ _ (hbddM F hF) (hbddM F' hF'))
        fun c hc => ?_
      obtain ⟨hi, hm, hb⟩ := convol_props P hF hc
      obtain ⟨hi', hm', hb'⟩ := convol_props P hF' hc
      rw [(hΦ₀ _ (hadd' F F' hF hF')).2.2.2 c hc]
      have : (fun p : P => ∫ g, c g * (F + F') (g * p) ∂μG) =
          (fun p : P => ∫ g, c g * F (g * p) ∂μG) + fun p : P => ∫ g, c g * F' (g * p) ∂μG := by
        funext p
        simp only [Pi.add_apply, mul_add]
        exact integral_add (hi p) (hi' p)
      rw [this, (hMadd _ _ hm hm' hb hb').1, ← (hΦ₀ F hF).2.2.2 c hc,
        ← (hΦ₀ F' hF').2.2.2 c hc, ← integral_add (hint c _ hc (hbddM F hF))
        (hint c _ hc (hbddM F' hF'))]
      simp only [Pi.add_apply, mul_add]
    filter_upwards [hΦΦ₀ _ (hadd' F F' hF hF'), hΦΦ₀ F hF, hΦΦ₀ F' hF', key] with g h1 h2 h3 h4
    simp only [Pi.add_apply] at h4 ⊢
    rw [h1, h2, h3, h4]
  · -- homogeneity
    intro a F hF
    have key : Φ₀ (a • F) =ᵐ[μG] a • Φ₀ F := by
      refine huniq _ _ (hbddM _ (hsmul' a F hF)) (hsmul' a _ (hbddM F hF)) fun c hc => ?_
      obtain ⟨hi, hm, hb⟩ := convol_props P hF hc
      rw [(hΦ₀ _ (hsmul' a F hF)).2.2.2 c hc]
      have : (fun p : P => ∫ g, c g * (a • F) (g * p) ∂μG) =
          a • fun p : P => ∫ g, c g * F (g * p) ∂μG := by
        funext p
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [← integral_const_mul]
        congr 1
        funext g
        ring
      rw [this, (hMsm _ hm hb).1 a, ← (hΦ₀ F hF).2.2.2 c hc, ← integral_const_mul]
      congr 1
      funext g
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    filter_upwards [hΦΦ₀ _ (hsmul' a F hF), hΦΦ₀ F hF, key] with g h1 h2 h3
    simp only [Pi.smul_apply] at h3 ⊢
    rw [h1, h2, h3]
  · -- positivity
    intro F hF hpos
    have key : 0 ≤ᵐ[μG] Φ₀ F := by
      obtain ⟨hφm, Cφ, hCφ⟩ := hbddM F hF
      refine ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite (fun s hs hμs => ?_)
        fun s hs hμs => ?_
      · exact Measure.integrableOn_of_bounded (M := Cφ) hμs.ne hφm.aestronglyMeasurable
          (Filter.Eventually.of_forall fun g => by rw [Real.norm_eq_abs]; exact hCφ g)
      · have hc : Integrable (s.indicator (1 : G → ℝ)) μG :=
          (integrable_indicator_iff hs).2 (integrableOn_const hμs.ne)
        obtain ⟨hi, hm, hb⟩ := convol_props P hF hc
        have h1 := (hΦ₀ F hF).2.2.2 _ hc
        rw [← integral_indicator hs]
        have : (fun g => s.indicator (Φ₀ F) g) = fun g => s.indicator 1 g * Φ₀ F g := by
          funext g
          by_cases hg : g ∈ s <;> simp [hg]
        rw [this, h1]
        refine (hMsm _ hm hb).2.1 fun p => integral_nonneg fun g => ?_
        exact mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _) (hpos _)
    filter_upwards [hΦΦ₀ F hF, key] with g h1 h2
    rw [h1]
    exact h2
  · -- unit
    have key : Φ₀ 1 =ᵐ[μG] 1 := by
      refine huniq _ _ (hbddM 1 hbdd1) hbdd1 fun c hc => ?_
      rw [(hΦ₀ 1 hbdd1).2.2.2 c hc]
      have : (fun p : P => ∫ g, c g * (1 : G → ℝ) (g * p) ∂μG) =
          (∫ g, c g ∂μG) • (1 : P → ℝ) := by
        funext p
        simp
      rw [this, (hMsm 1 measurable_one ⟨1, fun x => by simp⟩).1, hMone]
      simp
    filter_upwards [hΦΦ₀ 1 hbdd1, key] with g h1 h2
    rw [h1, h2]
  · -- null-set congruence
    intro F F' hF hF' hFF
    have key : Φ₀ F =ᵐ[μG] Φ₀ F' := by
      refine huniq _ _ (hbddM F hF) (hbddM F' hF') fun c hc => ?_
      rw [(hΦ₀ F hF).2.2.2 c hc, (hΦ₀ F' hF').2.2.2 c hc]
      congr 1
      funext p
      refine integral_congr_ae ?_
      have := (quasiMeasurePreserving_mul_right μG (p : G)).ae_eq_comp hFF
      filter_upwards [this] with g hg
      simp only [comp_apply] at hg
      rw [hg]
    filter_upwards [hΦΦ₀ F hF, hΦΦ₀ F' hF', key] with g h1 h2 h3
    rw [h1, h2, h3]
  · -- modularity
    intro F u hF hu huinv
    have key : Φ₀ (u * F) =ᵐ[μG] u * Φ₀ F := by
      refine huniq _ _ (hbddM _ (hmul' u F hu hF)) (hmul' u _ hu (hbddM F hF)) fun c hc => ?_
      have hcu : Integrable (fun g => c g * u g) μG := hint c u hc hu
      rw [(hΦ₀ _ (hmul' u F hu hF)).2.2.2 c hc]
      have : (fun p : P => ∫ g, c g * (u * F) (g * p) ∂μG) =
          fun p : P => ∫ g, (fun g => c g * u g) g * F (g * p) ∂μG := by
        funext p
        congr 1
        funext g
        simp only [Pi.mul_apply, huinv]
        ring
      rw [this, ← (hΦ₀ F hF).2.2.2 _ hcu]
      congr 1
      funext g
      simp only [Pi.mul_apply]
      ring
    filter_upwards [hΦΦ₀ _ (hmul' u F hu hF), hΦΦ₀ F hF, key] with g h1 h2 h3
    simp only [Pi.mul_apply] at h3 ⊢
    rw [h1, h2, h3]
  · -- left equivariance
    intro F h hF
    have key : Φ₀ (fun g => F (h * g)) =ᵐ[μG] fun g => Φ₀ F (h * g) := by
      refine huniq _ _ (hbddM _ (hleft F h hF)) (hleft _ h (hbddM F hF)) fun c hc => ?_
      have hch : Integrable (fun g => c (h⁻¹ * g)) μG := hc.comp_mul_left h⁻¹
      rw [(hΦ₀ _ (hleft F h hF)).2.2.2 c hc]
      have : (fun p : P => ∫ g, c g * F (h * (g * p)) ∂μG) =
          fun p : P => ∫ g, c (h⁻¹ * g) * F (g * p) ∂μG := by
        funext p
        rw [← integral_mul_left_eq_self (μ := μG) (fun g => c (h⁻¹ * g) * F (g * p)) h]
        simp only [inv_mul_cancel_left, mul_assoc]
      rw [this, ← (hΦ₀ F hF).2.2.2 _ hch,
        ← integral_mul_left_eq_self (μ := μG) (fun g => c (h⁻¹ * g) * Φ₀ F g) h]
      simp only [inv_mul_cancel_left]
    have hqmp := (measurePreserving_mul_left μG h).quasiMeasurePreserving
    filter_upwards [hΦΦ₀ _ (hleft F h hF), hqmp.ae_eq_comp (hΦΦ₀ F hF), key] with g h1 h2 h3
    simp only [comp_apply] at h2
    rw [h1, h2, h3]

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
/-- **Zimmer = milestone `isAmenableRel_orbit_quotient_of_isAmenableGroup`** (external: Zimmer
[31]; CFW p. 446). *Proof:* `κ` from `exists_equivariant_index`, `Φ` from
`exists_equivariant_expectation`; for `f` bounded measurable on the orbit relation put
`F_f (g) = f (gP, κ(g)⁻¹ • gP)` and `P_rel f = ` the descent (`exists_descent`) of `Φ F_f`. Each
`Monod.IsLeftInvariantMean` field is an a.e. statement on `G ⧸ P`, transferred to `G` through
`hν` (on measurable hulls); invariance: a partial transformation is `y ↦ γ • y` on countably many
Borel pieces (`γ ∈ Γ`), on which `F_{f^φ} = F_f (γ⁻¹ ·)` (equivariance of `κ`), then modularity
(pieces are right-`P`-invariant) and `G`-equivariance of `Φ`. *Size:* 300. -/
theorem zimmer (P : Subgroup G) (hP : IsClosed (P : Set G))
    [LocallyCompactSpace P] (hPamen : IsAmenableGroup P) (Γ : Subgroup G) [DiscreteTopology Γ]
    [MeasurableSpace (G ⧸ P)] [BorelSpace (G ⧸ P)]
    (ν : Measure (G ⧸ P)) [IsFiniteMeasure ν]
    (hν : ∀ A : Set (G ⧸ P), MeasurableSet A →
      (ν A = 0 ↔ Measure.haar ((QuotientGroup.mk : G → G ⧸ P) ⁻¹' A) = 0)) :
    Monod.IsAmenableRel ν {p : (G ⧸ P) × (G ⧸ P) | ∃ γ ∈ Γ, γ • p.1 = p.2} := by
  classical
  have : IsClosed (P : Set G) := hP
  have hΓc : Countable Γ := CFWPlan.Main.P6.countable_of_discrete_subgroup Γ
  set R : Set ((G ⧸ P) × (G ⧸ P)) := {p | ∃ γ ∈ Γ, γ • p.1 = p.2} with hRdef
  have hReq : Equivalence fun x y => (x, y) ∈ R :=
    (CFWPlan.Main.P6.isDiscreteMeasured_orbit P hP Γ ν hν).equivalence
  set π : G → G ⧸ P := QuotientGroup.mk with hπdef
  have hπm : Measurable π := QuotientGroup.continuous_mk.measurable
  have hsm : ∀ γ : G, Measurable (fun y : G ⧸ P => γ • y) := fun γ =>
    (continuous_const_smul γ).measurable
  have hπγ : ∀ (γ g : G), π (γ * g) = γ • π g := fun _ _ => rfl
  have hπP : ∀ g (p : P), π (g * p) = π g := fun g p =>
    (QuotientGroup.eq.2 (by simp)).symm
  obtain ⟨κ, hκm, hκ⟩ := CFWPlan.Main.P6.exists_equivariant_index Γ
  obtain ⟨Φ, hΦ1, hΦadd, hΦsmul, hΦnn, hΦone, hΦcongr, hΦmod, hΦeq⟩ :=
    CFWPlan.Main.P6.exists_equivariant_expectation P hP hPamen
  set μG : Measure G := Measure.haar with hμGdef
  -- the lift `F f (g) = f (gP, κ(g)⁻¹ gP)`
  set F : ((G ⧸ P) × (G ⧸ P) → ℝ) → G → ℝ :=
    fun f g => f (π g, (((κ g)⁻¹ : Γ) : G) • π g) with hFdef
  have hFR : ∀ g, (π g, (((κ g)⁻¹ : Γ) : G) • π g) ∈ R := fun g =>
    ⟨_, ((κ g)⁻¹ : Γ).2, rfl⟩
  have hFm : ∀ f, Measurable f → Measurable (F f) := by
    intro f hf
    have : Measurable (fun q : G × Γ => f (π q.1, (((q.2)⁻¹ : Γ) : G) • π q.1)) :=
      measurable_from_prod_countable_left fun γ =>
        (hf.comp (hπm.prodMk ((hsm _).comp hπm)) :
          Measurable fun x => f (π x, (((γ)⁻¹ : Γ) : G) • π x))
    exact this.comp (measurable_id.prodMk hκm)
  have hFb : ∀ f, Monod.IsBddMeasOn R f → IsBddMeas (F f) := by
    rintro f ⟨hf, C, hC⟩
    exact ⟨hFm f hf, C, fun g => hC _ (hFR g)⟩
  have hFγ : ∀ f (γ : Γ) g,
      F f ((γ : G) * g) = f ((γ : G) • π g, (((κ g)⁻¹ : Γ) : G) • π g) := by
    intro f γ g
    simp only [hFdef, hκ, hπγ, mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv, mul_smul,
      inv_smul_smul]
  -- the mean, by descent
  have hdesc : ∀ f : (G ⧸ P) × (G ⧸ P) → ℝ, ∃ v : G ⧸ P → ℝ, Monod.IsBddMeasOn R f →
      Measurable v ∧ ∀ g, v (π g) = Φ (F f) g := by
    intro f
    by_cases hf : Monod.IsBddMeasOn R f
    · have h1 := hΦ1 (F f) (hFb f hf)
      obtain ⟨v, hv, hvg⟩ := CFWPlan.Main.P6.exists_descent P hP h1.1.1 h1.2.1
      exact ⟨v, fun _ => ⟨hv, hvg⟩⟩
    · exact ⟨0, fun h => absurd h hf⟩
  choose Pr hPr using hdesc
  -- transfer from Haar measure on `G` to `ν`
  have htr : ∀ S : Set (G ⧸ P), MeasurableSet S → (∀ᵐ g ∂μG, π g ∈ S) → ∀ᵐ y ∂ν, y ∈ S := by
    intro S hS h
    rw [ae_iff] at h ⊢
    exact (hν Sᶜ hS.compl).2 h
  have htr_eq : ∀ a b : G ⧸ P → ℝ, Measurable a → Measurable b →
      (∀ᵐ g ∂μG, a (π g) = b (π g)) → a =ᵐ[ν] b := fun a b ha hb h =>
    htr {y | a y = b y} (measurableSet_eq_fun ha hb) h
  have hbdd_add : ∀ f f', Monod.IsBddMeasOn R f → Monod.IsBddMeasOn R f' → Monod.IsBddMeasOn R (f + f') := by
    rintro f f' ⟨hf, C, hC⟩ ⟨hf', C', hC'⟩
    refine ⟨hf.add hf', C + C', fun p hp => ?_⟩
    simp only [Pi.add_apply]
    exact (abs_add_le _ _).trans (add_le_add (hC p hp) (hC' p hp))
  have hbdd_smul : ∀ (c : ℝ) f, Monod.IsBddMeasOn R f → Monod.IsBddMeasOn R (c • f) := by
    rintro c f ⟨hf, C, hC⟩
    refine ⟨hf.const_smul c, |c| * C, fun p hp => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hC p hp) (abs_nonneg c)
  have hbdd_one : Monod.IsBddMeasOn R 1 := ⟨measurable_const, 1, fun p _ => by simp⟩
  have hbdd1G : IsBddMeas (1 : G → ℝ) := ⟨measurable_const, 1, fun g => by simp⟩
  have hΦzero : Φ 0 =ᵐ[μG] 0 := by
    have h := hΦsmul 0 1 hbdd1G
    rw [zero_smul, zero_smul] at h
    exact h
  refine ⟨Pr, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact fun f hf => ((hPr f) hf).1.aemeasurable
  · intro f f' hf hf' hnull
    obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null hnull
    have hFF : F f =ᵐ[μG] F f' := by
      rw [Filter.EventuallyEq, ae_iff]
      refine measure_mono_null (fun g hg => ?_) ((hν N hNm).1 hN0)
      exact hNsub ⟨(π g, (((κ g)⁻¹ : Γ) : G) • π g), ⟨hg, hFR g⟩, rfl⟩
    have h := hΦcongr _ _ (hFb f hf) (hFb f' hf') hFF
    refine htr_eq _ _ (hPr f hf).1 (hPr f' hf').1 ?_
    filter_upwards [h] with g hg
    rw [(hPr f hf).2, (hPr f' hf').2, hg]
  · intro f f' hf hf'
    have h := hΦadd _ _ (hFb f hf) (hFb f' hf')
    refine htr_eq _ _ (hPr _ (hbdd_add f f' hf hf')).1 ((hPr f hf).1.add (hPr f' hf').1) ?_
    filter_upwards [h] with g hg
    simp only [Pi.add_apply]
    rw [(hPr _ (hbdd_add f f' hf hf')).2, (hPr f hf).2, (hPr f' hf').2]
    exact hg
  · intro c f hf
    have h := hΦsmul c _ (hFb f hf)
    refine htr_eq _ _ (hPr _ (hbdd_smul c f hf)).1 ((hPr f hf).1.const_smul c) ?_
    filter_upwards [h] with g hg
    simp only [Pi.smul_apply]
    rw [(hPr _ (hbdd_smul c f hf)).2, (hPr f hf).2]
    exact hg
  · intro f hf hpos
    have h := hΦnn _ (hFb f hf) (fun g => hpos _ (hFR g))
    refine htr {y | 0 ≤ Pr f y} (measurableSet_le measurable_const (hPr f hf).1) ?_
    filter_upwards [h] with g hg
    show 0 ≤ Pr f (π g)
    rw [(hPr f hf).2]
    exact hg
  · refine htr_eq _ _ (hPr 1 hbdd_one).1 measurable_const ?_
    filter_upwards [hΦone] with g hg
    rw [(hPr 1 hbdd_one).2]
    exact hg
  · intro φ f hf
    -- the total inverse `ψ` of `φ`
    set ψ : G ⧸ P → G ⧸ P := fun y =>
      if h : y ∈ φ.cod then (φ.e.symm ⟨y, h⟩ : G ⧸ P) else y with hψdef
    have hψm : Measurable ψ := Measurable.dite
      (measurable_subtype_coe.comp φ.e.symm.measurable) measurable_subtype_coe
      φ.measurableSet_cod
    have hψR : ∀ y ∈ φ.cod, (ψ y, y) ∈ R := by
      intro y hy
      have := φ.graph_subset (φ.e.symm ⟨y, hy⟩)
      rw [MeasurableEquiv.apply_symm_apply] at this
      simpa only [hψdef, hy, dif_pos] using this
    have hsR : φ.shiftRel f = fun p => if p.1 ∈ φ.cod then f (ψ p.1, p.2) else 0 := by
      funext p
      simp only [Monod.PartialTransformation.shiftRel, hψdef]
      split_ifs <;> rfl
    have hsB : φ.shiftBase (Pr f) = fun y => if y ∈ φ.cod then Pr f (ψ y) else 0 := by
      funext y
      simp only [Monod.PartialTransformation.shiftBase, hψdef]
      split_ifs <;> rfl
    obtain ⟨hfm, C, hC⟩ := hf
    have hbddS : Monod.IsBddMeasOn R (φ.shiftRel f) := by
      refine ⟨?_, C, ?_⟩
      · rw [hsR]
        exact Measurable.ite (φ.measurableSet_cod.preimage measurable_fst)
          (hfm.comp ((hψm.comp measurable_fst).prodMk measurable_snd)) measurable_const
      · rintro ⟨y, x⟩ hyx
        rw [hsR]
        dsimp only
        split_ifs with hy
        · exact hC _ (hReq.trans (hψR y hy) hyx)
        · rw [abs_zero]
          exact (abs_nonneg _).trans (hC _ (hReq.refl y))
    have hf : Monod.IsBddMeasOn R f := ⟨hfm, C, hC⟩
    -- the pieces of `cod φ` on which `φ⁻¹` is a fixed `γ ∈ Γ`
    set Cγ : Γ → Set (G ⧸ P) := fun γ => φ.cod ∩ {y | ψ y = (γ : G) • y} with hCγdef
    have hCγm : ∀ γ, MeasurableSet (Cγ γ) := fun γ =>
      φ.measurableSet_cod.inter (measurableSet_eq_fun hψm (hsm γ))
    have hcov : ∀ y ∈ φ.cod, ∃ γ : Γ, y ∈ Cγ γ := by
      intro y hy
      obtain ⟨γ, hγ, h⟩ := hψR y hy
      refine ⟨(⟨γ, hγ⟩ : Γ)⁻¹, hy, ?_⟩
      show ψ y = (γ⁻¹ : G) • y
      exact eq_inv_smul_iff.2 h
    -- indicators of saturated sets are right-`P`-invariant
    have hind : ∀ S : Set (G ⧸ P), MeasurableSet S →
        IsBddMeas ((π ⁻¹' S).indicator (1 : G → ℝ)) ∧
          ∀ g (p : P), (π ⁻¹' S).indicator (1 : G → ℝ) (g * p) =
            (π ⁻¹' S).indicator (1 : G → ℝ) g := by
      intro S hS
      refine ⟨⟨measurable_const.indicator (hπm hS), 1, fun g => ?_⟩, fun g p => ?_⟩
      · by_cases hg : g ∈ π ⁻¹' S <;> simp [hg]
      · simp only [indicator, mem_preimage, hπP, Pi.one_apply]
    have hFS := hFb _ hbddS
    have hFf := hFb f hf
    -- on `π⁻¹ (C γ)`
    have hpiece : ∀ γ : Γ, ∀ᵐ g ∂μG, π g ∈ Cγ γ →
        Φ (F (φ.shiftRel f)) g = Pr f (ψ (π g)) := by
      intro γ
      obtain ⟨hIb, hIinv⟩ := hind _ (hCγm γ)
      set I := (π ⁻¹' Cγ γ).indicator (1 : G → ℝ) with hIdef
      have hFγb : IsBddMeas (fun g => F f ((γ : G) * g)) := by
        obtain ⟨hm, D, hD⟩ := hFf
        exact ⟨hm.comp (measurable_const_mul _), D, fun g => hD _⟩
      have heq : I * F (φ.shiftRel f) = I * fun g => F f ((γ : G) * g) := by
        funext g
        simp only [Pi.mul_apply, hIdef, indicator, mem_preimage]
        split_ifs with hg
        · rw [hFγ]
          simp only [hFdef, hsR, hg.1, if_true, Pi.one_apply, one_mul]
          rw [hg.2]
        · simp
      have h1 := hΦmod _ _ hFS hIb hIinv
      have h2 := hΦmod _ _ hFγb hIb hIinv
      have h3 := hΦeq (F f) (γ : G) hFf
      filter_upwards [h1, h2, h3] with g hg1 hg2 hg3 hgC
      have hIg : I g = 1 := by simp [hIdef, hgC]
      simp only [Pi.mul_apply, hIg, one_mul] at hg1 hg2
      rw [← hg1, heq, hg2, hg3, ← (hPr f hf).2, hπγ, hgC.2]
    -- off `π⁻¹ (cod φ)`
    have hoff : ∀ᵐ g ∂μG, π g ∉ φ.cod → Φ (F (φ.shiftRel f)) g = 0 := by
      obtain ⟨hIb, hIinv⟩ := hind _ φ.measurableSet_cod.compl
      set I := (π ⁻¹' φ.codᶜ).indicator (1 : G → ℝ) with hIdef
      have heq : I * F (φ.shiftRel f) = 0 := by
        funext g
        simp only [Pi.mul_apply, hIdef, indicator, mem_preimage, Pi.zero_apply]
        split_ifs with hg
        · simp only [hFdef, hsR, if_neg (show π g ∉ φ.cod from hg), mul_zero]
        · simp
      have h1 := hΦmod _ _ hFS hIb hIinv
      filter_upwards [h1, hΦzero] with g hg1 hg0 hgC
      have hIg : I g = 1 := by simp [hIdef, hgC]
      simp only [Pi.mul_apply, hIg, one_mul] at hg1
      rw [← hg1, heq, hg0]
      rfl
    have hall := ae_all_iff.2 hpiece
    rw [hsB]
    refine htr_eq _ _ (hPr _ hbddS).1
      (Measurable.ite φ.measurableSet_cod ((hPr f hf).1.comp hψm) measurable_const) ?_
    filter_upwards [hall, hoff] with g hg hg'
    rw [(hPr _ hbddS).2]
    by_cases hgc : π g ∈ φ.cod
    · obtain ⟨γ, hγ⟩ := hcov _ hgc
      rw [if_pos hgc]
      exact hg γ hγ
    · rw [if_neg hgc]
      exact hg' hgc

end CFWPlan.Main.P6
end

section
open MeasureTheory Set Function Filter Topology
open scoped ENNReal NNReal
namespace CFWPlan.Main
open ConnesFeldmanWeiss
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
alias zimmer := CFWPlan.Main.P6.zimmer

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
theorem solution {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (P : Subgroup G) (hP : IsClosed (P : Set G))
    [LocallyCompactSpace P] (hPamen : IsAmenableGroup P) (Γ : Subgroup G) [DiscreteTopology Γ]
    [MeasurableSpace (G ⧸ P)] [BorelSpace (G ⧸ P)]
    (ν : MeasureTheory.Measure (G ⧸ P)) [MeasureTheory.IsFiniteMeasure ν]
    (hν : ∀ A : Set (G ⧸ P), MeasurableSet A →
      (ν A = 0 ↔ MeasureTheory.Measure.haar ((QuotientGroup.mk : G → G ⧸ P) ⁻¹' A) = 0)) :
    Monod.IsAmenableRel ν {p : (G ⧸ P) × (G ⧸ P) | ∃ γ ∈ Γ, γ • p.1 = p.2} :=
  zimmer P hP hPamen Γ ν hν
end
