-- Prove2me | solution 1 for Freiman.lower_h5_bindings_a
-- status  : ACCEPTED   (prove)
-- author  : @Marac
-- created : 2026-09-11T22:37:11.769411+00:00
-- url     : https://prove2.me/submissions/f7c44ab3-3946-45cd-98e1-e4163e0bc996

import Definitions.Def_Freiman_lowerH5Verification
import Definitions.Def_Freiman_lowerInitialEntry
import Mathlib.Tactic

open Freiman

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem lower_h5_forall_getElem?_iff {α β : Type} (l : List (α × β)) (Q : ℕ → α → β → Prop) :
    (∀ bi : ℕ, ∀ cs g, l[bi]? = some (cs,g) → Q bi cs g) ↔
      ∀ bi ∈ List.range l.length, ∀ x ∈ (l[bi]?).toList, Q bi x.1 x.2 := by
  constructor
  · intro h bi _ x hx
    simp only [Option.mem_toList, Option.mem_def] at hx
    exact h bi x.1 x.2 hx
  · intro h bi cs g hbi
    have hlt : bi < l.length := (List.getElem?_eq_some_iff.mp hbi).1
    exact h bi (List.mem_range.mpr hlt) (cs,g) (by simp [hbi])

local instance instDecLowerH5RecordBinding (c : LowerH5Case) (r : LowerH5Record) :
    Decidable (LowerH5RecordBinding c r) :=
  decidable_of_iff (r.caseId = c.id ∧ (0 < r.witness ∧ r.witness ≤ lowerH5Witnesses.length) ∧
    (∀ i ∈ r.bounds, 0 < i ∧ i ≤ lowerH5Bounds.length) ∧
    (lowerH5RecordBounds r).toFinset = (lowerH5Residual c r.branch).toFinset ∧
    (lowerH5Witness r.witness).lowerBound ∈ lowerH5RecordBounds r ∧
    (lowerH5Witness r.witness).upperBound ∈ lowerH5RecordBounds r ∧
    (lowerH5Witness r.witness).rectangle = c.rectangle)
    ⟨fun ⟨a,b,c,d,e,f,g⟩ => ⟨a,b,c,d,e,f,g⟩, fun ⟨a,b,c,d,e,f,g⟩ => ⟨a,b,c,d,e,f,g⟩⟩

/-- Boolean-friendly restatement of `lowerH5CaseBinding` whose third conjunct is
phrased as a bounded `List.range` scan instead of a raw `∀ bi : ℕ, ...`, so that
Lean's automatic `Decidable` synthesis (which cannot see through the `structure`
`LowerH5RecordBinding` or an un-bounded `∀ bi : ℕ`) can find an instance via the
explicit local instance above together with the finite scan machinery. -/
def lowerH5CaseBindingB (c : LowerH5Case) : Prop :=
  lowerH5CaseShape c ∧
  (∀ r ∈ lowerH5RecordsFor c, LowerH5RecordBinding c r) ∧
  (∀ bi ∈ List.range (lowerH5Comparisons c).length, ∀ x ∈ ((lowerH5Comparisons c)[bi]?).toList,
    x.2 ≠ .automatic → (∃ r ∈ lowerH5RecordsFor c, r.branch = bi) ∨ (lowerH5Exceptional c ∧ bi=5)) ∧
  ((lowerH5Comparisons c).filter (fun z => match z.2 with | .automatic => true | _ => false)).length = c.automatic

theorem lowerH5CaseBindingB_imp (c : LowerH5Case) : lowerH5CaseBindingB c → lowerH5CaseBinding c := by
  intro ⟨h1,h2,h3,h4⟩
  refine ⟨h1,h2,?_,h4⟩
  exact (lower_h5_forall_getElem?_iff (lowerH5Comparisons c)
    (fun bi _ g => g ≠ .automatic → (∃ r ∈ lowerH5RecordsFor c, r.branch = bi) ∨
      (lowerH5Exceptional c ∧ bi=5))).mpr h3

local instance instDecLowerH5CaseBindingB (c : LowerH5Case) : Decidable (lowerH5CaseBindingB c) := by
  unfold lowerH5CaseBindingB lowerH5CaseShape lowerH5Exceptional
  infer_instance

theorem solution (hc : lowerH5CatalogValid) :
    ∀ c ∈ lowerH5Cases, c.kind = .a → lowerH5CaseBinding c := by
  clear hc
  have h : ∀ c ∈ lowerH5Cases, c.kind = .a → lowerH5CaseBindingB c := by decide +kernel
  intro c hcin hkind
  exact lowerH5CaseBindingB_imp c (h c hcin hkind)
