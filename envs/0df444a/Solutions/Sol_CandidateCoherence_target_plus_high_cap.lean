-- Prove2me | solution 1 for CandidateCoherence.target_plus_high_cap
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-25T22:39:45.258591+00:00
-- url     : https://prove2.me/submissions/c52f408b-931c-47f0-9f47-3e671971579d

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Linarith
import Definitions.Def_Sensitivity213303_CandidateCoherence
import Definitions.Def_Sensitivity213303_TournamentHighRows

namespace MinmaxLocal
end MinmaxLocal
namespace TournamentHighRows
end TournamentHighRows
section
/-
The graded-target to labeling-exclusion bridge.

Targets at different rows may use different lower thresholds. A geometric
one-child candidate has an accepted partner; coloring its row by the other
position makes every label mismatch an actual guard failure. This argument
is independent of fixed versus graded targets and applies to min/max targets.
-/


set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CandidateCoherence
open scoped Classical
open MinmaxLocal TournamentHighRows

variable {N : ℕ} {V X : Type}

















theorem mismatch_mono (R : V → V → Prop) (ell : V → V → Bool)
    (T U : Finset V) (hTU : T ⊆ U) (color : V → Bool) (v : V) :
    mismatch R ell T color v ⊆ mismatch R ell U color v := by
  classical
  intro w hw
  rcases Finset.mem_filter.mp hw with ⟨hwT,hw⟩
  exact Finset.mem_filter.mpr ⟨hTU hwT,hw⟩

theorem ordinaryGood_mono (R : V → V → Prop) (ell : V → V → Bool)
    (T U : Finset V) (hTU : T ⊆ U) (q : ℕ) (color : V → Bool)
    (hU : OrdinaryGood R ell U q color) : OrdinaryGood R ell T q color := by
  intro v hv
  exact (Finset.card_le_card (mismatch_mono R ell T U hTU color v)).trans (hU v (hTU hv))

theorem ordinary_card_lt (R : V → V → Prop) (ell : V → V → Bool)
    (q a : ℕ) (hexcl : NoOrdinary R ell q a)
    (T : Finset V) (color : V → Bool) (hT : OrdinaryGood R ell T q color) : T.card < a := by
  classical
  by_contra hn
  have ha : a ≤ T.card := Nat.le_of_not_gt hn
  obtain ⟨U,hUT,hUa⟩ := Finset.exists_subset_card_eq ha
  exact hexcl U hUa color (ordinaryGood_mono R ell U T hUT q color hT)

section ActualGuards
variable [Fintype V]

/-- Each label mismatch enters the actual selected-child failure set. -/
theorem mismatch_subset_failures (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X)
    (T : Finset V) (color : V → Bool)
    (hpartner : ∀ w ∈ T, ∀ b : Bool, b ≠ color w → P (children w b)) (v : V) :
    mismatch R ell T color v ⊆ guardFailures R ell P children v := by
  classical
  intro w hw
  rcases Finset.mem_filter.mp hw with ⟨hwT,hvw,hlabel⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ w,hvw,hpartner w hwT (ell v w) hlabel⟩

/-- Actual guard budgets imply ordinary coherence for any partner-valid coloring. -/
theorem ordinaryGood_of_actual_guards (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X)
    (T : Finset V) (q : ℕ) (color : V → Bool)
    (hpartner : ∀ w ∈ T, ∀ b : Bool, b ≠ color w → P (children w b))
    (hbudget : ∀ v ∈ T, (guardFailures R ell P children v).card ≤ q) :
    OrdinaryGood R ell T q color := by
  intro v hv
  exact (Finset.card_le_card (mismatch_subset_failures R ell P children T color hpartner v)).trans
    (hbudget v hv)







end ActualGuards
end CandidateCoherence







end

section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace CandidateCoherence
end CandidateCoherence
open CandidateCoherence
open scoped Classical
open MinmaxLocal TournamentHighRows
variable {N : ℕ} {V X : Type}
variable [Fintype V]

/-- Adjoin disjoint high rows of the same failure budget using arbitrary
    colors on those rows. This is the first strengthened prefix cap. -/
theorem solution (R : V → V → Prop) (ell : V → V → Bool)
    (P : X → Prop) (children : V → Bool → X)
    (T H : Finset V) (hdisjoint : Disjoint T H) (q a : ℕ)
    (hexcl : NoOrdinary R ell q a) (color : V → Bool)
    (hpartner : ∀ w ∈ T, ∀ b : Bool, b ≠ color w → P (children w b))
    (hhigh : ∀ w ∈ H, ∀ b : Bool, P (children w b))
    (hbudgetT : ∀ v ∈ T, (guardFailures R ell P children v).card ≤ q)
    (hbudgetH : ∀ v ∈ H, (guardFailures R ell P children v).card ≤ q) :
    T.card + H.card < a := by
  classical
  let extended : V → Bool := fun w => if w ∈ T then color w else false
  have hp : ∀ w ∈ T ∪ H, ∀ b : Bool, b ≠ extended w → P (children w b) := by
    intro w hw b hb
    by_cases hwT : w ∈ T
    · have hn : b ≠ color w := by simpa only [extended, if_pos hwT] using hb
      exact hpartner w hwT b hn
    · exact hhigh w ((Finset.mem_union.mp hw).resolve_left hwT) b
  have hb : ∀ v ∈ T ∪ H, (guardFailures R ell P children v).card ≤ q := by
    intro v hv
    exact (Finset.mem_union.mp hv).elim (hbudgetT v) (hbudgetH v)
  have hgood := ordinaryGood_of_actual_guards R ell P children (T ∪ H) q extended hp hb
  have hcard := ordinary_card_lt R ell q a hexcl (T ∪ H) extended hgood
  rwa [Finset.card_union_of_disjoint hdisjoint] at hcard
end
