-- Prove2me | solution 1 for BunkbedAux.exists_unique_partition_state
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-09-12T03:59:11.293869+00:00
-- url     : https://prove2.me/submissions/18d7a6bc-4384-45a3-9f8b-81ce059a7119

import Definitions.Def_BunkbedHypergraph
import Theorems.Thm_BunkbedAux_partition_sum_eq_total
import Theorems.Thm_BunkbedAux_sum_weight_eq_one

/-!
# A gadget copy induces the five-state Wierman–Ziff distribution on its attachment triple

The five partition probabilities `Pabc, Pab_c, Pac_b, Pa_bc, Pa_b_c` of
`Def_BunkbedPercolation` are the probabilities of five events describing which pairs among
`(a, b, c)` are connected.  This file proves the *event-level* facts that the substitution
argument actually needs:

* `PartEvent` packages the five predicates **verbatim** as they occur in those five
  definitions, indexed by the matching `WZ` state;
* `wzStateOf S a b c` is the (computable) WZ state induced by the configuration `S`;
* `solution` : for every configuration `S` there is **exactly one** `s : WZ` with
  `PartEvent s S a b c` — i.e. the five events are pairwise mutually exclusive and jointly
  exhaustive.  Equivalently (`partEvent_iff_state`) `PartEvent s S a b c ↔ wzStateOf S a b c = s`,
  so the five events are precisely the fibres of the state map, hence in bijection with the
  five partitions of `{a, b, c}` into reachability classes;
* `prob_state_eq` : the probability that the induced state is `s` is exactly the corresponding
  partition probability, so the induced law on `WZ` **is** the tuple
  `(Pabc, Pab_c, Pac_b, Pa_bc, Pa_b_c)`;
* `sum_partProb` / `sum_prob_state` : that law has total mass `1` (unconditionally in `w`), and
  `partProb_nonneg` : it is nonnegative as soon as `w` takes values in `[0,1]`, so it is a genuine
  probability distribution on the five WZ states;
* `probOf_eq_sum_states` : law of total probability — any event splits over the five states.

Note on a subtlety of the definitions: `Pabc` is stated as `a~b ∧ b~c` (not as the symmetric
`a~b ∧ b~c ∧ a~c`), `Pab_c` as `a~b ∧ ¬a~c`, and `Pac_b` as `a~c ∧ ¬a~b`.  Because reachability
is an equivalence relation these do single out the five reachability partitions:
`a~b ∧ b~c` forces `a~c` (all together); `a~b ∧ ¬a~c` forces `¬b~c` (so `{a,b}, {c}`);
`a~c ∧ ¬a~b` forces `¬b~c` (so `{a,c}, {b}`); `b~c ∧ ¬a~b` forces `¬a~c` (so `{a}, {b,c}`).
These consequences are recorded as `state_eq_*` below and are what makes the five events disjoint.
-/

open Bunkbed Bunkbed.Hyper Finset SimpleGraph

namespace GadgetStates

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The five partition events of the triple `(a, b, c)`, written **exactly** as the predicates
occurring in the definitions of `Pabc`, `Pab_c`, `Pac_b`, `Pa_bc`, `Pa_b_c`, and indexed by the
`WZ` state each one describes. -/
def PartEvent (s : WZ) (S : Finset (Sym2 V)) (a b c : V) : Prop :=
  match s with
  | WZ.abc   => (ofEdges S).Reachable a b ∧ (ofEdges S).Reachable b c
  | WZ.ab_c  => (ofEdges S).Reachable a b ∧ ¬ (ofEdges S).Reachable a c
  | WZ.ac_b  => (ofEdges S).Reachable a c ∧ ¬ (ofEdges S).Reachable a b
  | WZ.a_bc  => (ofEdges S).Reachable b c ∧ ¬ (ofEdges S).Reachable a b
  | WZ.a_b_c => ¬ (ofEdges S).Reachable a b ∧ ¬ (ofEdges S).Reachable b c ∧
                  ¬ (ofEdges S).Reachable a c

/-- The `WZ` state that the configuration `S` induces on the triple `(a, b, c)`. -/
def wzStateOf (S : Finset (Sym2 V)) (a b c : V) : WZ :=
  if (ofEdges S).Reachable a b then
    (if (ofEdges S).Reachable b c then WZ.abc else WZ.ab_c)
  else
    if (ofEdges S).Reachable b c then WZ.a_bc
    else if (ofEdges S).Reachable a c then WZ.ac_b else WZ.a_b_c

/-- The tuple of the five partition probabilities, read as a law on `WZ`. -/
def partProb (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a b c : V) : WZ → ℚ
  | WZ.abc   => Pabc E w a b c
  | WZ.ab_c  => Pab_c E w a b c
  | WZ.ac_b  => Pac_b E w a b c
  | WZ.a_bc  => Pa_bc E w a b c
  | WZ.a_b_c => Pa_b_c E w a b c

set_option linter.unusedSectionVars false in
/-- Sanity check, by `rfl`: `PartEvent` is **definitionally** the family of five predicates
occurring in the definitions of `Pabc`, `Pab_c`, `Pac_b`, `Pa_bc`, `Pa_b_c`. -/
theorem partEvent_def (S : Finset (Sym2 V)) (a b c : V) :
    (PartEvent WZ.abc S a b c = ((ofEdges S).Reachable a b ∧ (ofEdges S).Reachable b c)) ∧
    (PartEvent WZ.ab_c S a b c = ((ofEdges S).Reachable a b ∧ ¬ (ofEdges S).Reachable a c)) ∧
    (PartEvent WZ.ac_b S a b c = ((ofEdges S).Reachable a c ∧ ¬ (ofEdges S).Reachable a b)) ∧
    (PartEvent WZ.a_bc S a b c = ((ofEdges S).Reachable b c ∧ ¬ (ofEdges S).Reachable a b)) ∧
    (PartEvent WZ.a_b_c S a b c = (¬ (ofEdges S).Reachable a b ∧ ¬ (ofEdges S).Reachable b c ∧
        ¬ (ofEdges S).Reachable a c)) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### The five events are exactly the fibres of the state map -/

/-- The five partition events, as literally written in `Def_BunkbedPercolation`, are exactly the
fibres of the induced-state map. -/
theorem partEvent_iff_state (s : WZ) (S : Finset (Sym2 V)) (a b c : V) :
    PartEvent s S a b c ↔ wzStateOf S a b c = s := by
  by_cases hab : (ofEdges S).Reachable a b
  · by_cases hbc : (ofEdges S).Reachable b c
    · have hac : (ofEdges S).Reachable a c := hab.trans hbc
      cases s <;> simp +decide [PartEvent, wzStateOf, hab, hbc, hac]
    · have hac : ¬ (ofEdges S).Reachable a c := fun h => hbc (hab.symm.trans h)
      cases s <;> simp +decide [PartEvent, wzStateOf, hab, hbc, hac]
  · by_cases hbc : (ofEdges S).Reachable b c
    · have hac : ¬ (ofEdges S).Reachable a c := fun h => hab (h.trans hbc.symm)
      cases s <;> simp +decide [PartEvent, wzStateOf, hab, hbc, hac]
    · by_cases hac : (ofEdges S).Reachable a c
      · cases s <;> simp +decide [PartEvent, wzStateOf, hab, hbc, hac]
      · cases s <;> simp +decide [PartEvent, wzStateOf, hab, hbc, hac]

/-- All-together case: `Pabc`'s event `a~b ∧ b~c` is exactly the state `abc`. -/
theorem state_eq_abc (S : Finset (Sym2 V)) (a b c : V) :
    wzStateOf S a b c = WZ.abc ↔
      ((ofEdges S).Reachable a b ∧ (ofEdges S).Reachable b c ∧ (ofEdges S).Reachable a c) := by
  refine ⟨fun h => ?_, fun ⟨h1, h2, _⟩ => (partEvent_iff_state WZ.abc S a b c).1 ⟨h1, h2⟩⟩
  obtain ⟨h1, h2⟩ := (partEvent_iff_state WZ.abc S a b c).2 h
  exact ⟨h1, h2, h1.trans h2⟩

/-- Mixed case `{a,b}, {c}`: `Pab_c`'s event `a~b ∧ ¬a~c` also forces `¬b~c`. -/
theorem state_eq_ab_c (S : Finset (Sym2 V)) (a b c : V) :
    wzStateOf S a b c = WZ.ab_c ↔
      ((ofEdges S).Reachable a b ∧ ¬ (ofEdges S).Reachable a c ∧
        ¬ (ofEdges S).Reachable b c) := by
  refine ⟨fun h => ?_, fun ⟨h1, h2, _⟩ => (partEvent_iff_state WZ.ab_c S a b c).1 ⟨h1, h2⟩⟩
  obtain ⟨h1, h2⟩ := (partEvent_iff_state WZ.ab_c S a b c).2 h
  exact ⟨h1, h2, fun h3 => h2 (h1.trans h3)⟩

/-- Mixed case `{a,c}, {b}`: `Pac_b`'s event `a~c ∧ ¬a~b` also forces `¬b~c`. -/
theorem state_eq_ac_b (S : Finset (Sym2 V)) (a b c : V) :
    wzStateOf S a b c = WZ.ac_b ↔
      ((ofEdges S).Reachable a c ∧ ¬ (ofEdges S).Reachable a b ∧
        ¬ (ofEdges S).Reachable b c) := by
  refine ⟨fun h => ?_, fun ⟨h1, h2, _⟩ => (partEvent_iff_state WZ.ac_b S a b c).1 ⟨h1, h2⟩⟩
  obtain ⟨h1, h2⟩ := (partEvent_iff_state WZ.ac_b S a b c).2 h
  exact ⟨h1, h2, fun h3 => h2 (h1.trans h3.symm)⟩

/-- Mixed case `{a}, {b,c}`: `Pa_bc`'s event `b~c ∧ ¬a~b` also forces `¬a~c`. -/
theorem state_eq_a_bc (S : Finset (Sym2 V)) (a b c : V) :
    wzStateOf S a b c = WZ.a_bc ↔
      ((ofEdges S).Reachable b c ∧ ¬ (ofEdges S).Reachable a b ∧
        ¬ (ofEdges S).Reachable a c) := by
  refine ⟨fun h => ?_, fun ⟨h1, h2, _⟩ => (partEvent_iff_state WZ.a_bc S a b c).1 ⟨h1, h2⟩⟩
  obtain ⟨h1, h2⟩ := (partEvent_iff_state WZ.a_bc S a b c).2 h
  exact ⟨h1, h2, fun h3 => h2 (h3.trans h1.symm)⟩

/-- All-separate case. -/
theorem state_eq_a_b_c (S : Finset (Sym2 V)) (a b c : V) :
    wzStateOf S a b c = WZ.a_b_c ↔
      (¬ (ofEdges S).Reachable a b ∧ ¬ (ofEdges S).Reachable b c ∧
        ¬ (ofEdges S).Reachable a c) :=
  (partEvent_iff_state WZ.a_b_c S a b c).symm

/-! ### Exactly one of the five events holds -/

/-- The five events are **pairwise mutually exclusive**. -/
theorem partEvent_exclusive {s t : WZ} (hst : s ≠ t) (S : Finset (Sym2 V)) (a b c : V) :
    ¬ (PartEvent s S a b c ∧ PartEvent t S a b c) := by
  intro ⟨hs, ht⟩
  exact hst (((partEvent_iff_state s S a b c).1 hs).symm.trans
    ((partEvent_iff_state t S a b c).1 ht))

/-- The five events are **exhaustive**: their union is the whole configuration space. -/
theorem partEvent_exhaustive (S : Finset (Sym2 V)) (a b c : V) :
    ∃ s : WZ, PartEvent s S a b c :=
  ⟨wzStateOf S a b c, (partEvent_iff_state _ S a b c).2 rfl⟩

/-! ### The induced law on `WZ` is the tuple of partition probabilities -/

omit [Fintype V] in
private theorem probOf_congr (E : Finset (Sym2 V)) (w : Sym2 V → ℚ)
    {ev₁ ev₂ : Finset (Sym2 V) → Prop} [DecidablePred ev₁] [DecidablePred ev₂]
    (h : ∀ S, ev₁ S ↔ ev₂ S) : probOf E w ev₁ = probOf E w ev₂ :=
  Finset.sum_congr rfl fun S _ => if_congr (h S) rfl rfl

/-- **The state distribution.** The probability that a configuration induces the state `s` on
`(a, b, c)` is exactly the corresponding partition probability. -/
theorem prob_state_eq (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a b c : V) (s : WZ) :
    probOf E w (fun S => wzStateOf S a b c = s) = partProb E w a b c s := by
  cases s
  · exact probOf_congr E w fun S => ((partEvent_iff_state WZ.abc S a b c).symm)
  · exact probOf_congr E w fun S => ((partEvent_iff_state WZ.ab_c S a b c).symm)
  · exact probOf_congr E w fun S => ((partEvent_iff_state WZ.ac_b S a b c).symm)
  · exact probOf_congr E w fun S => ((partEvent_iff_state WZ.a_bc S a b c).symm)
  · exact probOf_congr E w fun S => ((partEvent_iff_state WZ.a_b_c S a b c).symm)

private theorem univ_WZ : (Finset.univ : Finset WZ)
    = {WZ.abc, WZ.ab_c, WZ.ac_b, WZ.a_bc, WZ.a_b_c} := by decide

/-- The five partition probabilities add up to `1`, for an arbitrary weight function `w`. -/
theorem sum_partProb (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a b c : V) :
    ∑ s : WZ, partProb E w a b c s = 1 := by
  rw [univ_WZ]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have h := BunkbedAux.partition_sum_eq_total E w a b c
  rw [BunkbedAux.sum_weight_eq_one E w] at h
  simp only [partProb]
  linarith [h]

/-- The induced law on `WZ` is a probability distribution: total mass `1`. -/
theorem sum_prob_state (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a b c : V) :
    ∑ s : WZ, probOf E w (fun S => wzStateOf S a b c = s) = 1 := by
  rw [Finset.sum_congr rfl fun s _ => prob_state_eq E w a b c s]
  exact sum_partProb E w a b c

/-- Restated in the order of the task: the five partition probabilities sum to `1`. -/
theorem partition_probs_sum_one (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a b c : V) :
    Pabc E w a b c + Pa_b_c E w a b c + Pa_bc E w a b c + Pab_c E w a b c + Pac_b E w a b c
      = 1 := by
  have h := BunkbedAux.partition_sum_eq_total E w a b c
  rw [BunkbedAux.sum_weight_eq_one E w] at h
  linarith

/-- The five identifications of `prob_state_eq`, spelled out. -/
theorem prob_state_abc (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a b c : V) :
    probOf E w (fun S => wzStateOf S a b c = WZ.abc) = Pabc E w a b c :=
  prob_state_eq E w a b c WZ.abc

theorem prob_state_ab_c (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a b c : V) :
    probOf E w (fun S => wzStateOf S a b c = WZ.ab_c) = Pab_c E w a b c :=
  prob_state_eq E w a b c WZ.ab_c

theorem prob_state_ac_b (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a b c : V) :
    probOf E w (fun S => wzStateOf S a b c = WZ.ac_b) = Pac_b E w a b c :=
  prob_state_eq E w a b c WZ.ac_b

theorem prob_state_a_bc (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a b c : V) :
    probOf E w (fun S => wzStateOf S a b c = WZ.a_bc) = Pa_bc E w a b c :=
  prob_state_eq E w a b c WZ.a_bc

theorem prob_state_a_b_c (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a b c : V) :
    probOf E w (fun S => wzStateOf S a b c = WZ.a_b_c) = Pa_b_c E w a b c :=
  prob_state_eq E w a b c WZ.a_b_c

/-! ### Nonnegativity, so the law is a genuine distribution -/

omit [Fintype V] in
private theorem weight_nonneg (E : Finset (Sym2 V)) (w : Sym2 V → ℚ)
    (hw : ∀ e, 0 ≤ w e ∧ w e ≤ 1) (S : Finset (Sym2 V)) : 0 ≤ weight E w S :=
  mul_nonneg (Finset.prod_nonneg fun e _ => (hw e).1)
    (Finset.prod_nonneg fun e _ => by linarith [(hw e).2])

/-- With weights in `[0,1]` every partition probability is nonnegative; together with
`sum_partProb` the five of them form a probability distribution on the five `WZ` states. -/
theorem partProb_nonneg (E : Finset (Sym2 V)) (w : Sym2 V → ℚ)
    (hw : ∀ e, 0 ≤ w e ∧ w e ≤ 1) (a b c : V) (s : WZ) : 0 ≤ partProb E w a b c s := by
  rw [← prob_state_eq E w a b c s]
  refine Finset.sum_nonneg fun S _ => ?_
  by_cases h : wzStateOf S a b c = s
  · simpa [h] using weight_nonneg E w hw S
  · simp [h]

/-! ### Law of total probability over the five states -/

/-- Any event splits as the disjoint union of its intersections with the five partition events:
this is the form in which the state decomposition is used in a substitution argument. -/
theorem probOf_eq_sum_states (E : Finset (Sym2 V)) (w : Sym2 V → ℚ) (a b c : V)
    (ev : Finset (Sym2 V) → Prop) [DecidablePred ev] :
    probOf E w ev = ∑ s : WZ, probOf E w (fun S => ev S ∧ wzStateOf S a b c = s) := by
  unfold probOf
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases h : ev S
  · simp [h]
  · simp [h]

end GadgetStates

/-- **Exactly one of the five partition events holds.**  For every percolation configuration `S`
and every triple `(a, b, c)` there is a unique `WZ` state `s` such that the corresponding event
— written verbatim as in the definitions of `Pabc`, `Pab_c`, `Pac_b`, `Pa_bc`, `Pa_b_c` — holds.
So the five events are pairwise mutually exclusive and jointly exhaustive; they are the fibres of
`GadgetStates.wzStateOf`, hence in bijection with the five partitions of `{a, b, c}` into
reachability classes. -/
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (S : Finset (Sym2 V)) (a b c : V) :
    ∃! s : WZ, GadgetStates.PartEvent s S a b c := by
  refine ⟨GadgetStates.wzStateOf S a b c,
    (GadgetStates.partEvent_iff_state _ S a b c).2 rfl, fun s hs => ?_⟩
  exact ((GadgetStates.partEvent_iff_state s S a b c).1 hs).symm
