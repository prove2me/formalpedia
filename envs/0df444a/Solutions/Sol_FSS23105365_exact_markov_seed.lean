-- Prove2me | solution 1 for FSS23105365.exact_markov_seed
-- status  : ACCEPTED   (prove)
-- author  : @YY
-- created : 2026-10-09T15:47:43.844908+00:00
-- url     : https://prove2.me/submissions/b3a9438f-1375-4138-9440-ee291fb37630

-- Standalone Appendix E.5 proof with all local dependencies.
import Definitions.Def_FSS23105365_Circuits
import Definitions.Def_FSS23105365_FiniteState
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Find
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rel
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Iterate
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.OrderClosed

noncomputable section

-- From Solutions.FSS23105365_CircuitCertificates
set_option autoImplicit false
namespace FSS23105365

/-- A straight-line register computation; both values and depths use it. -/
def runRegisters {A G : Type} (step : List A → G → A) (gs : List G) (vs : List A) : List A :=
  gs.foldl (fun xs g => xs ++ [step xs g]) vs

theorem runRegisters_length {A G : Type} (step : List A → G → A) (gs : List G)
    (vs : List A) : (runRegisters step gs vs).length = vs.length + gs.length := by
  induction gs generalizing vs with
  | nil => simp [runRegisters]
  | cons g gs ih =>
    change (runRegisters step gs (vs ++ [step vs g])).length = _
    rw [ih]
    simp
    omega

/-- A local register invariant extends to the final list. The relation can
be equality for Boolean semantics or an inequality for depth certificates. -/
theorem runRegisters_relation {A B G : Type} (step : List A → G → A)
    (R : A → B → Prop) (default : A) (ρ : ℕ → B) (gs : List G) (r : ℕ)
    (vs : List A) (hlen : vs.length = r)
    (hinput : ∀ j < r, R (vs.getD j default) (ρ j))
    (hstep : ∀ i : Fin gs.length, ∀ xs : List A, xs.length = r + i.val →
      (∀ j < xs.length, R (xs.getD j default) (ρ j)) →
      R (step xs (gs.get i)) (ρ (r + i.val))) :
    ∀ j < r + gs.length, R ((runRegisters step gs vs).getD j default) (ρ j) := by
  induction gs generalizing r vs with
  | nil => simpa only [runRegisters, List.foldl_nil, List.length_nil, Nat.add_zero] using hinput
  | cons g gs ih =>
    have hg : R (step vs g) (ρ r) := by
      simpa using hstep ⟨0, by simp⟩ vs (by simpa using hlen)
        (fun j hj => hinput j (by simpa [hlen] using hj))
    have hv : (vs ++ [step vs g]).length = r + 1 := by simp [hlen]
    have hvi : ∀ j < r + 1, R ((vs ++ [step vs g]).getD j default) (ρ j) := by
      intro j hj
      by_cases hjr : j < r
      · rw [List.getD_append _ _ _ _ (by omega)]
        exact hinput j hjr
      · have heq : j = r := by omega
        subst j
        rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
        exact hg
    have htail : ∀ i : Fin gs.length, ∀ xs : List A, xs.length = (r + 1) + i.val →
        (∀ j < xs.length, R (xs.getD j default) (ρ j)) →
        R (step xs (gs.get i)) (ρ ((r + 1) + i.val)) := by
      intro i xs hxs hrel
      simpa only [List.get_cons_succ', Fin.val_succ, Nat.add_assoc, Nat.add_comm 1] using
        hstep i.succ xs (by simpa [Nat.add_assoc, Nat.add_comm 1] using hxs) hrel
    simpa only [runRegisters, List.foldl_cons, List.length_cons, Nat.add_assoc,
      Nat.add_comm 1] using ih (r + 1) (vs ++ [step vs g]) hv hvi htail

def gateEvalFn (v : ℕ → Bool) : Gate → Bool
  | .constant b => b
  | .neg j => !(v j)
  | .conj js => js.all v
  | .disj js => js.any v

def gateDepthFn (d : ℕ → ℕ) (g : Gate) : ℕ :=
  1 + (g.sources.map d).foldl max 0

theorem list_all_congr_on {A : Type} (xs : List A) (f g : A → Bool)
    (h : ∀ x ∈ xs, f x = g x) : xs.all f = xs.all g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem list_any_congr_on {A : Type} (xs : List A) (f g : A → Bool)
    (h : ∀ x ∈ xs, f x = g x) : xs.any f = xs.any g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem gateEvalFn_congr (g : Gate) (v w : ℕ → Bool)
    (h : ∀ j ∈ g.sources, v j = w j) : gateEvalFn v g = gateEvalFn w g := by
  cases g with
  | constant b => rfl
  | neg j => simp only [gateEvalFn, h j (by simp [Gate.sources])]
  | conj js => exact list_all_congr_on js v w h
  | disj js => exact list_any_congr_on js v w h

theorem gate_eval_eq_fn (g : Gate) (vs : List Bool) :
    g.eval vs = gateEvalFn (fun j => vs.getD j false) g := by cases g <;> rfl

theorem foldl_max_map_mono {A : Type} (xs : List A) (f g : A → ℕ) (a b : ℕ)
    (hab : a ≤ b) (hfg : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).foldl max a ≤ (xs.map g).foldl max b := by
  induction xs generalizing a b with
  | nil => exact hab
  | cons x xs ih =>
    exact ih (max a (f x)) (max b (g x))
      (max_le_max hab (hfg x (by simp))) (fun y hy => hfg y (by simp [hy]))

theorem foldl_max_le {xs : List ℕ} {a D : ℕ} (ha : a ≤ D)
    (hx : ∀ x ∈ xs, x ≤ D) : xs.foldl max a ≤ D := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih => exact ih (max_le ha (hx x (by simp))) (fun y hy => hx y (by simp [hy]))

theorem gateDepthFn_mono (g : Gate) (d e : ℕ → ℕ)
    (h : ∀ j ∈ g.sources, d j ≤ e j) : gateDepthFn d g ≤ gateDepthFn e g :=
  Nat.add_le_add_left (foldl_max_map_mono g.sources d e 0 0 le_rfl h) 1

/-- Circuit evaluation agrees with any assignment satisfying the seed and
every gate equation. Gate validity is used to compare earlier registers. -/
theorem circuit_eval_of_certificate {Out : Type} (C : Circuit Out)
    (seed : Bits C.randomBits) (v : ℕ → Bool)
    (hinput : ∀ i : Fin C.randomBits, v i.val = seed i)
    (hgate : ∀ i : Fin C.gates.length,
      gateEvalFn v (C.gates.get i) = v (C.randomBits + i.val)) :
    C.eval seed = fun o => v (C.output o) := by
  have hrel := runRegisters_relation (fun vs g => Gate.eval vs g) Eq false v C.gates
    C.randomBits (List.ofFn seed) (by simp) (fun j hj => by
      rw [List.getD_eq_getElem _ _ (by simpa using hj)]
      simpa using (hinput ⟨j, hj⟩).symm) (fun i xs hxs hx => by
      rw [gate_eval_eq_fn]
      exact (gateEvalFn_congr (C.gates.get i) _ v (fun j hj =>
        hx j (by rw [hxs]; exact C.gate_valid i j hj))).trans (hgate i))
  funext o
  exact hrel (C.output o) (C.output_valid o)

/-- A natural-valued level for each wire bounds the actual circuit depth
if each gate lies at least one level after all of its source levels. -/
theorem circuit_depth_le_of_certificate {Out : Type} [Fintype Out] (C : Circuit Out)
    (d : ℕ → ℕ) (D : ℕ)
    (hgate : ∀ i : Fin C.gates.length,
      gateDepthFn d (C.gates.get i) ≤ d (C.randomBits + i.val))
    (hout : ∀ o, d (C.output o) ≤ D) : C.depth ≤ D := by
  classical
  have hrel := runRegisters_relation (fun vs g => Gate.depth vs g) (· ≤ ·) 0 d C.gates
    C.randomBits (List.replicate C.randomBits 0) (by simp)
    (fun j hj => by simp)
    (fun i xs hxs hx => (gateDepthFn_mono (C.gates.get i) _ d (fun j hj =>
      hx j (by rw [hxs]; exact C.gate_valid i j hj))).trans (hgate i))
  apply foldl_max_le (Nat.zero_le D)
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact (hrel _ (C.output_valid _)).trans (hout _)

end FSS23105365

-- From Solutions.FSS23105365_CircuitPrograms
set_option autoImplicit false
namespace FSS23105365

/-- A verified straight-line program with shared inputs. Assignments and
levels are certificates, discharged by constructors and checked against
the original `Circuit` semantics by `programCircuit`. -/
structure CircuitProgram (r : ℕ) where
  gates : List Gate
  valid : ∀ i : Fin gates.length, ∀ j ∈ (gates.get i).sources, j < r + i.val
  value : Bits r → ℕ → Bool
  input_value : ∀ seed (i : Fin r), value seed i.val = seed i
  gate_value : ∀ seed (i : Fin gates.length),
    gateEvalFn (value seed) (gates.get i) = value seed (r + i.val)
  level : ℕ → ℕ
  input_level : ∀ j < r, level j = 0
  gate_level : ∀ i : Fin gates.length,
    gateDepthFn level (gates.get i) ≤ level (r + i.val)

def emptyCircuitProgram (r : ℕ) : CircuitProgram r where
  gates := []
  valid i := Fin.elim0 i
  value seed j := if h : j < r then seed ⟨j, h⟩ else false
  input_value seed i := by simp
  gate_value _ i := Fin.elim0 i
  level _ := 0
  input_level _ _ := rfl
  gate_level i := Fin.elim0 i

/-- Choosing output wires produces an actual well-formed circuit. -/
def programCircuit {r : ℕ} {Out : Type} (P : CircuitProgram r)
    (output : Out → Fin (r + P.gates.length)) : Circuit Out where
  randomBits := r
  gates := P.gates
  output o := (output o).val
  gate_valid := P.valid
  output_valid o := (output o).isLt

theorem programCircuit_eval {r : ℕ} {Out : Type} (P : CircuitProgram r)
    (output : Out → Fin (r + P.gates.length)) (seed : Bits r) :
    (programCircuit P output).eval seed = fun o => P.value seed (output o).val :=
  circuit_eval_of_certificate (programCircuit P output) seed (P.value seed)
    (P.input_value seed) (P.gate_value seed)

theorem programCircuit_depth_le {r : ℕ} {Out : Type} [Fintype Out] (P : CircuitProgram r)
    (output : Out → Fin (r + P.gates.length)) (D : ℕ)
    (h : ∀ o, P.level (output o).val ≤ D) : (programCircuit P output).depth ≤ D :=
  circuit_depth_le_of_certificate (programCircuit P output) P.level D P.gate_level h

theorem programCircuit_size {r : ℕ} {Out : Type} [Fintype Out] (P : CircuitProgram r)
    (output : Out → Fin (r + P.gates.length)) :
    (programCircuit P output).size = r + P.gates.length +
      (P.gates.map (fun g => g.sources.length)).sum + Fintype.card Out := rfl

theorem gateDepthFn_congr (g : Gate) (d e : ℕ → ℕ)
    (h : ∀ j ∈ g.sources, d j = e j) : gateDepthFn d g = gateDepthFn e g := by
  apply le_antisymm
  · exact gateDepthFn_mono g d e (fun j hj => (h j hj).le)
  · exact gateDepthFn_mono g e d (fun j hj => (h j hj).symm.le)

theorem get_append_gate_cases (gs : List Gate) (g : Gate) (i : Fin (gs ++ [g]).length) :
    (∃ j : Fin gs.length, i.val = j.val ∧ (gs ++ [g]).get i = gs.get j) ∨
      (i.val = gs.length ∧ (gs ++ [g]).get i = g) := by
  by_cases hi : i.val < gs.length
  · exact Or.inl ⟨⟨i.val, hi⟩, rfl, by simp [List.get_eq_getElem, List.getElem_append_left hi]⟩
  · have he : i.val = gs.length := by have := i.isLt; simp at this; omega
    exact Or.inr ⟨he, by simp [List.get_eq_getElem, he]⟩

/-- Add one unbounded-fan-in gate. Existing wires retain their values and
levels, and the new wire has exactly the gate's value and certified level. -/
def appendCircuitGate {r : ℕ} (P : CircuitProgram r) (g : Gate)
    (hg : ∀ j ∈ g.sources, j < r + P.gates.length) : CircuitProgram r where
  gates := P.gates ++ [g]
  valid i j hj := by
    rcases get_append_gate_cases P.gates g i with ⟨k, hik, he⟩ | ⟨hi, he⟩
    · rw [he] at hj
      simpa only [hik] using P.valid k j hj
    · rw [he] at hj
      simpa only [hi] using hg j hj
  value seed j := if j < r + P.gates.length then P.value seed j else gateEvalFn (P.value seed) g
  input_value seed i := by
    simp only [if_pos (by omega : i.val < r + P.gates.length), P.input_value]
  gate_value seed i := by
    rcases get_append_gate_cases P.gates g i with ⟨k, hik, he⟩ | ⟨hi, he⟩
    · rw [he, hik, if_pos (by omega : r + k.val < r + P.gates.length)]
      calc
        _ = gateEvalFn (P.value seed) (P.gates.get k) := gateEvalFn_congr _ _ _ (by
          intro j hj
          have := P.valid k j hj
          simp only [if_pos (by omega : j < r + P.gates.length)])
        _ = _ := P.gate_value seed k
    · rw [he, hi, if_neg (Nat.lt_irrefl _)]
      exact gateEvalFn_congr _ _ _ (fun j hj => if_pos (hg j hj))
  level j := if j < r + P.gates.length then P.level j else gateDepthFn P.level g
  input_level j hj := by simp only [if_pos (by omega : j < r + P.gates.length), P.input_level j hj]
  gate_level i := by
    rcases get_append_gate_cases P.gates g i with ⟨k, hik, he⟩ | ⟨hi, he⟩
    · rw [he, hik, if_pos (by omega : r + k.val < r + P.gates.length)]
      calc
        _ = gateDepthFn P.level (P.gates.get k) := gateDepthFn_congr _ _ _ (by
          intro j hj
          have := P.valid k j hj
          simp only [if_pos (by omega : j < r + P.gates.length)])
        _ ≤ _ := P.gate_level k
    · rw [he, hi, if_neg (Nat.lt_irrefl _)]
      exact (gateDepthFn_congr _ _ _ (fun j hj => if_pos (hg j hj))).le

theorem appendCircuitGate_value_old {r : ℕ} (P : CircuitProgram r) (g : Gate)
    (hg : ∀ j ∈ g.sources, j < r + P.gates.length) (seed : Bits r)
    (j : ℕ) (hj : j < r + P.gates.length) :
    (appendCircuitGate P g hg).value seed j = P.value seed j := if_pos hj

theorem appendCircuitGate_value_new {r : ℕ} (P : CircuitProgram r) (g : Gate)
    (hg : ∀ j ∈ g.sources, j < r + P.gates.length) (seed : Bits r) :
    (appendCircuitGate P g hg).value seed (r + P.gates.length) = gateEvalFn (P.value seed) g :=
  if_neg (Nat.lt_irrefl _)

theorem appendCircuitGate_level_old {r : ℕ} (P : CircuitProgram r) (g : Gate)
    (hg : ∀ j ∈ g.sources, j < r + P.gates.length) (j : ℕ) (hj : j < r + P.gates.length) :
    (appendCircuitGate P g hg).level j = P.level j := if_pos hj

theorem appendCircuitGate_level_new {r : ℕ} (P : CircuitProgram r) (g : Gate)
    (hg : ∀ j ∈ g.sources, j < r + P.gates.length) :
    (appendCircuitGate P g hg).level (r + P.gates.length) = gateDepthFn P.level g :=
  if_neg (Nat.lt_irrefl _)

theorem appendCircuitGate_level_le {r : ℕ} (P : CircuitProgram r) (g : Gate)
    (hg : ∀ j ∈ g.sources, j < r + P.gates.length) (D : ℕ)
    (hD : ∀ j ∈ g.sources, P.level j ≤ D) :
    (appendCircuitGate P g hg).level (r + P.gates.length) ≤ D + 1 := by
  rw [appendCircuitGate_level_new]
  unfold gateDepthFn
  have hmax : (g.sources.map P.level).foldl max 0 ≤ D := by
    apply foldl_max_le (Nat.zero_le D)
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    exact hD j hj
  omega

/-- Exact gate-and-wire accounting for one append. -/
theorem appendCircuitGate_cost {r : ℕ} (P : CircuitProgram r) (g : Gate)
    (hg : ∀ j ∈ g.sources, j < r + P.gates.length) :
    (appendCircuitGate P g hg).gates.length +
        ((appendCircuitGate P g hg).gates.map (fun g => g.sources.length)).sum =
      P.gates.length + (P.gates.map (fun g => g.sources.length)).sum + 1 + g.sources.length := by
  simp only [appendCircuitGate, List.length_append, List.length_singleton, List.map_append,
    List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil]
  omega

end FSS23105365

-- From Solutions.FSS23105365_CircuitRewiring
set_option autoImplicit false
namespace FSS23105365

def mapGateWires (f : ℕ → ℕ) : Gate → Gate
  | .constant b => .constant b
  | .neg j => .neg (f j)
  | .conj js => .conj (js.map f)
  | .disj js => .disj (js.map f)

theorem mapGateWires_sources (f : ℕ → ℕ) (g : Gate) :
    (mapGateWires f g).sources = g.sources.map f := by cases g <;> rfl

theorem mapGateWires_eval (f : ℕ → ℕ) (v : ℕ → Bool) (g : Gate) :
    gateEvalFn v (mapGateWires f g) = gateEvalFn (v ∘ f) g := by
  cases g <;> simp [mapGateWires, gateEvalFn]

theorem mapGateWires_depth (f : ℕ → ℕ) (d : ℕ → ℕ) (g : Gate) :
    gateDepthFn d (mapGateWires f g) = gateDepthFn (d ∘ f) g := by
  simp only [gateDepthFn, mapGateWires_sources, List.map_map]

theorem foldl_max_shift (xs : List ℕ) (D a : ℕ) :
    (xs.map (fun x => D + x)).foldl max (D + a) = D + xs.foldl max a := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [show max (D + a) (D + x) = D + max a x by omega, ih]

theorem gateDepthFn_shift_le (d : ℕ → ℕ) (D : ℕ) (g : Gate) :
    gateDepthFn (fun j => D + d j) g ≤ D + gateDepthFn d g := by
  have hm := foldl_max_map_mono g.sources (fun j => D + d j) (fun j => D + d j)
    0 D (Nat.zero_le _) (fun _ _ => le_rfl)
  have hs : (g.sources.map (fun j => D + d j)).foldl max D =
      D + (g.sources.map d).foldl max 0 := by
    simpa only [List.map_map, Function.comp_def, Nat.add_zero] using
      foldl_max_shift (g.sources.map d) D 0
  unfold gateDepthFn
  rw [hs] at hm
  omega

/-- Inputs are replaced by existing wires; internal wires are translated
to a fresh contiguous region beginning at `base`. -/
def substituteWire {k base : ℕ} (input : Fin k → Fin base) (j : ℕ) : ℕ :=
  if h : j < k then (input ⟨j, h⟩).val else base + (j - k)

def spliceWireFn {A : Type} (base k : ℕ) (v w : ℕ → A) (j : ℕ) : A :=
  if j < base then v j else w (k + (j - base))

theorem substituteWire_internal {k base : ℕ} (input : Fin k → Fin base) (i : ℕ) :
    substituteWire input (k + i) = base + i := by simp [substituteWire]

theorem substituteWire_lt {k base : ℕ} (input : Fin k → Fin base)
    (i j : ℕ) (hj : j < k + i) : substituteWire input j < base + i := by
  unfold substituteWire
  split_ifs with h
  · have := (input ⟨j, h⟩).isLt
    omega
  · omega

theorem spliceWireFn_old {A : Type} {base k : ℕ} (v w : ℕ → A) (j : ℕ) (hj : j < base) :
    spliceWireFn base k v w j = v j := if_pos hj

theorem spliceWireFn_internal {A : Type} {base k : ℕ} (v w : ℕ → A) (i : ℕ) :
    spliceWireFn base k v w (base + i) = w (k + i) := by simp [spliceWireFn]

theorem spliceWireFn_substitute {A : Type} {k base : ℕ} (input : Fin k → Fin base)
    (v w : ℕ → A) (hin : ∀ i : Fin k, v (input i).val = w i.val) (j : ℕ) :
    spliceWireFn base k v w (substituteWire input j) = w j := by
  unfold substituteWire
  split_ifs with hj
  · exact (spliceWireFn_old v w _ (input ⟨j, hj⟩).isLt).trans (hin ⟨j, hj⟩)
  · rw [spliceWireFn_internal]
    congr 1
    omega

theorem spliceWireFn_substitute_le {k base : ℕ} (input : Fin k → Fin base)
    (v w : ℕ → ℕ) (hin : ∀ i : Fin k, v (input i).val ≤ w i.val) (j : ℕ) :
    spliceWireFn base k v w (substituteWire input j) ≤ w j := by
  unfold substituteWire
  split_ifs with hj
  · rw [spliceWireFn_old v w _ (input ⟨j, hj⟩).isLt]
    exact hin ⟨j, hj⟩
  · rw [spliceWireFn_internal, Nat.add_sub_of_le (by omega : k ≤ j)]

theorem get_append_map_cases {A : Type} (xs ys : List A) (f : A → A)
    (i : Fin (xs ++ ys.map f).length) :
    (∃ j : Fin xs.length, i.val = j.val ∧ (xs ++ ys.map f).get i = xs.get j) ∨
      (∃ j : Fin ys.length, i.val = xs.length + j.val ∧
        (xs ++ ys.map f).get i = f (ys.get j)) := by
  by_cases hi : i.val < xs.length
  · exact Or.inl ⟨⟨i.val, hi⟩, rfl, by simp [List.get_eq_getElem, List.getElem_append_left hi]⟩
  · have hj : i.val - xs.length < ys.length := by
      have := i.isLt
      simp at this
      omega
    refine Or.inr ⟨(⟨i.val - xs.length, hj⟩ : Fin ys.length), ?_, ?_⟩
    · change i.val = xs.length + (i.val - xs.length)
      omega
    · simp only [List.get_eq_getElem, List.getElem_append_right (Nat.le_of_not_gt hi),
        List.getElem_map]

end FSS23105365

-- From Solutions.FSS23105365_CircuitComposition
set_option autoImplicit false
namespace FSS23105365

/-- Compose a verified program with another program wired to selected
existing registers. No extra random input is introduced. -/
def composeCircuitProgram {r k : ℕ} (P : CircuitProgram r) (Q : CircuitProgram k)
    (input : Fin k → Fin (r + P.gates.length)) (D : ℕ)
    (hD : ∀ i, P.level (input i).val ≤ D) : CircuitProgram r where
  gates := P.gates ++ Q.gates.map (mapGateWires (substituteWire input))
  valid i j hj := by
    rcases get_append_map_cases P.gates Q.gates (mapGateWires (substituteWire input)) i with
      ⟨t, hi, he⟩ | ⟨t, hi, he⟩
    · rw [he] at hj
      simpa only [hi] using P.valid t j hj
    · rw [he, mapGateWires_sources] at hj
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hj
      simpa only [hi, Nat.add_assoc] using substituteWire_lt input t.val l (Q.valid t l hl)
  value seed := spliceWireFn (r + P.gates.length) k (P.value seed)
    (Q.value (fun i => P.value seed (input i).val))
  input_value seed i := by
    rw [spliceWireFn_old _ _ _ (by omega : i.val < r + P.gates.length)]
    exact P.input_value seed i
  gate_value seed i := by
    let s : Bits k := fun j => P.value seed (input j).val
    rcases get_append_map_cases P.gates Q.gates (mapGateWires (substituteWire input)) i with
      ⟨t, hi, he⟩ | ⟨t, hi, he⟩
    · rw [he, hi, spliceWireFn_old _ _ _ (by omega : r + t.val < r + P.gates.length)]
      exact (gateEvalFn_congr (P.gates.get t) _ (P.value seed) (fun j hj =>
        spliceWireFn_old _ _ _ (by have := P.valid t j hj; omega))).trans (P.gate_value seed t)
    · rw [he, hi, ← Nat.add_assoc, spliceWireFn_internal, mapGateWires_eval]
      exact (gateEvalFn_congr (Q.gates.get t) _ (Q.value s) (fun j _ =>
        spliceWireFn_substitute input (P.value seed) (Q.value s)
          (fun l => (Q.input_value s l).symm) j)).trans (Q.gate_value s t)
  level := spliceWireFn (r + P.gates.length) k P.level (fun j => D + Q.level j)
  input_level j hj := by
    rw [spliceWireFn_old _ _ _ (by omega : j < r + P.gates.length)]
    exact P.input_level j hj
  gate_level i := by
    rcases get_append_map_cases P.gates Q.gates (mapGateWires (substituteWire input)) i with
      ⟨t, hi, he⟩ | ⟨t, hi, he⟩
    · rw [he, hi, spliceWireFn_old _ _ _ (by omega : r + t.val < r + P.gates.length)]
      exact (gateDepthFn_congr (P.gates.get t) _ P.level (fun j hj =>
        spliceWireFn_old _ _ _ (by have := P.valid t j hj; omega))).le.trans (P.gate_level t)
    · rw [he, hi, ← Nat.add_assoc, spliceWireFn_internal, mapGateWires_depth]
      calc
        _ ≤ gateDepthFn (fun j => D + Q.level j) (Q.gates.get t) :=
          gateDepthFn_mono _ _ _ (fun j _ => spliceWireFn_substitute_le input P.level
            (fun j => D + Q.level j) (fun l => by
              rw [Q.input_level l.val l.isLt, Nat.add_zero]
              exact hD l) j)
        _ ≤ D + gateDepthFn Q.level (Q.gates.get t) := gateDepthFn_shift_le _ _ _
        _ ≤ D + Q.level (k + t.val) := Nat.add_le_add_left (Q.gate_level t) D

theorem composeCircuitProgram_value_old {r k : ℕ} (P : CircuitProgram r) (Q : CircuitProgram k)
    (input : Fin k → Fin (r + P.gates.length)) (D : ℕ) (hD : ∀ i, P.level (input i).val ≤ D)
    (seed : Bits r) (j : ℕ) (hj : j < r + P.gates.length) :
    (composeCircuitProgram P Q input D hD).value seed j = P.value seed j :=
  spliceWireFn_old _ _ _ hj

theorem composeCircuitProgram_value_new {r k : ℕ} (P : CircuitProgram r) (Q : CircuitProgram k)
    (input : Fin k → Fin (r + P.gates.length)) (D : ℕ) (hD : ∀ i, P.level (input i).val ≤ D)
    (seed : Bits r) (j : ℕ) :
    (composeCircuitProgram P Q input D hD).value seed (substituteWire input j) =
      Q.value (fun i => P.value seed (input i).val) j :=
  spliceWireFn_substitute input (P.value seed) (Q.value (fun i => P.value seed (input i).val))
    (fun i => (Q.input_value (fun i => P.value seed (input i).val) i).symm) j

theorem composeCircuitProgram_level_old {r k : ℕ} (P : CircuitProgram r) (Q : CircuitProgram k)
    (input : Fin k → Fin (r + P.gates.length)) (D : ℕ) (hD : ∀ i, P.level (input i).val ≤ D)
    (j : ℕ) (hj : j < r + P.gates.length) :
    (composeCircuitProgram P Q input D hD).level j = P.level j :=
  spliceWireFn_old (k := k) P.level (fun j => D + Q.level j) j hj

theorem composeCircuitProgram_level_new {r k : ℕ} (P : CircuitProgram r) (Q : CircuitProgram k)
    (input : Fin k → Fin (r + P.gates.length)) (D : ℕ) (hD : ∀ i, P.level (input i).val ≤ D)
    (j : ℕ) :
    (composeCircuitProgram P Q input D hD).level (substituteWire input j) ≤ D + Q.level j :=
  spliceWireFn_substitute_le input P.level (fun j => D + Q.level j) (fun i => by
    rw [Q.input_level i.val i.isLt, Nat.add_zero]
    exact hD i) j

/-- Composition copies each gate and source wire once. -/
theorem composeCircuitProgram_cost {r k : ℕ} (P : CircuitProgram r) (Q : CircuitProgram k)
    (input : Fin k → Fin (r + P.gates.length)) (D : ℕ) (hD : ∀ i, P.level (input i).val ≤ D) :
    (composeCircuitProgram P Q input D hD).gates.length +
        ((composeCircuitProgram P Q input D hD).gates.map (fun g => g.sources.length)).sum =
      (P.gates.length + (P.gates.map (fun g => g.sources.length)).sum) +
        (Q.gates.length + (Q.gates.map (fun g => g.sources.length)).sum) := by
  simp only [composeCircuitProgram, List.length_append, List.length_map, List.map_append,
    List.sum_append, List.map_map, Function.comp_def, mapGateWires_sources]
  omega

/-- Transport an output of the second program to its composed wire. -/
def composedOutput {r k : ℕ} (P : CircuitProgram r) (Q : CircuitProgram k)
    (input : Fin k → Fin (r + P.gates.length)) (D : ℕ) (hD : ∀ i, P.level (input i).val ≤ D)
    (j : Fin (k + Q.gates.length)) :
    Fin (r + (composeCircuitProgram P Q input D hD).gates.length) :=
  ⟨substituteWire input j.val, by
    simpa only [composeCircuitProgram, List.length_append, List.length_map, Nat.add_assoc] using
      substituteWire_lt input Q.gates.length j.val j.isLt⟩

/-- The compiled circuit computes functional composition, with exactly
the first program's random inputs and additive certified depth. -/
theorem composed_circuit_correct {r k : ℕ} {Out : Type} [Fintype Out]
    (P : CircuitProgram r) (Q : CircuitProgram k)
    (input : Fin k → Fin (r + P.gates.length)) (D E : ℕ)
    (hD : ∀ i, P.level (input i).val ≤ D)
    (output : Out → Fin (k + Q.gates.length)) (hE : ∀ o, Q.level (output o).val ≤ E) :
    ∃ C : Circuit Out, ∃ hbits : C.randomBits = r, C.depth ≤ D + E ∧
      (∀ seed : Bits r, C.eval (fun i => seed (Fin.cast hbits i)) =
        fun o => Q.value (fun i => P.value seed (input i).val) (output o).val) ∧
      C.size = r + (P.gates.length + (P.gates.map (fun g => g.sources.length)).sum) +
        (Q.gates.length + (Q.gates.map (fun g => g.sources.length)).sum) + Fintype.card Out := by
  let R := composeCircuitProgram P Q input D hD
  let out := fun o => composedOutput P Q input D hD (output o)
  refine ⟨programCircuit R out, rfl, ?_, ?_, ?_⟩
  · apply programCircuit_depth_le
    intro o
    exact (composeCircuitProgram_level_new P Q input D hD (output o).val).trans
      (Nat.add_le_add_left (hE o) D)
  · intro seed
    change (programCircuit R out).eval seed = _
    rw [programCircuit_eval]
    funext o
    exact composeCircuitProgram_value_new P Q input D hD seed (output o).val
  · rw [programCircuit_size]
    have hc := composeCircuitProgram_cost P Q input D hD
    dsimp [R] at *
    omega

end FSS23105365

-- From Solutions.FSS23105365_CircuitParallel
set_option autoImplicit false
namespace FSS23105365

def sharedInputWires {r : ℕ} (P : CircuitProgram r) : Fin r → Fin (r + P.gates.length) :=
  fun i => ⟨i.val, by omega⟩

theorem sharedInputWires_level {r : ℕ} (P : CircuitProgram r) (i : Fin r) :
    P.level (sharedInputWires P i).val ≤ 0 := (P.input_level i.val i.isLt).le

/-- Parallel composition shares all random input bits. -/
def parallelCircuitProgram {r : ℕ} (P Q : CircuitProgram r) : CircuitProgram r :=
  composeCircuitProgram P Q (sharedInputWires P) 0 (sharedInputWires_level P)

theorem parallelCircuitProgram_value_right {r : ℕ} (P Q : CircuitProgram r)
    (seed : Bits r) (j : ℕ) :
    (parallelCircuitProgram P Q).value seed (substituteWire (sharedInputWires P) j) =
      Q.value seed j := by
  rw [parallelCircuitProgram, composeCircuitProgram_value_new]
  have he : (fun i => P.value seed (sharedInputWires P i).val) = seed := by
    funext i
    exact P.input_value seed i
  rw [he]

def parallelLeftOutput {r : ℕ} (P Q : CircuitProgram r) (j : Fin (r + P.gates.length)) :
    Fin (r + (parallelCircuitProgram P Q).gates.length) := ⟨j.val, by
  have := j.isLt
  simp only [parallelCircuitProgram, composeCircuitProgram, List.length_append, List.length_map]
  omega⟩

def parallelRightOutput {r : ℕ} (P Q : CircuitProgram r) (j : Fin (r + Q.gates.length)) :
    Fin (r + (parallelCircuitProgram P Q).gates.length) :=
  composedOutput P Q (sharedInputWires P) 0 (sharedInputWires_level P) j

/-- The compiled parallel circuit retains the maximum depth and adds the
gate-and-wire costs, charging the shared input only once. -/
theorem parallel_circuit_correct {r : ℕ} {A B : Type} [Fintype A] [Fintype B]
    (P Q : CircuitProgram r) (outP : A → Fin (r + P.gates.length))
    (outQ : B → Fin (r + Q.gates.length)) (D E : ℕ)
    (hD : ∀ a, P.level (outP a).val ≤ D) (hE : ∀ b, Q.level (outQ b).val ≤ E) :
    ∃ C : Circuit (A ⊕ B), ∃ hbits : C.randomBits = r, C.depth ≤ max D E ∧
      (∀ seed : Bits r, C.eval (fun i => seed (Fin.cast hbits i)) =
        Sum.elim (fun a => P.value seed (outP a).val) (fun b => Q.value seed (outQ b).val)) ∧
      C.size = r + (P.gates.length + (P.gates.map (fun g => g.sources.length)).sum) +
        (Q.gates.length + (Q.gates.map (fun g => g.sources.length)).sum) +
          Fintype.card A + Fintype.card B := by
  let R := parallelCircuitProgram P Q
  let output : A ⊕ B → Fin (r + R.gates.length) :=
    Sum.elim (fun a => parallelLeftOutput P Q (outP a))
      (fun b => parallelRightOutput P Q (outQ b))
  refine ⟨programCircuit R output, rfl, ?_, ?_, ?_⟩
  · apply programCircuit_depth_le
    intro o
    cases o with
    | inl a =>
      change (composeCircuitProgram P Q _ _ _).level (outP a).val ≤ _
      rw [composeCircuitProgram_level_old _ _ _ _ _ _ (outP a).isLt]
      exact (hD a).trans (Nat.le_max_left D E)
    | inr b =>
      have hh := composeCircuitProgram_level_new P Q (sharedInputWires P) 0
        (sharedInputWires_level P) (outQ b).val
      simp only [Nat.zero_add] at hh
      exact hh.trans ((hE b).trans (Nat.le_max_right D E))
  · intro seed
    change (programCircuit R output).eval seed = _
    rw [programCircuit_eval]
    funext o
    cases o with
    | inl a => exact composeCircuitProgram_value_old P Q _ _ _ seed _ (outP a).isLt
    | inr b => exact parallelCircuitProgram_value_right P Q seed (outQ b).val
  · rw [programCircuit_size, Fintype.card_sum]
    have hc := composeCircuitProgram_cost P Q (sharedInputWires P) 0 (sharedInputWires_level P)
    change r + (composeCircuitProgram P Q _ _ _).gates.length +
      ((composeCircuitProgram P Q _ _ _).gates.map (fun g => g.sources.length)).sum +
        (Fintype.card A + Fintype.card B) = _
    omega

end FSS23105365

-- From Solutions.FSS23105365_CircuitFormula
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

def programCost {r : ℕ} (P : CircuitProgram r) : ℕ :=
  P.gates.length + (P.gates.map (fun g => g.sources.length)).sum

/-- Arbitrarily many programs share their inputs in parallel without a
depth increase. The cost is exactly the sum of all gate-and-wire costs. -/
theorem parallel_program_family {r m : ℕ} (P : Fin m → CircuitProgram r)
    (out : (i : Fin m) → Fin (r + (P i).gates.length)) (D : ℕ)
    (hD : ∀ i, (P i).level (out i).val ≤ D) :
    ∃ R : CircuitProgram r, ∃ output : Fin m → Fin (r + R.gates.length),
      (∀ seed i, R.value seed (output i).val = (P i).value seed (out i).val) ∧
      (∀ i, R.level (output i).val ≤ D) ∧ programCost R = ∑ i, programCost (P i) := by
  induction m with
  | zero =>
    exact ⟨emptyCircuitProgram r, Fin.elim0, fun _ i => Fin.elim0 i,
      fun i => Fin.elim0 i, by simp [programCost, emptyCircuitProgram]⟩
  | succ m ih =>
    obtain ⟨T, tail, ht, hd, hc⟩ := ih (fun i => P i.succ) (fun i => out i.succ)
      (fun i => hD i.succ)
    let R := parallelCircuitProgram (P 0) T
    let output : Fin (m + 1) → Fin (r + R.gates.length) :=
      Fin.cons (parallelLeftOutput (P 0) T (out 0))
        (fun i => parallelRightOutput (P 0) T (tail i))
    refine ⟨R, output, ?_, ?_, ?_⟩
    · intro seed i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact composeCircuitProgram_value_old (P 0) T _ _ _ seed _ (out 0).isLt
      · exact (parallelCircuitProgram_value_right (P 0) T seed (tail j).val).trans (ht seed j)
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change (composeCircuitProgram (P 0) T _ _ _).level (out 0).val ≤ D
        rw [composeCircuitProgram_level_old _ _ _ _ _ _ (out 0).isLt]
        exact hD 0
      · have hh := composeCircuitProgram_level_new (P 0) T (sharedInputWires (P 0)) 0
          (sharedInputWires_level (P 0)) (tail j).val
        simp only [Nat.zero_add] at hh
        exact hh.trans (hd j)
    · change programCost (composeCircuitProgram (P 0) T _ _ _) = _
      rw [programCost, composeCircuitProgram_cost]
      change programCost (P 0) + programCost T = _
      rw [hc, Fin.sum_univ_succ]

/-- Unbounded-fan-in formulas over the original random input bits. -/
inductive CircuitFormula (r : ℕ) where
  | input (i : Fin r)
  | constant (b : Bool)
  | neg (f : CircuitFormula r)
  | all (n : ℕ) (fs : Fin n → CircuitFormula r)
  | any (n : ℕ) (fs : Fin n → CircuitFormula r)

def formulaEval {r : ℕ} : CircuitFormula r → Bits r → Bool
  | .input i, x => x i
  | .constant b, _ => b
  | .neg f, x => !(formulaEval f x)
  | .all _ fs, x => (List.ofFn fun i => formulaEval (fs i) x).all id
  | .any _ fs, x => (List.ofFn fun i => formulaEval (fs i) x).any id

def formulaDepth {r : ℕ} : CircuitFormula r → ℕ
  | .input _ => 0
  | .constant _ => 1
  | .neg f => formulaDepth f + 1
  | .all _ fs => Finset.univ.sup (fun i => formulaDepth (fs i)) + 1
  | .any _ fs => Finset.univ.sup (fun i => formulaDepth (fs i)) + 1

/-- Each connective charges its gate and all incoming wires. -/
def formulaCost {r : ℕ} : CircuitFormula r → ℕ
  | .input _ => 0
  | .constant _ => 1
  | .neg f => formulaCost f + 2
  | .all n fs => (∑ i, formulaCost (fs i)) + 1 + n
  | .any n fs => (∑ i, formulaCost (fs i)) + 1 + n

/-- Append an AND or OR over a finite family of already computed wires. -/
theorem append_family_gate {r m : ℕ} (P : CircuitProgram r)
    (out : Fin m → Fin (r + P.gates.length)) (D : ℕ)
    (hD : ∀ i, P.level (out i).val ≤ D) (isAnd : Bool) :
    ∃ R : CircuitProgram r, ∃ output : Fin (r + R.gates.length),
      (∀ seed, R.value seed output.val =
        if isAnd then (List.ofFn fun i => P.value seed (out i).val).all id
        else (List.ofFn fun i => P.value seed (out i).val).any id) ∧
      R.level output.val ≤ D + 1 ∧ programCost R = programCost P + 1 + m := by
  let wires := List.ofFn (fun i => (out i).val)
  let g := if isAnd then Gate.conj wires else Gate.disj wires
  have hs : g.sources = wires := by cases isAnd <;> rfl
  have hg : ∀ j ∈ g.sources, j < r + P.gates.length := by
    intro j hj
    rw [hs] at hj
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hj
    exact (out i).isLt
  let R := appendCircuitGate P g hg
  let o : Fin (r + R.gates.length) := ⟨r + P.gates.length, by
    simp [R, appendCircuitGate]⟩
  refine ⟨R, o, ?_, ?_, ?_⟩
  · intro seed
    change (appendCircuitGate P g hg).value seed (r + P.gates.length) = _
    rw [appendCircuitGate_value_new]
    cases isAnd with
    | false =>
      simpa only [g, Bool.false_eq_true, ↓reduceIte, gateEvalFn, List.map_ofFn,
        Function.comp_def, id_eq, wires] using
        (List.any_map (f := P.value seed) (p := id) (l := wires)).symm
    | true =>
      simpa only [g, Bool.true_eq, ↓reduceIte, gateEvalFn, List.map_ofFn,
        Function.comp_def, id_eq, wires] using
        (List.all_map (f := P.value seed) (p := id) (l := wires)).symm
  · apply appendCircuitGate_level_le
    intro j hj
    rw [hs] at hj
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hj
    exact hD i
  · change programCost (appendCircuitGate P g hg) = _
    rw [programCost, appendCircuitGate_cost, hs]
    simp only [wires, List.length_ofFn]
    rfl

/-- Compile every formula into the original circuit representation, with
its exact semantics, at most its syntactic depth, and exact gate/wire cost. -/
theorem compile_circuit_formula {r : ℕ} (f : CircuitFormula r) :
    ∃ P : CircuitProgram r, ∃ out : Fin (r + P.gates.length),
      (∀ seed, P.value seed out.val = formulaEval f seed) ∧
      P.level out.val ≤ formulaDepth f ∧ programCost P = formulaCost f := by
  induction f with
  | input i =>
    refine ⟨emptyCircuitProgram r, ⟨i.val, by simpa [emptyCircuitProgram] using i.isLt⟩,
      fun seed => (emptyCircuitProgram r).input_value seed i, le_rfl, rfl⟩
  | constant b =>
    let P := emptyCircuitProgram r
    have hg : ∀ j ∈ (Gate.constant b).sources, j < r + P.gates.length := by simp [Gate.sources]
    let R := appendCircuitGate P (.constant b) hg
    refine ⟨R, ⟨r + P.gates.length, by simp [R, appendCircuitGate]⟩,
      fun seed => appendCircuitGate_value_new P _ hg seed, ?_, ?_⟩
    · exact appendCircuitGate_level_le P _ hg 0 (by simp [Gate.sources])
    · change programCost (appendCircuitGate P _ hg) = _
      rw [programCost, appendCircuitGate_cost]
      rfl
  | neg f ih =>
    obtain ⟨P, out, hv, hd, hc⟩ := ih
    have hg : ∀ j ∈ (Gate.neg out.val).sources, j < r + P.gates.length := by
      simpa [Gate.sources] using out.isLt
    let R := appendCircuitGate P (.neg out.val) hg
    refine ⟨R, ⟨r + P.gates.length, by simp [R, appendCircuitGate]⟩, ?_, ?_, ?_⟩
    · intro seed
      change (appendCircuitGate P _ hg).value seed (r + P.gates.length) = _
      rw [appendCircuitGate_value_new]
      exact congrArg Bool.not (hv seed)
    · exact appendCircuitGate_level_le P _ hg (formulaDepth f) (by simpa [Gate.sources] using hd)
    · change programCost (appendCircuitGate P _ hg) = _
      rw [programCost, appendCircuitGate_cost]
      change programCost P + 1 + 1 = formulaCost f + 2
      omega
  | all m fs ih =>
    choose P out hv hd hc using ih
    obtain ⟨R, output, hr, hrd, hrc⟩ := parallel_program_family P out
      (Finset.univ.sup (fun i => formulaDepth (fs i)))
      (fun i => (hd i).trans (Finset.le_sup (f := fun i => formulaDepth (fs i)) (Finset.mem_univ i)))
    obtain ⟨T, o, ht, htd, htc⟩ := append_family_gate R output _ hrd true
    refine ⟨T, o, ?_, htd, ?_⟩
    · intro seed
      rw [ht]
      simp only [Bool.true_eq, ↓reduceIte, hr, hv]
      rfl
    · rw [htc, hrc]
      simp only [hc, formulaCost]
  | any m fs ih =>
    choose P out hv hd hc using ih
    obtain ⟨R, output, hr, hrd, hrc⟩ := parallel_program_family P out
      (Finset.univ.sup (fun i => formulaDepth (fs i)))
      (fun i => (hd i).trans (Finset.le_sup (f := fun i => formulaDepth (fs i)) (Finset.mem_univ i)))
    obtain ⟨T, o, ht, htd, htc⟩ := append_family_gate R output _ hrd false
    refine ⟨T, o, ?_, htd, ?_⟩
    · intro seed
      rw [ht]
      simp only [Bool.false_eq_true, ↓reduceIte, hr, hv]
      rfl
    · rw [htc, hrc]
      simp only [hc, formulaCost]

theorem formula_circuit {r : ℕ} (f : CircuitFormula r) :
    ∃ C : Circuit Unit, ∃ hbits : C.randomBits = r,
      (∀ seed : Bits r, C.eval (fun i => seed (Fin.cast hbits i)) () = formulaEval f seed) ∧
      C.depth ≤ formulaDepth f ∧ C.size = r + formulaCost f + 1 := by
  obtain ⟨P, out, hv, hd, hc⟩ := compile_circuit_formula f
  refine ⟨programCircuit P (fun _ : Unit => out), rfl, ?_, ?_, ?_⟩
  · intro seed
    change (programCircuit P (fun _ : Unit => out)).eval seed () = _
    rw [programCircuit_eval]
    exact hv seed
  · exact programCircuit_depth_le P _ _ (fun _ => hd)
  · rw [programCircuit_size, Fintype.card_unit]
    change r + P.gates.length + (P.gates.map (fun g => g.sources.length)).sum + 1 = _
    dsimp [programCost] at hc
    omega

end FSS23105365

-- From Solutions.FSS23105365_CircuitLookup
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

def lookupLiteral {r : ℕ} (a : Bits r) (i : Fin r) : CircuitFormula r :=
  if a i then .input i else .neg (.input i)

def lookupClause {r : ℕ} (a : Bits r) : CircuitFormula r :=
  .all r (lookupLiteral a)

theorem lookupLiteral_true_iff {r : ℕ} (a x : Bits r) (i : Fin r) :
    formulaEval (lookupLiteral a i) x = true ↔ x i = a i := by
  cases ha : a i <;> cases hx : x i <;> simp [lookupLiteral, formulaEval, ha, hx]

theorem lookupClause_true_iff {r : ℕ} (a x : Bits r) :
    formulaEval (lookupClause a) x = true ↔ x = a := by
  change (List.ofFn fun i => formulaEval (lookupLiteral a i) x).all id = true ↔ _
  rw [List.all_eq_true]
  constructor
  · intro h
    funext i
    exact (lookupLiteral_true_iff a x i).mp
      (h _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
  · rintro rfl y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    exact (lookupLiteral_true_iff x x i).mpr rfl

theorem lookupClause_depth {r : ℕ} (a : Bits r) : formulaDepth (lookupClause a) ≤ 2 := by
  change Finset.univ.sup (fun i => formulaDepth (lookupLiteral a i)) + 1 ≤ 2
  have h : Finset.univ.sup (fun i => formulaDepth (lookupLiteral a i)) ≤ 1 := by
    apply Finset.sup_le
    intro i _
    cases hi : a i <;> simp [lookupLiteral, formulaDepth, hi]
  omega

theorem lookupClause_cost {r : ℕ} (a : Bits r) : formulaCost (lookupClause a) ≤ 3 * r + 1 := by
  have hsum : (∑ i : Fin r, formulaCost (lookupLiteral a i)) ≤ 2 * r := by
    calc
      _ ≤ ∑ _i : Fin r, 2 := Finset.sum_le_sum (fun i _ => by
        cases hi : a i <;> simp [lookupLiteral, formulaCost, hi])
      _ = _ := by simp; omega
  change (∑ i, formulaCost (lookupLiteral a i)) + 1 + r ≤ _
  omega

/-- A finite truth-table lookup as a depth-three DNF. The exponential
arity cost is explicit; this is used only for bounded-arity local maps. -/
def truthTableFormula {r : ℕ} (f : Bits r → Bool) : CircuitFormula r :=
  .any (Fintype.card (Bits r)) (fun i =>
    let a := (Fintype.equivFin (Bits r)).symm i
    if f a then lookupClause a else .constant false)

theorem truthTableFormula_eval {r : ℕ} (f : Bits r → Bool) (x : Bits r) :
    formulaEval (truthTableFormula f) x = f x := by
  classical
  let e := Fintype.equivFin (Bits r)
  let branch : Fin (Fintype.card (Bits r)) → CircuitFormula r :=
    fun i => if f (e.symm i) then lookupClause (e.symm i) else .constant false
  have hb : ∀ i, formulaEval (branch i) x = true ↔ f (e.symm i) = true ∧ x = e.symm i := by
    intro i
    by_cases hi : f (e.symm i) = true
    · simpa only [branch, if_pos hi, hi, true_and] using lookupClause_true_iff (e.symm i) x
    · simp only [branch, if_neg hi, formulaEval, Bool.false_eq_true, hi, false_and]
  apply Bool.eq_iff_iff.mpr
  change (List.ofFn fun i => formulaEval (branch i) x).any id = true ↔ f x = true
  rw [List.any_eq_true]
  constructor
  · rintro ⟨y, hy, hyt⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    obtain ⟨hf, hx⟩ := (hb i).mp hyt
    exact hx ▸ hf
  · intro hx
    refine ⟨formulaEval (branch (e x)) x, List.mem_ofFn.mpr ⟨e x, rfl⟩, ?_⟩
    exact (hb (e x)).mpr (by simpa only [e.symm_apply_apply, and_true] using hx)

theorem truthTableFormula_depth {r : ℕ} (f : Bits r → Bool) :
    formulaDepth (truthTableFormula f) ≤ 3 := by
  change Finset.univ.sup (fun i => formulaDepth
    (if f ((Fintype.equivFin (Bits r)).symm i) then
      lookupClause ((Fintype.equivFin (Bits r)).symm i) else .constant false)) + 1 ≤ 3
  have h : Finset.univ.sup (fun i => formulaDepth
      (if f ((Fintype.equivFin (Bits r)).symm i) then
        lookupClause ((Fintype.equivFin (Bits r)).symm i) else .constant false)) ≤ 2 := by
    apply Finset.sup_le
    intro i _
    split_ifs
    · exact lookupClause_depth _
    · change 1 ≤ 2
      omega
  omega

theorem truthTableFormula_cost {r : ℕ} (f : Bits r → Bool) :
    formulaCost (truthTableFormula f) ≤ 2 ^ r * (3 * r + 2) + 1 := by
  have hsum : (∑ i : Fin (Fintype.card (Bits r)), formulaCost
      (if f ((Fintype.equivFin (Bits r)).symm i) then
        lookupClause ((Fintype.equivFin (Bits r)).symm i) else .constant false)) ≤
      Fintype.card (Bits r) * (3 * r + 1) := by
    calc
      _ ≤ ∑ _i : Fin (Fintype.card (Bits r)), (3 * r + 1) := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs
        · exact lookupClause_cost _
        · change 1 ≤ 3 * r + 1
          omega
      _ = _ := by simp
  have hcard : Fintype.card (Bits r) = 2 ^ r := by simp [Bits, Fintype.card_fun]
  change (∑ i, formulaCost _) + 1 + Fintype.card (Bits r) ≤ _
  dsimp only
  calc
    _ ≤ Fintype.card (Bits r) * (3 * r + 1) + 1 + Fintype.card (Bits r) := by omega
    _ = _ := by rw [hcard]; ring

/-- Every finite Boolean lookup has an actual depth-three circuit. Its
size is exponential in arity, as expected; fixed arity gives constant cost. -/
theorem boolean_lookup_circuit {r : ℕ} (f : Bits r → Bool) :
    ∃ C : Circuit Unit, ∃ hbits : C.randomBits = r,
      (∀ x : Bits r, C.eval (fun i => x (Fin.cast hbits i)) () = f x) ∧
      C.depth ≤ 3 ∧ C.size ≤ r + 2 ^ r * (3 * r + 2) + 2 := by
  obtain ⟨C, hbits, he, hd, hs⟩ := formula_circuit (truthTableFormula f)
  refine ⟨C, hbits, fun x => (he x).trans (truthTableFormula_eval f x),
    hd.trans (truthTableFormula_depth f), ?_⟩
  rw [hs]
  have := truthTableFormula_cost f
  omega

end FSS23105365

-- From Solutions.FSS23105365_CircuitLocalMaps
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

def relabelFormula {k r : ℕ} (input : Fin k → Fin r) : CircuitFormula k → CircuitFormula r
  | .input i => .input (input i)
  | .constant b => .constant b
  | .neg f => .neg (relabelFormula input f)
  | .all n fs => .all n (fun i => relabelFormula input (fs i))
  | .any n fs => .any n (fun i => relabelFormula input (fs i))

theorem relabelFormula_eval {k r : ℕ} (input : Fin k → Fin r)
    (f : CircuitFormula k) (seed : Bits r) :
    formulaEval (relabelFormula input f) seed = formulaEval f (fun i => seed (input i)) := by
  induction f <;> simp only [relabelFormula, formulaEval, *]

theorem relabelFormula_depth {k r : ℕ} (input : Fin k → Fin r) (f : CircuitFormula k) :
    formulaDepth (relabelFormula input f) = formulaDepth f := by
  induction f <;> simp only [relabelFormula, formulaDepth, *]

theorem relabelFormula_cost {k r : ℕ} (input : Fin k → Fin r) (f : CircuitFormula k) :
    formulaCost (relabelFormula input f) = formulaCost f := by
  induction f <;> simp only [relabelFormula, formulaCost, *]

/-- Compile a finite formula family on shared inputs. Depth is bounded
uniformly, while all formula gates, source wires and output wires are charged. -/
theorem formula_family_circuit {r m : ℕ} (fs : Fin m → CircuitFormula r) (D : ℕ)
    (hD : ∀ i, formulaDepth (fs i) ≤ D) :
    ∃ C : Circuit (Fin m), ∃ hbits : C.randomBits = r,
      (∀ seed : Bits r, ∀ i, C.eval (fun j => seed (Fin.cast hbits j)) i = formulaEval (fs i) seed) ∧
      C.depth ≤ D ∧ C.size = r + (∑ i, formulaCost (fs i)) + m := by
  choose P out hv hd hc using fun i => compile_circuit_formula (fs i)
  obtain ⟨R, output, hr, hrd, hrc⟩ := parallel_program_family P out D (fun i => (hd i).trans (hD i))
  refine ⟨programCircuit R output, rfl, ?_, programCircuit_depth_le R output D hrd, ?_⟩
  · intro seed i
    change (programCircuit R output).eval seed i = _
    rw [programCircuit_eval]
    exact (hr seed i).trans (hv i seed)
  · rw [programCircuit_size, Fintype.card_fin]
    change r + R.gates.length + (R.gates.map (fun g => g.sources.length)).sum + m = _
    have hcost : programCost R = ∑ i, formulaCost (fs i) := by rw [hrc]; simp only [hc]
    dsimp [programCost] at hcost
    omega

/-- Parallel local Boolean maps have actual depth-three circuits. Each
output may select and repeat any `k` original input wires. For fixed `k`,
the stated gate-and-wire size bound is linear in inputs plus outputs. -/
theorem local_maps_circuit {r k m : ℕ} (input : Fin m → Fin k → Fin r)
    (f : Fin m → Bits k → Bool) :
    ∃ C : Circuit (Fin m), ∃ hbits : C.randomBits = r,
      (∀ seed : Bits r, ∀ i, C.eval (fun j => seed (Fin.cast hbits j)) i =
        f i (fun j => seed (input i j))) ∧
      C.depth ≤ 3 ∧ C.size ≤ r + m * (2 ^ k * (3 * k + 2) + 2) := by
  let fs : Fin m → CircuitFormula r := fun i => relabelFormula (input i) (truthTableFormula (f i))
  obtain ⟨C, hbits, he, hd, hs⟩ := formula_family_circuit fs 3 (fun i => by
    dsimp only [fs]
    rw [relabelFormula_depth]
    exact truthTableFormula_depth (f i))
  refine ⟨C, hbits, fun seed i => ?_, hd, ?_⟩
  · rw [he]
    dsimp only [fs]
    rw [relabelFormula_eval, truthTableFormula_eval]
  · have hsum : (∑ i, formulaCost (fs i)) ≤ m * (2 ^ k * (3 * k + 2) + 1) := by
      calc
        _ ≤ ∑ _i : Fin m, (2 ^ k * (3 * k + 2) + 1) := by
          apply Finset.sum_le_sum
          intro i _
          dsimp only [fs]
          rw [relabelFormula_cost]
          exact truthTableFormula_cost (f i)
        _ = _ := by simp
    rw [hs]
    calc
      _ ≤ r + m * (2 ^ k * (3 * k + 2) + 1) + m := by omega
      _ = _ := by ring

end FSS23105365

-- From Solutions.FSS23105365_FormulaConnectives
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

def formulaAnd {r : ℕ} (f g : CircuitFormula r) : CircuitFormula r :=
  .all 2 (Fin.cons f (Fin.cons g Fin.elim0))

def formulaOr {r : ℕ} (f g : CircuitFormula r) : CircuitFormula r :=
  .any 2 (Fin.cons f (Fin.cons g Fin.elim0))

theorem formulaAnd_eval {r : ℕ} (f g : CircuitFormula r) (x : Bits r) :
    formulaEval (formulaAnd f g) x = (formulaEval f x && formulaEval g x) := by
  simp [formulaAnd, formulaEval, List.ofFn_succ]

theorem formulaOr_eval {r : ℕ} (f g : CircuitFormula r) (x : Bits r) :
    formulaEval (formulaOr f g) x = (formulaEval f x || formulaEval g x) := by
  simp [formulaOr, formulaEval, List.ofFn_succ]

theorem formulaAnd_depth {r : ℕ} (f g : CircuitFormula r) :
    formulaDepth (formulaAnd f g) = max (formulaDepth f) (formulaDepth g) + 1 := by
  simp [formulaAnd, formulaDepth, Finset.univ_fin2]

theorem formulaOr_depth {r : ℕ} (f g : CircuitFormula r) :
    formulaDepth (formulaOr f g) = max (formulaDepth f) (formulaDepth g) + 1 := by
  simp [formulaOr, formulaDepth, Finset.univ_fin2]

theorem formulaAnd_cost {r : ℕ} (f g : CircuitFormula r) :
    formulaCost (formulaAnd f g) = formulaCost f + formulaCost g + 3 := by
  simp [formulaAnd, formulaCost, Fin.sum_univ_succ]

theorem formulaOr_cost {r : ℕ} (f g : CircuitFormula r) :
    formulaCost (formulaOr f g) = formulaCost f + formulaCost g + 3 := by
  simp [formulaOr, formulaCost, Fin.sum_univ_succ]

theorem formulaAny_true_iff {r n : ℕ} (fs : Fin n → CircuitFormula r) (x : Bits r) :
    formulaEval (.any n fs) x = true ↔ ∃ i, formulaEval (fs i) x = true := by
  simp only [formulaEval, List.any_eq_true, List.mem_ofFn]
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, hy⟩; exact ⟨i, hy⟩
  · rintro ⟨i, hi⟩; exact ⟨_, ⟨i, rfl⟩, hi⟩

end FSS23105365

-- From Solutions.FSS23105365_CircuitFiniteFamilies
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

def formulaIndexedAny {I : Type} [Fintype I] {r : ℕ} (fs : I → CircuitFormula r) :
    CircuitFormula r := .any (Fintype.card I) (fun i => fs ((Fintype.equivFin I).symm i))

theorem formulaIndexedAny_eval {I : Type} [Fintype I] {r : ℕ}
    (fs : I → CircuitFormula r) (seed : Bits r) :
    formulaEval (formulaIndexedAny fs) seed = true ↔ ∃ i, formulaEval (fs i) seed = true := by
  rw [formulaIndexedAny, formulaAny_true_iff]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨_, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨(Fintype.equivFin I) i, by simpa using hi⟩

theorem formulaIndexedAny_depth {I : Type} [Fintype I] {r : ℕ}
    (fs : I → CircuitFormula r) (D : ℕ) (hd : ∀ i, formulaDepth (fs i) ≤ D) :
    formulaDepth (formulaIndexedAny fs) ≤ D + 1 := by
  change Finset.univ.sup (fun i => formulaDepth (fs ((Fintype.equivFin I).symm i))) + 1 ≤ _
  exact Nat.add_le_add_right (Finset.sup_le (fun i _ => hd _)) 1

theorem formulaIndexedAny_cost {I : Type} [Fintype I] {r : ℕ}
    (fs : I → CircuitFormula r) (K : ℕ) (hk : ∀ i, formulaCost (fs i) ≤ K) :
    formulaCost (formulaIndexedAny fs) ≤ Fintype.card I * (K + 1) + 1 := by
  have hs : (∑ i : Fin (Fintype.card I), formulaCost (fs ((Fintype.equivFin I).symm i))) ≤
      Fintype.card I * K := by
    simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hk ((Fintype.equivFin I).symm i))
  change (∑ i : Fin (Fintype.card I), formulaCost (fs ((Fintype.equivFin I).symm i))) + 1 +
    Fintype.card I ≤ _
  nlinarith

/-- The formula compiler also supports arbitrary finite output types,
including tuples of a prefix index and a state-encoding bit. -/
theorem formula_fintype_family_circuit {Out : Type} [Fintype Out] {r : ℕ}
    (fs : Out → CircuitFormula r) (D : ℕ) (hD : ∀ i, formulaDepth (fs i) ≤ D) :
    ∃ C : Circuit Out, ∃ hbits : C.randomBits = r,
      (∀ seed : Bits r, ∀ i, C.eval (fun j => seed (Fin.cast hbits j)) i = formulaEval (fs i) seed) ∧
      C.depth ≤ D ∧ C.size = r + (∑ i, formulaCost (fs i)) + Fintype.card Out := by
  choose P out hv hd hc using fun i : Out => compile_circuit_formula (fs i)
  let e := Fintype.equivFin Out
  obtain ⟨R, output, hr, hrd, hrc⟩ := parallel_program_family
    (fun i => P (e.symm i)) (fun i => out (e.symm i)) D
    (fun i => (hd (e.symm i)).trans (hD (e.symm i)))
  let output' := fun i : Out => output (e i)
  refine ⟨programCircuit R output', rfl, ?_,
    programCircuit_depth_le R output' D (fun i => hrd (e i)), ?_⟩
  · intro seed i
    change (programCircuit R output').eval seed i = _
    rw [programCircuit_eval]
    have he := (hr seed (e i)).trans (hv (e.symm (e i)) seed)
    simpa only [Equiv.symm_apply_apply, output'] using he
  · rw [programCircuit_size]
    have hcost : programCost R = ∑ i : Out, formulaCost (fs i) := by
      rw [hrc]
      simp only [hc]
      exact e.symm.sum_comp (fun i => formulaCost (fs i))
    dsimp [programCost] at hcost
    omega

end FSS23105365

-- From Solutions.FSS23105365_FormulaSubstitution
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

def substituteFormula {k r : ℕ} (input : Fin k → CircuitFormula r) :
    CircuitFormula k → CircuitFormula r
  | .input i => input i
  | .constant b => .constant b
  | .neg f => .neg (substituteFormula input f)
  | .all n fs => .all n (fun i => substituteFormula input (fs i))
  | .any n fs => .any n (fun i => substituteFormula input (fs i))

theorem substituteFormula_eval {k r : ℕ} (input : Fin k → CircuitFormula r)
    (f : CircuitFormula k) (seed : Bits r) :
    formulaEval (substituteFormula input f) seed =
      formulaEval f (fun i => formulaEval (input i) seed) := by
  induction f <;> simp only [substituteFormula, formulaEval, *]

theorem substituteFormula_depth {k r : ℕ} (input : Fin k → CircuitFormula r)
    (D : ℕ) (hD : ∀ i, formulaDepth (input i) ≤ D) (f : CircuitFormula k) :
    formulaDepth (substituteFormula input f) ≤ D + formulaDepth f := by
  induction f with
  | input i => simpa [substituteFormula, formulaDepth] using hD i
  | constant b => simp [substituteFormula, formulaDepth]
  | neg f ih => simpa only [substituteFormula, formulaDepth, Nat.add_assoc] using Nat.add_le_add_right ih 1
  | all n fs ih | any n fs ih =>
    simp only [substituteFormula, formulaDepth]
    have hs : Finset.univ.sup (fun i => formulaDepth (substituteFormula input (fs i))) ≤
        D + Finset.univ.sup (fun i => formulaDepth (fs i)) := by
      apply Finset.sup_le
      intro i _
      exact (ih i).trans (Nat.add_le_add_left
        (Finset.le_sup (f := fun i => formulaDepth (fs i)) (Finset.mem_univ i)) D)
    omega

/-- The substitution cost includes every copied gate and wire. Fixed-size
lookup formulas therefore multiply a polynomial bound by a constant. -/
theorem substituteFormula_cost {k r : ℕ} (input : Fin k → CircuitFormula r)
    (K : ℕ) (hK : ∀ i, formulaCost (input i) ≤ K) (f : CircuitFormula k) :
    formulaCost (substituteFormula input f) ≤ formulaCost f * (K + 1) + K := by
  induction f with
  | input i => simpa [substituteFormula, formulaCost] using hK i
  | constant b => simp only [substituteFormula, formulaCost]; omega
  | neg f ih =>
    simp only [substituteFormula, formulaCost]
    nlinarith
  | all n fs ih | any n fs ih =>
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => ih i)
    have hs' : (∑ i, formulaCost (substituteFormula input (fs i))) ≤
        (∑ i, formulaCost (fs i)) * (K + 1) + n * K := by
      simpa only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id] using hs
    simp only [substituteFormula, formulaCost]
    nlinarith

theorem truthTableFormula_cost_mono {k ℓ : ℕ} (h : ℓ ≤ k) (f : Bits ℓ → Bool) :
    formulaCost (truthTableFormula f) ≤ 2 ^ k * (3 * k + 2) + 1 := by
  have hp : 2 ^ ℓ ≤ 2 ^ k := pow_le_pow_right' (by omega : 1 ≤ (2 : ℕ)) h
  have hm := Nat.mul_le_mul hp (by omega : 3 * ℓ + 2 ≤ 3 * k + 2)
  exact (truthTableFormula_cost f).trans (Nat.add_le_add_right hm 1)

end FSS23105365

-- From Solutions.FSS23105365_StarFreeExpressions
set_option autoImplicit false
namespace FSS23105365

/-- Star-free expressions, with complement always relative to the full
ambient word set. These are union, difference and concatenation expressions
over universal language and singleton letters; no Kleene star is a constructor. -/
inductive StarFreeExpr (U : Type) where
  | top
  | letter (a : U)
  | union (e f : StarFreeExpr U)
  | diff (e f : StarFreeExpr U)
  | concat (e f : StarFreeExpr U)

def sfDenote {U : Type} : StarFreeExpr U → List U → Prop
  | .top, _ => True
  | .letter a, w => w = [a]
  | .union e f, w => sfDenote e w ∨ sfDenote f w
  | .diff e f, w => sfDenote e w ∧ ¬sfDenote f w
  | .concat e f, w => ∃ u v, u ++ v = w ∧ sfDenote e u ∧ sfDenote f v

def wordCutLeft {n : ℕ} (t : Fin (n + 1)) : Fin t.val → Fin n :=
  fun i => ⟨i.val, by omega⟩

def wordCutRight {n : ℕ} (t : Fin (n + 1)) : Fin (n - t.val) → Fin n :=
  fun i => ⟨t.val + i.val, by omega⟩

theorem word_cut_list {U : Type} {n : ℕ} (x : Fin n → U) (t : Fin (n + 1)) :
    List.ofFn (fun i => x (wordCutLeft t i)) ++ List.ofFn (fun i => x (wordCutRight t i)) =
      List.ofFn x := by
  apply List.ext_getElem
  · simp only [List.length_append, List.length_ofFn]
    omega
  · intro i hi hj
    by_cases ht : i < t.val
    · rw [List.getElem_append_left (by simpa using ht)]
      simp [wordCutLeft]
    · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt ht)]
      simp only [List.getElem_ofFn, List.length_ofFn, wordCutRight]
      congr 1
      apply Fin.ext
      simp only [Fin.val_mk]
      omega

theorem sfDenote_concat_cut {U : Type} {n : ℕ} (e f : StarFreeExpr U) (x : Fin n → U) :
    sfDenote (.concat e f) (List.ofFn x) ↔
      ∃ t : Fin (n + 1), sfDenote e (List.ofFn (fun i => x (wordCutLeft t i))) ∧
        sfDenote f (List.ofFn (fun i => x (wordCutRight t i))) := by
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    have hlen : u.length + v.length = n := by simpa using congrArg List.length huv
    let t : Fin (n + 1) := ⟨u.length, by omega⟩
    have he := List.append_inj ((word_cut_list x t).trans huv.symm)
      (by simp [t] : (List.ofFn (fun i => x (wordCutLeft t i))).length = u.length)
    exact ⟨t, he.1.symm ▸ hu, he.2.symm ▸ hv⟩
  · rintro ⟨t, ht, hu⟩
    exact ⟨_, _, word_cut_list x t, ht, hu⟩

end FSS23105365

-- From Solutions.FSS23105365_StarFreeLanguages
set_option autoImplicit false
namespace FSS23105365

def IsStarFree {U : Type} (L : List U → Prop) : Prop :=
  ∃ e : StarFreeExpr U, ∀ w, sfDenote e w ↔ L w

theorem isStarFree_congr {U : Type} {L K : List U → Prop}
    (hL : IsStarFree L) (h : ∀ w, L w ↔ K w) : IsStarFree K := by
  obtain ⟨e, he⟩ := hL
  exact ⟨e, fun w => (he w).trans (h w)⟩

theorem isStarFree_top {U : Type} : IsStarFree (fun _ : List U => True) :=
  ⟨.top, fun _ => Iff.rfl⟩

theorem isStarFree_empty {U : Type} : IsStarFree (fun _ : List U => False) := by
  exact ⟨.diff .top .top, fun w => by simp [sfDenote]⟩

theorem isStarFree_letter {U : Type} (a : U) : IsStarFree (fun w => w = [a]) :=
  ⟨.letter a, fun _ => Iff.rfl⟩

theorem isStarFree_union {U : Type} {L K : List U → Prop}
    (hL : IsStarFree L) (hK : IsStarFree K) : IsStarFree (fun w => L w ∨ K w) := by
  obtain ⟨e, he⟩ := hL
  obtain ⟨f, hf⟩ := hK
  exact ⟨.union e f, fun w => or_congr (he w) (hf w)⟩

theorem isStarFree_diff {U : Type} {L K : List U → Prop}
    (hL : IsStarFree L) (hK : IsStarFree K) : IsStarFree (fun w => L w ∧ ¬K w) := by
  obtain ⟨e, he⟩ := hL
  obtain ⟨f, hf⟩ := hK
  exact ⟨.diff e f, fun w => and_congr (he w) (not_congr (hf w))⟩

theorem isStarFree_inter {U : Type} {L K : List U → Prop}
    (hL : IsStarFree L) (hK : IsStarFree K) : IsStarFree (fun w => L w ∧ K w) := by
  classical
  apply isStarFree_congr (isStarFree_diff hL (isStarFree_diff isStarFree_top hK))
  intro w
  simp

theorem isStarFree_concat {U : Type} {L K : List U → Prop}
    (hL : IsStarFree L) (hK : IsStarFree K) :
    IsStarFree (fun w => ∃ u v, u ++ v = w ∧ L u ∧ K v) := by
  obtain ⟨e, he⟩ := hL
  obtain ⟨f, hf⟩ := hK
  refine ⟨.concat e f, ?_⟩
  intro w
  simp only [sfDenote, he, hf]

theorem isStarFree_finset_union {U I : Type} (s : Finset I) (L : I → List U → Prop)
    (hL : ∀ i ∈ s, IsStarFree (L i)) : IsStarFree (fun w => ∃ i ∈ s, L i w) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact isStarFree_congr isStarFree_empty (by simp)
  | @insert i s hi ih =>
    apply isStarFree_congr (isStarFree_union (hL i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hL j (Finset.mem_insert_of_mem hj))))
    intro w
    simp

theorem isStarFree_finite_union {U I : Type} [Fintype I] (L : I → List U → Prop)
    (hL : ∀ i, IsStarFree (L i)) : IsStarFree (fun w => ∃ i, L i w) := by
  classical
  apply isStarFree_congr (isStarFree_finset_union Finset.univ L (fun i _ => hL i))
  simp

def WordOver {U : Type} (S : Finset U) (w : List U) : Prop := ∀ a ∈ w, a ∈ S

theorem wordOver_nil {U : Type} (S : Finset U) : WordOver S [] := by
  simp [WordOver]

theorem wordOver_cons {U : Type} (S : Finset U) (a : U) (w : List U) :
    WordOver S (a :: w) ↔ a ∈ S ∧ WordOver S w := by
  simp [WordOver]

theorem wordOver_append {U : Type} (S : Finset U) (u v : List U) :
    WordOver S (u ++ v) ↔ WordOver S u ∧ WordOver S v := by
  simp [WordOver, or_imp, forall_and]

theorem wordOver_empty_iff {U : Type} (w : List U) : WordOver ∅ w ↔ w = [] := by
  cases w with
  | nil => simp [WordOver]
  | cons a w => simp [wordOver_cons]

theorem wordOver_univ {U : Type} [Fintype U] (w : List U) : WordOver Finset.univ w := by
  simp [WordOver]

theorem isStarFree_contains {U : Type} (S : Finset U) :
    IsStarFree (fun w => ∃ a ∈ S, a ∈ w) := by
  have hs := isStarFree_finset_union S (fun a w => w = [a])
    (fun a _ => isStarFree_letter a)
  have ht := isStarFree_concat isStarFree_top (isStarFree_concat hs isStarFree_top)
  apply isStarFree_congr ht
  intro w
  constructor
  · rintro ⟨u, v, rfl, _, x, y, rfl, ⟨a, ha, rfl⟩, _⟩
    exact ⟨a, ha, by simp⟩
  · rintro ⟨a, ha, haw⟩
    obtain ⟨u, v, rfl⟩ := List.mem_iff_append.mp haw
    exact ⟨u, a :: v, rfl, trivial, [a], v, rfl, ⟨a, ha, rfl⟩, trivial⟩

/-- Restricting the alphabet uses complement relative to the original
ambient alphabet, so nested alphabet induction does not change its meaning. -/
theorem isStarFree_wordOver {U : Type} [Fintype U] (S : Finset U) :
    IsStarFree (WordOver S) := by
  classical
  apply isStarFree_congr (isStarFree_diff isStarFree_top
    (isStarFree_contains (Finset.univ \ S)))
  intro w
  simp [WordOver, Finset.mem_sdiff]
  constructor
  · intro h a ha
    by_contra hn
    exact h a hn ha
  · intro h a ha hw
    exact ha (h a hw)

theorem isStarFree_epsilon {U : Type} [Fintype U] :
    IsStarFree (fun w : List U => w = []) :=
  isStarFree_congr (isStarFree_wordOver ∅) wordOver_empty_iff

theorem isStarFree_word {U : Type} [Fintype U] (w : List U) :
    IsStarFree (fun v => v = w) := by
  induction w with
  | nil => exact isStarFree_epsilon
  | cons a w ih =>
    apply isStarFree_congr (isStarFree_concat (isStarFree_letter a) ih)
    intro v
    simp [eq_comm]

end FSS23105365

-- From Solutions.FSS23105365_DelimiterWords
set_option autoImplicit false
namespace FSS23105365

abbrev AlphabetBlock {U : Type} (B : Finset U) := {w : List U // WordOver B w}

def delimiterEncodeBlocks {U : Type} {B : Finset U} (c : U) (v : List (AlphabetBlock B)) : List U :=
  v.flatMap (fun w => w.val ++ [c])

theorem delimiterEncodeBlocks_nil {U : Type} {B : Finset U} (c : U) :
    delimiterEncodeBlocks c ([] : List (AlphabetBlock B)) = [] := rfl

theorem delimiterEncodeBlocks_cons {U : Type} {B : Finset U} (c : U)
    (v : AlphabetBlock B) (vs : List (AlphabetBlock B)) :
    delimiterEncodeBlocks c (v :: vs) = v.val ++ c :: delimiterEncodeBlocks c vs := by
  simp [delimiterEncodeBlocks, List.append_assoc]

theorem delimiterEncodeBlocks_append {U : Type} {B : Finset U} (c : U)
    (u v : List (AlphabetBlock B)) :
    delimiterEncodeBlocks c (u ++ v) = delimiterEncodeBlocks c u ++ delimiterEncodeBlocks c v := by
  simp [delimiterEncodeBlocks]

theorem delimiterEncodeBlocks_eq_nil {U : Type} {B : Finset U} (c : U)
    (v : List (AlphabetBlock B)) : delimiterEncodeBlocks c v = [] ↔ v = [] := by
  cases v with
  | nil => simp [delimiterEncodeBlocks_nil]
  | cons x xs => simp [delimiterEncodeBlocks_cons]

/-- The first occurrence of a delimiter determines both its preceding
block and the remaining suffix. -/
theorem delimiter_prefix_unique {U : Type} (c : U) (u v x y : List U)
    (hu : c ∉ u) (hv : c ∉ v) (he : u ++ c :: x = v ++ c :: y) :
    u = v ∧ x = y := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => exact ⟨rfl, (List.cons.inj he).2⟩
    | cons a v =>
      have ha : c = a := (List.cons.inj he).1
      exact (hv (by simp [ha])).elim
  | cons a u ih =>
    cases v with
    | nil =>
      have ha : a = c := (List.cons.inj he).1
      exact (hu (by simp [ha])).elim
    | cons b v =>
      obtain ⟨hab, huv⟩ := List.cons.inj he
      obtain ⟨rfl, hxy⟩ := ih v (fun h => hu (List.mem_cons_of_mem a h))
        (fun h => hv (List.mem_cons_of_mem b h)) huv
      exact ⟨by rw [hab], hxy⟩

theorem delimiterEncodeBlocks_injective {U : Type} {B : Finset U} (c : U) (hc : c ∉ B) :
    Function.Injective (delimiterEncodeBlocks (B := B) c) := by
  intro u
  induction u with
  | nil =>
    intro v he
    exact ((delimiterEncodeBlocks_eq_nil c v).mp he.symm).symm
  | cons a u ih =>
    intro v he
    cases v with
    | nil => exact (by simpa [delimiterEncodeBlocks_cons, delimiterEncodeBlocks_nil] using he : False).elim
    | cons b v =>
      rw [delimiterEncodeBlocks_cons, delimiterEncodeBlocks_cons] at he
      have ha : c ∉ a.val := fun h => hc (a.property c h)
      have hb : c ∉ b.val := fun h => hc (b.property c h)
      obtain ⟨hab, huv⟩ := delimiter_prefix_unique c _ _ _ _ ha hb he
      exact congrArg₂ List.cons (Subtype.ext hab) (ih huv)

/-- A word over S either avoids c entirely, or splits at its first and
last delimiter, with all intermediate blocks over S minus c. -/
theorem word_delimiter_factorization {U : Type} [DecidableEq U]
    (S : Finset U) (c : U) (w : List U) (hw : WordOver S w) :
    WordOver (S.erase c) w ∨
      ∃ p : AlphabetBlock (S.erase c), ∃ bs : List (AlphabetBlock (S.erase c)),
        ∃ s : AlphabetBlock (S.erase c), w = p.val ++ c :: (delimiterEncodeBlocks c bs ++ s.val) := by
  induction w with
  | nil => exact Or.inl (wordOver_nil _)
  | cons a w ih =>
    obtain ⟨ha, hw⟩ := (wordOver_cons S a w).mp hw
    rcases ih hw with hB | ⟨p, bs, s, he⟩
    · by_cases hac : a = c
      · subst a
        exact Or.inr ⟨⟨[], wordOver_nil _⟩, [], ⟨w, hB⟩, rfl⟩
      · exact Or.inl ((wordOver_cons _ _ _).mpr ⟨Finset.mem_erase.mpr ⟨hac, ha⟩, hB⟩)
    · by_cases hac : a = c
      · subst a
        refine Or.inr ⟨⟨[], wordOver_nil _⟩, p :: bs, s, ?_⟩
        simp only [List.nil_append, delimiterEncodeBlocks_cons, List.append_assoc, List.cons_append]
        exact congrArg (List.cons c) he
      · refine Or.inr ⟨⟨a :: p.val, (wordOver_cons _ _ _).mpr
          ⟨Finset.mem_erase.mpr ⟨hac, ha⟩, p.property⟩⟩, bs, s, ?_⟩
        exact congrArg (List.cons a) he

theorem delimiterEncodeBlocks_over {U : Type} {B S : Finset U} (c : U) (hc : c ∈ S)
    (hBS : B ⊆ S) (bs : List (AlphabetBlock B)) : WordOver S (delimiterEncodeBlocks c bs) := by
  induction bs with
  | nil => exact wordOver_nil _
  | cons b bs ih =>
    rw [delimiterEncodeBlocks_cons, wordOver_append, wordOver_cons]
    exact ⟨fun a ha => hBS (b.property a ha), hc, ih⟩

theorem delimiterEncodeBlocks_ends {U : Type} {B : Finset U} (c : U) (bs : List (AlphabetBlock B)) :
    delimiterEncodeBlocks c bs = [] ∨ ∃ v, delimiterEncodeBlocks c bs = v ++ [c] := by
  induction bs with
  | nil => exact Or.inl rfl
  | cons b bs ih =>
    rcases ih with he | ⟨v, hv⟩
    · exact Or.inr ⟨b.val, by rw [delimiterEncodeBlocks_cons, he]⟩
    · refine Or.inr ⟨b.val ++ c :: v, ?_⟩
      rw [delimiterEncodeBlocks_cons, hv]
      simp [List.append_assoc]

theorem delimiterEncodeBlocks_range {U : Type} [DecidableEq U] (S : Finset U) (c : U)
    (hc : c ∈ S) (w : List U) :
    (∃ bs : List (AlphabetBlock (S.erase c)), delimiterEncodeBlocks c bs = w) ↔
      WordOver S w ∧ (w = [] ∨ ∃ v, w = v ++ [c]) := by
  constructor
  · rintro ⟨bs, rfl⟩
    exact ⟨delimiterEncodeBlocks_over c hc (Finset.erase_subset _ _) bs, delimiterEncodeBlocks_ends c bs⟩
  · rintro ⟨hw, rfl | ⟨v, rfl⟩⟩
    · exact ⟨[], rfl⟩
    · have hv := ((wordOver_append S v [c]).mp hw).1
      rcases word_delimiter_factorization S c v hv with hB | ⟨p, bs, s, he⟩
      · exact ⟨[⟨v, hB⟩], by simp [delimiterEncodeBlocks_cons, delimiterEncodeBlocks_nil]⟩
      · refine ⟨p :: (bs ++ [s]), ?_⟩
        rw [delimiterEncodeBlocks_cons, delimiterEncodeBlocks_append, delimiterEncodeBlocks_cons, delimiterEncodeBlocks_nil, he]
        simp [List.append_assoc]

end FSS23105365

-- From Solutions.FSS23105365_StarFreeBlockCoding
set_option autoImplicit false
namespace FSS23105365

/-- Replace each letter of a block-label language by a delimiter-terminated
word. The delimiter cannot occur inside a block. -/
def BlockImageLanguage {U T : Type} (B : Finset U) (c : U) (label : List U → T)
    (L : List T → Prop) (w : List U) : Prop :=
  ∃ bs : List (AlphabetBlock B), delimiterEncodeBlocks c bs = w ∧ L (bs.map (fun b => label b.val))

theorem blockImage_union {U T : Type} (B : Finset U) (c : U) (label : List U → T)
    (L K : List T → Prop) (w : List U) :
    BlockImageLanguage B c label (fun v => L v ∨ K v) w ↔
      BlockImageLanguage B c label L w ∨ BlockImageLanguage B c label K w := by
  simp only [BlockImageLanguage, and_or_left, exists_or]

theorem blockImage_diff {U T : Type} (B : Finset U) (c : U) (hc : c ∉ B)
    (label : List U → T) (L K : List T → Prop) (w : List U) :
    BlockImageLanguage B c label (fun v => L v ∧ ¬K v) w ↔
      BlockImageLanguage B c label L w ∧ ¬BlockImageLanguage B c label K w := by
  constructor
  · rintro ⟨bs, he, hL, hK⟩
    refine ⟨⟨bs, he, hL⟩, ?_⟩
    rintro ⟨cs, hce, hcs⟩
    have hbc := delimiterEncodeBlocks_injective c hc (he.trans hce.symm)
    subst cs
    exact hK hcs
  · rintro ⟨⟨bs, he, hL⟩, hK⟩
    exact ⟨bs, he, hL, fun hb => hK ⟨bs, he, hb⟩⟩

theorem blockImage_concat {U T : Type} (B : Finset U) (c : U) (label : List U → T)
    (L K : List T → Prop) (w : List U) :
    BlockImageLanguage B c label (fun v => ∃ x y, x ++ y = v ∧ L x ∧ K y) w ↔
      ∃ u v, u ++ v = w ∧ BlockImageLanguage B c label L u ∧
        BlockImageLanguage B c label K v := by
  constructor
  · rintro ⟨bs, he, x, y, hxy, hL, hK⟩
    obtain ⟨us, vs, rfl, hu, hv⟩ := List.map_eq_append_iff.mp hxy.symm
    exact ⟨delimiterEncodeBlocks c us, delimiterEncodeBlocks c vs,
      (delimiterEncodeBlocks_append c us vs).symm.trans he,
      ⟨us, rfl, hu.symm ▸ hL⟩, ⟨vs, rfl, hv.symm ▸ hK⟩⟩
  · rintro ⟨u, v, rfl, ⟨us, rfl, hL⟩, ⟨vs, rfl, hK⟩⟩
    exact ⟨us ++ vs, delimiterEncodeBlocks_append c us vs, _, _, (List.map_append).symm, hL, hK⟩

theorem isStarFree_block_universe {U T : Type} [Fintype U] [DecidableEq U]
    (S : Finset U) (c : U) (hc : c ∈ S) (label : List U → T) :
    IsStarFree (BlockImageLanguage (S.erase c) c label (fun _ => True)) := by
  have hends := isStarFree_union isStarFree_epsilon
    (isStarFree_concat isStarFree_top (isStarFree_letter c))
  apply isStarFree_congr (isStarFree_inter (isStarFree_wordOver S) hends)
  intro w
  change _ ↔ ∃ bs, delimiterEncodeBlocks c bs = w ∧ True
  rw [show (∃ bs : List (AlphabetBlock (S.erase c)), delimiterEncodeBlocks c bs = w ∧ True) ↔
      ∃ bs : List (AlphabetBlock (S.erase c)), delimiterEncodeBlocks c bs = w by simp]
  rw [delimiterEncodeBlocks_range S c hc]
  simp [eq_comm]

theorem isStarFree_block_letter {U T : Type} (B : Finset U) (c : U)
    (label : List U → T) (t : T)
    (ht : IsStarFree (fun w => WordOver B w ∧ label w = t)) :
    IsStarFree (BlockImageLanguage B c label (fun v => v = [t])) := by
  apply isStarFree_congr (isStarFree_concat ht (isStarFree_letter c))
  intro w
  constructor
  · rintro ⟨u, v, rfl, ⟨hu, hl⟩, rfl⟩
    exact ⟨[⟨u, hu⟩], by simp [delimiterEncodeBlocks_cons, delimiterEncodeBlocks_nil], by simp [hl]⟩
  · rintro ⟨bs, he, hl⟩
    obtain ⟨b, rfl, hb⟩ := List.map_eq_singleton_iff.mp hl
    exact ⟨b.val, [c], by simpa [delimiterEncodeBlocks_cons, delimiterEncodeBlocks_nil] using he,
      ⟨b.property, hb⟩, rfl⟩

/-- Unique delimiter parsing makes block substitution preserve difference,
as well as union and concatenation. Each label fiber need only be star-free
on the smaller alphabet. -/
theorem isStarFree_block_image {U T : Type} [Fintype U] [DecidableEq U]
    (S : Finset U) (c : U) (hc : c ∈ S) (label : List U → T)
    (hlabel : ∀ t, IsStarFree (fun w => WordOver (S.erase c) w ∧ label w = t))
    {L : List T → Prop} (hL : IsStarFree L) :
    IsStarFree (BlockImageLanguage (S.erase c) c label L) := by
  obtain ⟨e, he⟩ := hL
  have hf : IsStarFree (BlockImageLanguage (S.erase c) c label (sfDenote e)) := by
    clear he
    induction e with
    | top => exact isStarFree_block_universe S c hc label
    | letter t => exact isStarFree_block_letter _ c label t (hlabel t)
    | union e f ihe ihf =>
      exact isStarFree_congr (isStarFree_union ihe ihf)
        (fun w => (blockImage_union _ c label (sfDenote e) (sfDenote f) w).symm)
    | diff e f ihe ihf =>
      exact isStarFree_congr (isStarFree_diff ihe ihf)
        (fun w => (blockImage_diff _ c (Finset.notMem_erase c S) label
          (sfDenote e) (sfDenote f) w).symm)
    | concat e f ihe ihf =>
      exact isStarFree_congr (isStarFree_concat ihe ihf)
        (fun w => (blockImage_concat _ c label (sfDenote e) (sfDenote f) w).symm)
  apply isStarFree_congr hf
  intro w
  simp only [BlockImageLanguage, he]

end FSS23105365

-- From Solutions.FSS23105365_LocalDivisor
set_option autoImplicit false
namespace FSS23105365

def MonoidAperiodic (M : Type) [Monoid M] : Prop :=
  ∀ x : M, ∃ n : ℕ, 0 < n ∧ x ^ n = x ^ (n + 1)

/-- In an aperiodic monoid, a product can equal the identity only when
both factors are the identity. No cancellation assumption is required. -/
theorem aperiodic_mul_eq_one {M : Type} [Monoid M] (hM : MonoidAperiodic M)
    (x y : M) (hxy : x * y = 1) : x = 1 ∧ y = 1 := by
  obtain ⟨n, _, hn⟩ := hM x
  have hpow : x ^ n * y ^ n = 1 := pow_mul_pow_eq_one n hxy
  have hx : x = 1 := by
    calc
      x = x * (x ^ n * y ^ n) := by rw [hpow, mul_one]
      _ = x ^ (n + 1) * y ^ n := by rw [pow_succ', mul_assoc]
      _ = x ^ n * y ^ n := by rw [← hn]
      _ = 1 := hpow
  exact ⟨hx, by simpa only [hx, one_mul] using hxy⟩

/-- The local divisor carrier is cM ∩ Mc. Its identity will be c and its
multiplication is (x*c) ∘ (c*y) = x*c*y, not ambient multiplication. -/
def LocalDivisor {M : Type} [Monoid M] (c : M) :=
  {z : M // (∃ x, c * x = z) ∧ ∃ y, y * c = z}

instance {M : Type} [Monoid M] [Fintype M] (c : M) : Fintype (LocalDivisor c) := by
  classical
  exact inferInstanceAs (Fintype {z : M // (∃ x, c * x = z) ∧ ∃ y, y * c = z})

def localRight {M : Type} [Monoid M] {c : M} (x : LocalDivisor c) : M :=
  Classical.choose x.property.1

def localLeft {M : Type} [Monoid M] {c : M} (x : LocalDivisor c) : M :=
  Classical.choose x.property.2

theorem localRight_spec {M : Type} [Monoid M] {c : M} (x : LocalDivisor c) :
    c * localRight x = x.val := Classical.choose_spec x.property.1

theorem localLeft_spec {M : Type} [Monoid M] {c : M} (x : LocalDivisor c) :
    localLeft x * c = x.val := Classical.choose_spec x.property.2

def localDivisorMul {M : Type} [Monoid M] {c : M} (x y : LocalDivisor c) : LocalDivisor c :=
  ⟨localLeft x * y.val, by
    constructor
    · refine ⟨localRight x * localRight y, ?_⟩
      rw [← mul_assoc, localRight_spec, ← localLeft_spec x, mul_assoc, localRight_spec]
    · refine ⟨localLeft x * localLeft y, ?_⟩
      rw [mul_assoc, localLeft_spec]⟩

theorem localDivisorMul_val_right {M : Type} [Monoid M] {c : M} (x y : LocalDivisor c) :
    (localDivisorMul x y).val = x.val * localRight y := by
  change localLeft x * y.val = _
  rw [← localRight_spec y, ← mul_assoc, localLeft_spec]

instance {M : Type} [Monoid M] (c : M) : Monoid (LocalDivisor c) where
  mul := localDivisorMul
  one := ⟨c, ⟨⟨1, mul_one c⟩, ⟨1, one_mul c⟩⟩⟩
  mul_assoc x y z := by
    apply Subtype.ext
    change (localDivisorMul (localDivisorMul x y) z).val =
      (localDivisorMul x (localDivisorMul y z)).val
    rw [localDivisorMul_val_right]
    change (localLeft x * y.val) * localRight z = localLeft x * (localDivisorMul y z).val
    rw [localDivisorMul_val_right, mul_assoc]
  one_mul x := by
    apply Subtype.ext
    exact (localDivisorMul_val_right _ x).trans (localRight_spec x)
  mul_one x := by
    apply Subtype.ext
    exact localLeft_spec x

theorem localDivisor_one_val {M : Type} [Monoid M] (c : M) :
    (1 : LocalDivisor c).val = c := rfl

theorem localDivisor_mul_val {M : Type} [Monoid M] {c : M} (x y : LocalDivisor c) :
    (x * y).val = x.val * localRight y := localDivisorMul_val_right x y

theorem localDivisor_mul_of_reps {M : Type} [Monoid M] {c : M}
    (a b : LocalDivisor c) (x y : M) (ha : x * c = a.val) (hb : c * y = b.val) :
    (a * b).val = x * c * y := by
  change localLeft a * b.val = _
  rw [← hb, ← mul_assoc, localLeft_spec, ← ha]

theorem localDivisor_pow_val {M : Type} [Monoid M] {c : M} (x : LocalDivisor c) (n : ℕ) :
    (x ^ n).val = c * localRight x ^ n := by
  induction n with
  | zero => simp [localDivisor_one_val]
  | succ n ih => rw [pow_succ, localDivisor_mul_val, ih, pow_succ, mul_assoc]

theorem localDivisor_aperiodic {M : Type} [Monoid M] (hM : MonoidAperiodic M) (c : M) :
    MonoidAperiodic (LocalDivisor c) := by
  intro x
  obtain ⟨n, hn, he⟩ := hM (localRight x)
  refine ⟨n, hn, Subtype.ext ?_⟩
  simp only [localDivisor_pow_val, he]

/-- A nonidentity local divisor of a finite aperiodic monoid is strictly
smaller. The missing element is the ambient identity. -/
theorem localDivisor_card_lt {M : Type} [Monoid M] [Fintype M]
    (hM : MonoidAperiodic M) (c : M) (hc : c ≠ 1) :
    Fintype.card (LocalDivisor c) < Fintype.card M := by
  classical
  apply Fintype.card_subtype_lt (p := fun z : M => (∃ x, c * x = z) ∧ ∃ y, y * c = z)
    (x := 1)
  rintro ⟨⟨x, hx⟩, _⟩
  exact hc (aperiodic_mul_eq_one hM c x hx).1

def localSandwich {M : Type} [Monoid M] (c x : M) : LocalDivisor c :=
  ⟨c * x * c, ⟨⟨x * c, (mul_assoc c x c).symm⟩, ⟨c * x, rfl⟩⟩⟩

theorem localSandwich_mul_val {M : Type} [Monoid M] (c x y : M) :
    (localSandwich c x * localSandwich c y).val = c * x * c * y * c := by
  rw [localDivisor_mul_of_reps _ _ (c * x) (y * c) rfl (mul_assoc c y c).symm]
  simp only [mul_assoc]

end FSS23105365

-- From Solutions.FSS23105365_MonoidFiberDecomposition
set_option autoImplicit false
namespace FSS23105365

def monoidWordValue {U M : Type} [Monoid M] (g : U → M) (w : List U) : M :=
  (w.map g).prod

theorem monoidWordValue_nil {U M : Type} [Monoid M] (g : U → M) :
    monoidWordValue g [] = 1 := rfl

theorem monoidWordValue_cons {U M : Type} [Monoid M] (g : U → M) (a : U) (w : List U) :
    monoidWordValue g (a :: w) = g a * monoidWordValue g w := rfl

theorem monoidWordValue_append {U M : Type} [Monoid M] (g : U → M) (u v : List U) :
    monoidWordValue g (u ++ v) = monoidWordValue g u * monoidWordValue g v := by
  simp [monoidWordValue]

def MonoidFiber {U M : Type} [Monoid M] (S : Finset U) (g : U → M) (p : M)
    (w : List U) : Prop := WordOver S w ∧ monoidWordValue g w = p

/-- Local multiplication deletes exactly one copy of the delimiter at
each joining point, matching the original word product. -/
theorem local_block_product {U M : Type} [Monoid M] (g : U → M) (c : U)
    (B : Finset U) (bs : List (AlphabetBlock B)) :
    ((bs.map (fun b => localSandwich (g c) (monoidWordValue g b.val))).prod).val =
      monoidWordValue g (c :: delimiterEncodeBlocks c bs) := by
  induction bs with
  | nil => simp [delimiterEncodeBlocks_nil, monoidWordValue, localDivisor_one_val]
  | cons b bs ih =>
    rw [List.map_cons, List.prod_cons]
    rw [localDivisor_mul_of_reps _ _ (g c * monoidWordValue g b.val)
      (monoidWordValue g (delimiterEncodeBlocks c bs)) rfl (by
        rw [ih, monoidWordValue_cons])]
    rw [delimiterEncodeBlocks_cons, monoidWordValue_cons, monoidWordValue_append,
      monoidWordValue_cons]
    simp only [mul_assoc]

def LocalCentralLanguage {U M : Type} [Monoid M] (B : Finset U) (c : U) (g : U → M)
    (p : LocalDivisor (g c)) (w : List U) : Prop :=
  ∃ bs : List (AlphabetBlock B), w = c :: delimiterEncodeBlocks c bs ∧
    (bs.map (fun b => localSandwich (g c) (monoidWordValue g b.val))).prod = p

theorem localCentral_value {U M : Type} [Monoid M] (B : Finset U) (c : U) (g : U → M)
    (p : LocalDivisor (g c)) (w : List U) (hw : LocalCentralLanguage B c g p w) :
    monoidWordValue g w = p.val := by
  obtain ⟨bs, rfl, he⟩ := hw
  rw [← local_block_product g c B bs, he]

theorem localCentral_over {U M : Type} [Monoid M] (B S : Finset U) (c : U)
    (hc : c ∈ S) (hBS : B ⊆ S) (g : U → M) (p : LocalDivisor (g c)) (w : List U)
    (hw : LocalCentralLanguage B c g p w) : WordOver S w := by
  obtain ⟨bs, rfl, _⟩ := hw
  exact (wordOver_cons S c _).mpr ⟨hc, delimiterEncodeBlocks_over c hc hBS bs⟩

theorem monoidFiber_decomposition {U M : Type} [DecidableEq U] [Monoid M]
    (S : Finset U) (c : U) (hc : c ∈ S) (g : U → M) (p : M) (w : List U) :
    MonoidFiber S g p w ↔ MonoidFiber (S.erase c) g p w ∨
      ∃ p₁ : M, ∃ p₂ : LocalDivisor (g c), ∃ p₃ : M, p₁ * p₂.val * p₃ = p ∧
        ∃ u v z, u ++ v ++ z = w ∧ MonoidFiber (S.erase c) g p₁ u ∧
          LocalCentralLanguage (S.erase c) c g p₂ v ∧ MonoidFiber (S.erase c) g p₃ z := by
  constructor
  · rintro ⟨hw, hp⟩
    rcases word_delimiter_factorization S c w hw with hB | ⟨u, bs, z, he⟩
    · exact Or.inl ⟨hB, hp⟩
    · let p₂ := (bs.map (fun b => localSandwich (g c) (monoidWordValue g b.val))).prod
      have hv : p₂.val = monoidWordValue g (c :: delimiterEncodeBlocks c bs) :=
        local_block_product g c _ bs
      have he' : u.val ++ (c :: delimiterEncodeBlocks c bs) ++ z.val = w := by
        rw [he]
        simp only [List.append_assoc, List.cons_append]
      refine Or.inr ⟨monoidWordValue g u.val, p₂, monoidWordValue g z.val, ?_,
        u.val, c :: delimiterEncodeBlocks c bs, z.val, he', ⟨u.property, rfl⟩,
        ⟨bs, rfl, rfl⟩, ⟨z.property, rfl⟩⟩
      rw [hv, ← monoidWordValue_append, ← monoidWordValue_append, he', hp]
  · rintro (⟨hw, hp⟩ | ⟨p₁, p₂, p₃, hp, u, v, z, rfl, hu, hv, hz⟩)
    · exact ⟨fun a ha => Finset.mem_of_mem_erase (hw a ha), hp⟩
    · constructor
      · rw [wordOver_append, wordOver_append]
        exact ⟨⟨fun a ha => Finset.mem_of_mem_erase (hu.1 a ha),
          localCentral_over _ _ c hc (Finset.erase_subset _ _) g p₂ v hv⟩,
          fun a ha => Finset.mem_of_mem_erase (hz.1 a ha)⟩
      · rw [monoidWordValue_append, monoidWordValue_append, hu.2, hz.2,
          localCentral_value _ c g p₂ v hv, hp]

theorem isStarFree_localCentral {U M : Type} [Fintype U] [DecidableEq U] [Monoid M]
    (S : Finset U) (c : U) (hc : c ∈ S) (g : U → M) (p : LocalDivisor (g c))
    (hB : ∀ t, IsStarFree (MonoidFiber (S.erase c) g t))
    (hp : IsStarFree (fun ts : List M => monoidWordValue (localSandwich (g c)) ts = p)) :
    IsStarFree (LocalCentralLanguage (S.erase c) c g p) := by
  have hi := isStarFree_block_image S c hc (monoidWordValue g) hB hp
  apply isStarFree_congr (isStarFree_concat (isStarFree_letter c) hi)
  intro w
  constructor
  · rintro ⟨u, v, rfl, rfl, bs, rfl, hbs⟩
    exact ⟨bs, rfl, by simpa [monoidWordValue, List.map_map, Function.comp_def] using hbs⟩
  · rintro ⟨bs, rfl, hbs⟩
    refine ⟨[c], delimiterEncodeBlocks c bs, rfl, rfl, bs, rfl, ?_⟩
    simpa [monoidWordValue, List.map_map, Function.comp_def] using hbs

theorem isStarFree_concat_three {U : Type} {L K J : List U → Prop}
    (hL : IsStarFree L) (hK : IsStarFree K) (hJ : IsStarFree J) :
    IsStarFree (fun w => ∃ u v z, u ++ v ++ z = w ∧ L u ∧ K v ∧ J z) := by
  apply isStarFree_congr (isStarFree_concat (isStarFree_concat hL hK) hJ)
  intro w
  constructor
  · rintro ⟨uv, z, rfl, ⟨u, v, rfl, hu, hv⟩, hz⟩
    exact ⟨u, v, z, rfl, hu, hv, hz⟩
  · rintro ⟨u, v, z, rfl, hu, hv, hz⟩
    exact ⟨u ++ v, z, rfl, ⟨u, v, rfl, hu, hv⟩, hz⟩

/-- One induction step: remove c from the alphabet and recurse through
the local divisor of g(c), then assemble the finite union of all products. -/
theorem isStarFree_monoidFiber_step {U M : Type} [Fintype U] [DecidableEq U]
    [Monoid M] [Fintype M] (S : Finset U) (c : U) (hc : c ∈ S) (g : U → M)
    (hB : ∀ t, IsStarFree (MonoidFiber (S.erase c) g t))
    (hlocal : ∀ p : LocalDivisor (g c),
      IsStarFree (fun ts : List M => monoidWordValue (localSandwich (g c)) ts = p))
    (p : M) : IsStarFree (MonoidFiber S g p) := by
  classical
  have hmid := fun q => isStarFree_localCentral S c hc g q hB (hlocal q)
  have hs : IsStarFree (fun w =>
      ∃ p₁ : M, ∃ p₂ : LocalDivisor (g c), ∃ p₃ : M, p₁ * p₂.val * p₃ = p ∧
        ∃ u v z, u ++ v ++ z = w ∧ MonoidFiber (S.erase c) g p₁ u ∧
          LocalCentralLanguage (S.erase c) c g p₂ v ∧ MonoidFiber (S.erase c) g p₃ z) := by
    apply isStarFree_finite_union
    intro p₁
    apply isStarFree_finite_union
    intro p₂
    apply isStarFree_finite_union
    intro p₃
    by_cases he : p₁ * p₂.val * p₃ = p
    · exact isStarFree_congr (isStarFree_concat_three (hB p₁) (hmid p₂) (hB p₃))
        (fun w => by simp [he])
    · exact isStarFree_congr isStarFree_empty (fun w => by simp [he])
  exact isStarFree_congr (isStarFree_union (hB p) hs)
    (fun w => (monoidFiber_decomposition S c hc g p w).symm)

end FSS23105365

-- From Solutions.FSS23105365_Aperiodicity
set_option autoImplicit false
namespace FSS23105365
open Function

/-- Every point on a positive-length closed orbit is a fixed point. This
excludes exactly the directed cycles of length at least two. -/
def NoNontrivialCycle {H : Type} (g : H → H) : Prop :=
  ∀ x k, 0 < k → g^[k] x = x → g x = x

/-- The pointwise finite-orbit argument gives the explicit stabilization
bound `card H`, including when the state set is empty. -/
theorem iterate_card_fixed_of_no_cycle {H : Type} [Fintype H]
    (g : H → H) (hg : NoNontrivialCycle g) (x : H) :
    g (g^[Fintype.card H] x) = g^[Fintype.card H] x := by
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Fintype.card H + 1) => g^[i.val] x) (by simp)
  have hp : ∃ a b : ℕ, a < b ∧ b ≤ Fintype.card H ∧ g^[a] x = g^[b] x := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i.val, j.val, h, Nat.le_of_lt_succ j.isLt, heq⟩
    · exact ⟨j.val, i.val, h, Nat.le_of_lt_succ i.isLt, heq.symm⟩
  obtain ⟨a, b, hab, hb, he⟩ := hp
  have hperiod : g^[b - a] (g^[a] x) = g^[a] x := by
    rw [← iterate_add_apply, Nat.sub_add_cancel hab.le]
    exact he.symm
  have hfix : IsFixedPt g (g^[a] x) := hg _ _ (Nat.sub_pos_of_lt hab) hperiod
  have hc : g^[Fintype.card H] x = g^[a] x := by
    rw [← Nat.sub_add_cancel (hab.le.trans hb), iterate_add_apply]
    exact hfix.iterate (Fintype.card H - a)
  rw [hc]
  exact hfix

/-- Lemma A.2: a finite self-map is eventually idempotent under iteration
exactly when it has no nontrivial cycle. -/
theorem cycle_criterion {H : Type} [Fintype H] (g : H → H) :
    (∃ k : ℕ, 0 < k ∧ g^[k] = g^[k + 1]) ↔ NoNontrivialCycle g := by
  constructor
  · rintro ⟨k, _, hk⟩ x n hn hx
    have hp : IsPeriodicPt g n x := hx
    have he : g^[k] x = g^[k] (g x) := by
      rw [← iterate_succ_apply]
      exact congrFun hk x
    exact ((hp.iterate k).eq_of_apply_eq_same (hp.apply.iterate k) hn he).symm
  · intro hg
    refine ⟨Fintype.card H + 1, by omega, ?_⟩
    funext x
    have hfix := iterate_card_fixed_of_no_cycle g hg x
    simp only [iterate_succ_apply']
    simp only [hfix]

/-- An order-preserving map on a linear order has no nontrivial cycle. -/
theorem monotone_no_nontrivial_cycle {H : Type} [LinearOrder H]
    (g : H → H) (hg : Monotone g) : NoNontrivialCycle g := by
  intro x n hn hx
  rcases le_total x (g x) with h | h
  · apply le_antisymm _ h
    have hm := hg.monotone_iterate_of_le_map h (show 1 ≤ n by omega)
    simpa [hx] using hm
  · apply le_antisymm h
    have hm := hg.antitone_iterate_of_map_le h (show 1 ≤ n by omega)
    simpa [hx] using hm

/-- Aperiodicity of the word-induced transition maps, with the positive
exponent convention used in the paper. -/
def AperiodicTransitions {H U : Type} (τ : H → U → H) : Prop :=
  ∀ w : List U, ∃ k : ℕ, 0 < k ∧
    (fun h => w.foldl τ h)^[k] = (fun h => w.foldl τ h)^[k + 1]

theorem aperiodicTransitions_iff_no_cycles {H U : Type} [Fintype H]
    (τ : H → U → H) :
    AperiodicTransitions τ ↔ ∀ w : List U, NoNontrivialCycle (fun h => w.foldl τ h) := by
  simp only [AperiodicTransitions, cycle_criterion]

/-- This is the terminal-component implication used in Lemma 3.5. -/
theorem monotone_transitions_aperiodic {H U : Type} [Fintype H] [LinearOrder H]
    (τ : H → U → H) (hτ : ∀ u, Monotone (fun h => τ h u)) :
    AperiodicTransitions τ := by
  apply (aperiodicTransitions_iff_no_cycles τ).mpr
  intro w
  apply monotone_no_nontrivial_cycle
  induction w with
  | nil => exact monotone_id
  | cons u w ih => exact ih.comp (hτ u)

end FSS23105365

-- From Solutions.FSS23105365_TransitionMonoid
set_option autoImplicit false
namespace FSS23105365

/-- Transformation multiplication is in reading order: f*g first applies
f, then g, matching the DFA's left fold on an input word. -/
def RunTransform (H : Type) := H → H

instance {H : Type} : Monoid (RunTransform H) where
  mul f g := fun h => g (f h)
  one := id
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

instance {H : Type} [Fintype H] : Fintype (RunTransform H) := by
  classical
  exact inferInstanceAs (Fintype (H → H))

theorem runTransform_pow_apply {H : Type} (f : RunTransform H) (n : ℕ) (h : H) :
    (f ^ n) h = (fun x => f x)^[n] h := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ]
    change f ((f ^ n) h) = (fun x => f x)^[n + 1] h
    rw [ih, Function.iterate_succ_apply']

def wordTransform {H U : Type} (τ : H → U → H) (w : List U) : RunTransform H :=
  fun h => w.foldl τ h

theorem wordTransform_append {H U : Type} (τ : H → U → H) (u v : List U) :
    wordTransform τ (u ++ v) = wordTransform τ u * wordTransform τ v := by
  funext h
  exact List.foldl_append

def transitionSubmonoid {H U : Type} (τ : H → U → H) : Submonoid (RunTransform H) where
  carrier := {f | ∃ w : List U, wordTransform τ w = f}
  one_mem' := ⟨[], rfl⟩
  mul_mem' := by
    rintro f g ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u ++ v, wordTransform_append τ u v⟩

abbrev TransitionMonoid {H U : Type} (τ : H → U → H) := transitionSubmonoid τ

instance {H U : Type} [Fintype H] (τ : H → U → H) : Fintype (TransitionMonoid τ) := by
  classical
  exact inferInstanceAs (Fintype {f : RunTransform H // f ∈ transitionSubmonoid τ})

def wordTransition {H U : Type} (τ : H → U → H) (w : List U) : TransitionMonoid τ :=
  ⟨wordTransform τ w, w, rfl⟩

theorem wordTransition_nil {H U : Type} (τ : H → U → H) : wordTransition τ [] = 1 := rfl

theorem wordTransition_append {H U : Type} (τ : H → U → H) (u v : List U) :
    wordTransition τ (u ++ v) = wordTransition τ u * wordTransition τ v :=
  Subtype.ext (wordTransform_append τ u v)

theorem wordTransition_apply {H U : Type} (τ : H → U → H) (w : List U) (h : H) :
    (wordTransition τ w).val h = w.foldl τ h := rfl

theorem wordTransition_product {H U : Type} (τ : H → U → H) (w : List U) :
    (w.map (fun u => wordTransition τ [u])).prod = wordTransition τ w := by
  induction w with
  | nil => rfl
  | cons u w ih =>
    rw [List.map_cons, List.prod_cons, ih]
    exact (wordTransition_append τ [u] w).symm

/-- The already-used DFA aperiodicity definition supplies precisely a
finite aperiodic recognizing monoid, with no new algebraic assumption. -/
theorem transitionMonoid_aperiodic {H U : Type} (τ : H → U → H)
    (hτ : AperiodicTransitions τ) : MonoidAperiodic (TransitionMonoid τ) := by
  intro x
  obtain ⟨w, hw⟩ := x.property
  obtain ⟨n, hn, he⟩ := hτ w
  refine ⟨n, hn, Subtype.ext ?_⟩
  change x.val ^ n = x.val ^ (n + 1)
  rw [← hw]
  funext h
  rw [runTransform_pow_apply, runTransform_pow_apply]
  exact congrFun he h

/-- State-to-state word languages are recognized by this monoid's
evaluation map at the selected start state. -/
theorem transitionMonoid_recognizes_run {H U : Type} (τ : H → U → H)
    (s t : H) (w : List U) :
    ((w.map (fun u => wordTransition τ [u])).prod).val s = t ↔ w.foldl τ s = t := by
  rw [wordTransition_product, wordTransition_apply]

end FSS23105365

-- From Solutions.FSS23105365_AperiodicStarFree
set_option autoImplicit false
namespace FSS23105365

theorem monoidWordValue_all_one {U M : Type} [Monoid M] (S : Finset U) (g : U → M)
    (hg : ∀ a ∈ S, g a = 1) (w : List U) (hw : WordOver S w) :
    monoidWordValue g w = 1 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    obtain ⟨ha, hw⟩ := (wordOver_cons S a w).mp hw
    rw [monoidWordValue_cons, hg a ha, ih hw, one_mul]

/-- The finite aperiodic monoid theorem, proved by induction on monoid
cardinality and then on the active alphabet. No language-theory theorem
is assumed: the local divisor step strictly decreases the first measure. -/
theorem aperiodic_monoid_fibers_starFree {U M : Type} [Fintype U] [Monoid M] [Fintype M]
    (hM : MonoidAperiodic M) (S : Finset U) (g : U → M) (p : M) :
    IsStarFree (MonoidFiber S g p) := by
  classical
  have main : ∀ n : ℕ, ∀ (N : Type) [Monoid N] [Fintype N],
      Fintype.card N = n → MonoidAperiodic N →
      ∀ (A : Type) [Fintype A] (T : Finset A) (f : A → N) (q : N),
        IsStarFree (MonoidFiber T f q) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro N instN finN hn hN A finA T
      induction T using Finset.strongInductionOn with
      | _ T ihT =>
        intro f q
        by_cases hall : ∀ a ∈ T, f a = 1
        · by_cases hq : q = 1
          · subst q
            apply isStarFree_congr (isStarFree_wordOver T)
            intro w
            exact ⟨fun hw => ⟨hw, monoidWordValue_all_one T f hall w hw⟩, And.left⟩
          · apply isStarFree_congr isStarFree_empty
            intro w
            constructor
            · exact False.elim
            · rintro ⟨hw, hval⟩
              exact hq (hval.symm.trans (monoidWordValue_all_one T f hall w hw))
        · push_neg at hall
          obtain ⟨c, hc, hfc⟩ := hall
          have hB : ∀ t, IsStarFree (MonoidFiber (T.erase c) f t) :=
            fun t => ihT (T.erase c) (Finset.erase_ssubset hc) f t
          have hsmall : Fintype.card (LocalDivisor (f c)) < n := by
            rw [← hn]
            exact localDivisor_card_lt hN (f c) hfc
          have hlocal : ∀ t : LocalDivisor (f c),
              IsStarFree (fun ts : List N => monoidWordValue (localSandwich (f c)) ts = t) := by
            intro t
            have ht := ih _ hsmall (LocalDivisor (f c)) rfl
              (localDivisor_aperiodic hN (f c)) N Finset.univ (localSandwich (f c)) t
            apply isStarFree_congr ht
            intro ts
            exact and_iff_right (wordOver_univ ts)
          exact isStarFree_monoidFiber_step T c hc f hB hlocal q
  exact main (Fintype.card M) M rfl hM U S g p

theorem aperiodic_monoid_word_fiber_starFree {U M : Type} [Fintype U] [Monoid M]
    [Fintype M] (hM : MonoidAperiodic M) (g : U → M) (p : M) :
    IsStarFree (fun w => monoidWordValue g w = p) := by
  apply isStarFree_congr (aperiodic_monoid_fibers_starFree hM Finset.univ g p)
  intro w
  exact and_iff_right (wordOver_univ w)

/-- Every state-to-state language of a finite aperiodic transition system
has an actual star-free expression over the same alphabet. -/
theorem aperiodic_run_language_starFree {H U : Type} [Fintype H] [Fintype U]
    (τ : H → U → H) (hτ : AperiodicTransitions τ) (s t : H) :
    IsStarFree (fun w : List U => w.foldl τ s = t) := by
  classical
  let g : U → TransitionMonoid τ := fun u => wordTransition τ [u]
  have hf : ∀ p : TransitionMonoid τ,
      IsStarFree (fun w => monoidWordValue g w = p ∧ p.val s = t) := by
    intro p
    by_cases hp : p.val s = t
    · exact isStarFree_congr (aperiodic_monoid_word_fiber_starFree
        (transitionMonoid_aperiodic τ hτ) g p) (fun w => by simp [hp])
    · exact isStarFree_congr isStarFree_empty (fun w => by simp [hp])
  apply isStarFree_congr (isStarFree_finite_union _ hf)
  intro w
  constructor
  · rintro ⟨p, rfl, hp⟩
    exact (transitionMonoid_recognizes_run τ s t w).mp hp
  · intro hw
    exact ⟨monoidWordValue g w, rfl, (transitionMonoid_recognizes_run τ s t w).mpr hw⟩

end FSS23105365

-- From Solutions.FSS23105365_StarFreeFormula
set_option autoImplicit false
namespace FSS23105365

/-- Compile a star-free expression using supplied letter-test formulas.
Concatenation is an OR over every cut, including the empty prefix/suffix. -/
def sfFormula {U : Type} {r : ℕ} (e : StarFreeExpr U) (n : ℕ)
    (atom : Fin n → U → CircuitFormula r) : CircuitFormula r :=
  match e with
  | .top => .constant true
  | .letter a => if hn : n = 1 then atom ⟨0, by omega⟩ a else .constant false
  | .union e f => formulaOr (sfFormula e n atom) (sfFormula f n atom)
  | .diff e f => formulaAnd (sfFormula e n atom) (.neg (sfFormula f n atom))
  | .concat e f => .any (n + 1) (fun t =>
      formulaAnd (sfFormula e t.val (fun i => atom (wordCutLeft t i)))
        (sfFormula f (n - t.val) (fun i => atom (wordCutRight t i))))

theorem sfFormula_correct {U : Type} {r : ℕ} (e : StarFreeExpr U) (n : ℕ)
    (atom : Fin n → U → CircuitFormula r) (x : Fin n → U) (seed : Bits r)
    (ha : ∀ i a, formulaEval (atom i a) seed = true ↔ x i = a) :
    formulaEval (sfFormula e n atom) seed = true ↔ sfDenote e (List.ofFn x) := by
  induction e generalizing n with
  | top => simp [sfFormula, formulaEval, sfDenote]
  | letter a =>
    by_cases hn : n = 1
    · subst n
      simp only [sfFormula, ↓reduceDIte, sfDenote, ha]
      simp [List.ofFn_succ]
    · have hne : List.ofFn x ≠ [a] := by
        intro h
        have := congrArg List.length h
        simp only [List.length_ofFn, List.length_singleton] at this
        exact hn this
      simp [sfFormula, hn, formulaEval, sfDenote, hne]
  | union e f ihe ihf =>
    simpa only [sfFormula, formulaOr_eval, Bool.or_eq_true, sfDenote] using
      or_congr (ihe n atom x ha) (ihf n atom x ha)
  | diff e f ihe ihf =>
    have hn : (!formulaEval (sfFormula f n atom) seed) = true ↔
        ¬sfDenote f (List.ofFn x) := by
      rw [← ihf n atom x ha]
      cases formulaEval (sfFormula f n atom) seed <;> simp
    simpa only [sfFormula, formulaAnd_eval, Bool.and_eq_true, formulaEval, sfDenote] using
      and_congr (ihe n atom x ha) hn
  | concat e f ihe ihf =>
    rw [sfFormula, formulaAny_true_iff, sfDenote_concat_cut]
    apply exists_congr
    intro t
    rw [formulaAnd_eval, Bool.and_eq_true]
    exact and_congr
      (ihe t.val _ (fun i => x (wordCutLeft t i)) (fun i a => ha (wordCutLeft t i) a))
      (ihf (n - t.val) _ (fun i => x (wordCutRight t i)) (fun i a => ha (wordCutRight t i) a))

end FSS23105365

-- From Solutions.FSS23105365_StarFreeBounds
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

def sfDepthBound {U : Type} : StarFreeExpr U → ℕ → ℕ
  | .top, _ => 1
  | .letter _, D => D + 1
  | .union e f, D => max (sfDepthBound e D) (sfDepthBound f D) + 1
  | .diff e f, D => max (sfDepthBound e D) (sfDepthBound f D) + 2
  | .concat e f, D => max (sfDepthBound e D) (sfDepthBound f D) + 2

def sfExponent {U : Type} : StarFreeExpr U → ℕ
  | .top => 0
  | .letter _ => 0
  | .union e f => max (sfExponent e) (sfExponent f)
  | .diff e f => max (sfExponent e) (sfExponent f)
  | .concat e f => max (sfExponent e) (sfExponent f) + 1

def sfCoefficient {U : Type} : StarFreeExpr U → ℕ → ℕ
  | .top, _ => 1
  | .letter _, A => A + 1
  | .union e f, A => sfCoefficient e A + sfCoefficient f A + 3
  | .diff e f, A => sfCoefficient e A + sfCoefficient f A + 5
  | .concat e f, A => sfCoefficient e A + sfCoefficient f A + 5

theorem monomial_bound_mono (C n m p q : ℕ) (hn : n ≤ m) (hp : p ≤ q) :
    C * (n + 1) ^ p ≤ C * (m + 1) ^ q := by
  apply Nat.mul_le_mul_left
  exact (pow_le_pow_left' (Nat.add_le_add_right hn 1) p).trans
    (pow_le_pow_right' (by omega : 1 ≤ m + 1) hp)

theorem polynomial_pair_bound (a b A B n p q t : ℕ)
    (ha : a ≤ A * (n + 1) ^ p) (hb : b ≤ B * (n + 1) ^ q) :
    a + b + t ≤ (A + B + t) * (n + 1) ^ max p q := by
  have hA := ha.trans (monomial_bound_mono A n n p (max p q) le_rfl (Nat.le_max_left _ _))
  have hB := hb.trans (monomial_bound_mono B n n q (max p q) le_rfl (Nat.le_max_right _ _))
  have hone := Nat.one_le_pow' (max p q) n
  have ht := Nat.mul_le_mul_left t hone
  nlinarith

/-- Depth depends on the fixed expression and atomic-test depth, and is
independent of the word length, including at concatenation nodes. -/
theorem sfFormula_depth_bound {U : Type} {r : ℕ} (e : StarFreeExpr U) (n : ℕ)
    (atom : Fin n → U → CircuitFormula r) (D : ℕ)
    (ha : ∀ i a, formulaDepth (atom i a) ≤ D) :
    formulaDepth (sfFormula e n atom) ≤ sfDepthBound e D := by
  induction e generalizing n with
  | top => exact le_rfl
  | letter a =>
    unfold sfFormula
    split_ifs with hn
    · exact (ha _ _).trans (Nat.le_succ _)
    · change 1 ≤ D + 1
      omega
  | union e f ihe ihf =>
    simp only [sfFormula, formulaOr_depth, sfDepthBound]
    exact Nat.add_le_add_right (max_le_max (ihe n atom ha) (ihf n atom ha)) 1
  | diff e f ihe ihf =>
    simp only [sfFormula, formulaAnd_depth, formulaDepth, sfDepthBound]
    have he := ihe n atom ha
    have hf := ihf n atom ha
    omega
  | concat e f ihe ihf =>
    have h : ∀ t : Fin (n + 1), formulaDepth
        (formulaAnd (sfFormula e t.val (fun i => atom (wordCutLeft t i)))
          (sfFormula f (n - t.val) (fun i => atom (wordCutRight t i)))) ≤
        max (sfDepthBound e D) (sfDepthBound f D) + 1 := by
      intro t
      rw [formulaAnd_depth]
      exact Nat.add_le_add_right (max_le_max
        (ihe t.val _ (fun i a => ha (wordCutLeft t i) a))
        (ihf (n - t.val) _ (fun i a => ha (wordCutRight t i) a))) 1
    have hs := Finset.sup_le (s := Finset.univ) (fun t _ => h t)
    change Finset.univ.sup _ + 1 ≤ _
    change _ ≤ max (sfDepthBound e D) (sfDepthBound f D) + 2
    simpa only [Nat.add_assoc] using Nat.add_le_add_right hs 1

/-- Every concatenation adds at most one polynomial degree. The constant
charges all Boolean gates and every source-wire occurrence. -/
theorem sfFormula_cost_bound {U : Type} {r : ℕ} (e : StarFreeExpr U) (n : ℕ)
    (atom : Fin n → U → CircuitFormula r) (A : ℕ)
    (ha : ∀ i a, formulaCost (atom i a) ≤ A) :
    formulaCost (sfFormula e n atom) ≤ sfCoefficient e A * (n + 1) ^ sfExponent e := by
  induction e generalizing n with
  | top => simp [sfFormula, formulaCost, sfCoefficient, sfExponent]
  | letter a =>
    simp only [sfFormula, sfCoefficient, sfExponent, pow_zero, Nat.mul_one]
    split_ifs
    · exact (ha _ _).trans (Nat.le_succ _)
    · change 1 ≤ A + 1
      omega
  | union e f ihe ihf =>
    simp only [sfFormula, formulaOr_cost, sfCoefficient, sfExponent]
    exact polynomial_pair_bound _ _ _ _ n _ _ 3 (ihe n atom ha) (ihf n atom ha)
  | diff e f ihe ihf =>
    have h := polynomial_pair_bound _ _ _ _ n _ _ 5 (ihe n atom ha) (ihf n atom ha)
    simp only [sfFormula, formulaAnd_cost, formulaCost, sfCoefficient, sfExponent]
    omega
  | concat e f ihe ihf =>
    let K := sfCoefficient e A + sfCoefficient f A + 3
    let p := max (sfExponent e) (sfExponent f)
    have hterm : ∀ t : Fin (n + 1), formulaCost
        (formulaAnd (sfFormula e t.val (fun i => atom (wordCutLeft t i)))
          (sfFormula f (n - t.val) (fun i => atom (wordCutRight t i)))) ≤ K * (n + 1) ^ p := by
      intro t
      rw [formulaAnd_cost]
      exact polynomial_pair_bound _ _ _ _ n _ _ 3
        ((ihe t.val _ (fun i a => ha (wordCutLeft t i) a)).trans
          (monomial_bound_mono _ t.val n _ _ (by omega) le_rfl))
        ((ihf (n - t.val) _ (fun i a => ha (wordCutRight t i) a)).trans
          (monomial_bound_mono _ (n - t.val) n _ _ (Nat.sub_le _ _) le_rfl))
    have hsum : (∑ t : Fin (n + 1), formulaCost
        (formulaAnd (sfFormula e t.val (fun i => atom (wordCutLeft t i)))
          (sfFormula f (n - t.val) (fun i => atom (wordCutRight t i))))) ≤
        (n + 1) * (K * (n + 1) ^ p) := by
      simpa using Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hterm t)
    change (∑ t, formulaCost _) + 1 + (n + 1) ≤ _
    change _ ≤ (K + 2) * (n + 1) ^ (p + 1)
    rw [pow_succ]
    have hone := Nat.one_le_pow' p n
    have hp := Nat.mul_le_mul_left (n + 1) hone
    nlinarith

end FSS23105365

-- From Solutions.FSS23105365_StarFreeCircuits
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

def blockInputWire (b n : ℕ) (i : Fin n) (j : Fin b) : Fin (n * b) :=
  finProdFinEquiv (i, j)

def decodedLetterWord {U : Type} {b : ℕ} (decode : Bits b → U) {n : ℕ}
    (seed : Bits (n * b)) : Fin n → U :=
  fun i => decode (fun j => seed (blockInputWire b n i j))

def sfLetterAtom {U : Type} [DecidableEq U] {b : ℕ} (decode : Bits b → U) (n : ℕ)
    (i : Fin n) (a : U) : CircuitFormula (n * b) :=
  relabelFormula (blockInputWire b n i) (truthTableFormula (fun w => decide (decode w = a)))

theorem sfLetterAtom_correct {U : Type} [DecidableEq U] {b n : ℕ} (decode : Bits b → U)
    (seed : Bits (n * b)) (i : Fin n) (a : U) :
    formulaEval (sfLetterAtom decode n i a) seed = true ↔ decodedLetterWord decode seed i = a := by
  simp only [sfLetterAtom, relabelFormula_eval, truthTableFormula_eval, decide_eq_true_eq,
    decodedLetterWord]

theorem sfLetterAtom_depth {U : Type} [DecidableEq U] {b n : ℕ} (decode : Bits b → U)
    (i : Fin n) (a : U) : formulaDepth (sfLetterAtom decode n i a) ≤ 3 := by
  rw [sfLetterAtom, relabelFormula_depth]
  exact truthTableFormula_depth _

theorem sfLetterAtom_cost {U : Type} [DecidableEq U] {b n : ℕ} (decode : Bits b → U)
    (i : Fin n) (a : U) : formulaCost (sfLetterAtom decode n i a) ≤ 2 ^ b * (3 * b + 2) + 1 := by
  rw [sfLetterAtom, relabelFormula_cost]
  exact truthTableFormula_cost _

/-- Explicit AC0 circuits with common resource bounds for every fixed star-free expression and
fixed-length binary letter decoder. No algebraic recognition hypothesis is
used or assumed in this compilation theorem. -/
theorem starFree_block_circuits {U : Type} [DecidableEq U] {b : ℕ}
    (decode : Bits b → U) (e : StarFreeExpr U) :
    ∃ D C k : ℕ, ∀ n : ℕ, ∃ S : Circuit Unit, ∃ hbits : S.randomBits = n * b,
      S.depth ≤ D ∧ S.size ≤ C * (n + 1) ^ k ∧
      ∀ seed : Bits (n * b), S.eval (fun i => seed (Fin.cast hbits i)) () = true ↔
        sfDenote e (List.ofFn (decodedLetterWord decode seed)) := by
  let A := 2 ^ b * (3 * b + 2) + 1
  let K := sfCoefficient e A
  let p := sfExponent e
  refine ⟨sfDepthBound e 3, b + K + 1, max 1 p, fun n => ?_⟩
  let f := sfFormula e n (sfLetterAtom decode n)
  obtain ⟨S, hbits, he, hd, hs⟩ := formula_circuit f
  refine ⟨S, hbits, hd.trans (sfFormula_depth_bound e n _ 3 (sfLetterAtom_depth decode)), ?_, ?_⟩
  · have hc : formulaCost f ≤ K * (n + 1) ^ p :=
      sfFormula_cost_bound e n _ A (sfLetterAtom_cost decode)
    have hpow : n + 1 ≤ (n + 1) ^ max 1 p := by
      simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ n + 1) (Nat.le_max_left 1 p)
    have hcoef := hc.trans (monomial_bound_mono K n n p (max 1 p) le_rfl (Nat.le_max_right 1 p))
    have hin : n * b ≤ b * (n + 1) ^ max 1 p := by nlinarith
    rw [hs]
    nlinarith
  · intro seed
    rw [he]
    exact sfFormula_correct e n _ _ seed (sfLetterAtom_correct decode seed)

/-- All prefix-membership bits are produced in parallel at the same depth.
The additional polynomial degree accounts explicitly for the n+1 prefixes. -/
theorem starFree_prefix_circuits {U : Type} [DecidableEq U] {b : ℕ}
    (decode : Bits b → U) (e : StarFreeExpr U) :
    ∃ D C k : ℕ, ∀ n : ℕ, ∃ S : Circuit (Fin (n + 1)), ∃ hbits : S.randomBits = n * b,
      S.depth ≤ D ∧ S.size ≤ C * (n + 1) ^ k ∧
      ∀ seed : Bits (n * b), ∀ t : Fin (n + 1),
        S.eval (fun i => seed (Fin.cast hbits i)) t = true ↔
          sfDenote e (List.ofFn (fun j => decodedLetterWord decode seed (wordCutLeft t j))) := by
  let A := 2 ^ b * (3 * b + 2) + 1
  let K := sfCoefficient e A
  let p := sfExponent e
  refine ⟨sfDepthBound e 3, b + K + 1, p + 1, fun n => ?_⟩
  let fs : Fin (n + 1) → CircuitFormula (n * b) := fun t =>
    sfFormula e t.val (fun j => sfLetterAtom decode n (wordCutLeft t j))
  have hd : ∀ t, formulaDepth (fs t) ≤ sfDepthBound e 3 := fun t =>
    sfFormula_depth_bound e t.val _ 3 (fun j a => sfLetterAtom_depth decode (wordCutLeft t j) a)
  obtain ⟨S, hbits, he, hdep, hs⟩ := formula_family_circuit fs (sfDepthBound e 3) hd
  refine ⟨S, hbits, hdep, ?_, ?_⟩
  · have hc : ∀ t, formulaCost (fs t) ≤ K * (n + 1) ^ p := fun t =>
      (sfFormula_cost_bound e t.val _ A (fun j a => sfLetterAtom_cost decode (wordCutLeft t j) a)).trans
        (monomial_bound_mono K t.val n p p (by omega) le_rfl)
    have hsum : (∑ t, formulaCost (fs t)) ≤ (n + 1) * (K * (n + 1) ^ p) := by
      simpa using Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => hc t)
    have hpow : n + 1 ≤ (n + 1) ^ (p + 1) := by
      simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ n + 1)
        (show 1 ≤ p + 1 by omega)
    have hin : n * b ≤ b * (n + 1) ^ (p + 1) := by nlinarith
    have hsum' : (∑ t, formulaCost (fs t)) ≤ K * (n + 1) ^ (p + 1) := by
      simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hsum
    rw [hs]
    nlinarith
  · intro seed t
    rw [he]
    exact sfFormula_correct e t.val _ _ seed
      (fun j a => sfLetterAtom_correct decode seed (wordCutLeft t j) a)

end FSS23105365

-- From Solutions.FSS23105365_StarFreeFamilies
set_option autoImplicit false
namespace FSS23105365

/-- A fixed finite family of star-free tests has common depth and
polynomial bounds, simultaneously for every prefix length. -/
theorem starFree_family_prefix_formulas {U I : Type} [DecidableEq U] [Fintype I]
    {b : ℕ} (decode : Bits b → U) (e : I → StarFreeExpr U) :
    ∃ D C k : ℕ, ∃ fs : (n : ℕ) → I → Fin (n + 1) → CircuitFormula (n * b),
      (∀ n i t, formulaDepth (fs n i t) ≤ D) ∧
      (∀ n i t, formulaCost (fs n i t) ≤ C * (n + 1) ^ k) ∧
      (∀ n i t (seed : Bits (n * b)), formulaEval (fs n i t) seed = true ↔
        sfDenote (e i) (List.ofFn (fun j => decodedLetterWord decode seed (wordCutLeft t j)))) := by
  let A := 2 ^ b * (3 * b + 2) + 1
  let D := Finset.univ.sup (fun i => sfDepthBound (e i) 3)
  let C := Finset.univ.sup (fun i => sfCoefficient (e i) A)
  let k := Finset.univ.sup (fun i => sfExponent (e i))
  let fs := fun n i (t : Fin (n + 1)) => sfFormula (e i) t.val
    (fun j => sfLetterAtom decode n (wordCutLeft t j))
  refine ⟨D, C, k, fs, ?_, ?_, ?_⟩
  · intro n i t
    exact (sfFormula_depth_bound (e i) t.val _ 3
      (fun j a => sfLetterAtom_depth decode (wordCutLeft t j) a)).trans
      (Finset.le_sup (f := fun i => sfDepthBound (e i) 3) (Finset.mem_univ i))
  · intro n i t
    have hcost := sfFormula_cost_bound (e i) t.val _ A
      (fun j a => sfLetterAtom_cost decode (wordCutLeft t j) a)
    have hk : sfExponent (e i) ≤ k :=
      Finset.le_sup (f := fun i => sfExponent (e i)) (Finset.mem_univ i)
    have hC : sfCoefficient (e i) A ≤ C :=
      Finset.le_sup (f := fun i => sfCoefficient (e i) A) (Finset.mem_univ i)
    exact (hcost.trans (monomial_bound_mono _ t.val n _ k (by omega) hk)).trans
      (Nat.mul_le_mul_right _ hC)
  · intro n i t seed
    exact sfFormula_correct (e i) t.val _ _ seed
      (fun j a => sfLetterAtom_correct decode seed (wordCutLeft t j) a)

end FSS23105365

-- From Solutions.FSS23105365_StarFreeSelection
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

def startInputBits {a r : ℕ} (seed : Bits (a + r)) : Bits a :=
  fun i => seed (Fin.castAdd r i)

def afterStartInputBits {a r : ℕ} (seed : Bits (a + r)) : Bits r :=
  fun i => seed (Fin.natAdd a i)

/-- A fixed number of start-state bits selects among a fixed finite family
of star-free tests. Every prefix and every output coordinate are computed
with the same constant depth and a common polynomial size bound. -/
theorem starFree_selected_prefix_circuits {U Out : Type} [DecidableEq U] [Fintype Out]
    {a b : ℕ} (decode : Bits b → U) (e : Bits a × Out → StarFreeExpr U) :
    ∃ D C k : ℕ, ∀ n : ℕ, ∃ S : Circuit (Fin (n + 1) × Out),
      ∃ hbits : S.randomBits = a + n * b,
      S.depth ≤ D ∧ S.size ≤ C * (n + 1) ^ k ∧
      ∀ seed : Bits (a + n * b), ∀ t : Fin (n + 1), ∀ j : Out,
        S.eval (fun i => seed (Fin.cast hbits i)) (t, j) = true ↔
          sfDenote (e (startInputBits seed, j)) (List.ofFn (fun i =>
            decodedLetterWord decode (afterStartInputBits seed) (wordCutLeft t i))) := by
  classical
  obtain ⟨D, C, k, fs, hdep, hcost, hsem⟩ := starFree_family_prefix_formulas decode e
  let A := 2 ^ a * (3 * a + 2) + 1
  let K := Fintype.card (Bits a) * (A + C + 4) + 1
  let q := Fintype.card Out
  refine ⟨max 3 D + 2, a + b + q * (K + 1), k + 1, fun n => ?_⟩
  let child := fun (o : Fin (n + 1) × Out) (z : Bits a) =>
    formulaAnd
      (relabelFormula (Fin.castAdd (n * b)) (truthTableFormula (fun x => decide (x = z))))
      (relabelFormula (Fin.natAdd a) (fs n (z, o.2) o.1))
  let ff := fun o => formulaIndexedAny (child o)
  have hdchild : ∀ o z, formulaDepth (child o z) ≤ max 3 D + 1 := by
    intro o z
    dsimp only [child]
    rw [formulaAnd_depth, relabelFormula_depth, relabelFormula_depth]
    exact Nat.add_le_add_right (max_le_max (truthTableFormula_depth _) (hdep n _ _)) 1
  have hcchild : ∀ o z, formulaCost (child o z) ≤ (A + C + 3) * (n + 1) ^ k := by
    intro o z
    dsimp only [child]
    rw [formulaAnd_cost, relabelFormula_cost, relabelFormula_cost]
    have h₁ := truthTableFormula_cost (fun x : Bits a => decide (x = z))
    have h₂ := hcost n (z, o.2) o.1
    have hp := Nat.one_le_pow' k n
    dsimp only [A]
    nlinarith
  have hd : ∀ o, formulaDepth (ff o) ≤ max 3 D + 2 := by
    intro o
    exact formulaIndexedAny_depth (child o) (max 3 D + 1) (hdchild o)
  have hc : ∀ o, formulaCost (ff o) ≤ K * (n + 1) ^ k := by
    intro o
    have hh := formulaIndexedAny_cost (child o) ((A + C + 3) * (n + 1) ^ k) (hcchild o)
    have hp := Nat.one_le_pow' k n
    dsimp only [ff, K]
    nlinarith
  obtain ⟨S, hbits, he, hD, hS⟩ := formula_fintype_family_circuit ff (max 3 D + 2) hd
  refine ⟨S, hbits, hD, ?_, ?_⟩
  · have hsum : (∑ o, formulaCost (ff o)) ≤ ((n + 1) * q) * (K * (n + 1) ^ k) := by
      simpa [q, Fintype.card_prod] using Finset.sum_le_sum
        (fun o (_ : o ∈ Finset.univ) => hc o)
    have hsum' : (∑ o, formulaCost (ff o)) ≤ q * K * (n + 1) ^ (k + 1) := by
      simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hsum
    have hp : n + 1 ≤ (n + 1) ^ (k + 1) := by
      simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ n + 1)
        (show 1 ≤ k + 1 by omega)
    rw [hS, Fintype.card_prod, Fintype.card_fin]
    change a + n * b + (∑ o, formulaCost (ff o)) + (n + 1) * q ≤ _
    nlinarith
  · intro seed t j
    rw [he]
    change formulaEval (formulaIndexedAny (child (t, j))) seed = true ↔ _
    rw [formulaIndexedAny_eval]
    simp only [child, formulaAnd_eval, Bool.and_eq_true, relabelFormula_eval,
      truthTableFormula_eval, decide_eq_true_eq, hsem]
    change (∃ z : Bits a, startInputBits seed = z ∧
      sfDenote (e (z, j)) (List.ofFn (fun i =>
        decodedLetterWord decode (afterStartInputBits seed) (wordCutLeft t i)))) ↔ _
    simp

end FSS23105365

-- From Solutions.FSS23105365_AperiodicEvaluation
set_option autoImplicit false
namespace FSS23105365

theorem aperiodic_observation_language_starFree {H U : Type} [Fintype H] [Fintype U]
    (τ : H → U → H) (hτ : AperiodicTransitions τ) (s : H) (observe : H → Bool) :
    IsStarFree (fun w : List U => observe (w.foldl τ s) = true) := by
  classical
  have hf : ∀ t : H, IsStarFree (fun w : List U => w.foldl τ s = t ∧ observe t = true) := by
    intro t
    by_cases ht : observe t = true
    · exact isStarFree_congr (aperiodic_run_language_starFree τ hτ s t)
        (fun w => by simp [ht])
    · exact isStarFree_congr isStarFree_empty (fun w => by simp [ht])
  apply isStarFree_congr (isStarFree_finite_union _ hf)
  intro w
  simp

theorem wordCutLeft_list_take {U : Type} {n : ℕ} (w : Fin n → U) (t : Fin (n + 1)) :
    List.ofFn (fun i => w (wordCutLeft t i)) = (List.ofFn w).take t.val := by
  have h := congrArg (List.take t.val) (word_cut_list w t)
  have ht : (List.ofFn (fun i => w (wordCutLeft t i))).take t.val =
      List.ofFn (fun i => w (wordCutLeft t i)) := List.take_of_length_le (by simp)
  simpa only [List.take_append, List.length_ofFn, Nat.sub_self, List.take_zero,
    List.append_nil, ht] using h

/-- Lemma 3.4, strengthened to all prefixes. Start-state and alphabet
decoders and output encodings are arbitrary fixed finite Boolean maps.
The circuits have exactly a+n*b input wires, uniformly bounded depth and
polynomial gate-and-wire size, and return the actual encoded reached state. -/
theorem aperiodic_prefix_evaluation_circuits {H U Out : Type} [Fintype H] [Fintype U]
    [Fintype Out] {a b : ℕ} (τ : H → U → H) (hτ : AperiodicTransitions τ)
    (start : Bits a → H) (letter : Bits b → U) (observe : H → Out → Bool) :
    ∃ D C k : ℕ, ∀ n : ℕ, ∃ S : Circuit (Fin (n + 1) × Out),
      ∃ hbits : S.randomBits = a + n * b,
      S.depth ≤ D ∧ S.size ≤ C * (n + 1) ^ k ∧
      ∀ seed : Bits (a + n * b), ∀ t : Fin (n + 1), ∀ j : Out,
        S.eval (fun i => seed (Fin.cast hbits i)) (t, j) =
          observe (((List.ofFn (decodedLetterWord letter (afterStartInputBits seed))).take
            t.val).foldl τ (start (startInputBits seed))) j := by
  classical
  have hex : ∀ z : Bits a × Out, ∃ e : StarFreeExpr U, ∀ w,
      sfDenote e w ↔ observe (w.foldl τ (start z.1)) z.2 = true :=
    fun z => aperiodic_observation_language_starFree τ hτ (start z.1) (fun h => observe h z.2)
  choose e he using hex
  obtain ⟨D, C, k, h⟩ := starFree_selected_prefix_circuits letter e
  refine ⟨D, C, k, fun n => ?_⟩
  obtain ⟨S, hbits, hd, hs, hval⟩ := h n
  refine ⟨S, hbits, hd, hs, fun seed t j => ?_⟩
  apply Bool.eq_iff_iff.mpr
  exact (hval seed t j).trans (by rw [he, wordCutLeft_list_take])

def encodeAutomatonInput {H U : Type} {a b n : ℕ} (encStart : H → Bits a)
    (encLetter : U → Bits b) (s : H) (w : Fin n → U) : Bits (a + n * b) :=
  Fin.append (encStart s) (fun i =>
    encLetter (w (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2)

theorem encodeAutomatonInput_start {H U : Type} {a b n : ℕ} (encStart : H → Bits a)
    (encLetter : U → Bits b) (s : H) (w : Fin n → U) :
    startInputBits (encodeAutomatonInput encStart encLetter s w) = encStart s := by
  funext i
  simp [startInputBits, encodeAutomatonInput]

theorem encodeAutomatonInput_word {H U : Type} {a b n : ℕ} (encStart : H → Bits a)
    (encLetter : U → Bits b) (letter : Bits b → U) (hletter : Function.LeftInverse letter encLetter)
    (s : H) (w : Fin n → U) :
    decodedLetterWord letter (afterStartInputBits (encodeAutomatonInput encStart encLetter s w)) =
      w := by
  funext i
  change letter (fun j => Fin.append (encStart s)
    (fun k => encLetter (w (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2)
    (Fin.natAdd a (finProdFinEquiv (i, j)))) = w i
  simp only [Fin.append_right, Equiv.symm_apply_apply]
  exact hletter (w i)

/-- The same family computes the complete run on every represented start
state and every represented word. Representation validity is expressed by
left inverses; there is no assumption about an input distribution. -/
theorem aperiodic_prefix_evaluation_encoded {H U Out : Type} [Fintype H] [Fintype U]
    [Fintype Out] {a b : ℕ} (τ : H → U → H) (hτ : AperiodicTransitions τ)
    (start : Bits a → H) (letter : Bits b → U) (observe : H → Out → Bool)
    (encStart : H → Bits a) (encLetter : U → Bits b)
    (hstart : Function.LeftInverse start encStart) (hletter : Function.LeftInverse letter encLetter) :
    ∃ D C k : ℕ, ∀ n : ℕ, ∃ S : Circuit (Fin (n + 1) × Out),
      ∃ hbits : S.randomBits = a + n * b,
      S.depth ≤ D ∧ S.size ≤ C * (n + 1) ^ k ∧
      ∀ s : H, ∀ w : Fin n → U, ∀ t : Fin (n + 1), ∀ j : Out,
        S.eval (fun i => encodeAutomatonInput encStart encLetter s w (Fin.cast hbits i)) (t, j) =
          observe (((List.ofFn w).take t.val).foldl τ s) j := by
  obtain ⟨D, C, k, h⟩ := aperiodic_prefix_evaluation_circuits τ hτ start letter observe
  refine ⟨D, C, k, fun n => ?_⟩
  obtain ⟨S, hbits, hd, hs, he⟩ := h n
  refine ⟨S, hbits, hd, hs, fun s w t j => ?_⟩
  rw [he, encodeAutomatonInput_start, encodeAutomatonInput_word _ _ _ hletter, hstart]

end FSS23105365

-- From Solutions.FSS23105365_FiniteStateEncoding
set_option autoImplicit false
namespace FSS23105365

def finiteOneHot {H : Type} [Fintype H] (h : H) : Bits (Fintype.card H) := by
  classical
  exact fun i => decide (h = (Fintype.equivFin H).symm i)

theorem finiteOneHot_injective {H : Type} [Fintype H] :
    Function.Injective (finiteOneHot (H := H)) := by
  classical
  intro h k he
  have hv := congrFun he ((Fintype.equivFin H) h)
  simpa [finiteOneHot, eq_comm] using hv

def finiteOneHotDecode {H : Type} [Fintype H] [Nonempty H] : Bits (Fintype.card H) → H :=
  Function.invFun finiteOneHot

theorem finiteOneHotDecode_leftInverse {H : Type} [Fintype H] [Nonempty H] :
    Function.LeftInverse (finiteOneHotDecode (H := H)) finiteOneHot :=
  Function.leftInverse_invFun finiteOneHot_injective

/-- A concrete injective encoding version of Lemma 3.4 for nonempty finite
state sets and alphabets. All start states and all words share the same
circuit for a fixed length; the output includes the empty prefix. -/
theorem aperiodic_evaluation_oneHot_nonempty {H U : Type} [Fintype H] [Fintype U]
    [Nonempty H] [Nonempty U] (τ : H → U → H) (hτ : AperiodicTransitions τ) :
    ∃ D C k : ℕ, ∀ n : ℕ, ∃ S : Circuit (Fin (n + 1) × Fin (Fintype.card H)),
      ∃ hbits : S.randomBits = Fintype.card H + n * Fintype.card U,
      S.depth ≤ D ∧ S.size ≤ C * (n + 1) ^ k ∧
      ∀ s : H, ∀ w : Fin n → U, ∀ t : Fin (n + 1), ∀ j : Fin (Fintype.card H),
        S.eval (fun i => encodeAutomatonInput finiteOneHot finiteOneHot s w (Fin.cast hbits i))
          (t, j) = finiteOneHot (((List.ofFn w).take t.val).foldl τ s) j :=
  aperiodic_prefix_evaluation_encoded τ hτ finiteOneHotDecode finiteOneHotDecode finiteOneHot
    finiteOneHot finiteOneHot finiteOneHotDecode_leftInverse finiteOneHotDecode_leftInverse

/-- Empty state sets or alphabets are handled directly by an input-wire
circuit; the general finite theorem therefore adds no nonemptiness assumption. -/
theorem aperiodic_evaluation_oneHot_empty {H U : Type} [Fintype H] [Fintype U]
    (hempty : IsEmpty H ∨ IsEmpty U) (τ : H → U → H) :
    ∃ D C k : ℕ, ∀ n : ℕ, ∃ S : Circuit (Fin (n + 1) × Fin (Fintype.card H)),
      ∃ hbits : S.randomBits = Fintype.card H + n * Fintype.card U,
      S.depth ≤ D ∧ S.size ≤ C * (n + 1) ^ k ∧
      ∀ s : H, ∀ w : Fin n → U, ∀ t : Fin (n + 1), ∀ j : Fin (Fintype.card H),
        S.eval (fun i => encodeAutomatonInput finiteOneHot finiteOneHot s w (Fin.cast hbits i))
          (t, j) = finiteOneHot (((List.ofFn w).take t.val).foldl τ s) j := by
  let h := Fintype.card H
  let u := Fintype.card U
  refine ⟨0, 2 * h + u, 1, fun n => ?_⟩
  let P := emptyCircuitProgram (h + n * u)
  let out : Fin (n + 1) × Fin h → Fin (h + n * u + P.gates.length) :=
    fun o => Fin.castAdd 0 (Fin.castAdd (n * u) o.2)
  refine ⟨programCircuit P out, rfl,
    programCircuit_depth_le P out 0 (fun _ => le_refl _), ?_, ?_⟩
  · rw [programCircuit_size]
    change h + n * u + 0 + 0 + Fintype.card (Fin (n + 1) × Fin h) ≤ _
    simp only [Fintype.card_prod, Fintype.card_fin, pow_one]
    nlinarith
  · intro s w t j
    rcases hempty with hH | hU
    · exact (hH.false s).elim
    · have hn : n = 0 := by
        by_contra hn
        exact hU.false (w ⟨0, Nat.pos_of_ne_zero hn⟩)
      have ht : t.val = 0 := by have := t.isLt; omega
      change (programCircuit P out).eval (encodeAutomatonInput finiteOneHot finiteOneHot s w)
        (t, j) = _
      rw [programCircuit_eval]
      change P.value (encodeAutomatonInput finiteOneHot finiteOneHot s w)
        (Fin.castAdd (n * u) j).val = _
      rw [P.input_value]
      simp [encodeAutomatonInput, ht]

/-- Full finite-alphabet Lemma 3.4, with explicit injective one-hot input
and output encodings and all prefixes in parallel, including degenerate
empty sets and the empty input word. -/
theorem aperiodic_evaluation_oneHot {H U : Type} [Fintype H] [Fintype U]
    (τ : H → U → H) (hτ : AperiodicTransitions τ) :
    ∃ D C k : ℕ, ∀ n : ℕ, ∃ S : Circuit (Fin (n + 1) × Fin (Fintype.card H)),
      ∃ hbits : S.randomBits = Fintype.card H + n * Fintype.card U,
      S.depth ≤ D ∧ S.size ≤ C * (n + 1) ^ k ∧
      ∀ s : H, ∀ w : Fin n → U, ∀ t : Fin (n + 1), ∀ j : Fin (Fintype.card H),
        S.eval (fun i => encodeAutomatonInput finiteOneHot finiteOneHot s w (Fin.cast hbits i))
          (t, j) = finiteOneHot (((List.ofFn w).take t.val).foldl τ s) j := by
  classical
  cases isEmpty_or_nonempty H with
  | inl hH => exact aperiodic_evaluation_oneHot_empty (Or.inl hH) τ
  | inr hH =>
    letI := hH
    cases isEmpty_or_nonempty U with
    | inl hU => exact aperiodic_evaluation_oneHot_empty (Or.inr hU) τ
    | inr hU =>
      letI := hU
      exact aperiodic_evaluation_oneHot_nonempty τ hτ

end FSS23105365

-- From Solutions.FSS23105365_StateLookupFormulas
set_option autoImplicit false
namespace FSS23105365

/-- Decode the computed one-hot state and combine it with a bounded
number of original input bits using a fixed finite truth table. -/
def stateLookupFormula {H : Type} [Fintype H] [Nonempty H] {r ℓ : ℕ}
    (state : Fin (Fintype.card H) → CircuitFormula r) (input : Fin ℓ → Fin r)
    (f : H → Bits ℓ → Bool) : CircuitFormula r :=
  substituteFormula (Fin.append state (fun i => .input (input i)))
    (truthTableFormula (fun z : Bits (Fintype.card H + ℓ) =>
      f (finiteOneHotDecode (fun i => z (Fin.castAdd ℓ i)))
        (fun i => z (Fin.natAdd (Fintype.card H) i))))

theorem stateLookupFormula_eval {H : Type} [Fintype H] [Nonempty H] {r ℓ : ℕ}
    (state : Fin (Fintype.card H) → CircuitFormula r) (input : Fin ℓ → Fin r)
    (f : H → Bits ℓ → Bool) (seed : Bits r) (h : H)
    (hstate : ∀ j, formulaEval (state j) seed = finiteOneHot h j) :
    formulaEval (stateLookupFormula state input f) seed = f h (fun i => seed (input i)) := by
  rw [stateLookupFormula, substituteFormula_eval, truthTableFormula_eval]
  simp only [Fin.append_left, Fin.append_right, formulaEval, hstate]
  rw [finiteOneHotDecode_leftInverse]

theorem stateLookupFormula_depth {H : Type} [Fintype H] [Nonempty H] {r ℓ : ℕ}
    (state : Fin (Fintype.card H) → CircuitFormula r) (input : Fin ℓ → Fin r)
    (f : H → Bits ℓ → Bool) (D : ℕ) (hD : ∀ j, formulaDepth (state j) ≤ D) :
    formulaDepth (stateLookupFormula state input f) ≤ D + 3 := by
  apply (substituteFormula_depth _ D ?_ _).trans
    (Nat.add_le_add_left (truthTableFormula_depth _) D)
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [Fin.append_left] using hD j
  · simp only [Fin.append_right, formulaDepth, Nat.zero_le]

theorem stateLookupFormula_cost {H : Type} [Fintype H] [Nonempty H] {r ℓ b : ℕ}
    (state : Fin (Fintype.card H) → CircuitFormula r) (input : Fin ℓ → Fin r)
    (f : H → Bits ℓ → Bool) (K : ℕ) (hK : ∀ j, formulaCost (state j) ≤ K) (hℓ : ℓ ≤ b) :
    formulaCost (stateLookupFormula state input f) ≤
      (2 ^ (Fintype.card H + b) * (3 * (Fintype.card H + b) + 2) + 1) * (K + 1) + K := by
  have hc := substituteFormula_cost
    (Fin.append state (fun i => CircuitFormula.input (input i))) K (by
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simpa only [Fin.append_left] using hK j
      · simp only [Fin.append_right, formulaCost, Nat.zero_le])
    (truthTableFormula (fun z : Bits (Fintype.card H + ℓ) =>
      f (finiteOneHotDecode (fun i => z (Fin.castAdd ℓ i)))
        (fun i => z (Fin.natAdd (Fintype.card H) i))))
  exact hc.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (K + 1)
    (truthTableFormula_cost_mono (Nat.add_le_add_left hℓ (Fintype.card H)) _)) K)

end FSS23105365

-- From Solutions.FSS23105365_DyadicFacts
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

theorem dyadic_zero : Dyadic 0 := by
  exact ⟨0, 0, by simp⟩

theorem dyadic_one : Dyadic 1 := by
  exact ⟨1, 0, by simp⟩

theorem dyadic_mul {x y : ℝ} (hx : Dyadic x) (hy : Dyadic y) :
    Dyadic (x * y) := by
  rcases hx with ⟨a, k, rfl⟩
  rcases hy with ⟨b, l, rfl⟩
  exact ⟨a * b, k + l, by simp [Nat.cast_mul, pow_add, div_mul_div_comm]⟩

theorem dyadic_add {x y : ℝ} (hx : Dyadic x) (hy : Dyadic y) :
    Dyadic (x + y) := by
  rcases hx with ⟨a, k, rfl⟩
  rcases hy with ⟨b, l, rfl⟩
  refine ⟨a * 2 ^ l + b * 2 ^ k, k + l, ?_⟩
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_pow, Nat.cast_ofNat, pow_add]
  simpa only [mul_comm] using
    div_add_div (a : ℝ) (b : ℝ)
      (pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0))
      (pow_ne_zero l (by norm_num : (2 : ℝ) ≠ 0))

theorem dyadic_finset_prod {α : Type} (s : Finset α) (f : α → ℝ)
    (h : ∀ x ∈ s, Dyadic (f x)) : Dyadic (∏ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using dyadic_one
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact dyadic_mul (h a (Finset.mem_insert_self a s))
      (ih (fun x hx => h x (Finset.mem_insert_of_mem hx)))

theorem dyadic_finset_sum {α : Type} (s : Finset α) (f : α → ℝ)
    (h : ∀ x ∈ s, Dyadic (f x)) : Dyadic (∑ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using dyadic_zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact dyadic_add (h a (Finset.mem_insert_self a s))
      (ih (fun x hx => h x (Finset.mem_insert_of_mem hx)))

/-- The elementary dyadic closure used by the finite-chain constructions. -/
theorem transitionDyadic_pathDyadic {q : ℕ} (M : MarkovChain q)
    (h : TransitionDyadic M) : PathDyadic M := by
  intro n γ
  apply dyadic_mul (h.1 _)
  exact dyadic_finset_prod Finset.univ _ (fun i _ => h.2 _ _)

/-- Coordinatewise projection preserves path-dyadicity, even without injectivity. -/
theorem projectedPathLaw_dyadic {q r : ℕ} (M : MarkovChain r)
    (h : PathDyadic M) (φ : Fin r → Fin q) (n : ℕ) (γ : Path q n) :
    Dyadic (projectedPathLaw M φ γ) := by
  classical
  apply dyadic_finset_sum Finset.univ
  intro η _
  split_ifs
  · exact h n η
  · exact dyadic_zero

end FSS23105365

-- From Solutions.FSS23105365_DyadicRealization
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

/-- A finite family of nonnegative dyadic numbers has a common power-of-two
denominator. The exponent can be chosen positive, as required in Lemma E.3. -/
theorem dyadic_common_denominator {α : Type} [Fintype α] (p : α → ℝ)
    (hp : ∀ x, Dyadic (p x)) :
    ∃ k : ℕ, 0 < k ∧ ∃ a : α → ℕ, ∀ x, p x = (a x : ℝ) / 2 ^ k := by
  classical
  choose a e he using hp
  let k := (∑ x, e x) + 1
  have hek (x : α) : e x ≤ k := by
    exact le_trans (Finset.single_le_sum (fun y _ => Nat.zero_le (e y))
      (Finset.mem_univ x)) (Nat.le_succ _)
  refine ⟨k, Nat.zero_lt_succ _, fun x => a x * 2 ^ (k - e x), ?_⟩
  intro x
  rw [he x, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hpow : (2 : ℝ) ^ k = 2 ^ (e x) * 2 ^ (k - e x) := by
    rw [← pow_add, Nat.add_sub_of_le (hek x)]
  rw [hpow]
  exact (mul_div_mul_right _ _ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))).symm

/-- Allocate a finite uniform source to prescribed integer multiplicities. -/
theorem exists_map_with_fiber_counts {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    (a : α → ℕ) (ha : ∑ x, a x = Fintype.card β) :
    ∃ f : β → α, ∀ x, Fintype.card {u : β // f u = x} = a x := by
  classical
  let e : β ≃ (Σ x, Fin (a x)) := Fintype.equivOfCardEq (by simp [ha])
  refine ⟨fun u => (e u).1, fun x => ?_⟩
  let ef : {u : β // (e u).1 = x} ≃ {u : (Σ y, Fin (a y)) // u.1 = x} :=
    e.subtypeEquiv (fun _ => Iff.rfl)
  let ep : {u : (Σ y, Fin (a y)) // u.1 = x} ≃ Fin (a x) :=
    Equiv.sigmaSubtype x
  simpa using Fintype.card_congr (ef.trans ep)

/-- A normalized distribution with the specified dyadic denominator can use
exactly that many fair bits, so all Markov rows can share a block length. -/
theorem distribution_realization_of_counts {α : Type} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (k : ℕ) (a : α → ℕ)
    (ha : ∀ x, p x = (a x : ℝ) / 2 ^ k) (hsum : ∑ x, p x = 1) :
    ∃ f : Bits k → α,
      ∀ x, (Fintype.card {u : Bits k // f u = x} : ℝ) / 2 ^ k = p x := by
  classical
  have hcounts : ∑ x, a x = 2 ^ k := by
    have h : (∑ x, (a x : ℝ)) / 2 ^ k = 1 := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
      simpa only [div_eq_mul_inv, ← Finset.sum_mul] using
        (show (∑ x, (a x : ℝ) / 2 ^ k) = 1 by simpa only [← ha] using hsum)
    have h' : (∑ x, (a x : ℝ)) = (2 : ℝ) ^ k :=
      (div_eq_one_iff_eq (pow_ne_zero _ (by norm_num))).mp h
    exact_mod_cast h'
  obtain ⟨f, hf⟩ := exists_map_with_fiber_counts (β := Bits k) a (by
    simpa only [Bits, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using hcounts)
  exact ⟨f, fun x => by rw [hf, ha]⟩

/-- The normalized dyadic case of the finite sampling construction used in
Lemma E.3: a fixed finite fair-bit seed realizes the distribution exactly. -/
theorem dyadic_distribution_realization {α : Type} [Fintype α] [DecidableEq α] (p : α → ℝ)
    (hp : ∀ x, Dyadic (p x)) (hsum : ∑ x, p x = 1) :
    ∃ k : ℕ, 0 < k ∧ ∃ f : Bits k → α,
      ∀ x, (Fintype.card {u : Bits k // f u = x} : ℝ) / 2 ^ k = p x := by
  obtain ⟨k, hk, a, ha⟩ := dyadic_common_denominator p hp
  exact ⟨k, hk, distribution_realization_of_counts p k a ha hsum⟩

/-- Initial and transition maps in the first paragraph of Lemma E.3. All
transition rows use the same positive block length; no probability oracle
is assumed. -/
theorem transitionDyadic_block_maps {q : ℕ} (M : MarkovChain q)
    (hM : TransitionDyadic M) :
    ∃ v s : ℕ, 0 < v ∧ 0 < s ∧
      ∃ g : Bits v → Fin q, ∃ δ : Fin q → Bits s → Fin q,
        (∀ x, (Fintype.card {e : Bits v // g e = x} : ℝ) / 2 ^ v = M.initial x) ∧
        (∀ x y, (Fintype.card {u : Bits s // δ x u = y} : ℝ) / 2 ^ s =
          M.transition x y) := by
  obtain ⟨v, hv, g, hg⟩ := dyadic_distribution_realization M.initial hM.1 M.initial_sum
  obtain ⟨s, hs, a, ha⟩ := dyadic_common_denominator
    (fun xy : Fin q × Fin q => M.transition xy.1 xy.2) (fun xy => hM.2 xy.1 xy.2)
  have hrows (x : Fin q) := distribution_realization_of_counts
    (M.transition x) s (fun y => a (x, y)) (fun y => ha (x, y)) (M.row_sum x)
  choose δ hδ using hrows
  exact ⟨v, s, hv, hs, g, δ, hg, hδ⟩

end FSS23105365

-- From Solutions.FSS23105365_BlockMarkov
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

/-- The full state sequence driven by a sequence of independent input blocks. -/
def drivenPath {Q U : Type} (δ : Q → U → Q) :
    (n : ℕ) → Q → (Fin n → U) → Fin (n + 1) → Q
  | 0, x, _ => fun _ => x
  | n + 1, x, u => Fin.cons x (drivenPath δ n (δ x (u 0)) (fun i => u i.succ))

@[simp] theorem drivenPath_zero {Q U : Type} (δ : Q → U → Q)
    (n : ℕ) (x : Q) (u : Fin n → U) : drivenPath δ n x u 0 = x := by
  cases n <;> rfl

@[simp] theorem drivenPath_step {Q U : Type} (δ : Q → U → Q)
    (n : ℕ) (x : Q) (u : Fin n → U) (i : Fin n) :
    drivenPath δ n x u i.succ = δ (drivenPath δ n x u i.castSucc) (u i) := by
  induction n generalizing x with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [drivenPath]
    · simpa [drivenPath] using ih (δ x (u 0)) (fun j => u j.succ) j

/-- Matching an entire run is equivalent to matching its initial state and
each individual transition. This identifies its fair-bit fiber exactly. -/
theorem drivenPath_eq_iff {Q U : Type} (δ : Q → U → Q)
    (n : ℕ) (x : Q) (u : Fin n → U) (γ : Fin (n + 1) → Q) :
    drivenPath δ n x u = γ ↔ x = γ 0 ∧
      ∀ i : Fin n, δ (γ i.castSucc) (u i) = γ i.succ := by
  constructor
  · intro h
    constructor
    · simpa using (congrFun h 0)
    · intro i
      simpa only [h] using (drivenPath_step δ n x u i).symm
  · rintro ⟨h0, hs⟩
    funext i
    induction i using Fin.induction with
    | zero => simpa using h0
    | succ i ih => rw [drivenPath_step, ih, hs]

/-- Independent block sources form a Cartesian product of fibers once the
target trajectory is fixed. -/
def drivenPathFiberEquiv {Q E U : Type} (g : E → Q) (δ : Q → U → Q)
    (n : ℕ) (γ : Fin (n + 1) → Q) :
    {z : E × (Fin n → U) // drivenPath δ n (g z.1) z.2 = γ} ≃
      ({e : E // g e = γ 0} ×
        ((i : Fin n) → {u : U // δ (γ i.castSucc) u = γ i.succ})) where
  toFun z :=
    let h := (drivenPath_eq_iff δ n (g z.1.1) z.1.2 γ).mp z.2
    (⟨z.1.1, h.1⟩, fun i => ⟨z.1.2 i, h.2 i⟩)
  invFun z := ⟨(z.1.1, fun i => (z.2 i).1),
    (drivenPath_eq_iff δ n (g z.1.1) (fun i => (z.2 i).1) γ).mpr
      ⟨z.1.2, fun i => (z.2 i).2⟩⟩
  left_inv z := by rfl
  right_inv z := by rfl

theorem drivenPath_fiber_card {Q E U : Type} [Fintype E] [Fintype U] [DecidableEq Q]
    (g : E → Q) (δ : Q → U → Q) (n : ℕ) (γ : Fin (n + 1) → Q) :
    Fintype.card {z : E × (Fin n → U) // drivenPath δ n (g z.1) z.2 = γ} =
      Fintype.card {e : E // g e = γ 0} *
        ∏ i : Fin n, Fintype.card {u : U // δ (γ i.castSucc) u = γ i.succ} := by
  simpa only [Fintype.card_prod, Fintype.card_pi] using
    Fintype.card_congr (drivenPathFiberEquiv g δ n γ)

/-- The independent block maps give exactly the full Markov path law,
including length-zero trajectories. -/
theorem drivenPath_markov_law {q v s : ℕ} (M : MarkovChain q)
    (g : Bits v → Fin q) (δ : Fin q → Bits s → Fin q)
    (hg : ∀ x, (Fintype.card {e : Bits v // g e = x} : ℝ) / 2 ^ v = M.initial x)
    (hδ : ∀ x y, (Fintype.card {u : Bits s // δ x u = y} : ℝ) / 2 ^ s =
      M.transition x y) (n : ℕ) (γ : Path q n) :
    (Fintype.card {z : Bits v × (Fin n → Bits s) //
      drivenPath δ n (g z.1) z.2 = γ} : ℝ) / 2 ^ (v + s * n) = pathLaw M γ := by
  rw [drivenPath_fiber_card, Nat.cast_mul, Nat.cast_prod]
  have hden : (2 : ℝ) ^ (v + s * n) = 2 ^ v * (2 ^ s) ^ n := by
    rw [pow_add, pow_mul]
  rw [hden, ← div_mul_div_comm]
  have hprod :
      (∏ i : Fin n, (Fintype.card {u : Bits s // δ (γ i.castSucc) u = γ i.succ} : ℝ)) /
        (2 ^ s) ^ n =
      ∏ i : Fin n, (Fintype.card {u : Bits s // δ (γ i.castSucc) u = γ i.succ} : ℝ) /
        2 ^ s := by simp [Finset.prod_div_distrib]
  rw [hprod, hg]
  simp only [hδ, pathLaw]
  rfl

/-- Fair bits can be split into one initial block and `n` transition blocks.
The equivalence is finite and hence preserves the uniform law exactly. -/
def blockSeedEquiv (v s n : ℕ) : Bits (v + s * n) ≃ Bits v × (Fin n → Bits s) :=
  Fintype.equivOfCardEq (by
    simp only [Bits, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Fintype.card_prod, pow_add, pow_mul])

/-- The probability identity in E.3 before implementing block buffering by
a binary DFA. This also verifies the linear fair-bit count of that encoding.
It asserts no circuit-depth bound. -/
theorem transitionDyadic_linear_seed_sampler {q : ℕ} (M : MarkovChain q)
    (hM : TransitionDyadic M) :
    ∃ v s : ℕ, 0 < v ∧ 0 < s ∧ ∀ n : ℕ,
      ∃ f : Bits (v + s * n) → Path q n,
        ∀ γ, (Fintype.card {u : Bits (v + s * n) // f u = γ} : ℝ) /
          2 ^ (v + s * n) = pathLaw M γ := by
  classical
  obtain ⟨v, s, hv, hs, g, δ, hg, hδ⟩ := transitionDyadic_block_maps M hM
  refine ⟨v, s, hv, hs, fun n => ?_⟩
  let e := blockSeedEquiv v s n
  let f := fun u => drivenPath δ n (g (e u).1) (e u).2
  refine ⟨f, fun γ => ?_⟩
  have hc : Fintype.card {u : Bits (v + s * n) // f u = γ} =
      Fintype.card {z : Bits v × (Fin n → Bits s) // drivenPath δ n (g z.1) z.2 = γ} :=
    Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))
  rw [hc]
  exact drivenPath_markov_law M g δ hg hδ n γ

end FSS23105365

-- From Solutions.FSS23105365_BinaryDecoder
set_option autoImplicit false
namespace FSS23105365

/-- A binary buffer represented by its remaining finite lookup table.
`j + 1` bits are still to be read. The first component is the last completed
Markov state. This is a finite state space for each fixed `Q` and `k`. -/
abbrev DecoderState (Q : Type) (k : ℕ) := Q × ((j : Fin k) × (Bits (j.val + 1) → Q))

def decoderReset {Q : Type} {k s : ℕ} (hs : s < k)
    (δ : Q → Bits (s + 1) → Q) (x : Q) : DecoderState Q k :=
  (x, ⟨⟨s, hs⟩, δ x⟩)

def decoderStep {Q : Type} {k s : ℕ} (hs : s < k)
    (δ : Q → Bits (s + 1) → Q) (z : DecoderState Q k) (b : Bool) :
    DecoderState Q k := by
  rcases z with ⟨x, ⟨⟨j, hj⟩, f⟩⟩
  cases j with
  | zero => exact decoderReset hs δ (f (fun _ => b))
  | succ j => exact (x, ⟨⟨j, Nat.lt_of_succ_lt hj⟩, fun u => f (Fin.cons b u)⟩)

/-- Reading one complete buffered block implements its finite lookup table. -/
theorem decoderStep_block {Q : Type} {k s : ℕ} (hs : s < k)
    (δ : Q → Bits (s + 1) → Q) (j : ℕ) (hj : j < k)
    (x : Q) (f : Bits (j + 1) → Q) (u : Bits (j + 1)) :
    (List.ofFn u).foldl (decoderStep hs δ) (x, ⟨⟨j, hj⟩, f⟩) =
      decoderReset hs δ (f u) := by
  induction j generalizing x with
  | zero =>
    have hu : (fun _ : Fin 1 => u 0) = u := by
      funext i
      exact congrArg u (by apply Fin.ext; omega)
    simp [List.ofFn_succ, decoderStep, hu]
  | succ j ih =>
    rw [List.ofFn_succ, List.foldl_cons]
    change (List.ofFn (fun i => u i.succ)).foldl (decoderStep hs δ)
      (x, ⟨⟨j, Nat.lt_of_succ_lt hj⟩, fun w => f (Fin.cons (u 0) w)⟩) = _
    rw [ih]
    congr 1
    exact congrArg f (Fin.cons_self_tail u)

theorem decoderReset_block {Q : Type} {k s : ℕ} (hs : s < k)
    (δ : Q → Bits (s + 1) → Q) (x : Q) (u : Bits (s + 1)) :
    (List.ofFn u).foldl (decoderStep hs δ) (decoderReset hs δ x) =
      decoderReset hs δ (δ x u) :=
  decoderStep_block hs δ s hs x (δ x) u

theorem decoderReset_blocks {Q : Type} {k s : ℕ} (hs : s < k)
    (δ : Q → Bits (s + 1) → Q) (x : Q) (us : List (Bits (s + 1))) :
    (us.flatMap List.ofFn).foldl (decoderStep hs δ) (decoderReset hs δ x) =
      decoderReset hs δ (us.foldl δ x) := by
  induction us generalizing x with
  | nil => rfl
  | cons u us ih =>
    simp only [List.flatMap_cons, List.foldl_append, decoderReset_block, List.foldl_cons, ih]

theorem drivenPath_prefix {Q U : Type} (δ : Q → U → Q)
    (n : ℕ) (x : Q) (u : Fin n → U) (i : Fin (n + 1)) :
    ((List.ofFn u).take i.val).foldl δ x = drivenPath δ n x u i := by
  induction n generalizing x with
  | zero =>
    have hi : i = 0 := by apply Fin.ext; omega
    simp [hi]
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simpa [List.ofFn_succ, drivenPath] using ih (δ x (u 0)) (fun j => u j.succ) j

/-- Consecutive equal-length blocks have the expected prefix boundaries. -/
private theorem take_append_length_add {α : Type} (xs ys : List α) (r : ℕ) :
    (xs ++ ys).take (xs.length + r) = xs ++ ys.take r := by
  rw [List.take_append]
  simp

theorem take_flatMap_bits {s : ℕ} (us : List (Bits s)) (i : ℕ) :
    (us.flatMap List.ofFn).take (s * i) = (us.take i).flatMap List.ofFn := by
  induction us generalizing i with
  | nil => simp
  | cons u us ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.flatMap_cons, List.take_succ_cons]
      rw [Nat.mul_succ, Nat.add_comm]
      simpa only [List.length_ofFn] using
        (take_append_length_add (List.ofFn u) (us.flatMap List.ofFn) (s * i)).trans
          (congrArg (fun t => List.ofFn u ++ t) (ih i))

/-- After the initial block and `i` transition blocks, the decoder's first
component is precisely the `i`th state of the block-driven Markov path. -/
theorem decoder_timed_projection {Q : Type} {k v s : ℕ} (hv : v < k) (hs : s < k)
    (g : Bits (v + 1) → Q) (δ : Q → Bits (s + 1) → Q) (x : Q)
    (n : ℕ) (e : Bits (v + 1)) (u : Fin n → Bits (s + 1)) (i : Fin (n + 1)) :
    (((List.ofFn e ++ (List.ofFn u).flatMap List.ofFn).take
      (v + 1 + (s + 1) * i.val)).foldl (decoderStep hs δ)
        (x, ⟨⟨v, hv⟩, g⟩)).1 = drivenPath δ n (g e) u i := by
  have ht := take_append_length_add (List.ofFn e) ((List.ofFn u).flatMap List.ofFn)
    ((s + 1) * i.val)
  simp only [List.length_ofFn] at ht
  rw [ht, take_flatMap_bits, List.foldl_append, decoderStep_block,
    decoderReset_blocks, drivenPath_prefix]
  rfl

/-- The canonical splitting of a fair word into an initial block followed
by consecutive transition blocks, with no seed permutation. -/
def consecutiveBlocksEquiv (v s n : ℕ) : Bits (v + n * s) ≃
    (Bits v × (Fin n → Bits s)) where
  toFun x := (fun i => x (Fin.castAdd (n * s) i),
    fun i j => x (Fin.natAdd v (finProdFinEquiv (i, j))))
  invFun z := Fin.append z.1 (fun i => z.2 (finProdFinEquiv.symm i).1
    (finProdFinEquiv.symm i).2)
  left_inv x := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
      change x (Fin.natAdd v (finProdFinEquiv (finProdFinEquiv.symm j))) = _
      rw [Equiv.apply_symm_apply]
  right_inv z := by
    apply Prod.ext
    · funext i; simp
    · funext i j
      simp only [Fin.append_right]
      rw [Equiv.symm_apply_apply]

theorem consecutiveBlocks_list (v s n : ℕ) (z : Bits v × (Fin n → Bits s)) :
    List.ofFn ((consecutiveBlocksEquiv v s n).symm z) =
      List.ofFn z.1 ++ (List.ofFn z.2).flatMap List.ofFn := by
  change List.ofFn (Fin.append z.1 (fun i : Fin (n * s) =>
    z.2 (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)) = _
  rw [List.ofFn_fin_append, List.ofFn_mul, List.flatMap_def, List.map_ofFn]
  congr 2
  congr 1
  funext i
  congr 1
  funext j
  have hi : (⟨i.val * s + j.val, by
      simpa [finProdFinEquiv, Nat.mul_comm, Nat.add_comm] using
        (finProdFinEquiv (i, j)).isLt⟩ : Fin (n * s)) =
      finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  simp only [hi, Equiv.symm_apply_apply]

end FSS23105365

-- From Solutions.FSS23105365_BlockDecoding
set_option autoImplicit false
namespace FSS23105365

/-- Decode successive blocks using the permutation indexed by the current
hidden state. This is the sequential specification of Algorithm 1's output. -/
def decodeBlocks {H U : Type} (τ : H → U → H) (π : H → U ≃ U) :
    (n : ℕ) → H → (Fin n → U) → (Fin n → U)
  | 0, _, u => u
  | n + 1, h, u => Fin.cons (π h (u 0))
      (decodeBlocks τ π n (τ h (u 0)) (Fin.tail u))

/-- Recover the source blocks from the output, updating hidden states using
the recovered source block, not the decoded output block. -/
def encodeBlocks {H U : Type} (τ : H → U → H) (π : H → U ≃ U) :
    (n : ℕ) → H → (Fin n → U) → (Fin n → U)
  | 0, _, w => w
  | n + 1, h, w =>
      let u := (π h).symm (w 0)
      Fin.cons u (encodeBlocks τ π n (τ h u) (Fin.tail w))

theorem encode_decode_blocks {H U : Type} (τ : H → U → H) (π : H → U ≃ U)
    (n : ℕ) (h : H) (u : Fin n → U) :
    encodeBlocks τ π n h (decodeBlocks τ π n h u) = u := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih => simp [decodeBlocks, encodeBlocks, ih]

theorem decode_encode_blocks {H U : Type} (τ : H → U → H) (π : H → U ≃ U)
    (n : ℕ) (h : H) (w : Fin n → U) :
    decodeBlocks τ π n h (encodeBlocks τ π n h w) = w := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih => simp [decodeBlocks, encodeBlocks, ih]

/-- The entire state-dependent block decoder is a permutation. No
independence assumption about the successive hidden states is needed. -/
def blockDecodeEquiv {H U : Type} (τ : H → U → H) (π : H → U ≃ U)
    (n : ℕ) (h : H) : (Fin n → U) ≃ (Fin n → U) where
  toFun := decodeBlocks τ π n h
  invFun := encodeBlocks τ π n h
  left_inv := encode_decode_blocks τ π n h
  right_inv := decode_encode_blocks τ π n h

/-- The sequential specification agrees with the parallel block formula
once the hidden prefix states are available. -/
theorem decodeBlocks_apply {H U : Type} (τ : H → U → H) (π : H → U ≃ U)
    (n : ℕ) (h : H) (u : Fin n → U) (i : Fin n) :
    decodeBlocks τ π n h u i = π (drivenPath τ n h u i.castSucc) (u i) := by
  induction n generalizing h with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [decodeBlocks]
    · have ht : Fin.tail u = (fun j => u j.succ) := Fin.tail_def
      simpa [decodeBlocks, drivenPath, ht] using ih (τ h (u 0)) (Fin.tail u) j

/-- Block projection is preserved along the whole trajectory. -/
theorem decoded_blocks_path {Q H U : Type} (δ : Q → U → Q)
    (τ : H → U → H) (π : H → U ≃ U) (φ : H → Q)
    (hproj : ∀ h u, φ (τ h u) = δ (φ h) (π h u))
    (n : ℕ) (h : H) (u : Fin n → U) :
    drivenPath δ n (φ h) (decodeBlocks τ π n h u) =
      φ ∘ drivenPath τ n h u := by
  apply (drivenPath_eq_iff δ n (φ h) _ _).mpr
  constructor
  · simp
  · intro i
    simp only [Function.comp_apply, decodeBlocks_apply, drivenPath_step, hproj]

/-- One output sequence has exactly one source sequence under block decoding. -/
theorem decoded_blocks_fiber_card {H U : Type} [Fintype U] [DecidableEq U]
    (τ : H → U → H) (π : H → U ≃ U) (n : ℕ) (h : H) (w : Fin n → U) :
    Fintype.card {u : Fin n → U // decodeBlocks τ π n h u = w} = 1 := by
  classical
  let e := blockDecodeEquiv τ π n h
  have he : ∀ u, decodeBlocks τ π n h u = w ↔ u = e.symm w :=
    fun u => e.eq_symm_apply.symm
  simp only [he]
  simp

end FSS23105365

-- From Definitions.Def_FSS23105365_DFARun
set_option autoImplicit false
namespace FSS23105365

/-- The state after reading the first `t` bits of the supplied word. -/
def BinaryDFA.stateAfter {r m : ℕ} (B : BinaryDFA r) (x : Bits m) (t : ℕ) : Fin r :=
  ((List.ofFn x).take t).foldl B.step B.start

/-- States of a binary DFA observed after the initial `v` bits and then at
successive `s`-bit block boundaries. The last time is the full word length. -/
def BinaryDFA.sampledPath {q r n : ℕ} (B : BinaryDFA r)
    (φ : Fin r → Fin q) (v s : ℕ) (x : Bits (v + n * s)) : Path q n :=
  fun i => φ (B.stateAfter x (v + s * i.val))

end FSS23105365

-- From Solutions.FSS23105365_RunSamplerCorrectness
set_option autoImplicit false
namespace FSS23105365

/-- The mathematical data supplied by Lemma 3.5. Existence of this structure
is a separate obligation; the correctness theorems below take it explicitly. -/
structure HiddenBlockModel {q : ℕ} (A : BinaryDFA q) (H : Type) (b : ℕ) where
  step : H → Bits b → H
  project : H → Fin q
  project_surjective : Function.Surjective project
  decode : H → Bits b ≃ Bits b
  block_project : ∀ h u, project (step h u) =
    (List.ofFn (decode h u)).foldl A.step (project h)
  aperiodic : AperiodicTransitions step

/-- Split a word into consecutive full blocks followed by its unchanged tail. -/
def blockTailEquiv (b m r : ℕ) : Bits (m * b + r) ≃
    ((Fin m → Bits b) × Bits r) where
  toFun x := (fun i j => x (Fin.castAdd r (finProdFinEquiv (i, j))),
    fun j => x (Fin.natAdd (m * b) j))
  invFun z := Fin.append (fun i => z.1 (finProdFinEquiv.symm i).1
    (finProdFinEquiv.symm i).2) z.2
  left_inv x := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
      change x (Fin.castAdd r (finProdFinEquiv (finProdFinEquiv.symm j))) = _
      rw [Equiv.apply_symm_apply]
    · simp only [Fin.append_right]
  right_inv z := by
    apply Prod.ext
    · funext i j
      simp only [Fin.append_left]
      rw [Equiv.symm_apply_apply]
    · funext j; simp

theorem blockTail_list (b m r : ℕ) (z : (Fin m → Bits b) × Bits r) :
    List.ofFn ((blockTailEquiv b m r).symm z) =
      (List.ofFn z.1).flatMap List.ofFn ++ List.ofFn z.2 := by
  change List.ofFn (Fin.append (fun i : Fin (m * b) =>
    z.1 (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) z.2) = _
  rw [List.ofFn_fin_append, List.ofFn_mul, List.flatMap_def, List.map_ofFn]
  congr 2
  congr 1
  funext i
  congr 1
  funext j
  have hi : (⟨i.val * b + j.val, by
      simpa [finProdFinEquiv, Nat.mul_comm, Nat.add_comm] using
        (finProdFinEquiv (i, j)).isLt⟩ : Fin (m * b)) =
      finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  simp only [hi, Equiv.symm_apply_apply]

/-- The source-to-output word map of Algorithm 1, including its unchanged
tail, is a permutation on exactly `m * b + r` input bits. -/
def hiddenWordEquiv {H : Type} {b : ℕ} (τ : H → Bits b → H)
    (π : H → Bits b ≃ Bits b) (h : H) (m r : ℕ) :
    Bits (m * b + r) ≃ Bits (m * b + r) :=
  (blockTailEquiv b m r).trans
    ((Equiv.prodCongr (blockDecodeEquiv τ π m h) (Equiv.refl (Bits r))).trans
      (blockTailEquiv b m r).symm)

theorem hiddenWord_list {H : Type} {b : ℕ} (τ : H → Bits b → H)
    (π : H → Bits b ≃ Bits b) (h : H) (m r : ℕ) (x : Bits (m * b + r)) :
    List.ofFn (hiddenWordEquiv τ π h m r x) =
      (List.ofFn (decodeBlocks τ π m h ((blockTailEquiv b m r x).1))).flatMap
        List.ofFn ++ List.ofFn (blockTailEquiv b m r x).2 := by
  exact blockTail_list b m r _

/-- Positive and zero-length tail cases use the same exact uniform law. -/
theorem hiddenWord_uniform {H : Type} {b : ℕ} (τ : H → Bits b → H)
    (π : H → Bits b ≃ Bits b) (h : H) (m r : ℕ) (w : Bits (m * b + r)) :
    (Fintype.card {x : Bits (m * b + r) // hiddenWordEquiv τ π h m r x = w} : ℝ) /
        2 ^ (m * b + r) = 1 / 2 ^ (m * b + r) := by
  classical
  have hc : Fintype.card {x : Bits (m * b + r) //
      hiddenWordEquiv τ π h m r x = w} = 1 := by
    let e := hiddenWordEquiv τ π h m r
    have he : ∀ x, e x = w ↔ x = e.symm w := fun x => e.eq_symm_apply.symm
    change Fintype.card {x // e x = w} = 1
    simp only [he]
    simp
  rw [hc, Nat.cast_one]

/-- Folding flattened blocks equals folding their individual transition maps. -/
theorem foldl_flatMap_blocks {Q : Type} {b : ℕ} (δ : Q → Bool → Q)
    (ws : List (Bits b)) (q : Q) :
    (ws.flatMap List.ofFn).foldl δ q =
      ws.foldl (fun q w => (List.ofFn w).foldl δ q) q := by
  induction ws generalizing q with
  | nil => rfl
  | cons w ws ih => simp only [List.flatMap_cons, List.foldl_append, List.foldl_cons, ih]

/-- Every decoded block boundary agrees with the projected hidden state.
This is the boundary-consistency step in Proposition 3.2. -/
theorem hidden_block_boundary {q b : ℕ} {H : Type} (A : BinaryDFA q)
    (B : HiddenBlockModel A H b) (m : ℕ) (h : H) (u : Fin m → Bits b)
    (i : Fin (m + 1)) :
    (((List.ofFn (decodeBlocks B.step B.decode m h u)).flatMap List.ofFn).take
      (b * i.val)).foldl A.step (B.project h) =
        B.project (drivenPath B.step m h u i) := by
  rw [take_flatMap_bits, foldl_flatMap_blocks, drivenPath_prefix]
  exact congrFun (decoded_blocks_path
    (fun q w => (List.ofFn w).foldl A.step q)
    B.step B.decode B.project B.block_project m h u) i

theorem flatMap_bits_length {b : ℕ} (us : List (Bits b)) :
    (us.flatMap List.ofFn).length = us.length * b := by
  induction us with
  | nil => simp
  | cons u us ih => simp [ih, Nat.add_mul, Nat.add_comm]

theorem take_append_complete_prefix {α : Type} (xs ys : List α) (t : ℕ) :
    (xs ++ ys).take (xs.length + t) = xs ++ ys.take t := by
  rw [List.take_append]
  simp

/-- A prefix ending within a block consists of all prior blocks and the
corresponding prefix of that one block. -/
theorem take_flatMap_bits_inside {b m : ℕ} (u : Fin m → Bits b)
    (i : Fin m) (t : ℕ) (ht : t ≤ b) :
    ((List.ofFn u).flatMap List.ofFn).take (b * i.val + t) =
      ((List.ofFn u).take i.val).flatMap List.ofFn ++ (List.ofFn (u i)).take t := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add, List.take_zero,
        List.flatMap_nil, List.nil_append, List.ofFn_succ, List.flatMap_cons]
      apply List.take_append_of_le_length
      simpa using ht
    · rw [List.ofFn_succ, List.flatMap_cons]
      have hp : b * (j.succ : Fin (m + 1)).val + t =
          (List.ofFn (u 0)).length + (b * j.val + t) := by
        simp [Fin.val_succ, List.length_ofFn, Nat.mul_add, Nat.add_comm, Nat.add_left_comm]
      rw [hp, take_append_complete_prefix, ih (fun i => u i.succ) j]
      simp only [Fin.val_succ, List.take_succ_cons, List.flatMap_cons, List.append_assoc]

/-- Decoding the `t`th position of a full block from its hidden boundary
gives exactly the true DFA state after that many output bits. -/
theorem hidden_block_inside {q b : ℕ} {H : Type} (A : BinaryDFA q)
    (B : HiddenBlockModel A H b) (m : ℕ) (h : H) (u : Fin m → Bits b)
    (i : Fin m) (t : ℕ) (ht : t ≤ b) :
    (((List.ofFn (decodeBlocks B.step B.decode m h u)).flatMap List.ofFn).take
      (b * i.val + t)).foldl A.step (B.project h) =
        ((List.ofFn (B.decode (drivenPath B.step m h u i.castSucc) (u i))).take t).foldl
          A.step (B.project (drivenPath B.step m h u i.castSucc)) := by
  rw [take_flatMap_bits_inside _ i t ht, List.foldl_append]
  have hb := hidden_block_boundary A B m h u i.castSucc
  rw [take_flatMap_bits] at hb
  simp only [Fin.val_castSucc] at hb
  rw [hb, decodeBlocks_apply]

/-- Appending the tail preserves every state computed inside a full block. -/
theorem hidden_word_inside {q b : ℕ} {H : Type} (A : BinaryDFA q)
    (B : HiddenBlockModel A H b) (m r : ℕ) (h : H) (u : Fin m → Bits b)
    (v : Bits r) (i : Fin m) (t : ℕ) (ht : t ≤ b) :
    ((List.ofFn ((blockTailEquiv b m r).symm
      (decodeBlocks B.step B.decode m h u, v))).take (b * i.val + t)).foldl
        A.step (B.project h) =
      ((List.ofFn (B.decode (drivenPath B.step m h u i.castSucc) (u i))).take t).foldl
        A.step (B.project (drivenPath B.step m h u i.castSucc)) := by
  rw [blockTail_list, List.take_append_of_le_length]
  · exact hidden_block_inside A B m h u i t ht
  · rw [flatMap_bits_length, List.length_ofFn]
    have hi : i.val + 1 ≤ m := i.isLt
    calc
      b * i.val + t ≤ b * i.val + b := Nat.add_le_add_left ht _
      _ = (i.val + 1) * b := by rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm i.val b]
      _ ≤ m * b := Nat.mul_le_mul_right b hi

/-- The tail advances from the last projected hidden state. This also
covers `m = 0`, where all output positions belong to the tail. -/
theorem hidden_word_tail {q b : ℕ} {H : Type} (A : BinaryDFA q)
    (B : HiddenBlockModel A H b) (m r : ℕ) (h : H) (u : Fin m → Bits b)
    (v : Bits r) (t : ℕ) :
    ((List.ofFn ((blockTailEquiv b m r).symm
      (decodeBlocks B.step B.decode m h u, v))).take (m * b + t)).foldl
        A.step (B.project h) =
      ((List.ofFn v).take t).foldl A.step
        (B.project (drivenPath B.step m h u (Fin.last m))) := by
  rw [blockTail_list]
  have hl : ((List.ofFn (decodeBlocks B.step B.decode m h u)).flatMap List.ofFn).length =
      m * b := by rw [flatMap_bits_length, List.length_ofFn]
  rw [← hl, take_append_complete_prefix, List.foldl_append]
  have hb := hidden_block_boundary A B m h u (Fin.last m)
  simp only [Fin.val_last] at hb
  rw [Nat.mul_comm b m, ← hl, List.take_length] at hb
  rw [hb]

/-- Algorithm 1's trajectory, expressed solely in terms of hidden prefix
states and constant-length block/tail lookups. -/
def locallyDecodedPath {q b : ℕ} {H : Type} (A : BinaryDFA q)
    (B : HiddenBlockModel A H b) (m r : ℕ) (h : H)
    (u : Fin m → Bits b) (v : Bits r) : Fin (m * b + r + 1) → Fin q :=
  fun i => if hi : i.val / b < m then
    let j : Fin m := ⟨i.val / b, hi⟩
    ((List.ofFn (B.decode (drivenPath B.step m h u j.castSucc) (u j))).take
      (i.val % b)).foldl A.step (B.project (drivenPath B.step m h u j.castSucc))
  else
    ((List.ofFn v).take (i.val - m * b)).foldl A.step
      (B.project (drivenPath B.step m h u (Fin.last m)))

/-- The parallel local decoding prescription gives every coordinate of
the true complete run, including the initial and final coordinates. -/
theorem locallyDecodedPath_correct {q b : ℕ} {H : Type} (A : BinaryDFA q)
    (B : HiddenBlockModel A H b) (hb : 0 < b) (m r : ℕ) (h : H)
    (u : Fin m → Bits b) (v : Bits r) :
    locallyDecodedPath A B m r h u v =
      drivenPath A.step (m * b + r) (B.project h)
        ((blockTailEquiv b m r).symm (decodeBlocks B.step B.decode m h u, v)) := by
  funext i
  rw [← drivenPath_prefix]
  unfold locallyDecodedPath
  split_ifs with hi
  · have hp := hidden_word_inside A B m r h u v
      ⟨i.val / b, hi⟩ (i.val % b) (Nat.mod_lt _ hb).le
    rw [Nat.div_add_mod] at hp
    exact hp.symm
  · have hle : m * b ≤ i.val := by
      have hh : m ≤ i.val / b := Nat.le_of_not_gt hi
      exact (Nat.le_div_iff_mul_le hb).mp hh
    have hp := hidden_word_tail A B m r h u v (i.val - m * b)
    rw [Nat.add_sub_of_le hle] at hp
    exact hp.symm

/-- The finite graph of a function of a uniform permuted source has
singleton fibers precisely on that graph. -/
theorem equiv_graph_fiber_card {E Ω : Type} [Fintype E] [DecidableEq E] [DecidableEq Ω]
    (e : E ≃ E) (f : E → Ω) (w : E) (z : Ω) :
    Fintype.card {x : E // (e x, f (e x)) = (w, z)} = if z = f w then 1 else 0 := by
  classical
  have he : ∀ x, (e x, f (e x)) = (w, z) ↔ x = e.symm w ∧ f w = z := by
    intro x
    rw [Prod.mk.injEq]
    constructor
    · rintro ⟨hx, hz⟩
      exact ⟨e.eq_symm_apply.mpr hx, hx ▸ hz⟩
    · rintro ⟨hx, hz⟩
      simp [hx, hz]
  simp only [he]
  by_cases hz : z = f w
  · simp [hz]
  · have hz' : f w ≠ z := Ne.symm hz
    simp [hz, hz']

/-- Conditional correctness of Proposition 3.2's full sampler: assuming
the hidden block representation, its local outputs have exactly the joint
uniform-word/full-run law. No AC0 complexity conclusion is asserted here. -/
theorem hidden_run_sampler_law {q b : ℕ} {H : Type} (A : BinaryDFA q)
    (B : HiddenBlockModel A H b) (hb : 0 < b) (m r : ℕ) (h : H)
    (hh : B.project h = A.start) (w : Bits (m * b + r))
    (γ : Path q (m * b + r)) :
    (Fintype.card {x : Bits (m * b + r) //
      (hiddenWordEquiv B.step B.decode h m r x,
        locallyDecodedPath A B m r h (blockTailEquiv b m r x).1
          (blockTailEquiv b m r x).2) = (w, γ)} : ℝ) / 2 ^ (m * b + r) =
      if γ = drivenPath A.step (m * b + r) A.start w then 1 / 2 ^ (m * b + r) else 0 := by
  classical
  have hpath : ∀ x : Bits (m * b + r),
      locallyDecodedPath A B m r h (blockTailEquiv b m r x).1
        (blockTailEquiv b m r x).2 =
        drivenPath A.step (m * b + r) A.start (hiddenWordEquiv B.step B.decode h m r x) := by
    intro x
    rw [locallyDecodedPath_correct A B hb, hh]
    rfl
  simp only [hpath]
  rw [equiv_graph_fiber_card]
  split_ifs <;> simp

end FSS23105365

-- From Solutions.FSS23105365_AperiodicPrefixFormulas
set_option autoImplicit false
namespace FSS23105365

/-- Fixed-start prefix formulas on precisely the original block bits.
There are no input wires for the fixed start state. -/
theorem aperiodic_block_prefix_formulas {H Out : Type} [Fintype H] [Fintype Out]
    {b : ℕ} (τ : H → Bits b → H) (hτ : AperiodicTransitions τ) (h : H)
    (observe : H → Out → Bool) :
    ∃ D C k : ℕ, ∃ fs : (m : ℕ) → Fin (m + 1) → Out → CircuitFormula (m * b),
      (∀ m t j, formulaDepth (fs m t j) ≤ D) ∧
      (∀ m t j, formulaCost (fs m t j) ≤ C * (m + 1) ^ k) ∧
      (∀ m t j (seed : Bits (m * b)), formulaEval (fs m t j) seed =
        observe (drivenPath τ m h (fun i l => seed (finProdFinEquiv (i, l))) t) j) := by
  classical
  have hex : ∀ j : Out, ∃ e : StarFreeExpr (Bits b), ∀ w,
      sfDenote e w ↔ observe (w.foldl τ h) j = true :=
    fun j => aperiodic_observation_language_starFree τ hτ h (fun h => observe h j)
  choose e he using hex
  obtain ⟨D, C, k, f, hd, hc, hv⟩ := starFree_family_prefix_formulas (id : Bits b → Bits b) e
  refine ⟨D, C, k, fun m t j => f m j t, fun m t j => hd m j t,
    fun m t j => hc m j t, ?_⟩
  intro m t j seed
  apply Bool.eq_iff_iff.mpr
  rw [hv, he, wordCutLeft_list_take, drivenPath_prefix]
  rfl

/-- Adding a tail only relabels existing input wires. Prefix-state
formulas ignore the tail and retain their original depth and cost. -/
theorem aperiodic_block_tail_prefix_formulas {H Out : Type} [Fintype H] [Fintype Out]
    {b : ℕ} (τ : H → Bits b → H) (hτ : AperiodicTransitions τ) (h : H)
    (observe : H → Out → Bool) :
    ∃ D C k : ℕ, ∃ fs : (m r : ℕ) → Fin (m + 1) → Out → CircuitFormula (m * b + r),
      (∀ m r t j, formulaDepth (fs m r t j) ≤ D) ∧
      (∀ m r t j, formulaCost (fs m r t j) ≤ C * (m + 1) ^ k) ∧
      (∀ m r t j (seed : Bits (m * b + r)), formulaEval (fs m r t j) seed =
        observe (drivenPath τ m h (blockTailEquiv b m r seed).1 t) j) := by
  obtain ⟨D, C, k, fs, hd, hc, he⟩ := aperiodic_block_prefix_formulas τ hτ h observe
  refine ⟨D, C, k, fun m r t j => relabelFormula (Fin.castAdd r) (fs m t j), ?_, ?_, ?_⟩
  · intro m r t j
    rw [relabelFormula_depth]
    exact hd m t j
  · intro m r t j
    rw [relabelFormula_cost]
    exact hc m t j
  · intro m r t j seed
    rw [relabelFormula_eval, he]
    rfl

end FSS23105365

-- From Solutions.FSS23105365_HiddenLocalOutputs
set_option autoImplicit false
namespace FSS23105365

theorem hiddenWordEquiv_block_bit {H : Type} {b : ℕ} (τ : H → Bits b → H)
    (π : H → Bits b ≃ Bits b) (h : H) (m r : ℕ) (seed : Bits (m * b + r))
    (i : Fin m) (j : Fin b) :
    hiddenWordEquiv τ π h m r seed (Fin.castAdd r (finProdFinEquiv (i, j))) =
      π (drivenPath τ m h (blockTailEquiv b m r seed).1 i.castSucc)
        ((blockTailEquiv b m r seed).1 i) j := by
  change Fin.append (fun k => decodeBlocks τ π m h (blockTailEquiv b m r seed).1
    (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    (blockTailEquiv b m r seed).2 (Fin.castAdd r (finProdFinEquiv (i, j))) = _
  rw [Fin.append_left, Equiv.symm_apply_apply, decodeBlocks_apply]

theorem hiddenWordEquiv_tail_bit {H : Type} {b : ℕ} (τ : H → Bits b → H)
    (π : H → Bits b ≃ Bits b) (h : H) (m r : ℕ) (seed : Bits (m * b + r)) (i : Fin r) :
    hiddenWordEquiv τ π h m r seed (Fin.natAdd (m * b) i) = seed (Fin.natAdd (m * b) i) := by
  change Fin.append (fun k => decodeBlocks τ π m h (blockTailEquiv b m r seed).1
    (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)
    (blockTailEquiv b m r seed).2 (Fin.natAdd (m * b) i) = _
  rw [Fin.append_right]
  rfl

def hiddenWordFormula {q b : ℕ} {H : Type} [Fintype H] [Nonempty H]
    (A : BinaryDFA q) (B : HiddenBlockModel A H b) (m r : ℕ)
    (state : Fin (m + 1) → Fin (Fintype.card H) → CircuitFormula (m * b + r)) :
    Fin (m * b + r) → CircuitFormula (m * b + r) :=
  Fin.addCases (fun k =>
    let ij := finProdFinEquiv.symm k
    stateLookupFormula (state ij.1.castSucc)
      (fun l => Fin.castAdd r (finProdFinEquiv (ij.1, l)))
      (fun h w => B.decode h w ij.2))
    (fun j => .input (Fin.natAdd (m * b) j))

def hiddenPathFormula {q b : ℕ} {H : Type} [Fintype H] [Nonempty H]
    (A : BinaryDFA q) (B : HiddenBlockModel A H b) (m r : ℕ)
    (state : Fin (m + 1) → Fin (Fintype.card H) → CircuitFormula (m * b + r))
    (i : Fin (m * b + r + 1)) (z : Fin q) : CircuitFormula (m * b + r) :=
  if hi : i.val / b < m then
    let j : Fin m := ⟨i.val / b, hi⟩
    stateLookupFormula (state j.castSucc)
      (fun l => Fin.castAdd r (finProdFinEquiv (j, l)))
      (fun h w => decide (((List.ofFn (B.decode h w)).take (i.val % b)).foldl A.step
        (B.project h) = z))
  else
    stateLookupFormula (state (Fin.last m)) (Fin.natAdd (m * b))
      (fun h v => decide (((List.ofFn v).take (i.val - m * b)).foldl A.step (B.project h) = z))

theorem hiddenWordFormula_eval {q b : ℕ} {H : Type} [Fintype H] [Nonempty H]
    (A : BinaryDFA q) (B : HiddenBlockModel A H b) (m r : ℕ) (h : H)
    (state : Fin (m + 1) → Fin (Fintype.card H) → CircuitFormula (m * b + r))
    (seed : Bits (m * b + r))
    (hs : ∀ t j, formulaEval (state t j) seed =
      finiteOneHot (drivenPath B.step m h (blockTailEquiv b m r seed).1 t) j)
    (i : Fin (m * b + r)) :
    formulaEval (hiddenWordFormula A B m r state i) seed =
      hiddenWordEquiv B.step B.decode h m r seed i := by
  refine Fin.addCases (fun k => ?_) (fun j => ?_) i
  · rw [hiddenWordFormula, Fin.addCases_left]
    rw [stateLookupFormula_eval _ _ _ seed _ (hs _)]
    have he := hiddenWordEquiv_block_bit B.step B.decode h m r seed
      (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
    change B.decode (drivenPath B.step m h (blockTailEquiv b m r seed).1
      (finProdFinEquiv.symm k).1.castSucc)
      ((blockTailEquiv b m r seed).1 (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2 = _
    simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using he.symm
  · rw [hiddenWordFormula, Fin.addCases_right, formulaEval, hiddenWordEquiv_tail_bit]

theorem hiddenPathFormula_eval {q b : ℕ} {H : Type} [Fintype H] [Nonempty H]
    (A : BinaryDFA q) (B : HiddenBlockModel A H b) (m r : ℕ) (h : H)
    (state : Fin (m + 1) → Fin (Fintype.card H) → CircuitFormula (m * b + r))
    (seed : Bits (m * b + r))
    (hs : ∀ t j, formulaEval (state t j) seed =
      finiteOneHot (drivenPath B.step m h (blockTailEquiv b m r seed).1 t) j)
    (i : Fin (m * b + r + 1)) (z : Fin q) :
    formulaEval (hiddenPathFormula A B m r state i z) seed =
      decide (locallyDecodedPath A B m r h (blockTailEquiv b m r seed).1
        (blockTailEquiv b m r seed).2 i = z) := by
  unfold hiddenPathFormula locallyDecodedPath
  split_ifs with hi
  · rw [stateLookupFormula_eval _ _ _ seed _ (hs _)]
    rfl
  · rw [stateLookupFormula_eval _ _ _ seed _ (hs _)]
    rfl

theorem hiddenWordFormula_depth {q b : ℕ} {H : Type} [Fintype H] [Nonempty H]
    (A : BinaryDFA q) (B : HiddenBlockModel A H b) (m r D : ℕ)
    (state : Fin (m + 1) → Fin (Fintype.card H) → CircuitFormula (m * b + r))
    (hd : ∀ t j, formulaDepth (state t j) ≤ D) (i : Fin (m * b + r)) :
    formulaDepth (hiddenWordFormula A B m r state i) ≤ D + 3 := by
  refine Fin.addCases (fun k => ?_) (fun j => ?_) i
  · rw [hiddenWordFormula, Fin.addCases_left]
    exact stateLookupFormula_depth _ _ _ D (hd _)
  · simp only [hiddenWordFormula, Fin.addCases_right, formulaDepth, Nat.zero_le]

theorem hiddenPathFormula_depth {q b : ℕ} {H : Type} [Fintype H] [Nonempty H]
    (A : BinaryDFA q) (B : HiddenBlockModel A H b) (m r D : ℕ)
    (state : Fin (m + 1) → Fin (Fintype.card H) → CircuitFormula (m * b + r))
    (hd : ∀ t j, formulaDepth (state t j) ≤ D)
    (i : Fin (m * b + r + 1)) (z : Fin q) :
    formulaDepth (hiddenPathFormula A B m r state i z) ≤ D + 3 := by
  unfold hiddenPathFormula
  split_ifs <;> exact stateLookupFormula_depth _ _ _ D (hd _)

theorem hiddenWordFormula_cost {q b : ℕ} {H : Type} [Fintype H] [Nonempty H]
    (A : BinaryDFA q) (B : HiddenBlockModel A H b) (m r K : ℕ)
    (state : Fin (m + 1) → Fin (Fintype.card H) → CircuitFormula (m * b + r))
    (hk : ∀ t j, formulaCost (state t j) ≤ K) (i : Fin (m * b + r)) :
    formulaCost (hiddenWordFormula A B m r state i) ≤
      (2 ^ (Fintype.card H + b) * (3 * (Fintype.card H + b) + 2) + 1) * (K + 1) + K := by
  refine Fin.addCases (fun k => ?_) (fun j => ?_) i
  · rw [hiddenWordFormula, Fin.addCases_left]
    exact stateLookupFormula_cost _ _ _ K (hk _) le_rfl
  · simp only [hiddenWordFormula, Fin.addCases_right, formulaCost, Nat.zero_le]

theorem hiddenPathFormula_cost {q b : ℕ} {H : Type} [Fintype H] [Nonempty H]
    (A : BinaryDFA q) (B : HiddenBlockModel A H b) (m r K : ℕ) (hr : r ≤ b)
    (state : Fin (m + 1) → Fin (Fintype.card H) → CircuitFormula (m * b + r))
    (hk : ∀ t j, formulaCost (state t j) ≤ K)
    (i : Fin (m * b + r + 1)) (z : Fin q) :
    formulaCost (hiddenPathFormula A B m r state i z) ≤
      (2 ^ (Fintype.card H + b) * (3 * (Fintype.card H + b) + 2) + 1) * (K + 1) + K := by
  unfold hiddenPathFormula
  split_ifs
  · exact stateLookupFormula_cost _ _ _ K (hk _) le_rfl
  · exact stateLookupFormula_cost _ _ _ K (hk _) hr

end FSS23105365

-- From Solutions.FSS23105365_EncodingFacts
set_option autoImplicit false
namespace FSS23105365

theorem pairOutcomeEncode_injective (n : ℕ) :
    Function.Injective (@pairOutcomeEncode n) := by
  intro x y h
  apply Prod.ext
  · funext i
    exact congrFun h (some i)
  · exact congrFun h none

theorem pathEncode_injective (q n : ℕ) :
    Function.Injective (@pathEncode q n) := by
  intro γ η h
  funext i
  have hi := congrFun h (i, γ i)
  have hval : η i = γ i := of_decide_eq_true (by
    simpa only [pathEncode, decide_true] using hi.symm)
  exact hval.symm

end FSS23105365

-- From Solutions.FSS23105365_HiddenRunCircuits
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

abbrev FullRunOutput (q n : ℕ) := Fin n ⊕ (Fin (n + 1) × Fin q)

def fullRunEncode {q n : ℕ} (z : Bits n × Path q n) : FullRunOutput q n → Bool :=
  Sum.elim z.1 (pathEncode z.2)

theorem fullRunEncode_injective (q n : ℕ) : Function.Injective (@fullRunEncode q n) := by
  intro x y he
  apply Prod.ext
  · funext i
    exact congrFun he (Sum.inl i)
  · apply pathEncode_injective q n
    funext i
    exact congrFun he (Sum.inr i)

/-- The hidden block algorithm is an actual Circuit with no extra input
bits. The depth and polynomial bound are common to all block counts and
all tails of length at most the fixed block length. -/
theorem hidden_run_circuits {q b : ℕ} {H : Type} [Fintype H]
    (A : BinaryDFA q) (B : HiddenBlockModel A H b) (hb : 0 < b) (h : H) :
    ∃ D C k : ℕ, ∀ m r : ℕ, r ≤ b →
      ∃ S : Circuit (FullRunOutput q (m * b + r)), ∃ hbits : S.randomBits = m * b + r,
        S.depth ≤ D ∧ S.size ≤ C * (m * b + r + 1) ^ k ∧
        ∀ seed : Bits (m * b + r), S.eval (fun i => seed (Fin.cast hbits i)) =
          fullRunEncode (hiddenWordEquiv B.step B.decode h m r seed,
            locallyDecodedPath A B m r h (blockTailEquiv b m r seed).1
              (blockTailEquiv b m r seed).2) := by
  letI : Nonempty H := ⟨h⟩
  obtain ⟨D, C, k, state, hd, hc, he⟩ :=
    aperiodic_block_tail_prefix_formulas B.step B.aperiodic h finiteOneHot
  let L := 2 ^ (Fintype.card H + b) * (3 * (Fintype.card H + b) + 2) + 1
  let K := L * (C + 1) + C
  refine ⟨D + 3, 1 + (q + 1) * (K + 1), k + 1, fun m r hr => ?_⟩
  let n := m * b + r
  let fs : FullRunOutput q n → CircuitFormula n :=
    Sum.elim (hiddenWordFormula A B m r (state m r))
      (fun o => hiddenPathFormula A B m r (state m r) o.1 o.2)
  have hdep : ∀ o, formulaDepth (fs o) ≤ D + 3 := by
    intro o
    cases o with
    | inl i => exact hiddenWordFormula_depth A B m r D (state m r) (hd m r) i
    | inr o => exact hiddenPathFormula_depth A B m r D (state m r) (hd m r) o.1 o.2
  have hmn : m ≤ n := by dsimp only [n]; nlinarith
  have hstate : ∀ t j, formulaCost (state m r t j) ≤ C * (n + 1) ^ k := fun t j =>
    (hc m r t j).trans (monomial_bound_mono C m n k k hmn le_rfl)
  have hcost : ∀ o, formulaCost (fs o) ≤ K * (n + 1) ^ k := by
    intro o
    have hlocal : formulaCost (fs o) ≤ L * (C * (n + 1) ^ k + 1) + C * (n + 1) ^ k := by
      cases o with
      | inl i => exact hiddenWordFormula_cost A B m r _ (state m r) hstate i
      | inr o => exact hiddenPathFormula_cost A B m r _ hr (state m r) hstate o.1 o.2
    have hp := Nat.one_le_pow' k n
    dsimp only [K]
    nlinarith
  obtain ⟨S, hbits, hval, hD, hsize⟩ := formula_fintype_family_circuit fs (D + 3) hdep
  refine ⟨S, hbits, hD, ?_, ?_⟩
  · have hout : Fintype.card (FullRunOutput q n) = n + (n + 1) * q := by
      simp [FullRunOutput, Fintype.card_sum, Fintype.card_prod]
    have hsum : (∑ o, formulaCost (fs o)) ≤ (n + (n + 1) * q) * (K * (n + 1) ^ k) := by
      simpa only [Finset.sum_const, Finset.card_univ, hout, nsmul_eq_mul, Nat.cast_id]
        using Finset.sum_le_sum (fun o (_ : o ∈ Finset.univ) => hcost o)
    have hsum' : (∑ o, formulaCost (fs o)) ≤ (q + 1) * K * (n + 1) ^ (k + 1) := by
      calc
        _ ≤ (n + (n + 1) * q) * (K * (n + 1) ^ k) := hsum
        _ ≤ ((n + 1) * (q + 1)) * (K * (n + 1) ^ k) :=
          Nat.mul_le_mul_right _ (by nlinarith)
        _ = _ := by ring
    have hp : n + 1 ≤ (n + 1) ^ (k + 1) := by
      simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ n + 1)
        (show 1 ≤ k + 1 by omega)
    rw [hsize, hout]
    change n + (∑ o, formulaCost (fs o)) + (n + (n + 1) * q) ≤
      (1 + (q + 1) * (K + 1)) * (n + 1) ^ (k + 1)
    nlinarith
  · intro seed
    funext o
    rw [hval]
    cases o with
    | inl i =>
      exact hiddenWordFormula_eval A B m r h (state m r) seed
        (fun t j => he m r t j seed) i
    | inr o =>
      exact hiddenPathFormula_eval A B m r h (state m r) seed
        (fun t j => he m r t j seed) o.1 o.2

end FSS23105365

-- From Solutions.FSS23105365_TotalVariation
set_option autoImplicit false
open scoped BigOperators
namespace FSS23105365

/-- Appendix C, Lemma C.1: deterministic projection cannot increase TV distance.
This is valid for arbitrary real weights, hence also for probability laws. -/
theorem tv_map_le {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (p q : α → ℝ) :
    tv (fun b => ∑ a, if f a = b then p a else 0)
       (fun b => ∑ a, if f a = b then q a else 0) ≤ tv p q := by
  classical
  unfold tv
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ = ∑ b, |∑ a, if f a = b then p a - q a else 0| := by
      congr 1
      funext b
      rw [← Finset.sum_sub_distrib]
      congr 2
      funext a
      split_ifs <;> simp
    _ ≤ ∑ b, ∑ a, |if f a = b then p a - q a else 0| := by
      apply Finset.sum_le_sum
      intro b _
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a, |p a - q a| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      simp only [apply_ite abs, abs_zero]
      simp

/-- Appendix C, Lemma C.1, Equation (26): errors of a base law and conditional
law combine with the second base law as the weighting distribution. -/
theorem tv_joint_le {α β : Type} [Fintype α] [Fintype β]
    (p q : α → ℝ) (K L : α → β → ℝ)
    (hq : ∀ a, 0 ≤ q a) (hK : ∀ a b, 0 ≤ K a b)
    (hKsum : ∀ a, ∑ b, K a b = 1) :
    tv (fun z : α × β => p z.1 * K z.1 z.2)
       (fun z : α × β => q z.1 * L z.1 z.2) ≤
      tv p q + ∑ a, q a * tv (K a) (L a) := by
  have hpoint (a : α) (b : β) :
      |p a * K a b - q a * L a b| ≤
        |p a - q a| * K a b + q a * |K a b - L a b| := by
    calc
      _ = |(p a - q a) * K a b + q a * (K a b - L a b)| := by ring_nf
      _ ≤ |(p a - q a) * K a b| + |q a * (K a b - L a b)| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg (hK a b), abs_of_nonneg (hq a)]
  unfold tv
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ (∑ a, ∑ b, (|p a - q a| * K a b + q a * |K a b - L a b|)) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hpoint a b))
    _ = _ := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, hKsum, mul_one]
      rw [add_div]
      congr 1
      simp only [div_eq_mul_inv, Finset.sum_mul, mul_assoc]

/-- The two-factor error bound for independent products, also in Lemma C.1. -/
theorem tv_product_le {α β : Type} [Fintype α] [Fintype β]
    (p q : α → ℝ) (r s : β → ℝ)
    (hq : ∀ a, 0 ≤ q a) (hr : ∀ b, 0 ≤ r b)
    (hqsum : ∑ a, q a = 1) (hrsum : ∑ b, r b = 1) :
    tv (fun z : α × β => p z.1 * r z.2)
       (fun z : α × β => q z.1 * s z.2) ≤ tv p q + tv r s := by
  have h := tv_joint_le p q (fun _ => r) (fun _ => s) hq
    (fun _ b => hr b) (fun _ => hrsum)
  simpa only [← Finset.sum_mul, hqsum, one_mul] using h

end FSS23105365

-- From Solutions.FSS23105365_PositiveKernelContraction
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

def kernelAdvance {Q : Type} [Fintype Q] (P : Q → Q → ℝ) (p : Q → ℝ) : Q → ℝ :=
  fun y => ∑ x, p x * P x y

def finiteL1 {Q : Type} [Fintype Q] (p q : Q → ℝ) : ℝ := ∑ x, |p x - q x|

theorem kernelAdvance_mass {Q : Type} [Fintype Q] (P : Q → Q → ℝ)
    (hrows : ∀ x, ∑ y, P x y = 1) (p : Q → ℝ) :
    (∑ y, kernelAdvance P p y) = ∑ x, p x := by
  unfold kernelAdvance
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hrows, mul_one]

theorem kernelAdvance_nonneg {Q : Type} [Fintype Q] (P : Q → Q → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (p : Q → ℝ) (hp : ∀ x, 0 ≤ p x) :
    ∀ y, 0 ≤ kernelAdvance P p y := by
  intro y
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hp x) (hP x y))

/-- A common positive mass at one destination suffices for strict L1
contraction on equal-mass input vectors. This is a direct finite-sum
Doeblin argument; no Markov-chain convergence theorem is assumed. -/
theorem kernelAdvance_l1_contraction {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Q → Q → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (hrows : ∀ x, ∑ y, P x y = 1) (z : Q) (ε : ℝ)
    (hminor : ∀ x, ε ≤ P x z) (p q : Q → ℝ)
    (hmass : (∑ x, p x) = ∑ x, q x) :
    finiteL1 (kernelAdvance P p) (kernelAdvance P q) ≤ (1 - ε) * finiteL1 p q := by
  classical
  let R : Q → Q → ℝ := fun x y => P x y - if y = z then ε else 0
  have hR : ∀ x y, 0 ≤ R x y := by
    intro x y
    by_cases hy : y = z
    · subst y; simpa [R] using sub_nonneg.mpr (hminor x)
    · simpa [R, hy] using hP x y
  have hRsum : ∀ x, ∑ y, R x y = 1 - ε := by
    intro x
    simp [R, Finset.sum_sub_distrib, hrows]
  have hdiff : ∀ y, kernelAdvance P p y - kernelAdvance P q y =
      ∑ x, (p x - q x) * R x y := by
    intro y
    simp only [kernelAdvance, R, mul_sub, sub_mul, Finset.sum_sub_distrib,
      ← Finset.sum_mul]
    rw [hmass]
    ring
  unfold finiteL1
  simp_rw [hdiff]
  calc
    _ ≤ ∑ y, ∑ x, |p x - q x| * R x y := by
      apply Finset.sum_le_sum
      intro y _
      simpa only [abs_mul, abs_of_nonneg (hR _ _)] using
        (Finset.abs_sum_le_sum_abs (fun x => (p x - q x) * R x y) Finset.univ)
    _ = _ := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hRsum]
      rw [← Finset.sum_mul, mul_comm]

theorem kernelAdvance_iterate_mass {Q : Type} [Fintype Q] (P : Q → Q → ℝ)
    (hrows : ∀ x, ∑ y, P x y = 1) (n : ℕ) (p : Q → ℝ) :
    (∑ x, (kernelAdvance P)^[n] p x) = ∑ x, p x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', kernelAdvance_mass P hrows, ih]

theorem kernelAdvance_iterate_nonneg {Q : Type} [Fintype Q] (P : Q → Q → ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (n : ℕ) (p : Q → ℝ) (hp : ∀ x, 0 ≤ p x) :
    ∀ y, 0 ≤ (kernelAdvance P)^[n] p y := by
  induction n with
  | zero => exact hp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact kernelAdvance_nonneg P hP _ ih

theorem kernelAdvance_iterate_l1_contraction {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Q → Q → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (hrows : ∀ x, ∑ y, P x y = 1) (z : Q) (ε : ℝ) (hε : ε ≤ 1)
    (hminor : ∀ x, ε ≤ P x z) (p q : Q → ℝ)
    (hmass : (∑ x, p x) = ∑ x, q x) (n : ℕ) :
    finiteL1 ((kernelAdvance P)^[n] p) ((kernelAdvance P)^[n] q) ≤
      (1 - ε) ^ n * finiteL1 p q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    calc
      _ ≤ (1 - ε) * finiteL1 ((kernelAdvance P)^[n] p) ((kernelAdvance P)^[n] q) :=
        kernelAdvance_l1_contraction P hP hrows z ε hminor _ _ (by
          rw [kernelAdvance_iterate_mass P hrows, kernelAdvance_iterate_mass P hrows, hmass])
      _ ≤ (1 - ε) * ((1 - ε) ^ n * finiteL1 p q) :=
        mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr hε)
      _ = _ := by rw [pow_succ]; ring

/-- A finite strictly positive stochastic kernel has a nontrivial common
minorization at a fixed destination. -/
theorem positive_kernel_minorization {Q : Type} [Fintype Q] [Nonempty Q]
    (P : Q → Q → ℝ) (hP : ∀ x y, 0 < P x y) (hrows : ∀ x, ∑ y, P x y = 1) :
    ∃ z : Q, ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ x, ε ≤ P x z := by
  classical
  let z : Q := Classical.choice ‹Nonempty Q›
  let μ := Finset.univ.inf' Finset.univ_nonempty (fun x => P x z)
  have hμ : 0 < μ := (Finset.lt_inf'_iff _).mpr (fun x _ => hP x z)
  have hμle : ∀ x, μ ≤ P x z := fun x => Finset.inf'_le _ (Finset.mem_univ x)
  have hle : P z z ≤ 1 := by
    rw [← hrows z]
    exact Finset.single_le_sum (fun x _ => (hP z x).le) (Finset.mem_univ z)
  refine ⟨z, μ / 2, by linarith, by linarith [hμle z], ?_⟩
  intro x
  linarith [hμle x]

end FSS23105365

-- From Solutions.FSS23105365_PositiveKernelConvergence
set_option autoImplicit false
namespace FSS23105365
open Filter
open scoped BigOperators Topology

theorem finiteL1_coordinate_le {Q : Type} [Fintype Q] (p q : Q → ℝ) (x : Q) :
    |p x - q x| ≤ finiteL1 p q := by
  classical
  exact Finset.single_le_sum (fun y _ => abs_nonneg (p y - q y)) (Finset.mem_univ x)

theorem finiteL1_le_two {Q : Type} [Fintype Q] (p q : Q → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) : finiteL1 p q ≤ 2 := by
  calc
    _ ≤ ∑ x, (p x + q x) := Finset.sum_le_sum (fun x _ => by
      simpa only [abs_of_nonneg (hp x), abs_of_nonneg (hq x)] using abs_sub (p x) (q x))
    _ = _ := by rw [Finset.sum_add_distrib, hp1, hq1]; norm_num

theorem kernel_iterate_coordinate_distance {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Q → Q → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (hrows : ∀ x, ∑ y, P x y = 1) (z : Q) (ε : ℝ) (hε : ε ≤ 1)
    (hminor : ∀ x, ε ≤ P x z) (p q : Q → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hp1 : ∑ x, p x = 1) (hq1 : ∑ x, q x = 1) (n : ℕ) (y : Q) :
    |(kernelAdvance P)^[n] p y - (kernelAdvance P)^[n] q y| ≤ 2 * (1 - ε) ^ n := by
  calc
    _ ≤ finiteL1 ((kernelAdvance P)^[n] p) ((kernelAdvance P)^[n] q) :=
      finiteL1_coordinate_le _ _ y
    _ ≤ (1 - ε) ^ n * finiteL1 p q :=
      kernelAdvance_iterate_l1_contraction P hP hrows z ε hε hminor p q
        (hp1.trans hq1.symm) n
    _ ≤ (1 - ε) ^ n * 2 := mul_le_mul_of_nonneg_left (finiteL1_le_two p q hp hq hp1 hq1)
      (pow_nonneg (sub_nonneg.mpr hε) n)
    _ = _ := mul_comm _ _

/-- Every probability trajectory of a strictly contracting finite kernel
converges coordinatewise. The consecutive-difference geometric bound is
proved from the finite-sum contraction estimate. -/
theorem kernel_iterate_has_limit {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Q → Q → ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (hrows : ∀ x, ∑ y, P x y = 1) (z : Q) (ε : ℝ)
    (hεpos : 0 < ε) (hε : ε ≤ 1) (hminor : ∀ x, ε ≤ P x z)
    (p : Q → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) :
    ∃ π : Q → ℝ, ∀ y, Tendsto (fun n => (kernelAdvance P)^[n] p y) atTop (𝓝 (π y)) := by
  have hex : ∀ y : Q, ∃ a : ℝ,
      Tendsto (fun n => (kernelAdvance P)^[n] p y) atTop (𝓝 a) := by
    intro y
    apply cauchySeq_tendsto_of_complete
    apply cauchySeq_of_le_geometric (1 - ε) 2 (by linarith)
    intro n
    have h := kernel_iterate_coordinate_distance P hP hrows z ε hε hminor
      p (kernelAdvance P p) hp (kernelAdvance_nonneg P hP p hp) hp1
      ((kernelAdvance_mass P hrows p).trans hp1) n y
    simpa only [Real.dist_eq, Function.iterate_succ_apply] using h
  choose π hπ using hex
  exact ⟨π, hπ⟩

theorem kernelAdvance_column_lower_bound {Q : Type} [Fintype Q]
    (P : Q → Q → ℝ) (y : Q) (a : ℝ) (hcol : ∀ x, a ≤ P x y)
    (p : Q → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) :
    a ≤ kernelAdvance P p y := by
  calc
    _ = ∑ x, p x * a := by rw [← Finset.sum_mul, hp1, one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hcol x) (hp x))

/-- Positive finite stochastic kernels have one common positive limit for
all initial probability vectors. This derives the convergence input needed
by the terminal hidden-state construction directly, without importing the
paper's cited convergence statement as an unproved assumption. -/
theorem positive_kernel_common_limit {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (P : Q → Q → ℝ) (hP : ∀ x y, 0 < P x y) (hrows : ∀ x, ∑ y, P x y = 1) :
    ∃ π : Q → ℝ, (∀ y, 0 < π y) ∧ (∑ y, π y = 1) ∧
      ∀ p : Q → ℝ, (∀ x, 0 ≤ p x) → (∑ x, p x = 1) →
        ∀ y, Tendsto (fun n => (kernelAdvance P)^[n] p y) atTop (𝓝 (π y)) := by
  classical
  obtain ⟨z, ε, hεpos, hεlt, hminor⟩ := positive_kernel_minorization P hP hrows
  let p₀ : Q → ℝ := fun x => if x = z then 1 else 0
  have hp₀ : ∀ x, 0 ≤ p₀ x := by intro x; simp only [p₀]; split_ifs <;> norm_num
  have hp₀1 : ∑ x, p₀ x = 1 := by simp [p₀]
  have hP0 : ∀ x y, 0 ≤ P x y := fun x y => (hP x y).le
  obtain ⟨π, hπ⟩ := kernel_iterate_has_limit P hP0 hrows z ε hεpos hεlt.le hminor p₀ hp₀ hp₀1
  have hcommon : ∀ p : Q → ℝ, (∀ x, 0 ≤ p x) → (∑ x, p x = 1) →
      ∀ y, Tendsto (fun n => (kernelAdvance P)^[n] p y) atTop (𝓝 (π y)) := by
    intro p hp hp1 y
    have hzlim : Tendsto (fun n : ℕ => 2 * (1 - ε) ^ n) atTop (𝓝 (0 : ℝ)) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
        (sub_nonneg.mpr hεlt.le) (by linarith : 1 - ε < 1)).const_mul 2
    have hdiff : Tendsto (fun n => (kernelAdvance P)^[n] p y - (kernelAdvance P)^[n] p₀ y)
        atTop (𝓝 (0 : ℝ)) := by
      refine squeeze_zero_norm (f := fun n => (kernelAdvance P)^[n] p y -
        (kernelAdvance P)^[n] p₀ y) (fun n => ?_) hzlim
      simpa only [Real.norm_eq_abs] using kernel_iterate_coordinate_distance P hP0 hrows z ε
        hεlt.le hminor p p₀ hp hp₀ hp1 hp₀1 n y
    simpa only [sub_add_cancel, zero_add] using hdiff.add (hπ y)
  have hπpos : ∀ y, 0 < π y := by
    intro y
    let a := Finset.univ.inf' Finset.univ_nonempty (fun x => P x y)
    have ha : 0 < a := (Finset.lt_inf'_iff _).mpr (fun x _ => hP x y)
    have hacol : ∀ x, a ≤ P x y := fun x => Finset.inf'_le _ (Finset.mem_univ x)
    have hbound : ∀ᶠ n in atTop, a ≤ (kernelAdvance P)^[n] p₀ y := by
      apply Filter.eventually_atTop.mpr
      refine ⟨1, fun n hn => ?_⟩
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      rw [Function.iterate_succ_apply']
      exact kernelAdvance_column_lower_bound P y a hacol _
        (kernelAdvance_iterate_nonneg P hP0 m p₀ hp₀)
        ((kernelAdvance_iterate_mass P hrows m p₀).trans hp₀1)
    exact ha.trans_le (ge_of_tendsto (hπ y) hbound)
  have hπsum : ∑ y, π y = 1 := by
    have hs := tendsto_finsetSum Finset.univ (fun y _ => hπ y)
    have hseq : (fun n : ℕ => ∑ y, (kernelAdvance P)^[n] p₀ y) = fun _ => (1 : ℝ) := by
      funext n
      exact (kernelAdvance_iterate_mass P hrows n p₀).trans hp₀1
    rw [hseq] at hs
    exact tendsto_nhds_unique hs tendsto_const_nhds
  exact ⟨π, hπpos, hπsum, hcommon⟩

end FSS23105365

-- From Solutions.FSS23105365_FiberPermutation
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

theorem fiber_card_eq_sum {U Q : Type} [Fintype U] [DecidableEq Q]
    (f : U → Q) (q : Q) :
    Fintype.card {u : U // f u = q} = ∑ u, if f u = q then 1 else 0 := by
  classical
  simp [Fintype.card_subtype]

/-- Destination counts aggregate exactly under a many-to-one projection. -/
theorem fiber_card_comp {U Q R : Type} [Fintype U] [Fintype Q]
    [DecidableEq Q] [DecidableEq R] (f : U → Q) (g : Q → R) (r : R) :
    Fintype.card {u : U // g (f u) = r} =
      ∑ q, if g q = r then Fintype.card {u : U // f u = q} else 0 := by
  classical
  simp_rw [fiber_card_eq_sum]
  symm
  calc
    _ = ∑ q, ∑ u, if f u = q then (if g q = r then 1 else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro q _
      by_cases hq : g q = r <;> simp [hq]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      simp

/-- Two maps from the same finite source with identical destination counts
differ by a permutation of that source. This supplies the block decoders
in the terminal-component construction. -/
theorem exists_input_permutation_of_equal_fibers {U Q : Type} [Fintype U]
    [DecidableEq Q] (f g : U → Q)
    (hcount : ∀ q, Fintype.card {u : U // f u = q} =
      Fintype.card {u : U // g u = q}) :
    ∃ π : Equiv.Perm U, ∀ u, g (π u) = f u := by
  classical
  let e : ∀ q, {u : U // f u = q} ≃ {u : U // g u = q} :=
    fun q => Fintype.equivOfCardEq (hcount q)
  let π := (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv g))
  refine ⟨π, fun u => ?_⟩
  exact (e (f u) ⟨u, rfl⟩).property

end FSS23105365

-- From Solutions.FSS23105365_IntegerMargins
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

/-- Fibers partition the finite source set. -/
theorem sum_fiber_card {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) : (∑ y, Fintype.card {x : α // f x = y}) = Fintype.card α := by
  simpa only [Fintype.card_sigma] using Fintype.card_congr (Equiv.sigmaFiberEquiv f)

/-- The integer-matrix construction in E.4: if the total column demand is
`card α * m`, it can be allocated into rows of exactly `m` units each. -/
theorem exists_integer_matrix_with_margins {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq β] (m : ℕ) (b : β → ℕ)
    (hb : ∑ y, b y = Fintype.card α * m) :
    ∃ C : α → β → ℕ,
      (∀ x, ∑ y, C x y = m) ∧ (∀ y, ∑ x, C x y = b y) := by
  classical
  obtain ⟨f, hf⟩ := exists_map_with_fiber_counts (β := α × Fin m) b (by simpa using hb)
  let C : α → β → ℕ := fun x y => Fintype.card {j : Fin m // f (x, j) = y}
  refine ⟨C, fun x => ?_, fun y => ?_⟩
  · simpa [C] using sum_fiber_card (fun j : Fin m => f (x, j))
  · have h := Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun x (j : Fin m) => f (x, j) = y))
    simpa only [Fintype.card_sigma, hf, C] using h.symm

end FSS23105365

-- From Solutions.FSS23105365_BlockCountKernel
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

/-- Partition a one-step extension by its intermediate state. -/
def extensionFiberEquiv {E U Q : Type} (f : E → Q) (δ : Q → U → Q) (y : Q) :
    {z : E × U // δ (f z.1) z.2 = y} ≃
      (Σ x : Q, {e : E // f e = x} × {u : U // δ x u = y}) where
  toFun z := ⟨f z.val.1, ⟨⟨z.val.1, rfl⟩, ⟨z.val.2, z.property⟩⟩⟩
  invFun z := ⟨(z.2.1.val, z.2.2.val), by rw [z.2.1.property]; exact z.2.2.property⟩
  left_inv z := rfl
  right_inv z := by
    rcases z with ⟨x, ⟨e, he⟩, ⟨u, hu⟩⟩
    subst x
    rfl

theorem extension_fiber_card {E U Q : Type} [Fintype E] [Fintype U] [Fintype Q]
    [DecidableEq Q] (f : E → Q) (δ : Q → U → Q) (y : Q) :
    Fintype.card {z : E × U // δ (f z.1) z.2 = y} =
      ∑ x, Fintype.card {e : E // f e = x} * Fintype.card {u : U // δ x u = y} := by
  simpa only [Fintype.card_sigma, Fintype.card_prod] using
    Fintype.card_congr (extensionFiberEquiv f δ y)

def wordEnd {Q U : Type} (δ : Q → U → Q) {n : ℕ} (x : Q) (w : Fin n → U) : Q :=
  (List.ofFn w).foldl δ x

def wordCount {Q U : Type} [Fintype U] [DecidableEq Q]
    (δ : Q → U → Q) (n : ℕ) (x y : Q) : ℕ :=
  Fintype.card {w : Fin n → U // wordEnd δ x w = y}

theorem wordEnd_snoc {Q U : Type} (δ : Q → U → Q)
    {n : ℕ} (x : Q) (w : Fin n → U) (u : U) :
    wordEnd δ x (Fin.snoc w u) = δ (wordEnd δ x w) u := by
  unfold wordEnd
  rw [List.ofFn_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, List.foldl_concat]

theorem wordCount_succ {Q U : Type} [Fintype Q] [Fintype U] [DecidableEq Q]
    (δ : Q → U → Q) (n : ℕ) (x y : Q) :
    wordCount δ (n + 1) x y = ∑ z, wordCount δ n x z *
      Fintype.card {u : U // δ z u = y} := by
  classical
  let e : ((Fin n → U) × U) ≃ (Fin (n + 1) → U) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => U))
  have hc := Fintype.card_congr (e.subtypeEquiv
    (p := fun z => δ (wordEnd δ x z.1) z.2 = y)
    (q := fun w => wordEnd δ x w = y) (fun z => by
      change _ ↔ wordEnd δ x (Fin.snoc z.1 z.2) = y
      rw [wordEnd_snoc]))
  exact hc.symm.trans (extension_fiber_card (wordEnd δ x) δ y)

theorem wordCount_row_sum {Q U : Type} [Fintype Q] [Fintype U] [DecidableEq Q]
    (δ : Q → U → Q) (n : ℕ) (x : Q) :
    (∑ y, wordCount δ n x y) = (Fintype.card U) ^ n := by
  simpa only [wordCount, Fintype.card_fun, Fintype.card_fin] using sum_fiber_card (wordEnd δ x)

def uniformStepKernel {Q U : Type} [Fintype U] [DecidableEq Q]
    (δ : Q → U → Q) (x y : Q) : ℝ :=
  (Fintype.card {u : U // δ x u = y} : ℝ) / Fintype.card U

theorem uniformStepKernel_nonneg {Q U : Type} [Fintype U] [DecidableEq Q]
    (δ : Q → U → Q) (x y : Q) : 0 ≤ uniformStepKernel δ x y := by
  unfold uniformStepKernel
  positivity

theorem uniformStepKernel_row_sum {Q U : Type} [Fintype Q] [Fintype U]
    [Nonempty U] [DecidableEq Q] (δ : Q → U → Q) (x : Q) :
    (∑ y, uniformStepKernel δ x y) = 1 := by
  classical
  simp only [uniformStepKernel, ← Finset.sum_div, ← Nat.cast_sum, sum_fiber_card]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero (α := U))

/-- Normalized complete-word transition counts are exactly the iterates
of the uniform-letter kernel. This connects the analytic convergence result
to the integer counts used by the hidden automaton. -/
theorem wordCount_normalized {Q U : Type} [Fintype Q] [Fintype U]
    [Nonempty U] [DecidableEq Q] (δ : Q → U → Q) (n : ℕ) (x y : Q) :
    (wordCount δ n x y : ℝ) / (Fintype.card U : ℝ) ^ n =
      (kernelAdvance (uniformStepKernel δ))^[n] (fun z => if z = x then 1 else 0) y := by
  classical
  induction n generalizing y with
  | zero =>
    by_cases hxy : x = y
    · subst y; simp [wordCount, wordEnd]
    · have hyx : y ≠ x := Ne.symm hxy
      simp [wordCount, wordEnd, hxy, hyx]
  | succ n ih =>
    rw [wordCount_succ, Nat.cast_sum, pow_succ, Finset.sum_div,
      Function.iterate_succ_apply']
    unfold kernelAdvance
    apply Finset.sum_congr rfl
    intro z _
    rw [Nat.cast_mul, ← div_mul_div_comm, ih]
    rfl

end FSS23105365

-- From Solutions.FSS23105365_IntegerQuantile
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

/-- Number of ranks assigned to states strictly below `k`. -/
def countPrefix {q : ℕ} (a : Fin q → ℕ) (k : ℕ) : ℕ :=
  ∑ i, if i.val < k then a i else 0

@[simp] theorem countPrefix_zero {q : ℕ} (a : Fin q → ℕ) : countPrefix a 0 = 0 := by
  simp [countPrefix]

@[simp] theorem countPrefix_total {q : ℕ} (a : Fin q → ℕ) : countPrefix a q = ∑ i, a i := by
  simp [countPrefix]

theorem countPrefix_mono {q : ℕ} (a : Fin q → ℕ) : Monotone (countPrefix a) := by
  intro k l hkl
  apply Finset.sum_le_sum
  intro i _
  by_cases hik : i.val < k
  · simp [hik, hik.trans_le hkl]
  · simp [hik]

theorem countPrefix_le_total {q : ℕ} (a : Fin q → ℕ) (k : ℕ) :
    countPrefix a k ≤ ∑ i, a i := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs <;> omega

theorem countPrefix_succ {q : ℕ} (a : Fin q → ℕ) (i : Fin q) :
    countPrefix a (i.val + 1) = countPrefix a i.val + a i := by
  have ht : ∀ j : Fin q,
      (if j.val < i.val + 1 then a j else 0) =
        (if j.val < i.val then a j else 0) + (if j = i then a j else 0) := by
    intro j
    by_cases hji : j = i
    · subst j; simp
    · have hn : j.val ≠ i.val := fun h => hji (Fin.ext h)
      by_cases hj : j.val < i.val
      · simp [hj, show j.val < i.val + 1 by omega, hji]
      · simp [hj, show ¬j.val < i.val + 1 by omega, hji]
  unfold countPrefix
  simp_rw [ht]
  rw [Finset.sum_add_distrib]
  simp

theorem exists_count_threshold {q : ℕ} (a : Fin q → ℕ) (u : Fin (∑ i, a i)) :
    ∃ k : ℕ, u.val < countPrefix a k := ⟨q, by simp⟩

def countThreshold {q : ℕ} (a : Fin q → ℕ) (u : Fin (∑ i, a i)) : ℕ :=
  Nat.find (exists_count_threshold a u)

theorem countThreshold_pos {q : ℕ} (a : Fin q → ℕ) (u : Fin (∑ i, a i)) :
    0 < countThreshold a u := by
  have h := Nat.find_spec (exists_count_threshold a u)
  change u.val < countPrefix a (countThreshold a u) at h
  by_contra hn
  have hz : countThreshold a u = 0 := by omega
  simp [hz] at h

theorem countThreshold_le {q : ℕ} (a : Fin q → ℕ) (u : Fin (∑ i, a i)) :
    countThreshold a u ≤ q := Nat.find_min' _ (by simp)

/-- The common-rank inverse cumulative-count map. It skips zero-count
states automatically and uses every rank exactly once. -/
def integerQuantile {q : ℕ} (a : Fin q → ℕ) (u : Fin (∑ i, a i)) : Fin q :=
  ⟨countThreshold a u - 1, by
    have hpos := countThreshold_pos a u
    have hle := countThreshold_le a u
    omega⟩

theorem integerQuantile_bounds {q : ℕ} (a : Fin q → ℕ) (u : Fin (∑ i, a i)) :
    countPrefix a (integerQuantile a u).val ≤ u.val ∧
      u.val < countPrefix a ((integerQuantile a u).val + 1) := by
  have hp := countThreshold_pos a u
  have hlt : countThreshold a u - 1 < countThreshold a u := by omega
  have hlo := Nat.find_min (exists_count_threshold a u) hlt
  have hhi := Nat.find_spec (exists_count_threshold a u)
  change ¬u.val < countPrefix a (countThreshold a u - 1) at hlo
  change u.val < countPrefix a (countThreshold a u) at hhi
  constructor
  · exact Nat.le_of_not_gt hlo
  · change u.val < countPrefix a (countThreshold a u - 1 + 1)
    rwa [Nat.sub_add_cancel hp]

theorem integerQuantile_eq_iff {q : ℕ} (a : Fin q → ℕ)
    (u : Fin (∑ i, a i)) (i : Fin q) :
    integerQuantile a u = i ↔ countPrefix a i.val ≤ u.val ∧
      u.val < countPrefix a (i.val + 1) := by
  constructor
  · intro h; simpa only [h] using integerQuantile_bounds a u
  · rintro ⟨hlo, hhi⟩
    have hb := integerQuantile_bounds a u
    apply Fin.ext
    by_contra hn
    rcases lt_or_gt_of_ne hn with h | h
    · have hp := countPrefix_mono a (show (integerQuantile a u).val + 1 ≤ i.val by omega)
      omega
    · have hp := countPrefix_mono a (show i.val + 1 ≤ (integerQuantile a u).val by omega)
      omega

/-- The quantile's fiber is the consecutive interval of the specified
integer length, giving its cardinality without probabilistic assumptions. -/
def integerQuantileFiberEquiv {q : ℕ} (a : Fin q → ℕ) (i : Fin q) :
    {u : Fin (∑ j, a j) // integerQuantile a u = i} ≃ Fin (a i) where
  toFun u := ⟨u.val.val - countPrefix a i.val, by
    have hb := (integerQuantile_eq_iff a u.val i).mp u.property
    rw [countPrefix_succ] at hb
    omega⟩
  invFun j := ⟨⟨countPrefix a i.val + j.val, by
    have hp := countPrefix_le_total a (i.val + 1)
    rw [countPrefix_succ] at hp
    omega⟩, by
      apply (integerQuantile_eq_iff a _ i).mpr
      change countPrefix a i.val ≤ countPrefix a i.val + j.val ∧
        countPrefix a i.val + j.val < countPrefix a (i.val + 1)
      rw [countPrefix_succ]
      constructor <;> omega⟩
  left_inv u := by
    apply Subtype.ext
    apply Fin.ext
    have hb := (integerQuantile_eq_iff a u.val i).mp u.property
    simp only
    omega
  right_inv j := by
    apply Fin.ext
    simp

theorem integerQuantile_fiber_card {q : ℕ} (a : Fin q → ℕ) (i : Fin q) :
    Fintype.card {u : Fin (∑ j, a j) // integerQuantile a u = i} = a i := by
  simpa using Fintype.card_congr (integerQuantileFiberEquiv a i)

/-- Larger cumulative counts put the same rank at an earlier state. This
is the order-compatibility step in the terminal-component construction. -/
theorem integerQuantile_le_of_prefix_ge {q : ℕ} (a b : Fin q → ℕ)
    (u : Fin (∑ i, a i)) (v : Fin (∑ i, b i)) (huv : u.val = v.val)
    (hprefix : ∀ k, countPrefix b k ≤ countPrefix a k) :
    integerQuantile a u ≤ integerQuantile b v := by
  have ha := integerQuantile_bounds a u
  have hb := integerQuantile_bounds b v
  by_contra hn
  have hlt : (integerQuantile b v).val + 1 ≤ (integerQuantile a u).val := by
    change ¬(integerQuantile a u).val ≤ (integerQuantile b v).val at hn
    omega
  have hc := (hprefix ((integerQuantile b v).val + 1)).trans (countPrefix_mono a hlt)
  omega

end FSS23105365

-- From Solutions.FSS23105365_MonotoneBlockRealization
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

/-- All rows use the same source rank, so cumulative-count ordering can
couple their destinations monotonically. -/
def rowQuantile {q N : ℕ} (a : Fin q → Fin q → ℕ)
    (htotal : ∀ h, ∑ i, a h i = N) (h : Fin q) (u : Fin N) : Fin q :=
  integerQuantile (a h) ((finCongr (htotal h).symm) u)

theorem rowQuantile_fiber_card {q N : ℕ} (a : Fin q → Fin q → ℕ)
    (htotal : ∀ h, ∑ i, a h i = N) (h i : Fin q) :
    Fintype.card {u : Fin N // rowQuantile a htotal h u = i} = a h i := by
  have hc := Fintype.card_congr ((finCongr (htotal h).symm).subtypeEquiv
    (p := fun u => rowQuantile a htotal h u = i)
    (q := fun u => integerQuantile (a h) u = i) (fun _ => Iff.rfl))
  exact hc.trans (integerQuantile_fiber_card (a h) i)

theorem rowQuantile_monotone {q N : ℕ} (a : Fin q → Fin q → ℕ)
    (htotal : ∀ h, ∑ i, a h i = N)
    (horder : ∀ h k, h ≤ k → ∀ j, countPrefix (a k) j ≤ countPrefix (a h) j)
    (u : Fin N) : Monotone (fun h => rowQuantile a htotal h u) := by
  intro h k hhk
  exact integerQuantile_le_of_prefix_ge (a h) (a k) _ _ rfl (horder h k hhk)

/-- Any finite source of the common row size realizes the same counts,
using a single fixed ranking of the source for every hidden state. -/
def rankedTransition {q : ℕ} {U : Type} [Fintype U]
    (a : Fin q → Fin q → ℕ) (htotal : ∀ h, ∑ i, a h i = Fintype.card U)
    (h : Fin q) (u : U) : Fin q :=
  rowQuantile a htotal h (Fintype.equivFin U u)

theorem rankedTransition_fiber_card {q : ℕ} {U : Type} [Fintype U]
    (a : Fin q → Fin q → ℕ) (htotal : ∀ h, ∑ i, a h i = Fintype.card U)
    (h i : Fin q) :
    Fintype.card {u : U // rankedTransition a htotal h u = i} = a h i := by
  classical
  have hc := Fintype.card_congr ((Fintype.equivFin U).subtypeEquiv
    (p := fun u => rankedTransition a htotal h u = i)
    (q := fun u => rowQuantile a htotal h u = i) (fun _ => Iff.rfl))
  exact hc.trans (rowQuantile_fiber_card a htotal h i)

/-- Terminal-component construction from the integer counts: common-rank
sampling is monotone and aperiodic, and per-state input permutations make
the projected transition agree exactly with the original transition table.
Choosing counts with the required ordering remains a separate obligation. -/
theorem monotone_block_realization {q : ℕ} {U R : Type} [Fintype U] [DecidableEq R]
    (a : Fin q → Fin q → ℕ) (htotal : ∀ h, ∑ i, a h i = Fintype.card U)
    (horder : ∀ h k, h ≤ k → ∀ j, countPrefix (a k) j ≤ countPrefix (a h) j)
    (φ : Fin q → R) (original : Fin q → U → R)
    (hmargin : ∀ h r, (∑ i, if φ i = r then a h i else 0) =
      Fintype.card {u : U // original h u = r}) :
    ∃ τ : Fin q → U → Fin q, ∃ π : Fin q → Equiv.Perm U,
      (∀ h i, Fintype.card {u : U // τ h u = i} = a h i) ∧
      (∀ u, Monotone (fun h => τ h u)) ∧ AperiodicTransitions τ ∧
      ∀ h u, φ (τ h u) = original h (π h u) := by
  classical
  let τ := rankedTransition a htotal
  have hcounts : ∀ h i, Fintype.card {u : U // τ h u = i} = a h i :=
    rankedTransition_fiber_card a htotal
  have hmono : ∀ u, Monotone (fun h => τ h u) :=
    fun u => rowQuantile_monotone a htotal horder (Fintype.equivFin U u)
  have hprojcounts : ∀ h r, Fintype.card {u : U // φ (τ h u) = r} =
      Fintype.card {u : U // original h u = r} := by
    intro h r
    rw [fiber_card_comp]
    simp_rw [hcounts]
    exact hmargin h r
  choose π hπ using fun h => exists_input_permutation_of_equal_fibers
    (fun u => φ (τ h u)) (original h) (hprojcounts h)
  exact ⟨τ, π, hcounts, hmono, monotone_transitions_aperiodic τ hmono,
    fun h u => (hπ h u).symm⟩

end FSS23105365

-- From Solutions.FSS23105365_TerminalSplitCounts
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

/-- Complementary real shares of an integer split exactly into a floor
and a ceiling. No mass is lost at a rounding boundary. -/
theorem complementary_floor_ceil (N : ℕ) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hsum : x + y = N) :
    Nat.floor x + Nat.ceil y = N := by
  have hfl := Nat.floor_le hx
  have hfh := Nat.lt_floor_add_one x
  have hcl := Nat.le_ceil y
  have hch := Nat.ceil_lt_add_one hy
  have hlo : N < Nat.floor x + Nat.ceil y + 1 := by
    have h : (N : ℝ) < (Nat.floor x : ℝ) + (Nat.ceil y : ℝ) + 1 := by linarith
    exact_mod_cast h
  have hhi : Nat.floor x + Nat.ceil y < N + 1 := by
    have h : (Nat.floor x : ℝ) + (Nat.ceil y : ℝ) < (N : ℝ) + 1 := by linarith
    exact_mod_cast h
  omega

/-- The two consecutive copies use the order minus states, then plus states. -/
def splitProjection (k : ℕ) : Fin (k + k) → Fin k := Fin.addCases id id

@[simp] theorem splitProjection_left (k : ℕ) (i : Fin k) :
    splitProjection k (Fin.castAdd k i) = i := by
  simp only [splitProjection, Fin.addCases_left, id_eq]

@[simp] theorem splitProjection_right (k : ℕ) (i : Fin k) :
    splitProjection k (Fin.natAdd k i) = i := by
  simp only [splitProjection, Fin.addCases_right, id_eq]

def splitWeight (k : ℕ) (h : Fin (k + k)) : ℝ :=
  ((h.val : ℝ) + 1) / ((k : ℝ) + k + 1)

theorem splitWeight_pos (k : ℕ) (h : Fin (k + k)) : 0 < splitWeight k h := by
  unfold splitWeight
  positivity

theorem splitWeight_lt_one (k : ℕ) (h : Fin (k + k)) : splitWeight k h < 1 := by
  unfold splitWeight
  apply (div_lt_one (by positivity : (0 : ℝ) < k + k + 1)).mpr
  have hh : (h.val : ℝ) < (k : ℝ) + k := by exact_mod_cast h.isLt
  linarith

theorem splitWeight_strictMono (k : ℕ) : StrictMono (splitWeight k) := by
  intro h l hhl
  unfold splitWeight
  apply (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < k + k + 1)).mpr
  have hh : (h.val : ℝ) < l.val := by exact_mod_cast hhl
  linarith

def splitLower {k : ℕ} (N : Fin k → Fin k → ℕ) (h : Fin (k + k)) (i : Fin k) : ℕ :=
  Nat.floor ((1 - splitWeight k h) * N (splitProjection k h) i)

def splitUpper {k : ℕ} (N : Fin k → Fin k → ℕ) (h : Fin (k + k)) (i : Fin k) : ℕ :=
  Nat.ceil (splitWeight k h * N (splitProjection k h) i)

def terminalSplitCounts {k : ℕ} (N : Fin k → Fin k → ℕ)
    (h : Fin (k + k)) : Fin (k + k) → ℕ :=
  Fin.append (splitLower N h) (splitUpper N h)

theorem split_counts_sum {k : ℕ} (N : Fin k → Fin k → ℕ)
    (h : Fin (k + k)) (i : Fin k) :
    splitLower N h i + splitUpper N h i = N (splitProjection k h) i := by
  apply complementary_floor_ceil
  · exact mul_nonneg (sub_nonneg.mpr (splitWeight_lt_one k h).le) (Nat.cast_nonneg _)
  · exact mul_nonneg (splitWeight_pos k h).le (Nat.cast_nonneg _)
  · ring

theorem terminalSplitCounts_row_sum {k : ℕ} (N : Fin k → Fin k → ℕ)
    (h : Fin (k + k)) :
    (∑ i, terminalSplitCounts N h i) = ∑ i, N (splitProjection k h) i := by
  rw [Fin.sum_univ_add]
  simp only [terminalSplitCounts, Fin.append_left, Fin.append_right]
  rw [← Finset.sum_add_distrib]
  simp_rw [split_counts_sum]

theorem terminalSplitCounts_projected_margin {k : ℕ} (N : Fin k → Fin k → ℕ)
    (h : Fin (k + k)) (j : Fin k) :
    (∑ i, if splitProjection k i = j then terminalSplitCounts N h i else 0) =
      N (splitProjection k h) j := by
  rw [Fin.sum_univ_add]
  simp only [splitProjection_left, splitProjection_right, terminalSplitCounts,
    Fin.append_left, Fin.append_right]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact split_counts_sum N h j

theorem prefix_add_suffix {q : ℕ} (a : Fin q → ℕ) (j : ℕ) :
    countPrefix a j + (∑ i, if j ≤ i.val then a i else 0) = ∑ i, a i := by
  rw [countPrefix, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < j
  · simp [hi, show ¬j ≤ i.val by omega]
  · simp [hi, show j ≤ i.val by omega]

/-- Lower entries decrease and upper entries increase between two rows.
Equal total mass then gives the required cumulative-count ordering at all
cuts, including cuts inside the upper half. -/
theorem split_prefix_order {k : ℕ} (l₁ l₂ u₁ u₂ : Fin k → ℕ)
    (hl : ∀ i, l₂ i ≤ l₁ i) (hu : ∀ i, u₁ i ≤ u₂ i)
    (htotal : (∑ i, Fin.append l₁ u₁ i) = ∑ i, Fin.append l₂ u₂ i) (j : ℕ) :
    countPrefix (Fin.append l₂ u₂) j ≤ countPrefix (Fin.append l₁ u₁) j := by
  by_cases hj : j ≤ k
  · apply Finset.sum_le_sum
    intro i _
    refine Fin.addCases (fun t => ?_) (fun t => ?_) i
    · simp only [Fin.val_castAdd, Fin.append_left]
      split_ifs <;> simp [hl]
    · simp only [Fin.val_natAdd, Fin.append_right]
      have ht : ¬k + t.val < j := by omega
      simp [ht]
  · have hs : (∑ i : Fin (k + k), if j ≤ i.val then Fin.append l₁ u₁ i else 0) ≤
        ∑ i : Fin (k + k), if j ≤ i.val then Fin.append l₂ u₂ i else 0 := by
      apply Finset.sum_le_sum
      intro i _
      refine Fin.addCases (fun t => ?_) (fun t => ?_) i
      · simp only [Fin.val_castAdd, Fin.append_left]
        have ht : ¬j ≤ t.val := by have := t.isLt; omega
        simp [ht]
      · simp only [Fin.val_natAdd, Fin.append_right]
        split_ifs <;> simp [hu]
    have h₁ := prefix_add_suffix (Fin.append l₁ u₁) j
    have h₂ := prefix_add_suffix (Fin.append l₂ u₂) j
    omega

end FSS23105365

-- From Solutions.FSS23105365_TerminalCountOrdering
set_option autoImplicit false
namespace FSS23105365
open Filter
open scoped BigOperators Topology

/-- Common positive row limits force entrywise ordering of the split
counts. Proving the stronger entrywise inequalities lets floor/ceil
monotonicity handle rounding without an asymptotic error placeholder. -/
theorem eventually_split_entry_order {k : ℕ}
    (N : ℕ → Fin k → Fin k → ℕ) (scale : ℕ → ℝ) (hscale : ∀ c, 0 < scale c)
    (π : Fin k → ℝ) (hπ : ∀ i, 0 < π i)
    (hconv : ∀ x i, Tendsto (fun c => (N c x i : ℝ) / scale c) atTop (𝓝 (π i)))
    (h l : Fin (k + k)) (hhl : h < l) (i : Fin k) :
    ∀ᶠ c in atTop, splitLower (N c) l i ≤ splitLower (N c) h i ∧
      splitUpper (N c) h i ≤ splitUpper (N c) l i := by
  have hw := splitWeight_strictMono k hhl
  have hlow : (1 - splitWeight k l) * π i < (1 - splitWeight k h) * π i :=
    mul_lt_mul_of_pos_right (by linarith) (hπ i)
  have hupp : splitWeight k h * π i < splitWeight k l * π i :=
    mul_lt_mul_of_pos_right hw (hπ i)
  have he₁ := ((hconv (splitProjection k l) i).const_mul (1 - splitWeight k l)).eventually_lt
    ((hconv (splitProjection k h) i).const_mul (1 - splitWeight k h)) hlow
  have he₂ := ((hconv (splitProjection k h) i).const_mul (splitWeight k h)).eventually_lt
    ((hconv (splitProjection k l) i).const_mul (splitWeight k l)) hupp
  filter_upwards [he₁, he₂] with c hc₁ hc₂
  rw [← mul_div_assoc, ← mul_div_assoc] at hc₁ hc₂
  have hl := (div_lt_div_iff_of_pos_right (hscale c)).mp hc₁
  have hu := (div_lt_div_iff_of_pos_right (hscale c)).mp hc₂
  exact ⟨Nat.floor_mono hl.le, Nat.ceil_mono hu.le⟩

/-- One finite threshold makes every pair of hidden states compatible at
every prefix. The common-limit assumption is explicit; its Markov-chain
derivation is not treated as an unproved assumption or a completed result here. -/
theorem eventually_terminal_prefix_order {k : ℕ}
    (N : ℕ → Fin k → Fin k → ℕ) (scale : ℕ → ℝ) (hscale : ∀ c, 0 < scale c)
    (π : Fin k → ℝ) (hπ : ∀ i, 0 < π i)
    (hconv : ∀ x i, Tendsto (fun c => (N c x i : ℝ) / scale c) atTop (𝓝 (π i)))
    (hrows : ∀ c x y, (∑ i, N c x i) = ∑ i, N c y i) :
    ∀ᶠ c in atTop, ∀ h l : Fin (k + k), h ≤ l → ∀ j,
      countPrefix (terminalSplitCounts (N c) l) j ≤
        countPrefix (terminalSplitCounts (N c) h) j := by
  have he : ∀ h l : Fin (k + k), ∀ i : Fin k, ∀ᶠ c in atTop,
      h < l → splitLower (N c) l i ≤ splitLower (N c) h i ∧
        splitUpper (N c) h i ≤ splitUpper (N c) l i := by
    intro h l i
    by_cases hhl : h < l
    · exact (eventually_split_entry_order N scale hscale π hπ hconv h l hhl i).mono
        (fun c hc _ => hc)
    · exact Filter.Eventually.of_forall (fun _ hc => (hhl hc).elim)
  have hall : ∀ᶠ c in atTop, ∀ h l : Fin (k + k), ∀ i : Fin k,
      h < l → splitLower (N c) l i ≤ splitLower (N c) h i ∧
        splitUpper (N c) h i ≤ splitUpper (N c) l i := by
    simpa only [Filter.eventually_all] using he
  filter_upwards [hall] with c hc
  intro h l hhl j
  rcases lt_or_eq_of_le hhl with hlt | rfl
  · apply split_prefix_order
    · exact fun i => (hc h l i hlt).1
    · exact fun i => (hc h l i hlt).2
    · change (∑ i, terminalSplitCounts (N c) h i) = ∑ i, terminalSplitCounts (N c) l i
      rw [terminalSplitCounts_row_sum, terminalSplitCounts_row_sum, hrows]
  · exact le_rfl

theorem exists_terminal_order_threshold {k : ℕ}
    (N : ℕ → Fin k → Fin k → ℕ) (scale : ℕ → ℝ) (hscale : ∀ c, 0 < scale c)
    (π : Fin k → ℝ) (hπ : ∀ i, 0 < π i)
    (hconv : ∀ x i, Tendsto (fun c => (N c x i : ℝ) / scale c) atTop (𝓝 (π i)))
    (hrows : ∀ c x y, (∑ i, N c x i) = ∑ i, N c y i) :
    ∃ c₀ : ℕ, 0 < c₀ ∧ ∀ c ≥ c₀, ∀ h l : Fin (k + k), h ≤ l → ∀ j,
      countPrefix (terminalSplitCounts (N c) l) j ≤
        countPrefix (terminalSplitCounts (N c) h) j := by
  obtain ⟨c₀, hc₀⟩ := Filter.eventually_atTop.mp
    (eventually_terminal_prefix_order N scale hscale π hπ hconv hrows)
  exact ⟨c₀ + 1, by omega, fun c hc => hc₀ c (by omega)⟩

/-- Once the terminal counts satisfy prefix ordering, the two-copy
construction has the exact original block-transition law and an aperiodic
hidden transition system. -/
theorem terminal_block_model_of_order {k : ℕ} {U : Type} [Fintype U]
    (N : Fin k → Fin k → ℕ) (original : Fin k → U → Fin k)
    (hcounts : ∀ x y, Fintype.card {u : U // original x u = y} = N x y)
    (hrows : ∀ x, ∑ y, N x y = Fintype.card U)
    (horder : ∀ h l : Fin (k + k), h ≤ l → ∀ j,
      countPrefix (terminalSplitCounts N l) j ≤ countPrefix (terminalSplitCounts N h) j) :
    ∃ τ : Fin (k + k) → U → Fin (k + k),
      ∃ decode : Fin (k + k) → Equiv.Perm U,
        Function.Surjective (splitProjection k) ∧
        (∀ h u, splitProjection k (τ h u) = original (splitProjection k h) (decode h u)) ∧
        AperiodicTransitions τ := by
  obtain ⟨τ, decode, _, _, ha, hd⟩ := monotone_block_realization (terminalSplitCounts N)
    (fun h => (terminalSplitCounts_row_sum N h).trans (hrows _)) horder
    (splitProjection k) (fun h => original (splitProjection k h)) (fun h y => by
      rw [terminalSplitCounts_projected_margin, hcounts])
  exact ⟨τ, decode, fun x => ⟨Fin.castAdd k x, splitProjection_left k x⟩, hd, ha⟩

end FSS23105365

-- From Solutions.FSS23105365_PositiveTransitionHiddenModel
set_option autoImplicit false
namespace FSS23105365
open Filter
open scoped BigOperators Topology

/-- Complete terminal-component construction in Lemma 3.5. If one block
can take every state to every state, all sufficiently large block lengths
have a two-copy hidden representation with an aperiodic transition monoid.
The threshold works for every later length, allowing a common choice across
all components in the final construction. -/
theorem positive_transition_hidden_model {k : ℕ} (hk : 0 < k) {U : Type}
    [Fintype U] [Nonempty U] (δ : Fin k → U → Fin k)
    (hfull : ∀ x y, ∃ u, δ x u = y) :
    ∃ c₀ : ℕ, 0 < c₀ ∧ ∀ c ≥ c₀,
      ∃ τ : Fin (k + k) → (Fin c → U) → Fin (k + k),
      ∃ decode : Fin (k + k) → Equiv.Perm (Fin c → U),
        Function.Surjective (splitProjection k) ∧
        (∀ h u, splitProjection k (τ h u) =
          wordEnd δ (splitProjection k h) (decode h u)) ∧ AperiodicTransitions τ := by
  classical
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hP : ∀ x y, 0 < uniformStepKernel δ x y := by
    intro x y
    apply div_pos
    · have hc : 0 < Fintype.card {u : U // δ x u = y} := by
        apply Fintype.card_pos_iff.mpr
        obtain ⟨u, hu⟩ := hfull x y
        exact ⟨⟨u, hu⟩⟩
      exact_mod_cast hc
    · exact_mod_cast Fintype.card_pos (α := U)
  obtain ⟨π, hπpos, _, hπ⟩ := positive_kernel_common_limit (uniformStepKernel δ) hP
    (uniformStepKernel_row_sum δ)
  have hconv : ∀ x y : Fin k,
      Tendsto (fun c : ℕ => (wordCount δ c x y : ℝ) / (Fintype.card U : ℝ) ^ c)
        atTop (𝓝 (π y)) := by
    intro x y
    simp_rw [wordCount_normalized]
    apply hπ
    · intro z; split_ifs <;> norm_num
    · simp
  obtain ⟨c₀, hc₀, horder⟩ := exists_terminal_order_threshold
    (fun c => wordCount δ c) (fun c => (Fintype.card U : ℝ) ^ c)
    (fun c => pow_pos (by exact_mod_cast Fintype.card_pos (α := U)) c) π hπpos hconv
    (fun c x y => (wordCount_row_sum δ c x).trans (wordCount_row_sum δ c y).symm)
  refine ⟨c₀, hc₀, fun c hc => ?_⟩
  exact terminal_block_model_of_order (wordCount δ c) (fun x => wordEnd δ x)
    (fun _ _ => rfl) (fun x => by
      simpa only [Fintype.card_fun, Fintype.card_fin] using wordCount_row_sum δ c x)
    (horder c hc)

end FSS23105365

-- From Solutions.FSS23105365_FiniteMonoidPower
set_option autoImplicit false
namespace FSS23105365

/-- Equality of two powers gives an eventual period of the power sequence. -/
theorem powers_eventually_periodic {M : Type} [Monoid M] (a : M)
    (i p : ℕ) (h : a ^ (i + p) = a ^ i) :
    ∀ t : ℕ, i ≤ t → ∀ k : ℕ, a ^ (t + p * k) = a ^ t := by
  intro t ht k
  have hstep : a ^ (t + p) = a ^ t := by
    calc
      _ = a ^ (i + p + (t - i)) := by congr 1; omega
      _ = a ^ (i + p) * a ^ (t - i) := pow_add _ _ _
      _ = a ^ i * a ^ (t - i) := by rw [h]
      _ = a ^ t := by rw [← pow_add, Nat.add_sub_of_le ht]
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      _ = a ^ (t + p * k) * a ^ p := by rw [Nat.mul_succ, ← pow_add, Nat.add_assoc]
      _ = a ^ t * a ^ p := by rw [ih]
      _ = a ^ t := by rw [← pow_add, hstep]

/-- Every element of a finite monoid has a positive idempotent power.
This is the finite-algebra step behind the idempotent Boolean support
matrix in Lemma 3.5. It requires no cancellativity or group structure. -/
theorem exists_positive_idempotent_power {M : Type} [Monoid M] [Fintype M] (a : M) :
    ∃ n : ℕ, 0 < n ∧ a ^ n * a ^ n = a ^ n := by
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Fintype.card M + 1) => a ^ i.val) (by simp)
  have hp : ∃ i j : ℕ, i < j ∧ a ^ i = a ^ j := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ⟨i.val, j.val, h, heq⟩
    · exact ⟨j.val, i.val, h, heq.symm⟩
  obtain ⟨i, j, hij, heq⟩ := hp
  let p := j - i
  have hp : 0 < p := Nat.sub_pos_of_lt hij
  have hper : a ^ (i + p) = a ^ i := by
    simpa only [p, Nat.add_sub_of_le hij.le] using heq.symm
  let n := p * (i + 1)
  have hn : 0 < n := Nat.mul_pos hp (by omega)
  have hin : i ≤ n := by
    have hh : i + 1 ≤ p * (i + 1) := by
      exact (Nat.one_mul (i + 1)).symm.le.trans
        (Nat.mul_le_mul_right (i + 1) (show 1 ≤ p from hp))
    exact (Nat.le_succ i).trans hh
  refine ⟨n, hn, ?_⟩
  rw [← pow_add]
  exact powers_eventually_periodic a i p hper n hin (i + 1)

end FSS23105365

-- From Solutions.FSS23105365_IdempotentSupport
set_option autoImplicit false
namespace FSS23105365

/-- Binary relations with multiplication in walk order. The type synonym
keeps this monoid structure separate from other structures on sets. -/
def WalkRelation (Q : Type) := SetRel Q Q

instance {Q : Type} : Monoid (WalkRelation Q) where
  mul R S := SetRel.comp R S
  one := SetRel.id
  mul_assoc := SetRel.comp_assoc
  one_mul := SetRel.id_comp
  mul_one := SetRel.comp_id

instance {Q : Type} [Fintype Q] : Fintype (WalkRelation Q) := by
  classical
  exact inferInstanceAs (Fintype (Set (Q × Q)))

def WalkRelation.holds {Q : Type} (R : WalkRelation Q) (x y : Q) : Prop :=
  R (x, y)

@[simp] theorem walkRelation_one {Q : Type} (x y : Q) :
    (1 : WalkRelation Q).holds x y ↔ x = y := Iff.rfl

@[simp] theorem walkRelation_mul {Q : Type} (R S : WalkRelation Q) (x y : Q) :
    (R * S).holds x y ↔ ∃ z, R.holds x z ∧ S.holds z y := Iff.rfl

def letterSupport {Q U : Type} (δ : Q → U → Q) : WalkRelation Q :=
  {xy | ∃ u, δ xy.1 u = xy.2}

/-- Support of exactly `n` transitions, as opposed to arbitrary reachability. -/
def blockSupport {Q U : Type} (δ : Q → U → Q) (n : ℕ) (x y : Q) : Prop :=
  ∃ w : Fin n → U, (List.ofFn w).foldl δ x = y

theorem support_power_iff {Q U : Type} (δ : Q → U → Q) (n : ℕ) (x y : Q) :
    (letterSupport δ ^ n).holds x y ↔ blockSupport δ n x y := by
  induction n generalizing x y with
  | zero =>
    simp only [pow_zero, walkRelation_one, blockSupport, List.ofFn_zero, List.foldl_nil]
    constructor
    · intro h; exact ⟨Fin.elim0, h⟩
    · rintro ⟨w, h⟩; exact h
  | succ n ih =>
    rw [pow_succ', walkRelation_mul]
    constructor
    · rintro ⟨z, ⟨u, hu⟩, hz⟩
      obtain ⟨w, hw⟩ := (ih z y).mp hz
      refine ⟨Fin.cons u w, ?_⟩
      simpa only [List.ofFn_cons, List.foldl_cons, hu] using hw
    · rintro ⟨w, hw⟩
      refine ⟨δ x (w 0), ⟨w 0, rfl⟩, (ih _ _).mpr ⟨Fin.tail w, ?_⟩⟩
      rw [List.ofFn_succ, List.foldl_cons] at hw
      simpa only [Fin.tail_def] using hw

/-- The idempotent Boolean support power used to define the component
graph in Lemma 3.5 exists for every finite transition system. -/
theorem exists_idempotent_block_support {Q U : Type} [Fintype Q]
    (δ : Q → U → Q) :
    ∃ a : ℕ, 0 < a ∧ ∀ x y,
      (∃ z, blockSupport δ a x z ∧ blockSupport δ a z y) ↔ blockSupport δ a x y := by
  obtain ⟨a, ha, he⟩ := exists_positive_idempotent_power (letterSupport δ)
  refine ⟨a, ha, fun x y => ?_⟩
  simp_rw [← support_power_iff]
  rw [← walkRelation_mul, he]

/-- Natural block-transition counts are positive precisely on their support. -/
theorem block_count_pos_iff {Q : Type} [DecidableEq Q] (δ : Q → Bool → Q)
    (n : ℕ) (x y : Q) :
    0 < Fintype.card {w : Bits n // (List.ofFn w).foldl δ x = y} ↔
      blockSupport δ n x y := by
  rw [Fintype.card_pos_iff]
  exact ⟨fun ⟨w⟩ => ⟨w.val, w.property⟩, fun ⟨w, hw⟩ => ⟨⟨w, hw⟩⟩⟩

end FSS23105365

-- From Solutions.FSS23105365_ComponentAperiodicity
set_option autoImplicit false
namespace FSS23105365
open Function

/-- Component labels can only move forward in the condensation order. -/
theorem component_le_foldl {H U C : Type} [Preorder C]
    (τ : H → U → H) (component : H → C)
    (hforward : ∀ h u, component h ≤ component (τ h u))
    (w : List U) (h : H) : component h ≤ component (w.foldl τ h) := by
  induction w generalizing h with
  | nil => exact le_rfl
  | cons u w ih => exact (hforward h u).trans (ih (τ h u))

/-- If a forward walk ends in its starting component, its first step did
not leave that component. -/
theorem component_first_of_return {H U C : Type} [PartialOrder C]
    (τ : H → U → H) (component : H → C)
    (hforward : ∀ h u, component h ≤ component (τ h u))
    (u : U) (w : List U) (h : H)
    (hreturn : component ((u :: w).foldl τ h) = component h) :
    component (τ h u) = component h := by
  apply le_antisymm _ (hforward h u)
  have hh := component_le_foldl τ component hforward w (τ h u)
  exact hh.trans_eq hreturn

/-- A nonempty word has at most one source whose image stays within a
transient component, provided each letter has that property. -/
theorem unique_internal_source_word {H U C : Type} [PartialOrder C]
    (τ : H → U → H) (component : H → C)
    (hforward : ∀ h u, component h ≤ component (τ h u)) (c : C)
    (hunique : ∀ u x y, component x = c → component y = c →
      component (τ x u) = c → component (τ y u) = c → x = y)
    (w : List U) (hw : w ≠ []) (x y : H)
    (hx : component x = c) (hy : component y = c)
    (hfx : component (w.foldl τ x) = c) (hfy : component (w.foldl τ y) = c) : x = y := by
  cases w with
  | nil => exact (hw rfl).elim
  | cons u w =>
    apply hunique u x y hx hy
    · exact (component_first_of_return τ component hforward u w x
        (hfx.trans hx.symm)).trans hx
    · exact (component_first_of_return τ component hforward u w y
        (hfy.trans hy.symm)).trans hy

/-- A positive closed orbit cannot move forward to a different component. -/
theorem component_eq_of_periodic {H C : Type} [PartialOrder C]
    (g : H → H) (component : H → C)
    (hforward : ∀ x, component x ≤ component (g x))
    (x : H) (n : ℕ) (hn : 0 < n) (hx : g^[n] x = x) :
    component (g x) = component x := by
  have hm : Monotone (fun k : ℕ => component (g^[k] x)) :=
    monotone_nat_of_le_succ (fun k => by
      simpa only [iterate_succ_apply'] using hforward (g^[k] x))
  apply le_antisymm _ (hforward x)
  simpa only [iterate_one, hx] using hm (show 1 ≤ n by omega)

/-- A closed terminal component equipped with a linear order and monotone
letter maps supplies the terminal hypothesis of `component_aperiodicity`. -/
theorem ordered_closed_component_cycle_free {H U : Type} (τ : H → U → H)
    (P : H → Prop) [LinearOrder {x : H // P x}]
    (hclosed : ∀ x u, P x → P (τ x u))
    (hmono : ∀ u, Monotone (fun x : {x : H // P x} =>
      (⟨τ x.val u, hclosed x.val u x.property⟩ : {x : H // P x})))
    (w : List U) (x : H) (hx : P x) (n : ℕ) (hn : 0 < n)
    (hperiod : (fun h => w.foldl τ h)^[n] x = x) : w.foldl τ x = x := by
  let σ : {x : H // P x} → U → {x : H // P x} :=
    fun x u => ⟨τ x.val u, hclosed x.val u x.property⟩
  have hfold : ∀ (ws : List U) (y : {x : H // P x}),
      (ws.foldl σ y).val = ws.foldl τ y.val := by
    intro ws
    induction ws with
    | nil => intro y; rfl
    | cons u ws ih => intro y; exact ih (σ y u)
  have hm : ∀ ws : List U, Monotone (fun y => ws.foldl σ y) := by
    intro ws
    induction ws with
    | nil => exact monotone_id
    | cons u w ih => exact ih.comp (hmono u)
  have hsc : Semiconj (fun y : {x : H // P x} => y.val)
      (fun y => w.foldl σ y) (fun y => w.foldl τ y) := hfold w
  have hp : (fun y => w.foldl σ y)^[n] ⟨x, hx⟩ = ⟨x, hx⟩ := by
    apply Subtype.ext
    exact (hsc.iterate_right n ⟨x, hx⟩).trans hperiod
  have hf := monotone_no_nontrivial_cycle (fun y => w.foldl σ y) (hm w) ⟨x, hx⟩ n hn hp
  exact (hfold w ⟨x, hx⟩).symm.trans (congrArg Subtype.val hf)

/-- Component-level criterion used at the end of Lemma 3.5. Terminal
components supply a cycle-free word map, while transient components have
at most one internal source per letter. -/
theorem component_aperiodicity {H U C : Type} [Fintype H] [PartialOrder C]
    (τ : H → U → H) (component : H → C) (terminal : C → Prop)
    (hforward : ∀ h u, component h ≤ component (τ h u))
    (hterminal : ∀ c, terminal c → ∀ w : List U, ∀ x : H,
      component x = c → ∀ n : ℕ, 0 < n →
        (fun h => w.foldl τ h)^[n] x = x → w.foldl τ x = x)
    (htransient : ∀ c, ¬terminal c → ∀ u x y,
      component x = c → component y = c →
        component (τ x u) = c → component (τ y u) = c → x = y) :
    AperiodicTransitions τ := by
  classical
  apply (aperiodicTransitions_iff_no_cycles τ).mpr
  intro w x n hn hx
  by_cases ht : terminal (component x)
  · exact hterminal (component x) ht w x rfl n hn hx
  · by_cases hw : w = []
    · simp [hw]
    · let g : H → H := fun h => w.foldl τ h
      have hg : ∀ h, component h ≤ component (g h) :=
        component_le_foldl τ component hforward w
      have hcx : component (g x) = component x :=
        component_eq_of_periodic g component hg x n hn hx
      have hp : IsPeriodicPt g n x := hx
      have hcg : component (g (g x)) = component x :=
        (component_eq_of_periodic g component hg (g x) n hn hp.apply).trans hcx
      exact (unique_internal_source_word τ component hforward (component x)
        (htransient _ ht) w hw x (g x) rfl hcx hcx hcg).symm

end FSS23105365

-- From Solutions.FSS23105365_TransientBlockAllocation
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

/-- The transient-component allocation in Lemma 3.5: if the total number
of internal transitions fits in one alphabet, state-dependent permutations
can make their input sets disjoint. The proof also covers zero counts. -/
theorem exists_permutations_with_disjoint_internal_inputs {Q U : Type}
    [Fintype Q] [Fintype U] (P : Q → U → Prop) [∀ q, DecidablePred (P q)]
    (hsize : (∑ q, Fintype.card {u : U // P q u}) ≤ Fintype.card U) :
    ∃ π : Q → Equiv.Perm U, ∀ q r u, P q (π q u) → P r (π r u) → q = r := by
  classical
  let E := (Σ q : Q, {u : U // P q u})
  have hcard : Fintype.card E ≤ Fintype.card U := by simpa [E] using hsize
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  have hex : ∀ q : Q, ∃ π : Equiv.Perm U, ∀ w : {u : U // P q u},
      π (e ⟨q, w⟩) = w.val := by
    intro q
    exact Equiv.Perm.exists_extending_pair (fun w : {u : U // P q u} => e ⟨q, w⟩)
      Subtype.val (fun _ _ hh => by
        have he := e.injective hh
        exact (Sigma.mk.inj_iff.mp he).2 |> eq_of_heq) Subtype.val_injective
  choose π hπ using hex
  refine ⟨π, fun q r u hq hr => ?_⟩
  let wq : {v : U // P q v} := ⟨π q u, hq⟩
  let wr : {v : U // P r v} := ⟨π r u, hr⟩
  have hq' : e ⟨q, wq⟩ = u := (π q).injective (hπ q wq)
  have hr' : e ⟨r, wr⟩ = u := (π r).injective (hπ r wr)
  exact congrArg Sigma.fst (e.injective (hq'.trans hr'.symm))

/-- Relabeling the fair block inputs preserves every projected destination
count, not just the total probability of remaining inside a component. -/
theorem input_permutation_preserves_fibers {U Q : Type} [Fintype U] [DecidableEq Q]
    (π : Equiv.Perm U) (f : U → Q) (q : Q) :
    Fintype.card {u : U // f (π u) = q} = Fintype.card {u : U // f u = q} := by
  exact Fintype.card_congr (π.subtypeEquiv (fun _ => Iff.rfl))

end FSS23105365

-- From Solutions.FSS23105365_TransientMassDecay
set_option autoImplicit false
namespace FSS23105365
open Filter
open scoped BigOperators Topology

/-- Surviving words are exactly an internal first letter followed by a
surviving suffix. The forward component order excludes leaving and returning. -/
def survivingWordConsEquiv {Q U C : Type} [PartialOrder C]
    (δ : Q → U → Q) (component : Q → C)
    (hforward : ∀ x u, component x ≤ component (δ x u))
    (c : C) (x : Q) (hx : component x = c) (n : ℕ) :
    {w : Fin (n + 1) → U // component (wordEnd δ x w) = c} ≃
      (Σ u : {u : U // component (δ x u) = c},
        {w : Fin n → U // component (wordEnd δ (δ x u.val) w) = c}) where
  toFun w := ⟨⟨w.val 0, by
    have hr : component ((w.val 0 :: List.ofFn (Fin.tail w.val)).foldl δ x) =
        component x := by
      simpa only [wordEnd, List.ofFn_succ, Fin.tail_def] using
        w.property.trans hx.symm
    exact (component_first_of_return δ component hforward _ _ x hr).trans hx⟩,
    ⟨Fin.tail w.val, by
      have hh := w.property
      unfold wordEnd at hh ⊢
      rw [List.ofFn_succ, List.foldl_cons] at hh
      exact hh⟩⟩
  invFun z := ⟨Fin.cons z.1.val z.2.val, by
    simpa only [wordEnd, List.ofFn_cons, List.foldl_cons] using z.2.property⟩
  left_inv w := by
    apply Subtype.ext
    exact Fin.cons_self_tail w.val
  right_inv z := by
    rcases z with ⟨⟨u, hu⟩, ⟨w, hw⟩⟩
    rfl

/-- A component with an exiting letter at every state has at most
`(card U - 1)^n` words of length `n` that remain inside it. -/
theorem transient_surviving_word_bound {Q U C : Type} [Fintype U]
    [PartialOrder C] [DecidableEq C] (δ : Q → U → Q) (component : Q → C)
    (hforward : ∀ x u, component x ≤ component (δ x u)) (c : C)
    (hexit : ∀ x, component x = c → ∃ u, component (δ x u) ≠ c)
    (n : ℕ) (x : Q) (hx : component x = c) :
    Fintype.card {w : Fin n → U // component (wordEnd δ x w) = c} ≤
      (Fintype.card U - 1) ^ n := by
  classical
  induction n generalizing x with
  | zero => simp [wordEnd, hx]
  | succ n ih =>
    rw [Fintype.card_congr (survivingWordConsEquiv δ component hforward c x hx n),
      Fintype.card_sigma]
    calc
      _ ≤ ∑ _u : {u : U // component (δ x u) = c}, (Fintype.card U - 1) ^ n :=
        Finset.sum_le_sum (fun u _ => ih (δ x u.val) u.property)
      _ = Fintype.card {u : U // component (δ x u) = c} *
          (Fintype.card U - 1) ^ n := by simp
      _ ≤ (Fintype.card U - 1) * (Fintype.card U - 1) ^ n := by
        apply Nat.mul_le_mul_right
        obtain ⟨u, hu⟩ := hexit x hx
        have hh := Fintype.card_subtype_lt (p := fun u => component (δ x u) = c) hu
        omega
      _ = _ := (pow_succ' _ _).symm

/-- Geometric decay gives one positive threshold after which the total
internal count of a transient component is smaller than the block alphabet. -/
theorem transient_internal_count_threshold {Q U C : Type} [Fintype Q] [Fintype U]
    [Nonempty U] [PartialOrder C] [DecidableEq C]
    (δ : Q → U → Q) (component : Q → C)
    (hforward : ∀ x u, component x ≤ component (δ x u)) (c : C)
    (hexit : ∀ x, component x = c → ∃ u, component (δ x u) ≠ c) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n ≥ n₀,
      (∑ x : {x : Q // component x = c},
        Fintype.card {w : Fin n → U // component (wordEnd δ x.val w) = c}) <
        Fintype.card (Fin n → U) := by
  classical
  let N := Fintype.card U
  let K := Fintype.card {x : Q // component x = c}
  have hN : 0 < N := Fintype.card_pos
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hratio0 : (0 : ℝ) ≤ (N - 1 : ℕ) / (N : ℝ) := by positivity
  have hratio1 : (N - 1 : ℕ) / (N : ℝ) < 1 := by
    apply (div_lt_one hNr).mpr
    exact_mod_cast (show N - 1 < N by omega)
  have hlim : Tendsto (fun n : ℕ => (K : ℝ) * ((N - 1 : ℕ) / (N : ℝ)) ^ n)
      atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio1).const_mul (K : ℝ)
  have hev : ∀ᶠ n in atTop, (K : ℝ) * ((N - 1 : ℕ) / (N : ℝ)) ^ n < 1 :=
    hlim.eventually_lt_const (by norm_num)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hev
  refine ⟨n₀ + 1, by omega, fun n hn => ?_⟩
  have hsmall : K * (N - 1) ^ n < N ^ n := by
    have hh := hn₀ n (by omega)
    rw [div_pow, ← mul_div_assoc, div_lt_one (pow_pos hNr n)] at hh
    exact_mod_cast hh
  calc
    _ ≤ ∑ _x : {x : Q // component x = c}, (N - 1) ^ n :=
      Finset.sum_le_sum (fun x _ =>
        transient_surviving_word_bound δ component hforward c hexit n x.val x.property)
    _ = K * (N - 1) ^ n := by simp [K]
    _ < N ^ n := hsmall
    _ = _ := by simp [N]

/-- Actual transient word counts discharge the size premise of the exact
per-state permutation construction, uniformly for every later block length. -/
theorem transient_block_permutation_threshold {Q U C : Type} [Fintype Q] [Fintype U]
    [Nonempty U] [PartialOrder C] [DecidableEq C]
    (δ : Q → U → Q) (component : Q → C)
    (hforward : ∀ x u, component x ≤ component (δ x u)) (c : C)
    (hexit : ∀ x, component x = c → ∃ u, component (δ x u) ≠ c) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n ≥ n₀,
      ∃ π : {x : Q // component x = c} → Equiv.Perm (Fin n → U),
        ∀ x y w, component (wordEnd δ x.val (π x w)) = c →
          component (wordEnd δ y.val (π y w)) = c → x = y := by
  classical
  obtain ⟨n₀, hn₀, hcount⟩ := transient_internal_count_threshold
    δ component hforward c hexit
  refine ⟨n₀, hn₀, fun n hn => ?_⟩
  exact exists_permutations_with_disjoint_internal_inputs
    (fun (x : {x : Q // component x = c}) (w : Fin n → U) =>
      component (wordEnd δ x.val w) = c) (hcount n hn).le

end FSS23105365

-- From Solutions.FSS23105365_SupportComponents
set_option autoImplicit false
namespace FSS23105365

/-- Reflexive reachability for a transition system whose one-step support
is already transitive (as occurs after taking an idempotent support power). -/
def supportReach {Q U : Type} (δ : Q → U → Q) (x y : Q) : Prop :=
  x = y ∨ ∃ u, δ x u = y

def TransitiveSupport {Q U : Type} (δ : Q → U → Q) : Prop :=
  ∀ x y z, (∃ u, δ x u = y) → (∃ u, δ y u = z) → ∃ u, δ x u = z

theorem supportReach_trans {Q U : Type} (δ : Q → U → Q)
    (htrans : TransitiveSupport δ) {x y z : Q}
    (hxy : supportReach δ x y) (hyz : supportReach δ y z) : supportReach δ x z := by
  rcases hxy with rfl | hxy
  · exact hyz
  rcases hyz with rfl | hyz
  · exact Or.inr hxy
  exact Or.inr (htrans x y z hxy hyz)

/-- SCC labels are their reachable sets, ordered by reverse inclusion.
Equality of labels is exactly mutual reachability, so no quotient choices
or unproved condensation-graph assumptions are needed. -/
def supportComponent {Q U : Type} (δ : Q → U → Q) (x : Q) : (Set Q)ᵒᵈ :=
  {y | supportReach δ x y}

theorem supportComponent_le_iff {Q U : Type} (δ : Q → U → Q)
    (htrans : TransitiveSupport δ) (x y : Q) :
    supportComponent δ x ≤ supportComponent δ y ↔ supportReach δ x y := by
  constructor
  · intro h
    exact h (show supportReach δ y y from Or.inl rfl)
  · intro h z hz
    exact supportReach_trans δ htrans h hz

theorem supportComponent_eq_iff {Q U : Type} (δ : Q → U → Q)
    (htrans : TransitiveSupport δ) (x y : Q) :
    supportComponent δ x = supportComponent δ y ↔
      supportReach δ x y ∧ supportReach δ y x := by
  rw [le_antisymm_iff, supportComponent_le_iff δ htrans,
    supportComponent_le_iff δ htrans]

theorem supportComponent_forward {Q U : Type} (δ : Q → U → Q)
    (htrans : TransitiveSupport δ) (x : Q) (u : U) :
    supportComponent δ x ≤ supportComponent δ (δ x u) :=
  (supportComponent_le_iff δ htrans _ _).mpr (Or.inr ⟨u, rfl⟩)

def supportTerminal {Q U : Type} (δ : Q → U → Q) (c : (Set Q)ᵒᵈ) : Prop :=
  ∀ x, supportComponent δ x = c → ∀ u, supportComponent δ (δ x u) = c

/-- In a transient SCC of a transitive support, every state has a
one-letter exit, even when the SCC consists of a single loopless state. -/
theorem transient_support_exit {Q U : Type} (δ : Q → U → Q)
    (htrans : TransitiveSupport δ) (c : (Set Q)ᵒᵈ)
    (ht : ¬supportTerminal δ c) (x : Q) (hx : supportComponent δ x = c) :
    ∃ u, supportComponent δ (δ x u) ≠ c := by
  classical
  obtain ⟨y, hy, u, hu⟩ : ∃ y, ∃ _ : supportComponent δ y = c,
      ∃ u, supportComponent δ (δ y u) ≠ c := by
    simpa only [supportTerminal, not_forall] using ht
  have hxy := ((supportComponent_eq_iff δ htrans x y).mp (hx.trans hy.symm)).1
  rcases hxy with rfl | hxy
  · exact ⟨u, hu⟩
  obtain ⟨v, hv⟩ := htrans x y (δ y u) hxy ⟨u, rfl⟩
  exact ⟨v, by simpa only [hv] using hu⟩

/-- A terminal component has full one-step support, including its diagonal.
The diagonal uses a nonempty alphabet and terminal closure; it does not
follow from reflexive SCC reachability alone. -/
theorem terminal_support_full {Q U : Type} [Nonempty U] (δ : Q → U → Q)
    (htrans : TransitiveSupport δ) (c : (Set Q)ᵒᵈ) (ht : supportTerminal δ c)
    (x y : Q) (hx : supportComponent δ x = c) (hy : supportComponent δ y = c) :
    ∃ u, δ x u = y := by
  have hxy := ((supportComponent_eq_iff δ htrans x y).mp (hx.trans hy.symm)).1
  rcases hxy with rfl | hxy
  · let u : U := Classical.choice ‹Nonempty U›
    have hback := ((supportComponent_eq_iff δ htrans (δ x u) x).mp
      ((ht x hx u).trans hx.symm)).1
    rcases hback with heq | hback
    · exact ⟨u, heq⟩
    · exact htrans x (δ x u) x ⟨u, rfl⟩ hback
  · exact hxy

/-- Restriction to an actual terminal SCC is closed by its definition. -/
def terminalComponentStep {Q U : Type} (δ : Q → U → Q) (c : (Set Q)ᵒᵈ)
    (ht : supportTerminal δ c) :
    {x : Q // supportComponent δ x = c} → U → {x : Q // supportComponent δ x = c} :=
  fun x u => ⟨δ x.val u, ht x.val x.property u⟩

theorem terminalComponentStep_full {Q U : Type} [Nonempty U] (δ : Q → U → Q)
    (htrans : TransitiveSupport δ) (c : (Set Q)ᵒᵈ) (ht : supportTerminal δ c)
    (x y : {x : Q // supportComponent δ x = c}) :
    ∃ u, terminalComponentStep δ c ht x u = y := by
  obtain ⟨u, hu⟩ := terminal_support_full δ htrans c ht x.val y.val x.property y.property
  exact ⟨u, Subtype.ext hu⟩

/-- The transient allocation premise is now derived from the actual SCC
of the given transition system, rather than assumed as a decay hypothesis. -/
theorem transient_support_permutation_threshold {Q U : Type} [Fintype Q] [Fintype U]
    [Nonempty U] (δ : Q → U → Q) (htrans : TransitiveSupport δ)
    (c : (Set Q)ᵒᵈ) (ht : ¬supportTerminal δ c) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n ≥ n₀,
      ∃ π : {x : Q // supportComponent δ x = c} → Equiv.Perm (Fin n → U),
        ∀ x y w, supportComponent δ (wordEnd δ x.val (π x w)) = c →
          supportComponent δ (wordEnd δ y.val (π y w)) = c → x = y := by
  classical
  exact transient_block_permutation_threshold δ (supportComponent δ)
    (supportComponent_forward δ htrans) c (transient_support_exit δ htrans c ht)

/-- Passing to a positive idempotent support block makes the support
transitive. This supplies the SCC construction's hypothesis for every DFA. -/
theorem exists_transitive_block_transition {Q U : Type} [Fintype Q] (δ : Q → U → Q) :
    ∃ a : ℕ, 0 < a ∧ TransitiveSupport (fun x (w : Fin a → U) => wordEnd δ x w) := by
  obtain ⟨a, ha, he⟩ := exists_idempotent_block_support δ
  refine ⟨a, ha, fun x y z hxy hyz => ?_⟩
  exact (he x z).mp ⟨y, hxy, hyz⟩

end FSS23105365

-- From Solutions.FSS23105365_TransitionTransport
set_option autoImplicit false
namespace FSS23105365

/-- A letter-by-letter transition map also intertwines complete words. -/
theorem foldl_transition_map {H Q U : Type} (τ : H → U → H) (δ : Q → U → Q)
    (φ : H → Q) (hφ : ∀ h u, φ (τ h u) = δ (φ h) u)
    (w : List U) (h : H) : φ (w.foldl τ h) = w.foldl δ (φ h) := by
  induction w generalizing h with
  | nil => rfl
  | cons u w ih => simpa only [List.foldl_cons, hφ] using ih (τ h u)

theorem wordEnd_transition_map {H Q U : Type} (τ : H → U → H) (δ : Q → U → Q)
    (φ : H → Q) (hφ : ∀ h u, φ (τ h u) = δ (φ h) u)
    {n : ℕ} (w : Fin n → U) (h : H) :
    φ (wordEnd τ h w) = wordEnd δ (φ h) w :=
  foldl_transition_map τ δ φ hφ (List.ofFn w) h

/-- Injectively embedded transition systems inherit aperiodicity. -/
theorem aperiodicTransitions_of_injective_map {H Q U : Type}
    (τ : H → U → H) (δ : Q → U → Q) (φ : H → Q)
    (hinj : Function.Injective φ) (hφ : ∀ h u, φ (τ h u) = δ (φ h) u)
    (hδ : AperiodicTransitions δ) : AperiodicTransitions τ := by
  intro w
  obtain ⟨k, hk, he⟩ := hδ w
  have hs : Function.Semiconj φ (fun h => w.foldl τ h) (fun q => w.foldl δ q) :=
    foldl_transition_map τ δ φ hφ w
  refine ⟨k, hk, funext (fun h => hinj ?_)⟩
  rw [hs.iterate_right k h, hs.iterate_right (k + 1) h]
  exact congrFun he (φ h)

/-- Replacing each letter by a letter of an aperiodic transition system
preserves aperiodicity, regardless of whether the relabeling is injective. -/
theorem aperiodicTransitions_relabel {H U V : Type} (τ : H → U → H)
    (f : V → U) (hτ : AperiodicTransitions τ) :
    AperiodicTransitions (fun h v => τ h (f v)) := by
  intro w
  simpa only [List.foldl_map] using hτ (w.map f)

end FSS23105365

-- From Solutions.FSS23105365_TerminalComponentModel
set_option autoImplicit false
namespace FSS23105365

/-- Reindex the positive-kernel construction to any finite nonempty state
space. The hidden state set and projection are fixed before the threshold. -/
theorem finite_positive_transition_hidden_model {Q U : Type} [Fintype Q] [Nonempty Q]
    [Fintype U] [Nonempty U] (δ : Q → U → Q) (hfull : ∀ x y, ∃ u, δ x u = y) :
    ∃ r : ℕ, ∃ φ : Fin r → Q, Function.Surjective φ ∧
      ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n ≥ n₀,
        ∃ τ : Fin r → (Fin n → U) → Fin r,
        ∃ decode : Fin r → Equiv.Perm (Fin n → U),
          (∀ h u, φ (τ h u) = wordEnd δ (φ h) (decode h u)) ∧
          AperiodicTransitions τ := by
  classical
  let e := Fintype.equivFin Q
  let d : Fin (Fintype.card Q) → U → Fin (Fintype.card Q) :=
    fun x u => e (δ (e.symm x) u)
  have hd : ∀ x u, e.symm (d x u) = δ (e.symm x) u := by
    intro x u; exact e.symm_apply_apply _
  have hdf : ∀ x y, ∃ u, d x u = y := by
    intro x y
    obtain ⟨u, hu⟩ := hfull (e.symm x) (e.symm y)
    exact ⟨u, by simp only [d, hu, e.apply_symm_apply]⟩
  obtain ⟨n₀, hn₀, hmodel⟩ := positive_transition_hidden_model
    (Fintype.card_pos (α := Q)) d hdf
  refine ⟨Fintype.card Q + Fintype.card Q,
    fun h => e.symm (splitProjection (Fintype.card Q) h), ?_, n₀, hn₀, ?_⟩
  · intro x
    exact ⟨Fin.castAdd _ (e x), by simp⟩
  · intro n hn
    obtain ⟨τ, decode, _, hp, ha⟩ := hmodel n hn
    refine ⟨τ, decode, fun h u => ?_, ha⟩
    change e.symm (splitProjection _ (τ h u)) = _
    rw [hp]
    exact wordEnd_transition_map d δ e.symm hd _ _

/-- The terminal construction now applies to every actual nonempty
terminal SCC of the transitive support, with exact original-state decoding. -/
theorem terminal_support_hidden_model {Q U : Type} [Fintype Q] [Fintype U]
    [Nonempty U] (δ : Q → U → Q) (htrans : TransitiveSupport δ)
    (c : (Set Q)ᵒᵈ) (hc : ∃ x, supportComponent δ x = c) (ht : supportTerminal δ c) :
    ∃ r : ℕ, ∃ φ : Fin r → {x : Q // supportComponent δ x = c},
      Function.Surjective φ ∧ ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n ≥ n₀,
        ∃ τ : Fin r → (Fin n → U) → Fin r,
        ∃ decode : Fin r → Equiv.Perm (Fin n → U),
          (∀ h u, (φ (τ h u)).val = wordEnd δ (φ h).val (decode h u)) ∧
          AperiodicTransitions τ := by
  classical
  haveI : Nonempty {x : Q // supportComponent δ x = c} := by
    obtain ⟨x, hx⟩ := hc
    exact ⟨⟨x, hx⟩⟩
  let d := terminalComponentStep δ c ht
  obtain ⟨r, φ, hφ, n₀, hn₀, hm⟩ := finite_positive_transition_hidden_model d
    (terminalComponentStep_full δ htrans c ht)
  refine ⟨r, φ, hφ, n₀, hn₀, fun n hn => ?_⟩
  obtain ⟨τ, decode, hp, ha⟩ := hm n hn
  refine ⟨τ, decode, fun h u => ?_, ha⟩
  rw [hp]
  exact wordEnd_transition_map d δ Subtype.val (fun _ _ => rfl) _ _

end FSS23105365

-- From Solutions.FSS23105365_ComponentModelAssembly
set_option autoImplicit false
namespace FSS23105365

/-- Assemble local hidden representations along a forward component order.
Exits are sent to a chosen representative of their exact projected target.
Terminal components use their own aperiodic maps; transient components use
the disjoint-source property of their input permutations. -/
theorem assemble_component_models {Q U C : Type} [Fintype C] [PartialOrder C]
    (δ : Q → U → Q) (component : Q → C) (terminal : C → Prop)
    (hforward : ∀ x u, component x ≤ component (δ x u))
    (r : C → ℕ) (φ : (c : C) → Fin (r c) → Q)
    (hφc : ∀ c h, component (φ c h) = c)
    (hφsurj : ∀ x, ∃ h : Fin (r (component x)), φ (component x) h = x)
    (decode : (c : C) → Fin (r c) → Equiv.Perm U)
    (hterminal : ∀ c, terminal c → ∃ t : Fin (r c) → U → Fin (r c),
      (∀ h u, φ c (t h u) = δ (φ c h) (decode c h u)) ∧ AperiodicTransitions t)
    (htransient : ∀ c, ¬terminal c → ∀ h k u,
      component (δ (φ c h) (decode c h u)) = c →
      component (δ (φ c k) (decode c k u)) = c → h = k) :
    ∃ τ : (Σ c, Fin (r c)) → U → (Σ c, Fin (r c)),
      (∀ h u, φ (τ h u).1 (τ h u).2 = δ (φ h.1 h.2) (decode h.1 h.2 u)) ∧
      AperiodicTransitions τ := by
  classical
  let H := Σ c, Fin (r c)
  let project : H → Q := fun h => φ h.1 h.2
  have hps : Function.Surjective project := by
    intro x
    obtain ⟨h, hh⟩ := hφsurj x
    exact ⟨⟨component x, h⟩, hh⟩
  choose liftState hliftState using hps
  have hl : ∀ c, ∃ t : Fin (r c) → U → Fin (r c), terminal c →
      (∀ h u, φ c (t h u) = δ (φ c h) (decode c h u)) ∧ AperiodicTransitions t := by
    intro c
    by_cases hc : terminal c
    · obtain ⟨t, hp, ha⟩ := hterminal c hc
      exact ⟨t, fun _ => ⟨hp, ha⟩⟩
    · exact ⟨fun h _ => h, fun h => (hc h).elim⟩
  choose localStep hlocal using hl
  let τ : H → U → H := fun h u => if terminal h.1 then
    ⟨h.1, localStep h.1 h.2 u⟩ else liftState (δ (project h) (decode h.1 h.2 u))
  have hp : ∀ h u, project (τ h u) = δ (project h) (decode h.1 h.2 u) := by
    rintro ⟨c, h⟩ u
    by_cases hc : terminal c
    · simpa only [τ, if_pos hc, project] using (hlocal c hc).1 h u
    · simpa only [τ, if_neg hc, project] using
        hliftState (δ (φ c h) (decode c h u))
  have hpc : ∀ h : H, component (project h) = h.1 := fun h => hφc h.1 h.2
  have hf : ∀ h u, h.1 ≤ (τ h u).1 := by
    intro h u
    rw [← hpc h, ← hpc (τ h u), hp]
    exact hforward _ _
  refine ⟨τ, hp, component_aperiodicity τ Sigma.fst terminal hf ?_ ?_⟩
  · intro c hc w x hx n hn hperiod
    rcases x with ⟨d, x⟩
    change d = c at hx
    subst d
    let embed : Fin (r c) → H := fun h => ⟨c, h⟩
    have hembed : ∀ h u, embed (localStep c h u) = τ (embed h) u := by
      intro h u
      simp only [embed, τ, if_pos hc]
    have hs : Function.Semiconj embed (fun h => w.foldl (localStep c) h)
        (fun h => w.foldl τ h) := foldl_transition_map _ _ embed hembed w
    have hinj : Function.Injective embed := by
      intro h k he
      exact eq_of_heq (Sigma.mk.inj_iff.mp he).2
    have hlperiod : (fun h => w.foldl (localStep c) h)^[n] x = x := by
      apply hinj
      exact (hs.iterate_right n x).trans hperiod
    have hfix := (aperiodicTransitions_iff_no_cycles (localStep c)).mp
      (hlocal c hc).2 w x n hn hlperiod
    exact (hs x).symm.trans (congrArg embed hfix)
  · intro c hc u x y hx hy htx hty
    rcases x with ⟨d, x⟩
    rcases y with ⟨e, y⟩
    change d = c at hx
    change e = c at hy
    subst d
    subst e
    have hdx : component (δ (φ c x) (decode c x u)) = c := by
      rw [← hp ⟨c, x⟩ u, hpc]
      exact htx
    have hdy : component (δ (φ c y) (decode c y u)) = c := by
      rw [← hp ⟨c, y⟩ u, hpc]
      exact hty
    exact congrArg (fun h => (⟨c, h⟩ : H)) (htransient c hc x y u hdx hdy)

end FSS23105365

-- From Solutions.FSS23105365_TransitiveSupportHiddenModel
set_option autoImplicit false
namespace FSS23105365

/-- The local data required for global assembly at a fixed block length. -/
structure LocalSupportModel {Q U : Type} (δ : Q → U → Q) (c : (Set Q)ᵒᵈ) (n : ℕ) where
  size : ℕ
  project : Fin size → {x : Q // supportComponent δ x = c}
  surjective : Function.Surjective project
  decode : Fin size → Equiv.Perm (Fin n → U)
  terminal : supportTerminal δ c → ∃ τ : Fin size → (Fin n → U) → Fin size,
    (∀ h u, (project (τ h u)).val = wordEnd δ (project h).val (decode h u)) ∧
      AperiodicTransitions τ
  transient : ¬supportTerminal δ c → ∀ h k u,
    supportComponent δ (wordEnd δ (project h).val (decode h u)) = c →
    supportComponent δ (wordEnd δ (project k).val (decode k u)) = c → h = k

theorem local_support_model_threshold {Q U : Type} [Fintype Q] [Fintype U] [Nonempty U]
    (δ : Q → U → Q) (htrans : TransitiveSupport δ) (c : (Set Q)ᵒᵈ)
    (hc : ∃ x, supportComponent δ x = c) :
    ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n ≥ n₀, Nonempty (LocalSupportModel δ c n) := by
  classical
  by_cases ht : supportTerminal δ c
  · obtain ⟨r, φ, hφ, n₀, hn₀, hm⟩ := terminal_support_hidden_model δ htrans c hc ht
    refine ⟨n₀, hn₀, fun n hn => ?_⟩
    obtain ⟨τ, decode, hp, ha⟩ := hm n hn
    exact ⟨{
      size := r, project := φ, surjective := hφ, decode := decode
      terminal := fun _ => ⟨τ, hp, ha⟩
      transient := fun hh => (hh ht).elim }⟩
  · obtain ⟨n₀, hn₀, hm⟩ := transient_support_permutation_threshold δ htrans c ht
    let e := Fintype.equivFin {x : Q // supportComponent δ x = c}
    refine ⟨n₀, hn₀, fun n hn => ?_⟩
    obtain ⟨π, hπ⟩ := hm n hn
    exact ⟨{
      size := Fintype.card {x : Q // supportComponent δ x = c}
      project := e.symm, surjective := e.symm.surjective
      decode := fun h => π (e.symm h)
      terminal := fun hh => (ht hh).elim
      transient := fun _ h k u hh hk => e.symm.injective (hπ _ _ u hh hk) }⟩

/-- Every finite transition system with transitive one-step support has
an exact aperiodic hidden block representation. The finite maximum of the
actual SCC thresholds discharges the simultaneous block-length choice. -/
theorem transitive_support_hidden_model {Q U : Type} [Fintype Q] [Fintype U] [Nonempty U]
    (δ : Q → U → Q) (htrans : TransitiveSupport δ) :
    ∃ n : ℕ, 0 < n ∧ ∃ r : ℕ, ∃ φ : Fin r → Q,
      Function.Surjective φ ∧ ∃ τ : Fin r → (Fin n → U) → Fin r,
      ∃ decode : Fin r → Equiv.Perm (Fin n → U),
        (∀ h u, φ (τ h u) = wordEnd δ (φ h) (decode h u)) ∧
        AperiodicTransitions τ := by
  classical
  let C := {c : (Set Q)ᵒᵈ // ∃ x, supportComponent δ x = c}
  let component : Q → C := fun x => ⟨supportComponent δ x, x, rfl⟩
  have hall : ∀ c : C, ∃ n₀ : ℕ, 0 < n₀ ∧ ∀ n ≥ n₀,
      Nonempty (LocalSupportModel δ c.val n) := fun c =>
    local_support_model_threshold δ htrans c.val c.property
  choose n₀ hn₀ hmodels using hall
  let n := Finset.univ.sup n₀ + 1
  have hn : 0 < n := by dsimp [n]; omega
  have hnc : ∀ c, n₀ c ≤ n := fun c =>
    (Finset.le_sup (f := n₀) (Finset.mem_univ c)).trans (Nat.le_succ _)
  let m : (c : C) → LocalSupportModel δ c.val n :=
    fun c => Classical.choice (hmodels c n (hnc c))
  let r : C → ℕ := fun c => (m c).size
  let φ : (c : C) → Fin (r c) → Q := fun c h => ((m c).project h).val
  have hφc : ∀ c h, component (φ c h) = c := by
    intro c h
    exact Subtype.ext ((m c).project h).property
  have hφsurj : ∀ x, ∃ h : Fin (r (component x)), φ (component x) h = x := by
    intro x
    obtain ⟨h, hh⟩ := (m (component x)).surjective ⟨x, rfl⟩
    exact ⟨h, congrArg Subtype.val hh⟩
  let d : Q → (Fin n → U) → Q := fun x w => wordEnd δ x w
  have hforward : ∀ x w, component x ≤ component (d x w) := by
    intro x w
    exact component_le_foldl δ (supportComponent δ) (supportComponent_forward δ htrans)
      (List.ofFn w) x
  obtain ⟨τ, hp, ha⟩ := assemble_component_models d component
    (fun c => supportTerminal δ c.val) hforward r φ hφc hφsurj
    (fun c => (m c).decode) (fun c hc => (m c).terminal hc)
    (fun c hc h k u hh hk => (m c).transient hc h k u
      (congrArg Subtype.val hh) (congrArg Subtype.val hk))
  let H := Σ c, Fin (r c)
  let e := Fintype.equivFin H
  let project : H → Q := fun h => φ h.1 h.2
  let τ' : Fin (Fintype.card H) → (Fin n → U) → Fin (Fintype.card H) :=
    fun h u => e (τ (e.symm h) u)
  have hτ' : ∀ h u, e.symm (τ' h u) = τ (e.symm h) u := by
    intro h u
    exact e.symm_apply_apply _
  refine ⟨n, hn, Fintype.card H, fun h => project (e.symm h), ?_, τ',
    fun h => (m (e.symm h).1).decode (e.symm h).2, ?_, ?_⟩
  · intro x
    obtain ⟨h, hh⟩ := hφsurj x
    exact ⟨e ⟨component x, h⟩, by simpa only [e.symm_apply_apply] using hh⟩
  · intro h u
    change project (e.symm (τ' h u)) = _
    rw [hτ']
    exact hp (e.symm h) u
  · exact aperiodicTransitions_of_injective_map τ' τ e.symm e.symm.injective hτ' ha

end FSS23105365

-- From Solutions.FSS23105365_HiddenBlockRepresentation
set_option autoImplicit false
namespace FSS23105365

/-- Consecutive blocks, in their original bit order. -/
def blockAlphabetEquiv (a c : ℕ) : Bits (c * a) ≃ (Fin c → Bits a) where
  toFun w i j := w (finProdFinEquiv (i, j))
  invFun ws k := ws (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  left_inv w := by
    funext k
    change w (finProdFinEquiv (finProdFinEquiv.symm k)) = w k
    rw [Equiv.apply_symm_apply]
  right_inv ws := by
    funext i j
    change ws (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = ws i j
    rw [Equiv.symm_apply_apply]

theorem blockAlphabet_list (a c : ℕ) (ws : Fin c → Bits a) :
    List.ofFn ((blockAlphabetEquiv a c).symm ws) = (List.ofFn ws).flatMap List.ofFn := by
  change List.ofFn (fun i : Fin (c * a) =>
    ws (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) = _
  rw [List.ofFn_mul, List.flatMap_def, List.map_ofFn]
  congr 1
  congr 1
  funext i
  congr 1
  funext j
  have hi : (⟨i.val * a + j.val, by
      simpa [finProdFinEquiv, Nat.mul_comm, Nat.add_comm] using
        (finProdFinEquiv (i, j)).isLt⟩ : Fin (c * a)) = finProdFinEquiv (i, j) := by
    apply Fin.ext
    simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  simp only [hi, Equiv.symm_apply_apply]

/-- Flattening a block word preserves the exact original DFA endpoint. -/
theorem blockAlphabet_wordEnd {Q : Type} (δ : Q → Bool → Q) (a c : ℕ)
    (x : Q) (ws : Fin c → Bits a) :
    wordEnd δ x ((blockAlphabetEquiv a c).symm ws) =
      wordEnd (fun q (w : Bits a) => wordEnd δ q w) x ws := by
  unfold wordEnd
  rw [blockAlphabet_list, foldl_flatMap_blocks]

/-- Lemma 3.5: every finite binary transition system admits a positive,
constant block length, a finite hidden state space, a surjective projection,
state-dependent block permutations, and an aperiodic transition monoid. -/
theorem hidden_block_representation {Q : Type} [Fintype Q] (δ : Q → Bool → Q) :
    ∃ b : ℕ, 0 < b ∧ ∃ r : ℕ, ∃ φ : Fin r → Q,
      Function.Surjective φ ∧ ∃ τ : Fin r → Bits b → Fin r,
      ∃ decode : Fin r → Equiv.Perm (Bits b),
        (∀ h u, φ (τ h u) = wordEnd δ (φ h) (decode h u)) ∧
        AperiodicTransitions τ := by
  obtain ⟨a, ha, htrans⟩ := exists_transitive_block_transition δ
  let d : Q → Bits a → Q := fun q w => wordEnd δ q w
  obtain ⟨c, hc, r, φ, hφ, τ, decode, hp, haper⟩ := transitive_support_hidden_model d htrans
  let e := blockAlphabetEquiv a c
  let τ' : Fin r → Bits (c * a) → Fin r := fun h u => τ h (e u)
  let decode' : Fin r → Equiv.Perm (Bits (c * a)) :=
    fun h => e.trans ((decode h).trans e.symm)
  refine ⟨c * a, Nat.mul_pos hc ha, r, φ, hφ, τ', decode', ?_, ?_⟩
  · intro h u
    change φ (τ h (e u)) = wordEnd δ (φ h) (e.symm (decode h (e u)))
    rw [hp]
    exact (blockAlphabet_wordEnd δ a c (φ h) (decode h (e u))).symm
  · exact aperiodicTransitions_relabel τ e haper

/-- The structure consumed by the full-run sampler is now obtained from
an arbitrary input DFA, with no assumed hidden-model or convergence premise. -/
theorem exists_hiddenBlockModel {q : ℕ} (A : BinaryDFA q) :
    ∃ b : ℕ, 0 < b ∧ ∃ r : ℕ, Nonempty (HiddenBlockModel A (Fin r) b) := by
  obtain ⟨b, hb, r, φ, hφ, τ, decode, hp, ha⟩ := hidden_block_representation A.step
  exact ⟨b, hb, r, ⟨{
    step := τ, project := φ, project_surjective := hφ, decode := decode,
    block_project := hp, aperiodic := ha }⟩⟩

/-- Unconditional correctness of the paper's block sampler for an arbitrary
DFA, including the complete trajectory and unchanged tail. Its circuit
depth and size still require the separate aperiodic-evaluation theorem. -/
theorem exists_hidden_run_sampler {q : ℕ} (A : BinaryDFA q) :
    ∃ b : ℕ, 0 < b ∧ ∃ s : ℕ, 0 < s ∧
      ∃ B : HiddenBlockModel A (Fin s) b, ∃ h : Fin s,
        B.project h = A.start ∧ ∀ m r (w : Bits (m * b + r)) (γ : Path q (m * b + r)),
          (Fintype.card {x : Bits (m * b + r) //
            (hiddenWordEquiv B.step B.decode h m r x,
              locallyDecodedPath A B m r h (blockTailEquiv b m r x).1
                (blockTailEquiv b m r x).2) = (w, γ)} : ℝ) / 2 ^ (m * b + r) =
            if γ = drivenPath A.step (m * b + r) A.start w then
              1 / 2 ^ (m * b + r) else 0 := by
  classical
  obtain ⟨b, hb, s, ⟨B⟩⟩ := exists_hiddenBlockModel A
  obtain ⟨h, hh⟩ := B.project_surjective A.start
  have hs : 0 < s := Nat.zero_le h.val |>.trans_lt h.isLt
  exact ⟨b, hb, s, hs, B, h, hh, fun m r w γ => hidden_run_sampler_law A B hb m r h hh w γ⟩

end FSS23105365

-- From Solutions.FSS23105365_CircuitExactLaw
set_option autoImplicit false
namespace FSS23105365

/-- Transfer an exactly counted finite-source function to the original
circuit law. The input-count equality supplies the seed reindexing, and
injective output encoding preserves exactly the intended outcome fibers. -/
theorem circuit_exactLaw_of_function {Out Ω : Type} [Fintype Ω] [DecidableEq Ω] {n : ℕ}
    (S : Circuit Out) (hbits : S.randomBits = n) (encode : Ω → Out → Bool)
    (hinj : Function.Injective encode) (f : Bits n → Ω)
    (he : ∀ seed : Bits n, S.eval (fun i => seed (Fin.cast hbits i)) = encode (f seed))
    (p : Ω → ℝ)
    (hp : ∀ z, (Fintype.card {seed : Bits n // f seed = z} : ℝ) / 2 ^ n = p z) :
    ExactLaw S encode p := by
  classical
  subst n
  have hv : ∀ seed, S.eval seed = encode (f seed) := by simpa only [Fin.cast_refl, id_eq] using he
  refine ⟨fun seed => ⟨f seed, hv seed⟩, fun z => ?_⟩
  have hfib : ∀ seed, S.eval seed = encode z ↔ f seed = z := by
    intro seed
    rw [hv]
    exact hinj.eq_iff
  unfold mass
  simp only [hfib]
  rw [← Fintype.card_subtype]
  exact hp z

end FSS23105365

-- From Solutions.FSS23105365_DFARunSampling
set_option autoImplicit false
namespace FSS23105365

def fullRunLaw {q n : ℕ} (A : BinaryDFA q) (z : Bits n × Path q n) : ℝ :=
  if z.2 = drivenPath A.step n A.start z.1 then 1 / (2 : ℝ) ^ n else 0

/-- The compiled block sampler preserves the exact joint law of the
uniform word and its entire DFA trajectory. -/
theorem hidden_run_circuits_exactLaw {q b : ℕ} {H : Type} [Fintype H]
    (A : BinaryDFA q) (B : HiddenBlockModel A H b) (hb : 0 < b) (h : H)
    (hh : B.project h = A.start) :
    ∃ D C k : ℕ, ∀ m r : ℕ, r ≤ b →
      ∃ S : Circuit (FullRunOutput q (m * b + r)), S.randomBits = m * b + r ∧
        S.depth ≤ D ∧ S.size ≤ C * (m * b + r + 1) ^ k ∧
        ExactLaw S fullRunEncode (fullRunLaw A) := by
  obtain ⟨D, C, k, hc⟩ := hidden_run_circuits A B hb h
  refine ⟨D, C, k, fun m r hr => ?_⟩
  obtain ⟨S, hbits, hd, hs, he⟩ := hc m r hr
  refine ⟨S, hbits, hd, hs, circuit_exactLaw_of_function S hbits fullRunEncode
    (fullRunEncode_injective q (m * b + r))
    (fun seed => (hiddenWordEquiv B.step B.decode h m r seed,
      locallyDecodedPath A B m r h (blockTailEquiv b m r seed).1
        (blockTailEquiv b m r seed).2)) he (fullRunLaw A) ?_⟩
  intro z
  exact hidden_run_sampler_law A B hb m r h hh z.1 z.2

/-- Proposition 3.2. Every binary DFA has an exact randomized-AC0 sampler
for the joint uniform word and full run. It uses exactly n fair input bits,
with one depth bound and one polynomial size bound for all n, including 0. -/
theorem exact_dfa_run_sampling {q : ℕ} (A : BinaryDFA q) :
    ∃ D C k : ℕ, ∀ n : ℕ, ∃ S : Circuit (FullRunOutput q n),
      S.randomBits = n ∧ S.depth ≤ D ∧ S.size ≤ C * (n + 1) ^ k ∧
      ExactLaw S fullRunEncode (fullRunLaw A) := by
  obtain ⟨b, hb, s, ⟨B⟩⟩ := exists_hiddenBlockModel A
  obtain ⟨h, hh⟩ := B.project_surjective A.start
  obtain ⟨D, C, k, hc⟩ := hidden_run_circuits_exactLaw A B hb h hh
  refine ⟨D, C, k, fun n => ?_⟩
  let P := fun ℓ => ∃ S : Circuit (FullRunOutput q ℓ),
    S.randomBits = ℓ ∧ S.depth ≤ D ∧ S.size ≤ C * (ℓ + 1) ^ k ∧
      ExactLaw S fullRunEncode (fullRunLaw A)
  have hn : P (n / b * b + n % b) := hc (n / b) (n % b) (Nat.mod_lt n hb).le
  exact Eq.mp (congrArg P (Nat.div_add_mod' n b)) hn

end FSS23105365

-- From Solutions.FSS23105365_DFARunFormulas
set_option autoImplicit false
namespace FSS23105365

/-- Retain the formula representation of the exact run sampler so that
fixed-state observations can be composed without adding random inputs. -/
theorem hidden_run_formulas {q b : ℕ} {H : Type} [Fintype H]
    (A : BinaryDFA q) (B : HiddenBlockModel A H b) (hb : 0 < b) (h : H)
    (hh : B.project h = A.start) :
    ∃ D C k : ℕ, ∀ m r : ℕ, r ≤ b →
      ∃ fs : FullRunOutput q (m * b + r) → CircuitFormula (m * b + r),
        (∀ o, formulaDepth (fs o) ≤ D) ∧
        (∀ o, formulaCost (fs o) ≤ C * (m * b + r + 1) ^ k) ∧
        ∃ e : Bits (m * b + r) ≃ Bits (m * b + r),
          ∀ seed o, formulaEval (fs o) seed = fullRunEncode
            (e seed, drivenPath A.step (m * b + r) A.start (e seed)) o := by
  letI : Nonempty H := ⟨h⟩
  obtain ⟨D, C, k, state, hd, hc, he⟩ :=
    aperiodic_block_tail_prefix_formulas B.step B.aperiodic h finiteOneHot
  let L := 2 ^ (Fintype.card H + b) * (3 * (Fintype.card H + b) + 2) + 1
  let K := L * (C + 1) + C
  refine ⟨D + 3, K, k, fun m r hr => ?_⟩
  let n := m * b + r
  let fs : FullRunOutput q n → CircuitFormula n :=
    Sum.elim (hiddenWordFormula A B m r (state m r))
      (fun o => hiddenPathFormula A B m r (state m r) o.1 o.2)
  refine ⟨fs, ?_, ?_, hiddenWordEquiv B.step B.decode h m r, ?_⟩
  · intro o
    cases o with
    | inl i => exact hiddenWordFormula_depth A B m r D (state m r) (hd m r) i
    | inr o => exact hiddenPathFormula_depth A B m r D (state m r) (hd m r) o.1 o.2
  · intro o
    have hmn : m ≤ n := by dsimp only [n]; nlinarith
    have hstate : ∀ t j, formulaCost (state m r t j) ≤ C * (n + 1) ^ k := fun t j =>
      (hc m r t j).trans (monomial_bound_mono C m n k k hmn le_rfl)
    have hlocal : formulaCost (fs o) ≤ L * (C * (n + 1) ^ k + 1) + C * (n + 1) ^ k := by
      cases o with
      | inl i => exact hiddenWordFormula_cost A B m r _ (state m r) hstate i
      | inr o => exact hiddenPathFormula_cost A B m r _ hr (state m r) hstate o.1 o.2
    have hp := Nat.one_le_pow' k n
    change formulaCost (fs o) ≤ K * (n + 1) ^ k
    dsimp only [K]
    nlinarith
  · intro seed o
    have hp : locallyDecodedPath A B m r h (blockTailEquiv b m r seed).1
        (blockTailEquiv b m r seed).2 = drivenPath A.step (m * b + r) A.start
          (hiddenWordEquiv B.step B.decode h m r seed) := by
      rw [locallyDecodedPath_correct A B hb, hh]
      rfl
    cases o with
    | inl i =>
      exact hiddenWordFormula_eval A B m r h (state m r) seed
        (fun t j => he m r t j seed) i
    | inr o =>
      have hv := hiddenPathFormula_eval A B m r h (state m r) seed
        (fun t j => he m r t j seed) o.1 o.2
      rw [hp] at hv
      exact hv

theorem exact_dfa_run_formulas {q : ℕ} (A : BinaryDFA q) :
    ∃ D C k : ℕ, ∀ n : ℕ, ∃ fs : FullRunOutput q n → CircuitFormula n,
      (∀ o, formulaDepth (fs o) ≤ D) ∧
      (∀ o, formulaCost (fs o) ≤ C * (n + 1) ^ k) ∧
      ∃ e : Bits n ≃ Bits n, ∀ seed o, formulaEval (fs o) seed =
        fullRunEncode (e seed, drivenPath A.step n A.start (e seed)) o := by
  obtain ⟨b, hb, s, ⟨B⟩⟩ := exists_hiddenBlockModel A
  obtain ⟨h, hh⟩ := B.project_surjective A.start
  obtain ⟨D, C, k, hc⟩ := hidden_run_formulas A B hb h hh
  refine ⟨D, C, k, fun n => ?_⟩
  let P := fun ℓ => ∃ fs : FullRunOutput q ℓ → CircuitFormula ℓ,
    (∀ o, formulaDepth (fs o) ≤ D) ∧
    (∀ o, formulaCost (fs o) ≤ C * (ℓ + 1) ^ k) ∧
    ∃ e : Bits ℓ ≃ Bits ℓ, ∀ seed o, formulaEval (fs o) seed =
      fullRunEncode (e seed, drivenPath A.step ℓ A.start (e seed)) o
  have hn : P (n / b * b + n % b) := hc (n / b) (n % b) (Nat.mod_lt n hb).le
  exact Eq.mp (congrArg P (Nat.div_add_mod' n b)) hn

end FSS23105365

-- From Solutions.FSS23105365_RunStateTests
set_option autoImplicit false
namespace FSS23105365

def runStateTestFormula {r n : ℕ} (fs : FullRunOutput r n → CircuitFormula n)
    (t : Fin (n + 1)) (p : Fin r → Bool) : CircuitFormula n :=
  formulaIndexedAny (fun z : Fin r =>
    if p z = true then fs (Sum.inr (t, z)) else .constant false)

theorem runStateTestFormula_eval {r n : ℕ} (fs : FullRunOutput r n → CircuitFormula n)
    (t : Fin (n + 1)) (p : Fin r → Bool) (seed w : Bits n) (γ : Path r n)
    (he : ∀ o, formulaEval (fs o) seed = fullRunEncode (w, γ) o) :
    formulaEval (runStateTestFormula fs t p) seed = p (γ t) := by
  apply Bool.eq_iff_iff.mpr
  rw [runStateTestFormula, formulaIndexedAny_eval]
  constructor
  · rintro ⟨z, hz⟩
    by_cases hp : p z = true
    · rw [if_pos hp, he] at hz
      change decide (γ t = z) = true at hz
      have heq := of_decide_eq_true hz
      exact heq ▸ hp
    · simp only [if_neg hp, formulaEval, Bool.false_eq_true] at hz
  · intro hp
    refine ⟨γ t, ?_⟩
    rw [if_pos hp, he]
    simp [fullRunEncode, pathEncode]

theorem runStateTestFormula_depth {r n : ℕ} (fs : FullRunOutput r n → CircuitFormula n)
    (t : Fin (n + 1)) (p : Fin r → Bool) (D : ℕ)
    (hd : ∀ o, formulaDepth (fs o) ≤ D) :
    formulaDepth (runStateTestFormula fs t p) ≤ max D 1 + 1 := by
  apply formulaIndexedAny_depth
  intro z
  split_ifs
  · exact (hd _).trans (Nat.le_max_left D 1)
  · exact Nat.le_max_right D 1

theorem runStateTestFormula_cost {r n : ℕ} (fs : FullRunOutput r n → CircuitFormula n)
    (t : Fin (n + 1)) (p : Fin r → Bool) (K : ℕ)
    (hk : ∀ o, formulaCost (fs o) ≤ K) :
    formulaCost (runStateTestFormula fs t p) ≤ r * (K + 2) + 1 := by
  have h := formulaIndexedAny_cost
    (fun z : Fin r => if p z = true then fs (Sum.inr (t, z)) else .constant false)
    (K + 1) (by
      intro z
      split_ifs
      · exact (hk _).trans (Nat.le_succ K)
      · change 1 ≤ K + 1
        omega)
  simpa only [runStateTestFormula, Fintype.card_fin, Nat.add_assoc] using h

end FSS23105365

-- From Solutions.FSS23105365_DFAObservationCircuits
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

def sampledRunIndex (v s n : ℕ) (i : Fin (n + 1)) : Fin (v + n * s + 1) :=
  ⟨v + s * i.val, by have := i.isLt; nlinarith⟩

theorem sampledPath_drivenPath {q r n : ℕ} (B : BinaryDFA r) (φ : Fin r → Fin q)
    (v s : ℕ) (w : Bits (v + n * s)) (i : Fin (n + 1)) :
    B.sampledPath φ v s w i =
      φ (drivenPath B.step (v + n * s) B.start w (sampledRunIndex v s n i)) := by
  rw [← drivenPath_prefix]
  rfl

/-- Sampled times and a fixed finite state projection add only a constant
depth layer. The original source length v+n*s is preserved exactly. -/
theorem dfa_observation_circuits {q r : ℕ} (B : BinaryDFA r) (φ : Fin r → Fin q)
    (v s : ℕ) :
    ∃ D C k : ℕ, ∀ n : ℕ, ∃ S : Circuit (Fin (n + 1) × Fin q),
      ∃ hbits : S.randomBits = v + n * s,
      S.depth ≤ D ∧ S.size ≤ C * (n + 1) ^ k ∧
      ∃ e : Bits (v + n * s) ≃ Bits (v + n * s),
        ∀ seed, S.eval (fun i => seed (Fin.cast hbits i)) =
          pathEncode (B.sampledPath φ v s (e seed)) := by
  obtain ⟨D, C, k, hc⟩ := exact_dfa_run_formulas B
  let G := C * (v + s + 1) ^ k
  let K := r * (G + 2) + 1
  refine ⟨max D 1 + 1, v + s + q * (K + 1), k + 1, fun n => ?_⟩
  obtain ⟨fs, hd, hs, e, he⟩ := hc (v + n * s)
  let ff := fun o : Fin (n + 1) × Fin q => runStateTestFormula fs
    (sampledRunIndex v s n o.1) (fun z => decide (φ z = o.2))
  have hdep : ∀ o, formulaDepth (ff o) ≤ max D 1 + 1 := fun o =>
    runStateTestFormula_depth fs _ _ D hd
  have hstate : ∀ o, formulaCost (fs o) ≤ G * (n + 1) ^ k := by
    intro o
    have hl : v + n * s + 1 ≤ (v + s + 1) * (n + 1) := by nlinarith
    have hp := Nat.mul_le_mul_left C (pow_le_pow_left' hl k)
    exact (hs o).trans (by simpa only [mul_pow, Nat.mul_assoc, G] using hp)
  have hcost : ∀ o, formulaCost (ff o) ≤ K * (n + 1) ^ k := by
    intro o
    have h := runStateTestFormula_cost fs (sampledRunIndex v s n o.1)
      (fun z => decide (φ z = o.2)) (G * (n + 1) ^ k) hstate
    have hp := Nat.one_le_pow' k n
    change formulaCost (ff o) ≤ (r * (G + 2) + 1) * (n + 1) ^ k
    nlinarith
  obtain ⟨S, hbits, hval, hD, hS⟩ := formula_fintype_family_circuit ff (max D 1 + 1) hdep
  refine ⟨S, hbits, hD, ?_, e, ?_⟩
  · have hsum : (∑ o, formulaCost (ff o)) ≤ ((n + 1) * q) * (K * (n + 1) ^ k) := by
      simpa using Finset.sum_le_sum (fun o (_ : o ∈ Finset.univ) => hcost o)
    have hsum' : (∑ o, formulaCost (ff o)) ≤ q * K * (n + 1) ^ (k + 1) := by
      simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hsum
    have hp : n + 1 ≤ (n + 1) ^ (k + 1) := by
      simpa only [pow_one] using pow_le_pow_right' (by omega : 1 ≤ n + 1)
        (show 1 ≤ k + 1 by omega)
    rw [hS, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    nlinarith
  · intro seed
    funext o
    rw [hval]
    change formulaEval (runStateTestFormula fs _ _) seed = _
    rw [runStateTestFormula_eval fs _ _ seed (e seed) _ (he seed)]
    rw [pathEncode, sampledPath_drivenPath]

end FSS23105365

-- From Solutions.FSS23105365_PathProjection
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

/-- Finite pushforward sums compose without assumptions on the weights. -/
theorem finite_pushforward_comp {α β γ : Type} [Fintype α] [Fintype β]
    [DecidableEq β] [DecidableEq γ] (f : α → β) (g : β → γ) (p : α → ℝ) (z : γ) :
    (∑ y, if g y = z then ∑ x, if f x = y then p x else 0 else 0) =
      ∑ x, if g (f x) = z then p x else 0 := by
  classical
  calc
    _ = ∑ y, ∑ x, if f x = y then (if g y = z then p x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : g y = z <;> simp [hy]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simp

theorem projectedPathLaw_comp {q r s n : ℕ} (M : MarkovChain s)
    (φ : Fin s → Fin r) (ψ : Fin r → Fin q) (γ : Path q n) :
    projectedPathLaw M (fun h => ψ (φ h)) γ =
      ∑ η : Path r n, if (fun i => ψ (η i)) = γ then projectedPathLaw M φ η else 0 := by
  exact (finite_pushforward_comp (fun ξ : Path s n => fun i => φ (ξ i))
    (fun η : Path r n => fun i => ψ (η i)) (pathLaw M) γ).symm

end FSS23105365

-- From Solutions.FSS23105365_PathWeights
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

/-- The same finite path product as `pathLaw`, on an arbitrary finite state
type. This permits the sigma-type state copies in the E.4 construction. -/
def finitePathWeight {H : Type} (μ : H → ℝ) (P : H → H → ℝ)
    {n : ℕ} (η : Fin (n + 1) → H) : ℝ :=
  μ (η 0) * ∏ i : Fin n, P (η i.castSucc) (η i.succ)

theorem pathLaw_eq_finitePathWeight {q n : ℕ} (M : MarkovChain q) (γ : Path q n) :
    pathLaw M γ = finitePathWeight M.initial M.transition γ := rfl

@[simp] theorem finitePathWeight_snoc {H : Type} (μ : H → ℝ) (P : H → H → ℝ)
    {n : ℕ} (η : Fin (n + 1) → H) (h : H) :
    finitePathWeight μ P (Fin.snoc η h) =
      finitePathWeight μ P η * P (η (Fin.last n)) h := by
  simp only [finitePathWeight, Fin.prod_univ_castSucc]
  simp only [← Fin.castSucc_succ, Fin.snoc_castSucc, Fin.snoc_last,
    Fin.succ_last, Fin.snoc_apply_zero]
  ring

theorem map_snoc {H Q : Type} (φ : H → Q) {n : ℕ}
    (η : Fin n → H) (h : H) :
    (fun i => φ ((Fin.snoc η h : Fin (n + 1) → H) i)) =
      Fin.snoc (fun i => φ (η i)) (φ h) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

/-- Joint mass of the observed path and the final hidden state. -/
def endpointPathMass {H Q : Type} [Fintype H] [DecidableEq H] [DecidableEq Q]
    (μ : H → ℝ) (P : H → H → ℝ) (φ : H → Q)
    {n : ℕ} (γ : Fin (n + 1) → Q) (h : H) : ℝ :=
  ∑ η : Fin (n + 1) → H,
    if (fun i => φ (η i)) = γ ∧ η (Fin.last n) = h then finitePathWeight μ P η else 0

theorem endpointPathMass_zero {H Q : Type} [Fintype H] [DecidableEq H] [DecidableEq Q]
    (μ : H → ℝ) (P : H → H → ℝ) (φ : H → Q) (γ : Fin 1 → Q) (h : H) :
    endpointPathMass μ P φ γ h = if φ h = γ 0 then μ h else 0 := by
  classical
  let e : H ≃ (Fin 1 → H) := (Equiv.funUnique (Fin 1) H).symm
  have he := e.sum_comp (fun η : Fin 1 → H =>
    if (fun i => φ (η i)) = γ ∧ η (Fin.last 0) = h then finitePathWeight μ P η else 0)
  rw [endpointPathMass, ← he]
  have heval (a : H) : e a = fun _ => a := rfl
  simp only [heval, finitePathWeight, Fin.prod_univ_zero, mul_one]
  have hfun (a : H) : (fun _ : Fin 1 => φ a) = γ ↔ φ a = γ 0 := by
    constructor
    · intro ha; exact congrFun ha 0
    · intro ha
      funext i
      have hi : i = 0 := by apply Fin.ext; omega
      simpa [hi] using ha
  simp only [hfun]
  simp [and_comm, ite_and]

theorem endpointPathMass_step_sum {H Q : Type} [Fintype H] [DecidableEq H] [DecidableEq Q]
    (μ : H → ℝ) (P : H → H → ℝ) (φ : H → Q)
    {n : ℕ} (γ : Fin (n + 1) → Q) (h : H) :
    (∑ a, endpointPathMass μ P φ γ a * P a h) =
      ∑ η : Fin (n + 1) → H, if (fun i => φ (η i)) = γ then
        finitePathWeight μ P η * P (η (Fin.last n)) h else 0 := by
  classical
  simp only [endpointPathMass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η _
  by_cases hη : (fun i => φ (η i)) = γ
  · simp [hη, ite_mul]
  · simp [hη]

theorem endpointPathMass_snoc {H Q : Type} [Fintype H] [DecidableEq H] [DecidableEq Q]
    (μ : H → ℝ) (P : H → H → ℝ) (φ : H → Q)
    {n : ℕ} (γ : Fin (n + 1) → Q) (q : Q) (h : H) :
    endpointPathMass μ P φ (Fin.snoc γ q) h =
      if φ h = q then ∑ a, endpointPathMass μ P φ γ a * P a h else 0 := by
  classical
  rw [endpointPathMass]
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 2) => H)).sum_comp]
  have heval (z : H × (Fin (n + 1) → H)) :
      (Fin.snocEquiv (fun _ : Fin (n + 2) => H)) z = Fin.snoc z.2 z.1 := rfl
  simp only [heval, map_snoc, Fin.snoc_inj,
    Fin.snoc_last, finitePathWeight_snoc]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single h]
  · rw [endpointPathMass_step_sum]
    by_cases hh : φ h = q
    · simp [hh]
    · simp [hh]
  · intro a _ ha
    simp [ha]
  · simp

/-- The fiber invariant in E.4, including zero-probability paths. Only the
initial masses and column margins are needed for this algebraic identity. -/
theorem endpointPathMass_fiber_invariant {H Q : Type} [Fintype H]
    [DecidableEq H] [DecidableEq Q]
    (μ : H → ℝ) (P : H → H → ℝ) (φ : H → Q)
    (μ₀ : Q → ℝ) (P₀ : Q → Q → ℝ) (w : Q → ℝ)
    (hw : ∀ q, w q ≠ 0)
    (hμ : ∀ h, μ h = μ₀ (φ h) / w (φ h))
    (hP : ∀ q h, (∑ a, if φ a = q then P a h else 0) =
      w q * P₀ q (φ h) / w (φ h))
    {n : ℕ} (γ : Fin (n + 1) → Q) (h : H) :
    endpointPathMass μ P φ γ h =
      if φ h = γ (Fin.last n) then finitePathWeight μ₀ P₀ γ / w (γ (Fin.last n)) else 0 := by
  classical
  induction n generalizing h with
  | zero =>
    rw [endpointPathMass_zero]
    simp only [finitePathWeight, Fin.prod_univ_zero, mul_one, Fin.last_zero]
    by_cases hh : φ h = γ 0
    · simp [hh, hμ]
    · simp [hh]
  | succ n ih =>
    rcases (Fin.snocEquiv (fun _ : Fin (n + 2) => Q)).surjective γ with ⟨⟨x, η⟩, rfl⟩
    have heval : (Fin.snocEquiv (fun _ : Fin (n + 2) => Q)) (x, η) =
        Fin.snoc η x := rfl
    rw [heval, Fin.snoc_last, endpointPathMass_snoc]
    by_cases hh : φ h = x
    · simp only [if_pos hh]
      simp_rw [ih]
      calc
        (∑ a, (if φ a = η (Fin.last n) then
            finitePathWeight μ₀ P₀ η / w (η (Fin.last n)) else 0) * P a h) =
            (finitePathWeight μ₀ P₀ η / w (η (Fin.last n))) *
              ∑ a, if φ a = η (Fin.last n) then P a h else 0 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          split_ifs <;> simp
        _ = _ := by
          rw [hP, hh, finitePathWeight_snoc]
          field_simp [hw]
    · simp [hh]

theorem sum_endpointPathMass {H Q : Type} [Fintype H] [DecidableEq H] [DecidableEq Q]
    (μ : H → ℝ) (P : H → H → ℝ) (φ : H → Q)
    {n : ℕ} (γ : Fin (n + 1) → Q) :
    (∑ h, endpointPathMass μ P φ γ h) =
      ∑ η : Fin (n + 1) → H,
        if (fun i => φ (η i)) = γ then finitePathWeight μ P η else 0 := by
  classical
  simp only [endpointPathMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η _
  by_cases hη : (fun i => φ (η i)) = γ <;> simp [hη]

/-- Summing the invariant over the last fiber proves equality of the
entire projected path distribution, as required in E.4. -/
theorem projected_finitePathWeight_eq {H Q : Type} [Fintype H]
    [DecidableEq H] [DecidableEq Q]
    (μ : H → ℝ) (P : H → H → ℝ) (φ : H → Q)
    (μ₀ : Q → ℝ) (P₀ : Q → Q → ℝ) (w : Q → ℝ)
    (hw : ∀ q, w q ≠ 0)
    (hμ : ∀ h, μ h = μ₀ (φ h) / w (φ h))
    (hP : ∀ q h, (∑ a, if φ a = q then P a h else 0) =
      w q * P₀ q (φ h) / w (φ h))
    (hcard : ∀ q, (Fintype.card {h : H // φ h = q} : ℝ) = w q)
    {n : ℕ} (γ : Fin (n + 1) → Q) :
    (∑ η : Fin (n + 1) → H,
      if (fun i => φ (η i)) = γ then finitePathWeight μ P η else 0) =
        finitePathWeight μ₀ P₀ γ := by
  rw [← sum_endpointPathMass]
  simp_rw [endpointPathMass_fiber_invariant μ P φ μ₀ P₀ w hw hμ hP]
  classical
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Fintype.card_subtype, hcard]
  exact mul_div_cancel₀ _ (hw _)

end FSS23105365

-- From Solutions.FSS23105365_RationalPathFacts
set_option autoImplicit false
namespace FSS23105365

theorem dyadic_is_rational {x : ℝ} (hx : Dyadic x) : ∃ a : ℚ, (a : ℝ) = x := by
  rcases hx with ⟨a, k, rfl⟩
  exact ⟨(a : ℚ) / 2 ^ k, by push_cast; rfl⟩

/-- Reachability with positive probability, as used when deleting
unreachable states in the first sentence of the E.4 proof. -/
def PositivelyReachable {q : ℕ} (M : MarkovChain q) (x : Fin q) : Prop :=
  ∃ n : ℕ, ∃ γ : Path q n, γ (Fin.last n) = x ∧ 0 < pathLaw M γ

theorem positivelyReachable_of_initial {q : ℕ} (M : MarkovChain q) (x : Fin q)
    (hx : 0 < M.initial x) : PositivelyReachable M x := by
  refine ⟨0, fun _ => x, rfl, ?_⟩
  simpa [pathLaw] using hx

theorem positivelyReachable_step {q : ℕ} (M : MarkovChain q) (x y : Fin q)
    (hx : PositivelyReachable M x) (hxy : 0 < M.transition x y) :
    PositivelyReachable M y := by
  obtain ⟨n, γ, hlast, hγ⟩ := hx
  refine ⟨n + 1, Fin.snoc γ y, Fin.snoc_last _ _, ?_⟩
  rw [pathLaw_eq_finitePathWeight, finitePathWeight_snoc, hlast,
    ← pathLaw_eq_finitePathWeight]
  exact mul_pos hγ hxy

/-- Rationality in E.4 follows by dividing the dyadic probability of an
extended path by the positive dyadic probability of its prefix. The
transition itself is not assumed dyadic. -/
theorem pathDyadic_transition_rational {q : ℕ} (M : MarkovChain q)
    (hM : PathDyadic M) (x y : Fin q) (hx : PositivelyReachable M x) :
    ∃ a : ℚ, (a : ℝ) = M.transition x y := by
  obtain ⟨n, γ, hlast, hγ⟩ := hx
  obtain ⟨a, ha⟩ := dyadic_is_rational (hM (n + 1) (Fin.snoc γ y))
  obtain ⟨b, hb⟩ := dyadic_is_rational (hM n γ)
  refine ⟨a / b, ?_⟩
  rw [Rat.cast_div, ha, hb, pathLaw_eq_finitePathWeight, finitePathWeight_snoc, hlast,
    ← pathLaw_eq_finitePathWeight]
  field_simp [ne_of_gt hγ]

theorem pathDyadic_initial_dyadic {q : ℕ} (M : MarkovChain q)
    (hM : PathDyadic M) (x : Fin q) : Dyadic (M.initial x) := by
  simpa [pathLaw] using hM 0 (fun _ => x)

end FSS23105365

-- From Solutions.FSS23105365_DyadicValuations
set_option autoImplicit false
namespace FSS23105365

theorem dyadic_rat_cast_iff (x : ℚ) :
    Dyadic (x : ℝ) ↔ ∃ a k : ℕ, x = (a : ℚ) / 2 ^ k := by
  constructor
  · rintro ⟨a, k, hx⟩
    refine ⟨a, k, ?_⟩
    apply Rat.cast_injective (α := ℝ)
    simpa using hx
  · rintro ⟨a, k, rfl⟩
    exact ⟨a, k, by push_cast; rfl⟩

/-- A nonnegative rational whose reduced denominator is a power of two is
dyadic in the real-valued probability definition used by the mission. -/
theorem dyadic_of_rat_den_pow (x : ℚ) (hx : 0 ≤ x) (k : ℕ)
    (hden : x.den = 2 ^ k) : Dyadic (x : ℝ) := by
  have hn : (x.num.toNat : ℝ) = (x.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hx)
  refine ⟨x.num.toNat, k, ?_⟩
  rw [Rat.cast_def, hden, hn]
  simp

/-- Odd-prime valuations of nonzero dyadic probabilities are nonnegative,
the fact that makes the minimum in E.4 well-founded. -/
theorem dyadic_odd_padicVal_nonneg (x : ℚ) (hx : Dyadic (x : ℝ))
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : 0 ≤ padicValRat p x := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, k, rfl⟩ := (dyadic_rat_cast_iff x).mp hx
  by_cases ha : a = 0
  · simp [ha]
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha
  have ht : padicValRat p (2 : ℚ) = 0 := by
    change padicValRat p ((2 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat, padicValNat_primes hp2]
    simp
  rw [padicValRat.div ha' (pow_ne_zero _ (by norm_num)), padicValRat.pow, ht]
  simp

/-- The converse number-theoretic criterion needed in E.4: nonnegative
valuations at every prime other than two exclude every odd factor from
the reduced denominator. -/
theorem dyadic_of_odd_padicVal_nonneg (x : ℚ) (hx : 0 ≤ x)
    (hval : ∀ p : ℕ, p.Prime → p ≠ 2 → 0 ≤ padicValRat p x) :
    Dyadic (x : ℝ) := by
  have hnodvd (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ x.den := by
    intro hd
    let : Fact p.Prime := ⟨hp⟩
    have hn : ¬ p ∣ x.num.natAbs := by
      intro hn
      have hg : p ∣ 1 := by
        simpa only [x.reduced] using Nat.dvd_gcd hn hd
      exact hp.ne_one (Nat.dvd_one.mp hg)
    have hvn : padicValInt p x.num = 0 := padicValNat.eq_zero_of_not_dvd hn
    have hvd : 1 ≤ padicValNat p x.den := one_le_padicValNat_of_dvd x.den_ne_zero hd
    have hv := hval p hp hp2
    rw [padicValRat_def, hvn] at hv
    omega
  have hfac : x.den.factorization = Finsupp.single 2 (x.den.factorization 2) := by
    ext p
    by_cases hp2 : p = 2
    · subst p; simp
    rw [Finsupp.single_eq_of_ne hp2]
    by_cases hp : p.Prime
    · exact Nat.factorization_eq_zero_of_not_dvd (hnodvd p hp hp2)
    · exact Nat.factorization_eq_zero_of_not_prime _ hp
  have hden : x.den = 2 ^ x.den.factorization 2 := by
    calc
      x.den = x.den.factorization.prod (· ^ ·) :=
        (Nat.prod_factorization_pow_eq_self x.den_ne_zero).symm
      _ = 2 ^ x.den.factorization 2 := by rw [hfac]; simp
  exact dyadic_of_rat_den_pow x hx _ hden

end FSS23105365

-- From Solutions.FSS23105365_DyadicWeightExistence
set_option autoImplicit false
namespace FSS23105365

/-- The odd-prime valuation minimum in E.4 is attained: its possible
values form a nonempty subset of the natural numbers. -/
theorem exists_minimum_odd_valuation (S : Set ℚ) (hne : S.Nonempty)
    (hd : ∀ a ∈ S, Dyadic (a : ℝ)) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ k : ℕ, (∃ a ∈ S, padicValRat p a = (k : ℤ)) ∧
      ∀ a ∈ S, (k : ℤ) ≤ padicValRat p a := by
  classical
  have hn (a : ℚ) (ha : a ∈ S) : 0 ≤ padicValRat p a :=
    dyadic_odd_padicVal_nonneg a (hd a ha) p hp hp2
  have hex : ∃ k : ℕ, ∃ a ∈ S, padicValRat p a = (k : ℤ) := by
    obtain ⟨a, ha⟩ := hne
    exact ⟨(padicValRat p a).toNat, a, ha, (Int.toNat_of_nonneg (hn a ha)).symm⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, fun a ha => ?_⟩
  have hb : Nat.find hex ≤ (padicValRat p a).toNat :=
    Nat.find_min' hex ⟨a, ha, (Int.toNat_of_nonneg (hn a ha)).symm⟩
  calc
    (Nat.find hex : ℤ) ≤ ((padicValRat p a).toNat : ℤ) := by exact_mod_cast hb
    _ = padicValRat p a := Int.toNat_of_nonneg (hn a ha)

/-- The minima over a set of dyadic probabilities are the odd-prime
valuations of one positive integer. A single member bounds their support. -/
theorem exists_dyadic_set_weight (S : Set ℚ) (hne : S.Nonempty)
    (hd : ∀ a ∈ S, Dyadic (a : ℝ)) :
    ∃ w : ℕ, 0 < w ∧ ∀ p : ℕ, p.Prime → p ≠ 2 →
      (∃ a ∈ S, padicValRat p a = padicValRat p (w : ℚ)) ∧
      ∀ a ∈ S, padicValRat p (w : ℚ) ≤ padicValRat p a := by
  classical
  have hex (p : ℕ) : ∃ k : ℕ,
      ((p.Prime ∧ p ≠ 2) →
        (∃ a ∈ S, padicValRat p a = (k : ℤ)) ∧ ∀ a ∈ S, (k : ℤ) ≤ padicValRat p a) ∧
      (¬ (p.Prime ∧ p ≠ 2) → k = 0) := by
    by_cases hp : p.Prime ∧ p ≠ 2
    · obtain ⟨k, hk, hb⟩ := exists_minimum_odd_valuation S hne hd p hp.1 hp.2
      exact ⟨k, fun _ => ⟨hk, hb⟩, fun h => (h hp).elim⟩
    · exact ⟨0, fun h => (hp h).elim, fun _ => rfl⟩
  choose a ha hz using hex
  obtain ⟨b, hb⟩ := hne
  have hsupp (p : ℕ) (hap : a p ≠ 0) : p ∈ b.num.natAbs.factorization.support := by
    have hp : p.Prime ∧ p ≠ 2 := by
      by_contra hp
      exact hap (hz p hp)
    have hbound := (ha p hp).2 b hb
    have hv : padicValNat p b.num.natAbs ≠ 0 := by
      rw [padicValRat_def, padicValInt] at hbound
      omega
    rw [Finsupp.mem_support_iff, Nat.factorization_def _ hp.1]
    exact hv
  let f : ℕ →₀ ℕ := Finsupp.onFinset b.num.natAbs.factorization.support a hsupp
  have hf (p : ℕ) : f p = a p := rfl
  have hfprime (p : ℕ) (hp : p ∈ f.support) : p.Prime := by
    have hap : a p ≠ 0 := by simpa only [hf] using Finsupp.mem_support_iff.mp hp
    by_contra hnp
    exact hap (hz p (fun h => hnp h.1))
  let w : ℕ := f.prod (· ^ ·)
  have hw : 0 < w := by
    apply Finset.prod_pos
    intro p hp
    exact pow_pos (hfprime p hp).pos _
  have hwfac : w.factorization = f := Nat.prod_pow_factorization_eq_self hfprime
  have hwval (p : ℕ) (hp : p.Prime) : padicValRat p (w : ℚ) = (a p : ℤ) := by
    rw [padicValRat.of_nat, ← Nat.factorization_def _ hp, hwfac, hf]
  refine ⟨w, hw, fun p hp hp2 => ?_⟩
  rw [hwval p hp]
  exact ha p ⟨hp, hp2⟩

/-- Abstract form of the valuation construction in E.4. The sets `S q`
will be the positive path probabilities ending at state `q`. -/
theorem exists_weights_of_dyadic_path_sets {Q : Type} (S : Q → Set ℚ)
    (hne : ∀ q, (S q).Nonempty)
    (hpos : ∀ q a, a ∈ S q → 0 < a)
    (hd : ∀ q a, a ∈ S q → Dyadic (a : ℝ))
    (μ : Q → ℚ) (P : Q → Q → ℚ)
    (hμn : ∀ q, 0 ≤ μ q) (hPn : ∀ q r, 0 ≤ P q r)
    (hμmem : ∀ q, 0 < μ q → μ q ∈ S q)
    (hclosed : ∀ q r a, a ∈ S q → 0 < P q r → a * P q r ∈ S r) :
    ∃ w : Q → ℕ, (∀ q, 0 < w q) ∧
      (∀ q, Dyadic ((μ q / (w q : ℚ) : ℚ) : ℝ)) ∧
      (∀ q r, Dyadic ((((w q : ℚ) * P q r) / (w r : ℚ) : ℚ) : ℝ)) := by
  classical
  choose w hw hmin using fun q => exists_dyadic_set_weight (S q) (hne q) (hd q)
  have hwn (q : Q) : (w q : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hw q))
  refine ⟨w, hw, fun q => ?_, fun q r => ?_⟩
  · by_cases hμ : μ q = 0
    · simpa [hμ] using dyadic_zero
    apply dyadic_of_odd_padicVal_nonneg _ (div_nonneg (hμn q) (Nat.cast_nonneg _))
    intro p hp hp2
    let : Fact p.Prime := ⟨hp⟩
    rw [padicValRat.div hμ (hwn q)]
    apply sub_nonneg.mpr
    exact (hmin q p hp hp2).2 _ (hμmem q (lt_of_le_of_ne (hμn q) (Ne.symm hμ)))
  · by_cases hP : P q r = 0
    · simpa [hP] using dyadic_zero
    apply dyadic_of_odd_padicVal_nonneg _
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (hPn q r)) (Nat.cast_nonneg _))
    intro p hp hp2
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨a, ha, hva⟩ := (hmin q p hp hp2).1
    have hnext := (hmin r p hp hp2).2 _
      (hclosed q r a ha (lt_of_le_of_ne (hPn q r) (Ne.symm hP)))
    rw [padicValRat.mul (ne_of_gt (hpos q a ha)) hP, hva] at hnext
    rw [padicValRat.div (mul_ne_zero (hwn q) hP) (hwn r), padicValRat.mul (hwn q) hP]
    exact sub_nonneg.mpr hnext

end FSS23105365

-- From Solutions.FSS23105365_DyadicLiftKernel
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

abbrev StateCopies {q : ℕ} (w : Fin q → ℕ) := (x : Fin q) × Fin (w x)

/-- Given the weights obtained in the first half of E.4, construct the
dyadic transition kernel with exactly the row and column margins used by
the fiber invariant. Existence of those weights remains a separate target. -/
theorem exists_dyadic_lift_kernel {q : ℕ} (M : MarkovChain q) (w : Fin q → ℕ)
    (hw : ∀ x, 0 < w x)
    (hd : ∀ x y, Dyadic ((w x : ℝ) * M.transition x y / (w y : ℝ))) :
    ∃ T : StateCopies w → StateCopies w → ℝ,
      (∀ h h', Dyadic (T h h')) ∧
      (∀ h h', 0 ≤ T h h') ∧
      (∀ h, ∑ h', T h h' = 1) ∧
      (∀ x (h' : StateCopies w), ∑ i : Fin (w x), T ⟨x, i⟩ h' =
        (w x : ℝ) * M.transition x h'.1 / (w h'.1 : ℝ)) := by
  classical
  obtain ⟨k, hk, a, ha⟩ := dyadic_common_denominator
    (fun xy : Fin q × Fin q => (w xy.1 : ℝ) * M.transition xy.1 xy.2 / (w xy.2 : ℝ))
    (fun xy => hd xy.1 xy.2)
  have hden : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hwn (x : Fin q) : (w x : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hw x))
  have ha' (x y : Fin q) : (a (x, y) : ℝ) =
      ((w x : ℝ) * M.transition x y / (w y : ℝ)) * 2 ^ k :=
    ((eq_div_iff hden).mp (ha (x, y))).symm
  have htot (x : Fin q) : (∑ h' : StateCopies w, a (x, h'.1)) = w x * 2 ^ k := by
    have hr : (∑ h' : StateCopies w, (a (x, h'.1) : ℝ)) = (w x : ℝ) * 2 ^ k := by
      rw [Fintype.sum_sigma]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc
        (∑ y, (w y : ℝ) * (a (x, y) : ℝ)) =
            ((w x : ℝ) * 2 ^ k) * ∑ y, M.transition x y := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          rw [ha']
          field_simp [hwn]
        _ = (w x : ℝ) * 2 ^ k := by rw [M.row_sum, mul_one]
    exact_mod_cast hr
  have hmat (x : Fin q) := exists_integer_matrix_with_margins
    (α := Fin (w x)) (β := StateCopies w) (2 ^ k) (fun h' => a (x, h'.1))
      (by simpa using htot x)
  choose C hrow hcol using hmat
  let T : StateCopies w → StateCopies w → ℝ :=
    fun h h' => (C h.1 h.2 h' : ℝ) / 2 ^ k
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · intro h h'; exact ⟨C h.1 h.2 h', k, rfl⟩
  · intro h h'; exact div_nonneg (Nat.cast_nonneg _) (le_of_lt (pow_pos (by norm_num) _))
  · intro h
    change (∑ h', (C h.1 h.2 h' : ℝ) / 2 ^ k) = 1
    simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum, hrow]
    simp [hden]
  · intro x h'
    change (∑ i : Fin (w x), (C x i h' : ℝ) / 2 ^ k) = _
    simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum, hcol]
    exact (ha (x, h'.1)).symm

end FSS23105365

-- From Solutions.FSS23105365_DyadicLiftFromWeights
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

/-- The second half of E.4, starting from its explicit integer weights.
All finite-chain normalization and the full projected path law are proved;
the existence of the weights is deliberately not assumed to be E.4 itself. -/
theorem dyadic_lift_from_weights {q : ℕ} (hq : 0 < q) (M : MarkovChain q)
    (w : Fin q → ℕ) (hw : ∀ x, 0 < w x)
    (hinit : ∀ x, Dyadic (M.initial x / (w x : ℝ)))
    (htrans : ∀ x y, Dyadic ((w x : ℝ) * M.transition x y / (w y : ℝ))) :
    ∃ r : ℕ, 0 < r ∧ ∃ N : MarkovChain r, ∃ φ : Fin r → Fin q,
      TransitionDyadic N ∧
      ∀ n : ℕ, ∀ γ : Path q n, projectedPathLaw N φ γ = pathLaw M γ := by
  classical
  obtain ⟨T, hTd, hTn, hTr, hTc⟩ := exists_dyadic_lift_kernel M w hw htrans
  let H := StateCopies w
  let μ : H → ℝ := fun h => M.initial h.1 / (w h.1 : ℝ)
  have hwn (x : Fin q) : (w x : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hw x))
  have hμn (h : H) : 0 ≤ μ h :=
    div_nonneg (M.initial_nonneg h.1) (Nat.cast_nonneg _)
  have hμs : ∑ h : H, μ h = 1 := by
    change (∑ h : StateCopies w, M.initial h.1 / (w h.1 : ℝ)) = 1
    rw [Fintype.sum_sigma]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    convert M.initial_sum using 1
    apply Finset.sum_congr rfl
    intro x _
    field_simp [hwn]
  let e : H ≃ Fin (Fintype.card H) := Fintype.equivFin H
  let N : MarkovChain (Fintype.card H) :=
    { initial := fun h => μ (e.symm h)
      transition := fun h h' => T (e.symm h) (e.symm h')
      initial_nonneg := fun h => hμn (e.symm h)
      transition_nonneg := fun h h' => hTn (e.symm h) (e.symm h')
      initial_sum := by rw [e.symm.sum_comp]; exact hμs
      row_sum := fun h => by rw [e.symm.sum_comp]; exact hTr (e.symm h) }
  let φ : Fin (Fintype.card H) → Fin q := fun h => (e.symm h).1
  have hr : 0 < Fintype.card H := Fintype.card_pos_iff.mpr
    ⟨⟨⟨0, hq⟩, ⟨0, hw ⟨0, hq⟩⟩⟩⟩
  refine ⟨Fintype.card H, hr, N, φ, ⟨fun h => hinit (e.symm h).1,
    fun h h' => hTd (e.symm h) (e.symm h')⟩, fun n γ => ?_⟩
  have hcols (x : Fin q) (h : H) :
      (∑ a : H, if a.1 = x then T a h else 0) =
        (w x : ℝ) * M.transition x h.1 / (w h.1 : ℝ) := by
    change (∑ a : StateCopies w, if a.1 = x then T a h else 0) = _
    rw [Fintype.sum_sigma, Finset.sum_eq_single x]
    · simpa using hTc x h
    · intro y _ hy; simp [hy]
    · simp
  have hcard (x : Fin q) : (Fintype.card {h : H // h.1 = x} : ℝ) = (w x : ℝ) := by
    exact_mod_cast (show Fintype.card {h : H // h.1 = x} = w x from by
      simpa only [Fintype.card_fin] using Fintype.card_congr
        (Equiv.sigmaSubtype (β := fun y : Fin q => Fin (w y)) x))
  let ep : (Fin (n + 1) → H) ≃ Path (Fintype.card H) n :=
    Equiv.arrowCongr (Equiv.refl _) e
  rw [projectedPathLaw, ← ep.sum_comp]
  calc
    (∑ η : Fin (n + 1) → H,
      if (fun i => φ (ep η i)) = γ then pathLaw N (ep η) else 0) =
        ∑ η : Fin (n + 1) → H,
          if (fun i => (η i).1) = γ then finitePathWeight μ T η else 0 := by
      apply Finset.sum_congr rfl
      intro η _
      simp [ep, φ, N, Equiv.arrowCongr, Function.comp_def, pathLaw, finitePathWeight]
      rfl
    _ = pathLaw M γ := by
      rw [pathLaw_eq_finitePathWeight]
      exact projected_finitePathWeight_eq μ T (fun h : H => h.1)
        M.initial M.transition (fun x => (w x : ℝ)) hwn (fun _ => rfl) hcols hcard γ

end FSS23105365

-- From Solutions.FSS23105365_DyadicReachableWeights
set_option autoImplicit false
namespace FSS23105365

/-- The integer weights in E.4 exist after unreachable states have been
removed. Positive path probabilities are used exactly as in the paper. -/
theorem pathDyadic_weights_of_reachable {q : ℕ} (M : MarkovChain q)
    (hM : PathDyadic M) (hreach : ∀ x, PositivelyReachable M x) :
    ∃ w : Fin q → ℕ, (∀ x, 0 < w x) ∧
      (∀ x, Dyadic (M.initial x / (w x : ℝ))) ∧
      (∀ x y, Dyadic ((w x : ℝ) * M.transition x y / (w y : ℝ))) := by
  classical
  choose μ hμ using fun x => dyadic_is_rational (pathDyadic_initial_dyadic M hM x)
  choose P hP using fun x y => pathDyadic_transition_rational M hM x y (hreach x)
  let S : Fin q → Set ℚ := fun x =>
    {a | ∃ n : ℕ, ∃ γ : Path q n,
      γ (Fin.last n) = x ∧ 0 < pathLaw M γ ∧ (a : ℝ) = pathLaw M γ}
  have hne (x : Fin q) : (S x).Nonempty := by
    obtain ⟨n, γ, hlast, hpos⟩ := hreach x
    obtain ⟨a, ha⟩ := dyadic_is_rational (hM n γ)
    exact ⟨a, n, γ, hlast, hpos, ha⟩
  have hpos (x : Fin q) (a : ℚ) (ha : a ∈ S x) : 0 < a := by
    obtain ⟨n, γ, _, hp, heq⟩ := ha
    have : (0 : ℝ) < (a : ℝ) := by rw [heq]; exact hp
    exact_mod_cast this
  have hd (x : Fin q) (a : ℚ) (ha : a ∈ S x) : Dyadic (a : ℝ) := by
    obtain ⟨n, γ, _, _, heq⟩ := ha
    rw [heq]
    exact hM n γ
  have hμn (x : Fin q) : 0 ≤ μ x := by
    have : (0 : ℝ) ≤ (μ x : ℝ) := by rw [hμ]; exact M.initial_nonneg x
    exact_mod_cast this
  have hPn (x y : Fin q) : 0 ≤ P x y := by
    have : (0 : ℝ) ≤ (P x y : ℝ) := by rw [hP]; exact M.transition_nonneg x y
    exact_mod_cast this
  have hμmem (x : Fin q) (hx : 0 < μ x) : μ x ∈ S x := by
    refine ⟨0, fun _ => x, rfl, ?_, ?_⟩
    · have : (0 : ℝ) < (μ x : ℝ) := by exact_mod_cast hx
      simpa [pathLaw, hμ] using this
    · simpa [pathLaw] using hμ x
  have hclosed (x y : Fin q) (a : ℚ) (ha : a ∈ S x) (hxy : 0 < P x y) :
      a * P x y ∈ S y := by
    obtain ⟨n, γ, hlast, hγ, heq⟩ := ha
    have hPpos : 0 < M.transition x y := by
      rw [← hP]
      exact_mod_cast hxy
    have hnext : pathLaw M (Fin.snoc γ y) = pathLaw M γ * M.transition x y := by
      rw [pathLaw_eq_finitePathWeight, finitePathWeight_snoc, hlast,
        ← pathLaw_eq_finitePathWeight]
    refine ⟨n + 1, Fin.snoc γ y, Fin.snoc_last _ _, ?_, ?_⟩
    · rw [hnext]; exact mul_pos hγ hPpos
    · rw [Rat.cast_mul, heq, hP, hnext]
  obtain ⟨w, hw, hwi, hwt⟩ := exists_weights_of_dyadic_path_sets S hne hpos hd
    μ P hμn hPn hμmem hclosed
  refine ⟨w, hw, fun x => ?_, fun x y => ?_⟩
  · simpa only [Rat.cast_div, Rat.cast_natCast, hμ] using hwi x
  · simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, hP] using hwt x y

/-- E.4 for a chain all of whose states are positively reachable. -/
theorem dyadic_lift_of_all_reachable {q : ℕ} (hq : 0 < q) (M : MarkovChain q)
    (hM : PathDyadic M) (hreach : ∀ x, PositivelyReachable M x) :
    ∃ r : ℕ, 0 < r ∧ ∃ N : MarkovChain r, ∃ φ : Fin r → Fin q,
      TransitionDyadic N ∧
      ∀ n : ℕ, ∀ γ : Path q n, projectedPathLaw N φ γ = pathLaw M γ := by
  obtain ⟨w, hw, hi, ht⟩ := pathDyadic_weights_of_reachable M hM hreach
  exact dyadic_lift_from_weights hq M w hw hi ht

end FSS23105365

-- From Solutions.FSS23105365_PathReachability
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

theorem pathLaw_nonneg {q n : ℕ} (M : MarkovChain q) (γ : Path q n) :
    0 ≤ pathLaw M γ := by
  apply mul_nonneg (M.initial_nonneg _)
  exact Finset.prod_nonneg (fun _ _ => M.transition_nonneg _ _)

theorem positive_path_states_reachable {q n : ℕ} (M : MarkovChain q)
    (γ : Path q n) (hγ : 0 < pathLaw M γ) (i : Fin (n + 1)) :
    PositivelyReachable M (γ i) := by
  induction n with
  | zero =>
    have hi : i = 0 := by apply Fin.ext; omega
    subst i
    apply positivelyReachable_of_initial
    simpa [pathLaw] using hγ
  | succ n ih =>
    rcases (Fin.snocEquiv (fun _ : Fin (n + 2) => Fin q)).surjective γ with ⟨⟨x, η⟩, rfl⟩
    have heval : (Fin.snocEquiv (fun _ : Fin (n + 2) => Fin q)) (x, η) =
        Fin.snoc η x := rfl
    rw [heval] at hγ ⊢
    have hprod : 0 < pathLaw M η * M.transition (η (Fin.last n)) x := by
      simpa only [pathLaw_eq_finitePathWeight, finitePathWeight_snoc] using hγ
    have hη : 0 < pathLaw M η := by
      rcases mul_pos_iff.mp hprod with h | h
      · exact h.1
      · exact (not_lt_of_ge (pathLaw_nonneg M η) h.1).elim
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact ⟨n + 1, Fin.snoc η x, rfl, hγ⟩
    · simpa using ih η hη j

theorem initial_zero_of_not_reachable {q : ℕ} (M : MarkovChain q) (x : Fin q)
    (hx : ¬ PositivelyReachable M x) : M.initial x = 0 := by
  apply le_antisymm _ (M.initial_nonneg x)
  exact le_of_not_gt (fun h => hx (positivelyReachable_of_initial M x h))

theorem transition_zero_to_unreachable {q : ℕ} (M : MarkovChain q) (x y : Fin q)
    (hx : PositivelyReachable M x) (hy : ¬ PositivelyReachable M y) :
    M.transition x y = 0 := by
  apply le_antisymm _ (M.transition_nonneg x y)
  exact le_of_not_gt (fun h => hy (positivelyReachable_step M x y hx h))

theorem exists_positivelyReachable {q : ℕ} (M : MarkovChain q) :
    ∃ x, PositivelyReachable M x := by
  by_contra h
  push Not at h
  have hz : ∑ x, M.initial x = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact initial_zero_of_not_reachable M x (h x)
  rw [M.initial_sum] at hz
  exact one_ne_zero hz

end FSS23105365

-- From Solutions.FSS23105365_ReachableRestriction
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

theorem sum_subtype_of_zero_outside {α : Type} [Fintype α] (p : α → Prop)
    [DecidablePred p] (f : α → ℝ) (hf : ∀ x, ¬ p x → f x = 0) :
    (∑ x : {x // p x}, f x) = ∑ x, f x := by
  have hz : (∑ x : {x // ¬ p x}, f x) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact hf x x.property
  simpa only [hz, add_zero] using Fintype.sum_subtype_add_sum_subtype p f

theorem pathLaw_of_state_embedding {q r n : ℕ} (M : MarkovChain q) (N : MarkovChain r)
    (ψ : Fin r → Fin q)
    (hi : ∀ x, N.initial x = M.initial (ψ x))
    (ht : ∀ x y, N.transition x y = M.transition (ψ x) (ψ y)) (η : Path r n) :
    pathLaw N η = pathLaw M (fun i => ψ (η i)) := by
  simp only [pathLaw, hi, ht]

/-- An injective state restriction preserves the whole path law when it
contains every state on each positive-probability path. -/
theorem projectedPathLaw_of_state_embedding {q r : ℕ} (M : MarkovChain q) (N : MarkovChain r)
    (ψ : Fin r → Fin q) (hψ : Function.Injective ψ)
    (hi : ∀ x, N.initial x = M.initial (ψ x))
    (ht : ∀ x y, N.transition x y = M.transition (ψ x) (ψ y))
    (hs : ∀ n (γ : Path q n), 0 < pathLaw M γ → ∀ i, ∃ x, ψ x = γ i)
    (n : ℕ) (γ : Path q n) : projectedPathLaw N ψ γ = pathLaw M γ := by
  classical
  by_cases hex : ∃ η : Path r n, (fun i => ψ (η i)) = γ
  · obtain ⟨η, hη⟩ := hex
    rw [projectedPathLaw, Finset.sum_eq_single η]
    · rw [if_pos hη, pathLaw_of_state_embedding M N ψ hi ht, hη]
    · intro η' _ hne
      apply if_neg
      intro heq
      apply hne
      funext i
      apply hψ
      exact (congrFun heq i).trans (congrFun hη i).symm
    · simp
  · have hz : pathLaw M γ = 0 := by
      apply le_antisymm _ (pathLaw_nonneg M γ)
      apply le_of_not_gt
      intro hpos
      choose η hη using hs n γ hpos
      exact hex ⟨η, funext hη⟩
    rw [hz, projectedPathLaw]
    apply Finset.sum_eq_zero
    intro η _
    exact if_neg (fun h => hex ⟨η, h⟩)

/-- Delete precisely the states unreachable from the initial support.
The finite restricted chain is normalized, all its states are reachable,
and its coordinatewise projection has the original full trajectory law. -/
theorem exists_reachable_restriction {q : ℕ} (M : MarkovChain q) :
    ∃ r : ℕ, 0 < r ∧ ∃ N : MarkovChain r, ∃ ψ : Fin r → Fin q,
      (∀ x, PositivelyReachable N x) ∧
      (∀ n (η : Path r n), pathLaw N η = pathLaw M (fun i => ψ (η i))) ∧
      (∀ n (γ : Path q n), projectedPathLaw N ψ γ = pathLaw M γ) := by
  classical
  let H := {x : Fin q // PositivelyReachable M x}
  let e : H ≃ Fin (Fintype.card H) := Fintype.equivFin H
  let ψ : Fin (Fintype.card H) → Fin q := fun x => (e.symm x).val
  have hψ : Function.Injective ψ := Subtype.val_injective.comp e.symm.injective
  have hμ : (∑ x : H, M.initial x.val) = 1 := by
    rw [sum_subtype_of_zero_outside (PositivelyReachable M) M.initial
      (initial_zero_of_not_reachable M), M.initial_sum]
  have hP (x : H) : (∑ y : H, M.transition x.val y.val) = 1 := by
    rw [sum_subtype_of_zero_outside (PositivelyReachable M) (M.transition x.val)
      (fun y hy => transition_zero_to_unreachable M x.val y x.property hy), M.row_sum]
  let N : MarkovChain (Fintype.card H) :=
    { initial := fun x => M.initial (ψ x)
      transition := fun x y => M.transition (ψ x) (ψ y)
      initial_nonneg := fun x => M.initial_nonneg (ψ x)
      transition_nonneg := fun x y => M.transition_nonneg (ψ x) (ψ y)
      initial_sum := by
        change (∑ x, M.initial (e.symm x).val) = 1
        exact (e.symm.sum_comp (fun x : H => M.initial x.val)).trans hμ
      row_sum := fun x => by
        change (∑ y, M.transition (ψ x) (e.symm y).val) = 1
        exact (e.symm.sum_comp (fun y : H => M.transition (ψ x) y.val)).trans
          (hP (e.symm x)) }
  have hr : 0 < Fintype.card H := by
    obtain ⟨x, hx⟩ := exists_positivelyReachable M
    exact Fintype.card_pos_iff.mpr ⟨⟨x, hx⟩⟩
  have hmap (n : ℕ) (η : Path (Fintype.card H) n) :
      pathLaw N η = pathLaw M (fun i => ψ (η i)) :=
    pathLaw_of_state_embedding M N ψ (fun _ => rfl) (fun _ _ => rfl) η
  have hlift (n : ℕ) (γ : Path q n) (hp : 0 < pathLaw M γ) :
      ∃ η : Path (Fintype.card H) n, (fun i => ψ (η i)) = γ := by
    refine ⟨fun i => e ⟨γ i, positive_path_states_reachable M γ hp i⟩, ?_⟩
    funext i
    simp [ψ]
  refine ⟨Fintype.card H, hr, N, ψ, ?_, hmap, ?_⟩
  · intro x
    obtain ⟨n, γ, hlast, hp⟩ := (e.symm x).property
    obtain ⟨η, hη⟩ := hlift n γ hp
    refine ⟨n, η, ?_, ?_⟩
    · apply hψ
      exact (congrFun hη (Fin.last n)).trans hlast
    · rw [hmap, hη]; exact hp
  · exact projectedPathLaw_of_state_embedding M N ψ hψ (fun _ => rfl) (fun _ _ => rfl)
      (fun n γ hp i => by
        obtain ⟨η, hη⟩ := hlift n γ hp
        exact ⟨η i, congrFun hη i⟩)

end FSS23105365

-- From Solutions.FSS23105365_DyadicLift
set_option autoImplicit false
namespace FSS23105365

/-- Full Lemma E.4 of Zenodo 23105365, with the exact type of the existing
`dyadic_lift` target. No reachability or weight hypothesis is added. -/
theorem dyadic_lift_proved (q : ℕ) (hq : 0 < q) (M : MarkovChain q)
    (hM : PathDyadic M) :
    ∃ r : ℕ, 0 < r ∧ ∃ N : MarkovChain r, ∃ φ : Fin r → Fin q,
      TransitionDyadic N ∧
      ∀ n : ℕ, ∀ γ : Path q n, projectedPathLaw N φ γ = pathLaw M γ := by
  classical
  obtain ⟨r, hr, N, ψ, hreach, hmap, hproj⟩ := exists_reachable_restriction M
  have hN : PathDyadic N := by
    intro n η
    rw [hmap]
    exact hM n (fun i => ψ (η i))
  obtain ⟨s, hs, L, φ, hL, hLN⟩ := dyadic_lift_of_all_reachable hr N hN hreach
  refine ⟨s, hs, L, fun h => ψ (φ h), hL, fun n γ => ?_⟩
  rw [projectedPathLaw_comp]
  simp_rw [hLN]
  exact hproj n γ

end FSS23105365

-- From Solutions.FSS23105365_ChainToDFA
set_option autoImplicit false
namespace FSS23105365

private theorem foldl_transport {Q R U : Type} (e : Q ≃ R) (δ : Q → U → Q)
    (x : Q) (us : List U) :
    us.foldl (fun y u => e (δ (e.symm y) u)) (e x) = e (us.foldl δ x) := by
  induction us generalizing x with
  | nil => rfl
  | cons u us ih => simpa only [List.foldl_cons, Equiv.symm_apply_apply] using ih (δ x u)

/-- Lemma E.3 of Zenodo 23105365: a finite transition-dyadic Markov chain
is exactly the projection, at fixed block boundaries, of a binary DFA run
on a uniformly random word. The input has `v + n * s` fair bits. -/
theorem transitionDyadic_chain_to_dfa {q : ℕ} (M : MarkovChain q)
    (hM : TransitionDyadic M) :
    ∃ r : ℕ, ∃ B : BinaryDFA r, ∃ v s : ℕ, 0 < v ∧ 0 < s ∧
      ∃ φ : Fin r → Fin q, ∀ n : ℕ, ∀ γ : Path q n,
        (Fintype.card {x : Bits (v + n * s) // B.sampledPath φ v s x = γ} : ℝ) /
          2 ^ (v + n * s) = pathLaw M γ := by
  classical
  obtain ⟨v, s, hv, hs, g, δ, hg, hδ⟩ := transitionDyadic_block_maps M hM
  obtain ⟨v, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hv)
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
  let k := max v s + 1
  have hvk : v < k := Nat.lt_succ_of_le (Nat.le_max_left v s)
  have hsk : s < k := Nat.lt_succ_of_le (Nat.le_max_right v s)
  let Q := DecoderState (Fin q) k
  let e : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  let start : Q := (g (fun _ => false), ⟨⟨v, hvk⟩, g⟩)
  let step := decoderStep hsk δ
  let B : BinaryDFA (Fintype.card Q) :=
    ⟨e start, fun y b => e (step (e.symm y) b), ∅⟩
  let φ : Fin (Fintype.card Q) → Fin q := fun y => (e.symm y).1
  refine ⟨Fintype.card Q, B, v + 1, s + 1, hv, hs, φ, fun n γ => ?_⟩
  let split := consecutiveBlocksEquiv (v + 1) (s + 1) n
  have hpath (x : Bits (v + 1 + n * (s + 1))) :
      B.sampledPath φ (v + 1) (s + 1) x =
        drivenPath δ n (g (split x).1) (split x).2 := by
    funext i
    change (e.symm (((List.ofFn x).take (v + 1 + (s + 1) * i.val)).foldl
      (fun y b => e (step (e.symm y) b)) (e start))).1 = _
    rw [foldl_transport, Equiv.symm_apply_apply]
    have hx := consecutiveBlocks_list (v + 1) (s + 1) n (split x)
    rw [Equiv.symm_apply_apply] at hx
    rw [hx]
    exact decoder_timed_projection hvk hsk g δ (g (fun _ => false)) n
      (split x).1 (split x).2 i
  have hc : Fintype.card {x : Bits (v + 1 + n * (s + 1)) //
      B.sampledPath φ (v + 1) (s + 1) x = γ} =
      Fintype.card {z : Bits (v + 1) × (Fin n → Bits (s + 1)) //
        drivenPath δ n (g z.1) z.2 = γ} := by
    apply Fintype.card_congr
    exact split.subtypeEquiv (fun x => by rw [hpath])
  rw [hc, Nat.mul_comm n (s + 1)]
  exact drivenPath_markov_law M g δ hg hδ n γ

end FSS23105365

-- From Solutions.FSS23105365_SamplerProjection
set_option autoImplicit false
namespace FSS23105365
open scoped BigOperators

theorem fiber_fraction_eq_sum {α β : Type} [Fintype α] [DecidableEq β]
    (f : α → β) (y : β) (d : ℝ) :
    (Fintype.card {x : α // f x = y} : ℝ) / d =
      ∑ x, if f x = y then 1 / d else 0 := by
  classical
  have hc : (Fintype.card {x : α // f x = y} : ℝ) =
      ∑ x, if f x = y then (1 : ℝ) else 0 := by
    simp [Fintype.card_subtype]
  rw [hc, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

/-- Projecting an exact finite-source sampler gives exactly the pushforward
law, including targets with an empty fiber. -/
theorem finite_sampler_projection {α β γ : Type} [Fintype α] [Fintype β]
    [DecidableEq β] [DecidableEq γ] (f : α → β) (g : β → γ) (d : ℝ)
    (p : β → ℝ) (hf : ∀ y, (Fintype.card {x : α // f x = y} : ℝ) / d = p y)
    (z : γ) :
    (Fintype.card {x : α // g (f x) = z} : ℝ) / d =
      ∑ y, if g y = z then p y else 0 := by
  rw [fiber_fraction_eq_sum]
  simp_rw [← hf, fiber_fraction_eq_sum]
  exact (finite_pushforward_comp f g (fun _ => 1 / d) z).symm

/-- E.3 and the full E.4 together give a binary-DFA representation for
every path-dyadic chain, without requiring the original transition rows to
be dyadic or rational on unreachable states. -/
theorem pathDyadic_chain_to_dfa {q : ℕ} (hq : 0 < q) (M : MarkovChain q)
    (hM : PathDyadic M) :
    ∃ r : ℕ, ∃ B : BinaryDFA r, ∃ v s : ℕ, 0 < v ∧ 0 < s ∧
      ∃ φ : Fin r → Fin q, ∀ n : ℕ, ∀ γ : Path q n,
        (Fintype.card {x : Bits (v + n * s) // B.sampledPath φ v s x = γ} : ℝ) /
          2 ^ (v + n * s) = pathLaw M γ := by
  classical
  obtain ⟨r, _, N, ψ, hN, hNM⟩ := dyadic_lift_proved q hq M hM
  obtain ⟨t, B, v, s, hv, hs, φ, hB⟩ := transitionDyadic_chain_to_dfa N hN
  refine ⟨t, B, v, s, hv, hs, ψ ∘ φ, fun n γ => ?_⟩
  have h := finite_sampler_projection (fun x => B.sampledPath φ v s x)
    (fun η : Path r n => fun i => ψ (η i)) (2 ^ (v + n * s)) (pathLaw N) (hB n) γ
  exact h.trans (hNM n γ)

/-- Without the circuit-depth requirement, the linear-seed sufficiency
part of E.5 follows already from E.3 and E.4. The AC0 requirement remains
a separate obligation through Proposition 3.2. -/
theorem pathDyadic_linear_seed_sampler {q : ℕ} (hq : 0 < q) (M : MarkovChain q)
    (hM : PathDyadic M) :
    ∃ v s : ℕ, 0 < v ∧ 0 < s ∧ ∀ n : ℕ,
      ∃ f : Bits (v + n * s) → Path q n,
        ∀ γ, (Fintype.card {x : Bits (v + n * s) // f x = γ} : ℝ) /
          2 ^ (v + n * s) = pathLaw M γ := by
  obtain ⟨r, B, v, s, hv, hs, φ, hB⟩ := pathDyadic_chain_to_dfa hq M hM
  exact ⟨v, s, hv, hs, fun n => ⟨B.sampledPath φ v s, hB n⟩⟩

end FSS23105365

-- From Solutions.FSS23105365_ExactMarkovSampling
set_option autoImplicit false
namespace FSS23105365

theorem fiber_card_precompose_equiv {α β : Type} [Fintype α] [DecidableEq β]
    (e : α ≃ α) (f : α → β) (y : β) :
    Fintype.card {x : α // f (e x) = y} = Fintype.card {x : α // f x = y} := by
  apply Fintype.card_congr
  exact {
    toFun := fun x => ⟨e x.val, x.property⟩
    invFun := fun x => ⟨e.symm x.val, by simpa using x.property⟩
    left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
    right_inv := fun x => Subtype.ext (e.apply_symm_apply x.val) }

/-- E.3, E.4 and the complete DFA-run circuit give exact Markov trajectory
circuits. The single affine fair-bit count v+n*s is retained throughout. -/
theorem pathDyadic_exact_circuits {q : ℕ} (hq : 0 < q) (M : MarkovChain q)
    (hM : PathDyadic M) :
    ∃ v s : ℕ, 0 < v ∧ 0 < s ∧ ∃ D C k : ℕ, ∀ n : ℕ,
      ∃ S : Circuit (Fin (n + 1) × Fin q), S.randomBits = v + n * s ∧
        S.depth ≤ D ∧ S.size ≤ C * (n + 1) ^ k ∧ ExactLaw S pathEncode (pathLaw M) := by
  obtain ⟨r, B, v, s, hv, hs, φ, hB⟩ := pathDyadic_chain_to_dfa hq M hM
  obtain ⟨D, C, k, hc⟩ := dfa_observation_circuits B φ v s
  refine ⟨v, s, hv, hs, D, C, k, fun n => ?_⟩
  obtain ⟨S, hbits, hd, hsize, e, he⟩ := hc n
  refine ⟨S, hbits, hd, hsize, circuit_exactLaw_of_function S hbits pathEncode
    (pathEncode_injective q n) (fun seed => B.sampledPath φ v s (e seed)) he (pathLaw M) ?_⟩
  intro γ
  rw [fiber_card_precompose_equiv]
  exact hB n γ

theorem circuit_mass_dyadic {Out Ω : Type} [Fintype Ω]
    (S : Circuit Out) (encode : Ω → Out → Bool) (z : Ω) : Dyadic (mass S encode z) := by
  classical
  exact ⟨(Finset.univ.filter (fun seed : Bits S.randomBits =>
    S.eval seed = encode z)).card, S.randomBits, rfl⟩

theorem exactPathAC0_pathDyadic {q : ℕ} (M : MarkovChain q) :
    ExactPathAC0 M → PathDyadic M := by
  rintro ⟨D, C, k, h⟩ n γ
  obtain ⟨S, _, _, _, hS⟩ := h n
  rw [← hS γ]
  exact circuit_mass_dyadic S pathEncode γ

/-- Appendix E.5: exact randomized-AC0 trajectory sampling is equivalent
to path-dyadicity, including the full sufficient direction. -/
theorem exact_markov_proved (q : ℕ) (hq : 0 < q) (M : MarkovChain q) :
    ExactPathAC0 M ↔ PathDyadic M := by
  refine ⟨exactPathAC0_pathDyadic M, fun hM => ?_⟩
  obtain ⟨v, s, _, _, D, C, k, hc⟩ := pathDyadic_exact_circuits hq M hM
  refine ⟨D, C, k, fun n => ?_⟩
  obtain ⟨S, _, hd, hs, hS⟩ := hc n
  exact ⟨S, hd, hs, hS⟩

/-- The sufficient direction uses at most linearly many fair bits, with
the same constant allowed to bound both circuit size and seed length. -/
theorem exact_markov_seed_proved (q : ℕ) (hq : 0 < q) (M : MarkovChain q)
    (hM : PathDyadic M) :
    ∃ D C k : ℕ, ∀ n : ℕ, ∃ S : Circuit (Fin (n + 1) × Fin q),
      S.depth ≤ D ∧ S.size ≤ C * (n + 1) ^ k ∧
      S.randomBits ≤ C * (n + 1) ∧ ExactLaw S pathEncode (pathLaw M) := by
  obtain ⟨v, s, _, _, D, C, k, hc⟩ := pathDyadic_exact_circuits hq M hM
  refine ⟨D, C + v + s, k, fun n => ?_⟩
  obtain ⟨S, hbits, hd, hs, hS⟩ := hc n
  refine ⟨S, hd, hs.trans (Nat.mul_le_mul_right _ (by omega)), ?_, hS⟩
  rw [hbits]
  nlinarith

end FSS23105365

end

open FSS23105365

theorem solution (q : ℕ) (hq : 0 < q) (M : MarkovChain q)
    (hM : PathDyadic M) :
    ∃ D C k : ℕ, ∀ n : ℕ, ∃ S : Circuit (Fin (n + 1) × Fin q),
      S.depth ≤ D ∧ S.size ≤ C * (n + 1) ^ k ∧
      S.randomBits ≤ C * (n + 1) ∧ ExactLaw S pathEncode (pathLaw M) := FSS23105365.exact_markov_seed_proved q hq M hM
