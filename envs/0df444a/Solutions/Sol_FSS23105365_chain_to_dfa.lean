-- Prove2me | solution 1 for FSS23105365.chain_to_dfa
-- status  : ACCEPTED   (prove)
-- author  : @YY
-- created : 2026-10-09T15:55:34.206052+00:00
-- url     : https://prove2.me/submissions/fee73c59-b455-4df9-8ce5-5ff190ccae12

-- Generated from Lean declaration graph and parser source spans.
-- Original statement and proof bodies are preserved.
import Definitions.Def_FSS23105365_Circuits
import Definitions.Def_FSS23105365_DFARun
import Definitions.Def_FSS23105365_FiniteState
import Init
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.OfFn
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Rel
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Relation
import Mathlib.Order.Fin.Tuple
import Mathlib.Order.Iterate
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Ring.Real

-- Source module: Solutions.FSS23105365_Aperiodicity
section
set_option autoImplicit false
namespace FSS23105365
open Function









/-- Aperiodicity of the word-induced transition maps, with the positive
exponent convention used in the paper. -/
def AperiodicTransitions {H U : Type} (τ : H → U → H) : Prop :=
  ∀ w : List U, ∃ k : ℕ, 0 < k ∧
    (fun h => w.foldl τ h)^[k] = (fun h => w.foldl τ h)^[k + 1]





end FSS23105365

end

-- Source module: Solutions.FSS23105365_DyadicRealization
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_BlockMarkov
section
set_option autoImplicit false
noncomputable section
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





end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_BinaryDecoder
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_PathSplitting
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators



def pathRight {Q : Type} {m n : ℕ} (γ : Fin (m + n + 1) → Q) : Fin (n + 1) → Q :=
  fun i => γ ⟨m + i.val, by omega⟩

















end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_MultipleBridgePaths
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- Total number of edges in a sequence of blocks. There is always at least
one block; individual blocks may have length zero. -/
def bridgeBlockLength : {k : ℕ} → (Fin (k + 1) → ℕ) → ℕ
  | 0, l => l 0
  | k + 1, l => l 0 + bridgeBlockLength (Fin.tail l)

/-- An actual full path whose start, end, and intermediate block boundaries
are the specified states. The recursive definition uses actual path cuts. -/
def bridgeBoundarySpec {Q : Type} : {k : ℕ} → (l : Fin (k + 1) → ℕ) →
    Q → Q → (Fin k → Q) → (Fin (bridgeBlockLength l + 1) → Q) → Prop
  | 0, l, s, t, _, γ => γ 0 = s ∧ γ (Fin.last (l 0)) = t
  | k + 1, l, s, t, y, γ => γ 0 = s ∧
      γ ⟨l 0, by simp only [bridgeBlockLength]; omega⟩ = y 0 ∧
      bridgeBoundarySpec (Fin.tail l) (y 0) t (Fin.tail y) (pathRight γ)

abbrev BoundaryPath (Q : Type) {k : ℕ} (l : Fin (k + 1) → ℕ)
    (s t : Q) (y : Fin k → Q) :=
  {γ : Fin (bridgeBlockLength l + 1) → Q // bridgeBoundarySpec l s t y γ}

instance boundaryPathFintype {Q : Type} [Fintype Q] {k : ℕ} (l : Fin (k + 1) → ℕ)
    (s t : Q) (y : Fin k → Q) : Fintype (BoundaryPath Q l s t y) := Fintype.ofFinite _

















end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_BridgeBoundaryMarginal
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators



/-- Read the intermediate states from the full trajectory, at the actual
cumulative block lengths. -/
def bridgeBoundaryStates {Q : Type} : {k : ℕ} → (l : Fin (k + 1) → ℕ) →
    (Fin (bridgeBlockLength l + 1) → Q) → (Fin k → Q)
  | 0, _, _ => Fin.elim0
  | k + 1, l, γ => Fin.cons (γ ⟨l 0, by simp only [bridgeBlockLength]; omega⟩)
      (bridgeBoundaryStates (Fin.tail l) (pathRight γ))















end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_GraphSCCPaths
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

/-- A canonical SCC label: the finite set of all reachable states. Equality
of these labels is equivalent to mutual reachability. -/
def graphComponent {Q : Type} [Fintype Q] (R : Q → Q → Prop) (x : Q) : Finset Q := by
  classical
  exact Finset.univ.filter (fun y => Relation.ReflTransGen R x y)





















def graphCrossings {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ : Fin (n + 1) → Q) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => graphComponent R (γ i.castSucc) ≠ graphComponent R (γ i.succ))









end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_BridgeObservationTransport
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- The actual boundary observation of an n-edge path, using a proved
block partition of exactly n edges. The only transport is an index cast. -/
def bridgeBoundaryObservation {Q : Type} {k n : ℕ} (l : Fin (k + 1) → ℕ)
    (hlen : bridgeBlockLength l = n) (γ : Fin (n + 1) → Q) : Fin k → Q :=
  bridgeBoundaryStates l (fun i => γ (Fin.cast (congrArg (fun j => j + 1) hlen) i))









end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ChainToDFA
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_OrderedBlockCuts
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

/-- Consecutive differences of an ordered cut vector. Repeated cuts are
allowed and represent zero-length blocks. -/
def cutGaps {k : ℕ} (c : Fin (k + 2) → ℕ) : Fin (k + 1) → ℕ :=
  fun i => c i.succ - c i.castSucc

theorem cutGaps_total {k : ℕ} (c : Fin (k + 2) → ℕ) (hc : Monotone c) :
    bridgeBlockLength (cutGaps c) = c (Fin.last (k + 1)) - c 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have ht : Monotone (Fin.tail c) := by
      intro i j hij
      exact hc (Fin.succ_le_succ_iff.mpr hij)
    have hfirst : c 0 ≤ c 1 := hc (Fin.zero_le 1)
    have hlast : c 1 ≤ c (Fin.last (k + 2)) := hc (Fin.le_last _)
    change (c 1 - c 0) + bridgeBlockLength (cutGaps (Fin.tail c)) = _
    rw [ih (Fin.tail c) ht]
    change c 1 - c 0 + (c (Fin.last (k + 2)) - c 1) = c (Fin.last (k + 2)) - c 0
    omega





end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SCCCategoryFibers
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365





def CategoryBoundaryMatches {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ η : Fin (n + 1) → Q) : Prop :=
  γ 0 = η 0 ∧ γ (Fin.last n) = η (Fin.last n) ∧
    ∀ i ∈ graphCrossings R γ, γ i.castSucc = η i.castSucc ∧ γ i.succ = η i.succ

instance categoryBoundaryMatchesDecidable {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ η : Fin (n + 1) → Q) : Decidable (CategoryBoundaryMatches R γ η) :=
  Classical.propDecidable _





end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SCCOrderedCuts
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

/-- All internal positions fixed by a category: both ends of every
cross-SCC edge, with the global endpoints kept separately. -/
def graphInteriorCuts {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ : Fin (n + 1) → Q) : Finset (Fin (n + 1)) := by
  classical
  exact Finset.univ.filter (fun j => j ≠ 0 ∧ j ≠ Fin.last n ∧
    ∃ i ∈ graphCrossings R γ, j = i.castSucc ∨ j = i.succ)





def graphOrderedCuts {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ : Fin (n + 1) → Q) : Fin ((graphInteriorCuts R γ).card + 2) → ℕ :=
  Fin.cons 0 (Fin.snoc (fun i => ((graphInteriorCuts R γ).orderEmbOfFin rfl i).val) n)

theorem graphOrderedCuts_start {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ : Fin (n + 1) → Q) : graphOrderedCuts R γ 0 = 0 := by
  simp [graphOrderedCuts]

theorem graphOrderedCuts_finish {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ : Fin (n + 1) → Q) :
    graphOrderedCuts R γ (Fin.last ((graphInteriorCuts R γ).card + 1)) = n := by
  simp [graphOrderedCuts, Fin.cons_last]



theorem graphOrderedCuts_monotone {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ : Fin (n + 1) → Q) : Monotone (graphOrderedCuts R γ) := by
  let S := graphInteriorCuts R γ
  let f : Fin S.card → ℕ := fun i => (S.orderEmbOfFin rfl i).val
  have hmono : Monotone f := fun i j hij => (S.orderEmbOfFin rfl).monotone hij
  have hle (i : Fin S.card) : f i ≤ n := Nat.le_of_lt_succ (S.orderEmbOfFin rfl i).isLt
  have hsnoc : Monotone (Fin.snoc f n : Fin (S.card + 1) → ℕ) := by
    intro i j hij
    cases j using Fin.lastCases with
    | last =>
      cases i using Fin.lastCases with
      | last => exact le_rfl
      | cast j => simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hle j
    | cast j =>
      cases i using Fin.lastCases with
      | last => have hi := j.isLt; simp only [Fin.le_def, Fin.val_last, Fin.val_castSucc] at hij; omega
      | cast i => simpa only [Fin.snoc_castSucc] using hmono (by simpa using hij)
  intro i j hij
  cases i using Fin.cases with
  | zero => simp only [graphOrderedCuts_start]; exact Nat.zero_le _
  | succ i =>
    cases j using Fin.cases with
    | zero => simp at hij
    | succ j =>
      change (Fin.snoc f n : Fin (S.card + 1) → ℕ) i ≤ (Fin.snoc f n : Fin (S.card + 1) → ℕ) j
      exact hsnoc (Fin.succ_le_succ_iff.mp hij)

def graphCategoryBlockLengths {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ : Fin (n + 1) → Q) : Fin ((graphInteriorCuts R γ).card + 1) → ℕ :=
  cutGaps (graphOrderedCuts R γ)

theorem graphCategoryBlockLengths_total {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ : Fin (n + 1) → Q) : bridgeBlockLength (graphCategoryBlockLengths R γ) = n := by
  rw [graphCategoryBlockLengths, cutGaps_total _ (graphOrderedCuts_monotone R γ),
    graphOrderedCuts_start, graphOrderedCuts_finish, Nat.sub_zero]











end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ConstructedCategoryLaw
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

def CategoryBlockMatches {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ η : Fin (n + 1) → Q) : Prop :=
  γ 0 = η 0 ∧ γ (Fin.last n) = η (Fin.last n) ∧
    bridgeBoundaryObservation (graphCategoryBlockLengths R γ) (graphCategoryBlockLengths_total R γ) γ =
    bridgeBoundaryObservation (graphCategoryBlockLengths R γ) (graphCategoryBlockLengths_total R γ) η

instance categoryBlockMatchesDecidable {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ η : Fin (n + 1) → Q) : Decidable (CategoryBlockMatches R γ η) :=
  Classical.propDecidable _





end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_IdempotentSupport
section
set_option autoImplicit false
noncomputable section
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

















end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_LocalDivisor
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365





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

















end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_RunSamplerCorrectness
section
set_option autoImplicit false
noncomputable section
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



































end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_TransitionMonoid
section
set_option autoImplicit false
noncomputable section
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















end FSS23105365

end
end

open FSS23105365
local notation "Path" => FSS23105365.Path
theorem solution {q : ℕ} (M : MarkovChain q)
    (hM : TransitionDyadic M) :
    ∃ r : ℕ, ∃ B : BinaryDFA r, ∃ v s : ℕ, 0 < v ∧ 0 < s ∧
      ∃ φ : Fin r → Fin q, ∀ n : ℕ, ∀ γ : Path q n,
        (Fintype.card {x : Bits (v + n * s) // B.sampledPath φ v s x = γ} : ℝ) /
          2 ^ (v + n * s) = pathLaw M γ := FSS23105365.transitionDyadic_chain_to_dfa M hM
