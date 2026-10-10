-- Prove2me | solution 1 for FSS23105365.word_sampling
-- status  : ACCEPTED   (prove)
-- author  : @YY
-- created : 2026-10-09T15:56:48.554199+00:00
-- url     : https://prove2.me/submissions/bac1681f-1b06-41c3-a827-408bf7c802b9

-- Generated from Lean declaration graph and parser source spans.
-- Original statement and proof bodies are preserved.
import Definitions.Def_FSS23105365_Circuits
import Definitions.Def_FSS23105365_DFARun
import Definitions.Def_FSS23105365_FiniteState
import Init
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Find
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Rel
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Relation
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Fin.Tuple
import Mathlib.Order.Iterate
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.OrderClosed

-- Source module: Solutions.FSS23105365_PathProjection
section
set_option autoImplicit false
noncomputable section
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



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_PathWeights
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- The same finite path product as `pathLaw`, on an arbitrary finite state
type. This permits the sigma-type state copies in the E.4 construction. -/
def finitePathWeight {H : Type} (μ : H → ℝ) (P : H → H → ℝ)
    {n : ℕ} (η : Fin (n + 1) → H) : ℝ :=
  μ (η 0) * ∏ i : Fin n, P (η i.castSucc) (η i.succ)



@[simp] theorem finitePathWeight_snoc {H : Type} (μ : H → ℝ) (P : H → H → ℝ)
    {n : ℕ} (η : Fin (n + 1) → H) (h : H) :
    finitePathWeight μ P (Fin.snoc η h) =
      finitePathWeight μ P η * P (η (Fin.last n)) h := by
  simp only [finitePathWeight, Fin.prod_univ_castSucc]
  simp only [← Fin.castSucc_succ, Fin.snoc_castSucc, Fin.snoc_last,
    Fin.succ_last, Fin.snoc_apply_zero]
  ring

















end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_DyadicRealization
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators



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







end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_IntegerMargins
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- Fibers partition the finite source set. -/
theorem sum_fiber_card {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) : (∑ y, Fintype.card {x : α // f x = y}) = Fintype.card α := by
  simpa only [Fintype.card_sigma] using Fintype.card_congr (Equiv.sigmaFiberEquiv f)



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ReachableRestriction
section
set_option autoImplicit false
noncomputable section
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











end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_BinaryDecoder
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365













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







end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SamplerProjection
section
set_option autoImplicit false
noncomputable section
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





end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_TotalVariation
section
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



end FSS23105365

end

-- Source module: Solutions.FSS23105365_TotalVariationProducts
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

theorem tv_nonneg {α : Type} [Fintype α] (p q : α → ℝ) : 0 ≤ tv p q :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by norm_num)

/-- For normalized finite laws, TV is one minus the overlap mass. -/
theorem tv_eq_one_sub_overlap {α : Type} [Fintype α] (p q : α → ℝ)
    (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1) :
    tv p q = 1 - ∑ x, min (p x) (q x) := by
  have hpoint (x : α) : |p x - q x| = p x + q x - 2 * min (p x) (q x) := by
    rcases le_total (p x) (q x) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  unfold tv
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hp, hq]
  ring

theorem tv_le_one {α : Type} [Fintype α] (p q : α → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hpsum : ∑ x, p x = 1) (hqsum : ∑ x, q x = 1) : tv p q ≤ 1 := by
  rw [tv_eq_one_sub_overlap p q hpsum hqsum]
  have h := Finset.sum_nonneg (fun x (_ : x ∈ Finset.univ) => le_min (hp x) (hq x))
  linarith

/-- The sharp product bound from Lemma C.1. The proof uses overlap masses,
equivalently the success probabilities of coordinatewise maximal couplings. -/
theorem tv_finite_product_le {I : Type} [Fintype I] [DecidableEq I] {α : I → Type}
    [∀ i, Fintype (α i)] (p q : ∀ i, α i → ℝ)
    (hp : ∀ i x, 0 ≤ p i x) (hq : ∀ i x, 0 ≤ q i x)
    (hpsum : ∀ i, ∑ x, p i x = 1) (hqsum : ∀ i, ∑ x, q i x = 1) :
    tv (fun x : ∀ i, α i => ∏ i, p i (x i))
      (fun x : ∀ i, α i => ∏ i, q i (x i)) ≤
      1 - ∏ i, (1 - tv (p i) (q i)) := by
  classical
  have hpall : (∑ x : ∀ i, α i, ∏ i, p i (x i)) = 1 := by
    rw [← Fintype.prod_sum]; simp only [hpsum, Finset.prod_const_one]
  have hqall : (∑ x : ∀ i, α i, ∏ i, q i (x i)) = 1 := by
    rw [← Fintype.prod_sum]; simp only [hqsum, Finset.prod_const_one]
  rw [tv_eq_one_sub_overlap _ _ hpall hqall]
  have hpoint (x : ∀ i, α i) :
      (∏ i, min (p i (x i)) (q i (x i))) ≤ min (∏ i, p i (x i)) (∏ i, q i (x i)) := by
    apply le_min
    · exact Finset.prod_le_prod (fun i _ => le_min (hp i _) (hq i _))
        (fun i _ => min_le_left _ _)
    · exact Finset.prod_le_prod (fun i _ => le_min (hp i _) (hq i _))
        (fun i _ => min_le_right _ _)
  have hoverlap := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hpoint x)
  rw [← Fintype.prod_sum (fun i (x : α i) => min (p i x) (q i x))] at hoverlap
  have hlocal (i : I) : 1 - tv (p i) (q i) = ∑ x, min (p i x) (q i x) := by
    rw [tv_eq_one_sub_overlap _ _ (hpsum i) (hqsum i)]; ring
  simp_rw [hlocal]
  linarith

theorem one_sub_finite_product_le_sum {I : Type} [Fintype I] (δ : I → ℝ)
    (hδ : ∀ i, 0 ≤ δ i) (hδ' : ∀ i, δ i ≤ 1) :
    1 - ∏ i, (1 - δ i) ≤ ∑ i, δ i := by
  classical
  have h (s : Finset I) : 1 - ∏ i ∈ s, (1 - δ i) ≤ ∑ i ∈ s, δ i := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      have hp : (∏ j ∈ s, (1 - δ j)) ≤ 1 :=
        Finset.prod_le_one (fun j _ => sub_nonneg.mpr (hδ' j))
          (fun j _ => by linarith [hδ j])
      nlinarith [hδ i]
  exact h Finset.univ

theorem tv_finite_product_le_sum {I : Type} [Fintype I] [DecidableEq I] {α : I → Type}
    [∀ i, Fintype (α i)] (p q : ∀ i, α i → ℝ)
    (hp : ∀ i x, 0 ≤ p i x) (hq : ∀ i x, 0 ≤ q i x)
    (hpsum : ∀ i, ∑ x, p i x = 1) (hqsum : ∀ i, ∑ x, q i x = 1) :
    tv (fun x : ∀ i, α i => ∏ i, p i (x i))
      (fun x : ∀ i, α i => ∏ i, q i (x i)) ≤ ∑ i, tv (p i) (q i) :=
  (tv_finite_product_le p q hp hq hpsum hqsum).trans
    (one_sub_finite_product_le_sum _ (fun i => tv_nonneg _ _)
      (fun i => tv_le_one _ _ (hp i) (hq i) (hpsum i) (hqsum i)))

/-- Conditioning on an event of positive probability changes a finite law
by exactly the probability of the discarded event. -/
theorem tv_conditioning {α : Type} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (G : Finset α) (hG : 0 < ∑ x ∈ G, p x) :
    tv p (fun x => if x ∈ G then p x / (∑ y ∈ G, p y) else 0) =
      ∑ x, if x ∈ G then 0 else p x := by
  classical
  let c := ∑ x ∈ G, p x
  have hc : 0 < c := hG
  have hcin : (∑ x, if x ∈ G then p x else 0) = c := by simp [c]
  have hcle : c ≤ 1 := by
    rw [← hcin, ← hsum]
    apply Finset.sum_le_sum
    intro x _
    split_ifs
    · exact le_rfl
    · exact hp x
  have hout : (∑ x, if x ∈ G then 0 else p x) = 1 - c := by
    have hh : ∀ x, (if x ∈ G then p x else 0) + (if x ∈ G then 0 else p x) = p x := by
      intro x; split_ifs <;> simp
    have ht := congrArg (fun f : α → ℝ => ∑ x, f x) (funext hh)
    simp only [Finset.sum_add_distrib, hcin, hsum] at ht
    linarith
  have hpoint (x : α) : |p x - (if x ∈ G then p x / c else 0)| =
      p x + (1 / c - 2) * (if x ∈ G then p x else 0) := by
    by_cases hx : x ∈ G
    · simp only [hx, if_true]
      have hle : p x ≤ p x / c := (le_div_iff₀ hc).mpr (by nlinarith [hp x])
      rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      ring
    · simp [hx, abs_of_nonneg (hp x)]
  change (∑ x, |p x - (if x ∈ G then p x / c else 0)|) / 2 = _
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcin, hsum, hout]
  field_simp [hc.ne'] <;> ring

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_WeightNormalization
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- Normalize nonnegative finite weights. A positive total mass is required
in every probability theorem using this definition. -/
def normalizeWeights {Ω : Type} [Fintype Ω] (w : Ω → ℝ) : Ω → ℝ :=
  fun x => w x / ∑ y, w y

theorem normalizeWeights_nonneg {Ω : Type} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) : ∀ x, 0 ≤ normalizeWeights w x := by
  intro x
  exact div_nonneg (hw x) (Finset.sum_nonneg (fun y _ => hw y))

theorem normalizeWeights_sum {Ω : Type} [Fintype Ω]
    (w : Ω → ℝ) (hw : 0 < ∑ x, w x) : ∑ x, normalizeWeights w x = 1 := by
  simp only [normalizeWeights, ← Finset.sum_div]
  exact div_self hw.ne'

theorem normalizeWeights_scale {Ω : Type} [Fintype Ω]
    (w : Ω → ℝ) (c : ℝ) (hc : c ≠ 0) :
    normalizeWeights (fun x => c * w x) = normalizeWeights w := by
  funext x
  simp only [normalizeWeights, ← Finset.mul_sum]
  exact mul_div_mul_left (w x) (∑ y, w y) hc

theorem tv_triangle {Ω : Type} [Fintype Ω] (p q r : Ω → ℝ) :
    tv p r ≤ tv p q + tv q r := by
  unfold tv
  rw [← add_div, ← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact Finset.sum_le_sum (fun x _ => abs_sub_le (p x) (q x) (r x))

theorem tv_normalize_self {Ω : Type} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hZ : 0 < ∑ x, w x) :
    tv (normalizeWeights w) w = |1 - ∑ x, w x| / 2 := by
  let Z := ∑ x, w x
  have hZ' : 0 < Z := hZ
  have hpoint (x : Ω) : |normalizeWeights w x - w x| = |1 / Z - 1| * w x := by
    change |w x / Z - w x| = _
    rw [show w x / Z - w x = (1 / Z - 1) * w x by ring,
      abs_mul, abs_of_nonneg (hw x)]
  unfold tv
  simp_rw [hpoint]
  rw [← Finset.mul_sum]
  change |1 / Z - 1| * Z / 2 = |1 - Z| / 2
  rw [← abs_of_pos hZ', ← abs_mul]
  rw [abs_of_pos hZ']
  congr 2
  field_simp [hZ'.ne']

/-- Normalization of nonnegative weights costs at most their original L1
error from a probability law. This estimate needs no lower bound on the
normalizing constant other than positivity. -/
theorem tv_normalize_le_l1 {Ω : Type} [Fintype Ω]
    (w p : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hZ : 0 < ∑ x, w x)
    (hp : ∑ x, p x = 1) :
    tv (normalizeWeights w) p ≤ ∑ x, |w x - p x| := by
  have hmass : |1 - ∑ x, w x| ≤ ∑ x, |w x - p x| := by
    rw [abs_sub_comm, ← hp, ← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have ht := tv_triangle (normalizeWeights w) w p
  rw [tv_normalize_self w hw hZ] at ht
  unfold tv at ht ⊢
  linarith

theorem tv_normalize_le_of_relative_error {Ω : Type} [Fintype Ω]
    (w p : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hZ : 0 < ∑ x, w x)
    (hp : ∑ x, p x = 1) (δ : ℝ)
    (herr : ∀ x, |w x - p x| ≤ δ * p x) :
    tv (normalizeWeights w) p ≤ δ := by
  calc
    _ ≤ ∑ x, |w x - p x| := tv_normalize_le_l1 w p hw hZ hp
    _ ≤ ∑ x, δ * p x := Finset.sum_le_sum (fun x _ => herr x)
    _ = δ := by rw [← Finset.mul_sum, hp, mul_one]

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_FiniteDisintegration
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def fiberWeight {Ω C : Type} [DecidableEq C] (f : Ω → C) (w : Ω → ℝ) (c : C) : Ω → ℝ :=
  fun x => if f x = c then w x else 0

def fiberMass {Ω C : Type} [Fintype Ω] [DecidableEq C]
    (f : Ω → C) (w : Ω → ℝ) (c : C) : ℝ := ∑ x, fiberWeight f w c x

theorem fiberWeight_nonneg {Ω C : Type} [DecidableEq C]
    (f : Ω → C) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (c : C) (x : Ω) :
    0 ≤ fiberWeight f w c x := by
  unfold fiberWeight
  split_ifs
  · exact hw x
  · exact le_rfl

theorem fiberMass_nonneg {Ω C : Type} [Fintype Ω] [DecidableEq C]
    (f : Ω → C) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (c : C) :
    0 ≤ fiberMass f w c := Finset.sum_nonneg (fun x _ => fiberWeight_nonneg f w hw c x)

theorem fiberMass_sum {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C]
    (f : Ω → C) (w : Ω → ℝ) : (∑ c, fiberMass f w c) = ∑ x, w x := by
  classical
  unfold fiberMass fiberWeight
  rw [Finset.sum_comm]
  simp

theorem fiberMass_pos_of_weight_pos {Ω C : Type} [Fintype Ω] [DecidableEq C]
    (f : Ω → C) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (x : Ω) (hx : 0 < w x) :
    0 < fiberMass f w (f x) := by
  have hle := Finset.single_le_sum (fun z _ => fiberWeight_nonneg f w hw (f x) z)
    (Finset.mem_univ x)
  have hle' : w x ≤ fiberMass f w (f x) := by simpa [fiberWeight, fiberMass] using hle
  exact hx.trans_le hle'

theorem fiberMass_pos_iff {Ω C : Type} [Fintype Ω] [DecidableEq C]
    (f : Ω → C) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (c : C) :
    0 < fiberMass f w c ↔ ∃ x, f x = c ∧ 0 < w x := by
  classical
  rw [fiberMass, Finset.sum_pos_iff_of_nonneg (fun x _ => fiberWeight_nonneg f w hw c x)]
  simp only [Finset.mem_univ, true_and, fiberWeight]
  apply exists_congr
  intro x
  by_cases hx : f x = c <;> simp [hx]

/-- Exact finite disintegration, with the fiber masses as the category law.
Only positivity of the total mass is needed; it may be arbitrarily small. -/
theorem normalized_weight_disintegration {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C]
    (f : Ω → C) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hZ : 0 < ∑ x, w x) (x : Ω) :
    (∑ c, normalizeWeights (fiberMass f w) c * normalizeWeights (fiberWeight f w c) x) =
      normalizeWeights w x := by
  classical
  have hterm (c : C) :
      normalizeWeights (fiberMass f w) c * normalizeWeights (fiberWeight f w c) x =
        if f x = c then w x / (∑ z, w z) else 0 := by
    simp only [normalizeWeights, fiberMass_sum]
    change fiberMass f w c / (∑ z, w z) * (fiberWeight f w c x / fiberMass f w c) = _
    by_cases hc : f x = c
    · rw [if_pos hc]
      have hn : fiberWeight f w c x = w x := if_pos hc
      rw [hn]
      by_cases hx : w x = 0
      · simp [hx]
      · have hm : 0 < fiberMass f w c := by
          rw [← hc]
          exact fiberMass_pos_of_weight_pos f w hw x (lt_of_le_of_ne (hw x) (Ne.symm hx))
        field_simp [hZ.ne', hm.ne']
    · rw [if_neg hc]
      have hn : fiberWeight f w c x = 0 := if_neg hc
      rw [hn]
      simp
  simp_rw [hterm]
  simp [normalizeWeights]

abbrev PositiveFiber {Ω C : Type} [Fintype Ω] [DecidableEq C] (f : Ω → C) (w : Ω → ℝ) :=
  {c : C // 0 < fiberMass f w c}

theorem positiveFiber_mass_sum {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C]
    (f : Ω → C) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ c : PositiveFiber f w, fiberMass f w c.val) = ∑ x, w x := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun c => 0 < fiberMass f w c)) (by simp)]
  rw [Finset.sum_filter, ← fiberMass_sum f w]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : 0 < fiberMass f w c
  · rw [if_pos hc]
  · rw [if_neg hc]
    exact (le_antisymm (le_of_not_gt hc) (fiberMass_nonneg f w hw c)).symm

theorem positiveFiber_normalized_mass {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C]
    (f : Ω → C) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (c : PositiveFiber f w) :
    normalizeWeights (fun d : PositiveFiber f w => fiberMass f w d.val) c =
      normalizeWeights (fiberMass f w) c.val := by
  simp only [normalizeWeights, positiveFiber_mass_sum f w hw, fiberMass_sum]

theorem positiveFiber_disintegration {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C]
    (f : Ω → C) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hZ : 0 < ∑ x, w x) (x : Ω) :
    (∑ c : PositiveFiber f w,
      normalizeWeights (fun d : PositiveFiber f w => fiberMass f w d.val) c *
        normalizeWeights (fiberWeight f w c.val) x) = normalizeWeights w x := by
  classical
  simp_rw [positiveFiber_normalized_mass f w hw]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun c => 0 < fiberMass f w c)) (by simp)
    (f := fun c => normalizeWeights (fiberMass f w) c * normalizeWeights (fiberWeight f w c) x)]
  rw [Finset.sum_filter, ← normalized_weight_disintegration f w hw hZ x]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : 0 < fiberMass f w c
  · rw [if_pos hc]
  · rw [if_neg hc]
    have hz := le_antisymm (le_of_not_gt hc) (fiberMass_nonneg f w hw c)
    simp [normalizeWeights, hz]



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ProbabilityRounding
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- Integer rounding with an exact prescribed sum and no new support.
Start with floors and add one on a subset of the positive coordinates.
Largest-remainder selection is unnecessary for the weak error bound of one. -/
theorem round_nonnegative_integer_sum {α : Type} [Fintype α]
    (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) (N : ℕ) (hsum : ∑ x, w x = N) :
    ∃ a : α → ℕ, (∑ x, a x = N) ∧
      (∀ x, |(a x : ℝ) - w x| ≤ 1) ∧ (∀ x, w x = 0 → a x = 0) := by
  classical
  let b : α → ℕ := fun x => ⌊w x⌋₊
  let s : Finset α := Finset.univ.filter (fun x => 0 < w x)
  have hb (x : α) : (b x : ℝ) ≤ w x := Nat.floor_le (hw x)
  have hb' (x : α) : w x < (b x : ℝ) + 1 := Nat.lt_floor_add_one _
  have hbase : ∑ x, b x ≤ N := by
    have h := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hb x)
    rw [hsum] at h
    exact_mod_cast h
  have hbound : N ≤ ∑ x, b x + s.card := by
    have h : ∀ x, w x ≤ (b x : ℝ) + if x ∈ s then 1 else 0 := by
      intro x
      by_cases hx : x ∈ s
      · simpa [hx] using (hb' x).le
      · have hz : w x = 0 := by
          have : ¬0 < w x := by simpa [s] using hx
          exact le_antisymm (le_of_not_gt this) (hw x)
        simp [hx, hz, b]
    have hh := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => h x)
    rw [hsum, Finset.sum_add_distrib] at hh
    simp only [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul, mul_one] at hh
    exact_mod_cast hh
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq
    (s := s) (n := N - ∑ x, b x) (by omega)
  let a : α → ℕ := fun x => b x + if x ∈ t then 1 else 0
  refine ⟨a, ?_, ?_, ?_⟩
  · simp only [a, Finset.sum_add_distrib, Finset.sum_ite_mem,
      Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_one, htcard]
    omega
  · intro x
    apply abs_le.mpr
    by_cases hx : x ∈ t
    · simp only [a, hx, if_true, Nat.cast_add, Nat.cast_one]
      constructor <;> linarith [hb x, hb' x]
    · simp only [a, hx, if_false, add_zero]
      constructor <;> linarith [hb x, hb' x]
  · intro x hx
    have hxt : x ∉ t := by
      intro h
      have hp : 0 < w x := (Finset.mem_filter.mp (hts h)).2
      simpa [hx] using hp
    simp [a, b, hx, hxt]

/-- The probabilistic part of Appendix C, Lemma C.2, at any positive integer
denominator. Circuit implementation and the choice of denominator are separate. -/
theorem probability_rounding_counts {α : Type} [Fintype α]
    (p : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (N : ℕ) (hN : 0 < N) :
    ∃ a : α → ℕ, (∑ x, a x = N) ∧
      (∀ x, p x = 0 → a x = 0) ∧
      tv (fun x => (a x : ℝ) / N) p ≤ Fintype.card α / (2 * (N : ℝ)) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  obtain ⟨a, ha, herr, hzero⟩ := round_nonnegative_integer_sum
    (fun x => (N : ℝ) * p x) (fun x => mul_nonneg hNr.le (hp x)) N
    (by rw [← Finset.mul_sum, hsum, mul_one])
  refine ⟨a, ha, fun x hx => hzero x (by rw [hx, mul_zero]), ?_⟩
  have hpoint (x : α) : |(a x : ℝ) / N - p x| ≤ 1 / N := by
    calc
      _ = |((a x : ℝ) - N * p x) / N| := by congr 1; field_simp
      _ = |(a x : ℝ) - N * p x| / N := by rw [abs_div, abs_of_pos hNr]
      _ ≤ 1 / N := div_le_div_of_nonneg_right (herr x) hNr.le
  unfold tv
  calc
    _ ≤ (∑ _x : α, (1 : ℝ) / N) / 2 :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => hpoint x)) (by norm_num)
    _ = _ := by simp; ring

/-- A support-preserving approximate finite distribution can be realized from
exactly `m` fair bits, with total variation at most `M / 2^(m+1)`.
This theorem concerns the finite source law; it does not assert circuit size. -/
theorem dyadic_rounding_sampler {α : Type} [Fintype α] [DecidableEq α]
    (p : α → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) (m : ℕ) :
    ∃ f : Bits m → α,
      (∀ seed, 0 < p (f seed)) ∧
      tv (fun x => (Fintype.card {seed : Bits m // f seed = x} : ℝ) / 2 ^ m) p ≤
        Fintype.card α / (2 : ℝ) ^ (m + 1) := by
  classical
  obtain ⟨a, ha, hzero, herr⟩ := probability_rounding_counts p hp hsum
    (2 ^ m) (by positivity)
  obtain ⟨f, hf⟩ := exists_map_with_fiber_counts (β := Bits m) a (by
    simpa only [Bits, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using ha)
  refine ⟨f, ?_, ?_⟩
  · intro seed
    by_contra h
    have hz : p (f seed) = 0 := le_antisymm (le_of_not_gt h) (hp _)
    have hcard : 0 < Fintype.card {u : Bits m // f u = f seed} :=
      Fintype.card_pos_iff.mpr ⟨⟨seed, rfl⟩⟩
    rw [hf, hzero _ hz] at hcard
    omega
  · simp only [hf]
    simpa only [Nat.cast_pow, Nat.cast_ofNat, pow_succ, mul_comm (2 : ℝ)] using herr

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_DyadicRoundingSeed
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

/-- The paper's logarithmic number of fair bits, rounded up. -/
def roundingSeed (M : ℕ) (η : ℝ) : ℕ :=
  ⌈Real.log M / Real.log 2 + logInv η⌉₊

theorem roundingSeed_denominator_bound (M : ℕ) (hM : 0 < M)
    (η : ℝ) (hη : 0 < η) :
    (M : ℝ) / (2 : ℝ) ^ roundingSeed M η ≤ η := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hMr : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hh : Real.log ((M : ℝ) / η) / Real.log 2 ≤ roundingSeed M η := by
    calc
      _ = Real.log M / Real.log 2 + logInv η := by
        rw [Real.log_div hMr.ne' hη.ne', sub_div]
        simp [logInv, Real.log_div one_ne_zero hη.ne', sub_eq_add_neg, neg_div]
      _ ≤ _ := Nat.le_ceil _
  have hpow : (M : ℝ) / η ≤ (2 : ℝ) ^ roundingSeed M η := by
    apply Real.le_pow_of_log_le (by norm_num)
    exact (div_le_iff₀ hlog).mp hh
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ roundingSeed M η)).mpr
  have := (div_le_iff₀ hη).mp hpow
  simpa only [mul_comm] using this



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_FiniteSeedLaws
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def finiteSeedLaw {Ω : Type} [Fintype Ω] [DecidableEq Ω] {m : ℕ} (f : Bits m → Ω) : Ω → ℝ :=
  fun x => (Fintype.card {seed : Bits m // f seed = x} : ℝ) / 2 ^ m

theorem finiteSeedLaw_as_fiberMass {Ω : Type} [Fintype Ω] [DecidableEq Ω] {m : ℕ}
    (f : Bits m → Ω) : finiteSeedLaw f = fiberMass f (fun _ => (1 : ℝ) / 2 ^ m) := by
  funext x
  exact fiber_fraction_eq_sum f x _

theorem finiteSeedLaw_nonneg {Ω : Type} [Fintype Ω] [DecidableEq Ω] {m : ℕ} (f : Bits m → Ω) :
    ∀ x, 0 ≤ finiteSeedLaw f x := by
  intro x
  exact div_nonneg (Nat.cast_nonneg _) (by positivity)

theorem finiteSeedLaw_sum {Ω : Type} [Fintype Ω] [DecidableEq Ω] {m : ℕ} (f : Bits m → Ω) :
    ∑ x, finiteSeedLaw f x = 1 := by
  classical
  rw [finiteSeedLaw_as_fiberMass, fiberMass_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Bits, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  exact mul_one_div_cancel (by positivity)

theorem finiteSeedLaw_pos_iff {Ω : Type} [Fintype Ω] [DecidableEq Ω] {m : ℕ} (f : Bits m → Ω) (x : Ω) :
    0 < finiteSeedLaw f x ↔ ∃ seed, f seed = x := by
  classical
  rw [finiteSeedLaw_as_fiberMass, fiberMass_pos_iff _ _ (fun _ => by positivity)]
  simp only [show (0 : ℝ) < 1 / 2 ^ m by positivity, and_true]

theorem finiteSeedLaw_map {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ] [DecidableEq Ω] [DecidableEq Ξ] {m : ℕ}
    (f : Bits m → Ω) (g : Ω → Ξ) :
    finiteSeedLaw (g ∘ f) = fiberMass g (finiteSeedLaw f) := by
  classical
  funext z
  exact finite_sampler_projection f g (2 ^ m) (finiteSeedLaw f) (fun _ => rfl) z

theorem finiteSeedLaw_equiv {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ] [DecidableEq Ω] [DecidableEq Ξ] {m : ℕ}
    (f : Bits m → Ω) (e : Ω ≃ Ξ) (x : Ξ) :
    finiteSeedLaw (e ∘ f) x = finiteSeedLaw f (e.symm x) := by
  classical
  unfold finiteSeedLaw
  congr 2
  apply Fintype.card_congr
  exact {
    toFun := fun seed => ⟨seed.val, e.injective (seed.property.trans (e.apply_symm_apply x).symm)⟩
    invFun := fun seed => ⟨seed.val, by change e (f seed.val) = x; rw [seed.property, e.apply_symm_apply]⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem tv_equiv_pullback {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]
    (e : Ω ≃ Ξ) (p q : Ξ → ℝ) : tv (p ∘ e) (q ∘ e) = tv p q := by
  simp only [tv, Function.comp_apply]
  rw [e.sum_comp (fun x => |p x - q x|)]



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_CircuitCertificates
section
set_option autoImplicit false
namespace FSS23105365

/-- A straight-line register computation; both values and depths use it. -/
def runRegisters {A G : Type} (step : List A → G → A) (gs : List G) (vs : List A) : List A :=
  gs.foldl (fun xs g => xs ++ [step xs g]) vs



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

end

-- Source module: Solutions.FSS23105365_CircuitPrograms
section
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

end

-- Source module: Solutions.FSS23105365_CircuitRewiring
section
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

end

-- Source module: Solutions.FSS23105365_CircuitComposition
section
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



end FSS23105365

end

-- Source module: Solutions.FSS23105365_CircuitParallel
section
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



end FSS23105365

end

-- Source module: Solutions.FSS23105365_CircuitFormula
section
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



end FSS23105365

end

-- Source module: Solutions.FSS23105365_CircuitLookup
section
set_option autoImplicit false
noncomputable section
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



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_CircuitLocalMaps
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_FormulaConnectives
section
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

end

-- Source module: Solutions.FSS23105365_CircuitFiniteFamilies
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_BitComparison
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- Binary digits of an integer below `2^m`, in little-endian order. -/
def rankBits {m : ℕ} (u : Fin (2 ^ m)) : Bits m :=
  fun i => u.val.testBit i.val

theorem rankBits_injective (m : ℕ) : Function.Injective (@rankBits m) := by
  intro u v h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < m
  · exact congrFun h ⟨i, hi⟩
  · have hp : 2 ^ m ≤ 2 ^ i := pow_le_pow_right' (by omega) (by omega)
    rw [Nat.testBit_eq_false_of_lt (u.isLt.trans_le hp),
      Nat.testBit_eq_false_of_lt (v.isLt.trans_le hp)]

def rankBitsEquiv (m : ℕ) : Fin (2 ^ m) ≃ Bits m :=
  Equiv.ofBijective rankBits ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨rankBits_injective m, by simp [Bits, Fintype.card_fun]⟩)

/-- Numerical order is determined by the largest differing bit. -/
theorem rank_lt_iff {m : ℕ} (u v : Fin (2 ^ m)) :
    u < v ↔ ∃ i : Fin m, rankBits u i = false ∧ rankBits v i = true ∧
      ∀ j : Fin m, i < j → rankBits u j = rankBits v j := by
  classical
  have high (j : ℕ) (hj : m ≤ j) : u.val.testBit j = v.val.testBit j := by
    have hp : 2 ^ m ≤ 2 ^ j := pow_le_pow_right' (by omega) hj
    rw [Nat.testBit_eq_false_of_lt (u.isLt.trans_le hp),
      Nat.testBit_eq_false_of_lt (v.isLt.trans_le hp)]
  constructor
  · intro huv
    let s := Finset.univ.filter (fun i : Fin m => rankBits u i ≠ rankBits v i)
    have hs : s.Nonempty := by
      by_contra h
      have he : rankBits u = rankBits v := by
        funext i
        by_contra hi
        exact h ⟨i, by simp [s, hi]⟩
      exact (ne_of_lt huv) (rankBits_injective m he)
    let i := s.max' hs
    have hi : rankBits u i ≠ rankBits v i :=
      (Finset.mem_filter.mp (s.max'_mem hs)).2
    have hafter (j : Fin m) (hij : i < j) : rankBits u j = rankBits v j := by
      by_contra h
      have hj : j ∈ s := by simp [s, h]
      exact (not_le_of_gt hij) (s.le_max' j hj)
    have hafterNat (j : ℕ) (hij : i.val < j) :
        u.val.testBit j = v.val.testBit j := by
      by_cases hj : j < m
      · exact hafter ⟨j, hj⟩ hij
      · exact high j (by omega)
    have hbits : rankBits u i = false ∧ rankBits v i = true := by
      cases hu : rankBits u i <;> cases hv : rankBits v i
      · exact False.elim (hi (hu.trans hv.symm))
      · exact ⟨rfl, rfl⟩
      · have hrev := Nat.lt_of_testBit i.val hv hu
          (fun j hj => (hafterNat j hj).symm)
        exact False.elim ((not_lt_of_ge huv.le) hrev)
      · exact False.elim (hi (hu.trans hv.symm))
    exact ⟨i, hbits.1, hbits.2, hafter⟩
  · rintro ⟨i, hu, hv, he⟩
    apply Nat.lt_of_testBit i.val hu hv
    intro j hij
    by_cases hj : j < m
    · exact he ⟨j, hj⟩ hij
    · exact high j (by omega)

/-- One comparison clause fixes the pivot to zero and all higher bits to
the hardwired endpoint. Lower bits are unconstrained. -/
def comparisonClause {m : ℕ} (endpoint : Bits m) (i : Fin m) : CircuitFormula m :=
  .all m (fun j => if i < j then lookupLiteral endpoint j
    else if j = i then .neg (.input j) else .constant true)

theorem comparisonClause_eval {m : ℕ} (endpoint seed : Bits m) (i : Fin m) :
    formulaEval (comparisonClause endpoint i) seed = true ↔
      seed i = false ∧ ∀ j : Fin m, i < j → seed j = endpoint j := by
  have hh : formulaEval (comparisonClause endpoint i) seed = true ↔
      ∀ j : Fin m, formulaEval
        (if i < j then lookupLiteral endpoint j
          else if j = i then .neg (.input j) else .constant true) seed = true := by
    simp only [comparisonClause, formulaEval, List.all_eq_true, List.mem_ofFn]
    constructor
    · intro h j; exact h _ ⟨j, rfl⟩
    · rintro h y ⟨j, rfl⟩; exact h j
  rw [hh]
  constructor
  · intro h
    constructor
    · simpa [formulaEval] using h i
    · intro j hj
      simpa only [hj, if_true, lookupLiteral_true_iff] using h j
  · rintro ⟨hi, hh⟩ j
    by_cases hj : i < j
    · simp only [hj, if_true, lookupLiteral_true_iff]
      exact hh j hj
    · by_cases he : j = i
      · subst j; simp [formulaEval, hi]
      · simp [hj, he, formulaEval]

theorem comparisonClause_depth {m : ℕ} (endpoint : Bits m) (i : Fin m) :
    formulaDepth (comparisonClause endpoint i) ≤ 2 := by
  change Finset.univ.sup (fun j => formulaDepth _) + 1 ≤ 2
  have hh : Finset.univ.sup (fun j : Fin m => formulaDepth
      (if i < j then lookupLiteral endpoint j
        else if j = i then .neg (.input j) else .constant true)) ≤ 1 := by
    apply Finset.sup_le
    intro j _
    split_ifs
    · cases he : endpoint j <;> simp [lookupLiteral, formulaDepth, he]
    · simp [formulaDepth]
    · simp [formulaDepth]
  omega

theorem comparisonClause_cost {m : ℕ} (endpoint : Bits m) (i : Fin m) :
    formulaCost (comparisonClause endpoint i) ≤ 3 * m + 1 := by
  have hh : (∑ j : Fin m, formulaCost
      (if i < j then lookupLiteral endpoint j
        else if j = i then .neg (.input j) else .constant true)) ≤ 2 * m := by
    calc
      _ ≤ ∑ _j : Fin m, 2 := by
        apply Finset.sum_le_sum
        intro j _
        split_ifs
        · cases he : endpoint j <;> simp [lookupLiteral, formulaCost, he]
        · simp [formulaCost]
        · simp [formulaCost]
      _ = _ := by simp; omega
  change (∑ j, formulaCost _) + 1 + m ≤ _
  omega

/-- Compare an `m`-bit rank to any hardwired natural-number endpoint.
Endpoints at or beyond `2^m` give the constant-true comparison. -/
def rankLessFormula (m endpoint : ℕ) : CircuitFormula m :=
  if h : endpoint < 2 ^ m then
    .any m (fun i => if endpoint.testBit i.val then
      comparisonClause (rankBits ⟨endpoint, h⟩) i else .constant false)
  else .constant true

theorem rankLessFormula_eval (m endpoint : ℕ) (seed : Bits m) :
    formulaEval (rankLessFormula m endpoint) seed = true ↔
      ((rankBitsEquiv m).symm seed).val < endpoint := by
  let u := (rankBitsEquiv m).symm seed
  have hu : rankBits u = seed := (rankBitsEquiv m).apply_symm_apply seed
  have hu' (i : Fin m) : u.val.testBit i.val = seed i := congrFun hu i
  by_cases he : endpoint < 2 ^ m
  · rw [rankLessFormula, dif_pos he, formulaAny_true_iff]
    have hc (i : Fin m) : formulaEval
        (if endpoint.testBit i.val then comparisonClause (rankBits ⟨endpoint, he⟩) i
          else .constant false) seed = true ↔
        endpoint.testBit i.val = true ∧ seed i = false ∧
          ∀ j : Fin m, i < j → seed j = rankBits ⟨endpoint, he⟩ j := by
      cases hb : endpoint.testBit i.val <;> simp [hb, formulaEval, comparisonClause_eval]
    simp_rw [hc]
    change _ ↔ u < (⟨endpoint, he⟩ : Fin (2 ^ m))
    simpa only [rankBits, hu', and_comm, and_left_comm, and_assoc] using
      (rank_lt_iff u ⟨endpoint, he⟩).symm
  · simp only [rankLessFormula, dif_neg he, formulaEval, true_iff]
    exact u.isLt.trans_le (by omega)

theorem rankLessFormula_depth (m endpoint : ℕ) :
    formulaDepth (rankLessFormula m endpoint) ≤ 3 := by
  unfold rankLessFormula
  split
  · change Finset.univ.sup (fun i => formulaDepth _) + 1 ≤ 3
    have hh : Finset.univ.sup (fun i : Fin m => formulaDepth
        (if endpoint.testBit i.val then comparisonClause (rankBits ⟨endpoint, by assumption⟩) i
          else .constant false)) ≤ 2 := by
      apply Finset.sup_le
      intro i _
      split_ifs
      · exact comparisonClause_depth _ _
      · simp [formulaDepth]
    omega
  · simp [formulaDepth]

theorem rankLessFormula_cost (m endpoint : ℕ) :
    formulaCost (rankLessFormula m endpoint) ≤ m * (3 * m + 2) + 1 := by
  unfold rankLessFormula
  split
  · have hh : (∑ i : Fin m, formulaCost
        (if endpoint.testBit i.val then comparisonClause (rankBits ⟨endpoint, by assumption⟩) i
          else .constant false)) ≤ m * (3 * m + 1) := by
      calc
        _ ≤ ∑ _i : Fin m, (3 * m + 1) := by
          apply Finset.sum_le_sum
          intro i _
          split_ifs
          · exact comparisonClause_cost _ _
          · simp [formulaCost]
        _ = _ := by simp
    change (∑ i, formulaCost _) + 1 + m ≤ _
    nlinarith
  · simp [formulaCost]

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_IntegerQuantile
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_QuantileCircuits
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def seedRankEquiv {M m : ℕ} (a : Fin M → ℕ) (ha : ∑ i, a i = 2 ^ m) :
    Bits m ≃ Fin (∑ i, a i) :=
  (rankBitsEquiv m).symm.trans (finCongr ha.symm)

def seedQuantile {M m : ℕ} (a : Fin M → ℕ) (ha : ∑ i, a i = 2 ^ m)
    (seed : Bits m) : Fin M := integerQuantile a (seedRankEquiv a ha seed)

theorem seedQuantile_fiber_card {M m : ℕ} (a : Fin M → ℕ)
    (ha : ∑ i, a i = 2 ^ m) (i : Fin M) :
    Fintype.card {seed : Bits m // seedQuantile a ha seed = i} = a i := by
  let e : {seed : Bits m // seedQuantile a ha seed = i} ≃
      {u : Fin (∑ j, a j) // integerQuantile a u = i} :=
    (seedRankEquiv a ha).subtypeEquiv (fun _ => Iff.rfl)
  exact (Fintype.card_congr e).trans (integerQuantile_fiber_card a i)

def rankIntervalFormula (m lower upper : ℕ) : CircuitFormula m :=
  formulaAnd (.neg (rankLessFormula m lower)) (rankLessFormula m upper)

theorem rankIntervalFormula_eval (m lower upper : ℕ) (seed : Bits m) :
    formulaEval (rankIntervalFormula m lower upper) seed = true ↔
      lower ≤ ((rankBitsEquiv m).symm seed).val ∧
      ((rankBitsEquiv m).symm seed).val < upper := by
  rw [rankIntervalFormula, formulaAnd_eval, Bool.and_eq_true]
  change ((!formulaEval (rankLessFormula m lower) seed) = true ∧
    formulaEval (rankLessFormula m upper) seed = true) ↔ _
  have hn : (!formulaEval (rankLessFormula m lower) seed) = true ↔
      ¬formulaEval (rankLessFormula m lower) seed = true := by
    cases formulaEval (rankLessFormula m lower) seed <;> decide
  rw [hn, rankLessFormula_eval, rankLessFormula_eval, not_lt]

theorem rankIntervalFormula_depth (m lower upper : ℕ) :
    formulaDepth (rankIntervalFormula m lower upper) ≤ 5 := by
  rw [rankIntervalFormula, formulaAnd_depth]
  change max (formulaDepth (rankLessFormula m lower) + 1)
    (formulaDepth (rankLessFormula m upper)) + 1 ≤ 5
  have hl := rankLessFormula_depth m lower
  have hu := rankLessFormula_depth m upper
  omega

theorem rankIntervalFormula_cost (m lower upper : ℕ) :
    formulaCost (rankIntervalFormula m lower upper) ≤ 2 * (m * (3 * m + 2) + 1) + 5 := by
  rw [rankIntervalFormula, formulaAnd_cost]
  change formulaCost (rankLessFormula m lower) + 2 +
    formulaCost (rankLessFormula m upper) + 3 ≤ _
  have hl := rankLessFormula_cost m lower
  have hu := rankLessFormula_cost m upper
  omega

theorem quantile_interval_test {M m : ℕ} (a : Fin M → ℕ)
    (ha : ∑ i, a i = 2 ^ m) (seed : Bits m) (i : Fin M) :
    formulaEval (rankIntervalFormula m (countPrefix a i.val)
      (countPrefix a (i.val + 1))) seed = true ↔ seedQuantile a ha seed = i := by
  rw [rankIntervalFormula_eval, seedQuantile, integerQuantile_eq_iff]
  rfl

/-- Inverse-CDF sampling from prescribed dyadic counts, with an actual
depth-six circuit and polynomial gate-and-wire size. -/
theorem quantile_circuit {M m : ℕ} {Out : Type} [Fintype Out]
    (a : Fin M → ℕ) (ha : ∑ i, a i = 2 ^ m) (encode : Fin M → Out → Bool) :
    ∃ S : Circuit Out, ∃ hbits : S.randomBits = m,
      S.depth ≤ 6 ∧
      S.size ≤ m + Fintype.card Out * (M * (2 * (m * (3 * m + 2) + 1) + 6) + 2) ∧
      ∀ seed : Bits m, S.eval (fun j => seed (Fin.cast hbits j)) =
        encode (seedQuantile a ha seed) := by
  classical
  let K := 2 * (m * (3 * m + 2) + 1) + 5
  let child (o : Out) (i : Fin M) : CircuitFormula m :=
    if encode i o then rankIntervalFormula m (countPrefix a i.val)
      (countPrefix a (i.val + 1)) else .constant false
  let fs (o : Out) := formulaIndexedAny (child o)
  have hchildD (o : Out) (i : Fin M) : formulaDepth (child o i) ≤ 5 := by
    dsimp only [child]
    split_ifs
    · exact rankIntervalFormula_depth _ _ _
    · simp [formulaDepth]
  have hchildC (o : Out) (i : Fin M) : formulaCost (child o i) ≤ K := by
    dsimp only [child]
    split_ifs
    · exact rankIntervalFormula_cost _ _ _
    · simp [K, formulaCost]
  have hd (o : Out) : formulaDepth (fs o) ≤ 6 :=
    formulaIndexedAny_depth (child o) 5 (hchildD o)
  have hc (o : Out) : formulaCost (fs o) ≤ M * (K + 1) + 1 := by
    simpa only [Fintype.card_fin] using formulaIndexedAny_cost (child o) K (hchildC o)
  obtain ⟨S, hbits, he, hD, hsize⟩ := formula_fintype_family_circuit fs 6 hd
  refine ⟨S, hbits, hD, ?_, ?_⟩
  · have hsum := Finset.sum_le_sum (fun o (_ : o ∈ Finset.univ) => hc o)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    rw [hsize]
    dsimp only [K] at hsum
    nlinarith
  · intro seed
    funext o
    rw [he]
    apply Bool.eq_iff_iff.mpr
    rw [formulaIndexedAny_eval]
    have hchild (i : Fin M) : formulaEval (child o i) seed = true ↔
        encode i o = true ∧ seedQuantile a ha seed = i := by
      dsimp only [child]
      cases hb : encode i o
      · simp [formulaEval]
      · simp only [if_true, true_and]
        exact quantile_interval_test a ha seed i
    simp_rw [hchild]
    simp



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_FiniteRoundingRealization
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- C.2 with the actual sampling function retained, so independent draws
can be composed probabilistically and the same function wired in a circuit. -/
theorem rounding_AC0_function_fin_budget {M : ℕ}
    {Out : Type} [Fintype Out] (encode : Fin M → Out → Bool)
    (p : Fin M → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (m : ℕ) (δ : ℝ) (hbudget : (M : ℝ) / 2 ^ m ≤ δ) :
    ∃ f : Bits m → Fin M, ∃ S : Circuit Out,
      ∃ hbits : S.randomBits = m,
        (∀ seed, S.eval (fun i => seed (Fin.cast hbits i)) = encode (f seed)) ∧
        (∀ seed, 0 < p (f seed)) ∧ tv (finiteSeedLaw f) p ≤ δ ∧ S.depth ≤ 6 ∧
        S.size ≤ m + Fintype.card Out * (M * (2 * (m * (3 * m + 2) + 1) + 6) + 2) := by
  obtain ⟨a, ha, hzero, herr⟩ := probability_rounding_counts p hp hsum (2 ^ m) (by positivity)
  obtain ⟨S, hbits, hD, hsize, he⟩ := quantile_circuit a ha encode
  let f := seedQuantile a ha
  have hs (seed : Bits m) : 0 < p (f seed) := by
    by_contra h
    have hz : p (f seed) = 0 := le_antisymm (le_of_not_gt h) (hp _)
    have hc : 0 < Fintype.card {u : Bits m // f u = f seed} :=
      Fintype.card_pos_iff.mpr ⟨⟨seed, rfl⟩⟩
    rw [seedQuantile_fiber_card, hzero _ hz] at hc
    omega
  have hlaw : finiteSeedLaw f = fun i => (a i : ℝ) / 2 ^ m := by
    funext i
    change (Fintype.card {u : Bits m // seedQuantile a ha u = i} : ℝ) / 2 ^ m = _
    rw [seedQuantile_fiber_card]
  refine ⟨f, S, hbits, he, hs, ?_, hD, hsize⟩
  rw [hlaw]
  calc
    _ ≤ (M : ℝ) / (2 * (2 : ℝ) ^ m) := by
      simpa only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] using herr
    _ ≤ (M : ℝ) / (2 : ℝ) ^ m := by
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) m]
    _ ≤ δ := hbudget

theorem rounding_AC0_function_fin {M : ℕ} (hM : 0 < M)
    {Out : Type} [Fintype Out] (encode : Fin M → Out → Bool)
    (p : Fin M → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ f : Bits (roundingSeed M δ) → Fin M, ∃ S : Circuit Out,
      ∃ hbits : S.randomBits = roundingSeed M δ,
        (∀ seed, S.eval (fun i => seed (Fin.cast hbits i)) = encode (f seed)) ∧
        (∀ seed, 0 < p (f seed)) ∧ tv (finiteSeedLaw f) p ≤ δ ∧ S.depth ≤ 6 ∧
        S.size ≤ roundingSeed M δ + Fintype.card Out *
          (M * (2 * (roundingSeed M δ * (3 * roundingSeed M δ + 2) + 1) + 6) + 2) :=
  rounding_AC0_function_fin_budget encode p hp hsum _ δ (roundingSeed_denominator_bound M hM δ hδ)

/-- A prescribed common seed length can be used for multiple conditional
laws whenever it meets their cardinality bound. This avoids summing seed
budgets over mutually exclusive endpoint branches. -/
theorem rounding_AC0_function_budget {Ω Out : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Out]
    (encode : Ω → Out → Bool) (p : Ω → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (m : ℕ) (δ : ℝ) (hbudget : (Fintype.card Ω : ℝ) / 2 ^ m ≤ δ) :
    ∃ f : Bits m → Ω, ∃ S : Circuit Out, ∃ hbits : S.randomBits = m,
      (∀ seed, S.eval (fun i => seed (Fin.cast hbits i)) = encode (f seed)) ∧
      (∀ seed, 0 < p (f seed)) ∧ tv (finiteSeedLaw f) p ≤ δ ∧ S.depth ≤ 6 ∧
      S.size ≤ m + Fintype.card Out * (Fintype.card Ω * (2 * (m * (3 * m + 2) + 1) + 6) + 2) := by
  classical
  let e := Fintype.equivFin Ω
  let p' := p ∘ e.symm
  have hpsum : ∑ i, p' i = 1 := (e.symm.sum_comp p).trans hsum
  obtain ⟨f, S, hbits, he, hs, htv, hD, hsize⟩ := rounding_AC0_function_fin_budget
    (encode ∘ e.symm) p' (fun i => hp (e.symm i)) hpsum m δ hbudget
  refine ⟨e.symm ∘ f, S, hbits, he, hs, ?_, hD, hsize⟩
  have h1 : finiteSeedLaw (e.symm ∘ f) = (finiteSeedLaw f) ∘ e := by
    funext x
    exact finiteSeedLaw_equiv f e.symm x
  have h2 : p = p' ∘ e := by funext x; simp [p', Function.comp_def]
  rw [h1, h2, tv_equiv_pullback]
  exact htv

/-- The same concrete rounding circuit works on every finite outcome
space, including endpoint-path subtypes and support-class boundary states.
Both the fair-bit function and its actual depth-six circuit are produced. -/
theorem rounding_AC0_function {Ω Out : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Out]
    (encode : Ω → Out → Bool) (p : Ω → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) (δ : ℝ) (hδ : 0 < δ) :
    ∃ f : Bits (roundingSeed (Fintype.card Ω) δ) → Ω, ∃ S : Circuit Out,
      ∃ hbits : S.randomBits = roundingSeed (Fintype.card Ω) δ,
        (∀ seed, S.eval (fun i => seed (Fin.cast hbits i)) = encode (f seed)) ∧
        (∀ seed, 0 < p (f seed)) ∧ tv (finiteSeedLaw f) p ≤ δ ∧ S.depth ≤ 6 ∧
        S.size ≤ roundingSeed (Fintype.card Ω) δ + Fintype.card Out *
          (Fintype.card Ω * (2 * (roundingSeed (Fintype.card Ω) δ *
            (3 * roundingSeed (Fintype.card Ω) δ + 2) + 1) + 6) + 2) := by
  classical
  let e := Fintype.equivFin Ω
  let p' := p ∘ e.symm
  have hpsum : ∑ i, p' i = 1 := (e.symm.sum_comp p).trans hsum
  have hM : 0 < Fintype.card Ω := by
    by_contra h
    have hz : Fintype.card Ω = 0 := by omega
    haveI := Fintype.card_eq_zero_iff.mp hz
    simp at hsum
  obtain ⟨f, S, hbits, he, hs, htv, hD, hsize⟩ := rounding_AC0_function_fin hM
    (encode ∘ e.symm) p' (fun i => hp (e.symm i)) hpsum δ hδ
  refine ⟨e.symm ∘ f, S, hbits, he, hs, ?_, hD, hsize⟩
  have h1 : finiteSeedLaw (e.symm ∘ f) = (finiteSeedLaw f) ∘ e := by
    funext x
    exact finiteSeedLaw_equiv f e.symm x
  have h2 : p = p' ∘ e := by funext x; simp [p', Function.comp_def]
  rw [h1, h2, tv_equiv_pullback]
  exact htv

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_WeightedMixtures
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def mixtureLaw {C Ω : Type} [Fintype C] (p : C → ℝ) (K : C → Ω → ℝ) : Ω → ℝ :=
  fun x => ∑ c, p c * K c x

theorem mixtureLaw_nonneg {C Ω : Type} [Fintype C] (p : C → ℝ) (K : C → Ω → ℝ)
    (hp : ∀ c, 0 ≤ p c) (hK : ∀ c x, 0 ≤ K c x) : ∀ x, 0 ≤ mixtureLaw p K x :=
  fun x => Finset.sum_nonneg (fun c _ => mul_nonneg (hp c) (hK c x))

theorem mixtureLaw_sum {C Ω : Type} [Fintype C] [Fintype Ω]
    (p : C → ℝ) (K : C → Ω → ℝ) (hp : ∑ c, p c = 1) (hK : ∀ c, ∑ x, K c x = 1) :
    ∑ x, mixtureLaw p K x = 1 := by
  unfold mixtureLaw
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hK, mul_one]
  exact hp

theorem mixtureLaw_as_pushforward {C Ω : Type} [Fintype C] [Fintype Ω] [DecidableEq Ω]
    (p : C → ℝ) (K : C → Ω → ℝ) (x : Ω) :
    (∑ z : C × Ω, if z.2 = x then p z.1 * K z.1 z.2 else 0) = mixtureLaw p K x := by
  classical
  rw [Fintype.sum_prod_type]
  simp [mixtureLaw]

theorem tv_mixture_le {C Ω : Type} [Fintype C] [Fintype Ω]
    (p q : C → ℝ) (K L : C → Ω → ℝ)
    (hq : ∀ c, 0 ≤ q c) (hK : ∀ c x, 0 ≤ K c x) (hKsum : ∀ c, ∑ x, K c x = 1) :
    tv (mixtureLaw p K) (mixtureLaw q L) ≤ tv p q + ∑ c, q c * tv (K c) (L c) := by
  classical
  have h := tv_map_le (fun z : C × Ω => z.2)
    (fun z => p z.1 * K z.1 z.2) (fun z => q z.1 * L z.1 z.2)
  simp only [mixtureLaw_as_pushforward] at h
  exact h.trans (tv_joint_le p q K L hq hK hKsum)

theorem tv_mixture_le_uniform {C Ω : Type} [Fintype C] [Fintype Ω]
    (p q : C → ℝ) (K L : C → Ω → ℝ)
    (hq : ∀ c, 0 ≤ q c) (hqsum : ∑ c, q c = 1)
    (hK : ∀ c x, 0 ≤ K c x) (hKsum : ∀ c, ∑ x, K c x = 1)
    (δ η : ℝ) (hpq : tv p q ≤ δ) (hKL : ∀ c, tv (K c) (L c) ≤ η) :
    tv (mixtureLaw p K) (mixtureLaw q L) ≤ δ + η := by
  apply (tv_mixture_le p q K L hq hK hKsum).trans
  apply add_le_add hpq
  calc
    _ ≤ ∑ c, q c * η := Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (hKL c) (hq c))
    _ = η := by rw [← Finset.sum_mul, hqsum, one_mul]

theorem mixtureLaw_pos_iff {C Ω : Type} [Fintype C]
    (p : C → ℝ) (K : C → Ω → ℝ) (hp : ∀ c, 0 ≤ p c) (hK : ∀ c x, 0 ≤ K c x) (x : Ω) :
    0 < mixtureLaw p K x ↔ ∃ c, 0 < p c ∧ 0 < K c x := by
  classical
  rw [mixtureLaw, Finset.sum_pos_iff_of_nonneg (fun c _ => mul_nonneg (hp c) (hK c x))]
  simp only [Finset.mem_univ, true_and]
  apply exists_congr
  intro c
  constructor
  · intro h
    exact ⟨pos_of_mul_pos_left h (hK c x), pos_of_mul_pos_right h (hp c)⟩
  · rintro ⟨h1, h2⟩
    exact mul_pos h1 h2

/-- Category rounding and conditional rounding combine additively, while
support preservation passes to the complete reconstructed law. Zero-mass
categories are excluded by the positive-fiber type, with no lower bound on
the positive masses. -/
theorem approximate_disintegration {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C]
    (f : Ω → C) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hZ : 0 < ∑ x, w x)
    (q : PositiveFiber f w → ℝ) (L : PositiveFiber f w → Ω → ℝ)
    (hq : ∀ c, 0 ≤ q c) (hqsum : ∑ c, q c = 1)
    (hL : ∀ c x, 0 ≤ L c x) (hLsum : ∀ c, ∑ x, L c x = 1)
    (hsupp : ∀ c x, 0 < L c x → 0 < fiberWeight f w c.val x)
    (δ η : ℝ)
    (hcat : tv q (normalizeWeights (fun c : PositiveFiber f w => fiberMass f w c.val)) ≤ δ)
    (hcond : ∀ c, tv (L c) (normalizeWeights (fiberWeight f w c.val)) ≤ η) :
    (∀ x, 0 ≤ mixtureLaw q L x) ∧ (∑ x, mixtureLaw q L x = 1) ∧
    (∀ x, 0 < mixtureLaw q L x → 0 < w x) ∧
    tv (mixtureLaw q L) (normalizeWeights w) ≤ δ + η := by
  classical
  let p := normalizeWeights (fun c : PositiveFiber f w => fiberMass f w c.val)
  let K := fun c : PositiveFiber f w => normalizeWeights (fiberWeight f w c.val)
  have hp : ∀ c, 0 ≤ p c := normalizeWeights_nonneg _ (fun c => c.property.le)
  have hpsum : ∑ c, p c = 1 := normalizeWeights_sum _ (by
    simpa only [positiveFiber_mass_sum f w hw] using hZ)
  have he : mixtureLaw p K = normalizeWeights w := by
    funext x
    exact positiveFiber_disintegration f w hw hZ x
  refine ⟨mixtureLaw_nonneg q L hq hL, mixtureLaw_sum q L hqsum hLsum, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, _, hc⟩ := (mixtureLaw_pos_iff q L hq hL x).mp hx
    have hs := hsupp c x hc
    unfold fiberWeight at hs
    split_ifs at hs with hf
    · exact hs
    · exact False.elim ((lt_irrefl 0) hs)
  · rw [← he]
    exact tv_mixture_le_uniform q p L K hp hpsum hL hLsum δ η hcat hcond

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_PositiveKernelContraction
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_PositiveKernelConvergence
section
set_option autoImplicit false
noncomputable section
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
paper's cited convergence statement as an unproved axiom. -/
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

end
end

-- Source module: Solutions.FSS23105365_KernelGeometricMixing
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open Filter
open scoped BigOperators Topology

/-- A coordinatewise limit of a finite time-homogeneous kernel orbit is
stationary. This is proved by passing the finite sum to the limit. -/
theorem kernel_limit_stationary {Q : Type} [Fintype Q]
    (P : Q → Q → ℝ) (p π : Q → ℝ)
    (hlim : ∀ y, Tendsto (fun n => (kernelAdvance P)^[n] p y) atTop (𝓝 (π y))) :
    kernelAdvance P π = π := by
  funext y
  have hs := tendsto_finsetSum Finset.univ
    (fun x _ => (hlim x).mul_const (P x y))
  have hs' : Tendsto (fun n => (kernelAdvance P)^[n + 1] p y)
      atTop (𝓝 (kernelAdvance P π y)) := by
    simpa only [Function.iterate_succ_apply', kernelAdvance] using hs
  have ht := (hlim y).comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hs' ht

theorem kernel_stationary_iterate {Q : Type} [Fintype Q]
    (P : Q → Q → ℝ) (π : Q → ℝ) (hπ : kernelAdvance P π = π) (n : ℕ) :
    (kernelAdvance P)^[n] π = π := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, hπ]

/-- Quantitative version of the positive-kernel convergence theorem.
The same geometric bound works for every starting probability distribution. -/
theorem positive_kernel_geometric_mixing {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (P : Q → Q → ℝ) (hP : ∀ x y, 0 < P x y) (hrows : ∀ x, ∑ y, P x y = 1) :
    ∃ π : Q → ℝ, ∃ ρ : ℝ,
      (∀ y, 0 < π y) ∧ (∑ y, π y = 1) ∧ kernelAdvance P π = π ∧
      0 < ρ ∧ ρ < 1 ∧
      ∀ p : Q → ℝ, (∀ x, 0 ≤ p x) → (∑ x, p x = 1) →
        ∀ n y, |(kernelAdvance P)^[n] p y - π y| ≤ 2 * ρ ^ n := by
  obtain ⟨π, hπpos, hπsum, hlim⟩ := positive_kernel_common_limit P hP hrows
  have hstat := kernel_limit_stationary P π π
    (hlim π (fun x => (hπpos x).le) hπsum)
  obtain ⟨z, ε, hεpos, hεlt, hminor⟩ := positive_kernel_minorization P hP hrows
  refine ⟨π, 1 - ε, hπpos, hπsum, hstat, by linarith, by linarith, ?_⟩
  intro p hp hp1 n y
  have h := kernel_iterate_coordinate_distance P (fun x y => (hP x y).le) hrows
    z ε hεlt.le hminor p π hp (fun x => (hπpos x).le) hp1 hπsum n y
  simpa only [kernel_stationary_iterate P π hstat] using h

/-- Strict positivity of the stationary law upgrades the common absolute
mixing rate to a uniform relative error rate. -/
theorem positive_kernel_relative_mixing {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (P : Q → Q → ℝ) (hP : ∀ x y, 0 < P x y) (hrows : ∀ x, ∑ y, P x y = 1) :
    ∃ π : Q → ℝ, ∃ C ρ : ℝ,
      (∀ y, 0 < π y) ∧ (∑ y, π y = 1) ∧ kernelAdvance P π = π ∧
      0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ p : Q → ℝ, (∀ x, 0 ≤ p x) → (∑ x, p x = 1) →
        ∀ n y, |(kernelAdvance P)^[n] p y / π y - 1| ≤ C * ρ ^ n := by
  classical
  obtain ⟨π, ρ, hπpos, hπsum, hstat, hρpos, hρlt, hmix⟩ :=
    positive_kernel_geometric_mixing P hP hrows
  let a := Finset.univ.inf' Finset.univ_nonempty π
  have ha : 0 < a := (Finset.lt_inf'_iff _).mpr (fun y _ => hπpos y)
  have hay (y : Q) : a ≤ π y := Finset.inf'_le _ (Finset.mem_univ y)
  refine ⟨π, 2 / a, ρ, hπpos, hπsum, hstat, by positivity, hρpos, hρlt, ?_⟩
  intro p hp hp1 n y
  calc
    _ = |((kernelAdvance P)^[n] p y - π y) / π y| := by
      congr 1
      field_simp [ne_of_gt (hπpos y)]
    _ = |(kernelAdvance P)^[n] p y - π y| / π y := by
      rw [abs_div, abs_of_pos (hπpos y)]
    _ ≤ (2 * ρ ^ n) / π y :=
      div_le_div_of_nonneg_right (hmix p hp hp1 n y) (hπpos y).le
    _ ≤ (2 * ρ ^ n) / a :=
      div_le_div_of_nonneg_left (by positivity) ha (hay y)
    _ = _ := by ring

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_DoobTransform
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- The Perron/Doob transform from the proofs of C.3 and E.6. -/
def doobKernel {Q : Type} (W : Q → Q → ℝ) (lam : ℝ) (r : Q → ℝ) : Q → Q → ℝ :=
  fun x y => W x y * r y / (lam * r x)

theorem doobKernel_nonneg {Q : Type} (W : Q → Q → ℝ)
    (hW : ∀ x y, 0 ≤ W x y) (lam : ℝ) (hlam : 0 < lam)
    (r : Q → ℝ) (hr : ∀ x, 0 < r x) : ∀ x y, 0 ≤ doobKernel W lam r x y := by
  intro x y
  exact div_nonneg (mul_nonneg (hW x y) (hr y).le) (mul_pos hlam (hr x)).le

theorem doobKernel_pos_iff {Q : Type} (W : Q → Q → ℝ)
    (lam : ℝ) (hlam : 0 < lam) (r : Q → ℝ) (hr : ∀ x, 0 < r x) (x y : Q) :
    0 < doobKernel W lam r x y ↔ 0 < W x y := by
  rw [doobKernel, div_pos_iff_of_pos_right (mul_pos hlam (hr x)),
    mul_pos_iff_of_pos_right (hr y)]

theorem doobKernel_row_sum {Q : Type} [Fintype Q]
    (W : Q → Q → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (r : Q → ℝ) (hr : ∀ x, 0 < r x)
    (heigen : ∀ x, ∑ y, W x y * r y = lam * r x) :
    ∀ x, ∑ y, doobKernel W lam r x y = 1 := by
  intro x
  simp only [doobKernel, ← Finset.sum_div, heigen]
  exact div_self (mul_pos hlam (hr x)).ne'

/-- Left and right Perron eigenvectors give the stationary weights of the
transformed kernel. Existence of those eigenvectors is a separate obligation. -/
theorem doobKernel_stationary {Q : Type} [Fintype Q]
    (W : Q → Q → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (l r : Q → ℝ) (hr : ∀ x, 0 < r x)
    (heigen : ∀ y, ∑ x, l x * W x y = lam * l y) :
    kernelAdvance (doobKernel W lam r) (fun x => l x * r x) = fun x => l x * r x := by
  funext y
  have hpoint (x : Q) : l x * r x * doobKernel W lam r x y =
      (l x * W x y) * (r y / lam) := by
    unfold doobKernel
    field_simp [hlam.ne', (hr x).ne']
  unfold kernelAdvance
  simp_rw [hpoint]
  rw [← Finset.sum_mul, heigen]
  field_simp [hlam.ne']

/-- The exact matrix-power identity behind the periodic Perron estimate. -/
def doobMatrix {Q : Type} (W : Matrix Q Q ℝ) (lam : ℝ) (r : Q → ℝ) : Matrix Q Q ℝ :=
  fun x y => W x y * r y / (lam * r x)

theorem doobMatrix_power {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (lam : ℝ) (hlam : 0 < lam)
    (r : Q → ℝ) (hr : ∀ x, 0 < r x) (n : ℕ) :
    ∀ x y, (doobMatrix W lam r ^ n) x y =
      (W ^ n) x y * r y / (lam ^ n * r x) := by
  induction n with
  | zero =>
    intro x y
    by_cases hxy : x = y
    · subst y; simp [Matrix.one_apply, (hr x).ne']
    · simp [Matrix.one_apply, hxy]
  | succ n ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply, pow_succ, Matrix.mul_apply]
    have hpoint (z : Q) :
        ((W ^ n) x z * r z / (lam ^ n * r x)) * doobMatrix W lam r z y =
          ((W ^ n) x z * W z y) * r y / (lam ^ (n + 1) * r x) := by
      unfold doobMatrix
      rw [pow_succ]
      field_simp [hlam.ne', (hr x).ne', (hr z).ne']
      <;> ring
    simp_rw [ih, hpoint]
    rw [← Finset.sum_div, ← Finset.sum_mul]

/-- Product of edge weights along a whole state trajectory. -/
def edgePathWeight {Q : Type} (W : Q → Q → ℝ) {n : ℕ} (γ : Fin (n + 1) → Q) : ℝ :=
  finitePathWeight (fun _ => 1) W γ

theorem edgePathWeight_snoc {Q : Type} (W : Q → Q → ℝ) {n : ℕ}
    (γ : Fin (n + 1) → Q) (y : Q) :
    edgePathWeight W (Fin.snoc γ y) = edgePathWeight W γ * W (γ (Fin.last n)) y :=
  finitePathWeight_snoc _ _ _ _

/-- The Doob change of weights telescopes to a factor depending only on
the length and endpoints, so relative probabilities within a bridge survive. -/
theorem doobKernel_path_weight {Q : Type} (W : Q → Q → ℝ)
    (lam : ℝ) (hlam : 0 < lam) (r : Q → ℝ) (hr : ∀ x, 0 < r x)
    (n : ℕ) (γ : Fin (n + 1) → Q) :
    edgePathWeight (doobKernel W lam r) γ =
      edgePathWeight W γ * r (γ (Fin.last n)) / (lam ^ n * r (γ 0)) := by
  induction n with
  | zero => simp [edgePathWeight, finitePathWeight, (hr (γ 0)).ne']
  | succ n ih =>
    obtain ⟨⟨y, γ'⟩, rfl⟩ := (Fin.snocEquiv (fun _ : Fin (n + 2) => Q)).surjective γ
    change edgePathWeight (doobKernel W lam r) (Fin.snoc γ' y) =
      edgePathWeight W (Fin.snoc γ' y) *
        r ((Fin.snoc γ' y : Fin (n + 2) → Q) (Fin.last (n + 1))) /
        (lam ^ (n + 1) * r ((Fin.snoc γ' y : Fin (n + 2) → Q) 0))
    rw [edgePathWeight_snoc, edgePathWeight_snoc, ih]
    simp only [Fin.snoc_last, Fin.snoc_apply_zero, doobKernel, pow_succ]
    field_simp [hlam.ne', (hr (γ' 0)).ne', (hr (γ' (Fin.last n))).ne']
    <;> ring

def bridgeWeight {Q : Type} [DecidableEq Q] (W : Q → Q → ℝ)
    (s t : Q) (n : ℕ) (γ : Fin (n + 1) → Q) : ℝ :=
  if γ 0 = s ∧ γ (Fin.last n) = t then edgePathWeight W γ else 0

theorem doobKernel_bridge_weight {Q : Type} [DecidableEq Q] (W : Q → Q → ℝ)
    (lam : ℝ) (hlam : 0 < lam) (r : Q → ℝ) (hr : ∀ x, 0 < r x)
    (s t : Q) (n : ℕ) :
    bridgeWeight (doobKernel W lam r) s t n =
      fun γ => (r t / (lam ^ n * r s)) * bridgeWeight W s t n γ := by
  funext γ
  unfold bridgeWeight
  by_cases h : γ 0 = s ∧ γ (Fin.last n) = t
  · simp only [if_pos h]
    rw [doobKernel_path_weight W lam hlam r hr, h.1, h.2]
    ring
  · simp [h]

theorem doobKernel_bridge_law {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (lam : ℝ) (hlam : 0 < lam)
    (r : Q → ℝ) (hr : ∀ x, 0 < r x) (s t : Q) (n : ℕ) :
    normalizeWeights (bridgeWeight (doobKernel W lam r) s t n) =
      normalizeWeights (bridgeWeight W s t n) := by
  rw [doobKernel_bridge_weight W lam hlam r hr]
  apply normalizeWeights_scale
  exact (div_pos (hr t) (mul_pos (pow_pos hlam n) (hr s))).ne'

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_BridgePartition
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def bridgePartition {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (s t : Q) (n : ℕ) : ℝ :=
  ∑ γ, bridgeWeight W s t n γ

theorem bridgePartition_zero {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (s t : Q) : bridgePartition W s t 0 = if s = t then 1 else 0 := by
  let e : Q ≃ (Fin 1 → Q) := (Equiv.funUnique (Fin 1) Q).symm
  unfold bridgePartition
  rw [← e.sum_comp]
  have he (x : Q) : e x = fun _ => x := rfl
  simp only [he, bridgeWeight, edgePathWeight, finitePathWeight,
    Fin.prod_univ_zero, mul_one]
  by_cases hst : s = t
  · subst t; simp
  · simp [hst, ite_and]

theorem bridgePartition_succ {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (s t : Q) (n : ℕ) :
    bridgePartition W s t (n + 1) = ∑ u, bridgePartition W s u n * W u t := by
  have hsum : (∑ γ : Fin (n + 1) → Q,
      if γ 0 = s then edgePathWeight W γ * W (γ (Fin.last n)) t else 0) =
      ∑ u, bridgePartition W s u n * W u t := by
    simp only [bridgePartition, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro γ _
    by_cases h : γ 0 = s
    · simp [bridgeWeight, h, ite_mul, eq_comm]
    · simp [bridgeWeight, h]
  rw [bridgePartition]
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 2) => Q)).sum_comp]
  have he (z : Q × (Fin (n + 1) → Q)) :
      (Fin.snocEquiv (fun _ : Fin (n + 2) => Q)) z = Fin.snoc z.2 z.1 := rfl
  simp only [he, bridgeWeight, Fin.snoc_apply_zero, Fin.snoc_last, edgePathWeight_snoc]
  rw [Fintype.sum_prod_type, Finset.sum_eq_single t]
  · simpa only [and_true] using hsum
  · intro u _ hu; simp [hu]
  · simp

/-- The normalizing constant of a length-n weighted bridge is exactly the
corresponding entry of the nth matrix power, including length zero. -/
theorem bridgePartition_eq_matrix_power {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (n : ℕ) :
    ∀ s t, bridgePartition (fun x y => W x y) s t n = (W ^ n) s t := by
  induction n with
  | zero => intro s t; simp [bridgePartition_zero, Matrix.one_apply]
  | succ n ih =>
    intro s t
    rw [bridgePartition_succ, pow_succ, Matrix.mul_apply]
    simp_rw [ih]



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_PathSplitting
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def pathLeft {Q : Type} {m n : ℕ} (γ : Fin (m + n + 1) → Q) : Fin (m + 1) → Q :=
  fun i => γ ⟨i.val, by omega⟩

def pathRight {Q : Type} {m n : ℕ} (γ : Fin (m + n + 1) → Q) : Fin (n + 1) → Q :=
  fun i => γ ⟨m + i.val, by omega⟩

/-- Concatenate two paths while retaining their common endpoint only once. -/
def pathJoin {Q : Type} {m n : ℕ} (α : Fin (m + 1) → Q) (β : Fin (n + 1) → Q) :
    Fin (m + n + 1) → Q :=
  fun i => if h : i.val < m then α ⟨i.val, by omega⟩ else β ⟨i.val - m, by omega⟩

theorem pathLeft_join {Q : Type} {m n : ℕ} (α : Fin (m + 1) → Q)
    (β : Fin (n + 1) → Q) (hmatch : α (Fin.last m) = β 0) :
    pathLeft (pathJoin α β) = α := by
  funext i
  unfold pathLeft pathJoin
  split_ifs with hi
  · rfl
  · change ¬ i.val < m at hi
    have he : i = Fin.last m := Fin.ext (show i.val = m by omega)
    subst i
    simpa using hmatch.symm

theorem pathRight_join {Q : Type} {m n : ℕ} (α : Fin (m + 1) → Q)
    (β : Fin (n + 1) → Q) : pathRight (pathJoin α β) = β := by
  funext i
  simp only [pathRight, pathJoin, Nat.not_lt.mpr (Nat.le_add_right m i.val),
    dite_false, Nat.add_sub_cancel_left]

theorem pathJoin_split {Q : Type} {m n : ℕ} (γ : Fin (m + n + 1) → Q) :
    pathJoin (pathLeft γ) (pathRight γ) = γ := by
  funext i
  unfold pathJoin
  split_ifs with hi
  · rfl
  · unfold pathRight
    congr 1
    apply Fin.ext
    dsimp
    omega

theorem edgePathWeight_split {Q : Type} (W : Q → Q → ℝ) {m n : ℕ}
    (γ : Fin (m + n + 1) → Q) :
    edgePathWeight W γ = edgePathWeight W (pathLeft γ) * edgePathWeight W (pathRight γ) := by
  simp only [edgePathWeight, finitePathWeight, one_mul]
  rw [Fin.prod_univ_add]
  congr 1



/-- Actual paths with the indicated endpoints; edge positivity is not imposed. -/
abbrev EndpointPath (Q : Type) (s t : Q) (n : ℕ) :=
  {γ : Fin (n + 1) → Q // γ 0 = s ∧ γ (Fin.last n) = t}



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_BridgeSplitLaw
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators



theorem endpointPath_weight_sum {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (s t : Q) (n : ℕ) :
    (∑ γ : EndpointPath Q s t n, edgePathWeight W γ.val) = bridgePartition W s t n := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun γ : Fin (n + 1) → Q =>
    γ 0 = s ∧ γ (Fin.last n) = t)) (by simp)]
  rw [Finset.sum_filter]
  rfl











theorem normalized_endpoint_bridge {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (s t : Q) (n : ℕ) (γ : EndpointPath Q s t n) :
    normalizeWeights (fun η : EndpointPath Q s t n => edgePathWeight W η.val) γ =
      normalizeWeights (bridgeWeight W s t n) γ.val := by
  unfold normalizeWeights
  rw [endpointPath_weight_sum]
  change edgePathWeight W γ.val / bridgePartition W s t n =
    bridgeWeight W s t n γ.val / bridgePartition W s t n
  rw [bridgeWeight, if_pos γ.property]

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ProductPerturbation
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- Multiplicative errors accumulate at most geometrically, without a
positivity assumption on the individual factors. -/
theorem finite_product_error {I : Type} [Fintype I] (f : I → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hf : ∀ i, |f i - 1| ≤ δ) :
    |(∏ i, f i) - 1| ≤ (1 + δ) ^ Fintype.card I - 1 := by
  classical
  have hfabs (i : I) : |f i| ≤ 1 + δ := by
    have hi := (abs_le.mp (hf i))
    apply abs_le.mpr
    constructor <;> linarith
  have h (s : Finset I) : |(∏ i ∈ s, f i) - 1| ≤ (1 + δ) ^ s.card - 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      have hprod : |∏ j ∈ s, f j| ≤ (1 + δ) ^ s.card := by
        rw [Finset.abs_prod]
        calc
          _ ≤ ∏ _j ∈ s, (1 + δ) :=
            Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => hfabs j)
          _ = _ := by simp
      rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, pow_succ]
      calc
        _ = |(f i - 1) * (∏ j ∈ s, f j) + ((∏ j ∈ s, f j) - 1)| := by congr 1; ring
        _ ≤ |f i - 1| * |∏ j ∈ s, f j| + |(∏ j ∈ s, f j) - 1| := by
          simpa only [abs_mul] using abs_add_le
            ((f i - 1) * (∏ j ∈ s, f j)) ((∏ j ∈ s, f j) - 1)
        _ ≤ δ * (1 + δ) ^ s.card + ((1 + δ) ^ s.card - 1) :=
          add_le_add (mul_le_mul (hf i) hprod (abs_nonneg _) hδ) ih
        _ = _ := by ring
  simpa using h Finset.univ

theorem one_add_pow_sub_one_le {n : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hsmall : (n : ℝ) * δ ≤ 1 / 2) :
    (1 + δ) ^ n - 1 ≤ 2 * n * δ := by
  have hx : (0 : ℝ) ≤ n * δ := mul_nonneg (Nat.cast_nonneg _) hδ
  have hden : 0 < 1 - (n : ℝ) * δ := by linarith
  have hpow : (1 + δ) ^ n ≤ Real.exp ((n : ℝ) * δ) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp δ]) n
  have hexp : Real.exp ((n : ℝ) * δ) ≤ 1 / (1 - (n : ℝ) * δ) :=
    Real.exp_bound_div_one_sub_of_interval hx (by linarith)
  have hrat : 1 / (1 - (n : ℝ) * δ) ≤ 1 + 2 * n * δ := by
    apply (div_le_iff₀ hden).mpr
    nlinarith
  linarith

theorem finite_product_error_linear {I : Type} [Fintype I] (f : I → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hsmall : (Fintype.card I : ℝ) * δ ≤ 1 / 2)
    (hf : ∀ i, |f i - 1| ≤ δ) :
    |(∏ i, f i) - 1| ≤ 2 * Fintype.card I * δ :=
  (finite_product_error f δ hδ hf).trans (one_add_pow_sub_one_le hδ hsmall)

/-- The boundary-weight approximation used in C.3 and E.6. A product of
small multiplicative perturbations of a probability law can be normalized
at a TV cost at most twice the number of factors times the local error. -/
theorem normalized_product_perturbation {Ω I : Type} [Fintype Ω] [Fintype I]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (f : Ω → I → ℝ) (δ : ℝ) (hδ : 0 ≤ δ) (hδlt : δ < 1)
    (hsmall : (Fintype.card I : ℝ) * δ ≤ 1 / 2)
    (hf : ∀ x i, |f x i - 1| ≤ δ) :
    (0 < ∑ x, p x * ∏ i, f x i) ∧
    (∀ x, 0 < normalizeWeights (fun y => p y * ∏ i, f y i) x ↔ 0 < p x) ∧
    tv (normalizeWeights (fun x => p x * ∏ i, f x i)) p ≤
      2 * Fintype.card I * δ := by
  have hfpos (x : Ω) (i : I) : 0 < f x i := by
    have := (abs_le.mp (hf x i)).1
    linarith
  have hprodpos (x : Ω) : 0 < ∏ i, f x i :=
    Finset.prod_pos (fun i _ => hfpos x i)
  have hw (x : Ω) : 0 ≤ p x * ∏ i, f x i := mul_nonneg (hp x) (hprodpos x).le
  have hsome : ∃ x, 0 < p x := by
    have hs : 0 < ∑ x, p x := by rw [hsum]; norm_num
    obtain ⟨x, _, hx⟩ := (Finset.sum_pos_iff_of_nonneg (fun x _ => hp x)).mp hs
    exact ⟨x, hx⟩
  have hZ : 0 < ∑ x, p x * ∏ i, f x i := by
    obtain ⟨x, hx⟩ := hsome
    exact lt_of_lt_of_le (mul_pos hx (hprodpos x))
      (Finset.single_le_sum (fun y _ => hw y) (Finset.mem_univ x))
  refine ⟨hZ, ?_, ?_⟩
  · intro x
    rw [normalizeWeights, div_pos_iff_of_pos_right hZ, mul_pos_iff_of_pos_right (hprodpos x)]
  · apply tv_normalize_le_of_relative_error _ p hw hZ hsum
    intro x
    have hh := mul_le_mul_of_nonneg_left
      (finite_product_error_linear (f x) δ hδ hsmall (hf x)) (hp x)
    calc
      _ = p x * |(∏ i, f x i) - 1| := by
        rw [show p x * (∏ i, f x i) - p x = p x * ((∏ i, f x i) - 1) by ring,
          abs_mul, abs_of_nonneg (hp x)]
      _ ≤ p x * (2 * Fintype.card I * δ) := hh
      _ = _ := mul_comm _ _

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_BridgeBoundaryApproximation
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- Weight of the intermediate boundaries of a bridge. `T i` advances from
one boundary to the next; `tail` goes from the final boundary to the fixed
endpoint. The endpoint may lie in a different cyclic class. -/
def boundaryWeight {Q : Type} {n : ℕ} (s : Q)
    (T : Fin n → Q → Q → ℝ) (tail : Q → ℝ) (y : Fin n → Q) : ℝ :=
  tail ((Fin.cons s y : Fin (n + 1) → Q) (Fin.last n)) *
    ∏ i, T i ((Fin.cons s y : Fin (n + 1) → Q) i.castSucc) (y i)

/-- Perron asymptotics turn the normalized bridge-boundary distribution
into a product law. The last block is allowed to end in another cyclic
class, and its leading constant cancels in normalization. -/
theorem bridge_boundary_product_approximation {Q : Type} [Fintype Q]
    {n : ℕ} (s : Q) (T : Fin n → Q → Q → ℝ) (tail : Q → ℝ)
    (π : Q → ℝ) (hπ : ∀ x, 0 < π x) (hπsum : ∑ x, π x = 1)
    (c : ℝ) (hc : 0 < c) (δ : ℝ) (hδ : 0 ≤ δ) (hδlt : δ < 1)
    (hsmall : ((n + 1 : ℕ) : ℝ) * δ ≤ 1 / 2)
    (hT : ∀ i x y, |T i x y / π y - 1| ≤ δ)
    (htail : ∀ x, |tail x / c - 1| ≤ δ) :
    (0 < ∑ y, boundaryWeight s T tail y) ∧
    (∀ y, 0 < normalizeWeights (boundaryWeight s T tail) y) ∧
    tv (normalizeWeights (boundaryWeight s T tail)) (fun y => ∏ i, π (y i)) ≤
      2 * (n + 1 : ℕ) * δ := by
  classical
  let p (y : Fin n → Q) : ℝ := ∏ i, π (y i)
  let f (y : Fin n → Q) : Option (Fin n) → ℝ
    | none => tail ((Fin.cons s y : Fin (n + 1) → Q) (Fin.last n)) / c
    | some i => T i ((Fin.cons s y : Fin (n + 1) → Q) i.castSucc) (y i) / π (y i)
  have hp (y : Fin n → Q) : 0 < p y := Finset.prod_pos (fun i _ => hπ (y i))
  have hpsum : ∑ y, p y = 1 := by
    change (∑ y : Fin n → Q, ∏ i, π (y i)) = 1
    rw [← Fintype.prod_sum (fun (_i : Fin n) (x : Q) => π x)]
    simp only [hπsum, Finset.prod_const_one]
  have hf (y : Fin n → Q) (i : Option (Fin n)) : |f y i - 1| ≤ δ := by
    cases i with
    | none => exact htail _
    | some i => exact hT i _ _
  have hfactor : boundaryWeight s T tail = fun y => c * (p y * ∏ i, f y i) := by
    funext y
    have hpoint (i : Fin n) : T i ((Fin.cons s y : Fin (n + 1) → Q) i.castSucc) (y i) =
        π (y i) * f y (some i) := by
      dsimp only [f]
      field_simp [(hπ (y i)).ne']
    unfold boundaryWeight
    simp_rw [hpoint]
    rw [Finset.prod_mul_distrib, Fintype.prod_option]
    dsimp only [p, f]
    field_simp [hc.ne']
    <;> ring
  obtain ⟨hZ, hsupp, htv⟩ := normalized_product_perturbation p
    (fun y => (hp y).le) hpsum f δ hδ hδlt
    (by simpa only [Fintype.card_option, Fintype.card_fin] using hsmall) hf
  have hnorm : normalizeWeights (boundaryWeight s T tail) =
      normalizeWeights (fun y => p y * ∏ i, f y i) := by
    rw [hfactor]
    exact normalizeWeights_scale _ c hc.ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [hfactor, ← Finset.mul_sum]
    exact mul_pos hc hZ
  · intro y
    rw [hnorm]
    exact (hsupp y).mpr (hp y)
  · rw [hnorm]
    simpa only [Fintype.card_option, Fintype.card_fin] using htv

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

theorem bridgeBoundarySpec_start {Q : Type} {k : ℕ} (l : Fin (k + 1) → ℕ)
    (s t : Q) (y : Fin k → Q) (γ : Fin (bridgeBlockLength l + 1) → Q)
    (hγ : bridgeBoundarySpec l s t y γ) : γ 0 = s := by
  cases k <;> exact hγ.1

theorem bridgeBoundarySpec_finish {Q : Type} {k : ℕ} (l : Fin (k + 1) → ℕ)
    (s t : Q) (y : Fin k → Q) (γ : Fin (bridgeBlockLength l + 1) → Q)
    (hγ : bridgeBoundarySpec l s t y γ) : γ (Fin.last (bridgeBlockLength l)) = t := by
  induction k generalizing s t with
  | zero => exact hγ.2
  | succ k ih => exact ih (Fin.tail l) (y 0) t (Fin.tail y) (pathRight γ) hγ.2.2

def boundaryPathSplitEquiv {Q : Type} {k : ℕ} (l : Fin (k + 2) → ℕ)
    (s t : Q) (y : Fin (k + 1) → Q) :
    BoundaryPath Q l s t y ≃
      (EndpointPath Q s (y 0) (l 0) × BoundaryPath Q (Fin.tail l) (y 0) t (Fin.tail y)) where
  toFun γ := (⟨pathLeft γ.val, ⟨γ.property.1, γ.property.2.1⟩⟩,
    ⟨pathRight γ.val, γ.property.2.2⟩)
  invFun z := ⟨pathJoin z.1.val z.2.val, by
    have hs := bridgeBoundarySpec_start (Fin.tail l) (y 0) t (Fin.tail y) z.2.val z.2.property
    have hm : z.1.val (Fin.last (l 0)) = z.2.val 0 := z.1.property.2.trans hs.symm
    have hl := pathLeft_join z.1.val z.2.val hm
    refine ⟨(congrFun hl 0).trans z.1.property.1,
      (congrFun hl (Fin.last (l 0))).trans z.1.property.2, ?_⟩
    change bridgeBoundarySpec (Fin.tail l) (y 0) t (Fin.tail y)
      (pathRight (pathJoin z.1.val z.2.val))
    rw [pathRight_join]
    exact z.2.property⟩
  left_inv γ := Subtype.ext (pathJoin_split γ.val)
  right_inv z := by
    have hs := bridgeBoundarySpec_start (Fin.tail l) (y 0) t (Fin.tail y) z.2.val z.2.property
    apply Prod.ext
    · exact Subtype.ext (pathLeft_join z.1.val z.2.val (z.1.property.2.trans hs.symm))
    · exact Subtype.ext (pathRight_join z.1.val z.2.val)

theorem boundaryWeight_head {Q : Type} {k : ℕ} (s : Q)
    (T : Fin (k + 1) → Q → Q → ℝ) (tail : Q → ℝ) (y : Fin (k + 1) → Q) :
    boundaryWeight s T tail y = T 0 s (y 0) *
      boundaryWeight (y 0) (Fin.tail T) tail (Fin.tail y) := by
  simp only [boundaryWeight, Fin.prod_univ_succ, Fin.cons_self_tail]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.castSucc_succ, Fin.cons_succ,
    Fin.cons_last, Fin.tail]
  ring

/-- The exact transfer-matrix weight for the prescribed block boundaries. -/
def bridgeBoundaryMass {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (s t : Q) (y : Fin k → Q) : ℝ :=
  boundaryWeight s (fun i x z => bridgePartition W x z (l i.castSucc))
    (fun x => bridgePartition W x t (l (Fin.last k))) y

theorem bridgeBoundaryMass_zero {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (l : Fin 1 → ℕ) (s t : Q) (y : Fin 0 → Q) :
    bridgeBoundaryMass W l s t y = bridgePartition W s t (l 0) := by
  simp [bridgeBoundaryMass, boundaryWeight]

theorem bridgeBoundaryMass_head {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (l : Fin (k + 2) → ℕ) (s t : Q) (y : Fin (k + 1) → Q) :
    bridgeBoundaryMass W l s t y = bridgePartition W s (y 0) (l 0) *
      bridgeBoundaryMass W (Fin.tail l) (y 0) t (Fin.tail y) := by
  unfold bridgeBoundaryMass
  rw [boundaryWeight_head]
  rfl

/-- Summing the weights of actual full paths with all prescribed boundaries
gives exactly the product of block transfer weights used in C.3 and E.6. -/
theorem boundaryPath_weight_sum {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (s t : Q) (y : Fin k → Q) :
    (∑ γ : BoundaryPath Q l s t y, edgePathWeight W γ.val) =
      bridgeBoundaryMass W l s t y := by
  classical
  induction k generalizing s t with
  | zero =>
    rw [bridgeBoundaryMass_zero]
    convert endpointPath_weight_sum W s t (l 0) using 1
    congr 1
    exact congrArg (fun h : Fintype (EndpointPath Q s t (l 0)) => h.elems)
      (Subsingleton.elim _ _)
  | succ k ih =>
    let e := boundaryPathSplitEquiv l s t y
    have he (γ : BoundaryPath Q l s t y) : edgePathWeight W γ.val =
        edgePathWeight W (e γ).1.val * edgePathWeight W (e γ).2.val :=
      edgePathWeight_split W γ.val
    simp_rw [he]
    rw [e.sum_comp (fun z : EndpointPath Q s (y 0) (l 0) ×
        BoundaryPath Q (Fin.tail l) (y 0) t (Fin.tail y) =>
      edgePathWeight W z.1.val * edgePathWeight W z.2.val)]
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul, endpointPath_weight_sum]
    rw [ih, bridgeBoundaryMass_head]

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_BridgeBoundaryMarginal
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

theorem bridgeBlockLength_eq_sum {k : ℕ} (l : Fin (k + 1) → ℕ) :
    bridgeBlockLength l = ∑ i, l i := by
  induction k with
  | zero => simp [bridgeBlockLength]
  | succ k ih => simp only [bridgeBlockLength, Fin.sum_univ_succ, ih, Fin.tail]

/-- Read the intermediate states from the full trajectory, at the actual
cumulative block lengths. -/
def bridgeBoundaryStates {Q : Type} : {k : ℕ} → (l : Fin (k + 1) → ℕ) →
    (Fin (bridgeBlockLength l + 1) → Q) → (Fin k → Q)
  | 0, _, _ => Fin.elim0
  | k + 1, l, γ => Fin.cons (γ ⟨l 0, by simp only [bridgeBlockLength]; omega⟩)
      (bridgeBoundaryStates (Fin.tail l) (pathRight γ))

theorem bridgeBoundarySpec_observation {Q : Type} {k : ℕ} (l : Fin (k + 1) → ℕ)
    (s t : Q) (y : Fin k → Q) (γ : Fin (bridgeBlockLength l + 1) → Q)
    (hγ : bridgeBoundarySpec l s t y γ) : bridgeBoundaryStates l γ = y := by
  induction k generalizing s t with
  | zero => exact Subsingleton.elim _ _
  | succ k ih =>
    change Fin.cons _ (bridgeBoundaryStates (Fin.tail l) (pathRight γ)) = y
    rw [hγ.2.1, ih (Fin.tail l) (y 0) t (Fin.tail y) (pathRight γ) hγ.2.2]
    exact Fin.cons_self_tail y

theorem bridgeBoundarySpec_of_observation {Q : Type} {k : ℕ} (l : Fin (k + 1) → ℕ)
    (s t : Q) (γ : Fin (bridgeBlockLength l + 1) → Q)
    (hs : γ 0 = s) (ht : γ (Fin.last (bridgeBlockLength l)) = t) :
    bridgeBoundarySpec l s t (bridgeBoundaryStates l γ) γ := by
  induction k generalizing s t with
  | zero => exact ⟨hs, ht⟩
  | succ k ih =>
    refine ⟨hs, rfl, ?_⟩
    change bridgeBoundarySpec (Fin.tail l) _ t
      (bridgeBoundaryStates (Fin.tail l) (pathRight γ)) (pathRight γ)
    apply ih
    · simp only [pathRight, Fin.val_zero, Nat.add_zero, bridgeBoundaryStates, Fin.cons_zero]
      rfl
    · exact ht

theorem bridgeBoundarySpec_iff {Q : Type} {k : ℕ} (l : Fin (k + 1) → ℕ)
    (s t : Q) (y : Fin k → Q) (γ : Fin (bridgeBlockLength l + 1) → Q) :
    bridgeBoundarySpec l s t y γ ↔
      γ 0 = s ∧ γ (Fin.last (bridgeBlockLength l)) = t ∧ bridgeBoundaryStates l γ = y := by
  constructor
  · intro h
    exact ⟨bridgeBoundarySpec_start l s t y γ h, bridgeBoundarySpec_finish l s t y γ h,
      bridgeBoundarySpec_observation l s t y γ h⟩
  · rintro ⟨hs, ht, hy⟩
    rw [← hy]
    exact bridgeBoundarySpec_of_observation l s t γ hs ht

/-- The exact unnormalized boundary marginal, computed by summing over all
full paths, is the transfer-matrix product. -/
theorem bridge_boundary_weight {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (s t : Q) (y : Fin k → Q) :
    (∑ γ : Fin (bridgeBlockLength l + 1) → Q, if bridgeBoundaryStates l γ = y then
      bridgeWeight W s t (bridgeBlockLength l) γ else 0) = bridgeBoundaryMass W l s t y := by
  classical
  rw [← boundaryPath_weight_sum]
  rw [← Finset.sum_subtype (Finset.univ.filter (bridgeBoundarySpec l s t y)) (by simp)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro γ _
  rw [bridgeBoundarySpec_iff]
  simp only [bridgeWeight]
  split_ifs <;> tauto

theorem bridgeBoundaryMass_sum {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (s t : Q) :
    (∑ y, bridgeBoundaryMass W l s t y) = bridgePartition W s t (bridgeBlockLength l) := by
  classical
  simp_rw [← bridge_boundary_weight]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

/-- The actual pushforward of the normalized full-bridge law is exactly
the normalization of boundaryWeight used by the quantitative approximation. -/
theorem normalized_bridge_boundaries {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (s t : Q) (y : Fin k → Q) :
    (∑ γ : Fin (bridgeBlockLength l + 1) → Q, if bridgeBoundaryStates l γ = y then
      normalizeWeights (bridgeWeight W s t (bridgeBlockLength l)) γ else 0) =
      normalizeWeights (bridgeBoundaryMass W l s t) y := by
  classical
  unfold normalizeWeights
  rw [bridgeBoundaryMass_sum]
  change (∑ γ : Fin (bridgeBlockLength l + 1) → Q, if bridgeBoundaryStates l γ = y then
    bridgeWeight W s t (bridgeBlockLength l) γ / bridgePartition W s t (bridgeBlockLength l)
    else 0) = _
  have hpoint (γ : Fin (bridgeBlockLength l + 1) → Q) :
      (if bridgeBoundaryStates l γ = y then bridgeWeight W s t (bridgeBlockLength l) γ /
        bridgePartition W s t (bridgeBlockLength l) else 0) =
      (if bridgeBoundaryStates l γ = y then bridgeWeight W s t (bridgeBlockLength l) γ else 0) /
        bridgePartition W s t (bridgeBlockLength l) := by
    split_ifs <;> simp
  simp_rw [hpoint]
  rw [← Finset.sum_div, bridge_boundary_weight]

theorem bridgeBoundaryMass_matrix {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Matrix Q Q ℝ) (l : Fin (k + 1) → ℕ) (s t : Q) (y : Fin k → Q) :
    bridgeBoundaryMass (fun x z => W x z) l s t y =
      boundaryWeight s (fun i x z => (W ^ l i.castSucc) x z)
        (fun x => (W ^ l (Fin.last k)) x t) y := by
  unfold bridgeBoundaryMass
  simp_rw [bridgePartition_eq_matrix_power]

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_CutoffBlockPartition
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def cutoffBoundaryCount (n L : ℕ) : ℕ := n / L - 1

/-- Split a segment into cutoff-sized blocks and merge its short remainder
into the last block. Segments shorter than the cutoff have one block. -/
def cutoffBlockLengths (n L : ℕ) : Fin (cutoffBoundaryCount n L + 1) → ℕ :=
  Fin.snoc (fun _ => L) (n - cutoffBoundaryCount n L * L)

theorem cutoffBlockLengths_internal (n L : ℕ) (i : Fin (cutoffBoundaryCount n L)) :
    cutoffBlockLengths n L i.castSucc = L := by simp [cutoffBlockLengths]

theorem cutoffBlockLengths_last (n L : ℕ) :
    cutoffBlockLengths n L (Fin.last (cutoffBoundaryCount n L)) =
      n - cutoffBoundaryCount n L * L := by simp [cutoffBlockLengths]

theorem cutoff_boundary_length_le (n L : ℕ) : cutoffBoundaryCount n L * L ≤ n := by
  exact (Nat.mul_le_mul_right L (Nat.sub_le (n / L) 1)).trans (Nat.div_mul_le_self n L)

theorem cutoffBlockLengths_total (n L : ℕ) :
    bridgeBlockLength (cutoffBlockLengths n L) = n := by
  rw [bridgeBlockLength_eq_sum, Fin.sum_univ_castSucc]
  simp only [cutoffBlockLengths_internal, cutoffBlockLengths_last, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact Nat.add_sub_of_le (cutoff_boundary_length_le n L)

theorem cutoffBlockLengths_short (n L : ℕ) (hn : n < L) :
    cutoffBoundaryCount n L = 0 ∧ ∀ i, cutoffBlockLengths n L i = n := by
  have hk : cutoffBoundaryCount n L = 0 := by simp [cutoffBoundaryCount, Nat.div_eq_of_lt hn]
  refine ⟨hk, ?_⟩
  intro i
  have hi : i = Fin.last (cutoffBoundaryCount n L) := by apply Fin.ext; simp at *; omega
  rw [hi, cutoffBlockLengths_last, hk]
  simp

theorem cutoffBlockLengths_long_tail (n L : ℕ) (hL : 0 < L) (hn : L ≤ n) :
    cutoffBlockLengths n L (Fin.last (cutoffBoundaryCount n L)) = L + n % L := by
  have hq : 1 ≤ n / L := (Nat.le_div_iff_mul_le hL).mpr (by simpa using hn)
  have hqsplit : n / L - 1 + 1 = n / L := Nat.sub_add_cancel hq
  have hdecomp := Nat.div_add_mod n L
  rw [cutoffBlockLengths_last]
  change n - (n / L - 1) * L = _
  have he : (n / L - 1) * L + L + n % L = n := by
    calc
      _ = (n / L - 1 + 1) * L + n % L := by ring
      _ = n := by rw [hqsplit]; simpa only [mul_comm] using hdecomp
  omega

theorem cutoffBlockLengths_lower (n L : ℕ) (hL : 0 < L) (hn : L ≤ n) :
    ∀ i, L ≤ cutoffBlockLengths n L i := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [cutoffBlockLengths_long_tail n L hL hn]
    omega
  · rw [cutoffBlockLengths_internal]

theorem cutoffBlockLengths_upper (n L : ℕ) (hL : 0 < L) :
    ∀ i, cutoffBlockLengths n L i < 2 * L := by
  intro i
  by_cases hn : L ≤ n
  · refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [cutoffBlockLengths_long_tail n L hL hn]
      have := Nat.mod_lt n hL
      omega
    · rw [cutoffBlockLengths_internal]
      omega
  · rw [(cutoffBlockLengths_short n L (by omega)).2 i]
    omega

/-- The draw count has the required n/L+O(1) bound, including n=0 and L>n. -/
theorem cutoff_block_count_bound (n L : ℕ) :
    cutoffBoundaryCount n L + 1 ≤ n / L + 1 ∧ cutoffBoundaryCount n L ≤ n := by
  dsimp only [cutoffBoundaryCount]
  exact ⟨Nat.succ_le_succ (Nat.sub_le _ _), (Nat.sub_le _ _).trans (Nat.div_le_self _ _)⟩

/-- For any fixed block exponent dividing the common cutoff, every long
segment partition has the exact internal-multiple and residual-tail form
required by periodic_actual_bridge_boundaries. -/
theorem cutoffBlockLengths_periodic {a n L : ℕ} (ha : 0 < a) (hL : 0 < L)
    (had : a ∣ L) (hn : L ≤ n) :
    let l := cutoffBlockLengths n L
    let m := fun i => l i / a
    let r := l (Fin.last (cutoffBoundaryCount n L)) % a
    (∀ i : Fin (cutoffBoundaryCount n L), l i.castSucc = a * m i.castSucc) ∧
    l (Fin.last (cutoffBoundaryCount n L)) = a * m (Fin.last (cutoffBoundaryCount n L)) + r ∧
    r < a ∧ (∀ i, L / a ≤ m i) := by
  dsimp only
  refine ⟨?_, ?_, Nat.mod_lt _ ha, ?_⟩
  · intro i
    rw [cutoffBlockLengths_internal]
    exact (Nat.mul_div_cancel' had).symm
  · exact (Nat.div_add_mod _ a).symm
  · intro i
    exact Nat.div_le_div_right (cutoffBlockLengths_lower n L hL hn i)

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_IndependentBridgeBlocks
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- Extract each entire block from the original trajectory, retaining both
endpoints. Its output length is exactly the requested block length. -/
def boundaryBlockPath {Q : Type} : {k : ℕ} → (l : Fin (k + 1) → ℕ) →
    (Fin (bridgeBlockLength l + 1) → Q) → (i : Fin (k + 1)) → (Fin (l i + 1) → Q)
  | 0, l, γ => Fin.cases γ (fun i => Fin.elim0 i)
  | k + 1, l, γ => Fin.cases (pathLeft γ)
      (fun i => boundaryBlockPath (Fin.tail l) (pathRight γ) i)

theorem edgePathWeight_blocks {Q : Type} (W : Q → Q → ℝ) {k : ℕ}
    (l : Fin (k + 1) → ℕ) (γ : Fin (bridgeBlockLength l + 1) → Q) :
    edgePathWeight W γ = ∏ i, edgePathWeight W (boundaryBlockPath l γ i) := by
  induction k with
  | zero =>
    simp [boundaryBlockPath]
    rfl
  | succ k ih =>
    rw [Fin.prod_univ_succ]
    change edgePathWeight W γ = edgePathWeight W (pathLeft γ) *
      ∏ i, edgePathWeight W (boundaryBlockPath (Fin.tail l) (pathRight γ) i)
    exact (edgePathWeight_split W γ).trans
      (congrArg (fun z => edgePathWeight W (pathLeft γ) * z) (ih (Fin.tail l) (pathRight γ)))

theorem fin_snoc_succ {Q : Type} {k : ℕ} (y : Fin (k + 1) → Q) (t : Q) (i : Fin (k + 1)) :
    (Fin.snoc y t : Fin (k + 2) → Q) i.succ = (Fin.snoc (Fin.tail y) t : Fin (k + 1) → Q) i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.succ_last, Fin.snoc_last]
  · rw [← Fin.castSucc_succ, Fin.snoc_castSucc, Fin.snoc_castSucc]
    rfl

theorem boundaryBlockPath_endpoints {Q : Type} {k : ℕ} (l : Fin (k + 1) → ℕ)
    (s t : Q) (y : Fin k → Q) (γ : Fin (bridgeBlockLength l + 1) → Q)
    (hγ : bridgeBoundarySpec l s t y γ) (i : Fin (k + 1)) :
    boundaryBlockPath l γ i 0 = (Fin.cons s y : Fin (k + 1) → Q) i ∧
      boundaryBlockPath l γ i (Fin.last (l i)) = (Fin.snoc y t : Fin (k + 1) → Q) i := by
  induction k generalizing s t with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    change γ 0 = s ∧ γ (Fin.last (l 0)) = (Fin.snoc y t : Fin 1 → Q) 0
    have he : (Fin.snoc y t : Fin 1 → Q) 0 = t := by
      change (Fin.snoc y t : Fin 1 → Q) (Fin.last 0) = t
      exact Fin.snoc_last (n := 0) (α := fun _ : Fin 1 => Q) t y
    rw [he]
    exact hγ
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · change (pathLeft γ) 0 = s ∧
        (pathLeft γ) (Fin.last (l 0)) = (Fin.snoc y t : Fin (k + 2) → Q) 0
      rw [Fin.snoc_apply_zero]
      exact ⟨hγ.1, hγ.2.1⟩
    · change boundaryBlockPath (Fin.tail l) (pathRight γ) j 0 = y j ∧
        boundaryBlockPath (Fin.tail l) (pathRight γ) j (Fin.last ((Fin.tail l) j)) =
          (Fin.snoc y t : Fin (k + 2) → Q) j.succ
      rw [fin_snoc_succ]
      have hj := ih (Fin.tail l) (y 0) t (Fin.tail y) (pathRight γ) hγ.2.2 j
      rw [Fin.cons_self_tail] at hj
      exact hj

theorem bridgeBoundaryMass_product {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (s t : Q) (y : Fin k → Q) :
    bridgeBoundaryMass W l s t y = ∏ i,
      bridgePartition W ((Fin.cons s y : Fin (k + 1) → Q) i)
        ((Fin.snoc y t : Fin (k + 1) → Q) i) (l i) := by
  unfold bridgeBoundaryMass boundaryWeight
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  ring

/-- Given all boundary states, the normalized whole-path weight is the
product of the individual normalized bridge weights of every actual block.
This includes zero-length blocks and arbitrary finite numbers of blocks. -/
theorem boundaryPath_normalized_product {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (s t : Q) (y : Fin k → Q)
    (γ : BoundaryPath Q l s t y) :
    normalizeWeights (fun η : BoundaryPath Q l s t y => edgePathWeight W η.val) γ =
      ∏ i, normalizeWeights
        (bridgeWeight W ((Fin.cons s y : Fin (k + 1) → Q) i)
          ((Fin.snoc y t : Fin (k + 1) → Q) i) (l i)) (boundaryBlockPath l γ.val i) := by
  have hpoint (i : Fin (k + 1)) :
      normalizeWeights
        (bridgeWeight W ((Fin.cons s y : Fin (k + 1) → Q) i)
          ((Fin.snoc y t : Fin (k + 1) → Q) i) (l i)) (boundaryBlockPath l γ.val i) =
      edgePathWeight W (boundaryBlockPath l γ.val i) /
        bridgePartition W ((Fin.cons s y : Fin (k + 1) → Q) i)
          ((Fin.snoc y t : Fin (k + 1) → Q) i) (l i) := by
    unfold normalizeWeights
    change bridgeWeight W _ _ _ _ / bridgePartition W _ _ _ = _
    rw [bridgeWeight, if_pos (boundaryBlockPath_endpoints l s t y γ.val γ.property i)]
  simp_rw [hpoint]
  unfold normalizeWeights
  rw [boundaryPath_weight_sum, bridgeBoundaryMass_product, Finset.prod_div_distrib]
  congr 1
  exact edgePathWeight_blocks W l γ.val

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_BridgeBlockEquivalence
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

theorem boundaryBlockPath_injective {Q : Type} {k : ℕ} (l : Fin (k + 1) → ℕ)
    (γ η : Fin (bridgeBlockLength l + 1) → Q)
    (he : ∀ i, boundaryBlockPath l γ i = boundaryBlockPath l η i) : γ = η := by
  induction k with
  | zero => exact he 0
  | succ k ih =>
    have hl : pathLeft γ = pathLeft η := he 0
    have hr : pathRight γ = pathRight η :=
      ih (Fin.tail l) (pathRight γ) (pathRight η) (fun i => he i.succ)
    exact (pathJoin_split γ).symm.trans
      ((congrArg₂ pathJoin hl hr).trans (pathJoin_split η))

abbrev BoundaryBlocks (Q : Type) {k : ℕ} (l : Fin (k + 1) → ℕ)
    (s t : Q) (y : Fin k → Q) :=
  (i : Fin (k + 1)) → EndpointPath Q ((Fin.cons s y : Fin (k + 1) → Q) i)
    ((Fin.snoc y t : Fin (k + 1) → Q) i) (l i)

def boundaryBlocks {Q : Type} {k : ℕ} (l : Fin (k + 1) → ℕ)
    (s t : Q) (y : Fin k → Q) (γ : BoundaryPath Q l s t y) : BoundaryBlocks Q l s t y :=
  fun i => ⟨boundaryBlockPath l γ.val i, boundaryBlockPath_endpoints l s t y γ.val γ.property i⟩

theorem boundaryBlocks_injective {Q : Type} {k : ℕ} (l : Fin (k + 1) → ℕ)
    (s t : Q) (y : Fin k → Q) : Function.Injective (boundaryBlocks l s t y) := by
  intro γ η he
  apply Subtype.ext
  apply boundaryBlockPath_injective l
  intro i
  exact congrArg (fun b : BoundaryBlocks Q l s t y => (b i).val) he

/-- Every independent choice of endpoint-compatible block paths concatenates
to a full path with precisely the specified boundary states. -/
theorem boundaryBlocks_surjective {Q : Type} {k : ℕ} (l : Fin (k + 1) → ℕ)
    (s t : Q) (y : Fin k → Q) : Function.Surjective (boundaryBlocks l s t y) := by
  intro b
  induction k generalizing s t with
  | zero =>
    have hend : (b 0).val (Fin.last (l 0)) = t := by
      have h := (b 0).property.2
      have hs : (Fin.snoc y t : Fin 1 → Q) 0 = t := by
        change (Fin.snoc y t : Fin 1 → Q) (Fin.last 0) = t
        exact Fin.snoc_last (n := 0) (α := fun _ : Fin 1 => Q) t y
      exact h.trans hs
    let γ : BoundaryPath Q l s t y := ⟨(b 0).val, ⟨(b 0).property.1, hend⟩⟩
    refine ⟨γ, ?_⟩
    funext i
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    rfl
  | succ k ih =>
    let a : EndpointPath Q s (y 0) (l 0) := ⟨(b 0).val, by
      constructor
      · exact (b 0).property.1
      · have h := (b 0).property.2
        simpa only [Fin.snoc_apply_zero] using h⟩
    let bt : BoundaryBlocks Q (Fin.tail l) (y 0) t (Fin.tail y) := fun j =>
      ⟨(b j.succ).val, by
        have h := (b j.succ).property
        change (b j.succ).val 0 = (Fin.cons (y 0) (Fin.tail y) : Fin (k + 1) → Q) j ∧
          (b j.succ).val (Fin.last ((Fin.tail l) j)) =
            (Fin.snoc (Fin.tail y) t : Fin (k + 1) → Q) j
        rw [Fin.cons_self_tail]
        change (b j.succ).val 0 = y j ∧
          (b j.succ).val (Fin.last (l j.succ)) =
            (Fin.snoc (Fin.tail y) t : Fin (k + 1) → Q) j
        simpa only [Fin.cons_succ, fin_snoc_succ] using h⟩
    obtain ⟨η, hη⟩ := ih (Fin.tail l) (y 0) t (Fin.tail y) bt
    let e := boundaryPathSplitEquiv l s t y
    let γ := e.symm (a, η)
    have hl : pathLeft γ.val = a.val := congrArg (fun z => z.1.val) (e.apply_symm_apply (a, η))
    have hr : pathRight γ.val = η.val := congrArg (fun z => z.2.val) (e.apply_symm_apply (a, η))
    refine ⟨γ, ?_⟩
    funext i
    apply Subtype.ext
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hl
    · change boundaryBlockPath (Fin.tail l) (pathRight γ.val) j = (b j.succ).val
      rw [hr]
      exact congrArg (fun z : BoundaryBlocks Q (Fin.tail l) (y 0) t (Fin.tail y) => (z j).val) hη

/-- A genuine equivalence with the full Cartesian product of block path
spaces, not merely an injection into compatible tuples. -/
def boundaryBlocksEquiv {Q : Type} {k : ℕ} (l : Fin (k + 1) → ℕ)
    (s t : Q) (y : Fin k → Q) : BoundaryPath Q l s t y ≃ BoundaryBlocks Q l s t y :=
  Equiv.ofBijective (boundaryBlocks l s t y)
    ⟨boundaryBlocks_injective l s t y, boundaryBlocks_surjective l s t y⟩

/-- Under the explicit concatenation equivalence, all conditional block
paths are independent with their respective normalized bridge laws. -/
theorem boundaryBlocks_independent_law {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (s t : Q) (y : Fin k → Q)
    (b : BoundaryBlocks Q l s t y) :
    normalizeWeights (fun γ : BoundaryPath Q l s t y => edgePathWeight W γ.val)
      ((boundaryBlocksEquiv l s t y).symm b) =
      ∏ i, normalizeWeights (fun α : EndpointPath Q
        ((Fin.cons s y : Fin (k + 1) → Q) i) ((Fin.snoc y t : Fin (k + 1) → Q) i) (l i) =>
          edgePathWeight W α.val) (b i) := by
  rw [boundaryPath_normalized_product]
  apply Finset.prod_congr rfl
  intro i _
  rw [normalized_endpoint_bridge]
  have he := congrArg (fun z : BoundaryBlocks Q l s t y => (z i).val)
    ((boundaryBlocksEquiv l s t y).apply_symm_apply b)
  change boundaryBlockPath l ((boundaryBlocksEquiv l s t y).symm b).val i = (b i).val at he
  rw [he]

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

theorem mem_graphComponent {Q : Type} [Fintype Q] (R : Q → Q → Prop) (x y : Q) :
    y ∈ graphComponent R x ↔ Relation.ReflTransGen R x y := by
  classical
  simp [graphComponent]

theorem graphComponent_self {Q : Type} [Fintype Q] (R : Q → Q → Prop) (x : Q) :
    x ∈ graphComponent R x := (mem_graphComponent R x x).mpr .refl

theorem graphComponent_subset {Q : Type} [Fintype Q] (R : Q → Q → Prop) {x y : Q}
    (hxy : Relation.ReflTransGen R x y) : graphComponent R y ⊆ graphComponent R x := by
  intro z hz
  exact (mem_graphComponent R x z).mpr (hxy.trans ((mem_graphComponent R y z).mp hz))

theorem graphComponent_eq_iff {Q : Type} [Fintype Q] (R : Q → Q → Prop) (x y : Q) :
    graphComponent R x = graphComponent R y ↔
      Relation.ReflTransGen R x y ∧ Relation.ReflTransGen R y x := by
  constructor
  · intro h
    constructor
    · apply (mem_graphComponent R x y).mp
      rw [h]; exact graphComponent_self R y
    · apply (mem_graphComponent R y x).mp
      rw [← h]; exact graphComponent_self R x
  · rintro ⟨hxy, hyx⟩
    exact Finset.Subset.antisymm (graphComponent_subset R hyx) (graphComponent_subset R hxy)

theorem graphComponent_card_pos {Q : Type} [Fintype Q] (R : Q → Q → Prop) (x : Q) :
    0 < (graphComponent R x).card := Finset.card_pos.mpr ⟨x, graphComponent_self R x⟩

theorem graphComponent_card_le {Q : Type} [Fintype Q] (R : Q → Q → Prop) (x : Q) :
    (graphComponent R x).card ≤ Fintype.card Q := Finset.card_le_univ _

def RespectsGraph {Q : Type} (R : Q → Q → Prop) {n : ℕ} (γ : Fin (n + 1) → Q) : Prop :=
  ∀ i : Fin n, R (γ i.castSucc) (γ i.succ)

theorem graph_path_reaches {Q : Type} (R : Q → Q → Prop) {n : ℕ}
    (γ : Fin (n + 1) → Q) (hγ : RespectsGraph R γ) (i j : Fin (n + 1)) (hij : i ≤ j) :
    Relation.ReflTransGen R (γ i) (γ j) := by
  have haux : ∀ k : ℕ, ∀ hk : k < n + 1, ∀ i : Fin (n + 1), i.val ≤ k →
      Relation.ReflTransGen R (γ i) (γ ⟨k, hk⟩) := by
    intro k
    induction k with
    | zero =>
      intro hk i hi
      have he : i = ⟨0, hk⟩ := Fin.ext (show i.val = 0 by omega)
      rw [he]
    | succ k ih =>
      intro hk i hi
      by_cases he : i.val = k + 1
      · have he' : i = ⟨k + 1, hk⟩ := Fin.ext he
        rw [he']
      · have hprev := ih (by omega) i (by omega)
        exact hprev.trans (.single (hγ ⟨k, by omega⟩))
  exact haux j.val j.isLt i hij

theorem graph_path_component_antitone {Q : Type} [Fintype Q]
    (R : Q → Q → Prop) {n : ℕ} (γ : Fin (n + 1) → Q) (hγ : RespectsGraph R γ)
    {i j : Fin (n + 1)} (hij : i ≤ j) :
    graphComponent R (γ j) ⊆ graphComponent R (γ i) :=
  graphComponent_subset R (graph_path_reaches R γ hγ i j hij)

/-- A trajectory cannot leave an SCC and later return to it. -/
theorem graph_path_no_return {Q : Type} [Fintype Q]
    (R : Q → Q → Prop) {n : ℕ} (γ : Fin (n + 1) → Q) (hγ : RespectsGraph R γ)
    (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k)
    (hik : graphComponent R (γ i) = graphComponent R (γ k)) :
    graphComponent R (γ j) = graphComponent R (γ i) := by
  apply Finset.Subset.antisymm (graph_path_component_antitone R γ hγ hij)
  rw [hik]
  exact graph_path_component_antitone R γ hγ hjk

def graphCrossings {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ : Fin (n + 1) → Q) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => graphComponent R (γ i.castSucc) ≠ graphComponent R (γ i.succ))

theorem mem_graphCrossings {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ : Fin (n + 1) → Q) (i : Fin n) :
    i ∈ graphCrossings R γ ↔ graphComponent R (γ i.castSucc) ≠ graphComponent R (γ i.succ) := by
  classical
  simp [graphCrossings]

theorem graph_crossing_rank_drop {Q : Type} [Fintype Q]
    (R : Q → Q → Prop) {n : ℕ} (γ : Fin (n + 1) → Q) (hγ : RespectsGraph R γ)
    (i : Fin n) (hi : i ∈ graphCrossings R γ) :
    (graphComponent R (γ i.succ)).card < (graphComponent R (γ i.castSucc)).card := by
  have hsub := graphComponent_subset R (.single (hγ i))
  have hne := (mem_graphCrossings R γ i).mp hi
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne.symm⟩)

theorem graph_crossing_ranks_ordered {Q : Type} [Fintype Q]
    (R : Q → Q → Prop) {n : ℕ} (γ : Fin (n + 1) → Q) (hγ : RespectsGraph R γ)
    (i j : Fin n) (hj : j ∈ graphCrossings R γ) (hij : i < j) :
    (graphComponent R (γ j.succ)).card < (graphComponent R (γ i.succ)).card := by
  have hmid : i.succ ≤ j.castSucc := by change i.val + 1 ≤ j.val; omega
  exact (graph_crossing_rank_drop R γ hγ j hj).trans_le
    (Finset.card_le_card (graph_path_component_antitone R γ hγ hmid))

/-- Every valid trajectory has at most `|Q|-1` cross-SCC edges and hence
at most `|Q|` SCC segments, independently of its length. -/
theorem graph_crossings_card_bound {Q : Type} [Fintype Q]
    (R : Q → Q → Prop) {n : ℕ} (γ : Fin (n + 1) → Q) (hγ : RespectsGraph R γ) :
    (graphCrossings R γ).card + 1 ≤ Fintype.card Q := by
  classical
  let f : {i : Fin n // i ∈ graphCrossings R γ} → Fin (Fintype.card Q - 1) := fun i =>
    ⟨(graphComponent R (γ i.val.succ)).card - 1, by
      have hdrop := graph_crossing_rank_drop R γ hγ i.val i.property
      have hupper := graphComponent_card_le R (γ i.val.castSucc)
      have hpos := graphComponent_card_pos R (γ i.val.succ)
      omega⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    have hval := congrArg Fin.val hij
    change (graphComponent R (γ i.val.succ)).card - 1 =
      (graphComponent R (γ j.val.succ)).card - 1 at hval
    have hipos := graphComponent_card_pos R (γ i.val.succ)
    have hjpos := graphComponent_card_pos R (γ j.val.succ)
    rcases lt_trichotomy i.val j.val with h | h | h
    · have := graph_crossing_ranks_ordered R γ hγ i.val j.val j.property h
      omega
    · exact h
    · have := graph_crossing_ranks_ordered R γ hγ j.val i.val i.property h
      omega
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe, Fintype.card_fin] at hcard
  have hQ := (graphComponent_card_pos R (γ 0)).trans_le (graphComponent_card_le R (γ 0))
  omega

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SCCBridgeRestriction
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

theorem edgePathWeight_nonneg {Q : Type} (W : Q → Q → ℝ)
    (hW : ∀ x y, 0 ≤ W x y) {n : ℕ} (γ : Fin (n + 1) → Q) :
    0 ≤ edgePathWeight W γ := by
  simp only [edgePathWeight, finitePathWeight, one_mul]
  exact Finset.prod_nonneg (fun i _ => hW _ _)

theorem edgePathWeight_pos_iff {Q : Type} (W : Q → Q → ℝ)
    (hW : ∀ x y, 0 ≤ W x y) {n : ℕ} (γ : Fin (n + 1) → Q) :
    0 < edgePathWeight W γ ↔ RespectsGraph (fun x y => 0 < W x y) γ := by
  simp only [edgePathWeight, finitePathWeight, one_mul]
  constructor
  · intro h i
    have hn := Finset.prod_ne_zero_iff.mp h.ne' i (Finset.mem_univ i)
    exact lt_of_le_of_ne (hW _ _) (Ne.symm hn)
  · intro h
    exact Finset.prod_pos (fun i _ => h i)



theorem bridgeWeight_nonneg {Q : Type} [DecidableEq Q] (W : Q → Q → ℝ)
    (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ) (γ : Fin (n + 1) → Q) :
    0 ≤ bridgeWeight W s t n γ := by
  unfold bridgeWeight
  split_ifs
  · exact edgePathWeight_nonneg W hW γ
  · exact le_rfl

theorem bridgeWeight_pos_iff {Q : Type} [DecidableEq Q] (W : Q → Q → ℝ)
    (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ) (γ : Fin (n + 1) → Q) :
    0 < bridgeWeight W s t n γ ↔
      γ 0 = s ∧ γ (Fin.last n) = t ∧ RespectsGraph (fun x y => 0 < W x y) γ := by
  unfold bridgeWeight
  by_cases he : γ 0 = s ∧ γ (Fin.last n) = t
  · simp [he, edgePathWeight_pos_iff W hW γ]
  · simp only [if_neg he, lt_self_iff_false, false_iff]
    exact fun h => he ⟨h.1, h.2.1⟩

/-- A positive bridge between states of one SCC never visits another SCC.
The support graph is that of the original nonnegative matrix, without
assuming transitive one-step support or aperiodicity. -/
theorem positive_bridge_stays_in_component {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q)
    (hst : graphComponent (fun x y => 0 < W x y) s =
      graphComponent (fun x y => 0 < W x y) t)
    (n : ℕ) (γ : Fin (n + 1) → Q) (hγ : 0 < bridgeWeight W s t n γ) :
    ∀ i, graphComponent (fun x y => 0 < W x y) (γ i) =
      graphComponent (fun x y => 0 < W x y) s := by
  obtain ⟨hs, ht, hg⟩ := (bridgeWeight_pos_iff W hW s t n γ).mp hγ
  intro i
  have hends : graphComponent (fun x y => 0 < W x y) (γ 0) =
      graphComponent (fun x y => 0 < W x y) (γ (Fin.last n)) := by
    simpa only [hs, ht] using hst
  simpa only [hs] using graph_path_no_return _ γ hg 0 i (Fin.last n)
    (Fin.zero_le i) (Fin.le_last i) hends

theorem bridgeWeight_zero_outside_component {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q)
    (hst : graphComponent (fun x y => 0 < W x y) s =
      graphComponent (fun x y => 0 < W x y) t)
    (n : ℕ) (γ : Fin (n + 1) → Q)
    (hout : ¬ ∀ i, graphComponent (fun x y => 0 < W x y) (γ i) =
      graphComponent (fun x y => 0 < W x y) s) : bridgeWeight W s t n γ = 0 := by
  apply le_antisymm _ (bridgeWeight_nonneg W hW s t n γ)
  exact le_of_not_gt (fun hp => hout (positive_bridge_stays_in_component W hW s t hst n γ hp))





end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_MatrixBridgeMixing
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- Matrix powers agree with the previously formalized finite-kernel
iteration, with an actual point-mass start. -/
theorem matrix_power_kernel_iterate {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (n : ℕ) :
    ∀ x y, (P ^ n) x y =
      (kernelAdvance (fun u v => P u v))^[n] (fun z => if z = x then 1 else 0) y := by
  induction n with
  | zero => intro x y; simp [Matrix.one_apply, eq_comm]
  | succ n ih =>
    intro x y
    rw [pow_succ, Matrix.mul_apply, Function.iterate_succ_apply', kernelAdvance]
    simp_rw [ih]

theorem positive_matrix_relative_mixing {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 < P x y) (hrows : ∀ x, ∑ y, P x y = 1) :
    ∃ π : Q → ℝ, ∃ C ρ : ℝ,
      (∀ y, 0 < π y) ∧ (∑ y, π y = 1) ∧ 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ n x y, |(P ^ n) x y / π y - 1| ≤ C * ρ ^ n := by
  obtain ⟨π, C, ρ, hπ, hπsum, _, hC, hρ, hρlt, hmix⟩ :=
    positive_kernel_relative_mixing (fun x y => P x y) hP hrows
  refine ⟨π, C, ρ, hπ, hπsum, hC, hρ, hρlt, ?_⟩
  intro n x y
  rw [matrix_power_kernel_iterate]
  apply hmix
  · intro z; split_ifs <;> norm_num
  · simp



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ActualBridgeBoundaryApproximation
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

theorem bridgePartition_nonneg {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ) :
    0 ≤ bridgePartition W s t n :=
  Finset.sum_nonneg (fun γ _ => bridgeWeight_nonneg W hW s t n γ)

theorem bridgeBoundaryMass_pos_iff {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y)
    (l : Fin (k + 1) → ℕ) (s t : Q) (y : Fin k → Q) :
    0 < bridgeBoundaryMass W l s t y ↔ ∀ i : Fin (k + 1),
      0 < bridgePartition W ((Fin.cons s y : Fin (k + 1) → Q) i)
        ((Fin.snoc y t : Fin (k + 1) → Q) i) (l i) := by
  rw [bridgeBoundaryMass_product]
  constructor
  · intro hp i
    have hn := Finset.prod_ne_zero_iff.mp hp.ne' i (Finset.mem_univ i)
    exact lt_of_le_of_ne (bridgePartition_nonneg W hW _ _ _) (Ne.symm hn)
  · intro h
    exact Finset.prod_pos (fun i _ => h i)

theorem bridgeBoundaryMass_pos_iff_path {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y)
    (l : Fin (k + 1) → ℕ) (s t : Q) (y : Fin k → Q) :
    0 < bridgeBoundaryMass W l s t y ↔
      ∃ γ : BoundaryPath Q l s t y, 0 < edgePathWeight W γ.val := by
  rw [← boundaryPath_weight_sum]
  exact (Finset.sum_pos_iff_of_nonneg (fun γ _ => edgePathWeight_nonneg W hW γ.val)).trans
    (by simp only [Finset.mem_univ, true_and])





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

theorem normalized_bridge_observation {Q : Type} [Fintype Q] [DecidableEq Q]
    {k n : ℕ} (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n)
    (s t : Q) (y : Fin k → Q) :
    (∑ γ : Fin (n + 1) → Q, if bridgeBoundaryObservation l hlen γ = y then
      normalizeWeights (bridgeWeight W s t n) γ else 0) =
      normalizeWeights (bridgeBoundaryMass W l s t) y := by
  subst n
  simp only [bridgeBoundaryObservation, Fin.cast_eq_self]
  exact normalized_bridge_boundaries W l s t y

theorem positive_boundary_observation {Q : Type} {k n : ℕ} (W : Q → Q → ℝ)
    (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n) (s t : Q) (y : Fin k → Q)
    (hp : ∃ γ : BoundaryPath Q l s t y, 0 < edgePathWeight W γ.val) :
    ∃ γ : Fin (n + 1) → Q, γ 0 = s ∧ γ (Fin.last n) = t ∧
      bridgeBoundaryObservation l hlen γ = y ∧ 0 < edgePathWeight W γ := by
  subst n
  obtain ⟨γ, hγ⟩ := hp
  obtain ⟨hs, ht, hy⟩ := (bridgeBoundarySpec_iff l s t y γ.val).mp γ.property
  refine ⟨γ.val, hs, ht, ?_, hγ⟩
  simpa only [bridgeBoundaryObservation, Fin.cast_eq_self] using hy

def cutoffBoundaryObservation {Q : Type} (n L : ℕ) (γ : Fin (n + 1) → Q) :
    Fin (cutoffBoundaryCount n L) → Q :=
  bridgeBoundaryObservation (cutoffBlockLengths n L) (cutoffBlockLengths_total n L) γ



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

/-- The recursive bridge observation reads exactly the stated ordered
cuts. A natural-indexed ambient path keeps the offset identity explicit. -/
theorem bridgeBoundaryStates_cutGaps {Q : Type} {k : ℕ}
    (c : Fin (k + 2) → ℕ) (hc : Monotone c) (γ : ℕ → Q) :
    bridgeBoundaryStates (cutGaps c) (fun i => γ (i.val + c 0)) =
      fun i : Fin k => γ (c i.castSucc.succ) := by
  induction k with
  | zero => funext i; exact Fin.elim0 i
  | succ k ih =>
    have ht : Monotone (Fin.tail c) := by
      intro i j hij
      exact hc (Fin.succ_le_succ_iff.mpr hij)
    have hfirst : c 0 ≤ c 1 := hc (Fin.zero_le 1)
    have hoff : c 1 - c 0 + c 0 = c 1 := Nat.sub_add_cancel hfirst
    have hp : (fun i : Fin (bridgeBlockLength (cutGaps (Fin.tail c)) + 1) =>
        γ ((c 1 - c 0) + i.val + c 0)) =
        (fun i : Fin (bridgeBlockLength (cutGaps (Fin.tail c)) + 1) => γ (i.val + (Fin.tail c) 0)) := by
      funext i
      change γ ((c 1 - c 0) + i.val + c 0) = γ (i.val + c 1)
      congr 1
      omega
    change (Fin.cons (γ ((c 1 - c 0) + c 0))
      (bridgeBoundaryStates (cutGaps (Fin.tail c))
        (fun i => γ ((c 1 - c 0) + i.val + c 0))) :
      Fin (k + 1) → Q) = _
    rw [hoff, hp, ih (Fin.tail c) ht]
    funext i
    cases i using Fin.cases <;> rfl

/-- Transport the cut identity to an actual n-edge path. This is the
interface needed to turn category crossing positions into block bridges. -/
theorem bridgeBoundaryObservation_cutGaps {Q : Type} {k n : ℕ}
    (c : Fin (k + 2) → ℕ) (hc : Monotone c) (hstart : c 0 = 0)
    (hfinish : c (Fin.last (k + 1)) = n) (γ : Fin (n + 1) → Q) :
    bridgeBoundaryObservation (cutGaps c)
      (by rw [cutGaps_total c hc, hstart, hfinish, Nat.sub_zero]) γ =
      fun i : Fin k => γ ⟨c i.castSucc.succ, by
        have h := hc (Fin.le_last i.castSucc.succ)
        omega⟩ := by
  let η : ℕ → Q := fun j => if h : j < n + 1 then γ ⟨j, h⟩ else γ 0
  have htotal : bridgeBlockLength (cutGaps c) = n := by
    rw [cutGaps_total c hc, hstart, hfinish, Nat.sub_zero]
  have he : (fun i : Fin (bridgeBlockLength (cutGaps c) + 1) =>
      γ (Fin.cast (congrArg (fun j => j + 1) htotal) i)) =
        (fun i => η (i.val + c 0)) := by
    funext i
    have hi : i.val < n + 1 := by simpa only [htotal] using i.isLt
    simp only [hstart, Nat.add_zero, η, dif_pos hi]
    rfl
  unfold bridgeBoundaryObservation
  rw [he, bridgeBoundaryStates_cutGaps c hc η]
  funext i
  have hi : c i.castSucc.succ < n + 1 := by
    have h := hc (Fin.le_last i.castSucc.succ)
    omega
  simp only [η, dif_pos hi]

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SCCCategories
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

/-- Crossings are indexed by the reachable-set rank of the component they
enter. This rank decreases strictly, so a fixed number of slots suffices. -/
def graphCrossingSlot {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ : Fin (n + 1) → Q) (i : Fin n) : Fin (Fintype.card Q) :=
  ⟨(graphComponent R (γ i.succ)).card - 1, by
    have hp := graphComponent_card_pos R (γ i.succ)
    have hu := graphComponent_card_le R (γ i.succ)
    omega⟩

theorem graphCrossingSlot_injective {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ : Fin (n + 1) → Q) (hγ : RespectsGraph R γ)
    (i j : Fin n) (hi : i ∈ graphCrossings R γ) (hj : j ∈ graphCrossings R γ)
    (he : graphCrossingSlot R γ i = graphCrossingSlot R γ j) : i = j := by
  have hval := congrArg Fin.val he
  change (graphComponent R (γ i.succ)).card - 1 = (graphComponent R (γ j.succ)).card - 1 at hval
  have hip := graphComponent_card_pos R (γ i.succ)
  have hjp := graphComponent_card_pos R (γ j.succ)
  rcases lt_trichotomy i j with h | h | h
  · have := graph_crossing_ranks_ordered R γ hγ i j hj h
    omega
  · exact h
  · have := graph_crossing_ranks_ordered R γ hγ j i hi h
    omega

abbrev CrossingRecord (Q : Type) (n : ℕ) := Fin n × Q × Q

def graphCrossingRecord {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ : Fin (n + 1) → Q) (slot : Fin (Fintype.card Q)) : Option (CrossingRecord Q n) := by
  classical
  exact if h : ∃ i, i ∈ graphCrossings R γ ∧ graphCrossingSlot R γ i = slot then
    let i := Classical.choose h
    some (i, γ i.castSucc, γ i.succ)
  else none

theorem graphCrossingRecord_at_crossing {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ : Fin (n + 1) → Q) (hγ : RespectsGraph R γ)
    (i : Fin n) (hi : i ∈ graphCrossings R γ) :
    graphCrossingRecord R γ (graphCrossingSlot R γ i) = some (i, γ i.castSucc, γ i.succ) := by
  classical
  have hex : ∃ j, j ∈ graphCrossings R γ ∧ graphCrossingSlot R γ j = graphCrossingSlot R γ i :=
    ⟨i, hi, rfl⟩
  rw [graphCrossingRecord, dif_pos hex]
  have hj := Classical.choose_spec hex
  have he := graphCrossingSlot_injective R γ hγ (Classical.choose hex) i hj.1 hi hj.2
  simp only [he]

theorem graphCrossingRecord_some_iff {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ : Fin (n + 1) → Q) (hγ : RespectsGraph R γ)
    (slot : Fin (Fintype.card Q)) (i : Fin n) (x y : Q) :
    graphCrossingRecord R γ slot = some (i, x, y) ↔
      i ∈ graphCrossings R γ ∧ graphCrossingSlot R γ i = slot ∧
        γ i.castSucc = x ∧ γ i.succ = y := by
  classical
  constructor
  · intro h
    unfold graphCrossingRecord at h
    split_ifs at h with hex
    · have hj := Classical.choose_spec hex
      have hp := Option.some.inj h
      simp only [Prod.mk.injEq] at hp
      rcases hp with ⟨rfl, hx, hy⟩
      exact ⟨hj.1, hj.2, hx, hy⟩
  · rintro ⟨hi, hslot, rfl, rfl⟩
    rw [← hslot]
    exact graphCrossingRecord_at_crossing R γ hγ i hi

/-- Initial/final states and cross-SCC times/edges. Internal path states
are deliberately absent: conditioning on a category leaves whole bridges. -/
abbrev GraphCategory (Q : Type) [Fintype Q] (n : ℕ) :=
  Q × Q × (Fin (Fintype.card Q) → Option (CrossingRecord Q n))

def graphCategory {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ : Fin (n + 1) → Q) : GraphCategory Q n :=
  (γ 0, γ (Fin.last n), graphCrossingRecord R γ)

theorem graphCategory_recovers_crossing {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ η : Fin (n + 1) → Q) (hγ : RespectsGraph R γ) (hη : RespectsGraph R η)
    (hcat : graphCategory R γ = graphCategory R η) (i : Fin n)
    (hi : i ∈ graphCrossings R γ) :
    i ∈ graphCrossings R η ∧ γ i.castSucc = η i.castSucc ∧ γ i.succ = η i.succ := by
  have he := congrArg (fun c : GraphCategory Q n => c.2.2 (graphCrossingSlot R γ i)) hcat
  change graphCrossingRecord R γ _ = graphCrossingRecord R η _ at he
  rw [graphCrossingRecord_at_crossing R γ hγ i hi] at he
  obtain ⟨hiη, _, hx, hy⟩ := (graphCrossingRecord_some_iff R η hη _ i _ _).mp he.symm
  exact ⟨hiη, hx.symm, hy.symm⟩

/-- Equality of the finite encoding means exactly equality of the category
data used in the source proof, with no hidden constraint on internal paths. -/
theorem graphCategory_eq_iff {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ η : Fin (n + 1) → Q) (hγ : RespectsGraph R γ) (hη : RespectsGraph R η) :
    graphCategory R γ = graphCategory R η ↔
      γ 0 = η 0 ∧ γ (Fin.last n) = η (Fin.last n) ∧
      graphCrossings R γ = graphCrossings R η ∧
      ∀ i ∈ graphCrossings R γ, γ i.castSucc = η i.castSucc ∧ γ i.succ = η i.succ := by
  classical
  constructor
  · intro h
    refine ⟨congrArg Prod.fst h, congrArg (fun c : GraphCategory Q n => c.2.1) h, ?_, ?_⟩
    · apply Finset.ext
      intro i
      exact ⟨fun hi => (graphCategory_recovers_crossing R γ η hγ hη h i hi).1,
        fun hi => (graphCategory_recovers_crossing R η γ hη hγ h.symm i hi).1⟩
    · intro i hi
      exact (graphCategory_recovers_crossing R γ η hγ hη h i hi).2
  · rintro ⟨hstart, hfinish, hcross, hend⟩
    apply Prod.ext hstart
    apply Prod.ext hfinish
    funext slot
    apply Option.ext
    rintro ⟨i, x, y⟩
    change graphCrossingRecord R γ slot = some (i, x, y) ↔
      graphCrossingRecord R η slot = some (i, x, y)
    rw [graphCrossingRecord_some_iff R γ hγ, graphCrossingRecord_some_iff R η hη]
    have hslot (hi : i ∈ graphCrossings R γ) : graphCrossingSlot R γ i = graphCrossingSlot R η i := by
      apply Fin.ext
      change (graphComponent R (γ i.succ)).card - 1 = (graphComponent R (η i.succ)).card - 1
      rw [(hend i hi).2]
    constructor
    · rintro ⟨hi, hs, hx, hy⟩
      have he := hend i hi
      exact ⟨by simpa only [← hcross] using hi, (hslot hi).symm.trans hs,
        he.1.symm.trans hx, he.2.symm.trans hy⟩
    · rintro ⟨hi, hs, hx, hy⟩
      have hi' : i ∈ graphCrossings R γ := by simpa only [hcross] using hi
      have he := hend i hi'
      exact ⟨hi', (hslot hi').trans hs, he.1.trans hx, he.2.trans hy⟩

/-- For fixed state space, the category type has polynomial size in n.
This counts a superset of realizable categories, so it also bounds every
positive-probability accepting category family. -/
theorem graphCategory_card_polynomial {Q : Type} [Fintype Q] (n : ℕ) :
    Fintype.card (GraphCategory Q n) ≤
      (Fintype.card Q * Fintype.card Q * (Fintype.card Q * Fintype.card Q + 1) ^ Fintype.card Q) *
        (n + 1) ^ Fintype.card Q := by
  let q := Fintype.card Q
  have hh : n * (q * q) + 1 ≤ (q * q + 1) * (n + 1) := by nlinarith
  calc
    _ = q * q * (n * (q * q) + 1) ^ q := by
      simp only [GraphCategory, CrossingRecord, Fintype.card_prod, Fintype.card_fun,
        Fintype.card_option, Fintype.card_fin]
      dsimp only [q]
      ring
    _ ≤ q * q * ((q * q + 1) * (n + 1)) ^ q :=
      Nat.mul_le_mul_left _ (pow_le_pow_left' hh q)
    _ = _ := by rw [mul_pow]; ring

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SCCCategoryFibers
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

/-- Holding the original crossing endpoints fixed determines the entire
SCC itinerary of every other valid path. Extra crossings are impossible. -/
theorem graph_path_components_of_crossing_endpoints {Q : Type} [Fintype Q]
    (R : Q → Q → Prop) {n : ℕ} (γ η : Fin (n + 1) → Q)
    (hη : RespectsGraph R η) (hs : γ 0 = η 0) (ht : γ (Fin.last n) = η (Fin.last n))
    (he : ∀ i ∈ graphCrossings R γ, γ i.castSucc = η i.castSucc ∧ γ i.succ = η i.succ) :
    ∀ i, graphComponent R (γ i) = graphComponent R (η i) := by
  have hforward : ∀ i, graphComponent R (η i) ⊆ graphComponent R (γ i) := by
    intro i
    induction i using Fin.induction with
    | zero => rw [hs]
    | succ j ih =>
      by_cases hj : j ∈ graphCrossings R γ
      · rw [(he j hj).2]
      · have hsame : graphComponent R (γ j.castSucc) = graphComponent R (γ j.succ) :=
          not_not.mp (fun h => hj ((mem_graphCrossings R γ j).mpr h))
        rw [← hsame]
        exact (graphComponent_subset R (.single (hη j))).trans ih
  have hbackward : ∀ i, graphComponent R (γ i) ⊆ graphComponent R (η i) := by
    intro i
    refine Fin.reverseInduction ?_ (fun j ih => ?_) i
    · rw [ht]
    · by_cases hj : j ∈ graphCrossings R γ
      · rw [(he j hj).1]
      · have hsame : graphComponent R (γ j.castSucc) = graphComponent R (γ j.succ) :=
          not_not.mp (fun h => hj ((mem_graphCrossings R γ j).mpr h))
        rw [hsame]
        exact ih.trans (graphComponent_subset R (.single (hη j)))
  intro i
  exact Finset.Subset.antisymm (hbackward i) (hforward i)

theorem graphCategory_eq_boundary_iff {Q : Type} [Fintype Q]
    (R : Q → Q → Prop) {n : ℕ} (γ η : Fin (n + 1) → Q)
    (hγ : RespectsGraph R γ) (hη : RespectsGraph R η) :
    graphCategory R γ = graphCategory R η ↔
      γ 0 = η 0 ∧ γ (Fin.last n) = η (Fin.last n) ∧
        ∀ i ∈ graphCrossings R γ, γ i.castSucc = η i.castSucc ∧ γ i.succ = η i.succ := by
  rw [graphCategory_eq_iff R γ η hγ hη]
  constructor
  · rintro ⟨hs, ht, _, he⟩
    exact ⟨hs, ht, he⟩
  · rintro ⟨hs, ht, he⟩
    refine ⟨hs, ht, ?_, he⟩
    have hc := graph_path_components_of_crossing_endpoints R γ η hη hs ht he
    apply Finset.ext
    intro i
    rw [mem_graphCrossings, mem_graphCrossings, hc i.castSucc, hc i.succ]

def CategoryBoundaryMatches {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ η : Fin (n + 1) → Q) : Prop :=
  γ 0 = η 0 ∧ γ (Fin.last n) = η (Fin.last n) ∧
    ∀ i ∈ graphCrossings R γ, γ i.castSucc = η i.castSucc ∧ γ i.succ = η i.succ

instance categoryBoundaryMatchesDecidable {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ η : Fin (n + 1) → Q) : Decidable (CategoryBoundaryMatches R γ η) :=
  Classical.propDecidable _

/-- On the support graph of a nonnegative kernel, restricting a full path
weight to one category is exactly fixing its boundary states. The initial
weight is constant on this fiber and factors out. -/
theorem category_path_weight_boundary {Q : Type} [Fintype Q] [DecidableEq Q]
    (μ : Q → ℝ) (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) {n : ℕ}
    (γ η : Fin (n + 1) → Q) (hγ : RespectsGraph (fun x y => 0 < W x y) γ) :
    (if graphCategory (fun x y => 0 < W x y) γ = graphCategory (fun x y => 0 < W x y) η
      then finitePathWeight μ W η else 0) =
    μ (γ 0) * (if CategoryBoundaryMatches (fun x y => 0 < W x y) γ η
      then edgePathWeight W η else 0) := by
  classical
  have hw : finitePathWeight μ W η = μ (η 0) * edgePathWeight W η := by
    simp [finitePathWeight, edgePathWeight]
  by_cases hη : RespectsGraph (fun x y => 0 < W x y) η
  · have heq := graphCategory_eq_boundary_iff (fun x y => 0 < W x y) γ η hγ hη
    change (_ = _) ↔ CategoryBoundaryMatches _ γ η at heq
    by_cases he : CategoryBoundaryMatches (fun x y => 0 < W x y) γ η
    · rw [if_pos (heq.mpr he), if_pos he, hw, he.1]
    · rw [if_neg (fun h => he (heq.mp h)), if_neg he, mul_zero]
  · have hz : edgePathWeight W η = 0 := by
      apply le_antisymm _ (edgePathWeight_nonneg W hW η)
      exact le_of_not_gt (fun hp => hη ((edgePathWeight_pos_iff W hW η).mp hp))
    simp only [hw, hz, mul_zero, ite_self]



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

theorem mem_graphInteriorCuts {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ : Fin (n + 1) → Q) (j : Fin (n + 1)) :
    j ∈ graphInteriorCuts R γ ↔ j ≠ 0 ∧ j ≠ Fin.last n ∧
      ∃ i ∈ graphCrossings R γ, j = i.castSucc ∨ j = i.succ := by
  classical
  simp [graphInteriorCuts]

theorem graphInteriorCuts_card_le {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ : Fin (n + 1) → Q) :
    (graphInteriorCuts R γ).card ≤ 2 * (graphCrossings R γ).card := by
  classical
  have hsub : graphInteriorCuts R γ ⊆
      (graphCrossings R γ).image Fin.castSucc ∪ (graphCrossings R γ).image Fin.succ := by
    intro j hj
    obtain ⟨_, _, i, hi, he⟩ := (mem_graphInteriorCuts R γ j).mp hj
    rcases he with rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  have h := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have h1 := Finset.card_image_le (s := graphCrossings R γ) (f := Fin.castSucc)
  have h2 := Finset.card_image_le (s := graphCrossings R γ) (f := Fin.succ)
  omega

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

theorem graphOrderedCuts_internal {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ : Fin (n + 1) → Q) (i : Fin (graphInteriorCuts R γ).card) :
    graphOrderedCuts R γ i.castSucc.succ = ((graphInteriorCuts R γ).orderEmbOfFin rfl i).val := by
  simp [graphOrderedCuts]

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

theorem graphCategoryBlockLengths_count {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ : Fin (n + 1) → Q) (hγ : RespectsGraph R γ) :
    (graphInteriorCuts R γ).card + 1 ≤ 2 * Fintype.card Q - 1 := by
  have h1 := graphInteriorCuts_card_le R γ
  have h2 := graph_crossings_card_bound R γ hγ
  omega

theorem categoryBoundaryMatches_iff_interiorCuts {Q : Type} [Fintype Q]
    (R : Q → Q → Prop) {n : ℕ} (γ η : Fin (n + 1) → Q) :
    CategoryBoundaryMatches R γ η ↔ γ 0 = η 0 ∧ γ (Fin.last n) = η (Fin.last n) ∧
      ∀ j ∈ graphInteriorCuts R γ, γ j = η j := by
  constructor
  · rintro ⟨hs, ht, he⟩
    refine ⟨hs, ht, ?_⟩
    intro j hj
    obtain ⟨_, _, i, hi, heq⟩ := (mem_graphInteriorCuts R γ j).mp hj
    rcases heq with rfl | rfl
    · exact (he i hi).1
    · exact (he i hi).2
  · rintro ⟨hs, ht, he⟩
    refine ⟨hs, ht, ?_⟩
    intro i hi
    have hpoint (j : Fin (n + 1)) (hj : j = i.castSucc ∨ j = i.succ) : γ j = η j := by
      by_cases h0 : j = 0
      · simpa only [h0] using hs
      by_cases hn : j = Fin.last n
      · simpa only [hn] using ht
      exact he j ((mem_graphInteriorCuts R γ j).mpr ⟨h0, hn, i, hi, hj⟩)
    exact ⟨hpoint i.castSucc (Or.inl rfl), hpoint i.succ (Or.inr rfl)⟩

theorem graphCategoryBlock_observation {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ η : Fin (n + 1) → Q) :
    bridgeBoundaryObservation (graphCategoryBlockLengths R γ) (graphCategoryBlockLengths_total R γ) η =
      fun i => η ((graphInteriorCuts R γ).orderEmbOfFin rfl i) := by
  have h := bridgeBoundaryObservation_cutGaps (graphOrderedCuts R γ)
    (graphOrderedCuts_monotone R γ) (graphOrderedCuts_start R γ) (graphOrderedCuts_finish R γ) η
  apply h.trans
  funext i
  congr 1
  apply Fin.ext
  exact graphOrderedCuts_internal R γ i

theorem categoryBoundaryMatches_iff_block_observation {Q : Type} [Fintype Q]
    (R : Q → Q → Prop) {n : ℕ} (γ η : Fin (n + 1) → Q) :
    CategoryBoundaryMatches R γ η ↔ γ 0 = η 0 ∧ γ (Fin.last n) = η (Fin.last n) ∧
      bridgeBoundaryObservation (graphCategoryBlockLengths R γ) (graphCategoryBlockLengths_total R γ) γ =
      bridgeBoundaryObservation (graphCategoryBlockLengths R γ) (graphCategoryBlockLengths_total R γ) η := by
  rw [categoryBoundaryMatches_iff_interiorCuts R γ η, graphCategoryBlock_observation,
    graphCategoryBlock_observation]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · intro h
    funext i
    exact h _ ((graphInteriorCuts R γ).orderEmbOfFin_mem rfl i)
  · intro h j hj
    obtain ⟨i, hi⟩ := ((graphInteriorCuts R γ).orderIsoOfFin rfl).surjective ⟨j, hj⟩
    have hv := congrArg Subtype.val hi
    change (graphInteriorCuts R γ).orderEmbOfFin rfl i = j at hv
    have hh := congrFun h i
    change γ ((graphInteriorCuts R γ).orderEmbOfFin rfl i) = η ((graphInteriorCuts R γ).orderEmbOfFin rfl i) at hh
    rw [hv] at hh
    exact hh



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SCCBlockKinds
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

theorem graph_component_eq_of_no_crossings {Q : Type} [Fintype Q]
    (R : Q → Q → Prop) {n : ℕ} (γ : Fin (n + 1) → Q) (u v : Fin (n + 1)) (huv : u ≤ v)
    (hno : ∀ i : Fin n, u.val ≤ i.val → i.val < v.val → i ∉ graphCrossings R γ) :
    graphComponent R (γ u) = graphComponent R (γ v) := by
  have haux : ∀ b : ℕ, u.val ≤ b → ∀ hb : b ≤ v.val,
      graphComponent R (γ u) = graphComponent R (γ ⟨b, by omega⟩) := by
    intro b hub
    induction b, hub using Nat.le_induction with
    | base => intro hb; rfl
    | succ b hub ih =>
      intro hb
      have hh := ih (by omega)
      let i : Fin n := ⟨b, by omega⟩
      have hn := hno i hub (by change b < v.val; omega)
      have he : graphComponent R (γ i.castSucc) = graphComponent R (γ i.succ) := by
        by_contra hc
        exact hn ((mem_graphCrossings R γ i).mpr hc)
      exact hh.trans he
  exact haux v.val huv le_rfl

/-- No category cut lies strictly between consecutive ordered cuts. -/
theorem graphOrderedCuts_no_interior {Q : Type} [Fintype Q]
    (R : Q → Q → Prop) {n : ℕ} (γ : Fin (n + 1) → Q)
    (i : Fin ((graphInteriorCuts R γ).card + 1)) (j : Fin (n + 1))
    (hj : j ∈ graphInteriorCuts R γ) :
    ¬ (graphOrderedCuts R γ i.castSucc < j.val ∧ j.val < graphOrderedCuts R γ i.succ) := by
  obtain ⟨b, hb⟩ := ((graphInteriorCuts R γ).orderIsoOfFin rfl).surjective ⟨j, hj⟩
  have hv := congrArg (fun z => z.val.val) hb
  have hcut : graphOrderedCuts R γ b.castSucc.succ = j.val :=
    (graphOrderedCuts_internal R γ b).trans hv
  have hmono := graphOrderedCuts_monotone R γ
  rintro ⟨hl, hr⟩
  rw [← hcut] at hl hr
  have hleft : i.castSucc < b.castSucc.succ := by
    by_contra h
    have hle := hmono (le_of_not_gt h)
    omega
  have hright : b.castSucc.succ < i.succ := by
    by_contra h
    have hle := hmono (le_of_not_gt h)
    omega
  simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at hleft hright
  omega

/-- Any cross-SCC edge lying in a constructed block occupies that entire
block. Both endpoints were included among the category cuts. -/
theorem graphOrderedCuts_crossing_block {Q : Type} [Fintype Q]
    (R : Q → Q → Prop) {n : ℕ} (γ : Fin (n + 1) → Q)
    (i : Fin ((graphInteriorCuts R γ).card + 1)) (j : Fin n)
    (hj : j ∈ graphCrossings R γ)
    (hl : graphOrderedCuts R γ i.castSucc ≤ j.val)
    (hr : j.val < graphOrderedCuts R γ i.succ) :
    graphOrderedCuts R γ i.castSucc = j.val ∧
      graphOrderedCuts R γ i.succ = j.val + 1 := by
  have hu : graphOrderedCuts R γ i.succ ≤ n := by
    have h := graphOrderedCuts_monotone R γ (Fin.le_last i.succ)
    simpa only [graphOrderedCuts_finish] using h
  have hleft : graphOrderedCuts R γ i.castSucc = j.val := by
    by_contra h
    have hstrict : graphOrderedCuts R γ i.castSucc < j.val := by omega
    have h0 : j.castSucc ≠ 0 := by intro he; have := congrArg Fin.val he; simp at this; omega
    have hn : j.castSucc ≠ Fin.last n := by intro he; have := congrArg Fin.val he; simp at this; omega
    have hm := (mem_graphInteriorCuts R γ j.castSucc).mpr ⟨h0, hn, j, hj, Or.inl rfl⟩
    exact graphOrderedCuts_no_interior R γ i j.castSucc hm ⟨hstrict, hr⟩
  have hright : graphOrderedCuts R γ i.succ = j.val + 1 := by
    by_contra h
    have hstrict : j.val + 1 < graphOrderedCuts R γ i.succ := by omega
    have h0 : j.succ ≠ 0 := by intro he; have := congrArg Fin.val he; simp at this
    have hn : j.succ ≠ Fin.last n := by intro he; have := congrArg Fin.val he; simp at this; omega
    have hm := (mem_graphInteriorCuts R γ j.succ).mpr ⟨h0, hn, j, hj, Or.inr rfl⟩
    exact graphOrderedCuts_no_interior R γ i j.succ hm ⟨by change _ < j.val + 1; omega, hstrict⟩
  exact ⟨hleft, hright⟩

/-- Each constructed category block either has both endpoints in one
actual SCC, or is a single fixed cross-SCC edge. No longer block crosses
components, so the periodic SCC bridge theorems apply to the internal ones. -/
theorem graphCategoryBlockKinds {Q : Type} [Fintype Q]
    (R : Q → Q → Prop) {n : ℕ} (γ : Fin (n + 1) → Q)
    (i : Fin ((graphInteriorCuts R γ).card + 1)) :
    let left : Fin (n + 1) := ⟨graphOrderedCuts R γ i.castSucc, by
      have h := graphOrderedCuts_monotone R γ (Fin.le_last i.castSucc)
      rw [graphOrderedCuts_finish] at h
      omega⟩
    let right : Fin (n + 1) := ⟨graphOrderedCuts R γ i.succ, by
      have h := graphOrderedCuts_monotone R γ (Fin.le_last i.succ)
      rw [graphOrderedCuts_finish] at h
      omega⟩
    graphComponent R (γ left) = graphComponent R (γ right) ∨
      (graphCategoryBlockLengths R γ i = 1 ∧
        ∃ j ∈ graphCrossings R γ, j.val = left.val ∧ j.val + 1 = right.val) := by
  classical
  dsimp only
  by_cases hex : ∃ j ∈ graphCrossings R γ,
      graphOrderedCuts R γ i.castSucc ≤ j.val ∧ j.val < graphOrderedCuts R γ i.succ
  · obtain ⟨j, hj, hl, hr⟩ := hex
    obtain ⟨hleft, hright⟩ := graphOrderedCuts_crossing_block R γ i j hj hl hr
    right
    refine ⟨?_, j, hj, hleft.symm, hright.symm⟩
    simp only [graphCategoryBlockLengths, cutGaps, hleft, hright, Nat.add_sub_cancel_left]
  · left
    apply graph_component_eq_of_no_crossings R γ _ _
      (graphOrderedCuts_monotone R γ (by exact Fin.castSucc_le_succ i))
    intro j hl hr hj
    exact hex ⟨j, hj, hl, hr⟩

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

/-- The full category fiber is the constructed block-boundary fiber,
including candidates outside the support graph, whose path weights vanish. -/
theorem category_path_weight_constructed_blocks {Q : Type} [Fintype Q] [DecidableEq Q]
    (μ : Q → ℝ) (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) {n : ℕ}
    (γ η : Fin (n + 1) → Q) (hγ : RespectsGraph (fun x y => 0 < W x y) γ) :
    (if graphCategory (fun x y => 0 < W x y) γ = graphCategory (fun x y => 0 < W x y) η
      then finitePathWeight μ W η else 0) =
    μ (γ 0) * (if CategoryBlockMatches (fun x y => 0 < W x y) γ η
      then edgePathWeight W η else 0) := by
  classical
  rw [category_path_weight_boundary μ W hW γ η hγ]
  have he : CategoryBoundaryMatches (fun x y => 0 < W x y) γ η ↔
      CategoryBlockMatches (fun x y => 0 < W x y) γ η :=
    categoryBoundaryMatches_iff_block_observation _ γ η
  by_cases hb : CategoryBoundaryMatches (fun x y => 0 < W x y) γ η
  · rw [if_pos hb, if_pos (he.mp hb)]
  · rw [if_neg hb, if_neg (fun h => hb (he.mpr h))]



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_EmbeddedWeights
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

theorem embedded_weight_fiber {α β : Type} [Fintype α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (w : β → ℝ)
    (hsupp : ∀ b, (¬ ∃ a, f a = b) → w b = 0) (b : β) :
    (∑ a, if f a = b then w (f a) else 0) = w b := by
  classical
  by_cases h : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := h
    simp only [hf.eq_iff]
    simp
  · rw [hsupp b h]
    apply Finset.sum_eq_zero
    intro a _
    exact if_neg (fun ha => h ⟨a, ha⟩)

theorem embedded_weight_sum {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (w : β → ℝ)
    (hsupp : ∀ b, (¬ ∃ a, f a = b) → w b = 0) :
    (∑ a, w (f a)) = ∑ b, w b := by
  classical
  conv_rhs => arg 2; ext b; rw [← embedded_weight_fiber f hf w hsupp b]
  rw [Finset.sum_comm]
  simp

/-- Exact transport of normalized supported weights along an injection.
This includes zero total mass as an algebraic identity. -/
theorem embedded_normalized_weights {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (w : β → ℝ)
    (hsupp : ∀ b, (¬ ∃ a, f a = b) → w b = 0) (b : β) :
    (∑ a, if f a = b then normalizeWeights (fun a => w (f a)) a else 0) =
      normalizeWeights w b := by
  classical
  simp only [normalizeWeights, embedded_weight_sum f hf w hsupp]
  have hterm (a : α) :
      (if f a = b then w (f a) / (∑ z, w z) else 0) =
        (if f a = b then w (f a) else 0) / (∑ z, w z) := by
    split_ifs <;> simp
  simp_rw [hterm]
  rw [← Finset.sum_div, embedded_weight_fiber f hf w hsupp b]

theorem embedded_normalized_tv_le {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (w : β → ℝ)
    (hsupp : ∀ b, (¬ ∃ a, f a = b) → w b = 0) (p : α → ℝ) :
    tv (normalizeWeights w) (fun b => ∑ a, if f a = b then p a else 0) ≤
      tv (normalizeWeights (fun a => w (f a))) p := by
  have h := tv_map_le f (normalizeWeights (fun a => w (f a))) p
  simpa only [embedded_normalized_weights f hf w hsupp] using h

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_BridgeConcatenationLaw
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def boundaryRestrictedWeight {Q : Type} (W : Q → Q → ℝ) {k : ℕ}
    (l : Fin (k + 1) → ℕ) (s t : Q) (y : Fin k → Q) :
    (Fin (bridgeBlockLength l + 1) → Q) → ℝ := by
  classical
  exact fun γ => if bridgeBoundarySpec l s t y γ then edgePathWeight W γ else 0

def concatenateBridgeBlocks {Q : Type} {k : ℕ} (l : Fin (k + 1) → ℕ)
    (s t : Q) (y : Fin k → Q) (b : BoundaryBlocks Q l s t y) :
    Fin (bridgeBlockLength l + 1) → Q := ((boundaryBlocksEquiv l s t y).symm b).val

theorem concatenateBridgeBlocks_spec {Q : Type} {k : ℕ} (l : Fin (k + 1) → ℕ)
    (s t : Q) (y : Fin k → Q) (b : BoundaryBlocks Q l s t y) :
    bridgeBoundarySpec l s t y (concatenateBridgeBlocks l s t y b) :=
  ((boundaryBlocksEquiv l s t y).symm b).property

theorem concatenateBridgeBlocks_weight {Q : Type} {k : ℕ} (W : Q → Q → ℝ)
    (l : Fin (k + 1) → ℕ) (s t : Q) (y : Fin k → Q) (b : BoundaryBlocks Q l s t y) :
    edgePathWeight W (concatenateBridgeBlocks l s t y b) = ∏ i, edgePathWeight W (b i).val := by
  rw [edgePathWeight_blocks]
  apply Finset.prod_congr rfl
  intro i _
  have h := congrArg (fun z : BoundaryBlocks Q l s t y => (z i).val)
    ((boundaryBlocksEquiv l s t y).apply_symm_apply b)
  change boundaryBlockPath l (concatenateBridgeBlocks l s t y b) i = (b i).val at h
  rw [h]



theorem boundaryRestrictedWeight_sum {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (s t : Q) (y : Fin k → Q) :
    (∑ γ, boundaryRestrictedWeight W l s t y γ) = bridgeBoundaryMass W l s t y := by
  classical
  rw [← boundaryPath_weight_sum]
  rw [← Finset.sum_subtype (Finset.univ.filter (fun γ => bridgeBoundarySpec l s t y γ)) (by simp)]
  rw [Finset.sum_filter]
  rfl

theorem normalized_boundaryPath_embed {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (s t : Q) (y : Fin k → Q)
    (η : Fin (bridgeBlockLength l + 1) → Q) :
    (∑ γ : BoundaryPath Q l s t y, if γ.val = η then
      normalizeWeights (fun z : BoundaryPath Q l s t y => edgePathWeight W z.val) γ else 0) =
      normalizeWeights (boundaryRestrictedWeight W l s t y) η := by
  classical
  have hsupp : ∀ γ, (¬ ∃ z : BoundaryPath Q l s t y, z.val = γ) →
      boundaryRestrictedWeight W l s t y γ = 0 := by
    intro γ h
    exact if_neg (fun hp => h ⟨⟨γ, hp⟩, rfl⟩)
  have he : (fun γ : BoundaryPath Q l s t y => boundaryRestrictedWeight W l s t y γ.val) =
      (fun γ : BoundaryPath Q l s t y => edgePathWeight W γ.val) := by
    funext γ
    exact if_pos γ.property
  have h := embedded_normalized_weights (fun γ : BoundaryPath Q l s t y => γ.val)
    Subtype.val_injective (boundaryRestrictedWeight W l s t y) hsupp η
  rw [he] at h
  exact h

/-- Independent endpoint-compatible block bridges, followed by actual
concatenation, reproduce the complete ambient conditional path law. -/
theorem concatenated_independent_bridge_law {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (s t : Q) (y : Fin k → Q)
    (η : Fin (bridgeBlockLength l + 1) → Q) :
    (∑ b : BoundaryBlocks Q l s t y, if concatenateBridgeBlocks l s t y b = η then
      (∏ i, normalizeWeights (fun α : EndpointPath Q
        ((Fin.cons s y : Fin (k + 1) → Q) i) ((Fin.snoc y t : Fin (k + 1) → Q) i) (l i) =>
          edgePathWeight W α.val) (b i)) else 0) =
      normalizeWeights (boundaryRestrictedWeight W l s t y) η := by
  classical
  simp_rw [← boundaryBlocks_independent_law W l s t y]
  have he := (boundaryBlocksEquiv l s t y).symm.sum_comp
    (fun γ : BoundaryPath Q l s t y => if γ.val = η then
      normalizeWeights (fun z : BoundaryPath Q l s t y => edgePathWeight W z.val) γ else 0)
  exact he.trans (normalized_boundaryPath_embed W l s t y η)

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_BridgeConcatenationTransport
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def pathLengthEquiv {Q : Type} {m n : ℕ} (h : m = n) :
    (Fin (m + 1) → Q) ≃ (Fin (n + 1) → Q) :=
  Equiv.cast (congrArg (fun j => Fin (j + 1) → Q) h)

def concatenateBridgeBlocksAtLength {Q : Type} {k n : ℕ}
    (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n)
    (s t : Q) (y : Fin k → Q) (b : BoundaryBlocks Q l s t y) : Fin (n + 1) → Q :=
  pathLengthEquiv hlen (concatenateBridgeBlocks l s t y b)

def boundaryRestrictedWeightAtLength {Q : Type} {k n : ℕ} (W : Q → Q → ℝ)
    (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n) (s t : Q) (y : Fin k → Q) :
    (Fin (n + 1) → Q) → ℝ :=
  fun γ => boundaryRestrictedWeight W l s t y ((pathLengthEquiv hlen).symm γ)

theorem concatenateBridgeBlocksAtLength_spec {Q : Type} {k n : ℕ}
    (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n)
    (s t : Q) (y : Fin k → Q) (b : BoundaryBlocks Q l s t y) :
    let γ := concatenateBridgeBlocksAtLength l hlen s t y b
    γ 0 = s ∧ γ (Fin.last n) = t ∧ bridgeBoundaryObservation l hlen γ = y := by
  subst n
  simpa only [concatenateBridgeBlocksAtLength, pathLengthEquiv, Equiv.cast_refl,
    Equiv.refl_apply, bridgeBoundaryObservation, Fin.cast_eq_self] using
    (bridgeBoundarySpec_iff l s t y _).mp (concatenateBridgeBlocks_spec l s t y b)

theorem concatenateBridgeBlocksAtLength_weight {Q : Type} {k n : ℕ}
    (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n)
    (s t : Q) (y : Fin k → Q) (b : BoundaryBlocks Q l s t y) :
    edgePathWeight W (concatenateBridgeBlocksAtLength l hlen s t y b) =
      ∏ i, edgePathWeight W (b i).val := by
  subst n
  exact concatenateBridgeBlocks_weight W l s t y b

theorem boundaryRestrictedWeightAtLength_eq {Q : Type} [DecidableEq Q] {k n : ℕ} (W : Q → Q → ℝ)
    (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n) (s t : Q) (y : Fin k → Q)
    (γ : Fin (n + 1) → Q) :
    boundaryRestrictedWeightAtLength W l hlen s t y γ =
      if γ 0 = s ∧ γ (Fin.last n) = t ∧ bridgeBoundaryObservation l hlen γ = y
      then edgePathWeight W γ else 0 := by
  classical
  subst n
  change boundaryRestrictedWeight W l s t y γ = _
  have he : bridgeBoundarySpec l s t y γ ↔
      γ 0 = s ∧ γ (Fin.last (bridgeBlockLength l)) = t ∧
        bridgeBoundaryObservation l rfl γ = y := by
    simpa only [bridgeBoundaryObservation, Fin.cast_eq_self] using bridgeBoundarySpec_iff l s t y γ
  by_cases h : bridgeBoundarySpec l s t y γ
  · rw [boundaryRestrictedWeight, if_pos h, if_pos (he.mp h)]
  · rw [boundaryRestrictedWeight, if_neg h, if_neg (fun hh => h (he.mpr hh))]

theorem concatenated_independent_bridge_law_at_length {Q : Type} [Fintype Q] [DecidableEq Q]
    {k n : ℕ} (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n)
    (s t : Q) (y : Fin k → Q) (η : Fin (n + 1) → Q) :
    (∑ b : BoundaryBlocks Q l s t y,
      if concatenateBridgeBlocksAtLength l hlen s t y b = η then
        (∏ i, normalizeWeights (fun α : EndpointPath Q
          ((Fin.cons s y : Fin (k + 1) → Q) i) ((Fin.snoc y t : Fin (k + 1) → Q) i) (l i) =>
            edgePathWeight W α.val) (b i)) else 0) =
      normalizeWeights (boundaryRestrictedWeightAtLength W l hlen s t y) η := by
  subst n
  exact concatenated_independent_bridge_law W l s t y η

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_CategoryConcatenation
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators











theorem category_boundaryRestrictedWeight {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (R : Q → Q → Prop) {n : ℕ} (γ : Fin (n + 1) → Q) :
    boundaryRestrictedWeightAtLength W (graphCategoryBlockLengths R γ)
      (graphCategoryBlockLengths_total R γ) (γ 0) (γ (Fin.last n))
      (bridgeBoundaryObservation (graphCategoryBlockLengths R γ) (graphCategoryBlockLengths_total R γ) γ) =
      fun η => if CategoryBlockMatches R γ η then edgePathWeight W η else 0 := by
  classical
  funext η
  rw [boundaryRestrictedWeightAtLength_eq]
  have he : (η 0 = γ 0 ∧ η (Fin.last n) = γ (Fin.last n) ∧
      bridgeBoundaryObservation (graphCategoryBlockLengths R γ) (graphCategoryBlockLengths_total R γ) η =
        bridgeBoundaryObservation (graphCategoryBlockLengths R γ) (graphCategoryBlockLengths_total R γ) γ) ↔
      CategoryBlockMatches R γ η := by
    simp only [CategoryBlockMatches, eq_comm]
  by_cases h : CategoryBlockMatches R γ η
  · rw [if_pos h, if_pos (he.mpr h)]
  · rw [if_neg h, if_neg (fun hh => h (he.mp hh))]







end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ApproximateBridgeConcatenation
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

abbrev BridgeBlockPath (Q : Type) {k : ℕ} (l : Fin (k + 1) → ℕ)
    (s t : Q) (y : Fin k → Q) (i : Fin (k + 1)) :=
  EndpointPath Q ((Fin.cons s y : Fin (k + 1) → Q) i)
    ((Fin.snoc y t : Fin (k + 1) → Q) i) (l i)

def concatenateBlockLaw {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n) (s t : Q) (y : Fin k → Q)
    (p : ∀ i, BridgeBlockPath Q l s t y i → ℝ) : (Fin (n + 1) → Q) → ℝ :=
  fiberMass (concatenateBridgeBlocksAtLength l hlen s t y)
    (fun b : BoundaryBlocks Q l s t y => ∏ i, p i (b i))

theorem concatenateBlockLaw_nonneg {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n) (s t : Q) (y : Fin k → Q)
    (p : ∀ i, BridgeBlockPath Q l s t y i → ℝ) (hp : ∀ i b, 0 ≤ p i b) :
    ∀ γ, 0 ≤ concatenateBlockLaw l hlen s t y p γ :=
  fiberMass_nonneg _ _ (fun b => Finset.prod_nonneg (fun i _ => hp i (b i)))

theorem concatenateBlockLaw_sum {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n) (s t : Q) (y : Fin k → Q)
    (p : ∀ i, BridgeBlockPath Q l s t y i → ℝ) (hp : ∀ i, ∑ b, p i b = 1) :
    ∑ γ, concatenateBlockLaw l hlen s t y p γ = 1 := by
  rw [concatenateBlockLaw, fiberMass_sum, ← Fintype.prod_sum]
  simp only [hp, Finset.prod_const_one]

theorem concatenateBlockLaw_exact {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n)
    (s t : Q) (y : Fin k → Q) :
    concatenateBlockLaw l hlen s t y
      (fun i => normalizeWeights (fun b : BridgeBlockPath Q l s t y i => edgePathWeight W b.val)) =
      normalizeWeights (boundaryRestrictedWeightAtLength W l hlen s t y) := by
  funext γ
  exact concatenated_independent_bridge_law_at_length W l hlen s t y γ

theorem concatenateBlockLaw_support {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n)
    (s t : Q) (y : Fin k → Q) (p : ∀ i, BridgeBlockPath Q l s t y i → ℝ)
    (hp : ∀ i b, 0 ≤ p i b) (hsupp : ∀ i b, 0 < p i b → 0 < edgePathWeight W b.val) :
    ∀ γ, 0 < concatenateBlockLaw l hlen s t y p γ →
      0 < boundaryRestrictedWeightAtLength W l hlen s t y γ := by
  classical
  intro γ hγ
  obtain ⟨b, hb, hprod⟩ := (fiberMass_pos_iff _ _
    (fun b : BoundaryBlocks Q l s t y => Finset.prod_nonneg (fun i _ => hp i (b i))) γ).mp hγ
  have hlocal (i : Fin (k + 1)) : 0 < edgePathWeight W (b i).val := by
    apply hsupp i (b i)
    exact lt_of_le_of_ne (hp i (b i))
      (Ne.symm (Finset.prod_ne_zero_iff.mp hprod.ne' i (Finset.mem_univ i)))
  rw [← hb, boundaryRestrictedWeightAtLength_eq,
    if_pos (concatenateBridgeBlocksAtLength_spec l hlen s t y b),
    concatenateBridgeBlocksAtLength_weight]
  exact Finset.prod_pos (fun i _ => hlocal i)

/-- Block errors add after actual concatenation. The assumptions describe
probability laws on the full Cartesian product of endpoint path spaces,
and every output retains the required boundaries and positive path weight. -/
theorem approximate_concatenated_bridges {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y)
    (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n) (s t : Q) (y : Fin k → Q)
    (hpart : ∀ i, 0 < bridgePartition W ((Fin.cons s y : Fin (k + 1) → Q) i)
      ((Fin.snoc y t : Fin (k + 1) → Q) i) (l i))
    (p : ∀ i, BridgeBlockPath Q l s t y i → ℝ)
    (hp : ∀ i b, 0 ≤ p i b) (hpsum : ∀ i, ∑ b, p i b = 1)
    (hsupp : ∀ i b, 0 < p i b → 0 < edgePathWeight W b.val)
    (δ : Fin (k + 1) → ℝ)
    (herror : ∀ i, tv (p i)
      (normalizeWeights (fun b : BridgeBlockPath Q l s t y i => edgePathWeight W b.val)) ≤ δ i) :
    (∀ γ, 0 ≤ concatenateBlockLaw l hlen s t y p γ) ∧
    (∑ γ, concatenateBlockLaw l hlen s t y p γ = 1) ∧
    (∀ γ, 0 < concatenateBlockLaw l hlen s t y p γ →
      0 < boundaryRestrictedWeightAtLength W l hlen s t y γ) ∧
    tv (concatenateBlockLaw l hlen s t y p)
      (normalizeWeights (boundaryRestrictedWeightAtLength W l hlen s t y)) ≤ ∑ i, δ i := by
  classical
  let K := fun i => normalizeWeights (fun b : BridgeBlockPath Q l s t y i => edgePathWeight W b.val)
  have hK : ∀ i b, 0 ≤ K i b := fun i => normalizeWeights_nonneg _
    (fun b => edgePathWeight_nonneg W hW b.val)
  have hKsum : ∀ i, ∑ b, K i b = 1 := by
    intro i
    apply normalizeWeights_sum
    rw [endpointPath_weight_sum]
    exact hpart i
  refine ⟨concatenateBlockLaw_nonneg l hlen s t y p hp,
    concatenateBlockLaw_sum l hlen s t y p hpsum,
    concatenateBlockLaw_support W l hlen s t y p hp hsupp, ?_⟩
  rw [← concatenateBlockLaw_exact W l hlen s t y]
  have hmap := tv_map_le (concatenateBridgeBlocksAtLength l hlen s t y)
    (fun b : BoundaryBlocks Q l s t y => ∏ i, p i (b i))
    (fun b : BoundaryBlocks Q l s t y => ∏ i, K i (b i))
  exact hmap.trans ((tv_finite_product_le_sum p K hp hK hpsum hKsum).trans
    (Finset.sum_le_sum (fun i _ => herror i)))

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SubprobabilityKernels
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

theorem normalizeWeights_sum_le_one {Ω : Type} [Fintype Ω] (w : Ω → ℝ)
    (hw : ∀ x, 0 ≤ w x) : (∑ x, normalizeWeights w x) ≤ 1 := by
  have hs : 0 ≤ ∑ x, w x := Finset.sum_nonneg (fun x _ => hw x)
  by_cases hz : (∑ x, w x) = 0
  · simp [normalizeWeights, hz]
  · exact (normalizeWeights_sum w (lt_of_le_of_ne hs (Ne.symm hz))).le



theorem mixtureLaw_sum_on_support {C Ω : Type} [Fintype C] [Fintype Ω]
    (p : C → ℝ) (K : C → Ω → ℝ) (hp : ∀ c, 0 ≤ p c)
    (hpsum : ∑ c, p c = 1) (hKsum : ∀ c, 0 < p c → ∑ x, K c x = 1) :
    ∑ x, mixtureLaw p K x = 1 := by
  unfold mixtureLaw
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have he (c : C) : p c * (∑ x, K c x) = p c := by
    by_cases hz : p c = 0
    · rw [hz, zero_mul]
    · rw [hKsum c (lt_of_le_of_ne (hp c) (Ne.symm hz)), mul_one]
  simp_rw [he]
  exact hpsum

/-- Mixing the same nonnegative weights changes TV by at most the weighted
conditional errors; no normalization is required for the kernels. -/
theorem tv_mixture_same_weights_le {C Ω : Type} [Fintype C] [Fintype Ω]
    (p : C → ℝ) (K L : C → Ω → ℝ) (hp : ∀ c, 0 ≤ p c) :
    tv (mixtureLaw p K) (mixtureLaw p L) ≤ ∑ c, p c * tv (K c) (L c) := by
  have hpoint (x : Ω) : |mixtureLaw p K x - mixtureLaw p L x| ≤
      ∑ c, p c * |K c x - L c x| := by
    unfold mixtureLaw
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ c, |p c * K c x - p c * L c x| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp_rw [← mul_sub, abs_mul, abs_of_nonneg (hp _)]
  calc
    _ ≤ (∑ x, ∑ c, p c * |K c x - L c x|) / 2 :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => hpoint x)) (by norm_num)
    _ = _ := by
      rw [Finset.sum_comm, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro c _
      rw [← Finset.mul_sum]
      exact mul_div_assoc _ _ _

/-- Even a subprobability kernel contracts TV. Zero-mass boundary fibers
can therefore use the identically zero normalized conditional kernel. -/
theorem tv_mixture_subprobability_le {C Ω : Type} [Fintype C] [Fintype Ω]
    (p q : C → ℝ) (K : C → Ω → ℝ)
    (hK : ∀ c x, 0 ≤ K c x) (hKsum : ∀ c, (∑ x, K c x) ≤ 1) :
    tv (mixtureLaw p K) (mixtureLaw q K) ≤ tv p q := by
  have hpoint (x : Ω) : |mixtureLaw p K x - mixtureLaw q K x| ≤
      ∑ c, |p c - q c| * K c x := by
    unfold mixtureLaw
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ c, |p c * K c x - q c * K c x| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp_rw [← sub_mul, abs_mul, abs_of_nonneg (hK _ _)]
  calc
    _ ≤ (∑ x, ∑ c, |p c - q c| * K c x) / 2 :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => hpoint x)) (by norm_num)
    _ = (∑ c, |p c - q c| * ∑ x, K c x) / 2 := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
    _ ≤ (∑ c, |p c - q c|) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply Finset.sum_le_sum
      intro c _
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hKsum c) (abs_nonneg (p c - q c))

theorem tv_mixture_error_on_support {C Ω : Type} [Fintype C] [Fintype Ω]
    (p q : C → ℝ) (K L : C → Ω → ℝ) (hp : ∀ c, 0 ≤ p c) (hpsum : ∑ c, p c = 1)
    (hL : ∀ c x, 0 ≤ L c x) (hLsum : ∀ c, (∑ x, L c x) ≤ 1)
    (δ η : ℝ) (hcat : tv p q ≤ δ)
    (hcond : ∀ c, 0 < p c → tv (K c) (L c) ≤ η) :
    tv (mixtureLaw p K) (mixtureLaw q L) ≤ δ + η := by
  have hlocal (c : C) : p c * tv (K c) (L c) ≤ p c * η := by
    by_cases hz : p c = 0
    · simp only [hz, zero_mul, le_refl]
    · exact mul_le_mul_of_nonneg_left (hcond c (lt_of_le_of_ne (hp c) (Ne.symm hz))) (hp c)
  have hsum : (∑ c, p c * tv (K c) (L c)) ≤ η := by
    calc
      _ ≤ ∑ c, p c * η := Finset.sum_le_sum (fun c _ => hlocal c)
      _ = η := by rw [← Finset.sum_mul, hpsum, one_mul]
  have h1 := (tv_mixture_same_weights_le p K L hp).trans hsum
  have h2 := (tv_mixture_subprobability_le p q L hL hLsum).trans hcat
  have htri := tv_triangle (mixtureLaw p K) (mixtureLaw p L) (mixtureLaw q L)
  linarith

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_BridgeBoundaryDisintegration
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

theorem boundaryRestrictedWeightAtLength_nonneg {Q : Type} [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y)
    (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n) (s t : Q) (y : Fin k → Q) :
    ∀ γ, 0 ≤ boundaryRestrictedWeightAtLength W l hlen s t y γ := by
  intro γ
  rw [boundaryRestrictedWeightAtLength_eq]
  split_ifs
  · exact edgePathWeight_nonneg W hW γ
  · exact le_rfl

theorem boundaryRestrictedWeightAtLength_sum {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n)
    (s t : Q) (y : Fin k → Q) :
    (∑ γ, boundaryRestrictedWeightAtLength W l hlen s t y γ) = bridgeBoundaryMass W l s t y := by
  subst n
  exact boundaryRestrictedWeight_sum W l s t y

/-- The conditional fiber of the actual boundary observation retains the
original endpoint constraints and full path weight. -/
theorem bridge_boundary_fiberWeight {Q : Type} [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n)
    (s t : Q) (y : Fin k → Q) :
    fiberWeight (bridgeBoundaryObservation l hlen) (bridgeWeight W s t n) y =
      boundaryRestrictedWeightAtLength W l hlen s t y := by
  classical
  funext γ
  rw [boundaryRestrictedWeightAtLength_eq]
  unfold fiberWeight bridgeWeight
  by_cases hobs : bridgeBoundaryObservation l hlen γ = y <;>
    by_cases hs : γ 0 = s <;> by_cases ht : γ (Fin.last n) = t <;> simp [hobs, hs, ht]

theorem bridge_boundary_fiberMass {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n)
    (s t : Q) :
    fiberMass (bridgeBoundaryObservation l hlen) (bridgeWeight W s t n) =
      bridgeBoundaryMass W l s t := by
  funext y
  unfold fiberMass
  rw [bridge_boundary_fiberWeight]
  exact boundaryRestrictedWeightAtLength_sum W l hlen s t y

theorem boundaryRestrictedWeightAtLength_positive_bridge {Q : Type} [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n)
    (s t : Q) (y : Fin k → Q) (γ : Fin (n + 1) → Q)
    (hγ : 0 < boundaryRestrictedWeightAtLength W l hlen s t y γ) :
    0 < bridgeWeight W s t n γ := by
  rw [← bridge_boundary_fiberWeight W l hlen s t y] at hγ
  unfold fiberWeight at hγ
  split_ifs at hγ
  · exact hγ
  · exact False.elim ((lt_irrefl 0) hγ)

/-- Draw the exact boundary law and then the exact boundary-conditioned
full path. This reproduces the entire n-step bridge law, including zero
boundary fibers whose normalized conditional law is identically zero. -/
theorem normalized_bridge_boundary_mixture {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y)
    (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n) (s t : Q)
    (hp : 0 < bridgePartition W s t n) :
    mixtureLaw (normalizeWeights (bridgeBoundaryMass W l s t))
      (fun y => normalizeWeights (boundaryRestrictedWeightAtLength W l hlen s t y)) =
      normalizeWeights (bridgeWeight W s t n) := by
  funext γ
  have h := normalized_weight_disintegration (bridgeBoundaryObservation l hlen)
    (bridgeWeight W s t n) (bridgeWeight_nonneg W hW s t n) hp γ
  rw [bridge_boundary_fiberMass W l hlen s t] at h
  simp_rw [bridge_boundary_fiberWeight W l hlen s t] at h
  exact h

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_RoundedBridgeBlocks
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

theorem endpointPath_card_bound {Q : Type} [Fintype Q] [DecidableEq Q] (s t : Q) (n : ℕ) :
    Fintype.card (EndpointPath Q s t n) ≤ Fintype.card Q ^ (n + 1) := by
  have h := Fintype.card_subtype_le (fun γ : Fin (n + 1) → Q => γ 0 = s ∧ γ (Fin.last n) = t)
  simpa only [Fintype.card_fun, Fintype.card_fin] using h

def bridgeRoundingSeed (q n : ℕ) (δ : ℝ) := roundingSeed (q ^ (n + 1)) δ





theorem logInv_nonneg_of_le_one (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1) : 0 ≤ logInv δ := by
  unfold logInv
  apply div_nonneg
  · apply Real.log_nonneg
    exact (le_div_iff₀ hδ).mpr (by simpa using hδle)
  · exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

theorem bridgeRoundingSeed_linear_bound (q n : ℕ) (hq : 0 < q) (δ : ℝ)
    (hδ : 0 < δ) (hδle : δ ≤ 1) :
    (bridgeRoundingSeed q n δ : ℝ) ≤ (n + 1 : ℕ) * (Real.log q / Real.log 2) + logInv δ + 1 := by
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr hq
  have hlq : 0 ≤ Real.log q / Real.log 2 := div_nonneg (Real.log_nonneg hq1)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have he : Real.log (q ^ (n + 1) : ℕ) / Real.log 2 =
      (n + 1 : ℕ) * (Real.log q / Real.log 2) := by
    rw [Nat.cast_pow, Real.log_pow]
    ring
  change (⌈Real.log (q ^ (n + 1) : ℕ) / Real.log 2 + logInv δ⌉₊ : ℝ) ≤ _
  rw [he]
  exact (Nat.ceil_lt_add_one (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hlq)
    (logInv_nonneg_of_le_one δ hδ hδle))).le

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ApproximateBoundaryBridges
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def boundaryBlockMixtureLaw {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n) (s t : Q)
    (a : (Fin k → Q) → ℝ) (p : ∀ (y : Fin k → Q) i, BridgeBlockPath Q l s t y i → ℝ) :
    (Fin (n + 1) → Q) → ℝ :=
  mixtureLaw a (fun y => concatenateBlockLaw l hlen s t y (p y))

/-- Internal bridge sampler assembly. First sample an approximate boundary
tuple and then independently sample all blocks conditional on that tuple.
Only tuples with positive sampling mass need normalized conditional laws.
The result stays inside the original positive bridge support, and boundary
and block errors add without a lower bound on any bridge probability. -/
theorem approximate_boundary_block_mixture {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y)
    (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n) (s t : Q)
    (hpart : 0 < bridgePartition W s t n)
    (a : (Fin k → Q) → ℝ) (ha : ∀ y, 0 ≤ a y) (hasum : ∑ y, a y = 1)
    (hasupp : ∀ y, 0 < a y → 0 < bridgeBoundaryMass W l s t y)
    (p : ∀ (y : Fin k → Q) i, BridgeBlockPath Q l s t y i → ℝ)
    (hp : ∀ y i b, 0 ≤ p y i b)
    (hpsum : ∀ y, 0 < a y → ∀ i, ∑ b, p y i b = 1)
    (hsupp : ∀ y i b, 0 < p y i b → 0 < edgePathWeight W b.val)
    (δ η : ℝ) (e : (Fin k → Q) → Fin (k + 1) → ℝ)
    (hboundary : tv a (normalizeWeights (bridgeBoundaryMass W l s t)) ≤ δ)
    (hblock : ∀ y, 0 < a y → ∀ i, tv (p y i)
      (normalizeWeights (fun b : BridgeBlockPath Q l s t y i => edgePathWeight W b.val)) ≤ e y i)
    (hbudget : ∀ y, 0 < a y → (∑ i, e y i) ≤ η) :
    (∀ γ, 0 ≤ boundaryBlockMixtureLaw l hlen s t a p γ) ∧
    (∑ γ, boundaryBlockMixtureLaw l hlen s t a p γ = 1) ∧
    (∀ γ, 0 < boundaryBlockMixtureLaw l hlen s t a p γ → 0 < bridgeWeight W s t n γ) ∧
    tv (boundaryBlockMixtureLaw l hlen s t a p)
      (normalizeWeights (bridgeWeight W s t n)) ≤ δ + η := by
  classical
  let L := fun y => concatenateBlockLaw l hlen s t y (p y)
  let K := fun y => normalizeWeights (boundaryRestrictedWeightAtLength W l hlen s t y)
  have hLn : ∀ y γ, 0 ≤ L y γ := fun y => concatenateBlockLaw_nonneg l hlen s t y (p y) (hp y)
  have hlocal (y : Fin k → Q) (hy : 0 < a y) :=
    approximate_concatenated_bridges W hW l hlen s t y
      ((bridgeBoundaryMass_pos_iff W hW l s t y).mp (hasupp y hy))
      (p y) (hp y) (hpsum y hy) (hsupp y) (e y) (hblock y hy)
  refine ⟨mixtureLaw_nonneg a L ha hLn,
    mixtureLaw_sum_on_support a L ha hasum (fun y hy => (hlocal y hy).2.1), ?_, ?_⟩
  · intro γ hγ
    obtain ⟨y, hy, hLγ⟩ := (mixtureLaw_pos_iff a L ha hLn γ).mp hγ
    exact boundaryRestrictedWeightAtLength_positive_bridge W l hlen s t y γ
      ((hlocal y hy).2.2.1 γ hLγ)
  · have hKn : ∀ y γ, 0 ≤ K y γ := fun y => normalizeWeights_nonneg _
      (boundaryRestrictedWeightAtLength_nonneg W hW l hlen s t y)
    have hKs : ∀ y, (∑ γ, K y γ) ≤ 1 := fun y => normalizeWeights_sum_le_one _
      (boundaryRestrictedWeightAtLength_nonneg W hW l hlen s t y)
    have ht := tv_mixture_error_on_support a (normalizeWeights (bridgeBoundaryMass W l s t)) L K
      ha hasum hKn hKs δ η hboundary (fun y hy => ((hlocal y hy).2.2.2).trans (hbudget y hy))
    have he := normalized_bridge_boundary_mixture W hW l hlen s t hpart
    change mixtureLaw (normalizeWeights (bridgeBoundaryMass W l s t)) K = _ at he
    rw [he] at ht
    exact ht

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_RoundedBridgeKernels
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def bridgeRoundingSize (q n : ℕ) (δ : ℝ) : ℕ :=
  bridgeRoundingSeed q n δ + ((n + 1) * q) *
    (q ^ (n + 1) * (2 * (bridgeRoundingSeed q n δ * (3 * bridgeRoundingSeed q n δ + 2) + 1) + 6) + 2)

/-- A concrete conditional block sampler, with its fair-bit function,
verified circuit, support, TV error, and resource certificates together. -/
structure RoundedBridgeModel {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (s t : Q) (n : ℕ) (δ : ℝ) where
  sample : Bits (bridgeRoundingSeed (Fintype.card Q) n δ) → EndpointPath Q s t n
  circuit : Circuit (Fin (n + 1) × Q)
  randomBits_eq : circuit.randomBits = bridgeRoundingSeed (Fintype.card Q) n δ
  eval_eq : ∀ seed i x, circuit.eval (fun j => seed (Fin.cast randomBits_eq j)) (i, x) =
    decide ((sample seed).val i = x)
  sample_positive : ∀ seed, 0 < edgePathWeight W (sample seed).val
  error : tv (finiteSeedLaw sample)
    (normalizeWeights (fun γ : EndpointPath Q s t n => edgePathWeight W γ.val)) ≤ δ
  depth_le : circuit.depth ≤ 6
  size_le : circuit.size ≤ bridgeRoundingSize (Fintype.card Q) n δ





















end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_BridgeSeedBudgets
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

theorem roundingSeed_upper_of_card_le (M q : ℕ) (hM : 0 < M) (hMq : M ≤ q)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1) :
    (roundingSeed M δ : ℝ) ≤ Real.log q / Real.log 2 + logInv δ + 1 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hM1 : (1 : ℝ) ≤ M := Nat.one_le_cast.mpr hM
  have hn : 0 ≤ Real.log M / Real.log 2 + logInv δ :=
    add_nonneg (div_nonneg (Real.log_nonneg hM1) hlog2.le) (logInv_nonneg_of_le_one δ hδ hδle)
  have hlog : Real.log M / Real.log 2 ≤ Real.log q / Real.log 2 :=
    div_le_div_of_nonneg_right (Real.log_le_log (Nat.cast_pos.mpr hM) (Nat.cast_le.mpr hMq)) hlog2.le
  exact (Nat.ceil_lt_add_one hn).le.trans (by linarith)











end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_UniformSourceComposition
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def uniformSourceLaw {U Ω : Type} [Fintype U] [DecidableEq Ω] (f : U → Ω) : Ω → ℝ :=
  fun x => (Fintype.card {u : U // f u = x} : ℝ) / Fintype.card U

theorem uniformSourceLaw_bits {Ω : Type} [Fintype Ω] [DecidableEq Ω] {m : ℕ}
    (f : Bits m → Ω) : uniformSourceLaw f = finiteSeedLaw f := by
  funext x
  simp only [uniformSourceLaw, finiteSeedLaw, Bits, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat]

theorem uniformSourceLaw_reindex {U V Ω : Type} [Fintype U] [Fintype V] [DecidableEq Ω]
    (e : U ≃ V) (f : V → Ω) : uniformSourceLaw (f ∘ e) = uniformSourceLaw f := by
  funext x
  let ex : {u : U // (f ∘ e) u = x} ≃ {v : V // f v = x} := {
    toFun := fun u => ⟨e u.val, u.property⟩
    invFun := fun v => ⟨e.symm v.val, by simpa only [Function.comp_apply, e.apply_symm_apply] using v.property⟩
    left_inv := fun u => Subtype.ext (e.symm_apply_apply u.val)
    right_inv := fun v => Subtype.ext (e.apply_symm_apply v.val) }
  unfold uniformSourceLaw
  rw [Fintype.card_congr ex, Fintype.card_congr e]

/-- Independent finite sources and coordinatewise maps give precisely the
product of their output laws, including dependent source/output spaces. -/
theorem uniformSourceLaw_pi {I : Type} [Fintype I] [DecidableEq I] {U Ω : I → Type}
    [∀ i, Fintype (U i)] [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (f : ∀ i, U i → Ω i) (x : ∀ i, Ω i) :
    uniformSourceLaw (fun u : ∀ i, U i => fun i => f i (u i)) x =
      ∏ i, uniformSourceLaw (f i) (x i) := by
  classical
  let e : {u : ∀ i, U i // (fun i => f i (u i)) = x} ≃
      ((i : I) → {u : U i // f i u = x i}) := {
    toFun := fun u i => ⟨u.val i, congrFun u.property i⟩
    invFun := fun u => ⟨(fun i => (u i).val), funext (fun i => (u i).property)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  unfold uniformSourceLaw
  rw [Fintype.card_congr e]
  simp only [Fintype.card_pi, Nat.cast_prod, Finset.prod_div_distrib]

theorem uniformSourceLaw_comp {U Ω Ξ : Type} [Fintype U] [Fintype Ω]
    [DecidableEq Ω] [DecidableEq Ξ] (f : U → Ω) (g : Ω → Ξ) :
    uniformSourceLaw (g ∘ f) = fiberMass g (uniformSourceLaw f) := by
  funext z
  exact finite_sampler_projection f g (Fintype.card U) (uniformSourceLaw f) (fun _ => rfl) z

/-- The second source is reused across mutually exclusive branches. It
remains independent of the first source and realizes the selected kernel. -/
theorem uniformSourceLaw_joint {U V C Ω : Type} [Fintype U] [Fintype V]
    [DecidableEq C] [DecidableEq Ω] (f : U → C) (g : C → V → Ω) (c : C) (x : Ω) :
    uniformSourceLaw (fun uv : U × V => (f uv.1, g (f uv.1) uv.2)) (c, x) =
      uniformSourceLaw f c * uniformSourceLaw (g c) x := by
  classical
  let e : {uv : U × V // (f uv.1, g (f uv.1) uv.2) = (c, x)} ≃
      {u : U // f u = c} × {v : V // g c v = x} := {
    toFun := fun uv => (⟨uv.val.1, congrArg Prod.fst uv.property⟩,
      ⟨uv.val.2, by
        have hc := congrArg Prod.fst uv.property
        have hx := congrArg Prod.snd uv.property
        change f uv.val.1 = c at hc
        change g (f uv.val.1) uv.val.2 = x at hx
        simpa only [hc] using hx⟩)
    invFun := fun uv => ⟨(uv.1.val, uv.2.val), by simp only [uv.1.property, uv.2.property]⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  unfold uniformSourceLaw
  rw [Fintype.card_congr e]
  simp only [Fintype.card_prod, Nat.cast_mul]
  exact mul_div_mul_comm _ _ _ _

theorem uniformSourceLaw_sequential {U V C Ω : Type} [Fintype U] [Fintype V]
    [Fintype C] [Fintype Ω] [DecidableEq C] [DecidableEq Ω]
    (f : U → C) (g : C → V → Ω) :
    uniformSourceLaw (fun uv : U × V => g (f uv.1) uv.2) =
      mixtureLaw (uniformSourceLaw f) (fun c => uniformSourceLaw (g c)) := by
  let joint := fun uv : U × V => (f uv.1, g (f uv.1) uv.2)
  have hj : uniformSourceLaw joint = fun z : C × Ω =>
      uniformSourceLaw f z.1 * uniformSourceLaw (g z.1) z.2 := by
    funext z
    exact uniformSourceLaw_joint f g z.1 z.2
  have hm := uniformSourceLaw_comp joint Prod.snd
  rw [hj] at hm
  funext x
  apply (congrFun hm x).trans
  simpa only [fiberMass, fiberWeight] using
    mixtureLaw_as_pushforward (uniformSourceLaw f) (fun c => uniformSourceLaw (g c)) x

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_DisjointSeedSlots
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- This bijection is on bit indices, not on bitstrings: each local input
is a fixed wire into the shared seed, with no computed transformation. -/
def seedIndexEquiv {I : Type} [Fintype I] [DecidableEq I] (m : I → ℕ) :
    (Σ i, Fin (m i)) ≃ Fin (∑ i, m i) :=
  (Fintype.equivFin (Σ i, Fin (m i))).trans (finCongr (by simp only [Fintype.card_sigma, Fintype.card_fin]))

def seedSlot {I : Type} [Fintype I] [DecidableEq I] (m : I → ℕ) (i : I) :
    Fin (m i) → Fin (∑ j, m j) := fun j => seedIndexEquiv m ⟨i, j⟩



def seedSlotsEquiv {I : Type} [Fintype I] [DecidableEq I] (m : I → ℕ) :
    Bits (∑ i, m i) ≃ ((i : I) → Bits (m i)) where
  toFun seed i j := seed (seedSlot m i j)
  invFun seeds j := seeds ((seedIndexEquiv m).symm j).1 ((seedIndexEquiv m).symm j).2
  left_inv seed := by
    funext j
    change seed (seedIndexEquiv m ((seedIndexEquiv m).symm j)) = seed j
    rw [Equiv.apply_symm_apply]
  right_inv seeds := by
    funext i j
    change seeds ((seedIndexEquiv m).symm (seedIndexEquiv m ⟨i, j⟩)).1
      ((seedIndexEquiv m).symm (seedIndexEquiv m ⟨i, j⟩)).2 = seeds i j
    rw [Equiv.symm_apply_apply]

def parallelSeedSample {I : Type} [Fintype I] [DecidableEq I] {Ω : I → Type}
    (m : I → ℕ) (f : ∀ i, Bits (m i) → Ω i) : Bits (∑ i, m i) → ∀ i, Ω i :=
  fun seed i => f i ((seedSlotsEquiv m seed) i)

/-- Disjoint fixed seed slots realize the exact independent product law,
using the sum of the local bit counts, even for an empty family. -/
theorem parallelSeedSample_law {I : Type} [Fintype I] [DecidableEq I] {Ω : I → Type}
    [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (m : I → ℕ) (f : ∀ i, Bits (m i) → Ω i) (x : ∀ i, Ω i) :
    finiteSeedLaw (parallelSeedSample m f) x = ∏ i, finiteSeedLaw (f i) (x i) := by
  rw [← uniformSourceLaw_bits]
  have he := uniformSourceLaw_reindex (seedSlotsEquiv m) (fun u => fun i => f i (u i))
  change uniformSourceLaw (parallelSeedSample m f) = _ at he
  rw [congrFun he x, uniformSourceLaw_pi]
  simp only [uniformSourceLaw_bits]

def seedPairEquiv (m n : ℕ) : Bits (m + n) ≃ Bits m × Bits n where
  toFun seed := (fun i => seed (Fin.castAdd n i), fun j => seed (Fin.natAdd m j))
  invFun seeds := Fin.append seeds.1 seeds.2
  left_inv seed := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
  right_inv seeds := by
    apply Prod.ext <;> funext j
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]

def sequentialSeedSample {C Ω : Type} {m n : ℕ}
    (f : Bits m → C) (g : C → Bits n → Ω) : Bits (m + n) → Ω :=
  fun seed => g (f (seedPairEquiv m n seed).1) (seedPairEquiv m n seed).2

/-- A category seed followed by one shared conditional seed realizes the
exact mixture. The conditional budget is paid once, not once per category. -/
theorem sequentialSeedSample_law {C Ω : Type} [Fintype C] [Fintype Ω] [DecidableEq C] [DecidableEq Ω]
    {m n : ℕ} (f : Bits m → C) (g : C → Bits n → Ω) :
    finiteSeedLaw (sequentialSeedSample f g) =
      mixtureLaw (finiteSeedLaw f) (fun c => finiteSeedLaw (g c)) := by
  rw [← uniformSourceLaw_bits]
  have he := uniformSourceLaw_reindex (seedPairEquiv m n) (fun uv => g (f uv.1) uv.2)
  change uniformSourceLaw (sequentialSeedSample f g) = _ at he
  rw [he, uniformSourceLaw_sequential]
  simp only [uniformSourceLaw_bits]

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_EmbeddedProductLaws
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

theorem tv_symm {Ω : Type} [Fintype Ω] (p q : Ω → ℝ) : tv p q = tv q p := by
  unfold tv
  simp only [abs_sub_comm]

def embeddedProductLaw {A Q : Type} [Fintype A] [DecidableEq Q] {k : ℕ}
    (f : A → Q) (p : Fin k → A → ℝ) : (Fin k → Q) → ℝ :=
  fiberMass (fun z : Fin k → A => fun i => f (z i)) (fun z => ∏ i, p i (z i))

theorem embeddedProductLaw_nonneg {A Q : Type} [Fintype A] [DecidableEq Q] {k : ℕ}
    (f : A → Q) (p : Fin k → A → ℝ) (hp : ∀ i x, 0 ≤ p i x) :
    ∀ y, 0 ≤ embeddedProductLaw f p y :=
  fiberMass_nonneg _ _ (fun z => Finset.prod_nonneg (fun i _ => hp i (z i)))

theorem embeddedProductLaw_sum {A Q : Type} [Fintype A] [Fintype Q] [DecidableEq Q] {k : ℕ}
    (f : A → Q) (p : Fin k → A → ℝ) (hp : ∀ i, ∑ x, p i x = 1) :
    ∑ y, embeddedProductLaw f p y = 1 := by
  rw [embeddedProductLaw, fiberMass_sum, ← Fintype.prod_sum]
  simp only [hp, Finset.prod_const_one]

theorem embeddedProductLaw_positive_tuple {A Q : Type} [Fintype A] [DecidableEq Q] {k : ℕ}
    (f : A → Q) (p : Fin k → A → ℝ) (hp : ∀ i x, 0 ≤ p i x) (y : Fin k → Q)
    (hy : 0 < embeddedProductLaw f p y) :
    ∃ z : Fin k → A, (fun i => f (z i)) = y ∧ ∀ i, 0 < p i (z i) := by
  classical
  obtain ⟨z, he, hz⟩ := (fiberMass_pos_iff _ _
    (fun z : Fin k → A => Finset.prod_nonneg (fun i _ => hp i (z i))) y).mp hy
  refine ⟨z, he, fun i => ?_⟩
  exact lt_of_le_of_ne (hp i (z i))
    (Ne.symm (Finset.prod_ne_zero_iff.mp hz.ne' i (Finset.mem_univ i)))

theorem tv_embeddedProductLaw_le {A Q : Type} [Fintype A] [Fintype Q] [DecidableEq Q] {k : ℕ}
    (f : A → Q) (p q : Fin k → A → ℝ)
    (hp : ∀ i x, 0 ≤ p i x) (hq : ∀ i x, 0 ≤ q i x)
    (hpsum : ∀ i, ∑ x, p i x = 1) (hqsum : ∀ i, ∑ x, q i x = 1) :
    tv (embeddedProductLaw f p) (embeddedProductLaw f q) ≤ ∑ i, tv (p i) (q i) := by
  classical
  exact (tv_map_le (fun z : Fin k → A => fun i => f (z i))
    (fun z => ∏ i, p i (z i)) (fun z => ∏ i, q i (z i))).trans
    (tv_finite_product_le_sum p q hp hq hpsum hqsum)

theorem tv_rounded_embeddedProductLaw {A Q : Type} [Fintype A] [DecidableEq A]
    [Fintype Q] [DecidableEq Q] {k m : ℕ} (embed : A → Q) (f : Bits m → A)
    (ν : A → ℝ) (hν : ∀ x, 0 ≤ ν x) (hνsum : ∑ x, ν x = 1)
    (δ : ℝ) (herror : tv (finiteSeedLaw f) ν ≤ δ) :
    tv (embeddedProductLaw (k := k) embed (fun _ => finiteSeedLaw f))
      (embeddedProductLaw embed (fun _ => ν)) ≤ k * δ := by
  apply (tv_embeddedProductLaw_le embed _ _ (fun _ => finiteSeedLaw_nonneg f)
    (fun _ => hν) (fun _ => finiteSeedLaw_sum f) (fun _ => hνsum)).trans
  calc
    _ ≤ ∑ _i : Fin k, δ := Finset.sum_le_sum (fun _ _ => herror)
    _ = _ := by simp

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_RepeatedSeedSamples
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

theorem finiteSeedLaw_cast {Ω : Type} [Fintype Ω] [DecidableEq Ω] {m n : ℕ}
    (h : m = n) (f : Bits m → Ω) :
    finiteSeedLaw (fun seed : Bits n => f (fun i => seed (Fin.cast h i))) = finiteSeedLaw f := by
  subst n
  rfl

/-- Independent repeated draws read disjoint fixed wires, with exactly k*m bits. -/
def repeatedSeedSample {A : Type} {m : ℕ} (k : ℕ) (f : Bits m → A) :
    Bits (k * m) → (Fin k → A) :=
  fun seed => parallelSeedSample (fun _ : Fin k => m) (fun _ => f)
    (fun j => seed (Fin.cast (by simp) j))

theorem repeatedSeedSample_law {A : Type} [Fintype A] [DecidableEq A] {m : ℕ}
    (k : ℕ) (f : Bits m → A) :
    finiteSeedLaw (repeatedSeedSample k f) = fun z => ∏ i, finiteSeedLaw f (z i) := by
  unfold repeatedSeedSample
  rw [finiteSeedLaw_cast]
  funext z
  exact parallelSeedSample_law _ _ z

def embeddedRepeatedSeedSample {A Q : Type} {m : ℕ} (k : ℕ)
    (embed : A → Q) (f : Bits m → A) : Bits (k * m) → (Fin k → Q) :=
  (fun z : Fin k → A => fun i => embed (z i)) ∘ repeatedSeedSample k f

theorem embeddedRepeatedSeedSample_law {A Q : Type} [Fintype A] [DecidableEq A]
    [Fintype Q] [DecidableEq Q] {m : ℕ} (k : ℕ) (embed : A → Q) (f : Bits m → A) :
    finiteSeedLaw (embeddedRepeatedSeedSample k embed f) =
      embeddedProductLaw embed (fun _ => finiteSeedLaw f) := by
  rw [embeddedRepeatedSeedSample, finiteSeedLaw_map, repeatedSeedSample_law]
  rfl

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ClassBoundaryWeights
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

theorem boundaryWeight_supported {Q : Type} {k : ℕ} (R : Q → Prop)
    (s : Q) (hs : R s) (T : Fin k → Q → Q → ℝ) (tail : Q → ℝ)
    (hclosed : ∀ i x z, R x → ¬ R z → T i x z = 0)
    (y : Fin k → Q) (hy : boundaryWeight s T tail y ≠ 0) : ∀ i, R (y i) := by
  induction k generalizing s with
  | zero => intro i; exact Fin.elim0 i
  | succ k ih =>
    rw [boundaryWeight_head] at hy
    have hs' : R (y 0) := by
      by_contra h
      exact (left_ne_zero_of_mul hy) (hclosed 0 s (y 0) hs h)
    have ht := ih (y 0) hs' (Fin.tail T)
      (fun i x z hx hz => hclosed i.succ x z hx hz) (Fin.tail y) (right_ne_zero_of_mul hy)
    intro i
    exact Fin.cases hs' ht i

theorem boundaryWeight_map {A Q : Type} {k : ℕ} (f : A → Q)
    (s : A) (T : Fin k → Q → Q → ℝ) (tail : Q → ℝ) (y : Fin k → A) :
    boundaryWeight (f s) T tail (fun i => f (y i)) =
      boundaryWeight s (fun i x z => T i (f x) (f z)) (fun x => tail (f x)) y := by
  have hc (i : Fin (k + 1)) :
      (Fin.cons (f s) (fun j => f (y j)) : Fin (k + 1) → Q) i =
        f ((Fin.cons s y : Fin (k + 1) → A) i) := by
    cases i using Fin.cases <;> simp
  simp only [boundaryWeight, hc]

theorem subtype_tuple_injective {Q : Type} {k : ℕ} (R : Q → Prop) :
    Function.Injective (fun y : Fin k → {x // R x} => fun i => (y i).val) := by
  intro y z h
  funext i
  exact Subtype.ext (congrFun h i)

theorem supported_boundary_weight_zero {Q : Type} {k : ℕ} (R : Q → Prop)
    (s : Q) (hs : R s) (T : Fin k → Q → Q → ℝ) (tail : Q → ℝ)
    (hclosed : ∀ i x z, R x → ¬ R z → T i x z = 0) (y : Fin k → Q)
    (hy : ¬ ∃ z : Fin k → {x // R x}, (fun i => (z i).val) = y) :
    boundaryWeight s T tail y = 0 := by
  by_contra hn
  have h := boundaryWeight_supported R s hs T tail hclosed y hn
  exact hy ⟨fun i => ⟨y i, h i⟩, rfl⟩



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SCCMatrixRestriction
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

abbrev SCCState {Q : Type} [Fintype Q] (W : Matrix Q Q ℝ) (s : Q) :=
  {x : Q // graphComponent (fun i j => 0 < W i j) x =
    graphComponent (fun i j => 0 < W i j) s}

def sccMatrix {Q : Type} [Fintype Q] (W : Matrix Q Q ℝ) (s : Q) :
    Matrix (SCCState W s) (SCCState W s) ℝ := fun x y => W x.val y.val

theorem scc_bridgeWeight_embed {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (s : Q) (x y : SCCState W s) (n : ℕ)
    (γ : Fin (n + 1) → SCCState W s) :
    bridgeWeight (fun i j => sccMatrix W s i j) x y n γ =
      bridgeWeight (fun i j => W i j) x.val y.val n (fun i => (γ i).val) := by
  have hx : γ 0 = x ↔ (γ 0).val = x.val := Subtype.ext_iff
  have hy : γ (Fin.last n) = y ↔ (γ (Fin.last n)).val = y.val := Subtype.ext_iff
  simp only [bridgeWeight, hx, hy, edgePathWeight, finitePathWeight, sccMatrix]

theorem scc_bridgeWeight_supported {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j) (s : Q)
    (x y : SCCState W s) (n : ℕ) (γ : Fin (n + 1) → Q)
    (hγ : ¬ ∃ z : Fin (n + 1) → SCCState W s, (fun i => (z i).val) = γ) :
    bridgeWeight (fun i j => W i j) x.val y.val n γ = 0 := by
  apply bridgeWeight_zero_outside_component (fun i j => W i j) hW x.val y.val
    (x.property.trans y.property.symm) n γ
  intro hin
  apply hγ
  exact ⟨fun i => ⟨γ i, (hin i).trans x.property⟩, rfl⟩

/-- The restriction uses an arbitrary representative s and arbitrary
endpoints in its actual SCC. It preserves the full bridge partition. -/
theorem scc_bridgePartition {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j) (s : Q)
    (x y : SCCState W s) (n : ℕ) :
    bridgePartition (fun i j => sccMatrix W s i j) x y n =
      bridgePartition (fun i j => W i j) x.val y.val n := by
  classical
  change (∑ γ, bridgeWeight (fun i j => sccMatrix W s i j) x y n γ) = _
  simp_rw [scc_bridgeWeight_embed]
  exact embedded_weight_sum _ (subtype_tuple_injective _)
    (bridgeWeight (fun i j => W i j) x.val y.val n)
    (scc_bridgeWeight_supported W hW s x y n)

theorem sccMatrix_power {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j) (s : Q)
    (n : ℕ) (x y : SCCState W s) :
    (sccMatrix W s ^ n) x y = (W ^ n) x.val y.val := by
  rw [← bridgePartition_eq_matrix_power (sccMatrix W s), scc_bridgePartition W hW,
    bridgePartition_eq_matrix_power W]

/-- The normalized restricted bridge pushes forward to exactly the actual
ambient full-path bridge law. This is an equality of the complete laws. -/
theorem normalized_scc_bridge_law {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j) (s : Q)
    (x y : SCCState W s) (n : ℕ) (γ : Fin (n + 1) → Q) :
    (∑ z : Fin (n + 1) → SCCState W s, if (fun i => (z i).val) = γ then
      normalizeWeights (bridgeWeight (fun i j => sccMatrix W s i j) x y n) z else 0) =
      normalizeWeights (bridgeWeight (fun i j => W i j) x.val y.val n) γ := by
  classical
  have he : (fun z : Fin (n + 1) → SCCState W s =>
      bridgeWeight (fun i j => W i j) x.val y.val n (fun i => (z i).val)) =
      bridgeWeight (fun i j => sccMatrix W s i j) x y n := by
    funext z
    exact (scc_bridgeWeight_embed W s x y n z).symm
  have h := embedded_normalized_weights _ (subtype_tuple_injective _)
    (bridgeWeight (fun i j => W i j) x.val y.val n)
    (scc_bridgeWeight_supported W hW s x y n) γ
  rw [he] at h
  exact h

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_FiniteMonoidPower
section
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



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_WeightedIdempotentSupport
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

def matrixSupport {Q : Type} (W : Matrix Q Q ℝ) : WalkRelation Q :=
  {xy | 0 < W xy.1 xy.2}

theorem matrixSupport_mul {Q : Type} [Fintype Q]
    (W V : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j) (hV : ∀ i j, 0 ≤ V i j) :
    matrixSupport (W * V) = matrixSupport W * matrixSupport V := by
  apply Set.ext
  intro p
  change 0 < (W * V) p.1 p.2 ↔ ∃ j, 0 < W p.1 j ∧ 0 < V j p.2
  rw [Matrix.mul_apply, Finset.sum_pos_iff_of_nonneg
    (fun j _ => mul_nonneg (hW p.1 j) (hV j p.2))]
  simp only [Finset.mem_univ, true_and]
  apply exists_congr
  intro j
  constructor
  · intro hp
    rcases mul_pos_iff.mp hp with h | h
    · exact h
    · exact False.elim ((not_lt_of_ge (hW p.1 j)) h.1)
  · rintro ⟨ha, hb⟩
    exact mul_pos ha hb

theorem matrixSupport_one {Q : Type} [DecidableEq Q] :
    matrixSupport (1 : Matrix Q Q ℝ) = 1 := by
  apply Set.ext
  intro p
  change 0 < (1 : Matrix Q Q ℝ) p.1 p.2 ↔ p.1 = p.2
  by_cases h : p.1 = p.2 <;> simp [Matrix.one_apply, h]

theorem matrixSupport_power {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j) (n : ℕ) :
    matrixSupport (W ^ n) = matrixSupport W ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using (matrixSupport_one (Q := Q))
  | succ n ih =>
    rw [pow_succ, matrixSupport_mul _ _ (Matrix.pow_apply_nonneg hW n) hW, ih, pow_succ]

/-- Every finite nonnegative weighted kernel has a positive block exponent
whose actual support is idempotent. This supplies a common block multiple
without assuming aperiodicity or identifying a minimal period. -/
theorem exists_idempotent_matrix_support {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j) :
    ∃ a : ℕ, 0 < a ∧ ∀ x y,
      (∃ z, 0 < (W ^ a) x z ∧ 0 < (W ^ a) z y) ↔ 0 < (W ^ a) x y := by
  obtain ⟨a, ha, he⟩ := exists_positive_idempotent_power (matrixSupport W)
  refine ⟨a, ha, ?_⟩
  have hrel : matrixSupport (W ^ a) * matrixSupport (W ^ a) = matrixSupport (W ^ a) := by
    rw [matrixSupport_power W hW, he]
  intro x y
  change ((matrixSupport (W ^ a)) * matrixSupport (W ^ a)).holds x y ↔
    (matrixSupport (W ^ a)).holds x y
  rw [hrel]

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_StationaryRecurrentSupport
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

/-- A closed set cannot have a positive incoming edge when every state
has strictly positive stationary weight. This is a finite mass-balance proof. -/
theorem stationary_closed_no_entry {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Q → Q → ℝ) (hP : ∀ x y, 0 ≤ P x y) (π : Q → ℝ) (hπ : ∀ x, 0 < π x)
    (hstat : ∀ y, ∑ x, π x * P x y = π y) (S : Finset Q)
    (hstay : ∀ x ∈ S, ∑ y ∈ S, P x y = 1)
    (x y : Q) (hx : x ∉ S) (hy : y ∈ S) : P x y = 0 := by
  apply le_antisymm _ (hP x y)
  apply le_of_not_gt
  intro hp
  have hle (i : Q) : (if i ∈ S then π i else 0) ≤ ∑ j ∈ S, π i * P i j := by
    by_cases hi : i ∈ S
    · rw [if_pos hi, ← Finset.mul_sum, hstay i hi, mul_one]
    · rw [if_neg hi]
      exact Finset.sum_nonneg (fun j _ => mul_nonneg (hπ i).le (hP i j))
  have hstrict : (∑ i, if i ∈ S then π i else 0) < ∑ i, ∑ j ∈ S, π i * P i j := by
    apply Finset.sum_lt_sum (fun i _ => hle i)
    refine ⟨x, Finset.mem_univ x, ?_⟩
    rw [if_neg hx]
    exact (mul_pos (hπ x) hp).trans_le
      (Finset.single_le_sum (fun j _ => mul_nonneg (hπ x).le (hP x j)) hy)
  have hL : (∑ i, if i ∈ S then π i else 0) = ∑ i ∈ S, π i := by simp
  have hR : (∑ i, ∑ j ∈ S, π i * P i j) = ∑ j ∈ S, π j := by
    rw [Finset.sum_comm]
    simp_rw [hstat]
  rw [hL, hR] at hstrict
  exact (lt_irrefl _) hstrict

/-- Every positive transition lies on a directed cycle when a finite
stochastic kernel has a strictly positive stationary law. -/
theorem stationary_support_returns {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Q → Q → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1)
    (π : Q → ℝ) (hπ : ∀ x, 0 < π x) (hstat : ∀ y, ∑ x, π x * P x y = π y)
    (x y : Q) (hxy : 0 < P x y) : Relation.ReflTransGen (fun i j => 0 < P i j) y x := by
  classical
  let R := fun i j => 0 < P i j
  let S := graphComponent R y
  have hstay : ∀ i ∈ S, ∑ j ∈ S, P i j = 1 := by
    intro i hi
    have he : (∑ j ∈ S, P i j) = ∑ j, P i j := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro j _ hj
      apply le_antisymm _ (hP i j)
      apply le_of_not_gt
      intro hp
      apply hj
      exact (mem_graphComponent R y j).mpr
        (((mem_graphComponent R y i).mp hi).trans (.single hp))
    rw [he, hrows]
  apply (mem_graphComponent R y x).mp
  by_contra hx
  have hz := stationary_closed_no_entry P hP π hπ hstat S hstay x y hx
    (graphComponent_self R y)
  exact hxy.ne' hz

theorem transitive_reachable_eq_or {Q : Type} (R : Q → Q → Prop)
    (htrans : ∀ x y z, R x y → R y z → R x z) {x y : Q}
    (h : Relation.ReflTransGen R x y) : x = y ∨ R x y := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail b c hab hbc ih =>
    rcases ih with rfl | hab
    · exact Or.inr hbc
    · exact Or.inr (htrans _ _ _ hab hbc)

/-- Once the support is transitive, positive stationary weights rule out
all one-way or transient components. The support is an equivalence relation
with a positive diagonal, hence each class has a strictly positive kernel. -/
theorem stationary_transitive_support_equivalence {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Q → Q → ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1)
    (π : Q → ℝ) (hπ : ∀ x, 0 < π x) (hstat : ∀ y, ∑ x, π x * P x y = π y)
    (htrans : ∀ x y z, 0 < P x y → 0 < P y z → 0 < P x z) :
    Equivalence (fun x y => 0 < P x y) := by
  have hsym : ∀ x y, 0 < P x y → 0 < P y x := by
    intro x y hp
    have hr := stationary_support_returns P hP hrows π hπ hstat x y hp
    rcases transitive_reachable_eq_or _ htrans hr with he | he
    · simpa only [he] using hp
    · exact he
  refine ⟨?_, fun h => hsym _ _ h, fun h1 h2 => htrans _ _ _ h1 h2⟩
  intro x
  have hp : 0 < ∑ y, P x y := by rw [hrows]; norm_num
  obtain ⟨y, _, hxy⟩ := (Finset.sum_pos_iff_of_nonneg (fun y _ => hP x y)).mp hp
  exact htrans x y x hxy (hsym x y hxy)

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_RecurrentPowerClasses
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

theorem stochastic_matrix_power_rows {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hrows : ∀ x, ∑ y, P x y = 1) (n : ℕ) :
    ∀ x, ∑ y, (P ^ n) x y = 1 := by
  induction n with
  | zero => intro x; simp [Matrix.one_apply]
  | succ n ih =>
    intro x
    simp only [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hrows, mul_one]
    exact ih x

theorem stationary_matrix_power {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (π : Q → ℝ) (hstat : ∀ y, ∑ x, π x * P x y = π y)
    (n : ℕ) : ∀ y, ∑ x, π x * (P ^ n) x y = π y := by
  induction n with
  | zero => intro y; simp [Matrix.one_apply]
  | succ n ih =>
    intro y
    simp only [pow_succ, Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [← mul_assoc, ← Finset.sum_mul, ih]
    exact hstat y

theorem recurrent_idempotent_power {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1)
    (π : Q → ℝ) (hπ : ∀ x, 0 < π x) (hstat : ∀ y, ∑ x, π x * P x y = π y) :
    ∃ a : ℕ, 0 < a ∧ Equivalence (fun x y => 0 < (P ^ a) x y) := by
  obtain ⟨a, ha, he⟩ := exists_idempotent_matrix_support P hP
  refine ⟨a, ha, ?_⟩
  apply stationary_transitive_support_equivalence (fun x y => (P ^ a) x y)
    (Matrix.pow_apply_nonneg hP a) (stochastic_matrix_power_rows P hrows a) π hπ
    (stationary_matrix_power P π hstat a)
  intro x y z hxy hyz
  exact (he x z).mp ⟨y, hxy, hyz⟩

abbrev PositiveSupportClass {Q : Type} (P : Matrix Q Q ℝ) (s : Q) :=
  {x : Q // 0 < P s x}

def supportClassMatrix {Q : Type} (P : Matrix Q Q ℝ) (s : Q) :
    Matrix (PositiveSupportClass P s) (PositiveSupportClass P s) ℝ :=
  fun x y => P x.val y.val

theorem supportClassMatrix_pos {Q : Type} (P : Matrix Q Q ℝ)
    (he : Equivalence (fun x y => 0 < P x y)) (s : Q) :
    ∀ x y, 0 < supportClassMatrix P s x y := by
  intro x y
  exact he.trans (he.symm x.property) y.property

theorem supportClassMatrix_rows {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1)
    (he : Equivalence (fun x y => 0 < P x y)) (s : Q) :
    ∀ x, ∑ y, supportClassMatrix P s x y = 1 := by
  classical
  intro x
  change (∑ y : PositiveSupportClass P s, P x.val y.val) = 1
  rw [← Finset.sum_subtype (Finset.univ.filter (fun y => 0 < P s y)) (by simp)]
  rw [Finset.sum_filter]
  have hterm (y : Q) : (if 0 < P s y then P x.val y else 0) = P x.val y := by
    by_cases hy : 0 < P s y
    · rw [if_pos hy]
    · have hz : P x.val y = 0 := by
        apply le_antisymm _ (hP _ _)
        exact le_of_not_gt (fun hp => hy (he.trans x.property hp))
      rw [if_neg hy, hz]
  simp_rw [hterm]
  exact hrows x.val

/-- Every finite stochastic matrix with a positive stationary law admits
a fixed positive block exponent for which every support class is a closed,
strictly positive stochastic kernel with geometric relative convergence.
No aperiodicity assumption is imposed on the original matrix. -/
theorem recurrent_power_class_mixing {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1)
    (π : Q → ℝ) (hπ : ∀ x, 0 < π x) (hstat : ∀ y, ∑ x, π x * P x y = π y) :
    ∃ a : ℕ, 0 < a ∧ Equivalence (fun x y => 0 < (P ^ a) x y) ∧
      ∀ s : Q, ∃ (ν : PositiveSupportClass (P ^ a) s → ℝ) (C ρ : ℝ),
        (∀ x, 0 < ν x) ∧ (∑ x, ν x = 1) ∧ 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
        ∀ n x y, |(supportClassMatrix (P ^ a) s ^ n) x y / ν y - 1| ≤ C * ρ ^ n := by
  obtain ⟨a, ha, he⟩ := recurrent_idempotent_power P hP hrows π hπ hstat
  refine ⟨a, ha, he, ?_⟩
  intro s
  letI : Nonempty (PositiveSupportClass (P ^ a) s) := ⟨⟨s, he.refl s⟩⟩
  exact positive_matrix_relative_mixing (supportClassMatrix (P ^ a) s)
    (supportClassMatrix_pos (P ^ a) he s)
    (supportClassMatrix_rows (P ^ a) (Matrix.pow_apply_nonneg hP a)
      (stochastic_matrix_power_rows P hrows a) he s)

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SupportClassPowers
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

theorem sum_supportClass_eq {Q : Type} [Fintype Q]
    (P : Matrix Q Q ℝ) (s : Q) (f : Q → ℝ)
    (hf : ∀ y, ¬ 0 < P s y → f y = 0) :
    (∑ y : PositiveSupportClass P s, f y.val) = ∑ y, f y := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter (fun y => 0 < P s y)) (by simp)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : 0 < P s y
  · rw [if_pos hy]
  · rw [if_neg hy, hf y hy]

theorem supportClass_no_exit {Q : Type} (P : Matrix Q Q ℝ)
    (hP : ∀ x y, 0 ≤ P x y) (he : Equivalence (fun x y => 0 < P x y))
    (s : Q) (x : PositiveSupportClass P s) (y : Q) (hy : ¬ 0 < P s y) :
    P x.val y = 0 := by
  apply le_antisymm _ (hP _ _)
  exact le_of_not_gt (fun hp => hy (he.trans x.property hp))

theorem supportClass_power_no_exit {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (he : Equivalence (fun x y => 0 < P x y)) (s : Q)
    (n : ℕ) (x : PositiveSupportClass P s) (y : Q) (hy : ¬ 0 < P s y) :
    (P ^ n) x.val y = 0 := by
  classical
  induction n generalizing x with
  | zero =>
    have hne : x.val ≠ y := fun h => hy (h ▸ x.property)
    simp [Matrix.one_apply, hne]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hz : 0 < P s z
    · rw [ih ⟨z, hz⟩, mul_zero]
    · rw [supportClass_no_exit P hP he s x z hz, zero_mul]

/-- Restricting a closed support class commutes with every matrix power.
In particular, this is an identity for the original transition probabilities,
not a separately normalized chain. -/
theorem supportClassMatrix_power {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (he : Equivalence (fun x y => 0 < P x y)) (s : Q)
    (n : ℕ) (x y : PositiveSupportClass P s) :
    (supportClassMatrix P s ^ n) x y = (P ^ n) x.val y.val := by
  classical
  induction n generalizing x y with
  | zero => simp [Matrix.one_apply, Subtype.ext_iff]
  | succ n ih =>
    rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply]
    simp_rw [ih]
    change (∑ z : PositiveSupportClass P s, P x.val z.val * (P ^ n) z.val y.val) = _
    apply sum_supportClass_eq P s (fun z => P x.val z * (P ^ n) z y.val)
    intro z hz
    rw [supportClass_no_exit P hP he s x z hz, zero_mul]

theorem supportClass_block_power {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (a : ℕ)
    (he : Equivalence (fun x y => 0 < (P ^ a) x y)) (s : Q)
    (n : ℕ) (x y : PositiveSupportClass (P ^ a) s) :
    (supportClassMatrix (P ^ a) s ^ n) x y = (P ^ (a * n)) x.val y.val := by
  rw [supportClassMatrix_power (P ^ a) (Matrix.pow_apply_nonneg hP a) he]
  rw [pow_mul]

/-- A tail of arbitrary residual length is an exact weighted sum over the
blocked start class. Its endpoint may be outside that class. -/
theorem supportClass_tail_power {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (a : ℕ)
    (he : Equivalence (fun x y => 0 < (P ^ a) x y)) (s : Q)
    (n r : ℕ) (x : PositiveSupportClass (P ^ a) s) (t : Q) :
    (P ^ (a * n + r)) x.val t =
      ∑ z : PositiveSupportClass (P ^ a) s,
        (supportClassMatrix (P ^ a) s ^ n) x z * (P ^ r) z.val t := by
  classical
  rw [pow_add, Matrix.mul_apply]
  simp_rw [supportClass_block_power P hP a he]
  symm
  apply sum_supportClass_eq (P ^ a) s (fun z => (P ^ (a * n)) x.val z * (P ^ r) z t)
  intro z hz
  have hzero := supportClass_power_no_exit (P ^ a)
    (Matrix.pow_apply_nonneg hP a) he s n x z hz
  rw [← pow_mul] at hzero
  rw [hzero, zero_mul]

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_PerronFeasibleMax
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

/-- Normalized nonnegative subeigenvectors, with a nonnegative candidate
eigenvalue. This is a closed finite-dimensional feasibility condition. -/
def PerronFeasible {Q : Type} [Fintype Q] (W : Matrix Q Q ℝ)
    (lam : ℝ) (v : Q → ℝ) : Prop :=
  0 ≤ lam ∧ v ∈ stdSimplex ℝ Q ∧ ∀ i, lam * v i ≤ (W *ᵥ v) i

theorem perronFeasible_bounded {Q : Type} [Fintype Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j)
    (lam : ℝ) (v : Q → ℝ) (h : PerronFeasible W lam v) :
    lam ≤ ∑ i, ∑ j, W i j := by
  calc
    lam = ∑ i, lam * v i := by rw [← Finset.mul_sum, h.2.1.2, mul_one]
    _ ≤ ∑ i, (W *ᵥ v) i := Finset.sum_le_sum (fun i _ => h.2.2 i)
    _ ≤ ∑ i, ∑ j, W i j := by
      apply Finset.sum_le_sum
      intro i _
      change (∑ j, W i j * v j) ≤ _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_of_le_one_right (hW i j) (mem_Icc_of_mem_stdSimplex h.2.1 j).2

theorem perronFeasible_closed {Q : Type} [Fintype Q] (W : Matrix Q Q ℝ) :
    IsClosed {z : ℝ × (Q → ℝ) | PerronFeasible W z.1 z.2} := by
  change IsClosed ({z : ℝ × (Q → ℝ) | 0 ≤ z.1} ∩
    ({z : ℝ × (Q → ℝ) | z.2 ∈ stdSimplex ℝ Q} ∩
      {z : ℝ × (Q → ℝ) | ∀ i, z.1 * z.2 i ≤ (W *ᵥ z.2) i}))
  apply IsClosed.inter (isClosed_le continuous_const continuous_fst)
  apply IsClosed.inter ((isClosed_stdSimplex ℝ Q).preimage continuous_snd)
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_le
  · fun_prop
  · change Continuous (fun z : ℝ × (Q → ℝ) => ∑ j, W i j * z.2 j)
    fun_prop

theorem perronFeasible_compact {Q : Type} [Fintype Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j) :
    IsCompact {z : ℝ × (Q → ℝ) | PerronFeasible W z.1 z.2} := by
  apply ((isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (∑ i, ∑ j, W i j))).prod
    (isCompact_stdSimplex ℝ Q)).of_isClosed_subset
    (perronFeasible_closed W)
  intro z hz
  exact ⟨⟨hz.1, perronFeasible_bounded W hW z.1 z.2 hz⟩, hz.2.1⟩

theorem perronFeasible_nonempty {Q : Type} [Fintype Q] [Nonempty Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j) :
    {z : ℝ × (Q → ℝ) | PerronFeasible W z.1 z.2}.Nonempty := by
  classical
  let q : Q := Classical.choice inferInstance
  refine ⟨(0, fun j => if j = q then 1 else 0), le_rfl, ?_, ?_⟩
  · constructor
    · intro i
      change 0 ≤ (if i = q then (1 : ℝ) else 0)
      split_ifs <;> norm_num
    · simp
  · intro i
    simp only [zero_mul, Matrix.mulVec, dotProduct]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hW i j) (by split_ifs <;> norm_num))

/-- A maximal normalized nonnegative subeigenvector exists. This uses the
extreme value theorem on an explicitly closed, bounded feasible set; no
Perron eigenvector existence theorem is assumed. -/
theorem exists_maximal_perronFeasible {Q : Type} [Fintype Q] [Nonempty Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j) :
    ∃ (lam : ℝ) (v : Q → ℝ), PerronFeasible W lam v ∧
      ∀ (a : ℝ) (u : Q → ℝ), PerronFeasible W a u → a ≤ lam := by
  obtain ⟨z, hz, hmax⟩ := (perronFeasible_compact W hW).exists_isMaxOn
    (perronFeasible_nonempty W hW) continuous_fst.continuousOn
  refine ⟨z.1, z.2, hz, ?_⟩
  intro a u hu
  exact hmax (show (a, u) ∈ {z : ℝ × (Q → ℝ) | PerronFeasible W z.1 z.2} from hu)

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_PerronCommuting
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

theorem positive_matrix_mulVec_pos {Q : Type} [Fintype Q]
    (B : Matrix Q Q ℝ) (hB : ∀ i j, 0 < B i j)
    (v : Q → ℝ) (hv : ∀ i, 0 ≤ v i) (hn : ∃ i, 0 < v i) :
    ∀ i, 0 < (B *ᵥ v) i := by
  intro i
  obtain ⟨j, hj⟩ := hn
  apply Finset.sum_pos_iff_of_nonneg (fun k _ => mul_nonneg (hB i k).le (hv k)) |>.mpr
  exact ⟨j, Finset.mem_univ j, mul_pos (hB i j) hj⟩

theorem perronFeasible_normalize {Q : Type} [Fintype Q] [Nonempty Q]
    (W : Matrix Q Q ℝ) (a : ℝ) (ha : 0 ≤ a) (v : Q → ℝ)
    (hv : ∀ i, 0 < v i) (hsub : ∀ i, a * v i ≤ (W *ᵥ v) i) :
    PerronFeasible W a (fun i => v i / ∑ j, v j) := by
  have hZ : 0 < ∑ j, v j := Finset.sum_pos (fun i _ => hv i) Finset.univ_nonempty
  refine ⟨ha, ⟨fun i => (div_pos (hv i) hZ).le, ?_⟩, ?_⟩
  · rw [← Finset.sum_div]
    exact div_self hZ.ne'
  · intro i
    change a * (v i / ∑ j, v j) ≤ ∑ j, W i j * (v j / ∑ k, v k)
    simp only [← mul_div_assoc, ← Finset.sum_div]
    exact div_le_div_of_nonneg_right (hsub i) hZ.le

/-- A positive matrix commuting with W spreads every nonzero nonnegative
residual to all coordinates. At a maximal subeigenvalue, the residual must
therefore vanish. This is the central existence argument. -/
theorem perron_exists_of_positive_commuting {Q : Type} [Fintype Q] [Nonempty Q]
    (W B : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j)
    (hB : ∀ i j, 0 < B i j) (hcomm : W * B = B * W)
    (hrow : ∀ i, ∃ j, 0 < W i j) :
    ∃ (lam : ℝ) (r : Q → ℝ), 0 < lam ∧ (∀ i, 0 < r i) ∧ W *ᵥ r = lam • r := by
  classical
  obtain ⟨lam, v, hv, hmax⟩ := exists_maximal_perronFeasible W hW
  have hvnz : ∃ i, 0 < v i := by
    have hp : 0 < ∑ i, v i := by rw [hv.2.1.2]; norm_num
    obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hv.2.1.1 i)).mp hp
    exact ⟨i, hi⟩
  let r := B *ᵥ v
  have hr : ∀ i, 0 < r i := positive_matrix_mulVec_pos B hB v hv.2.1.1 hvnz
  let z : Q → ℝ := W *ᵥ v - lam • v
  have hz : ∀ i, 0 ≤ z i := by
    intro i
    exact sub_nonneg.mpr (hv.2.2 i)
  have hres : W *ᵥ r - lam • r = B *ᵥ z := by
    dsimp only [r, z]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, hcomm]
  have hz0 : z = 0 := by
    by_contra hn
    have hzp : ∃ i, 0 < z i := by
      by_contra hc
      apply hn
      funext i
      have hh : ¬ 0 < z i := fun h => hc ⟨i, h⟩
      exact le_antisymm (le_of_not_gt hh) (hz i)
    have hBz : ∀ i, 0 < (B *ᵥ z) i := positive_matrix_mulVec_pos B hB z hz hzp
    let d := Finset.univ.inf' Finset.univ_nonempty (fun i => (B *ᵥ z) i / r i)
    have hd : 0 < d := (Finset.lt_inf'_iff _).mpr
      (fun i _ => div_pos (hBz i) (hr i))
    have hdi (i : Q) : d ≤ (B *ᵥ z) i / r i := Finset.inf'_le _ (Finset.mem_univ i)
    have hnew : ∀ i, (lam + d) * r i ≤ (W *ᵥ r) i := by
      intro i
      have hm := (le_div_iff₀ (hr i)).mp (hdi i)
      have he := congrFun hres i
      change (W *ᵥ r) i - lam * r i = (B *ᵥ z) i at he
      nlinarith
    have hf := perronFeasible_normalize W (lam + d) (add_nonneg hv.1 hd.le) r hr hnew
    have hc := hmax (lam + d) (fun i => r i / ∑ j, r j) hf
    linarith
  have heigen : W *ᵥ r = lam • r := by
    rw [hz0, Matrix.mulVec_zero] at hres
    exact sub_eq_zero.mp hres
  have hlam : 0 < lam := by
    let i : Q := Classical.choice inferInstance
    obtain ⟨j, hj⟩ := hrow i
    have hp : 0 < (W *ᵥ r) i := by
      apply Finset.sum_pos_iff_of_nonneg (fun k _ => mul_nonneg (hW i k) (hr k).le) |>.mpr
      exact ⟨j, Finset.mem_univ j, mul_pos hj (hr j)⟩
    rw [heigen] at hp
    exact (mul_pos_iff_of_pos_right (hr i)).mp hp
  exact ⟨lam, r, hlam, hr, heigen⟩

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_IrreduciblePerron
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

/-- A finite sum of powers of an irreducible nonnegative matrix is strictly
positive and commutes with the original matrix. The selected powers may
differ between pairs of states, so no aperiodicity assumption is needed. -/
theorem irreducible_positive_commuting {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : W.IsIrreducible) :
    ∃ B : Matrix Q Q ℝ, (∀ i j, 0 < B i j) ∧ W * B = B * W := by
  classical
  have hp := (Matrix.isIrreducible_iff_exists_pow_pos hW.nonneg).mp hW
  choose k hkpos hk using hp
  let B : Matrix Q Q ℝ := ∑ p : Q × Q, W ^ k p.1 p.2
  refine ⟨B, ?_, ?_⟩
  · intro i j
    simp only [B, Matrix.sum_apply]
    apply Finset.sum_pos_iff_of_nonneg
      (fun p _ => Matrix.pow_apply_nonneg hW.nonneg (k p.1 p.2) i j) |>.mpr
    exact ⟨(i, j), Finset.mem_univ _, hk i j⟩
  · dsimp only [B]
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rw [← pow_succ', ← pow_succ]

theorem irreducible_row_positive {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : W.IsIrreducible) (i : Q) : ∃ j, 0 < W i j := by
  obtain ⟨k, hk, hp⟩ := (Matrix.isIrreducible_iff_exists_pow_pos hW.nonneg).mp hW i i
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [pow_succ', Matrix.mul_apply] at hp
  obtain ⟨j, _, hj⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun j _ => mul_nonneg (hW.nonneg i j) (Matrix.pow_apply_nonneg hW.nonneg m j i))).mp hp
  refine ⟨j, ?_⟩
  rcases mul_pos_iff.mp hj with h | h
  · exact h.1
  · exact False.elim ((not_lt_of_ge (hW.nonneg i j)) h.1)

/-- Every finite irreducible nonnegative real matrix has a strictly positive
right eigenvector with a strictly positive eigenvalue. Periodic matrices
and cyclic singleton components are included. -/
theorem irreducible_positive_eigenvector {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (W : Matrix Q Q ℝ) (hW : W.IsIrreducible) :
    ∃ (lam : ℝ) (r : Q → ℝ), 0 < lam ∧ (∀ i, 0 < r i) ∧ W *ᵥ r = lam • r := by
  obtain ⟨B, hB, hcomm⟩ := irreducible_positive_commuting W hW
  exact perron_exists_of_positive_commuting W B hW.nonneg hB hcomm
    (irreducible_row_positive W hW)

/-- Positive left and right eigenvectors must have the same eigenvalue,
because their scalar pairing is strictly positive. -/
theorem positive_left_right_eigenvalue_eq {Q : Type} [Fintype Q] [Nonempty Q]
    (W : Matrix Q Q ℝ) (a b : ℝ) (l r : Q → ℝ)
    (hl : ∀ i, 0 < l i) (hr : ∀ i, 0 < r i)
    (hleft : ∀ j, ∑ i, l i * W i j = a * l j)
    (hright : ∀ i, ∑ j, W i j * r j = b * r i) : a = b := by
  have hpair : 0 < ∑ i, l i * r i :=
    Finset.sum_pos (fun i _ => mul_pos (hl i) (hr i)) Finset.univ_nonempty
  have he : a * (∑ i, l i * r i) = b * (∑ i, l i * r i) := by
    calc
      _ = ∑ j, (∑ i, l i * W i j) * r j := by
        simp_rw [hleft]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i, l i * (∑ j, W i j * r j) := by
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by
        simp_rw [hright]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  exact (mul_right_cancel₀ hpair.ne') he

/-- Positive left/right vectors, sharing one positive eigenvalue, normalized
by their pairing as required by the Doob transform in C.3 and E.6. -/
theorem irreducible_perron_vectors {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (W : Matrix Q Q ℝ) (hW : W.IsIrreducible) :
    ∃ (lam : ℝ) (l r : Q → ℝ), 0 < lam ∧ (∀ i, 0 < l i) ∧ (∀ i, 0 < r i) ∧
      (∑ i, l i * r i = 1) ∧
      (∀ i, ∑ j, W i j * r j = lam * r i) ∧
      (∀ j, ∑ i, l i * W i j = lam * l j) := by
  obtain ⟨lam, r, hlam, hr, heR⟩ := irreducible_positive_eigenvector W hW
  obtain ⟨mu, l, hmu, hl, heL⟩ := irreducible_positive_eigenvector W.transpose hW.transpose
  have hright (i : Q) : ∑ j, W i j * r j = lam * r i := congrFun heR i
  have hleft (j : Q) : ∑ i, l i * W i j = mu * l j := by
    have h := congrFun heL j
    simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul,
      mul_comm] using h
  have heq : mu = lam := positive_left_right_eigenvalue_eq W mu lam l r hl hr hleft hright
  subst mu
  let Z := ∑ i, l i * r i
  have hZ : 0 < Z := Finset.sum_pos (fun i _ => mul_pos (hl i) (hr i)) Finset.univ_nonempty
  refine ⟨lam, fun i => l i / Z, r, hlam, fun i => div_pos (hl i) hZ, hr, ?_, hright, ?_⟩
  · simp only [div_mul_eq_mul_div, ← Finset.sum_div]
    exact div_self hZ.ne'
  · intro j
    simp only [div_mul_eq_mul_div]
    rw [← Finset.sum_div, hleft, mul_div_assoc]

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_PerronDoobModel
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

theorem doobMatrix_irreducible {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : W.IsIrreducible) (lam : ℝ) (hlam : 0 < lam)
    (r : Q → ℝ) (hr : ∀ i, 0 < r i) : (doobMatrix W lam r).IsIrreducible := by
  have hn : ∀ i j, 0 ≤ doobMatrix W lam r i j :=
    doobKernel_nonneg (fun i j => W i j) hW.nonneg lam hlam r hr
  apply (Matrix.isIrreducible_iff_exists_pow_pos hn).mpr
  intro i j
  obtain ⟨k, hk, hp⟩ := (Matrix.isIrreducible_iff_exists_pow_pos hW.nonneg).mp hW i j
  refine ⟨k, hk, ?_⟩
  rw [doobMatrix_power W lam hlam r hr]
  exact div_pos (mul_pos hp (hr j)) (mul_pos (pow_pos hlam k) (hr i))

/-- The Doob stochastic model exists for every finite irreducible
nonnegative matrix. The eigenvectors are constructed by proved existence
lemmas, and every endpoint-conditioned bridge law is preserved exactly. -/
theorem irreducible_doob_model {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (W : Matrix Q Q ℝ) (hW : W.IsIrreducible) :
    ∃ (lam : ℝ) (l r : Q → ℝ), 0 < lam ∧ (∀ i, 0 < l i) ∧ (∀ i, 0 < r i) ∧
      (∑ i, l i * r i = 1) ∧
      (∀ i, ∑ j, W i j * r j = lam * r i) ∧
      (∀ j, ∑ i, l i * W i j = lam * l j) ∧
      (doobMatrix W lam r).IsIrreducible ∧
      (∀ i, ∑ j, doobMatrix W lam r i j = 1) ∧
      (∀ i j, 0 < doobMatrix W lam r i j ↔ 0 < W i j) ∧
      (kernelAdvance (fun i j => doobMatrix W lam r i j) (fun i => l i * r i) =
        fun i => l i * r i) ∧
      ∀ (s t : Q) (n : ℕ),
        normalizeWeights (bridgeWeight (fun i j => doobMatrix W lam r i j) s t n) =
          normalizeWeights (bridgeWeight (fun i j => W i j) s t n) := by
  obtain ⟨lam, l, r, hlam, hl, hr, hnorm, hright, hleft⟩ := irreducible_perron_vectors W hW
  refine ⟨lam, l, r, hlam, hl, hr, hnorm, hright, hleft,
    doobMatrix_irreducible W hW lam hlam r hr, ?_, ?_, ?_, ?_⟩
  · exact doobKernel_row_sum (fun i j => W i j) lam hlam r hr hright
  · exact doobKernel_pos_iff (fun i j => W i j) lam hlam r hr
  · exact doobKernel_stationary (fun i j => W i j) lam hlam l r hr hleft
  · intro s t n
    exact doobKernel_bridge_law (fun i j => W i j) lam hlam r hr s t n

theorem perron_weighted_row_identity {Q : Type} [Fintype Q]
    (W : Matrix Q Q ℝ) (lam : ℝ) (l : Q → ℝ)
    (hleft : ∀ j, ∑ i, l i * W i j = lam * l j) :
    lam * (∑ i, l i) = ∑ i, l i * (∑ j, W i j) := by
  rw [Finset.mul_sum]
  simp_rw [← hleft]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

/-- A positive left eigenvector transfers a strict row-sum defect into a
strict eigenvalue bound. With c=2 this is the source subcriticality argument. -/
theorem perron_strict_row_bound {Q : Type} [Fintype Q] [Nonempty Q]
    (W : Matrix Q Q ℝ) (lam : ℝ) (l : Q → ℝ) (hl : ∀ i, 0 < l i)
    (hleft : ∀ j, ∑ i, l i * W i j = lam * l j)
    (c : ℝ) (hrows : ∀ i, ∑ j, W i j ≤ c) (hdefect : ∃ i, ∑ j, W i j < c) : lam < c := by
  have hZ : 0 < ∑ i, l i := Finset.sum_pos (fun i _ => hl i) Finset.univ_nonempty
  have hstrict : (∑ i, l i * (∑ j, W i j)) < ∑ i, l i * c := by
    apply Finset.sum_lt_sum
    · intro i _
      exact mul_le_mul_of_nonneg_left (hrows i) (hl i).le
    · obtain ⟨i, hi⟩ := hdefect
      exact ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left hi (hl i)⟩
  rw [← perron_weighted_row_identity W lam l hleft, ← Finset.sum_mul, mul_comm (∑ i, l i) c]
    at hstrict
  nlinarith



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_DoobPowerClassMixing
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

/-- The finite family of support classes admits one common geometric rate
and coefficient, independent of the start class and number of block steps. -/
theorem recurrent_power_classes_uniform {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1)
    (π : Q → ℝ) (hπ : ∀ x, 0 < π x) (hstat : ∀ y, ∑ x, π x * P x y = π y) :
    ∃ (a : ℕ) (C ρ : ℝ), 0 < a ∧ 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      Equivalence (fun x y => 0 < (P ^ a) x y) ∧
      ∀ s : Q, ∃ ν : PositiveSupportClass (P ^ a) s → ℝ,
        (∀ x, 0 < ν x) ∧ (∑ x, ν x = 1) ∧
        ∀ n x y, |(supportClassMatrix (P ^ a) s ^ n) x y / ν y - 1| ≤ C * ρ ^ n := by
  classical
  obtain ⟨a, ha, he, hclasses⟩ := recurrent_power_class_mixing P hP hrows π hπ hstat
  choose ν C ρ hν hsum hC hρ hρlt hmix using hclasses
  let Cmax := Finset.univ.sup' Finset.univ_nonempty C
  let ρmax := Finset.univ.sup' Finset.univ_nonempty ρ
  let s₀ : Q := Classical.choice inferInstance
  have hCmax : 0 < Cmax := (hC s₀).trans_le (Finset.le_sup' C (Finset.mem_univ s₀))
  have hρmax : 0 < ρmax := (hρ s₀).trans_le (Finset.le_sup' ρ (Finset.mem_univ s₀))
  have hρmaxlt : ρmax < 1 := (Finset.sup'_lt_iff _).mpr (fun s _ => hρlt s)
  refine ⟨a, Cmax, ρmax, ha, hCmax, hρmax, hρmaxlt, he, ?_⟩
  intro s
  refine ⟨ν s, hν s, hsum s, ?_⟩
  intro n x y
  apply (hmix s n x y).trans
  exact mul_le_mul (Finset.le_sup' C (Finset.mem_univ s))
    (pow_le_pow_left₀ (hρ s).le (Finset.le_sup' ρ (Finset.mem_univ s)) n)
    (pow_nonneg (hρ s).le n) hCmax.le



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_PeriodicTailMixing
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

/-- Nonnegative weighting preserves a uniform relative error, irrespective
of how small the weighted normalizing constant is. -/
theorem weighted_relative_error {Q : Type} [Fintype Q]
    (v w b : Q → ℝ) (hw : ∀ z, 0 < w z) (hb : ∀ z, 0 ≤ b z)
    (δ : ℝ) (hv : ∀ z, |v z / w z - 1| ≤ δ)
    (hc : 0 < ∑ z, w z * b z) :
    |(∑ z, v z * b z) / (∑ z, w z * b z) - 1| ≤ δ := by
  classical
  have hpoint (z : Q) : |v z - w z| ≤ δ * w z := by
    have h := hv z
    rw [div_sub_one (hw z).ne', abs_div, abs_of_pos (hw z)] at h
    exact (div_le_iff₀ (hw z)).mp h
  rw [div_sub_one hc.ne', abs_div, abs_of_pos hc]
  apply (div_le_iff₀ hc).mpr
  calc
    |(∑ z, v z * b z) - ∑ z, w z * b z| = |∑ z, (v z - w z) * b z| := by
      simp only [Finset.sum_sub_distrib, sub_mul]
    _ ≤ ∑ z, |(v z - w z) * b z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z, δ * w z * b z := by
      apply Finset.sum_le_sum
      intro z _
      rw [abs_mul, abs_of_nonneg (hb z)]
      exact mul_le_mul_of_nonneg_right (hpoint z) (hb z)
    _ = δ * ∑ z, w z * b z := by simp only [Finset.mul_sum, mul_assoc]

def supportClassTailCoefficient {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (a : ℕ) (s : Q)
    (ν : PositiveSupportClass (P ^ a) s → ℝ) (r : ℕ) (t : Q) : ℝ :=
  ∑ z, ν z * (P ^ r) z.val t

theorem supportClassTailCoefficient_pos_iff {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (a : ℕ) (s : Q)
    (ν : PositiveSupportClass (P ^ a) s → ℝ) (hν : ∀ z, 0 < ν z)
    (r : ℕ) (t : Q) :
    0 < supportClassTailCoefficient P a s ν r t ↔
      ∃ z : PositiveSupportClass (P ^ a) s, 0 < (P ^ r) z.val t := by
  unfold supportClassTailCoefficient
  rw [Finset.sum_pos_iff_of_nonneg (fun z _ =>
    mul_nonneg (hν z).le (Matrix.pow_apply_nonneg hP r _ _))]
  simp only [Finset.mem_univ, true_and, mul_pos_iff_of_pos_left (hν _)]

/-- Positive endpoint mass of the actual original chain implies positivity
of the leading tail coefficient; no acceptance-probability lower bound is
assumed or introduced. -/
theorem supportClassTailCoefficient_pos_of_path {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (a : ℕ)
    (he : Equivalence (fun x y => 0 < (P ^ a) x y)) (s : Q)
    (ν : PositiveSupportClass (P ^ a) s → ℝ) (hν : ∀ z, 0 < ν z)
    (n r : ℕ) (x : PositiveSupportClass (P ^ a) s) (t : Q)
    (hp : 0 < (P ^ (a * n + r)) x.val t) :
    0 < supportClassTailCoefficient P a s ν r t := by
  rw [supportClass_tail_power P hP a he s] at hp
  have hpos := (Finset.sum_pos_iff_of_nonneg (fun z _ => mul_nonneg
    (Matrix.pow_apply_nonneg (fun i j => (supportClassMatrix_pos (P ^ a) he s i j).le)
      n x z) (Matrix.pow_apply_nonneg hP r z.val t))).mp hp
  obtain ⟨z, _, hz⟩ := hpos
  apply (supportClassTailCoefficient_pos_iff P hP a s ν hν r t).mpr
  exact ⟨z, pos_of_mul_pos_right hz (Matrix.pow_apply_nonneg
    (fun i j => (supportClassMatrix_pos (P ^ a) he s i j).le) n x z)⟩

/-- The class mixing estimate controls every compatible residual endpoint
of the actual matrix power, with the same relative error. -/
theorem supportClass_tail_relative_mixing {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (a : ℕ)
    (he : Equivalence (fun x y => 0 < (P ^ a) x y)) (s : Q)
    (ν : PositiveSupportClass (P ^ a) s → ℝ) (hν : ∀ z, 0 < ν z)
    (δ : ℝ) (n r : ℕ) (x : PositiveSupportClass (P ^ a) s) (t : Q)
    (hmix : ∀ z, |(supportClassMatrix (P ^ a) s ^ n) x z / ν z - 1| ≤ δ)
    (hc : 0 < supportClassTailCoefficient P a s ν r t) :
    |(P ^ (a * n + r)) x.val t / supportClassTailCoefficient P a s ν r t - 1| ≤ δ := by
  rw [supportClass_tail_power P hP a he s]
  exact weighted_relative_error _ ν (fun z => (P ^ r) z.val t) hν
    (fun z => Matrix.pow_apply_nonneg hP r z.val t) δ hmix hc

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SupportedBoundaryApproximation
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

theorem supported_boundary_product_approximation {Q : Type} [Fintype Q] [DecidableEq Q]
    {k : ℕ} (R : Q → Prop) [DecidablePred R] (s : {x // R x})
    (T : Fin k → Q → Q → ℝ) (tail : Q → ℝ)
    (hclosed : ∀ i x z, R x → ¬ R z → T i x z = 0)
    (ν : {x // R x} → ℝ) (hν : ∀ x, 0 < ν x) (hνsum : ∑ x, ν x = 1)
    (c : ℝ) (hc : 0 < c) (δ : ℝ) (hδ : 0 ≤ δ) (hδlt : δ < 1)
    (hsmall : ((k + 1 : ℕ) : ℝ) * δ ≤ 1 / 2)
    (hT : ∀ i (x z : {x // R x}), |T i x.val z.val / ν z - 1| ≤ δ)
    (htail : ∀ x : {x // R x}, |tail x.val / c - 1| ≤ δ) :
    (0 < ∑ y, boundaryWeight s.val T tail y) ∧
    (∀ z : Fin k → {x // R x}, 0 < boundaryWeight s.val T tail (fun i => (z i).val)) ∧
    tv (normalizeWeights (boundaryWeight s.val T tail))
      (fun y => ∑ z : Fin k → {x // R x}, if (fun i => (z i).val) = y then
        (∏ i, ν (z i)) else 0) ≤ 2 * (k + 1 : ℕ) * δ := by
  classical
  let f := fun z : Fin k → {x // R x} => fun i => (z i).val
  let w := boundaryWeight s.val T tail
  let v := boundaryWeight s (fun i x z => T i x.val z.val) (fun x => tail x.val)
  have hweight : (fun z => w (f z)) = v := by
    funext z
    exact boundaryWeight_map (fun x : {x // R x} => x.val) s T tail z
  have hsupp : ∀ y, (¬ ∃ z, f z = y) → w y = 0 :=
    supported_boundary_weight_zero R s.val s.property T tail hclosed
  obtain ⟨hZ, hp, htv⟩ := bridge_boundary_product_approximation s
    (fun i x z => T i x.val z.val) (fun x => tail x.val)
    ν hν hνsum c hc δ hδ hδlt hsmall hT htail
  have hsum := embedded_weight_sum f (subtype_tuple_injective R) w hsupp
  rw [hweight] at hsum
  refine ⟨hsum ▸ hZ, ?_, ?_⟩
  · intro z
    have hz : 0 < v z := (div_pos_iff_of_pos_right hZ).mp (hp z)
    change 0 < w (f z)
    rw [congrFun hweight z]
    exact hz
  · have h := embedded_normalized_tv_le f (subtype_tuple_injective R) w hsupp
      (fun z => ∏ i, ν (z i))
    rw [hweight] at h
    exact h.trans htv

/-- Relative estimates restricted to the closed boundary class suffice
for the actual ambient full-path bridge law. All sampled tuples admit
positive-weight full paths, including tails ending outside the class. -/
theorem supported_actual_bridge_boundary_approximation {Q : Type} [Fintype Q] [DecidableEq Q]
    {k : ℕ} (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y)
    (l : Fin (k + 1) → ℕ) (R : Q → Prop) [DecidablePred R]
    (s : {x // R x}) (t : Q)
    (hclosed : ∀ (i : Fin k) x z, R x → ¬ R z → (W ^ l i.castSucc) x z = 0)
    (ν : {x // R x} → ℝ) (hν : ∀ x, 0 < ν x) (hνsum : ∑ x, ν x = 1)
    (c : ℝ) (hc : 0 < c) (δ : ℝ) (hδ : 0 ≤ δ) (hδlt : δ < 1)
    (hsmall : ((k + 1 : ℕ) : ℝ) * δ ≤ 1 / 2)
    (hT : ∀ (i : Fin k) (x z : {x // R x}), |(W ^ l i.castSucc) x.val z.val / ν z - 1| ≤ δ)
    (htail : ∀ x : {x // R x}, |(W ^ l (Fin.last k)) x.val t / c - 1| ≤ δ) :
    (0 < bridgePartition (fun x z => W x z) s.val t (bridgeBlockLength l)) ∧
    (∀ y : Fin k → {x // R x}, ∃ γ : BoundaryPath Q l s.val t (fun i => (y i).val),
      0 < edgePathWeight (fun x z => W x z) γ.val) ∧
    tv (fun y => ∑ γ : Fin (bridgeBlockLength l + 1) → Q,
        if bridgeBoundaryStates l γ = y then
          normalizeWeights (bridgeWeight (fun x z => W x z) s.val t (bridgeBlockLength l)) γ else 0)
      (fun y => ∑ z : Fin k → {x // R x}, if (fun i => (z i).val) = y then
        (∏ i, ν (z i)) else 0) ≤ 2 * (k + 1 : ℕ) * δ := by
  classical
  have he : bridgeBoundaryMass (fun x z => W x z) l s.val t =
      boundaryWeight s.val (fun i x z => (W ^ l i.castSucc) x z)
        (fun x => (W ^ l (Fin.last k)) x t) := by
    funext y
    exact bridgeBoundaryMass_matrix W l s.val t y
  obtain ⟨hZ, hp, htv⟩ := supported_boundary_product_approximation R s
    (fun i x z => (W ^ l i.castSucc) x z) (fun x => (W ^ l (Fin.last k)) x t)
    hclosed ν hν hνsum c hc δ hδ hδlt hsmall hT htail
  rw [← he] at hZ hp htv
  refine ⟨by simpa only [bridgeBoundaryMass_sum] using hZ, ?_, ?_⟩
  · intro y
    exact (bridgeBoundaryMass_pos_iff_path (fun x z => W x z) hW l s.val t
      (fun i => (y i).val)).mp (hp y)
  · simpa only [normalized_bridge_boundaries] using htv

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_PeriodicBridgeBoundaries
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

theorem periodic_bridgeBlockLength {k : ℕ} (a r : ℕ)
    (l m : Fin (k + 1) → ℕ) (hl : ∀ i : Fin k, l i.castSucc = a * m i.castSucc)
    (ht : l (Fin.last k) = a * m (Fin.last k) + r) :
    bridgeBlockLength l = a * (∑ i, m i) + r := by
  rw [bridgeBlockLength_eq_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp_rw [hl]
  rw [ht, ← Finset.mul_sum]
  ring

/-- The boundary law of an actual compatible bridge, for a possibly
periodic chain, is close to independent samples from its blocked start
class. Only positivity of the endpoint mass is required. -/
theorem periodic_actual_bridge_boundaries {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (a : ℕ)
    (he : Equivalence (fun x y => 0 < (P ^ a) x y)) (s : Q)
    (ν : PositiveSupportClass (P ^ a) s → ℝ) (hν : ∀ z, 0 < ν z)
    (hνsum : ∑ z, ν z = 1) (C ρ : ℝ) (hC : 0 < C) (hρ : 0 < ρ) (hρlt : ρ < 1)
    (hmix : ∀ n x z, |(supportClassMatrix (P ^ a) s ^ n) x z / ν z - 1| ≤ C * ρ ^ n)
    (k : ℕ) (l m : Fin (k + 1) → ℕ) (r : ℕ) (t : Q) (B : ℕ)
    (hl : ∀ i : Fin k, l i.castSucc = a * m i.castSucc)
    (ht : l (Fin.last k) = a * m (Fin.last k) + r)
    (hm : ∀ i, B ≤ m i)
    (hp : 0 < bridgePartition (fun x z => P x z) s t (bridgeBlockLength l))
    (hδ : C * ρ ^ B < 1) (hsmall : ((k + 1 : ℕ) : ℝ) * (C * ρ ^ B) ≤ 1 / 2) :
    (∀ y : Fin k → PositiveSupportClass (P ^ a) s,
      ∃ γ : BoundaryPath Q l s t (fun i => (y i).val), 0 < edgePathWeight (fun x z => P x z) γ.val) ∧
    tv (fun y => ∑ γ : Fin (bridgeBlockLength l + 1) → Q,
        if bridgeBoundaryStates l γ = y then
          normalizeWeights (bridgeWeight (fun x z => P x z) s t (bridgeBlockLength l)) γ else 0)
      (fun y => ∑ z : Fin k → PositiveSupportClass (P ^ a) s,
        if (fun i => (z i).val) = y then (∏ i, ν (z i)) else 0) ≤
      2 * (k + 1 : ℕ) * (C * ρ ^ B) := by
  classical
  have hp' : 0 < (P ^ (a * (∑ i, m i) + r)) s t := by
    rw [bridgePartition_eq_matrix_power, periodic_bridgeBlockLength a r l m hl ht] at hp
    exact hp
  have hc := supportClassTailCoefficient_pos_of_path P hP a he s ν hν
    (∑ i, m i) r ⟨s, he.refl s⟩ t hp'
  have hbound (i : Fin (k + 1)) : C * ρ ^ m i ≤ C * ρ ^ B :=
    mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ.le hρlt.le (hm i)) hC.le
  have hclosed (i : Fin k) (x z : Q) (hx : 0 < (P ^ a) s x)
      (hz : ¬ 0 < (P ^ a) s z) : (P ^ l i.castSucc) x z = 0 := by
    rw [hl i, pow_mul]
    exact supportClass_power_no_exit (P ^ a) (Matrix.pow_apply_nonneg hP a) he s
      (m i.castSucc) ⟨x, hx⟩ z hz
  have hT (i : Fin k) (x z : PositiveSupportClass (P ^ a) s) :
      |(P ^ l i.castSucc) x.val z.val / ν z - 1| ≤ C * ρ ^ B := by
    rw [hl i, ← supportClass_block_power P hP a he s]
    exact (hmix (m i.castSucc) x z).trans (hbound i.castSucc)
  have htail (x : PositiveSupportClass (P ^ a) s) :
      |(P ^ l (Fin.last k)) x.val t / supportClassTailCoefficient P a s ν r t - 1| ≤ C * ρ ^ B := by
    rw [ht]
    apply (supportClass_tail_relative_mixing P hP a he s ν hν
      (C * ρ ^ m (Fin.last k)) (m (Fin.last k)) r x t (hmix (m (Fin.last k)) x) hc).trans
    exact hbound (Fin.last k)
  exact (supported_actual_bridge_boundary_approximation P hP l (fun x => 0 < (P ^ a) s x)
    ⟨s, he.refl s⟩ t hclosed ν hν hνsum (supportClassTailCoefficient P a s ν r t) hc
    (C * ρ ^ B) (by positivity) hδ hsmall hT htail).2

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_IrreducibleBridgeApproximation
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

/-- Uniform bridge-boundary product approximation for actual W-weighted
paths, using the support classes of the blocked stochastic model K.
The constants are chosen before lengths, endpoints and the number of cuts.
Every conclusion concerns an actual full-path marginal and support. -/
def PeriodicBridgeBoundaryApproximation {Q : Type} [Fintype Q] [DecidableEq Q]
    (W K : Matrix Q Q ℝ) (a : ℕ) (C ρ : ℝ) : Prop :=
  ∀ s : Q, ∃ ν : PositiveSupportClass (K ^ a) s → ℝ,
    (∀ z, 0 < ν z) ∧ (∑ z, ν z = 1) ∧
    ∀ (k : ℕ) (l m : Fin (k + 1) → ℕ) (r : ℕ) (t : Q) (B : ℕ),
      (∀ i : Fin k, l i.castSucc = a * m i.castSucc) →
      l (Fin.last k) = a * m (Fin.last k) + r →
      (∀ i, B ≤ m i) →
      0 < bridgePartition (fun x z => W x z) s t (bridgeBlockLength l) →
      C * ρ ^ B < 1 → ((k + 1 : ℕ) : ℝ) * (C * ρ ^ B) ≤ 1 / 2 →
      (∀ y : Fin k → PositiveSupportClass (K ^ a) s,
        ∃ γ : BoundaryPath Q l s t (fun i => (y i).val),
          0 < edgePathWeight (fun x z => W x z) γ.val) ∧
      tv (fun y => ∑ γ : Fin (bridgeBlockLength l + 1) → Q,
          if bridgeBoundaryStates l γ = y then
            normalizeWeights (bridgeWeight (fun x z => W x z) s t (bridgeBlockLength l)) γ else 0)
        (fun y => ∑ z : Fin k → PositiveSupportClass (K ^ a) s,
          if (fun i => (z i).val) = y then (∏ i, ν (z i)) else 0) ≤
        2 * (k + 1 : ℕ) * (C * ρ ^ B)

theorem recurrent_periodic_bridge_approximation {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1)
    (π : Q → ℝ) (hπ : ∀ x, 0 < π x) (hstat : ∀ y, ∑ x, π x * P x y = π y) :
    ∃ (a : ℕ) (C ρ : ℝ), 0 < a ∧ 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      Equivalence (fun x y => 0 < (P ^ a) x y) ∧
      PeriodicBridgeBoundaryApproximation P P a C ρ := by
  obtain ⟨a, C, ρ, ha, hC, hρ, hρlt, he, hclasses⟩ :=
    recurrent_power_classes_uniform P hP hrows π hπ hstat
  refine ⟨a, C, ρ, ha, hC, hρ, hρlt, he, ?_⟩
  intro s
  obtain ⟨ν, hν, hνsum, hmix⟩ := hclasses s
  refine ⟨ν, hν, hνsum, ?_⟩
  exact periodic_actual_bridge_boundaries P hP a he s ν hν hνsum C ρ hC hρ hρlt hmix

/-- The periodic bridge estimate holds for every finite irreducible
nonnegative matrix, with no supplied eigenvectors or aperiodicity
hypothesis and no positive lower bound on the conditioning mass. -/
theorem irreducible_periodic_bridge_approximation {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (W : Matrix Q Q ℝ) (hW : W.IsIrreducible) :
    ∃ (lam : ℝ) (r : Q → ℝ) (a : ℕ) (C ρ : ℝ),
      0 < lam ∧ (∀ x, 0 < r x) ∧ 0 < a ∧ 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
      (∀ x, ∑ y, doobMatrix W lam r x y = 1) ∧
      Equivalence (fun x y => 0 < (doobMatrix W lam r ^ a) x y) ∧
      PeriodicBridgeBoundaryApproximation W (doobMatrix W lam r) a C ρ := by
  obtain ⟨lam, l, r, hlam, hl, hr, hnorm, hright, hleft, hK, hrows, hsupp, hstat, hbridge⟩ :=
    irreducible_doob_model W hW
  have hstation (y : Q) : ∑ x, (l x * r x) * doobMatrix W lam r x y = l y * r y :=
    congrFun hstat y
  obtain ⟨a, C, ρ, ha, hC, hρ, hρlt, he, happ⟩ :=
    recurrent_periodic_bridge_approximation (doobMatrix W lam r) hK.nonneg hrows
      (fun x => l x * r x) (fun x => mul_pos (hl x) (hr x)) hstation
  refine ⟨lam, r, a, C, ρ, hlam, hr, ha, hC, hρ, hρlt, hrows, he, ?_⟩
  intro s
  obtain ⟨ν, hν, hνsum, hbound⟩ := happ s
  refine ⟨ν, hν, hνsum, ?_⟩
  intro k lengths m rem t B hlengths htail hm hp hδ hsmall
  have hpK : 0 < bridgePartition (fun x z => doobMatrix W lam r x z)
      s t (bridgeBlockLength lengths) := by
    rw [bridgePartition_eq_matrix_power] at hp ⊢
    rw [doobMatrix_power W lam hlam r hr]
    exact div_pos (mul_pos hp (hr t))
      (mul_pos (pow_pos hlam (bridgeBlockLength lengths)) (hr s))
  obtain ⟨hpath, htv⟩ := hbound k lengths m rem t B hlengths htail hm hpK hδ hsmall
  refine ⟨?_, ?_⟩
  · intro y
    obtain ⟨γ, hγ⟩ := hpath y
    refine ⟨γ, ?_⟩
    have hsteps := (edgePathWeight_pos_iff (fun x z => doobMatrix W lam r x z) hK.nonneg γ.val).mp hγ
    apply (edgePathWeight_pos_iff (fun x z => W x z) hW.nonneg γ.val).mpr
    intro i
    exact (hsupp _ _).mp (hsteps i)
  · simpa only [hbridge] using htv

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_GeometricBlockLength
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

def geometricCutoff (ρ x : ℝ) : ℕ :=
  ⌈Real.log (1 / x) / (-Real.log ρ)⌉₊

theorem geometricCutoff_bound {ρ x : ℝ} (hρ : 0 < ρ) (hρlt : ρ < 1) (hx : 0 < x) :
    ρ ^ geometricCutoff ρ x ≤ x := by
  have hden : 0 < -Real.log ρ := neg_pos.mpr (Real.log_neg hρ hρlt)
  have hh := (div_le_iff₀ hden).mp (Nat.le_ceil (Real.log (1 / x) / (-Real.log ρ)))
  change Real.log (1 / x) ≤ (geometricCutoff ρ x : ℝ) * (-Real.log ρ) at hh
  rw [Real.log_div one_ne_zero hx.ne', Real.log_one, zero_sub] at hh
  apply (Real.pow_le_iff_le_log hρ hx).mpr
  nlinarith

theorem geometricCutoff_upper {ρ x : ℝ} (hρ : 0 < ρ) (hρlt : ρ < 1)
    (hx : 0 < x) (hxle : x ≤ 1) :
    (geometricCutoff ρ x : ℝ) ≤ Real.log (1 / x) / (-Real.log ρ) + 1 := by
  apply (Nat.ceil_lt_add_one ?_).le
  apply div_nonneg
  · apply Real.log_nonneg
    exact (le_div_iff₀ hx).mpr (by simpa using hxle)
  · exact (neg_pos.mpr (Real.log_neg hρ hρlt)).le

/-- A common block length can be logarithmic, divisible by a fixed period,
and beyond any fixed reachability threshold. The constants are independent
of the trajectory length and requested accuracy. -/
theorem logarithmic_geometric_block {ρ C : ℝ}
    (hρ : 0 < ρ) (hρlt : ρ < 1) (hC : 0 < C)
    (period threshold : ℕ) (hperiod : 0 < period) :
    ∃ A K : ℝ, 0 < A ∧ 0 < K ∧
      ∀ (n : ℕ) (η : ℝ), 0 < η → η ≤ 1 →
        ∃ B : ℕ, period ∣ B ∧ threshold ≤ B ∧ 0 < B ∧
          C * ρ ^ B ≤ η / (8 * (n + 1 : ℕ)) ∧
          (B : ℝ) ≤ A * Real.log ((n + 1 : ℕ) / η) + K := by
  let D := max 1 C
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hD1 : 1 ≤ D := le_max_left _ _
  have hCD : C ≤ D := le_max_right _ _
  let a := -Real.log ρ
  have ha : 0 < a := neg_pos.mpr (Real.log_neg hρ hρlt)
  have hp : (0 : ℝ) < period := Nat.cast_pos.mpr hperiod
  have hlog : 0 ≤ Real.log (8 * D) := Real.log_nonneg (by linarith)
  refine ⟨period / a, period * (Real.log (8 * D) / a + threshold + 2),
    div_pos hp ha, mul_pos hp (by positivity), ?_⟩
  intro n η hη hηle
  let x := η / (8 * D * (n + 1 : ℕ))
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hn1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.le_add_left 1 n
  have hx : 0 < x := by dsimp only [x]; positivity
  have hxle : x ≤ 1 := by
    dsimp only [x]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * D * (n + 1 : ℕ))).mpr
    nlinarith
  let m := geometricCutoff ρ x
  let B := period * (m + 1 + threshold)
  have hbase : m + 1 + threshold ≤ B := Nat.le_mul_of_pos_left _ hperiod
  have hmB : m ≤ B := by omega
  have hB : 0 < B := by omega
  have hxlog : Real.log (1 / x) = Real.log (8 * D) + Real.log ((n + 1 : ℕ) / η) := by
    have heq : 1 / x = (8 * D) * ((n + 1 : ℕ) / η) := by dsimp [x]; field_simp
    rw [heq, Real.log_mul (mul_pos (by norm_num) hD).ne' (div_pos hn hη).ne']
  refine ⟨B, dvd_mul_right period _, by omega, hB, ?_, ?_⟩
  · calc
      C * ρ ^ B ≤ D * ρ ^ B := mul_le_mul_of_nonneg_right hCD (pow_nonneg hρ.le B)
      _ ≤ D * ρ ^ m := mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hρ.le hρlt.le hmB) hD.le
      _ ≤ D * x := mul_le_mul_of_nonneg_left (geometricCutoff_bound hρ hρlt hx) hD.le
      _ = η / (8 * (n + 1 : ℕ)) := by dsimp [x]; field_simp
  · have hm := geometricCutoff_upper hρ hρlt hx hxle
    rw [hxlog] at hm
    change (m : ℝ) ≤ (Real.log (8 * D) + Real.log ((n + 1 : ℕ) / η)) / a + 1 at hm
    have hb := mul_le_mul_of_nonneg_left
      (add_le_add_right (add_le_add_right hm 1) (threshold : ℝ)) hp.le
    dsimp only [B]
    push_cast
    calc
      (period : ℝ) * (m + 1 + threshold) ≤
          period * (((Real.log (8 * D) + Real.log ((n + 1 : ℕ) / η)) / a + 1) + 1 + threshold) := by
        simpa only [add_comm, add_left_comm, add_assoc] using hb
      _ = _ := by push_cast; ring

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_LogarithmicBridgeApproximation
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

theorem geometric_bridge_error_budget (C ρ : ℝ) (hC : 0 < C) (hρ : 0 < ρ)
    (n B : ℕ) (ε : ℝ) (hε : ε ≤ 1)
    (hbound : C * ρ ^ B ≤ ε / (8 * (n + 1 : ℕ))) :
    C * ρ ^ B < 1 ∧
      ∀ k : ℕ, k ≤ n → ((k + 1 : ℕ) : ℝ) * (C * ρ ^ B) ≤ 1 / 2 ∧
        2 * (k + 1 : ℕ) * (C * ρ ^ B) ≤ ε / 4 := by
  have hδ : 0 < C * ρ ^ B := mul_pos hC (pow_pos hρ B)
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hn1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hb := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (n + 1 : ℕ))).mp hbound
  have hd := mul_le_mul_of_nonneg_right hn1 hδ.le
  refine ⟨by nlinarith, ?_⟩
  intro k hk
  have hkn : ((k + 1 : ℕ) : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ hk
  have hprod := mul_le_mul_of_nonneg_right hkn hδ.le
  constructor <;> nlinarith







end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_CyclicSCC
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

theorem matrix_power_positive_comp {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j) (m n : ℕ) (x y z : Q)
    (hm : 0 < (W ^ m) x y) (hn : 0 < (W ^ n) y z) :
    0 < (W ^ (m + n)) x z := by
  rw [pow_add, Matrix.mul_apply]
  exact (mul_pos hm hn).trans_le (Finset.single_le_sum
    (fun j _ => mul_nonneg (Matrix.pow_apply_nonneg hW m x j)
      (Matrix.pow_apply_nonneg hW n j z)) (Finset.mem_univ y))

theorem positive_power_of_reachable {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j) {x y : Q}
    (h : Relation.ReflTransGen (fun i j => 0 < W i j) x y) :
    ∃ n : ℕ, 0 < (W ^ n) x y := by
  induction h with
  | refl => exact ⟨0, by simp⟩
  | @tail y z hxy hyz ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, matrix_power_positive_comp W hW n 1 x y z hn (by simpa using hyz)⟩

/-- A positive-length return walk at the representative. For an SCC this
is equivalent to having any internal edge, as proved below. -/
def CyclicSCC {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (s : Q) : Prop := ∃ n : ℕ, 0 < n ∧ 0 < (W ^ n) s s

theorem cyclicSCC_of_internal_edge {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j) (s : Q)
    (x y : SCCState W s) (hxy : 0 < W x.val y.val) : CyclicSCC W s := by
  have hsx := ((graphComponent_eq_iff _ x.val s).mp x.property).2
  have hys := ((graphComponent_eq_iff _ y.val s).mp y.property).1
  obtain ⟨m, hm⟩ := positive_power_of_reachable W hW hsx
  obtain ⟨n, hn⟩ := positive_power_of_reachable W hW hys
  exact ⟨m + 1 + n, by omega, matrix_power_positive_comp W hW (m + 1) n s y.val s
    (matrix_power_positive_comp W hW m 1 s x.val y.val hm (by simpa using hxy)) hn⟩

/-- Every actual cyclic SCC restriction is irreducible in Mathlib's
positive-length sense, including a singleton with a positive self-loop. -/
theorem cyclic_sccMatrix_irreducible {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j) (s : Q) (hc : CyclicSCC W s) :
    (sccMatrix W s).IsIrreducible := by
  classical
  apply (Matrix.isIrreducible_iff_exists_pow_pos (A := sccMatrix W s)
    (fun x y => hW x.val y.val)).mpr
  intro x y
  have hxs := ((graphComponent_eq_iff _ x.val s).mp x.property).1
  have hsy := ((graphComponent_eq_iff _ y.val s).mp y.property).2
  obtain ⟨m, hm⟩ := positive_power_of_reachable W hW hxs
  obtain ⟨n, hn⟩ := positive_power_of_reachable W hW hsy
  obtain ⟨k, hk, hkk⟩ := hc
  refine ⟨m + k + n, by omega, ?_⟩
  rw [sccMatrix_power W hW]
  exact matrix_power_positive_comp W hW (m + k) n x.val s y.val
    (matrix_power_positive_comp W hW m k x.val s s hm hkk) hn



theorem acyclic_sccMatrix_zero {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j) (s : Q) (hc : ¬ CyclicSCC W s) :
    sccMatrix W s = 0 := by
  ext x y
  apply le_antisymm _ (hW x.val y.val)
  exact le_of_not_gt (fun hp => hc (cyclicSCC_of_internal_edge W hW s x y hp))



/-- An acyclic SCC contributes only zero-length positive bridges. This
closes the exceptional singleton case excluded by positive-return
irreducibility, without dropping those trajectories from the sampler. -/
theorem acyclic_scc_bridge_length_zero {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j) (s : Q) (hc : ¬ CyclicSCC W s)
    (x y : SCCState W s) (n : ℕ)
    (hp : 0 < bridgePartition (fun i j => W i j) x.val y.val n) : n = 0 := by
  classical
  by_contra hn
  rw [← scc_bridgePartition W hW s x y n, bridgePartition_eq_matrix_power,
    acyclic_sccMatrix_zero W hW s hc, zero_pow hn] at hp
  exact (lt_irrefl 0) hp



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_CommonGeometricBlock
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- A finite nonempty family of block exponents and mixing estimates has
one common logarithmic cutoff in original transition steps. The required
relative error is uniform over every member of the family. -/
theorem common_geometric_block_nonempty {I : Type} [Fintype I] [Nonempty I]
    (a threshold : I → ℕ) (ha : ∀ i, 0 < a i)
    (C ρ : I → ℝ) (hC : ∀ i, 0 < C i) (hρ : ∀ i, 0 < ρ i) (hρlt : ∀ i, ρ i < 1) :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
        ∃ L : ℕ, 0 < L ∧ (L : ℝ) ≤ A * Real.log ((n + 1 : ℕ) / ε) + D ∧
          ∀ i, a i ∣ L ∧ 0 < L / a i ∧ threshold i ≤ L / a i ∧
            C i * ρ i ^ (L / a i) ≤ ε / (8 * (n + 1 : ℕ)) := by
  classical
  let d := ∏ i, a i
  have hd : 0 < d := Finset.prod_pos (fun i _ => ha i)
  have had (i : I) : a i ∣ d := Finset.dvd_prod_of_mem a (Finset.mem_univ i)
  have hle (i : I) : a i ≤ d := Nat.le_of_dvd hd (had i)
  let Cmax := Finset.univ.sup' Finset.univ_nonempty C
  let ρmax := Finset.univ.sup' Finset.univ_nonempty ρ
  let tmax := Finset.univ.sup threshold
  let i₀ : I := Classical.choice inferInstance
  have hCmax : 0 < Cmax := (hC i₀).trans_le (Finset.le_sup' C (Finset.mem_univ i₀))
  have hρmax : 0 < ρmax := (hρ i₀).trans_le (Finset.le_sup' ρ (Finset.mem_univ i₀))
  have hρmaxlt : ρmax < 1 := (Finset.sup'_lt_iff _).mpr (fun i _ => hρlt i)
  obtain ⟨A, D, hA, hD, hb⟩ := logarithmic_geometric_block hρmax hρmaxlt hCmax
    1 tmax (by omega)
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  refine ⟨d * A, d * D, mul_pos hd' hA, mul_pos hd' hD, ?_⟩
  intro n ε hε hεle
  obtain ⟨B, _, htB, hB, herr, hlen⟩ := hb n ε hε hεle
  refine ⟨d * B, Nat.mul_pos hd hB, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left hlen hd'.le
    simpa only [Nat.cast_mul, mul_add, mul_assoc] using h
  · intro i
    have hBi : B ≤ d * B / a i := (Nat.le_div_iff_mul_le (ha i)).mpr (by
      simpa only [mul_comm B (a i)] using Nat.mul_le_mul_right B (hle i))
    refine ⟨dvd_mul_of_dvd_left (had i) B, hB.trans_le hBi,
      (Finset.le_sup (Finset.mem_univ i)).trans (htB.trans hBi), ?_⟩
    apply le_trans _ herr
    apply mul_le_mul (Finset.le_sup' C (Finset.mem_univ i)) _
      (pow_nonneg (hρ i).le _) hCmax.le
    exact (pow_le_pow_left₀ (hρ i).le (Finset.le_sup' ρ (Finset.mem_univ i)) _).trans
      (pow_le_pow_of_le_one hρmax.le hρmaxlt.le hBi)



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SCCPeriodicModels
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

abbrev CyclicSCCIndex {Q : Type} [Fintype Q] [DecidableEq Q] (W : Matrix Q Q ℝ) :=
  {s : Q // CyclicSCC W s}

/-- Finite data for each actual cyclic SCC. All constants and models are
fixed before path lengths, accuracy and accepting endpoints are chosen. -/
structure SCCPeriodicModel {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (s : Q) where
  lam : ℝ
  right : SCCState W s → ℝ
  blockExponent : ℕ
  coefficient : ℝ
  rate : ℝ
  lam_pos : 0 < lam
  right_pos : ∀ x, 0 < right x
  exponent_pos : 0 < blockExponent
  coefficient_pos : 0 < coefficient
  rate_pos : 0 < rate
  rate_lt_one : rate < 1
  stochastic : ∀ x, ∑ y, doobMatrix (sccMatrix W s) lam right x y = 1
  approximation : PeriodicBridgeBoundaryApproximation (sccMatrix W s)
    (doobMatrix (sccMatrix W s) lam right) blockExponent coefficient rate

theorem cyclic_scc_periodic_model_exists {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j) (s : Q) (hc : CyclicSCC W s) :
    Nonempty (SCCPeriodicModel W s) := by
  letI : Nonempty (SCCState W s) := ⟨⟨s, rfl⟩⟩
  obtain ⟨lam, r, a, C, ρ, hlam, hr, ha, hC, hρ, hρlt, hrows, _, happ⟩ :=
    irreducible_periodic_bridge_approximation (sccMatrix W s)
      (cyclic_sccMatrix_irreducible W hW s hc)
  exact ⟨⟨lam, r, a, C, ρ, hlam, hr, ha, hC, hρ, hρlt, hrows, happ⟩⟩



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_CutoffBridgeApproximation
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

/-- Apply the periodic estimate to the concrete cutoff partition, and
state the result on actual n-edge input paths. The category-independent
error budget can use any global horizon N >= n. -/
theorem periodic_cutoff_bridge_approximation {Q : Type} [Fintype Q] [DecidableEq Q]
    (W K : Matrix Q Q ℝ) (a : ℕ) (ha : 0 < a)
    (C ρ : ℝ) (hC : 0 < C) (hρ : 0 < ρ)
    (happ : PeriodicBridgeBoundaryApproximation W K a C ρ) :
    ∀ s : Q, ∃ ν : PositiveSupportClass (K ^ a) s → ℝ,
      (∀ z, 0 < ν z) ∧ (∑ z, ν z = 1) ∧
      ∀ (N : ℕ) (ε : ℝ) (L : ℕ), 0 < L → a ∣ L → ε ≤ 1 →
        C * ρ ^ (L / a) ≤ ε / (8 * (N + 1 : ℕ)) →
        ∀ (n : ℕ), n ≤ N → L ≤ n → ∀ t : Q,
          0 < bridgePartition (fun x z => W x z) s t n →
          (∀ y : Fin (cutoffBoundaryCount n L) → PositiveSupportClass (K ^ a) s,
            ∃ γ : Fin (n + 1) → Q, γ 0 = s ∧ γ (Fin.last n) = t ∧
              cutoffBoundaryObservation n L γ = (fun i => (y i).val) ∧
              0 < edgePathWeight (fun x z => W x z) γ) ∧
          tv (fun y => ∑ γ : Fin (n + 1) → Q,
              if cutoffBoundaryObservation n L γ = y then
                normalizeWeights (bridgeWeight (fun x z => W x z) s t n) γ else 0)
            (fun y => ∑ z : Fin (cutoffBoundaryCount n L) → PositiveSupportClass (K ^ a) s,
              if (fun i => (z i).val) = y then (∏ i, ν (z i)) else 0) ≤ ε / 4 := by
  intro s
  obtain ⟨ν, hν, hνsum, hbound⟩ := happ s
  refine ⟨ν, hν, hνsum, ?_⟩
  intro N ε L hL had hεle herr n hn hLn t hp
  obtain ⟨hδ, hbudget⟩ := geometric_bridge_error_budget C ρ hC hρ N (L / a) ε hεle herr
  have hk := (cutoff_block_count_bound n L).2.trans hn
  obtain ⟨hsmall, herr'⟩ := hbudget (cutoffBoundaryCount n L) hk
  obtain ⟨hl, ht, _, hm⟩ := cutoffBlockLengths_periodic ha hL had hLn
  have hp' : 0 < bridgePartition (fun x z => W x z) s t
      (bridgeBlockLength (cutoffBlockLengths n L)) := by
    simpa only [cutoffBlockLengths_total] using hp
  obtain ⟨hpath, htv⟩ := hbound (cutoffBoundaryCount n L) (cutoffBlockLengths n L)
    (fun i => cutoffBlockLengths n L i / a)
    (cutoffBlockLengths n L (Fin.last (cutoffBoundaryCount n L)) % a) t (L / a)
    hl ht hm hp' hδ hsmall
  refine ⟨?_, ?_⟩
  · intro y
    exact positive_boundary_observation (fun x z => W x z) (cutoffBlockLengths n L)
      (cutoffBlockLengths_total n L) s t (fun i => (y i).val) (hpath y)
  · have h := htv.trans herr'
    have hobs (y : Fin (cutoffBoundaryCount n L) → Q) :
        (∑ γ : Fin (n + 1) → Q, if cutoffBoundaryObservation n L γ = y then
          normalizeWeights (bridgeWeight (fun x z => W x z) s t n) γ else 0) =
          normalizeWeights (bridgeBoundaryMass (fun x z => W x z) (cutoffBlockLengths n L) s t) y :=
      normalized_bridge_observation (fun x z => W x z) (cutoffBlockLengths n L)
        (cutoffBlockLengths_total n L) s t y
    simp_rw [hobs]
    simpa only [normalized_bridge_boundaries] using h

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_RoundedPeriodicBoundaries
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

/-- For a long periodic bridge, the boundary approximation is realized by
independent copies of a concrete fair-bit function and depth-six circuit.
The bound combines periodic replacement and actual dyadic rounding error. -/
theorem rounded_periodic_boundary_sampler {Q : Type} [Fintype Q] [DecidableEq Q]
    (W K : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (a : ℕ) (ha : 0 < a)
    (C ρ : ℝ) (hC : 0 < C) (hρ : 0 < ρ)
    (happ : PeriodicBridgeBoundaryApproximation W K a C ρ)
    (s t : Q) (N n L : ℕ) (ε δ : ℝ) (hL : 0 < L) (had : a ∣ L)
    (hεle : ε ≤ 1) (herr : C * ρ ^ (L / a) ≤ ε / (8 * (N + 1 : ℕ)))
    (hn : n ≤ N) (hLn : L ≤ n) (hpart : 0 < bridgePartition (fun x y => W x y) s t n)
    (hδ : 0 < δ) :
    ∃ f : Bits (roundingSeed (Fintype.card (PositiveSupportClass (K ^ a) s)) δ) →
      PositiveSupportClass (K ^ a) s,
      ∃ S : Circuit Q, ∃ hbits : S.randomBits = roundingSeed (Fintype.card (PositiveSupportClass (K ^ a) s)) δ,
        (∀ seed x, S.eval (fun i => seed (Fin.cast hbits i)) x = decide ((f seed).val = x)) ∧
        S.depth ≤ 6 ∧
        S.size ≤ roundingSeed (Fintype.card (PositiveSupportClass (K ^ a) s)) δ + Fintype.card Q *
          (Fintype.card (PositiveSupportClass (K ^ a) s) *
            (2 * (roundingSeed (Fintype.card (PositiveSupportClass (K ^ a) s)) δ *
              (3 * roundingSeed (Fintype.card (PositiveSupportClass (K ^ a) s)) δ + 2) + 1) + 6) + 2) ∧
        let b := embeddedProductLaw (k := cutoffBoundaryCount n L)
          (fun z : PositiveSupportClass (K ^ a) s => z.val) (fun _ => finiteSeedLaw f)
        (∀ y, 0 ≤ b y) ∧ (∑ y, b y = 1) ∧
        (∀ y, 0 < b y → 0 < bridgeBoundaryMass (fun x y => W x y) (cutoffBlockLengths n L) s t y) ∧
        tv b (normalizeWeights (bridgeBoundaryMass (fun x y => W x y) (cutoffBlockLengths n L) s t)) ≤
          ε / 4 + cutoffBoundaryCount n L * δ := by
  classical
  obtain ⟨ν, hν, hνsum, happrox⟩ := periodic_cutoff_bridge_approximation W K a ha C ρ hC hρ happ s
  obtain ⟨hpaths, htv⟩ := happrox N ε L hL had hεle herr n hn hLn t hpart
  obtain ⟨f, S, hbits, he, _, hround, hD, hsize⟩ := rounding_AC0_function
    (fun z : PositiveSupportClass (K ^ a) s => fun x : Q => decide (z.val = x))
    ν (fun z => (hν z).le) hνsum δ hδ
  refine ⟨f, S, hbits, (fun seed x => congrFun (he seed) x), hD, hsize, ?_⟩
  let embed := fun z : PositiveSupportClass (K ^ a) s => z.val
  let b := embeddedProductLaw (k := cutoffBoundaryCount n L) embed (fun _ => finiteSeedLaw f)
  refine ⟨embeddedProductLaw_nonneg embed _ (fun _ => finiteSeedLaw_nonneg f),
    embeddedProductLaw_sum embed _ (fun _ => finiteSeedLaw_sum f), ?_, ?_⟩
  · intro y hy
    obtain ⟨z, hz, _⟩ := embeddedProductLaw_positive_tuple embed _ (fun _ => finiteSeedLaw_nonneg f) y hy
    obtain ⟨γ, hs, ht, hobs, hp⟩ := hpaths z
    have hobs' : bridgeBoundaryObservation (cutoffBlockLengths n L) (cutoffBlockLengths_total n L) γ = y :=
      hobs.trans hz
    rw [← bridge_boundary_fiberMass (fun x y => W x y) (cutoffBlockLengths n L)
      (cutoffBlockLengths_total n L) s t]
    apply (fiberMass_pos_iff _ _ (bridgeWeight_nonneg (fun x y => W x y) hW s t n) y).mpr
    refine ⟨γ, hobs', ?_⟩
    rw [bridgeWeight, if_pos ⟨hs, ht⟩]
    exact hp
  · have hobs (y : Fin (cutoffBoundaryCount n L) → Q) :
        (∑ γ : Fin (n + 1) → Q, if cutoffBoundaryObservation n L γ = y then
          normalizeWeights (bridgeWeight (fun x y => W x y) s t n) γ else 0) =
          normalizeWeights (bridgeBoundaryMass (fun x y => W x y) (cutoffBlockLengths n L) s t) y :=
      normalized_bridge_observation (fun x y => W x y) (cutoffBlockLengths n L)
        (cutoffBlockLengths_total n L) s t y
    simp_rw [hobs] at htv
    have hroundall := tv_rounded_embeddedProductLaw (k := cutoffBoundaryCount n L) embed f ν
      (fun z => (hν z).le) hνsum δ hround
    have hreverse : tv (embeddedProductLaw (k := cutoffBoundaryCount n L) embed (fun _ => ν))
        (normalizeWeights (bridgeBoundaryMass (fun x y => W x y) (cutoffBlockLengths n L) s t)) ≤ ε / 4 := by
      rw [tv_symm]
      exact htv
    have htri := tv_triangle b (embeddedProductLaw embed (fun _ => ν))
      (normalizeWeights (bridgeBoundaryMass (fun x y => W x y) (cutoffBlockLengths n L) s t))
    exact htri.trans (by linarith)

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_RoundedPeriodicBridge
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix





theorem internal_bridge_rounding_error_budget (N k : ℕ) (hk : k ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    0 < ε / (8 * (N + 1 : ℕ)) ∧
    ε / 4 + (2 * k + 1 : ℕ) * (ε / (8 * (N + 1 : ℕ))) ≤ ε / 2 := by
  have hden : (0 : ℝ) < 8 * (N + 1 : ℕ) := by positivity
  let δ := ε / (8 * (N + 1 : ℕ))
  have hδ : 0 < δ := div_pos hε hden
  refine ⟨hδ, ?_⟩
  have hkm : (k : ℝ) * δ ≤ (N : ℝ) * δ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) hδ.le
  have he : 8 * ((N : ℝ) + 1) * δ = ε := by
    dsimp only [δ]
    rw [← Nat.cast_add_one N]
    exact mul_div_cancel₀ ε hden.ne'
  change ε / 4 + (2 * k + 1 : ℕ) * δ ≤ ε / 2
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
  nlinarith

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_EndpointSeedTransport
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

def subtypeSeedSample {Ω : Type} {m : ℕ} (P : Ω → Prop)
    (f : Bits m → Ω) (hf : ∀ seed, P (f seed)) : Bits m → {x // P x} :=
  fun seed => ⟨f seed, hf seed⟩

theorem finiteSeedLaw_subtype {Ω : Type} [Fintype Ω] [DecidableEq Ω] {m : ℕ}
    (P : Ω → Prop) [DecidablePred P] (f : Bits m → Ω) (hf : ∀ seed, P (f seed))
    (x : {x // P x}) : finiteSeedLaw (subtypeSeedSample P f hf) x = finiteSeedLaw f x.val := by
  unfold finiteSeedLaw
  congr 2
  apply Fintype.card_congr
  exact {
    toFun := fun seed => ⟨seed.val, congrArg Subtype.val seed.property⟩
    invFun := fun seed => ⟨seed.val, Subtype.ext seed.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- Restricting to a known output subtype preserves the entire TV error,
without any conditioning division or loss depending on event probability. -/
theorem tv_subtypeSeedSample {Ω : Type} [Fintype Ω] [DecidableEq Ω] {m : ℕ}
    (P : Ω → Prop) [DecidablePred P] (f : Bits m → Ω) (hf : ∀ seed, P (f seed))
    (q : Ω → ℝ) (hq : ∀ x, ¬ P x → q x = 0) :
    tv (finiteSeedLaw (subtypeSeedSample P f hf)) (fun x => q x.val) = tv (finiteSeedLaw f) q := by
  unfold tv
  simp_rw [finiteSeedLaw_subtype]
  congr 1
  apply sum_subtype_of_zero_outside P (fun x => |finiteSeedLaw f x - q x|)
  intro x hx
  have hz : finiteSeedLaw f x = 0 := by
    apply le_antisymm _ (finiteSeedLaw_nonneg f x)
    by_contra h
    obtain ⟨seed, rfl⟩ := (finiteSeedLaw_pos_iff f x).mp (lt_of_not_ge h)
    exact hx (hf seed)
  rw [hz, hq x hx, sub_self, abs_zero]

theorem positive_bridge_seed_endpoints {Q : Type} [Fintype Q] [DecidableEq Q] {m n : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q)
    (f : Bits m → (Fin (n + 1) → Q)) (hf : ∀ seed, 0 < bridgeWeight W s t n (f seed)) :
    ∀ seed, f seed 0 = s ∧ f seed (Fin.last n) = t := by
  intro seed
  have h := (bridgeWeight_pos_iff W hW s t n (f seed)).mp (hf seed)
  exact ⟨h.1, h.2.1⟩

theorem endpoint_seed_transport {Q : Type} [Fintype Q] [DecidableEq Q] {m n : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q)
    (f : Bits m → (Fin (n + 1) → Q)) (hf : ∀ seed, 0 < bridgeWeight W s t n (f seed)) :
    ∃ g : Bits m → EndpointPath Q s t n,
      (∀ seed, (g seed).val = f seed) ∧
      (∀ seed, 0 < edgePathWeight W (g seed).val) ∧
      tv (finiteSeedLaw g) (normalizeWeights (fun x : EndpointPath Q s t n => edgePathWeight W x.val)) =
        tv (finiteSeedLaw f) (normalizeWeights (bridgeWeight W s t n)) := by
  let P := fun γ : Fin (n + 1) → Q => γ 0 = s ∧ γ (Fin.last n) = t
  have hend := positive_bridge_seed_endpoints W hW s t f hf
  let g := subtypeSeedSample P f hend
  refine ⟨g, fun _ => rfl, ?_, ?_⟩
  · intro seed
    have h := hf seed
    rw [bridgeWeight, if_pos (hend seed)] at h
    exact h
  · have hnorm : (normalizeWeights (fun x : EndpointPath Q s t n => edgePathWeight W x.val)) =
        fun x => normalizeWeights (bridgeWeight W s t n) x.val := by
      funext x
      exact normalized_endpoint_bridge W s t n x
    rw [hnorm]
    apply tv_subtypeSeedSample P f hend
    intro γ hγ
    change ¬ (γ 0 = s ∧ γ (Fin.last n) = t) at hγ
    simp only [normalizeWeights, bridgeWeight, if_neg hγ, zero_div]



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_PositiveSupportRounding
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

abbrev PositiveWeightSupport {Ω : Type} (w : Ω → ℝ) := {x : Ω // 0 < w x}

def positiveWeightCard {Ω : Type} [Fintype Ω] (w : Ω → ℝ) : ℕ :=
  Fintype.card (PositiveWeightSupport w)

theorem positiveWeightSupport_sum {Ω : Type} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x : PositiveWeightSupport w, w x.val) = ∑ x, w x := by
  apply sum_subtype_of_zero_outside
  intro x hx
  exact le_antisymm (le_of_not_gt hx) (hw x)



theorem normalized_positiveWeightSupport {Ω : Type} [Fintype Ω]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (x : PositiveWeightSupport w) :
    normalizeWeights (fun y : PositiveWeightSupport w => w y.val) x = normalizeWeights w x.val := by
  simp only [normalizeWeights, positiveWeightSupport_sum w hw]

/-- Round only the positive support, then embed its outputs back in the
original space. The seed bound depends on the number of possible outputs,
not the cardinality of the ambient outcome type. -/
theorem supported_rounding_circuit_budget {Ω Out : Type} [Fintype Ω] [DecidableEq Ω] [Fintype Out]
    (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (hZ : 0 < ∑ x, w x)
    (encode : Ω → Out → Bool) (m : ℕ) (δ : ℝ)
    (hbudget : (positiveWeightCard w : ℝ) / 2 ^ m ≤ δ) :
    ∃ f : Bits m → Ω, ∃ S : Circuit Out, ∃ hbits : S.randomBits = m,
      (∀ seed, S.eval (fun j => seed (Fin.cast hbits j)) = encode (f seed)) ∧
      (∀ seed, 0 < w (f seed)) ∧ tv (finiteSeedLaw f) (normalizeWeights w) ≤ δ ∧
      S.depth ≤ 6 ∧ S.size ≤ m + Fintype.card Out *
        (positiveWeightCard w * (2 * (m * (3 * m + 2) + 1) + 6) + 2) := by
  classical
  let p := fun x : PositiveWeightSupport w => w x.val
  have hp : ∀ x, 0 ≤ p x := fun x => x.property.le
  have hpZ : 0 < ∑ x, p x := by simpa only [p, positiveWeightSupport_sum w hw] using hZ
  obtain ⟨g, S, hbits, he, _, htv, hD, hsize⟩ := rounding_AC0_function_budget
    (fun x : PositiveWeightSupport w => encode x.val) (normalizeWeights p)
    (normalizeWeights_nonneg p hp) (normalizeWeights_sum p hpZ) m δ hbudget
  let f := fun seed => (g seed).val
  have hf : ∀ seed, 0 < w (f seed) := fun seed => (g seed).property
  have hsub : subtypeSeedSample (fun x => 0 < w x) f hf = g := by
    funext seed
    rfl
  have hzero : ∀ x, ¬ 0 < w x → normalizeWeights w x = 0 := by
    intro x hx
    have hz := le_antisymm (le_of_not_gt hx) (hw x)
    simp only [normalizeWeights, hz, zero_div]
  have hdist := tv_subtypeSeedSample (fun x => 0 < w x) f hf (normalizeWeights w) hzero
  rw [hsub] at hdist
  have hnorm : normalizeWeights p = fun x : PositiveWeightSupport w => normalizeWeights w x.val :=
    funext (normalized_positiveWeightSupport w hw)
  refine ⟨f, S, hbits, he, hf, ?_, hD, hsize⟩
  rw [← hdist, ← hnorm]
  exact htv

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_PositiveBridgeCounting
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

/-- With zero-one adjacency entries, a state path has weight zero or one.
For labeled graphs this applies after recording the label in each state. -/
theorem edgePathWeight_zero_or_one {Q : Type} (W : Q → Q → ℝ)
    (hW : ∀ x y, W x y = 0 ∨ W x y = 1) (n : ℕ) (γ : Fin (n + 1) → Q) :
    edgePathWeight W γ = 0 ∨ edgePathWeight W γ = 1 := by
  induction n with
  | zero => simp [edgePathWeight, finitePathWeight]
  | succ n ih =>
    obtain ⟨⟨y, γ'⟩, rfl⟩ := (Fin.snocEquiv (fun _ : Fin (n + 2) => Q)).surjective γ
    change edgePathWeight W (Fin.snoc γ' y) = 0 ∨ edgePathWeight W (Fin.snoc γ' y) = 1
    rw [edgePathWeight_snoc]
    rcases ih γ' with h | h <;>
      rcases hW (γ' (Fin.last n)) y with h' | h' <;> simp [h, h']

/-- The number of feasible endpoint paths equals the corresponding
adjacency-matrix power entry, including length zero. -/
theorem positive_endpoint_card_eq_matrix_power {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ x y, W x y = 0 ∨ W x y = 1)
    (s t : Q) (n : ℕ) :
    (positiveWeightCard (fun γ : EndpointPath Q s t n => edgePathWeight W γ.val) : ℝ) =
      (W ^ n) s t := by
  classical
  let w := fun γ : EndpointPath Q s t n => edgePathWeight W γ.val
  have hw (γ : EndpointPath Q s t n) : 0 ≤ w γ := by
    rcases edgePathWeight_zero_or_one W hW n γ.val with h | h <;> simp [w, h]
  have hone (γ : PositiveWeightSupport w) : w γ.val = 1 := by
    rcases edgePathWeight_zero_or_one W hW n γ.val.val with h | h
    · exact False.elim ((ne_of_gt γ.property) h)
    · exact h
  calc
    _ = ∑ γ : PositiveWeightSupport w, w γ.val := by
      change (positiveWeightCard w : ℝ) = _
      simp [hone, positiveWeightCard]
    _ = ∑ γ : EndpointPath Q s t n, w γ := positiveWeightSupport_sum w hw
    _ = bridgePartition W s t n := endpointPath_weight_sum W s t n
    _ = _ := bridgePartition_eq_matrix_power W n s t

theorem positive_eigenvector_power {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (lam : ℝ) (r : Q → ℝ)
    (heigen : W *ᵥ r = lam • r) (n : ℕ) :
    (W ^ n) *ᵥ r = lam ^ n • r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, heigen,
      smul_smul, pow_succ]

/-- A positive right eigenvector bounds every matrix-power entry without
requiring an asymptotic convergence theorem or an endpoint mass lower bound. -/
theorem positive_eigenvector_entry_bound {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y)
    (lam : ℝ) (r : Q → ℝ) (hr : ∀ x, 0 < r x)
    (heigen : W *ᵥ r = lam • r) (n : ℕ) (s t : Q) :
    (W ^ n) s t ≤ lam ^ n * (r s / r t) := by
  have he := congrFun (positive_eigenvector_power W lam r heigen n) s
  change (∑ y, (W ^ n) s y * r y) = lam ^ n * r s at he
  have ht : (W ^ n) s t * r t ≤ lam ^ n * r s := by
    rw [← he]
    exact Finset.single_le_sum
      (fun y _ => mul_nonneg (Matrix.pow_apply_nonneg hW n s y) (hr y).le)
      (Finset.mem_univ t)
  rw [← mul_div_assoc]
  exact (le_div_iff₀ (hr t)).mpr ht

/-- One finite constant works at every length and for every pair of endpoints. -/
theorem positive_eigenvector_uniform_growth {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y)
    (lam : ℝ) (hlam : 0 ≤ lam) (r : Q → ℝ) (hr : ∀ x, 0 < r x)
    (heigen : W *ᵥ r = lam • r) (γ : ℝ) (hγ : lam ≤ γ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ) (s t : Q), (W ^ n) s t ≤ C * γ ^ n := by
  classical
  let C := 1 + ∑ x : Q, ∑ y : Q, r x / r y
  have hrat (x y : Q) : 0 ≤ r x / r y := (div_pos (hr x) (hr y)).le
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun x _ =>
      Finset.sum_nonneg (fun y _ => hrat x y)))
  refine ⟨C, hC, ?_⟩
  intro n s t
  have hratio : r s / r t ≤ C := by
    have h1 := Finset.single_le_sum (fun y _ => hrat s y) (Finset.mem_univ t)
    have h2 : (∑ y : Q, r s / r y) ≤ ∑ x : Q, ∑ y : Q, r x / r y :=
      Finset.single_le_sum (fun x _ =>
        Finset.sum_nonneg (fun y _ => hrat x y)) (Finset.mem_univ s)
    dsimp only [C]
    linarith
  calc
    (W ^ n) s t ≤ lam ^ n * (r s / r t) :=
      positive_eigenvector_entry_bound W hW lam r hr heigen n s t
    _ ≤ γ ^ n * C := mul_le_mul (pow_le_pow_left₀ hlam hγ n) hratio
      (hrat s t) (pow_nonneg (hlam.trans hγ) n)
    _ = _ := mul_comm _ _

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_AcceptedGraphCategories
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

local instance acceptedGraphCategoryDecEq {Q : Type} [Fintype Q] {n : ℕ} :
    DecidableEq (GraphCategory Q n) := Classical.decEq _

/-- Accepted paths of a weighted graph, without normalizing its rows.
This is needed when transitions are missing or terminal components have
been deleted in the source subcritical construction. -/
def acceptedGraphWeight {Q : Type} [DecidableEq Q] (W : Q → Q → ℝ)
    (s : Q) (F : Finset Q) {n : ℕ} (γ : Fin (n + 1) → Q) : ℝ :=
  if γ 0 = s ∧ γ (Fin.last n) ∈ F then edgePathWeight W γ else 0

theorem acceptedGraphWeight_nonneg {Q : Type} [DecidableEq Q] (W : Q → Q → ℝ)
    (hW : ∀ x y, 0 ≤ W x y) (s : Q) (F : Finset Q) {n : ℕ} (γ : Fin (n + 1) → Q) :
    0 ≤ acceptedGraphWeight W s F γ := by
  unfold acceptedGraphWeight
  split_ifs
  · exact edgePathWeight_nonneg W hW γ
  · exact le_rfl

theorem acceptedGraphWeight_pos_iff {Q : Type} [DecidableEq Q] (W : Q → Q → ℝ)
    (s : Q) (F : Finset Q) {n : ℕ} (γ : Fin (n + 1) → Q) :
    0 < acceptedGraphWeight W s F γ ↔
      γ 0 = s ∧ γ (Fin.last n) ∈ F ∧ 0 < edgePathWeight W γ := by
  unfold acceptedGraphWeight
  split_ifs with h
  · tauto
  · simp only [lt_self_iff_false, false_iff]
    tauto

abbrev AcceptedGraphCategory {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (s : Q) (F : Finset Q) (n : ℕ) :=
  PositiveFiber (graphCategory (fun x y => 0 < W x y)) (acceptedGraphWeight (n := n) W s F)

theorem acceptedGraphCategory_has_path {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s : Q) (F : Finset Q) {n : ℕ}
    (c : AcceptedGraphCategory W s F n) :
    ∃ γ : Fin (n + 1) → Q, graphCategory (fun x y => 0 < W x y) γ = c.val ∧
      γ 0 = s ∧ γ (Fin.last n) ∈ F ∧ 0 < edgePathWeight W γ := by
  obtain ⟨γ, hcat, hp⟩ := (fiberMass_pos_iff _ _ (acceptedGraphWeight_nonneg W hW s F) c.val).mp c.property
  exact ⟨γ, hcat, (acceptedGraphWeight_pos_iff W s F γ).mp hp⟩

def acceptedGraphRepresentative {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s : Q) (F : Finset Q) {n : ℕ}
    (c : AcceptedGraphCategory W s F n) : Fin (n + 1) → Q :=
  Classical.choose (acceptedGraphCategory_has_path W hW s F c)

theorem acceptedGraphRepresentative_spec {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s : Q) (F : Finset Q) {n : ℕ}
    (c : AcceptedGraphCategory W s F n) :
    let γ := acceptedGraphRepresentative W hW s F c
    graphCategory (fun x y => 0 < W x y) γ = c.val ∧
      γ 0 = s ∧ γ (Fin.last n) ∈ F ∧ 0 < edgePathWeight W γ :=
  Classical.choose_spec (acceptedGraphCategory_has_path W hW s F c)

theorem acceptedGraphCategory_nonempty {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s : Q) (F : Finset Q) (n : ℕ)
    (hZ : 0 < ∑ γ : Fin (n + 1) → Q, acceptedGraphWeight W s F γ) :
    Nonempty (AcceptedGraphCategory W s F n) := by
  classical
  obtain ⟨γ, _, hγ⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun γ _ => acceptedGraphWeight_nonneg W hW s F γ)).mp hZ
  exact ⟨⟨_, fiberMass_pos_of_weight_pos _ _ (acceptedGraphWeight_nonneg W hW s F) γ hγ⟩⟩

theorem acceptedGraphCategory_card_polynomial {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (s : Q) (F : Finset Q) (n : ℕ) :
    Fintype.card (AcceptedGraphCategory W s F n) ≤
      (Fintype.card Q * Fintype.card Q * (Fintype.card Q * Fintype.card Q + 1) ^ Fintype.card Q) *
        (n + 1) ^ Fintype.card Q :=
  (Fintype.card_subtype_le _).trans (graphCategory_card_polynomial n)

/-- The accepting event fixes only the start and final state, both already
recorded by a category. Its entire unnormalized fiber is exactly the
constructed block-boundary weight, including zero-weight paths. -/
theorem accepted_graph_category_fiber {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s : Q) (F : Finset Q) {n : ℕ}
    (γ : Fin (n + 1) → Q) (hstart : γ 0 = s) (hF : γ (Fin.last n) ∈ F)
    (hγ : 0 < edgePathWeight W γ) :
    fiberWeight (graphCategory (fun x y => 0 < W x y)) (acceptedGraphWeight W s F)
      (graphCategory (fun x y => 0 < W x y) γ) =
      fun η => if CategoryBlockMatches (fun x y => 0 < W x y) γ η then edgePathWeight W η else 0 := by
  classical
  funext η
  have hg := (edgePathWeight_pos_iff W hW γ).mp hγ
  have hbase : (if graphCategory (fun x y => 0 < W x y) γ = graphCategory (fun x y => 0 < W x y) η
      then edgePathWeight W η else 0) =
      (if CategoryBlockMatches (fun x y => 0 < W x y) γ η then edgePathWeight W η else 0) := by
    have hb := category_path_weight_constructed_blocks (fun _ => 1) W hW γ η hg
    by_cases hc : graphCategory (fun x y => 0 < W x y) γ = graphCategory (fun x y => 0 < W x y) η
    · simpa only [if_pos hc, edgePathWeight, one_mul] using hb
    · simpa only [if_neg hc, edgePathWeight, one_mul] using hb
  rw [← hbase]
  unfold fiberWeight
  by_cases hc : graphCategory (fun x y => 0 < W x y) η = graphCategory (fun x y => 0 < W x y) γ
  · have hi : η 0 = γ 0 := congrArg (fun c : GraphCategory Q n => c.1) hc
    have ht : η (Fin.last n) = γ (Fin.last n) := congrArg (fun c : GraphCategory Q n => c.2.1) hc
    rw [if_pos hc, if_pos hc.symm, acceptedGraphWeight, if_pos ⟨hi.trans hstart, ht ▸ hF⟩]
  · rw [if_neg hc, if_neg (Ne.symm hc)]







end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_AcceptedGraphSelector
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

local instance acceptedGraphSelectorDecEq {Q : Type} [Fintype Q] {n : ℕ} :
    DecidableEq (GraphCategory Q n) := Classical.decEq _

def acceptedGraphChoiceLaw {Q : Type} [Fintype Q] [DecidableEq Q] {n : ℕ}
    (W : Q → Q → ℝ) (s : Q) (F : Finset Q) : AcceptedGraphCategory W s F n → ℝ :=
  normalizeWeights (fun c => fiberMass (graphCategory (fun x y => 0 < W x y))
    (acceptedGraphWeight W s F) c.val)

theorem acceptedGraphChoiceLaw_nonneg {Q : Type} [Fintype Q] [DecidableEq Q] {n : ℕ}
    (W : Q → Q → ℝ) (s : Q) (F : Finset Q) :
    ∀ c : AcceptedGraphCategory W s F n, 0 ≤ acceptedGraphChoiceLaw W s F c :=
  normalizeWeights_nonneg _ (fun c => c.property.le)

theorem acceptedGraphChoiceLaw_sum {Q : Type} [Fintype Q] [DecidableEq Q] {n : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s : Q) (F : Finset Q)
    (hZ : 0 < ∑ γ : Fin (n + 1) → Q, acceptedGraphWeight W s F γ) :
    ∑ c : AcceptedGraphCategory W s F n, acceptedGraphChoiceLaw W s F c = 1 := by
  apply normalizeWeights_sum
  rw [positiveFiber_mass_sum _ _ (acceptedGraphWeight_nonneg W hW s F)]
  exact hZ

def acceptedGraphChoiceSeed {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (s : Q) (F : Finset Q) (n : ℕ) (ε : ℝ) : ℕ :=
  roundingSeed (Fintype.card (AcceptedGraphCategory W s F n)) (ε / 2)

def acceptedGraphChoiceSize {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (s : Q) (F : Finset Q) (n : ℕ) (ε : ℝ) : ℕ :=
  let c := Fintype.card (AcceptedGraphCategory W s F n)
  let r := acceptedGraphChoiceSeed W s F n ε
  r + c * (c * (2 * (r * (3 * r + 2) + 1) + 6) + 2)

/-- An actual category selector for arbitrary nonnegative graph weights.
Its only acceptance assumption is that at least one accepted path has
positive weight; missing transitions are not renormalized. -/
theorem accepted_graph_category_selector {Q : Type} [Fintype Q] [DecidableEq Q] {n : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s : Q) (F : Finset Q)
    (hZ : 0 < ∑ γ : Fin (n + 1) → Q, acceptedGraphWeight W s F γ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : Bits (acceptedGraphChoiceSeed W s F n ε) → AcceptedGraphCategory W s F n,
      ∃ A : Circuit (AcceptedGraphCategory W s F n),
      ∃ hbits : A.randomBits = acceptedGraphChoiceSeed W s F n ε,
      (∀ seed c, A.eval (fun j => seed (Fin.cast hbits j)) c = decide (f seed = c)) ∧
      tv (finiteSeedLaw f) (acceptedGraphChoiceLaw W s F) ≤ ε / 2 ∧
      A.depth ≤ 6 ∧ A.size ≤ acceptedGraphChoiceSize W s F n ε := by
  classical
  obtain ⟨f, A, hbits, he, _, htv, hD, hsize⟩ := rounding_AC0_function
    (fun c d : AcceptedGraphCategory W s F n => decide (c = d)) (acceptedGraphChoiceLaw W s F)
    (acceptedGraphChoiceLaw_nonneg W s F) (acceptedGraphChoiceLaw_sum W hW s F hZ)
    (ε / 2) (by positivity)
  exact ⟨f, A, hbits, fun seed c => congrFun (he seed) c, htv, hD, hsize⟩

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SCCEndpointSampling
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

def mapEndpointPath {H Q : Type} (embed : H → Q) {s t : H} {n : ℕ}
    (γ : EndpointPath H s t n) : EndpointPath Q (embed s) (embed t) n :=
  ⟨fun i => embed (γ.val i), ⟨congrArg embed γ.property.1, congrArg embed γ.property.2⟩⟩

/-- Viewing a fixed-endpoint sampler in the ambient path space preserves
the entire TV distance to the bridge law, with no positivity denominator. -/
theorem endpoint_sampler_ambient_tv {Q : Type} [Fintype Q] [DecidableEq Q] {m n : ℕ}
    (W : Q → Q → ℝ) (s t : Q) (f : Bits m → EndpointPath Q s t n) :
    tv (finiteSeedLaw f) (normalizeWeights (fun γ : EndpointPath Q s t n => edgePathWeight W γ.val)) =
      tv (finiteSeedLaw (fun seed => (f seed).val)) (normalizeWeights (bridgeWeight W s t n)) := by
  let P := fun γ : Fin (n + 1) → Q => γ 0 = s ∧ γ (Fin.last n) = t
  have h := tv_subtypeSeedSample P (fun seed => (f seed).val) (fun seed => (f seed).property)
    (normalizeWeights (bridgeWeight W s t n)) (by
      intro γ hγ
      change ¬ (γ 0 = s ∧ γ (Fin.last n) = t) at hγ
      simp only [normalizeWeights, bridgeWeight, if_neg hγ, zero_div])
  have hn : normalizeWeights (fun γ : EndpointPath Q s t n => edgePathWeight W γ.val) =
      fun γ => normalizeWeights (bridgeWeight W s t n) γ.val := funext (normalized_endpoint_bridge W s t n)
  rw [hn]
  exact h

theorem scc_endpoint_sample_positive {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (s : Q) {x y : SCCState W s} {n : ℕ}
    (γ : EndpointPath (SCCState W s) x y n)
    (hγ : 0 < edgePathWeight (fun i j => sccMatrix W s i j) γ.val) :
    0 < edgePathWeight (fun i j => W i j) (mapEndpointPath Subtype.val γ).val := hγ

/-- Sampling inside the actual SCC and forgetting subtype annotations
approximates the complete original endpoint bridge. No probability of
remaining inside the component is divided out: that support is exact. -/
theorem scc_endpoint_sampler_error {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j) (s : Q)
    (x y : SCCState W s) {m n : ℕ} (f : Bits m → EndpointPath (SCCState W s) x y n) :
    tv (finiteSeedLaw (fun seed => mapEndpointPath Subtype.val (f seed)))
      (normalizeWeights (fun γ : EndpointPath Q x.val y.val n => edgePathWeight (fun i j => W i j) γ.val)) ≤
    tv (finiteSeedLaw f) (normalizeWeights
      (fun γ : EndpointPath (SCCState W s) x y n => edgePathWeight (fun i j => sccMatrix W s i j) γ.val)) := by
  rw [endpoint_sampler_ambient_tv, endpoint_sampler_ambient_tv]
  let embed := fun γ : Fin (n + 1) → SCCState W s => fun i => (γ i).val
  let fval := fun seed => (f seed).val
  have ht := tv_map_le embed (finiteSeedLaw fval)
    (normalizeWeights (bridgeWeight (fun i j => sccMatrix W s i j) x y n))
  have hnorm : (fun γ => ∑ z, if embed z = γ then
      normalizeWeights (bridgeWeight (fun i j => sccMatrix W s i j) x y n) z else 0) =
      normalizeWeights (bridgeWeight (fun i j => W i j) x.val y.val n) := by
    funext γ
    exact normalized_scc_bridge_law W hW s x y n γ
  rw [hnorm] at ht
  have hmap := finiteSeedLaw_map fval embed
  change finiteSeedLaw (embed ∘ fval) =
    (fun γ => ∑ z, if embed z = γ then finiteSeedLaw fval z else 0) at hmap
  rw [← hmap] at ht
  exact ht

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_CircuitProgramRecovery
section
set_option autoImplicit false
namespace FSS23105365

/-- Every valid gate list has an exact-level certified program. The
construction copies gates verbatim, rather than replacing the circuit by
an arbitrary extensionally equivalent Boolean function. -/
theorem exactProgram_of_gates (r : ℕ) (gs : List Gate)
    (hv : ∀ i : Fin gs.length, ∀ j ∈ (gs.get i).sources, j < r + i.val) :
    ∃ P : CircuitProgram r, P.gates = gs ∧
      ∀ i : Fin P.gates.length, gateDepthFn P.level (P.gates.get i) = P.level (r + i.val) := by
  revert hv
  induction gs using List.reverseRecOn with
  | nil =>
    intro hv
    exact ⟨emptyCircuitProgram r, rfl, fun i => Fin.elim0 i⟩
  | @append_singleton gs g ih =>
    intro hv
    have hvgs : ∀ i : Fin gs.length, ∀ j ∈ (gs.get i).sources, j < r + i.val := by
      intro i j hj
      have hi : i.val < (gs ++ [g]).length := by simp only [List.length_append, List.length_singleton]; omega
      have he : (gs ++ [g]).get ⟨i.val, hi⟩ = gs.get i := by
        simp only [List.get_eq_getElem, List.getElem_append_left i.isLt]
      exact hv ⟨i.val, hi⟩ j (by rw [he]; exact hj)
    obtain ⟨P, hP, hExact⟩ := ih hvgs
    subst gs
    have hg : ∀ j ∈ g.sources, j < r + P.gates.length := by
      intro j hj
      have hi : P.gates.length < (P.gates ++ [g]).length := by simp
      have he : (P.gates ++ [g]).get ⟨P.gates.length, hi⟩ = g := by simp [List.get_eq_getElem]
      exact hv ⟨P.gates.length, hi⟩ j (by rw [he]; exact hj)
    let R := appendCircuitGate P g hg
    refine ⟨R, rfl, ?_⟩
    intro i
    rcases get_append_gate_cases P.gates g i with ⟨j, hi, he⟩ | ⟨hi, he⟩
    · change gateDepthFn R.level ((P.gates ++ [g]).get i) = R.level (r + i.val)
      rw [he, hi, appendCircuitGate_level_old P g hg _ (by omega : r + j.val < r + P.gates.length)]
      exact (gateDepthFn_congr (P.gates.get j) R.level P.level (fun x hx =>
        appendCircuitGate_level_old P g hg x (by have := P.valid j x hx; omega))).trans (hExact j)
    · change gateDepthFn R.level ((P.gates ++ [g]).get i) = R.level (r + i.val)
      rw [he, hi, appendCircuitGate_level_new]
      exact gateDepthFn_congr g R.level P.level (fun x hx => appendCircuitGate_level_old P g hg x (hg x hx))

theorem exactProgram_register_levels {r : ℕ} (P : CircuitProgram r)
    (hExact : ∀ i : Fin P.gates.length, gateDepthFn P.level (P.gates.get i) = P.level (r + i.val)) :
    ∀ j < r + P.gates.length,
      (runRegisters (fun ds g => Gate.depth ds g) P.gates (List.replicate r 0)).getD j 0 = P.level j := by
  apply runRegisters_relation (fun ds g => Gate.depth ds g) Eq 0 P.level P.gates r
    (List.replicate r 0) (by simp)
  · intro j hj
    rw [P.input_level j hj]
    simp
  · intro i xs hxs hx
    change gateDepthFn (fun j => xs.getD j 0) (P.gates.get i) = _
    exact (gateDepthFn_congr (P.gates.get i) _ P.level (fun j hj =>
      hx j (by rw [hxs]; exact P.valid i j hj))).trans (hExact i)

theorem foldl_max_ge_initial (xs : List ℕ) (a : ℕ) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons x xs ih => exact (Nat.le_max_left a x).trans (ih (max a x))

theorem foldl_max_ge_member (xs : List ℕ) (a x : ℕ) (hx : x ∈ xs) : x ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with h | h
    · subst x
      exact (Nat.le_max_right a y).trans (foldl_max_ge_initial ys (max a y))
    · exact ih (max a y) h

/-- Exact certificates recover each output's true level from the actual
gate-depth interpreter, so no looser certificate inflates composition depth. -/
theorem exactProgram_output_level_le_depth {r : ℕ} {Out : Type} [Fintype Out]
    (P : CircuitProgram r) (out : Out → Fin (r + P.gates.length))
    (hExact : ∀ i : Fin P.gates.length, gateDepthFn P.level (P.gates.get i) = P.level (r + i.val))
    (o : Out) : P.level (out o).val ≤ (programCircuit P out).depth := by
  classical
  let ds := runRegisters (fun ds g => Gate.depth ds g) P.gates (List.replicate r 0)
  have he : ds.getD (out o).val 0 = P.level (out o).val :=
    exactProgram_register_levels P hExact _ (out o).isLt
  rw [← he]
  apply foldl_max_ge_member
  apply List.mem_ofFn.mpr
  exact ⟨(Fintype.equivFin Out) o, by simp only [Equiv.symm_apply_apply]; rfl⟩

/-- Any previously constructed Circuit can now be reused by the verified
composition/parallel constructors, with identical gates and true output
depths. This includes the concrete rounding circuits from C.2. -/
theorem circuit_as_program {Out : Type} [Fintype Out] (C : Circuit Out) :
    ∃ P : CircuitProgram C.randomBits, ∃ out : Out → Fin (C.randomBits + P.gates.length),
      (∀ seed o, P.value seed (out o).val = C.eval seed o) ∧
      (∀ o, P.level (out o).val ≤ C.depth) ∧
      C.randomBits + programCost P + Fintype.card Out = C.size := by
  rcases C with ⟨r, gs, output, hv, ho⟩
  obtain ⟨P, hP, hExact⟩ := exactProgram_of_gates r gs hv
  subst gs
  let out := fun o => (⟨output o, ho o⟩ : Fin (r + P.gates.length))
  refine ⟨P, out, ?_, ?_, ?_⟩
  · intro seed o
    exact (congrFun (programCircuit_eval P out seed) o).symm
  · exact fun o => exactProgram_output_level_le_depth P out hExact o
  · simp only [programCost, Circuit.size, Nat.add_assoc]

end FSS23105365

end

-- Source module: Solutions.FSS23105365_CircuitAssembly
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- Rewire every input of an existing circuit to a chosen shared-seed
coordinate. The actual gate list is copied, preserving its output depths. -/
theorem circuit_rewired_program {Out : Type} [Fintype Out] (C : Circuit Out) {r : ℕ}
    (input : Fin C.randomBits → Fin r) :
    ∃ R : CircuitProgram r, ∃ out : Out → Fin (r + R.gates.length),
      (∀ seed o, R.value seed (out o).val = C.eval (fun j => seed (input j)) o) ∧
      (∀ o, R.level (out o).val ≤ C.depth) ∧
      C.randomBits + programCost R + Fintype.card Out = C.size := by
  obtain ⟨P, output, hv, hd, hc⟩ := circuit_as_program C
  let E := emptyCircuitProgram r
  let wires : Fin C.randomBits → Fin (r + E.gates.length) := input
  have hw : ∀ i, E.level (wires i).val ≤ 0 := fun _ => le_rfl
  let R := composeCircuitProgram E P wires 0 hw
  let out := fun o => composedOutput E P wires 0 hw (output o)
  refine ⟨R, out, ?_, ?_, ?_⟩
  · intro seed o
    have he := composeCircuitProgram_value_new E P wires 0 hw seed (output o).val
    have hi : (fun j => E.value seed (wires j).val) = fun j => seed (input j) := by
      funext j
      exact E.input_value seed (input j)
    rw [hi] at he
    exact he.trans (hv _ o)
  · intro o
    exact (composeCircuitProgram_level_new E P wires 0 hw (output o).val).trans
      (by simpa only [Nat.zero_add] using hd o)
  · have hcost := composeCircuitProgram_cost E P wires 0 hw
    change programCost R = programCost E + programCost P at hcost
    have hzero : programCost E = 0 := rfl
    rw [hzero, Nat.zero_add] at hcost
    rw [hcost]
    exact hc



/-- Any finite family of already-built circuits can run on fixed wires
of one shared seed. Output depth is bounded by the common leaf depth.
The explicit polynomial size bound permits gate duplication per output. -/
theorem parallel_circuit_family {I : Type} [Fintype I] [DecidableEq I]
    {Out : I → Type} [∀ i, Fintype (Out i)] (C : ∀ i, Circuit (Out i)) {r : ℕ}
    (input : ∀ i, Fin (C i).randomBits → Fin r) (D : ℕ) (hD : ∀ i, (C i).depth ≤ D) :
    ∃ S : Circuit (Σ i, Out i), ∃ hbits : S.randomBits = r,
      (∀ (seed : Bits r) i o, S.eval (fun j => seed (Fin.cast hbits j)) ⟨i, o⟩ =
        (C i).eval (fun j => seed (input i j)) o) ∧
      S.depth ≤ D ∧
      S.size ≤ r + (∑ i, Fintype.card (Out i) * (C i).size) + Fintype.card (Σ i, Out i) := by
  classical
  choose P out hv hd hc using fun i => circuit_rewired_program (C i) (input i)
  let e := Fintype.equivFin (Σ i, Out i)
  obtain ⟨R, output, hr, hrd, hrc⟩ := parallel_program_family
    (fun j => P (e.symm j).1) (fun j => out (e.symm j).1 (e.symm j).2) D
    (fun j => (hd (e.symm j).1 (e.symm j).2).trans (hD (e.symm j).1))
  let output' := fun z : Σ i, Out i => output (e z)
  have hcost : programCost R ≤ ∑ i, Fintype.card (Out i) * (C i).size := by
    calc
      _ = ∑ z : Σ i, Out i, programCost (P z.1) :=
        hrc.trans (e.symm.sum_comp (fun z : Σ i, Out i => programCost (P z.1)))
      _ ≤ ∑ z : Σ i, Out i, (C z.1).size := by
        apply Finset.sum_le_sum
        intro z _
        have h := hc z.1
        omega
      _ = _ := by
        rw [Fintype.sum_sigma]
        change (∑ i : I, ∑ _o : Out i, (C i).size) = _
        simp
  refine ⟨programCircuit R output', rfl, ?_,
    programCircuit_depth_le R output' D (fun z => hrd (e z)), ?_⟩
  · intro seed i o
    change (programCircuit R output').eval seed ⟨i, o⟩ = _
    rw [programCircuit_eval]
    have he := (hr seed (e ⟨i, o⟩)).trans (hv (e.symm (e ⟨i, o⟩)).1 seed (e.symm (e ⟨i, o⟩)).2)
    rw [e.symm_apply_apply] at he
    exact he
  · rw [programCircuit_size]
    unfold programCost at hcost
    omega



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_CircuitSequentialAssembly
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

/-- Actual circuit composition through selected output wires introduces
no new random bits, adds depths, and has at most the sum of the sizes. -/
theorem circuit_compose {Mid Out : Type} [Fintype Mid] [Fintype Out]
    (C : Circuit Mid) (B : Circuit Out) (input : Fin B.randomBits → Mid) :
    ∃ S : Circuit Out, ∃ hbits : S.randomBits = C.randomBits,
      (∀ (seed : Bits C.randomBits) o,
        S.eval (fun j => seed (Fin.cast hbits j)) o = B.eval (fun i => C.eval seed (input i)) o) ∧
      S.depth ≤ C.depth + B.depth ∧ S.size ≤ C.size + B.size := by
  obtain ⟨P, outP, hvP, hdP, hcP⟩ := circuit_as_program C
  obtain ⟨Q, outQ, hvQ, hdQ, hcQ⟩ := circuit_as_program B
  let wires := fun i => outP (input i)
  have hw : ∀ i, P.level (wires i).val ≤ C.depth := fun i => hdP (input i)
  let R := composeCircuitProgram P Q wires C.depth hw
  let out := fun o => composedOutput P Q wires C.depth hw (outQ o)
  refine ⟨programCircuit R out, rfl, ?_, ?_, ?_⟩
  · intro seed o
    have he := composeCircuitProgram_value_new P Q wires C.depth hw seed (outQ o).val
    have hi : (fun i => P.value seed (wires i).val) = fun i => C.eval seed (input i) := by
      funext i
      exact hvP seed (input i)
    rw [hi] at he
    exact (congrFun (programCircuit_eval R out seed) o).trans (he.trans (hvQ _ o))
  · apply programCircuit_depth_le
    intro o
    exact (composeCircuitProgram_level_new P Q wires C.depth hw (outQ o).val).trans
      (Nat.add_le_add_left (hdQ o) C.depth)
  · rw [programCircuit_size]
    have hcost := composeCircuitProgram_cost P Q wires C.depth hw
    change programCost R = programCost P + programCost Q at hcost
    unfold programCost at hcost hcP hcQ
    omega

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_CircuitMultiplexing
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def multiplexFormula {I : Type} [Fintype I] {r : ℕ}
    (select branch : I → Fin r) : CircuitFormula r :=
  formulaIndexedAny (fun i => formulaAnd (.input (select i)) (.input (branch i)))

theorem multiplexFormula_eval {I : Type} [Fintype I] [DecidableEq I] {r : ℕ}
    (select branch : I → Fin r) (seed : Bits r) (chosen : I)
    (hsel : ∀ i, seed (select i) = decide (chosen = i)) :
    formulaEval (multiplexFormula select branch) seed = seed (branch chosen) := by
  apply Bool.eq_iff_iff.mpr
  rw [multiplexFormula, formulaIndexedAny_eval]
  simp only [formulaAnd_eval, formulaEval, Bool.and_eq_true, hsel, decide_eq_true_eq]
  constructor
  · rintro ⟨i, rfl, hi⟩
    exact hi
  · intro h
    exact ⟨chosen, rfl, h⟩

theorem multiplexFormula_depth {I : Type} [Fintype I] {r : ℕ} (select branch : I → Fin r) :
    formulaDepth (multiplexFormula select branch) ≤ 2 := by
  apply formulaIndexedAny_depth _ 1
  intro i
  simp only [formulaAnd_depth, formulaDepth, Nat.max_self, Nat.zero_add, le_refl]

theorem multiplexFormula_cost {I : Type} [Fintype I] {r : ℕ} (select branch : I → Fin r) :
    formulaCost (multiplexFormula select branch) ≤ Fintype.card I * 4 + 1 := by
  apply formulaIndexedAny_cost _ 3
  intro i
  simp only [formulaAnd_cost, formulaCost, Nat.zero_add, le_refl]

/-- One-hot selection adds precisely two gate layers and polynomial
gate/wire cost. Branch outputs are already computed input wires. -/
theorem multiplexer_circuit {I Out : Type} [Fintype I] [DecidableEq I] [Fintype Out] {r : ℕ}
    (select : I → Fin r) (branch : I → Out → Fin r) :
    ∃ S : Circuit Out, ∃ hbits : S.randomBits = r,
      (∀ (seed : Bits r) (chosen : I), (∀ i, seed (select i) = decide (chosen = i)) →
        ∀ o, S.eval (fun j => seed (Fin.cast hbits j)) o = seed (branch chosen o)) ∧
      S.depth ≤ 2 ∧ S.size ≤ r + Fintype.card Out * (4 * Fintype.card I + 2) := by
  let fs := fun o => multiplexFormula select (fun i => branch i o)
  obtain ⟨S, hbits, he, hD, hsize⟩ := formula_fintype_family_circuit fs 2
    (fun o => multiplexFormula_depth select (fun i => branch i o))
  refine ⟨S, hbits, ?_, hD, ?_⟩
  · intro seed chosen hsel o
    exact (he seed o).trans (multiplexFormula_eval select (fun i => branch i o) seed chosen hsel)
  · have hsum := Finset.sum_le_sum (fun o (_ : o ∈ Finset.univ) =>
      multiplexFormula_cost select (fun i => branch i o))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    rw [hsize]
    change r + (∑ o, formulaCost (fs o)) + Fintype.card Out ≤ _
    nlinarith

/-- Attach the two-layer selector to an actual circuit that computes
category/endpoint selectors and branch outputs. No random inputs are added. -/
theorem circuit_select_outputs {I Mid Out : Type} [Fintype I] [DecidableEq I]
    [Fintype Mid] [Fintype Out] (C : Circuit Mid) (select : I → Mid) (branch : I → Out → Mid) :
    ∃ S : Circuit Out, ∃ hbits : S.randomBits = C.randomBits,
      (∀ (seed : Bits C.randomBits) (chosen : I),
        (∀ i, C.eval seed (select i) = decide (chosen = i)) →
        ∀ o, S.eval (fun j => seed (Fin.cast hbits j)) o = C.eval seed (branch chosen o)) ∧
      S.depth ≤ C.depth + 2 ∧
      S.size ≤ C.size + Fintype.card Mid + Fintype.card Out * (4 * Fintype.card I + 2) := by
  let e := Fintype.equivFin Mid
  obtain ⟨B, hBbits, hBeval, hBD, hBsize⟩ := multiplexer_circuit
    (fun i => e (select i)) (fun i o => e (branch i o))
  let input := fun j : Fin B.randomBits => e.symm (Fin.cast hBbits j)
  obtain ⟨S, hbits, he, hD, hsize⟩ := circuit_compose C B input
  refine ⟨S, hbits, ?_, hD.trans (Nat.add_le_add_left hBD C.depth), ?_⟩
  · intro seed chosen hsel o
    rw [he]
    have hs : ∀ i, (fun j => C.eval seed (e.symm j)) (e (select i)) = decide (chosen = i) := by
      simpa only [Equiv.symm_apply_apply] using hsel
    have hh := hBeval (fun j => C.eval seed (e.symm j)) chosen hs o
    simpa only [input, Equiv.symm_apply_apply] using hh
  · omega

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SubtypeStateCircuit
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- Embed one-hot subtype states into the original state alphabet. States
outside the subtype receive a constant false wire; states inside reuse
the corresponding existing output. The seed is unchanged. -/
theorem subtype_state_circuit {I Q : Type} [Fintype I] [Fintype Q] [DecidableEq Q]
    (P : Q → Prop) [DecidablePred P] (C : Circuit (I × {x // P x}))
    (f : Bits C.randomBits → (I → {x // P x}))
    (hC : ∀ seed i x, C.eval seed (i, x) = decide (f seed i = x)) :
    ∃ S : Circuit (I × Q), ∃ hbits : S.randomBits = C.randomBits,
      (∀ (seed : Bits C.randomBits) i x,
        S.eval (fun j => seed (Fin.cast hbits j)) (i, x) = decide ((f seed i).val = x)) ∧
      S.depth ≤ C.depth + 1 ∧
      S.size ≤ C.size + Fintype.card I * Fintype.card {x // P x} + 2 * (Fintype.card I * Fintype.card Q) := by
  let e := Fintype.equivFin (I × {x // P x})
  let fs : (I × Q) → CircuitFormula (Fintype.card (I × {x // P x})) := fun o =>
    if h : P o.2 then .input (e (o.1, ⟨o.2, h⟩)) else .constant false
  have hfd : ∀ o, formulaDepth (fs o) ≤ 1 := by
    intro o
    dsimp only [fs]
    split_ifs <;> simp only [formulaDepth, Nat.zero_le, le_refl]
  obtain ⟨B, hBbits, hBe, hBD, hBsize⟩ := formula_fintype_family_circuit fs 1 hfd
  let input := fun j : Fin B.randomBits => e.symm (Fin.cast hBbits j)
  obtain ⟨S, hbits, he, hD, hsize⟩ := circuit_compose C B input
  refine ⟨S, hbits, ?_, hD.trans (Nat.add_le_add_left hBD C.depth), ?_⟩
  · intro seed i x
    rw [he]
    have hb := hBe (fun j => C.eval seed (e.symm j)) (i, x)
    change B.eval (fun j => C.eval seed (input j)) (i, x) = _ at hb
    rw [hb]
    dsimp only [fs]
    split_ifs with hx
    · simp only [formulaEval, Equiv.symm_apply_apply, hC, Subtype.ext_iff]
    · have hn : (f seed i).val ≠ x := fun h => hx (h ▸ (f seed i).property)
      simp only [formulaEval, hn, decide_false]
  · have hfc : ∀ o, formulaCost (fs o) ≤ 1 := by
      intro o
      dsimp only [fs]
      split_ifs <;> simp only [formulaCost, Nat.zero_le, le_refl]
    have hs := Finset.sum_le_sum (fun o (_ : o ∈ Finset.univ) => hfc o)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id,
      mul_one, Fintype.card_prod] at hs
    simp only [Fintype.card_prod] at hBsize
    omega

theorem subtype_state_circuit_budget {I Q : Type} [Fintype I] [Fintype Q] [DecidableEq Q]
    {r : ℕ} (P : Q → Prop) [DecidablePred P] (C : Circuit (I × {x // P x}))
    (hCbits : C.randomBits = r) (f : Bits r → (I → {x // P x}))
    (hC : ∀ seed i x, C.eval (fun j => seed (Fin.cast hCbits j)) (i, x) = decide (f seed i = x)) :
    ∃ S : Circuit (I × Q), ∃ hbits : S.randomBits = r,
      (∀ (seed : Bits r) i x,
        S.eval (fun j => seed (Fin.cast hbits j)) (i, x) = decide ((f seed i).val = x)) ∧
      S.depth ≤ C.depth + 1 ∧
      S.size ≤ C.size + Fintype.card I * Fintype.card {x // P x} + 2 * (Fintype.card I * Fintype.card Q) := by
  subst r
  exact subtype_state_circuit P C f hC

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_BoundaryPairCircuits
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def addressedState {I Q : Type} (a : Q ⊕ I) (y : I → Q) : Q :=
  match a with | Sum.inl s => s | Sum.inr i => y i

def addressedStateFormula {I Q : Type} [DecidableEq Q] {r : ℕ}
    (wire : I × Q → Fin r) (a : Q ⊕ I) (x : Q) : CircuitFormula r :=
  match a with | Sum.inl s => .constant (decide (s = x)) | Sum.inr i => .input (wire (i, x))

theorem addressedStateFormula_eval {I Q : Type} [DecidableEq Q] {r : ℕ}
    (wire : I × Q → Fin r) (a : Q ⊕ I) (x : Q) (seed : Bits r) (y : I → Q)
    (hy : ∀ i x, seed (wire (i, x)) = decide (y i = x)) :
    formulaEval (addressedStateFormula wire a x) seed = decide (addressedState a y = x) := by
  cases a with
  | inl s => rfl
  | inr i => exact hy i x

theorem addressedStateFormula_bounds {I Q : Type} [DecidableEq Q] {r : ℕ}
    (wire : I × Q → Fin r) (a : Q ⊕ I) (x : Q) :
    formulaDepth (addressedStateFormula wire a x) ≤ 1 ∧
      formulaCost (addressedStateFormula wire a x) ≤ 1 := by
  cases a <;> simp only [addressedStateFormula, formulaDepth, formulaCost, le_refl, Nat.zero_le, and_self]

/-- Select two state coordinates or fixed states from an existing one-hot
state circuit, and form their one-hot pair with constant depth overhead. -/
theorem addressed_pair_circuit {I Q : Type} [Fintype I] [Fintype Q] [DecidableEq Q]
    (C : Circuit (I × Q)) (f : Bits C.randomBits → (I → Q))
    (hC : ∀ seed i x, C.eval seed (i, x) = decide (f seed i = x)) (left right : Q ⊕ I) :
    ∃ S : Circuit (Q × Q), ∃ hbits : S.randomBits = C.randomBits,
      (∀ (seed : Bits C.randomBits) z,
        S.eval (fun j => seed (Fin.cast hbits j)) z =
          decide ((addressedState left (f seed), addressedState right (f seed)) = z)) ∧
      S.depth ≤ C.depth + 2 ∧
      S.size ≤ C.size + Fintype.card I * Fintype.card Q + 6 * (Fintype.card Q * Fintype.card Q) := by
  let e := Fintype.equivFin (I × Q)
  let fs := fun z : Q × Q => formulaAnd
    (addressedStateFormula e left z.1) (addressedStateFormula e right z.2)
  have hd : ∀ z, formulaDepth (fs z) ≤ 2 := by
    intro z
    rw [formulaAnd_depth]
    have hl := (addressedStateFormula_bounds e left z.1).1
    have hr := (addressedStateFormula_bounds e right z.2).1
    omega
  obtain ⟨B, hBbits, hBeval, hBD, hBsize⟩ := formula_fintype_family_circuit fs 2 hd
  let input := fun j : Fin B.randomBits => e.symm (Fin.cast hBbits j)
  obtain ⟨S, hbits, he, hD, hsize⟩ := circuit_compose C B input
  refine ⟨S, hbits, ?_, hD.trans (Nat.add_le_add_left hBD C.depth), ?_⟩
  · intro seed z
    rw [he]
    have h := hBeval (fun j => C.eval seed (e.symm j)) z
    change B.eval (fun j => C.eval seed (input j)) z = _ at h
    rw [h, formulaAnd_eval]
    have hs : ∀ i x, (fun j => C.eval seed (e.symm j)) (e (i, x)) = decide (f seed i = x) := by
      intro i x
      simpa only [Equiv.symm_apply_apply] using hC seed i x
    rw [addressedStateFormula_eval e left z.1 _ (f seed) hs,
      addressedStateFormula_eval e right z.2 _ (f seed) hs]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq, Prod.ext_iff]
  · have hc : ∀ z, formulaCost (fs z) ≤ 5 := by
      intro z
      rw [formulaAnd_cost]
      have hl := (addressedStateFormula_bounds e left z.1).2
      have hr := (addressedStateFormula_bounds e right z.2).2
      omega
    have hs := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) => hc z)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id, Fintype.card_prod] at hs
    simp only [Fintype.card_prod] at hBsize
    omega

theorem boundary_pair_circuit {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (C : Circuit (Fin k × Q)) (f : Bits C.randomBits → (Fin k → Q))
    (hC : ∀ seed i x, C.eval seed (i, x) = decide (f seed i = x))
    (s t : Q) (i : Fin (k + 1)) :
    ∃ S : Circuit (Q × Q), ∃ hbits : S.randomBits = C.randomBits,
      (∀ (seed : Bits C.randomBits) z,
        S.eval (fun j => seed (Fin.cast hbits j)) z =
          decide (((Fin.cons s (f seed) : Fin (k + 1) → Q) i,
            (Fin.snoc (f seed) t : Fin (k + 1) → Q) i) = z)) ∧
      S.depth ≤ C.depth + 2 ∧ S.size ≤ C.size + k * Fintype.card Q + 6 * (Fintype.card Q * Fintype.card Q) := by
  let left : Q ⊕ Fin k := Fin.cases (Sum.inl s) (fun j => Sum.inr j) i
  let right : Q ⊕ Fin k := Fin.lastCases (Sum.inl t) (fun j => Sum.inr j) i
  obtain ⟨S, hbits, he, hD, hsize⟩ := addressed_pair_circuit C f hC left right
  refine ⟨S, hbits, ?_, hD, by simpa only [Fintype.card_fin] using hsize⟩
  intro seed z
  rw [he]
  have hl : addressedState left (f seed) = (Fin.cons s (f seed) : Fin (k + 1) → Q) i := by
    dsimp only [left]
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  have hr : addressedState right (f seed) = (Fin.snoc (f seed) t : Fin (k + 1) → Q) i := by
    dsimp only [right]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last, addressedState, Fin.snoc_last]
    · simp only [Fin.lastCases_castSucc, addressedState, Fin.snoc_castSucc]
  rw [hl, hr]

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SharedConditionalSeeds
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

theorem uniformSourceLaw_ignore_right {U V Ω : Type} [Fintype U] [Fintype V] [Nonempty V]
    [DecidableEq Ω] (f : U → Ω) :
    uniformSourceLaw (fun uv : U × V => f uv.1) = uniformSourceLaw f := by
  funext x
  let e : {uv : U × V // f uv.1 = x} ≃ {u : U // f u = x} × V := {
    toFun := fun uv => (⟨uv.val.1, uv.property⟩, uv.val.2)
    invFun := fun uv => ⟨(uv.1.val, uv.2), uv.1.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  unfold uniformSourceLaw
  rw [Fintype.card_congr e]
  simp only [Fintype.card_prod, Nat.cast_mul]
  exact mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr Fintype.card_pos.ne')

/-- Extending a sampler's available seed only adds ignored input wires. -/
def paddedSeedSample {Ω : Type} {m M : ℕ} (f : Bits m → Ω) (hm : m ≤ M) : Bits M → Ω :=
  fun seed => f (fun i => seed (Fin.castLE hm i))

theorem paddedSeedSample_law {Ω : Type} [Fintype Ω] [DecidableEq Ω] {m M : ℕ}
    (f : Bits m → Ω) (hm : m ≤ M) : finiteSeedLaw (paddedSeedSample f hm) = finiteSeedLaw f := by
  classical
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [← uniformSourceLaw_bits]
  have he := uniformSourceLaw_reindex (seedPairEquiv m n) (fun uv => f uv.1)
  change uniformSourceLaw (paddedSeedSample f hm) = _ at he
  rw [he, uniformSourceLaw_ignore_right, uniformSourceLaw_bits]

def sharedConditionalSeedSample {C Ω : Type} {r M : ℕ} (m : C → ℕ)
    (hm : ∀ c, m c ≤ M) (f : Bits r → C) (g : ∀ c, Bits (m c) → Ω) : Bits (r + M) → Ω :=
  sequentialSeedSample f (fun c => paddedSeedSample (g c) (hm c))

/-- The conditional budget is the maximum across branches: independent
category bits plus one shared padded seed realize the exact mixture of
branch laws, even when different categories need different bit counts. -/
theorem sharedConditionalSeedSample_law {C Ω : Type} [Fintype C] [Fintype Ω]
    [DecidableEq C] [DecidableEq Ω] {r M : ℕ} (m : C → ℕ)
    (hm : ∀ c, m c ≤ M) (f : Bits r → C) (g : ∀ c, Bits (m c) → Ω) :
    finiteSeedLaw (sharedConditionalSeedSample m hm f g) =
      mixtureLaw (finiteSeedLaw f) (fun c => finiteSeedLaw (g c)) := by
  rw [sharedConditionalSeedSample, sequentialSeedSample_law]
  simp only [paddedSeedSample_law]

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ConditionalCircuitAssembly
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- An actual one-hot selector followed by conditional branch circuits.
All branches reuse the same M input slots; only the selector seed is
separate. The final multiplexer adds two layers after parallel evaluation. -/
theorem conditional_circuit_assembly {I Out : Type} [Fintype I] [DecidableEq I] [Fintype Out]
    (A : Circuit I) (B : I → Circuit Out) (f : Bits A.randomBits → I)
    (hselect : ∀ seed i, A.eval seed i = decide (f seed = i))
    (M D : ℕ) (hm : ∀ i, (B i).randomBits ≤ M) (hD : ∀ i, (B i).depth ≤ D) :
    ∃ S : Circuit Out, ∃ hbits : S.randomBits = A.randomBits + M,
      (∀ (seed : Bits (A.randomBits + M)) o,
        S.eval (fun j => seed (Fin.cast hbits j)) o =
          (B (f (seedPairEquiv A.randomBits M seed).1)).eval
            (fun j => (seedPairEquiv A.randomBits M seed).2
              (Fin.castLE (hm (f (seedPairEquiv A.randomBits M seed).1)) j)) o) ∧
      S.depth ≤ max A.depth D + 2 ∧
      S.size ≤ (A.randomBits + M) + Fintype.card I * A.size +
        Fintype.card Out * (∑ i, (B i).size) +
        2 * (Fintype.card I + Fintype.card I * Fintype.card Out) +
        Fintype.card Out * (4 * Fintype.card I + 2) := by
  classical
  let LeafOut : Option I → Type := fun i => match i with | none => I | some _ => Out
  letI : ∀ i, Fintype (LeafOut i) := fun i => by cases i <;> dsimp only [LeafOut] <;> infer_instance
  let Leaf : ∀ i, Circuit (LeafOut i) := fun i => match i with | none => A | some c => B c
  let input : ∀ i, Fin (Leaf i).randomBits → Fin (A.randomBits + M) := fun i =>
    match i with
    | none => Fin.castAdd M
    | some c => fun j => Fin.natAdd A.randomBits (Fin.castLE (hm c) j)
  have hLeafD : ∀ i, (Leaf i).depth ≤ max A.depth D := by
    intro i
    cases i with
    | none => exact Nat.le_max_left _ _
    | some c => exact (hD c).trans (Nat.le_max_right _ _)
  obtain ⟨F, hFbits, hFeval, hFD, hFsize⟩ := parallel_circuit_family Leaf input _ hLeafD
  let select : I → (Σ i, LeafOut i) := fun i => ⟨none, i⟩
  let branch : I → Out → (Σ i, LeafOut i) := fun i o => ⟨some i, o⟩
  obtain ⟨S, hSbits, hSeval, hSD, hSsize⟩ := circuit_select_outputs F select branch
  refine ⟨S, hSbits.trans hFbits, ?_, hSD.trans (Nat.add_le_add_right hFD 2), ?_⟩
  · intro seed o
    let seedF := fun j => seed (Fin.cast hFbits j)
    let chosen := f (seedPairEquiv A.randomBits M seed).1
    have hsel : ∀ i, F.eval seedF (select i) = decide (chosen = i) := by
      intro i
      exact (hFeval seed none i).trans (hselect (seedPairEquiv A.randomBits M seed).1 i)
    have he := (hSeval seedF chosen hsel o).trans (hFeval seed (some chosen) o)
    have hseed : (fun j => seed (Fin.cast hFbits (Fin.cast hSbits j))) =
        fun j => seed (Fin.cast (hSbits.trans hFbits) j) := by
      funext j
      congr 1
    dsimp only [seedF] at he
    rw [hseed] at he
    exact he
  · have hcard : Fintype.card (Σ i, LeafOut i) = Fintype.card I + Fintype.card I * Fintype.card Out := by
      let e : (Σ i, LeafOut i) ≃ I ⊕ (I × Out) := {
        toFun := fun z => match z with | ⟨none, i⟩ => Sum.inl i | ⟨some i, o⟩ => Sum.inr (i, o)
        invFun := fun z => match z with | Sum.inl i => ⟨none, i⟩ | Sum.inr z => ⟨some z.1, z.2⟩
        left_inv := by rintro ⟨i, o⟩; cases i <;> rfl
        right_inv := by intro z; cases z <;> rfl }
      simpa only [Fintype.card_sum, Fintype.card_prod] using Fintype.card_congr e
    have hcost : (∑ i, Fintype.card (LeafOut i) * (Leaf i).size) =
        Fintype.card I * A.size + Fintype.card Out * (∑ i, (B i).size) := by
      rw [Fintype.sum_option]
      simp only [LeafOut, Leaf, Finset.mul_sum]
    rw [hcard, hcost] at hFsize
    rw [hcard] at hSsize
    omega

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SharedPrefixWiring
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- All blocks read the same prefix and disjoint local tails. Only one
copy of the prefix is charged in the global random-input count. -/
def sharedPrefixSlot {I : Type} [Fintype I] [DecidableEq I] (r : ℕ) (m : I → ℕ) (i : I) :
    Fin (r + m i) → Fin (r + ∑ j, m j) :=
  Fin.addCases (Fin.castAdd (∑ j, m j)) (fun j => Fin.natAdd r (seedSlot m i j))

theorem sharedPrefixSlot_split {I : Type} [Fintype I] [DecidableEq I]
    (r : ℕ) (m : I → ℕ) (i : I) (seed : Bits (r + ∑ j, m j)) :
    seedPairEquiv r (m i) (fun j => seed (sharedPrefixSlot r m i j)) =
      ((seedPairEquiv r (∑ j, m j) seed).1,
        seedSlotsEquiv m (seedPairEquiv r (∑ j, m j) seed).2 i) := by
  apply Prod.ext <;> funext j
  · simp only [seedPairEquiv, Equiv.coe_fn_mk, sharedPrefixSlot, Fin.addCases_left]
  · simp only [seedPairEquiv, Equiv.coe_fn_mk, sharedPrefixSlot, Fin.addCases_right, seedSlotsEquiv]

theorem shared_prefix_circuit_family {I : Type} [Fintype I] [DecidableEq I]
    {Out : I → Type} [∀ i, Fintype (Out i)] (r : ℕ) (m : I → ℕ)
    (C : ∀ i, Circuit (Out i)) (hbits : ∀ i, (C i).randomBits = r + m i)
    (D : ℕ) (hD : ∀ i, (C i).depth ≤ D) :
    ∃ S : Circuit (Σ i, Out i), ∃ hSbits : S.randomBits = r + ∑ i, m i,
      (∀ (seed : Bits (r + ∑ i, m i)) i o,
        S.eval (fun j => seed (Fin.cast hSbits j)) ⟨i, o⟩ =
          (C i).eval (fun j => seed (sharedPrefixSlot r m i (Fin.cast (hbits i) j))) o) ∧
      S.depth ≤ D ∧
      S.size ≤ (r + ∑ i, m i) + (∑ i, Fintype.card (Out i) * (C i).size) + Fintype.card (Σ i, Out i) :=
  parallel_circuit_family C (fun i j => sharedPrefixSlot r m i (Fin.cast (hbits i) j)) D hD

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_CircuitOutputWiring
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

/-- Selecting or repeating output wires adds no gate layer. The size
equation replaces only the charged output wires. -/
theorem circuit_output_wiring {Mid Out : Type} [Fintype Mid] [Fintype Out]
    (C : Circuit Mid) (wire : Out → Mid) :
    ∃ S : Circuit Out, ∃ hbits : S.randomBits = C.randomBits,
      (∀ (seed : Bits C.randomBits) o,
        S.eval (fun j => seed (Fin.cast hbits j)) o = C.eval seed (wire o)) ∧
      S.depth ≤ C.depth ∧ S.size + Fintype.card Mid = C.size + Fintype.card Out := by
  obtain ⟨P, out, hv, hd, hc⟩ := circuit_as_program C
  refine ⟨programCircuit P (out ∘ wire), rfl, ?_,
    programCircuit_depth_le P (out ∘ wire) C.depth (fun o => hd (wire o)), ?_⟩
  · intro seed o
    exact (congrFun (programCircuit_eval P (out ∘ wire) seed) o).trans (hv seed (wire o))
  · rw [programCircuit_size]
    unfold programCost at hc
    omega

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ConcatenationWiring
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

theorem boundaryBlockPath_map {Q R : Type} {k : ℕ} (l : Fin (k + 1) → ℕ)
    (γ : Fin (bridgeBlockLength l + 1) → Q) (f : Q → R) (i : Fin (k + 1)) :
    boundaryBlockPath l (f ∘ γ) i = f ∘ boundaryBlockPath l γ i := by
  induction k with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    rfl
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih (Fin.tail l) (pathRight γ) j

/-- This extracts a coordinate index, so it is a fixed wire and does not
depend on boundary states or on any random seed. -/
def boundaryBlockIndex {k : ℕ} (l : Fin (k + 1) → ℕ) (i : Fin (k + 1)) :
    Fin (l i + 1) → Fin (bridgeBlockLength l + 1) := boundaryBlockPath l id i

theorem boundaryBlockPath_index {Q : Type} {k : ℕ} (l : Fin (k + 1) → ℕ)
    (γ : Fin (bridgeBlockLength l + 1) → Q) (i : Fin (k + 1)) (j : Fin (l i + 1)) :
    boundaryBlockPath l γ i j = γ (boundaryBlockIndex l i j) :=
  congrFun (boundaryBlockPath_map l id γ i) j

theorem boundaryBlockIndex_surjective {k : ℕ} (l : Fin (k + 1) → ℕ) :
    Function.Surjective (fun z : Σ i, Fin (l i + 1) => boundaryBlockIndex l z.1 z.2) := by
  classical
  intro j
  by_contra h
  have hh : (fun _ : Fin (bridgeBlockLength l + 1) => false) = fun x => decide (x = j) := by
    apply boundaryBlockPath_injective l
    intro i
    funext t
    rw [boundaryBlockPath_index, boundaryBlockPath_index]
    have hn : boundaryBlockIndex l i t ≠ j := fun he => h ⟨⟨i, t⟩, he⟩
    simp only [hn, decide_false]
  have hf := congrFun hh j
  simp only [decide_true] at hf
  exact Bool.false_ne_true hf

def concatenationWire {k n : ℕ} (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n)
    (j : Fin (n + 1)) : Σ i, Fin (l i + 1) :=
  Classical.choose (boundaryBlockIndex_surjective l (Fin.cast (congrArg (fun n => n + 1) hlen.symm) j))

theorem concatenateBridgeBlocksAtLength_wire {Q : Type} {k n : ℕ}
    (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n)
    (s t : Q) (y : Fin k → Q) (b : BoundaryBlocks Q l s t y) (j : Fin (n + 1)) :
    concatenateBridgeBlocksAtLength l hlen s t y b j =
      (b (concatenationWire l hlen j).1).val (concatenationWire l hlen j).2 := by
  subst n
  let z := concatenationWire l rfl j
  have hz : boundaryBlockIndex l z.1 z.2 = j :=
    Classical.choose_spec (boundaryBlockIndex_surjective l j)
  have hb := congrArg (fun bs : BoundaryBlocks Q l s t y => (bs z.1).val)
    ((boundaryBlocksEquiv l s t y).apply_symm_apply b)
  have he := congrFun hb z.2
  change boundaryBlockPath l (concatenateBridgeBlocks l s t y b) z.1 z.2 = (b z.1).val z.2 at he
  rw [boundaryBlockPath_index, hz] at he
  exact he

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_RepeatedBoundaryCircuit
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- Independent copies of one boundary-state circuit use precisely k*m
bits and the same disjoint coordinate map as embeddedRepeatedSeedSample. -/
theorem repeated_boundary_circuit {A Q : Type} [Fintype Q] [DecidableEq Q] {m : ℕ}
    (k : ℕ) (embed : A → Q) (f : Bits m → A) (C : Circuit Q) (hCbits : C.randomBits = m)
    (hC : ∀ seed x, C.eval (fun j => seed (Fin.cast hCbits j)) x = decide (embed (f seed) = x)) :
    ∃ S : Circuit (Fin k × Q), ∃ hbits : S.randomBits = k * m,
      (∀ (seed : Bits (k * m)) i x,
        S.eval (fun j => seed (Fin.cast hbits j)) (i, x) =
          decide (embeddedRepeatedSeedSample k embed f seed i = x)) ∧
      S.depth ≤ C.depth ∧
      S.size ≤ k * m + (k * Fintype.card Q) * C.size + k * Fintype.card Q := by
  have hsum : (∑ _i : Fin k, m) = k * m := by simp
  let input := fun (i : Fin k) (j : Fin C.randomBits) =>
    Fin.cast hsum (seedSlot (fun _ : Fin k => m) i (Fin.cast hCbits j))
  obtain ⟨B, hBbits, hBe, hBD, hBsize⟩ := parallel_circuit_family (fun _ : Fin k => C)
    input C.depth (fun _ => le_rfl)
  let wire := fun o : Fin k × Q => (⟨o.1, o.2⟩ : Σ _i : Fin k, Q)
  obtain ⟨S, hSbits, hSe, hSD, hSsize⟩ := circuit_output_wiring B wire
  refine ⟨S, hSbits.trans hBbits, ?_, hSD.trans hBD, ?_⟩
  · intro seed i x
    let localSeed := seedSlotsEquiv (fun _ : Fin k => m) (fun j => seed (Fin.cast hsum j)) i
    have he := ((hSe (fun j => seed (Fin.cast hBbits j)) (i, x)).trans (hBe seed i x)).trans (hC localSeed x)
    have hseed : (fun j => seed (Fin.cast hBbits (Fin.cast hSbits j))) =
        fun j => seed (Fin.cast (hSbits.trans hBbits) j) := by
      funext j
      congr 1
    rw [hseed] at he
    exact he
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id,
      Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin] at hBsize hSsize
    simp only [Nat.mul_assoc] at hBsize ⊢
    omega

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_PeriodicBridgeCircuit
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix









def boundaryRoundingCircuitSize (q M : ℕ) (δ : ℝ) : ℕ :=
  let m := roundingSeed M δ
  m + q * (M * (2 * (m * (3 * m + 2) + 1) + 6) + 2)





end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SCCBridgeCircuit
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

theorem scc_endpoint_circuit_transport {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j) (s : Q)
    (x y : SCCState W s) {m n : ℕ} (f : Bits m → EndpointPath (SCCState W s) x y n)
    (C : Circuit (Fin (n + 1) × SCCState W s)) (hCbits : C.randomBits = m)
    (hCe : ∀ seed i z, C.eval (fun j => seed (Fin.cast hCbits j)) (i, z) = decide ((f seed).val i = z))
    (hpos : ∀ seed, 0 < edgePathWeight (fun i j => sccMatrix W s i j) (f seed).val)
    (δ : ℝ) (herr : tv (finiteSeedLaw f)
      (normalizeWeights (fun γ : EndpointPath (SCCState W s) x y n =>
        edgePathWeight (fun i j => sccMatrix W s i j) γ.val)) ≤ δ) :
    ∃ g : Bits m → EndpointPath Q x.val y.val n,
      ∃ S : Circuit (Fin (n + 1) × Q), ∃ hbits : S.randomBits = m,
      (∀ seed i z, S.eval (fun j => seed (Fin.cast hbits j)) (i, z) = decide ((g seed).val i = z)) ∧
      S.depth ≤ C.depth + 1 ∧
      S.size ≤ C.size + (n + 1) * Fintype.card (SCCState W s) + 2 * ((n + 1) * Fintype.card Q) ∧
      (∀ seed, 0 < edgePathWeight (fun i j => W i j) (g seed).val) ∧
      tv (finiteSeedLaw g) (normalizeWeights
        (fun γ : EndpointPath Q x.val y.val n => edgePathWeight (fun i j => W i j) γ.val)) ≤ δ := by
  let P := fun z => graphComponent (fun i j => 0 < W i j) z = graphComponent (fun i j => 0 < W i j) s
  obtain ⟨S, hbits, he, hD, hsize⟩ := subtype_state_circuit_budget P C hCbits (fun seed => (f seed).val) hCe
  refine ⟨fun seed => mapEndpointPath Subtype.val (f seed), S, hbits, he, hD, ?_, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using hsize
  · intro seed
    exact scc_endpoint_sample_positive W s (f seed) (hpos seed)
  · exact (scc_endpoint_sampler_error W hW s x y f).trans herr







end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_FixedBridgeBlocks
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- A zero- or one-edge path with specified endpoints has no internal
choice. This covers both acyclic singleton segments and crossing edges. -/
theorem endpointPath_subsingleton_short {Q : Type} (s t : Q) {n : ℕ} (hn : n ≤ 1) :
    Subsingleton (EndpointPath Q s t n) := by
  constructor
  intro γ η
  apply Subtype.ext
  funext i
  by_cases hi : i = 0
  · subst i
    exact γ.property.1.trans η.property.1.symm
  · have hilast : i = Fin.last n := Fin.ext (by
      have hz : i.val ≠ 0 := fun h => hi (Fin.ext h)
      have hb := i.isLt
      simp only [Fin.val_last]
      omega)
    subst i
    exact γ.property.2.trans η.property.2.symm

theorem normalized_short_bridge_one {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (s t : Q) {n : ℕ} (hn : n ≤ 1)
    (hpart : 0 < bridgePartition W s t n) (γ : EndpointPath Q s t n) :
    normalizeWeights (fun η : EndpointPath Q s t n => edgePathWeight W η.val) γ = 1 := by
  letI := endpointPath_subsingleton_short s t hn
  have hsum := normalizeWeights_sum (fun η : EndpointPath Q s t n => edgePathWeight W η.val)
    (by rw [endpointPath_weight_sum]; exact hpart)
  simpa only [Fintype.sum_subsingleton (a := γ)] using hsum

/-- The unique compatible path realizes the entire short bridge law
deterministically. No random draw is needed for a fixed crossing edge. -/
theorem short_bridge_deterministic_law {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) {n : ℕ} (hn : n ≤ 1)
    (hpart : 0 < bridgePartition W s t n) :
    ∃ γ : EndpointPath Q s t n, 0 < edgePathWeight W γ.val ∧
      ∀ η : EndpointPath Q s t n,
        (if γ = η then (1 : ℝ) else 0) =
          normalizeWeights (fun z : EndpointPath Q s t n => edgePathWeight W z.val) η := by
  classical
  have hs : 0 < ∑ γ : EndpointPath Q s t n, edgePathWeight W γ.val := by
    rw [endpointPath_weight_sum]
    exact hpart
  obtain ⟨γ, _, hγ⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun γ _ => edgePathWeight_nonneg W hW γ.val)).mp hs
  letI := endpointPath_subsingleton_short s t hn
  refine ⟨γ, hγ, fun η => ?_⟩
  rw [if_pos (Subsingleton.elim γ η), normalized_short_bridge_one W s t hn hpart η]

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_FixedBridgeCircuit
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

theorem finiteSeedLaw_constant {Ω : Type} [Fintype Ω] [DecidableEq Ω] (x y : Ω) :
    finiteSeedLaw (fun _ : Bits 0 => x) y = if x = y then 1 else 0 := by
  by_cases h : x = y <;> simp [finiteSeedLaw, Bits, h]

theorem constant_output_circuit {Out : Type} [Fintype Out] (value : Out → Bool) :
    ∃ S : Circuit Out, ∃ hbits : S.randomBits = 0,
      (∀ (seed : Bits 0) o, S.eval (fun j => seed (Fin.cast hbits j)) o = value o) ∧
      S.depth ≤ 1 ∧ S.size = 2 * Fintype.card Out := by
  let fs : Out → CircuitFormula 0 := fun o => .constant (value o)
  obtain ⟨S, hbits, he, hD, hsize⟩ := formula_fintype_family_circuit fs 1 (fun _ => le_rfl)
  refine ⟨S, hbits, he, hD, ?_⟩
  simp only [fs, formulaCost, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id,
    mul_one, Nat.zero_add] at hsize
  omega

/-- Fixed crossing edges and zero-length singleton segments have exact
zero-random-bit samplers and actual depth-one output circuits. -/
theorem fixed_bridge_circuit {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) {n : ℕ} (hn : n ≤ 1)
    (hpart : 0 < bridgePartition W s t n) :
    ∃ f : Bits 0 → EndpointPath Q s t n,
      ∃ S : Circuit (Fin (n + 1) × Q), ∃ hbits : S.randomBits = 0,
      (∀ seed i x, S.eval (fun j => seed (Fin.cast hbits j)) (i, x) = decide ((f seed).val i = x)) ∧
      S.depth ≤ 1 ∧ S.size = 2 * ((n + 1) * Fintype.card Q) ∧
      (∀ seed, 0 < edgePathWeight W (f seed).val) ∧
      finiteSeedLaw f = normalizeWeights (fun γ : EndpointPath Q s t n => edgePathWeight W γ.val) := by
  obtain ⟨γ, hγ, hγlaw⟩ := short_bridge_deterministic_law W hW s t hn hpart
  obtain ⟨S, hbits, he, hD, hsize⟩ := constant_output_circuit
    (fun o : Fin (n + 1) × Q => decide (γ.val o.1 = o.2))
  refine ⟨fun _ => γ, S, hbits, (fun seed i x => he seed (i, x)), hD,
    by simpa only [Fintype.card_prod, Fintype.card_fin] using hsize, fun _ => hγ, ?_⟩
  funext η
  rw [finiteSeedLaw_constant]
  exact hγlaw η

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_CertifiedBridgeSamplers
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

/-- One actual endpoint sampler and the circuit computing that same
function, with support and error certificates. Its seed length is free
to vary between fixed, short, and long segment constructions. -/
structure CertifiedBridgeSampler {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (s t : Q) (n : ℕ) (δ : ℝ) where
  seedLength : ℕ
  sample : Bits seedLength → EndpointPath Q s t n
  circuit : Circuit (Fin (n + 1) × Q)
  randomBits_eq : circuit.randomBits = seedLength
  eval_eq : ∀ seed i x, circuit.eval (fun j => seed (Fin.cast randomBits_eq j)) (i, x) =
    decide ((sample seed).val i = x)
  sample_positive : ∀ seed, 0 < edgePathWeight W (sample seed).val
  error : tv (finiteSeedLaw sample)
    (normalizeWeights (fun γ : EndpointPath Q s t n => edgePathWeight W γ.val)) ≤ δ



theorem certified_fixed_bridge {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) {n : ℕ} (hn : n ≤ 1)
    (hpart : 0 < bridgePartition W s t n) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∃ B : CertifiedBridgeSampler W s t n δ,
      B.seedLength = 0 ∧ B.circuit.depth ≤ 1 ∧ B.circuit.size = 2 * ((n + 1) * Fintype.card Q) := by
  obtain ⟨f, S, hbits, he, hD, hsize, hf, hlaw⟩ := fixed_bridge_circuit W hW s t hn hpart
  have herr : tv (finiteSeedLaw f)
      (normalizeWeights (fun γ : EndpointPath Q s t n => edgePathWeight W γ.val)) ≤ δ := by
    rw [hlaw]
    simpa only [tv, sub_self, abs_zero, Finset.sum_const_zero, zero_div] using hδ
  exact ⟨{ seedLength := 0
           sample := f
           circuit := S
           randomBits_eq := hbits
           eval_eq := he
           sample_positive := hf
           error := herr }, rfl, hD, hsize⟩

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_CategoryBridgeApproximation
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators



abbrev CategoryBridgeBlockPath {Q : Type} [Fintype Q] (R : Q → Q → Prop)
    {n : ℕ} (γ : Fin (n + 1) → Q) (i : Fin ((graphInteriorCuts R γ).card + 1)) :=
  BridgeBlockPath Q (graphCategoryBlockLengths R γ) (γ 0) (γ (Fin.last n))
    (bridgeBoundaryObservation (graphCategoryBlockLengths R γ) (graphCategoryBlockLengths_total R γ) γ) i

def categoryApproximateLaw {Q : Type} [Fintype Q] [DecidableEq Q] (R : Q → Q → Prop)
    {n : ℕ} (γ : Fin (n + 1) → Q) (p : ∀ i, CategoryBridgeBlockPath R γ i → ℝ) :
    (Fin (n + 1) → Q) → ℝ :=
  concatenateBlockLaw (graphCategoryBlockLengths R γ) (graphCategoryBlockLengths_total R γ)
    (γ 0) (γ (Fin.last n))
    (bridgeBoundaryObservation (graphCategoryBlockLengths R γ) (graphCategoryBlockLengths_total R γ) γ) p

theorem positive_observed_block_partitions {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) {k n : ℕ}
    (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n) (γ : Fin (n + 1) → Q)
    (hγ : 0 < edgePathWeight W γ) :
    ∀ i, 0 < bridgePartition W
      ((Fin.cons (γ 0) (bridgeBoundaryObservation l hlen γ) : Fin (k + 1) → Q) i)
      ((Fin.snoc (bridgeBoundaryObservation l hlen γ) (γ (Fin.last n)) : Fin (k + 1) → Q) i) (l i) := by
  subst n
  apply (bridgeBoundaryMass_pos_iff W hW l _ _ _).mp
  apply (bridgeBoundaryMass_pos_iff_path W hW l _ _ _).mpr
  have hs : bridgeBoundarySpec l (γ 0) (γ (Fin.last (bridgeBlockLength l)))
      (bridgeBoundaryObservation l rfl γ) γ := by
    rw [bridgeBoundarySpec_iff]
    exact ⟨rfl, rfl, rfl⟩
  exact ⟨⟨γ, hs⟩, hγ⟩

theorem approximate_constructed_category {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (R : Q → Q → Prop)
    {n : ℕ} (γ : Fin (n + 1) → Q) (hγ : 0 < edgePathWeight W γ)
    (p : ∀ i, CategoryBridgeBlockPath R γ i → ℝ)
    (hp : ∀ i b, 0 ≤ p i b) (hpsum : ∀ i, ∑ b, p i b = 1)
    (hsupp : ∀ i b, 0 < p i b → 0 < edgePathWeight W b.val)
    (δ : Fin ((graphInteriorCuts R γ).card + 1) → ℝ)
    (herror : ∀ i, tv (p i)
      (normalizeWeights (fun b : CategoryBridgeBlockPath R γ i => edgePathWeight W b.val)) ≤ δ i) :
    (∀ η, 0 ≤ categoryApproximateLaw R γ p η) ∧
    (∑ η, categoryApproximateLaw R γ p η = 1) ∧
    (∀ η, 0 < categoryApproximateLaw R γ p η →
      CategoryBlockMatches R γ η ∧ 0 < edgePathWeight W η) ∧
    tv (categoryApproximateLaw R γ p)
      (normalizeWeights (fun η => if CategoryBlockMatches R γ η then edgePathWeight W η else 0)) ≤
      ∑ i, δ i := by
  classical
  have h := approximate_concatenated_bridges W hW (graphCategoryBlockLengths R γ)
    (graphCategoryBlockLengths_total R γ) (γ 0) (γ (Fin.last n))
    (bridgeBoundaryObservation (graphCategoryBlockLengths R γ) (graphCategoryBlockLengths_total R γ) γ)
    (positive_observed_block_partitions W hW _ _ γ hγ) p hp hpsum hsupp δ herror
  rw [category_boundaryRestrictedWeight] at h
  refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
  intro η hη
  have hw := h.2.2.1 η hη
  by_cases hm : CategoryBlockMatches R γ η
  · exact ⟨hm, by simpa only [if_pos hm] using hw⟩
  · simp only [if_neg hm, lt_self_iff_false] at hw





end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_CategorySegmentSamplers
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

def categorySegmentStart {Q : Type} [Fintype Q] (R : Q → Q → Prop) {n : ℕ}
    (γ : Fin (n + 1) → Q) (i : Fin ((graphInteriorCuts R γ).card + 1)) : Q :=
  (Fin.cons (γ 0) (bridgeBoundaryObservation (graphCategoryBlockLengths R γ)
    (graphCategoryBlockLengths_total R γ) γ) : Fin ((graphInteriorCuts R γ).card + 1) → Q) i

def categorySegmentEnd {Q : Type} [Fintype Q] (R : Q → Q → Prop) {n : ℕ}
    (γ : Fin (n + 1) → Q) (i : Fin ((graphInteriorCuts R γ).card + 1)) : Q :=
  (Fin.snoc (bridgeBoundaryObservation (graphCategoryBlockLengths R γ)
    (graphCategoryBlockLengths_total R γ) γ) (γ (Fin.last n)) : Fin ((graphInteriorCuts R γ).card + 1) → Q) i

def categorySegmentStartIndex {Q : Type} [Fintype Q] (R : Q → Q → Prop) {n : ℕ}
    (γ : Fin (n + 1) → Q) (i : Fin ((graphInteriorCuts R γ).card + 1)) : Fin (n + 1) :=
  ⟨graphOrderedCuts R γ i.castSucc, by
    have h := graphOrderedCuts_monotone R γ (Fin.le_last i.castSucc)
    rw [graphOrderedCuts_finish] at h
    omega⟩

def categorySegmentEndIndex {Q : Type} [Fintype Q] (R : Q → Q → Prop) {n : ℕ}
    (γ : Fin (n + 1) → Q) (i : Fin ((graphInteriorCuts R γ).card + 1)) : Fin (n + 1) :=
  ⟨graphOrderedCuts R γ i.succ, by
    have h := graphOrderedCuts_monotone R γ (Fin.le_last i.succ)
    rw [graphOrderedCuts_finish] at h
    omega⟩

theorem categorySegmentStart_eq {Q : Type} [Fintype Q] (R : Q → Q → Prop) {n : ℕ}
    (γ : Fin (n + 1) → Q) (i : Fin ((graphInteriorCuts R γ).card + 1)) :
    categorySegmentStart R γ i = γ (categorySegmentStartIndex R γ i) := by
  unfold categorySegmentStart
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [Fin.cons_zero]
    apply congrArg γ
    apply Fin.ext
    exact (graphOrderedCuts_start R γ).symm
  · rw [Fin.cons_succ, graphCategoryBlock_observation]
    dsimp only
    apply congrArg γ
    apply Fin.ext
    exact (graphOrderedCuts_internal R γ j).symm

theorem categorySegmentEnd_eq {Q : Type} [Fintype Q] (R : Q → Q → Prop) {n : ℕ}
    (γ : Fin (n + 1) → Q) (i : Fin ((graphInteriorCuts R γ).card + 1)) :
    categorySegmentEnd R γ i = γ (categorySegmentEndIndex R γ i) := by
  unfold categorySegmentEnd
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]
    apply congrArg γ
    apply Fin.ext
    exact (graphOrderedCuts_finish R γ).symm
  · rw [Fin.snoc_castSucc, graphCategoryBlock_observation]
    dsimp only
    apply congrArg γ
    apply Fin.ext
    exact (graphOrderedCuts_internal R γ j).symm

theorem category_segment_kind {Q : Type} [Fintype Q] (R : Q → Q → Prop) {n : ℕ}
    (γ : Fin (n + 1) → Q) (i : Fin ((graphInteriorCuts R γ).card + 1)) :
    graphCategoryBlockLengths R γ i ≤ 1 ∨
      graphComponent R (categorySegmentStart R γ i) = graphComponent R (categorySegmentEnd R γ i) := by
  obtain h | h := graphCategoryBlockKinds R γ i
  · right
    rw [categorySegmentStart_eq, categorySegmentEnd_eq]
    exact h
  · exact Or.inl h.1.le

theorem category_segment_length_le {Q : Type} [Fintype Q] (R : Q → Q → Prop) {n : ℕ}
    (γ : Fin (n + 1) → Q) (i : Fin ((graphInteriorCuts R γ).card + 1)) :
    graphCategoryBlockLengths R γ i ≤ n := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (graphCategoryBlockLengths R γ j))
    (Finset.mem_univ i)
  rw [← bridgeBlockLength_eq_sum, graphCategoryBlockLengths_total] at h
  exact h



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_CertifiedBridgeConcatenation
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def certifiedBlockTuple {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (s t : Q) (y : Fin k → Q)
    (δ : Fin (k + 1) → ℝ)
    (B : ∀ i, CertifiedBridgeSampler W ((Fin.cons s y : Fin (k + 1) → Q) i)
      ((Fin.snoc y t : Fin (k + 1) → Q) i) (l i) (δ i)) :
    Bits (∑ i, (B i).seedLength) → BoundaryBlocks Q l s t y :=
  parallelSeedSample (fun i => (B i).seedLength) (fun i => (B i).sample)

def certifiedConcatenatedSample {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n)
    (s t : Q) (y : Fin k → Q) (δ : Fin (k + 1) → ℝ)
    (B : ∀ i, CertifiedBridgeSampler W ((Fin.cons s y : Fin (k + 1) → Q) i)
      ((Fin.snoc y t : Fin (k + 1) → Q) i) (l i) (δ i)) :
    Bits (∑ i, (B i).seedLength) → (Fin (n + 1) → Q) :=
  concatenateBridgeBlocksAtLength l hlen s t y ∘ certifiedBlockTuple W l s t y δ B

theorem certifiedConcatenatedSample_law {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n)
    (s t : Q) (y : Fin k → Q) (δ : Fin (k + 1) → ℝ)
    (B : ∀ i, CertifiedBridgeSampler W ((Fin.cons s y : Fin (k + 1) → Q) i)
      ((Fin.snoc y t : Fin (k + 1) → Q) i) (l i) (δ i)) :
    finiteSeedLaw (certifiedConcatenatedSample W l hlen s t y δ B) =
      concatenateBlockLaw l hlen s t y (fun i => finiteSeedLaw (B i).sample) := by
  rw [certifiedConcatenatedSample, finiteSeedLaw_map]
  have hb : finiteSeedLaw (certifiedBlockTuple W l s t y δ B) =
      fun b : BoundaryBlocks Q l s t y => ∏ i, finiteSeedLaw (B i).sample (b i) := by
    funext b
    exact parallelSeedSample_law _ _ b
  rw [hb]
  rfl



/-- Complete circuits for arbitrary certified segments concatenate in
parallel at their common depth. Their independent random bits are paid
once each, and the returned circuit computes the same product-law sample. -/
theorem certified_concatenation_circuit {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n)
    (s t : Q) (y : Fin k → Q) (δ : Fin (k + 1) → ℝ)
    (B : ∀ i, CertifiedBridgeSampler W ((Fin.cons s y : Fin (k + 1) → Q) i)
      ((Fin.snoc y t : Fin (k + 1) → Q) i) (l i) (δ i))
    (D : ℕ) (hD : ∀ i, (B i).circuit.depth ≤ D) :
    ∃ S : Circuit (Fin (n + 1) × Q), ∃ hbits : S.randomBits = ∑ i, (B i).seedLength,
      (∀ seed j x, S.eval (fun p => seed (Fin.cast hbits p)) (j, x) =
        decide (certifiedConcatenatedSample W l hlen s t y δ B seed j = x)) ∧
      S.depth ≤ D ∧ S.size ≤ (∑ i, (B i).seedLength) +
        (∑ i, ((l i + 1) * Fintype.card Q) * (B i).circuit.size) +
        (∑ i, (l i + 1) * Fintype.card Q) + (n + 1) * Fintype.card Q := by
  let m := fun i => (B i).seedLength
  let input := fun i j => seedSlot m i (Fin.cast (B i).randomBits_eq j)
  obtain ⟨C, hCbits, hCe, hCD, hCsize⟩ := parallel_circuit_family (fun i => (B i).circuit) input D hD
  let wire : (Fin (n + 1) × Q) → (Σ i : Fin (k + 1), Fin (l i + 1) × Q) := fun o =>
    ⟨(concatenationWire l hlen o.1).1, ((concatenationWire l hlen o.1).2, o.2)⟩
  obtain ⟨S, hSbits, hSe, hSD, hSsize⟩ := circuit_output_wiring C wire
  refine ⟨S, hSbits.trans hCbits, ?_, hSD.trans hCD, ?_⟩
  · intro seed j x
    let z := concatenationWire l hlen j
    have he := ((hSe (fun p => seed (Fin.cast hCbits p)) (j, x)).trans
      (hCe seed z.1 (z.2, x))).trans ((B z.1).eval_eq (seedSlotsEquiv m seed z.1) z.2 x)
    have hseed : (fun p => seed (Fin.cast hCbits (Fin.cast hSbits p))) =
        fun p => seed (Fin.cast (hSbits.trans hCbits) p) := by
      funext p
      congr 1
    rw [hseed] at he
    change S.eval _ (j, x) = decide (concatenateBridgeBlocksAtLength l hlen s t y _ j = x)
    rw [concatenateBridgeBlocksAtLength_wire]
    exact he
  · simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin] at hCsize hSsize
    change S.size ≤ (∑ i, m i) + _ + _ + _
    omega

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_AcceptingCategoryCircuit
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix



def categorySegmentTolerance (q : ℕ) (ε : ℝ) : ℝ := ε / (2 * q)

theorem categorySegmentTolerance_bounds (q : ℕ) (hq : 0 < q) (ε : ℝ)
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    0 < categorySegmentTolerance q ε ∧ categorySegmentTolerance q ε ≤ 1 ∧
      (2 * (q : ℝ)) * (categorySegmentTolerance q ε / 2) = ε / 2 := by
  have hq' : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr hq
  have hden : (0 : ℝ) < 2 * q := by positivity
  refine ⟨div_pos hε hden, (div_le_one hden).mpr (by linarith), ?_⟩
  unfold categorySegmentTolerance
  have h := mul_div_cancel₀ ε hden.ne'
  linarith



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_StarFreeExpressions
section
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

end

-- Source module: Solutions.FSS23105365_StarFreeLanguages
section
set_option autoImplicit false
noncomputable section
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



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_DelimiterWords
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_StarFreeBlockCoding
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_LocalDivisor
section
set_option autoImplicit false
noncomputable section
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



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_MonoidFiberDecomposition
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

def monoidWordValue {U M : Type} [Monoid M] (g : U → M) (w : List U) : M :=
  (w.map g).prod



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

end
end

-- Source module: Solutions.FSS23105365_Aperiodicity
section
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

end
end

-- Source module: Solutions.FSS23105365_AperiodicStarFree
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_StarFreeFormula
section
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

end

-- Source module: Solutions.FSS23105365_StarFreeBounds
section
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

end

-- Source module: Solutions.FSS23105365_StarFreeCircuits
section
set_option autoImplicit false
noncomputable section
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





end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_StarFreeFamilies
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_AperiodicEvaluation
section
set_option autoImplicit false
noncomputable section
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











end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_BlockDecoding
section
set_option autoImplicit false
noncomputable section
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





end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_AperiodicPrefixFormulas
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_SamplingLogBounds
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

def stateLog (q : ℕ) : ℝ := Real.log q / Real.log 2

theorem stateLog_nonneg {q : ℕ} (hq : 0 < q) : 0 ≤ stateLog q :=
  div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hq)) (Real.log_pos (by norm_num)).le

theorem stateLog_mono {p q : ℕ} (hp : 0 < p) (hpq : p ≤ q) : stateLog p ≤ stateLog q :=
  div_le_div_of_nonneg_right (Real.log_le_log (Nat.cast_pos.mpr hp) (Nat.cast_le.mpr hpq))
    (Real.log_pos (by norm_num)).le

theorem logInv_antitone {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ ≤ ε) : logInv ε ≤ logInv δ := by
  unfold logInv
  apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num)).le
  apply Real.log_le_log (div_pos (by norm_num) (hδ.trans_le hδε))
  exact one_div_le_one_div_of_le hδ hδε

theorem logInv_half {ε : ℝ} (hε : 0 < ε) : logInv (ε / 2) = logInv ε + 1 := by
  unfold logInv
  rw [show 1 / (ε / 2) = (1 / ε) * 2 by ring,
    Real.log_mul (by positivity) (by norm_num), add_div, div_self (Real.log_pos (by norm_num)).ne']

theorem logInv_ge_one {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1 / 2) : 1 ≤ logInv ε := by
  have h := logInv_antitone hε hεle
  norm_num [logInv] at h ⊢
  exact h

theorem log_succ_le (n : ℕ) : Real.log (n + 1 : ℕ) ≤ n := by
  have h := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (n + 1 : ℕ))
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using h



theorem localRoundingTolerance_bounds (N : ℕ) {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1) :
    0 < ε / (8 * (N + 1 : ℕ)) ∧ ε / (8 * (N + 1 : ℕ)) ≤ ε / 2 ∧ ε / 2 ≤ 1 := by
  have hN : (1 : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  refine ⟨by positivity, ?_, by linarith⟩
  apply div_le_div_of_nonneg_left hε.le (by norm_num)
  nlinarith

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_GrowthRoundingSeed
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

/-- A common endpoint-independent budget for an outcome set of cardinality
at most C times gamma to the block length. -/
def growthRoundingSeed (C γ : ℝ) (n : ℕ) (δ : ℝ) : ℕ :=
  ⌈Real.log C / Real.log 2 + n * (Real.log γ / Real.log 2) + logInv δ⌉₊

theorem growthRoundingSeed_denominator_bound (C γ : ℝ) (hC : 0 < C) (hγ : 0 < γ)
    (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    C * γ ^ n / (2 : ℝ) ^ growthRoundingSeed C γ n δ ≤ δ := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hh : Real.log (C * γ ^ n / δ) / Real.log 2 ≤ growthRoundingSeed C γ n δ := by
    calc
      _ = Real.log C / Real.log 2 + n * (Real.log γ / Real.log 2) + logInv δ := by
        rw [Real.log_div (mul_pos hC (pow_pos hγ n)).ne' hδ.ne',
          Real.log_mul hC.ne' (pow_pos hγ n).ne', Real.log_pow]
        simp only [logInv, Real.log_div one_ne_zero hδ.ne', Real.log_one, zero_sub]
        ring
      _ ≤ _ := Nat.le_ceil _
  have hpow : C * γ ^ n / δ ≤ (2 : ℝ) ^ growthRoundingSeed C γ n δ := by
    apply Real.le_pow_of_log_le (by norm_num)
    exact (div_le_iff₀ hlog2).mp hh
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ growthRoundingSeed C γ n δ)).mpr
  have hh' := (div_le_iff₀ hδ).mp hpow
  simpa only [mul_comm] using hh'

theorem growthRoundingSeed_card_budget (M : ℕ) (C γ : ℝ) (hC : 0 < C) (hγ : 0 < γ)
    (n : ℕ) (hM : (M : ℝ) ≤ C * γ ^ n) (δ : ℝ) (hδ : 0 < δ) :
    (M : ℝ) / (2 : ℝ) ^ growthRoundingSeed C γ n δ ≤ δ :=
  (div_le_div_of_nonneg_right hM (by positivity)).trans
    (growthRoundingSeed_denominator_bound C γ hC hγ n δ hδ)

theorem growthRoundingSeed_upper (C γ : ℝ) (hC : 1 ≤ C) (hγ : 1 ≤ γ)
    (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1) :
    (growthRoundingSeed C γ n δ : ℝ) ≤
      n * (Real.log γ / Real.log 2) + logInv δ + Real.log C / Real.log 2 + 1 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hh : 0 ≤ Real.log C / Real.log 2 + n * (Real.log γ / Real.log 2) + logInv δ :=
    add_nonneg (add_nonneg (div_nonneg (Real.log_nonneg hC) hlog2.le)
      (mul_nonneg (Nat.cast_nonneg n) (div_nonneg (Real.log_nonneg hγ) hlog2.le)))
      (logInv_nonneg_of_le_one δ hδ hδle)
  have h := (Nat.ceil_lt_add_one hh).le
  change (growthRoundingSeed C γ n δ : ℝ) ≤ _ at h
  linarith

theorem subcritical_log_rate {γ : ℝ} (hγ : 1 < γ) (hγ2 : γ < 2) :
    0 < Real.log γ / Real.log 2 ∧ Real.log γ / Real.log 2 < 1 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨div_pos (Real.log_pos hγ) hlog2, ?_⟩
  rw [div_lt_one hlog2]
  exact Real.log_lt_log (by linarith) hγ2

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_BinaryBoundarySeeds
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def binaryBoundarySeed (n : ℕ) (ε : ℝ) : ℕ := growthRoundingSeed 1 2 n (ε / 4)

theorem logInv_quarter {ε : ℝ} (hε : 0 < ε) : logInv (ε / 4) = logInv ε + 2 := by
  rw [show ε / 4 = (ε / 2) / 2 by ring, logInv_half (by positivity), logInv_half hε]
  ring

theorem binaryBoundarySeed_bound (n : ℕ) {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1 / 2) :
    (binaryBoundarySeed n ε : ℝ) ≤ n + 4 * logInv ε := by
  have h := growthRoundingSeed_upper 1 2 (by norm_num) (by norm_num) n (ε / 4)
    (by positivity) (by linarith)
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  simp only [Real.log_one, zero_div, div_self hl, mul_one, add_zero, logInv_quarter hε] at h
  change (binaryBoundarySeed n ε : ℝ) ≤ _ at h
  linarith [logInv_ge_one hε hεle]

/-- One common seed bound for every distribution on at most 2^n outcomes. -/
theorem binary_boundary_rounding {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1)
    (n : ℕ) (hcard : Fintype.card Ω ≤ 2 ^ n) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : Bits (binaryBoundarySeed n ε) → Ω,
      (∀ seed, 0 < p (f seed)) ∧ tv (finiteSeedLaw f) p ≤ ε / 4 := by
  obtain ⟨f, hf, herr⟩ := dyadic_rounding_sampler p hp hsum (binaryBoundarySeed n ε)
  refine ⟨f, hf, herr.trans ?_⟩
  have hcard' : (Fintype.card Ω : ℝ) ≤ 1 * (2 : ℝ) ^ n := by
    simpa only [one_mul, Nat.cast_pow, Nat.cast_ofNat] using (Nat.cast_le (α := ℝ)).mpr hcard
  have hb := growthRoundingSeed_card_budget (Fintype.card Ω) 1 2 (by norm_num) (by norm_num)
    n hcard' (ε / 4) (by positivity)
  apply le_trans _ hb
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
  change (2 : ℝ) ^ binaryBoundarySeed n ε ≤ 2 ^ (binaryBoundarySeed n ε + 1)
  rw [pow_succ]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (binaryBoundarySeed n ε)]

theorem head_middle_tail_seed_bound (T M R : ℕ) {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1 / 2) :
    ((binaryBoundarySeed T ε + (M + binaryBoundarySeed R ε) : ℕ) : ℝ) ≤
      (T + (M + R) : ℕ) + 8 * logInv ε := by
  have hT := binaryBoundarySeed_bound T hε hεle
  have hR := binaryBoundarySeed_bound R hε hεle
  push_cast
  linarith

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_FiberPermutation
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_BlockCountKernel
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_SeededBridgeModels
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

def seededBridgeSize (q n m : ℕ) : ℕ :=
  m + ((n + 1) * q) * (q ^ (n + 1) * (2 * (m * (3 * m + 2) + 1) + 6) + 2)

/-- A concrete bridge function and circuit at a prescribed common seed
length. The length may exploit feasible-path growth, independently of the
ambient state-space bound used only to estimate circuit size. -/
structure SeededBridgeModel {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (s t : Q) (n : ℕ) (δ : ℝ) (m : ℕ) where
  sample : Bits m → EndpointPath Q s t n
  circuit : Circuit (Fin (n + 1) × Q)
  randomBits_eq : circuit.randomBits = m
  eval_eq : ∀ seed i x, circuit.eval (fun j => seed (Fin.cast randomBits_eq j)) (i, x) =
    decide ((sample seed).val i = x)
  sample_positive : ∀ seed, 0 < edgePathWeight W (sample seed).val
  error : tv (finiteSeedLaw sample)
    (normalizeWeights (fun γ : EndpointPath Q s t n => edgePathWeight W γ.val)) ≤ δ
  depth_le : circuit.depth ≤ 6
  size_le : circuit.size ≤ seededBridgeSize (Fintype.card Q) n m

abbrev SeededBridgeFamily {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (δ : ℝ) (m : ℕ → ℕ) :=
  ∀ (s t : Q) (n : ℕ), 0 < bridgePartition W s t n → SeededBridgeModel W s t n δ (m n)

theorem seededBridgeModel_nonempty {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ)
    (hp : 0 < bridgePartition W s t n) (δ : ℝ) (m : ℕ)
    (hbudget : (positiveWeightCard
      (fun γ : EndpointPath Q s t n => edgePathWeight W γ.val) : ℝ) / 2 ^ m ≤ δ) :
    Nonempty (SeededBridgeModel W s t n δ m) := by
  classical
  let w := fun γ : EndpointPath Q s t n => edgePathWeight W γ.val
  have hw : ∀ γ, 0 ≤ w γ := fun γ => edgePathWeight_nonneg W hW γ.val
  have hZ : 0 < ∑ γ, w γ := by simpa only [w, endpointPath_weight_sum] using hp
  obtain ⟨f, S, hbits, he, hf, herr, hD, hsize⟩ := supported_rounding_circuit_budget w hw hZ
    (fun γ : EndpointPath Q s t n => fun ix : Fin (n + 1) × Q => decide (γ.val ix.1 = ix.2))
    m δ hbudget
  have hcard : positiveWeightCard w ≤ Fintype.card Q ^ (n + 1) :=
    (Fintype.card_subtype_le (fun γ => 0 < w γ)).trans (endpointPath_card_bound s t n)
  refine ⟨{ sample := f
            circuit := S
            randomBits_eq := hbits
            eval_eq := fun seed i x => congrFun (he seed) (i, x)
            sample_positive := hf
            error := herr
            depth_le := hD
            size_le := ?_ }⟩
  simp only [Fintype.card_prod, Fintype.card_fin] at hsize
  exact hsize.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hcard) 2)) _)

theorem growth_seededBridgeFamily_exists {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (h01 : ∀ x y, W x y = 0 ∨ W x y = 1)
    (C γ : ℝ) (hC : 0 < C) (hγ : 0 < γ)
    (hgrowth : ∀ (n : ℕ) (s t : Q), (W ^ n) s t ≤ C * γ ^ n)
    (δ : ℝ) (hδ : 0 < δ) :
    Nonempty (SeededBridgeFamily W δ (fun n => growthRoundingSeed C γ n δ)) := by
  classical
  have hW : ∀ x y, 0 ≤ W x y := by
    intro x y
    rcases h01 x y with h | h <;> simp [h]
  refine ⟨fun s t n hp => Classical.choice (seededBridgeModel_nonempty W hW s t n hp δ _ ?_)⟩
  apply growthRoundingSeed_card_budget _ C γ hC hγ n _ δ hδ
  rw [positive_endpoint_card_eq_matrix_power W h01]
  exact hgrowth n s t

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SeededEndpointCircuits
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- A common-domain block sampler for every endpoint pair. Impossible
pairs return a constant path and are excluded by the eventual selector's
support certificate. All endpoint branches use the same number of bits. -/
def totalSeededBridgeSample {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m) :
    Bits (m n) → (Fin (n + 1) → Q) :=
  if hp : 0 < bridgePartition W s t n then
    fun seed => (R s t n hp).sample seed |>.val
  else fun _ _ => s

theorem totalSeededBridgeSample_eq {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ)
    (hp : 0 < bridgePartition W s t n) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m) :
    totalSeededBridgeSample W hW s t n δ m R =
      fun seed => ((R s t n hp).sample seed).val := dif_pos hp

theorem totalSeededBridgeSample_circuit {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m) :
    ∃ B : Circuit (Fin (n + 1) × Q), ∃ hbits : B.randomBits = m n,
      (∀ seed i x, B.eval (fun j => seed (Fin.cast hbits j)) (i, x) =
        decide (totalSeededBridgeSample W hW s t n δ m R seed i = x)) ∧
      B.depth ≤ 6 ∧ B.size ≤ seededBridgeSize (Fintype.card Q) n (m n) := by
  by_cases hp : 0 < bridgePartition W s t n
  · let M := R s t n hp
    refine ⟨M.circuit, M.randomBits_eq, ?_, M.depth_le, M.size_le⟩
    intro seed i x
    rw [totalSeededBridgeSample_eq W hW s t n hp δ m R]
    exact M.eval_eq seed i x
  · let fs : (Fin (n + 1) × Q) → CircuitFormula (m n) :=
      fun o => .constant (decide (s = o.2))
    obtain ⟨B, hbits, he, hD, hsize⟩ := formula_fintype_family_circuit fs 1 (fun _ => le_rfl)
    refine ⟨B, hbits, ?_, hD.trans (by omega), ?_⟩
    · intro seed i x
      rw [he]
      have hs : totalSeededBridgeSample W hW s t n δ m R = fun _ _ => s := dif_neg hp
      rw [hs]
      rfl
    · simp only [fs, formulaCost, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, Fintype.card_prod, Fintype.card_fin, Nat.cast_id] at hsize
      rw [hsize]
      unfold seededBridgeSize
      have h : 2 ≤ Fintype.card Q ^ (n + 1) *
          (2 * (m n *
            (3 * m n + 2) + 1) + 6) + 2 := by omega
      have hh := Nat.mul_le_mul_left ((n + 1) * Fintype.card Q) h
      simpa only [Nat.mul_two, Nat.add_assoc] using
        Nat.add_le_add_left hh (m n)

/-- Local endpoint selection has only |Q|^2 branches, regardless of the
number of blocks in the full path. Branches share one block seed and add
two selector layers. No enumeration of complete boundary tuples occurs. -/
theorem seeded_endpoint_selected_block_circuit {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (n : ℕ) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m)
    (A : Circuit (Q × Q)) (f : Bits A.randomBits → Q × Q)
    (hselect : ∀ seed z, A.eval seed z = decide (f seed = z)) :
    ∃ S : Circuit (Fin (n + 1) × Q),
      ∃ hbits : S.randomBits = A.randomBits + m n,
      (∀ (seed : Bits (A.randomBits + m n)) i x,
        let split := seedPairEquiv A.randomBits (m n) seed
        let z := f split.1
        S.eval (fun j => seed (Fin.cast hbits j)) (i, x) =
          decide (totalSeededBridgeSample W hW z.1 z.2 n δ m R split.2 i = x)) ∧
      S.depth ≤ max A.depth 6 + 2 ∧
      S.size ≤ (A.randomBits + m n) +
        (Fintype.card Q * Fintype.card Q) * A.size +
        ((n + 1) * Fintype.card Q) *
          ((Fintype.card Q * Fintype.card Q) * seededBridgeSize (Fintype.card Q) n (m n)) +
        2 * ((Fintype.card Q * Fintype.card Q) +
          (Fintype.card Q * Fintype.card Q) * ((n + 1) * Fintype.card Q)) +
        ((n + 1) * Fintype.card Q) * (4 * (Fintype.card Q * Fintype.card Q) + 2) := by
  choose B hBbits hBeval hBD hBsize using
    fun z : Q × Q => totalSeededBridgeSample_circuit W hW z.1 z.2 n δ m R
  obtain ⟨S, hbits, he, hD, hsize⟩ := conditional_circuit_assembly A B f hselect
    (m n) 6 (fun z => (hBbits z).le) hBD
  refine ⟨S, hbits, ?_, hD, ?_⟩
  · intro seed i x
    dsimp only
    rw [he]
    exact hBeval _ _ i x
  · have hsum := Finset.sum_le_sum (fun z (_ : z ∈ Finset.univ) => hBsize z)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod] at hsum
    simp only [Fintype.card_prod, Fintype.card_fin] at hsize
    apply hsize.trans
    gcongr
    exact hsum



def seededEndpointSelectedSize (r selectorSize q n : ℕ) (m : ℕ → ℕ) : ℕ :=
  (r + m n) + (q * q) * selectorSize +
    ((n + 1) * q) * ((q * q) * seededBridgeSize q n (m n)) +
    2 * ((q * q) + (q * q) * ((n + 1) * q)) + ((n + 1) * q) * (4 * (q * q) + 2)

theorem seededEndpointSelectedSize_mono (r q n A B : ℕ) (m : ℕ → ℕ) (h : A ≤ B) :
    seededEndpointSelectedSize r A q n m ≤ seededEndpointSelectedSize r B q n m := by
  unfold seededEndpointSelectedSize
  gcongr

theorem seeded_endpoint_selected_block_circuit_budget {Q : Type} [Fintype Q] [DecidableEq Q] {r : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (n : ℕ) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m)
    (A : Circuit (Q × Q)) (hA : A.randomBits = r) (f : Bits r → Q × Q)
    (hselect : ∀ seed z, A.eval (fun j => seed (Fin.cast hA j)) z = decide (f seed = z)) :
    ∃ S : Circuit (Fin (n + 1) × Q), ∃ hbits : S.randomBits = r + m n,
      (∀ (seed : Bits (r + m n)) i x,
        let split := seedPairEquiv r (m n) seed
        let z := f split.1
        S.eval (fun j => seed (Fin.cast hbits j)) (i, x) =
          decide (totalSeededBridgeSample W hW z.1 z.2 n δ m R split.2 i = x)) ∧
      S.depth ≤ max A.depth 6 + 2 ∧
      S.size ≤ seededEndpointSelectedSize r A.size (Fintype.card Q) n m := by
  subst r
  exact seeded_endpoint_selected_block_circuit W hW n δ m R A f hselect

def seededBoundarySelectedSize (r boundarySize k q n : ℕ) (m : ℕ → ℕ) : ℕ :=
  seededEndpointSelectedSize r (boundarySize + k * q + 6 * (q * q)) q n m

/-- A local block now reads its two actual boundary states from a single
shared boundary circuit. Its separate tail contains only this block's seed. -/
theorem seeded_boundary_selected_block_circuit {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m)
    (C : Circuit (Fin k × Q)) (f : Bits C.randomBits → (Fin k → Q))
    (hC : ∀ seed i x, C.eval seed (i, x) = decide (f seed i = x))
    (s t : Q) (i : Fin (k + 1)) (n : ℕ) :
    ∃ S : Circuit (Fin (n + 1) × Q),
      ∃ hbits : S.randomBits = C.randomBits + m n,
      (∀ (seed : Bits (C.randomBits + m n)) j x,
        let split := seedPairEquiv C.randomBits (m n) seed
        let y := f split.1
        S.eval (fun p => seed (Fin.cast hbits p)) (j, x) = decide
          (totalSeededBridgeSample W hW ((Fin.cons s y : Fin (k + 1) → Q) i)
            ((Fin.snoc y t : Fin (k + 1) → Q) i) n δ m R split.2 j = x)) ∧
      S.depth ≤ max (C.depth + 2) 6 + 2 ∧
      S.size ≤ seededBoundarySelectedSize C.randomBits C.size k (Fintype.card Q) n m := by
  obtain ⟨A, hA, hAe, hAD, hAsize⟩ := boundary_pair_circuit C f hC s t i
  let pair := fun seed => ((Fin.cons s (f seed) : Fin (k + 1) → Q) i,
    (Fin.snoc (f seed) t : Fin (k + 1) → Q) i)
  obtain ⟨S, hbits, he, hD, hsize⟩ := seeded_endpoint_selected_block_circuit_budget W hW n δ m R A hA pair hAe
  refine ⟨S, hbits, he, ?_, ?_⟩
  · exact hD.trans (Nat.add_le_add_right (max_le_max_right 6 hAD) 2)
  · exact hsize.trans (seededEndpointSelectedSize_mono _ _ _ _ _ m hAsize)


end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SeededBridgeKernels
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- Impossible endpoint requests have zero kernel mass. Every positive
request uses the actual certified finite-bit sampler above. -/
def seededBridgeKernel {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ)
    (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m) : EndpointPath Q s t n → ℝ := by
  classical
  exact if hp : 0 < bridgePartition W s t n then
    finiteSeedLaw (R s t n hp).sample else fun _ => 0

theorem seededBridgeKernel_nonneg {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m) :
    ∀ γ, 0 ≤ seededBridgeKernel W hW s t n δ m R γ := by
  classical
  intro γ
  unfold seededBridgeKernel
  split_ifs
  · exact finiteSeedLaw_nonneg _ γ
  · exact le_rfl

theorem seededBridgeKernel_eq {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ)
    (hp : 0 < bridgePartition W s t n) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m) :
    seededBridgeKernel W hW s t n δ m R =
      finiteSeedLaw (R s t n hp).sample := dif_pos hp

theorem seededBridgeKernel_sum {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ)
    (hp : 0 < bridgePartition W s t n) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m) :
    ∑ γ, seededBridgeKernel W hW s t n δ m R γ = 1 := by
  rw [seededBridgeKernel_eq W hW s t n hp δ m R]
  exact finiteSeedLaw_sum _

theorem seededBridgeKernel_support {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m)
    (γ : EndpointPath Q s t n) (hγ : 0 < seededBridgeKernel W hW s t n δ m R γ) :
    0 < edgePathWeight W γ.val := by
  classical
  unfold seededBridgeKernel at hγ
  split_ifs at hγ with hp
  · obtain ⟨seed, rfl⟩ := (finiteSeedLaw_pos_iff _ γ).mp hγ
    exact (R s t n hp).sample_positive seed
  · exact False.elim ((lt_irrefl 0) hγ)

theorem seededBridgeKernel_error {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ)
    (hp : 0 < bridgePartition W s t n) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m) :
    tv (seededBridgeKernel W hW s t n δ m R)
      (normalizeWeights (fun γ : EndpointPath Q s t n => edgePathWeight W γ.val)) ≤ δ := by
  rw [seededBridgeKernel_eq W hW s t n hp δ m R]
  exact (R s t n hp).error

def seededBlocksKernel {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y)
    (l : Fin (k + 1) → ℕ) (s t : Q) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m)
    (y : Fin k → Q) (i : Fin (k + 1)) : BridgeBlockPath Q l s t y i → ℝ :=
  seededBridgeKernel W hW ((Fin.cons s y : Fin (k + 1) → Q) i)
    ((Fin.snoc y t : Fin (k + 1) → Q) i) (l i) δ m R

/-- Substituting the prescribed-seed block laws removes all conditional
sampler-existence hypotheses from the internal boundary/block assembly. -/
theorem seeded_boundary_block_sampler {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y)
    (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n) (s t : Q)
    (hpart : 0 < bridgePartition W s t n)
    (a : (Fin k → Q) → ℝ) (ha : ∀ y, 0 ≤ a y) (hasum : ∑ y, a y = 1)
    (hasupp : ∀ y, 0 < a y → 0 < bridgeBoundaryMass W l s t y)
    (η δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m)
    (hboundary : tv a (normalizeWeights (bridgeBoundaryMass W l s t)) ≤ η) :
    let law := boundaryBlockMixtureLaw l hlen s t a (seededBlocksKernel W hW l s t δ m R)
    (∀ γ, 0 ≤ law γ) ∧ (∑ γ, law γ = 1) ∧
    (∀ γ, 0 < law γ → 0 < bridgeWeight W s t n γ) ∧
    tv law (normalizeWeights (bridgeWeight W s t n)) ≤ η + (k + 1 : ℕ) * δ := by
  apply approximate_boundary_block_mixture W hW l hlen s t hpart a ha hasum hasupp
    (seededBlocksKernel W hW l s t δ m R)
    (fun y i => seededBridgeKernel_nonneg W hW _ _ _ δ m R)
    (fun y hy i => seededBridgeKernel_sum W hW _ _ _
      ((bridgeBoundaryMass_pos_iff W hW l s t y).mp (hasupp y hy) i) δ m R)
    (fun y i b => seededBridgeKernel_support W hW _ _ _ δ m R b)
    η ((k + 1 : ℕ) * δ) (fun _ _ => δ) hboundary
    (fun y hy i => seededBridgeKernel_error W hW _ _ _
      ((bridgeBoundaryMass_pos_iff W hW l s t y).mp (hasupp y hy) i) δ m R)
  intro y hy
  simp

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SeededBridgeDrawing
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def seededBlockSeedBudget {k : ℕ} (m : ℕ → ℕ) (l : Fin (k + 1) → ℕ) : ℕ :=
  ∑ i, m (l i)

def drawnSeededBlocks {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (s t : Q) (y : Fin k → Q) (hy : 0 < bridgeBoundaryMass W l s t y) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m) :
    Bits (seededBlockSeedBudget m l) → BoundaryBlocks Q l s t y :=
  parallelSeedSample (fun i => m (l i))
    (fun i => (R ((Fin.cons s y : Fin (k + 1) → Q) i)
      ((Fin.snoc y t : Fin (k + 1) → Q) i) (l i)
      ((bridgeBoundaryMass_pos_iff W hW l s t y).mp hy i)).sample)

theorem drawnSeededBlocks_law {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (s t : Q) (y : Fin k → Q) (hy : 0 < bridgeBoundaryMass W l s t y) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m) :
    finiteSeedLaw (drawnSeededBlocks W hW l s t y hy δ m R) =
      fun b : BoundaryBlocks Q l s t y => ∏ i, seededBlocksKernel W hW l s t δ m R y i (b i) := by
  funext b
  change finiteSeedLaw (parallelSeedSample
    (fun i => m (l i))
    (fun i => (R _ _ _
      ((bridgeBoundaryMass_pos_iff W hW l s t y).mp hy i)).sample)) b = _
  rw [parallelSeedSample_law]
  apply Finset.prod_congr rfl
  intro i _
  exact (congrFun (seededBridgeKernel_eq W hW _ _ _
    ((bridgeBoundaryMass_pos_iff W hW l s t y).mp hy i) δ m R) (b i)).symm

def drawnSeededBridge {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (hlen : bridgeBlockLength l = n) (s t : Q) (y : Fin k → Q)
    (hy : 0 < bridgeBoundaryMass W l s t y) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m) :
    Bits (seededBlockSeedBudget m l) → (Fin (n + 1) → Q) :=
  concatenateBridgeBlocksAtLength l hlen s t y ∘ drawnSeededBlocks W hW l s t y hy δ m R

/-- The explicit flat seed and block-index wiring realize exactly the
previously assembled conditional bridge distribution. -/
theorem drawnSeededBridge_law {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (hlen : bridgeBlockLength l = n) (s t : Q) (y : Fin k → Q)
    (hy : 0 < bridgeBoundaryMass W l s t y) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m) :
    finiteSeedLaw (drawnSeededBridge W hW l hlen s t y hy δ m R) =
      concatenateBlockLaw l hlen s t y (seededBlocksKernel W hW l s t δ m R y) := by
  rw [drawnSeededBridge, finiteSeedLaw_map, drawnSeededBlocks_law]
  rfl

theorem drawnSeededBridge_support {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (hlen : bridgeBlockLength l = n) (s t : Q) (y : Fin k → Q)
    (hy : 0 < bridgeBoundaryMass W l s t y) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m)
    (seed : Bits (seededBlockSeedBudget m l)) :
    0 < bridgeWeight W s t n (drawnSeededBridge W hW l hlen s t y hy δ m R seed) := by
  let b := drawnSeededBlocks W hW l s t y hy δ m R seed
  have hs := concatenateBridgeBlocksAtLength_spec l hlen s t y b
  change 0 < bridgeWeight W s t n (concatenateBridgeBlocksAtLength l hlen s t y b)
  rw [bridgeWeight, if_pos ⟨hs.1, hs.2.1⟩, concatenateBridgeBlocksAtLength_weight]
  apply Finset.prod_pos
  intro i _
  exact (R _ _ _
    ((bridgeBoundaryMass_pos_iff W hW l s t y).mp hy i)).sample_positive _



/-- Totalize a conditional draw with a constant path on impossible boundary
tuples. The support hypothesis below proves these branches are never selected. -/
def conditionalSeededBridge {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (hlen : bridgeBlockLength l = n) (s t : Q) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m)
    (y : Fin k → Q) : Bits (seededBlockSeedBudget m l) → (Fin (n + 1) → Q) :=
  if hy : 0 < bridgeBoundaryMass W l s t y then
    drawnSeededBridge W hW l hlen s t y hy δ m R
  else fun _ _ => s

def drawnSeededBoundaryBridge {Q : Type} [Fintype Q] [DecidableEq Q] {k n r : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (hlen : bridgeBlockLength l = n) (s t : Q) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m)
    (f : Bits r → (Fin k → Q)) :
    Bits (r + seededBlockSeedBudget m l) → (Fin (n + 1) → Q) :=
  sequentialSeedSample f (conditionalSeededBridge W hW l hlen s t δ m R)

/-- The whole bridge has one flat fair seed. Its second slice is reused
across conditional choices; its law is exactly the earlier hierarchical law. -/
theorem drawnSeededBoundaryBridge_law {Q : Type} [Fintype Q] [DecidableEq Q] {k n r : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (hlen : bridgeBlockLength l = n) (s t : Q) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m)
    (f : Bits r → (Fin k → Q))
    (hf : ∀ seed, 0 < bridgeBoundaryMass W l s t (f seed)) :
    finiteSeedLaw (drawnSeededBoundaryBridge W hW l hlen s t δ m R f) =
      boundaryBlockMixtureLaw l hlen s t (finiteSeedLaw f) (seededBlocksKernel W hW l s t δ m R) := by
  rw [drawnSeededBoundaryBridge, sequentialSeedSample_law]
  funext γ
  unfold boundaryBlockMixtureLaw mixtureLaw
  apply Finset.sum_congr rfl
  intro y _
  dsimp only
  by_cases hy : 0 < bridgeBoundaryMass W l s t y
  · have hg : conditionalSeededBridge W hW l hlen s t δ m R y =
        drawnSeededBridge W hW l hlen s t y hy δ m R := dif_pos hy
    rw [hg, drawnSeededBridge_law]
  · have hz : finiteSeedLaw f y = 0 := by
      apply le_antisymm _ (finiteSeedLaw_nonneg f y)
      by_contra h
      obtain ⟨seed, rfl⟩ := (finiteSeedLaw_pos_iff f y).mp (lt_of_not_ge h)
      exact hy (hf seed)
    rw [hz, zero_mul, zero_mul]

theorem drawnSeededBoundaryBridge_support {Q : Type} [Fintype Q] [DecidableEq Q] {k n r : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (hlen : bridgeBlockLength l = n) (s t : Q) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m)
    (f : Bits r → (Fin k → Q)) (hf : ∀ seed, 0 < bridgeBoundaryMass W l s t (f seed))
    (seed : Bits (r + seededBlockSeedBudget m l)) :
    0 < bridgeWeight W s t n (drawnSeededBoundaryBridge W hW l hlen s t δ m R f seed) := by
  unfold drawnSeededBoundaryBridge sequentialSeedSample conditionalSeededBridge
  rw [dif_pos (hf _)]
  exact drawnSeededBridge_support W hW l hlen s t _ (hf _) δ m R _


end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SeededParallelCircuit
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def locallyDrawnSeededBlocks {Q : Type} [Fintype Q] [DecidableEq Q] {k r : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (s t : Q) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m) (f : Bits r → (Fin k → Q))
    (seed : Bits (r + seededBlockSeedBudget m l)) (i : Fin (k + 1)) :
    Fin (l i + 1) → Q :=
  let split := seedPairEquiv r (seededBlockSeedBudget m l) seed
  let y := f split.1
  totalSeededBridgeSample W hW ((Fin.cons s y : Fin (k + 1) → Q) i)
    ((Fin.snoc y t : Fin (k + 1) → Q) i) (l i) δ m R
    (seedSlotsEquiv (fun j => m (l j)) split.2 i)

theorem locallyDrawnSeededBlocks_eq {Q : Type} [Fintype Q] [DecidableEq Q] {k r : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (s t : Q) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m) (f : Bits r → (Fin k → Q))
    (seed : Bits (r + seededBlockSeedBudget m l))
    (hy : 0 < bridgeBoundaryMass W l s t (f (seedPairEquiv r (seededBlockSeedBudget m l) seed).1))
    (i : Fin (k + 1)) :
    locallyDrawnSeededBlocks W hW l s t δ m R f seed i =
      (drawnSeededBlocks W hW l s t
        (f (seedPairEquiv r (seededBlockSeedBudget m l) seed).1) hy δ m R
        (seedPairEquiv r (seededBlockSeedBudget m l) seed).2 i).val := by
  unfold locallyDrawnSeededBlocks
  dsimp only
  rw [totalSeededBridgeSample_eq W hW _ _ _ ((bridgeBoundaryMass_pos_iff W hW l s t _).mp hy i) δ m R]
  rfl

def parallelSeededBlockSize {k : ℕ} (r boundarySize q : ℕ) (l : Fin (k + 1) → ℕ) (m : ℕ → ℕ) : ℕ :=
  (r + seededBlockSeedBudget m l) +
    (∑ i, ((l i + 1) * q) * seededBoundarySelectedSize r boundarySize k q (l i) m) +
    (∑ i, (l i + 1) * q)

/-- Every block is now evaluated in parallel. Its boundary prefix is
shared, its conditional seed slots are disjoint, and its endpoint choice
uses only local pairs. This circuit computes all coordinates of all blocks. -/
theorem parallel_seeded_block_circuit {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (s t : Q) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m)
    (C : Circuit (Fin k × Q)) (f : Bits C.randomBits → (Fin k → Q))
    (hC : ∀ seed i x, C.eval seed (i, x) = decide (f seed i = x)) :
    ∃ S : Circuit (Σ i : Fin (k + 1), Fin (l i + 1) × Q),
      ∃ hbits : S.randomBits = C.randomBits + seededBlockSeedBudget m l,
      (∀ (seed : Bits (C.randomBits + seededBlockSeedBudget m l)) i j x,
        S.eval (fun p => seed (Fin.cast hbits p)) ⟨i, (j, x)⟩ =
          decide (locallyDrawnSeededBlocks W hW l s t δ m R f seed i j = x)) ∧
      S.depth ≤ max (C.depth + 2) 6 + 2 ∧
      S.size ≤ parallelSeededBlockSize C.randomBits C.size (Fintype.card Q) l m := by
  choose B hBbits hBe hBD hBsize using
    fun i => seeded_boundary_selected_block_circuit W hW δ m R C f hC s t i (l i)
  let slots := fun i => m (l i)
  obtain ⟨S, hbits, he, hD, hsize⟩ := shared_prefix_circuit_family C.randomBits slots B hBbits _ hBD
  refine ⟨S, hbits, ?_, hD, ?_⟩
  · intro seed i j x
    have hb := hBe i (fun p => seed (sharedPrefixSlot C.randomBits slots i p)) j x
    dsimp only at hb
    rw [sharedPrefixSlot_split C.randomBits slots i seed] at hb
    exact (he seed i (j, x)).trans hb
  · have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      Nat.mul_le_mul_left ((l i + 1) * Fintype.card Q) (hBsize i))
    simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin] at hsize
    unfold parallelSeededBlockSize
    change S.size ≤ (C.randomBits + ∑ i, slots i) + _ + _
    omega



theorem drawnSeededBoundaryBridge_wire {Q : Type} [Fintype Q] [DecidableEq Q] {k n r : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (hlen : bridgeBlockLength l = n) (s t : Q) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m)
    (f : Bits r → (Fin k → Q)) (hf : ∀ seed, 0 < bridgeBoundaryMass W l s t (f seed))
    (seed : Bits (r + seededBlockSeedBudget m l)) (j : Fin (n + 1)) :
    drawnSeededBoundaryBridge W hW l hlen s t δ m R f seed j =
      locallyDrawnSeededBlocks W hW l s t δ m R f seed
        (concatenationWire l hlen j).1 (concatenationWire l hlen j).2 := by
  unfold drawnSeededBoundaryBridge sequentialSeedSample conditionalSeededBridge
  rw [dif_pos (hf _)]
  change concatenateBridgeBlocksAtLength l hlen s t _
    (drawnSeededBlocks W hW l s t _ (hf _) δ m R _) j = _
  rw [concatenateBridgeBlocksAtLength_wire,
    locallyDrawnSeededBlocks_eq W hW l s t δ m R f seed (hf _)]

/-- An actual circuit for the complete flat-seed bridge function, given
the boundary circuit. All short blocks execute in parallel and the final
path is fixed output wiring, so depth is independent of the block count. -/
theorem drawn_seeded_boundary_bridge_circuit {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (hlen : bridgeBlockLength l = n) (s t : Q) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m)
    (C : Circuit (Fin k × Q)) (f : Bits C.randomBits → (Fin k → Q))
    (hC : ∀ seed i x, C.eval seed (i, x) = decide (f seed i = x))
    (hf : ∀ seed, 0 < bridgeBoundaryMass W l s t (f seed)) :
    ∃ S : Circuit (Fin (n + 1) × Q),
      ∃ hbits : S.randomBits = C.randomBits + seededBlockSeedBudget m l,
      (∀ (seed : Bits (C.randomBits + seededBlockSeedBudget m l)) j x,
        S.eval (fun p => seed (Fin.cast hbits p)) (j, x) =
          decide (drawnSeededBoundaryBridge W hW l hlen s t δ m R f seed j = x)) ∧
      S.depth ≤ max (C.depth + 2) 6 + 2 ∧
      S.size ≤ parallelSeededBlockSize C.randomBits C.size (Fintype.card Q) l m + (n + 1) * Fintype.card Q := by
  obtain ⟨B, hBbits, hBe, hBD, hBsize⟩ := parallel_seeded_block_circuit W hW l s t δ m R C f hC
  let wire : (Fin (n + 1) × Q) → (Σ i : Fin (k + 1), Fin (l i + 1) × Q) := fun o =>
    ⟨(concatenationWire l hlen o.1).1, ((concatenationWire l hlen o.1).2, o.2)⟩
  obtain ⟨S, hSbits, hSe, hSD, hSsize⟩ := circuit_output_wiring B wire
  refine ⟨S, hSbits.trans hBbits, ?_, hSD.trans hBD, ?_⟩
  · intro seed j x
    have he := (hSe (fun p => seed (Fin.cast hBbits p)) (j, x)).trans
      (hBe seed (concatenationWire l hlen j).1 (concatenationWire l hlen j).2 x)
    have hseed : (fun p => seed (Fin.cast hBbits (Fin.cast hSbits p))) =
        fun p => seed (Fin.cast (hSbits.trans hBbits) p) := by
      funext p
      congr 1
    rw [hseed] at he
    rw [drawnSeededBoundaryBridge_wire W hW l hlen s t δ m R f hf seed j]
    exact he
  · simp only [Fintype.card_prod, Fintype.card_fin] at hSsize
    omega

theorem drawn_seeded_boundary_bridge_circuit_budget {Q : Type} [Fintype Q] [DecidableEq Q] {k n r : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (hlen : bridgeBlockLength l = n) (s t : Q) (δ : ℝ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m)
    (C : Circuit (Fin k × Q)) (hCbits : C.randomBits = r) (f : Bits r → (Fin k → Q))
    (hC : ∀ seed i x, C.eval (fun j => seed (Fin.cast hCbits j)) (i, x) = decide (f seed i = x))
    (hf : ∀ seed, 0 < bridgeBoundaryMass W l s t (f seed)) :
    ∃ S : Circuit (Fin (n + 1) × Q),
      ∃ hbits : S.randomBits = r + seededBlockSeedBudget m l,
      (∀ (seed : Bits (r + seededBlockSeedBudget m l)) j x,
        S.eval (fun p => seed (Fin.cast hbits p)) (j, x) =
          decide (drawnSeededBoundaryBridge W hW l hlen s t δ m R f seed j = x)) ∧
      S.depth ≤ max (C.depth + 2) 6 + 2 ∧
      S.size ≤ parallelSeededBlockSize r C.size (Fintype.card Q) l m + (n + 1) * Fintype.card Q := by
  subst r
  exact drawn_seeded_boundary_bridge_circuit W hW l hlen s t δ m R C f hC hf


end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SeededPeriodicCircuit
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

def seededPeriodicSeedBudget {k : ℕ} (M : ℕ) (l : Fin (k + 1) → ℕ)
    (δ : ℝ) (m : ℕ → ℕ) : ℕ := k * roundingSeed M δ + seededBlockSeedBudget m l

theorem parallelSeededBlockSize_mono {k : ℕ} (r q A B : ℕ)
    (l : Fin (k + 1) → ℕ) (m : ℕ → ℕ) (hAB : A ≤ B) :
    parallelSeededBlockSize r A q l m ≤ parallelSeededBlockSize r B q l m := by
  have hs : (∑ i, ((l i + 1) * q) * seededBoundarySelectedSize r A k q (l i) m) ≤
      ∑ i, ((l i + 1) * q) * seededBoundarySelectedSize r B k q (l i) m := by
    apply Finset.sum_le_sum
    intro i _
    apply Nat.mul_le_mul_left
    exact seededEndpointSelectedSize_mono _ _ _ _ _ m (by omega)
  unfold parallelSeededBlockSize
  omega

def seededPeriodicCircuitSize (q M boundarySize n L : ℕ) (δ : ℝ) (m : ℕ → ℕ) : ℕ :=
  let k := cutoffBoundaryCount n L
  let b := roundingSeed M δ
  parallelSeededBlockSize (k * b) (k * b + (k * q) * boundarySize + k * q)
    q (cutoffBlockLengths n L) m + (n + 1) * q

/-- A complete periodic bridge circuit with arbitrary certified local
seed budgets. Endpoint branches share slots, blocks use disjoint slots,
and the same circuit/function has the full support and TV guarantees. -/
theorem periodic_seeded_bridge_circuit_realization {Q : Type} [Fintype Q] [DecidableEq Q]
    (W K : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (a : ℕ) (ha : 0 < a)
    (C ρ : ℝ) (hC : 0 < C) (hρ : 0 < ρ)
    (happ : PeriodicBridgeBoundaryApproximation W K a C ρ)
    (s t : Q) (N n L : ℕ) (ε δ : ℝ) (hL : 0 < L) (had : a ∣ L)
    (hεle : ε ≤ 1) (herr : C * ρ ^ (L / a) ≤ ε / (8 * (N + 1 : ℕ)))
    (hn : n ≤ N) (hLn : L ≤ n) (hpart : 0 < bridgePartition W s t n)
    (hδ : 0 < δ) (m : ℕ → ℕ) (R : SeededBridgeFamily W δ m) :
    ∃ g : Bits (seededPeriodicSeedBudget
        (Fintype.card (PositiveSupportClass (K ^ a) s)) (cutoffBlockLengths n L) δ m) → (Fin (n + 1) → Q),
      ∃ S : Circuit (Fin (n + 1) × Q),
      ∃ hbits : S.randomBits = seededPeriodicSeedBudget
        (Fintype.card (PositiveSupportClass (K ^ a) s)) (cutoffBlockLengths n L) δ m,
      (∀ seed i x, S.eval (fun j => seed (Fin.cast hbits j)) (i, x) = decide (g seed i = x)) ∧
      S.depth ≤ 10 ∧ S.size ≤ seededPeriodicCircuitSize (Fintype.card Q)
        (Fintype.card (PositiveSupportClass (K ^ a) s))
        (boundaryRoundingCircuitSize (Fintype.card Q) (Fintype.card (PositiveSupportClass (K ^ a) s)) δ)
        n L δ m ∧
      (∀ seed, 0 < bridgeWeight W s t n (g seed)) ∧
      tv (finiteSeedLaw g) (normalizeWeights (bridgeWeight W s t n)) ≤
        ε / 4 + (2 * cutoffBoundaryCount n L + 1 : ℕ) * δ := by
  obtain ⟨f, B, hBbits, hBe, hBD, hBsize, hb, hsum, hsupp, htv⟩ :=
    rounded_periodic_boundary_sampler W K hW a ha C ρ hC hρ happ s t N n L ε δ
      hL had hεle herr hn hLn hpart hδ
  let embed := fun z : PositiveSupportClass (K ^ a) s => z.val
  let b := embeddedRepeatedSeedSample (cutoffBoundaryCount n L) embed f
  obtain ⟨A, hAbits, hAe, hAD, hAsize⟩ :=
    repeated_boundary_circuit (cutoffBoundaryCount n L) embed f B hBbits hBe
  have hbpos : ∀ seed, 0 < bridgeBoundaryMass W (cutoffBlockLengths n L) s t (b seed) := by
    intro seed
    apply hsupp
    rw [← embeddedRepeatedSeedSample_law]
    exact (finiteSeedLaw_pos_iff b (b seed)).mpr ⟨seed, rfl⟩
  have hbsupp : ∀ y, 0 < finiteSeedLaw b y →
      0 < bridgeBoundaryMass W (cutoffBlockLengths n L) s t y := by
    intro y hy
    obtain ⟨seed, rfl⟩ := (finiteSeedLaw_pos_iff b y).mp hy
    exact hbpos seed
  have hbtv : tv (finiteSeedLaw b) (normalizeWeights (bridgeBoundaryMass W (cutoffBlockLengths n L) s t)) ≤
      ε / 4 + cutoffBoundaryCount n L * δ := by
    rw [embeddedRepeatedSeedSample_law]
    exact htv
  let g := drawnSeededBoundaryBridge W hW (cutoffBlockLengths n L)
    (cutoffBlockLengths_total n L) s t δ m R b
  obtain ⟨S, hbits, he, hD, hsize⟩ := drawn_seeded_boundary_bridge_circuit_budget W hW
    (cutoffBlockLengths n L) (cutoffBlockLengths_total n L) s t δ m R A hAbits b hAe hbpos
  obtain ⟨_, _, hsupport, herror⟩ := seeded_boundary_block_sampler W hW
    (cutoffBlockLengths n L) (cutoffBlockLengths_total n L) s t hpart (finiteSeedLaw b)
    (finiteSeedLaw_nonneg b) (finiteSeedLaw_sum b) hbsupp
    (ε / 4 + cutoffBoundaryCount n L * δ) δ m R hbtv
  have hlaw := drawnSeededBoundaryBridge_law W hW (cutoffBlockLengths n L)
    (cutoffBlockLengths_total n L) s t δ m R b hbpos
  refine ⟨g, S, hbits, he, ?_, ?_, ?_, ?_⟩
  · omega
  · unfold seededPeriodicCircuitSize
    dsimp only
    apply hsize.trans
    apply Nat.add_le_add_right
    apply parallelSeededBlockSize_mono
    apply hAsize.trans
    gcongr
    exact hBsize
  · intro seed
    exact drawnSeededBoundaryBridge_support W hW (cutoffBlockLengths n L)
      (cutoffBlockLengths_total n L) s t δ m R b hbpos seed
  · change tv (finiteSeedLaw (drawnSeededBoundaryBridge W hW _ _ _ _ _ _ _ _)) _ ≤ _
    rw [hlaw]
    apply herror.trans
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    ring_nf
    exact le_rfl

theorem periodic_seeded_endpoint_bridge {Q : Type} [Fintype Q] [DecidableEq Q]
    (W K : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (a : ℕ) (ha : 0 < a)
    (C ρ : ℝ) (hC : 0 < C) (hρ : 0 < ρ)
    (happ : PeriodicBridgeBoundaryApproximation W K a C ρ)
    (s t : Q) (N n L : ℕ) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1)
    (hL : 0 < L) (had : a ∣ L)
    (herr : C * ρ ^ (L / a) ≤ ε / (8 * (N + 1 : ℕ)))
    (hn : n ≤ N) (hLn : L ≤ n) (hpart : 0 < bridgePartition W s t n)
    (m : ℕ → ℕ) (R : SeededBridgeFamily W (ε / (8 * (N + 1 : ℕ))) m) :
    let δ := ε / (8 * (N + 1 : ℕ))
    ∃ B : CertifiedBridgeSampler W s t n (ε / 2),
      B.seedLength = seededPeriodicSeedBudget
        (Fintype.card (PositiveSupportClass (K ^ a) s)) (cutoffBlockLengths n L) δ m ∧
      B.circuit.depth ≤ 10 ∧ B.circuit.size ≤ seededPeriodicCircuitSize (Fintype.card Q)
        (Fintype.card (PositiveSupportClass (K ^ a) s))
        (boundaryRoundingCircuitSize (Fintype.card Q) (Fintype.card (PositiveSupportClass (K ^ a) s)) δ)
        n L δ m := by
  dsimp only
  have hk := ((cutoff_block_count_bound n L).2).trans hn
  obtain ⟨hδ, hbudget⟩ := internal_bridge_rounding_error_budget N (cutoffBoundaryCount n L) hk ε hε
  obtain ⟨f, S, hbits, he, hD, hsize, hf, htv⟩ := periodic_seeded_bridge_circuit_realization
    W K hW a ha C ρ hC hρ happ s t N n L ε (ε / (8 * (N + 1 : ℕ)))
    hL had hεle herr hn hLn hpart hδ m R
  obtain ⟨g, hval, hpos, hdist⟩ := endpoint_seed_transport W hW s t f hf
  refine ⟨{ seedLength := _
            sample := g
            circuit := S
            randomBits_eq := hbits
            eval_eq := ?_
            sample_positive := hpos
            error := ?_ }, rfl, hD, hsize⟩
  · intro seed i x
    rw [hval]
    exact he seed i x
  · rw [hdist]
    exact htv.trans hbudget

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_GrowthPeriodicSeed
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

theorem seededBlockSeedBudget_growth_bound {k n : ℕ}
    (C γ : ℝ) (hC : 1 ≤ C) (hγ : 1 ≤ γ)
    (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1) :
    (seededBlockSeedBudget (fun b => growthRoundingSeed C γ b δ) l : ℝ) ≤
      n * (Real.log γ / Real.log 2) +
        (k + 1 : ℕ) * (Real.log C / Real.log 2 + logInv δ + 1) := by
  have hlen' : (∑ i, l i) = n := (bridgeBlockLength_eq_sum l).symm.trans hlen
  have hsum : (∑ i, (l i : ℝ)) = n := by exact_mod_cast hlen'
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    growthRoundingSeed_upper C γ hC hγ (l i) δ hδ hδle)
  simp only [seededBlockSeedBudget, Nat.cast_sum]
  calc
    _ ≤ ∑ i : Fin (k + 1), ((l i : ℝ) * (Real.log γ / Real.log 2) +
        logInv δ + Real.log C / Real.log 2 + 1) := hb
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- The actual sum of independent block budgets keeps the coefficient
log2(gamma) on the total path length. Boundary randomness contributes
only one fixed local overhead for each draw. -/
theorem seededPeriodicSeedBudget_growth_bound {k n : ℕ}
    (q M : ℕ) (hq : 0 < q) (hM : 0 < M) (hMq : M ≤ q)
    (C γ : ℝ) (hC : 1 ≤ C) (hγ : 1 ≤ γ)
    (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1) :
    (seededPeriodicSeedBudget M l δ (fun b => growthRoundingSeed C γ b δ) : ℝ) ≤
      n * (Real.log γ / Real.log 2) +
        (2 * k + 1 : ℕ) * (stateLog q + Real.log C / Real.log 2 + logInv δ + 1) := by
  have hb := seededBlockSeedBudget_growth_bound C γ hC hγ l hlen δ hδ hδle
  have hc := mul_le_mul_of_nonneg_left (roundingSeed_upper_of_card_le M q hM hMq δ hδ hδle)
    (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hqlog := stateLog_nonneg hq
  have hClog : 0 ≤ Real.log C / Real.log 2 :=
    div_nonneg (Real.log_nonneg hC) (Real.log_pos (by norm_num)).le
  have hkq := mul_nonneg (Nat.cast_nonneg (k + 1) : (0 : ℝ) ≤ (k + 1 : ℕ)) hqlog
  have hkc := mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hClog
  simp only [seededPeriodicSeedBudget, Nat.cast_add, Nat.cast_mul]
  have hh := add_le_add hc hb
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, stateLog] at hh hkq hkc ⊢
  nlinarith

/-- The overhead constants are independent of the cutoff multiplier.
This is the per-segment estimate needed before summing category segments. -/
theorem cutoff_growth_seed_budget (q M n L : ℕ)
    (hq : 0 < q) (hM : 0 < M) (hMq : M ≤ q) (hL : 0 < L)
    (C γ : ℝ) (hC : 1 ≤ C) (hγ : 1 ≤ γ)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1) :
    (seededPeriodicSeedBudget M (cutoffBlockLengths n L) δ
      (fun b => growthRoundingSeed C γ b δ) : ℝ) ≤
      n * (Real.log γ / Real.log 2) +
        (2 * ((n : ℝ) / L) + 1) * (stateLog q + Real.log C / Real.log 2 + logInv δ + 1) := by
  have hb := seededPeriodicSeedBudget_growth_bound q M hq hM hMq C γ hC hγ
    (cutoffBlockLengths n L) (cutoffBlockLengths_total n L) δ hδ hδle
  have hk : (cutoffBoundaryCount n L : ℝ) ≤ (n : ℝ) / L := by
    apply (le_div_iff₀ (Nat.cast_pos.mpr hL)).mpr
    exact_mod_cast cutoff_boundary_length_le n L
  have hover : 0 ≤ stateLog q + Real.log C / Real.log 2 + logInv δ + 1 := by
    have hqlog := stateLog_nonneg hq
    have hClog := div_nonneg (Real.log_nonneg hC) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    have hδlog := logInv_nonneg_of_le_one δ hδ hδle
    linarith
  apply hb.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_right _ hover
  push_cast
  linarith

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_GrowthPeriodicCircuit
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

theorem periodicBoundarySupportCard_pos {Q : Type} [Fintype Q] [DecidableEq Q]
    (W K : Matrix Q Q ℝ) (a : ℕ) (C ρ : ℝ)
    (happ : PeriodicBridgeBoundaryApproximation W K a C ρ) (s : Q) :
    0 < Fintype.card (PositiveSupportClass (K ^ a) s) := by
  obtain ⟨ν, _, hsum, _⟩ := happ s
  by_contra h
  have hz : Fintype.card (PositiveSupportClass (K ^ a) s) = 0 := by omega
  haveI := Fintype.card_eq_zero_iff.mp hz
  simp at hsum

/-- An actual long-bridge circuit instantiated with growth-based local
rounding, with no remaining assumption that local samplers exist. Its
linear random-bit coefficient is log2(gamma), while overhead scales with
the number of blocks. -/
theorem growth_periodic_endpoint_bridge {Q : Type} [Fintype Q] [DecidableEq Q]
    (W K : Matrix Q Q ℝ) (h01 : ∀ x y, W x y = 0 ∨ W x y = 1)
    (a : ℕ) (ha : 0 < a) (C ρ : ℝ) (hC : 0 < C) (hρ : 0 < ρ)
    (happ : PeriodicBridgeBoundaryApproximation W K a C ρ)
    (G γ : ℝ) (hG : 1 ≤ G) (hγ : 1 ≤ γ)
    (hgrowth : ∀ (b : ℕ) (x y : Q), (W ^ b) x y ≤ G * γ ^ b)
    (s t : Q) (N n L : ℕ) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1)
    (hL : 0 < L) (had : a ∣ L)
    (herr : C * ρ ^ (L / a) ≤ ε / (8 * (N + 1 : ℕ)))
    (hn : n ≤ N) (hLn : L ≤ n) (hpart : 0 < bridgePartition W s t n) :
    let δ := ε / (8 * (N + 1 : ℕ))
    let m := fun b => growthRoundingSeed G γ b δ
    ∃ B : CertifiedBridgeSampler W s t n (ε / 2),
      B.seedLength = seededPeriodicSeedBudget
        (Fintype.card (PositiveSupportClass (K ^ a) s)) (cutoffBlockLengths n L) δ m ∧
      (B.seedLength : ℝ) ≤ n * (Real.log γ / Real.log 2) +
        (2 * ((n : ℝ) / L) + 1) * (stateLog (Fintype.card Q) + Real.log G / Real.log 2 + logInv δ + 1) ∧
      B.circuit.depth ≤ 10 ∧ B.circuit.size ≤ seededPeriodicCircuitSize (Fintype.card Q)
        (Fintype.card (PositiveSupportClass (K ^ a) s))
        (boundaryRoundingCircuitSize (Fintype.card Q) (Fintype.card (PositiveSupportClass (K ^ a) s)) δ)
        n L δ m := by
  dsimp only
  have hW : ∀ x y, 0 ≤ W x y := by
    intro x y
    rcases h01 x y with h | h <;> simp [h]
  have hδ := localRoundingTolerance_bounds N hε hεle
  obtain ⟨R⟩ := growth_seededBridgeFamily_exists W h01 G γ
    (zero_lt_one.trans_le hG) (zero_lt_one.trans_le hγ) hgrowth _ hδ.1
  obtain ⟨B, hbits, hD, hsize⟩ := periodic_seeded_endpoint_bridge W K hW a ha C ρ hC hρ happ
    s t N n L ε hε hεle hL had herr hn hLn hpart _ R
  refine ⟨B, hbits, ?_, hD, hsize⟩
  rw [hbits]
  apply cutoff_growth_seed_budget (Fintype.card Q) _ n L
    (Fintype.card_pos_iff.mpr ⟨s⟩) (periodicBoundarySupportCard_pos W K a C ρ happ s)
    (Fintype.card_subtype_le _) hL G γ hG hγ _ hδ.1 (hδ.2.1.trans hδ.2.2)

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_GrowthSCCBridge
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

def growthSCCSeedBudget {Q : Type} [Fintype Q] [DecidableEq Q]
    {W : Matrix Q Q ℝ} {s : Q} (model : SCCPeriodicModel W s) (x : SCCState W s)
    (G γ : ℝ) (n L : ℕ) (δ : ℝ) : ℕ :=
  seededPeriodicSeedBudget
    (Fintype.card (PositiveSupportClass (doobMatrix (sccMatrix W s) model.lam model.right ^ model.blockExponent) x))
    (cutoffBlockLengths n L) δ (fun b => growthRoundingSeed G γ b δ)

def growthSCCCircuitSize {Q : Type} [Fintype Q] [DecidableEq Q]
    {W : Matrix Q Q ℝ} {s : Q} (model : SCCPeriodicModel W s) (x : SCCState W s)
    (G γ : ℝ) (n L : ℕ) (δ : ℝ) : ℕ :=
  let q := Fintype.card (SCCState W s)
  let M := Fintype.card (PositiveSupportClass
    (doobMatrix (sccMatrix W s) model.lam model.right ^ model.blockExponent) x)
  seededPeriodicCircuitSize q M (boundaryRoundingCircuitSize q M δ) n L δ
    (fun b => growthRoundingSeed G γ b δ) + (n + 1) * q + 2 * ((n + 1) * Fintype.card Q)

/-- The growth-budget long bridge is realized over the original state
alphabet. SCC embedding preserves all random bits, support and TV error. -/
theorem growth_scc_periodic_bridge {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (h01 : ∀ x y, W x y = 0 ∨ W x y = 1)
    (s : Q) (model : SCCPeriodicModel W s) (G γ : ℝ) (hG : 1 ≤ G) (hγ : 1 ≤ γ)
    (hgrowth : ∀ (b : ℕ) (x y : SCCState W s), (sccMatrix W s ^ b) x y ≤ G * γ ^ b)
    (x y : SCCState W s) (N n L : ℕ) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1)
    (hL : 0 < L) (had : model.blockExponent ∣ L)
    (hmix : model.coefficient * model.rate ^ (L / model.blockExponent) ≤ ε / (8 * (N + 1 : ℕ)))
    (hn : n ≤ N) (hLn : L ≤ n) (hpart : 0 < bridgePartition W x.val y.val n) :
    let δ := ε / (8 * (N + 1 : ℕ))
    ∃ B : CertifiedBridgeSampler W x.val y.val n (ε / 2),
      B.seedLength = growthSCCSeedBudget model x G γ n L δ ∧
      (B.seedLength : ℝ) ≤ n * (Real.log γ / Real.log 2) +
        (2 * ((n : ℝ) / L) + 1) *
          (stateLog (Fintype.card (SCCState W s)) + Real.log G / Real.log 2 + logInv δ + 1) ∧
      B.circuit.depth ≤ 11 ∧ B.circuit.size ≤ growthSCCCircuitSize model x G γ n L δ := by
  have hW : ∀ i j, 0 ≤ W i j := by
    intro i j
    rcases h01 i j with h | h <;> simp [h]
  have hpart' : 0 < bridgePartition (sccMatrix W s) x y n := by
    rw [scc_bridgePartition W hW]
    exact hpart
  obtain ⟨B, hbits, hseed, hD, hsize⟩ := growth_periodic_endpoint_bridge
    (sccMatrix W s) (doobMatrix (sccMatrix W s) model.lam model.right)
    (fun i j => h01 i.val j.val) model.blockExponent model.exponent_pos
    model.coefficient model.rate model.coefficient_pos model.rate_pos model.approximation
    G γ hG hγ hgrowth x y N n L ε hε hεle hL had hmix hn hLn hpart'
  obtain ⟨g, S, hSbits, he, hSD, hSsize, hpos, herror⟩ := scc_endpoint_circuit_transport
    W hW s x y B.sample B.circuit B.randomBits_eq B.eval_eq B.sample_positive (ε / 2) B.error
  refine ⟨{ seedLength := B.seedLength
            sample := g
            circuit := S
            randomBits_eq := hSbits
            eval_eq := he
            sample_positive := hpos
            error := herror }, hbits, hseed, ?_, ?_⟩
  · change S.depth ≤ 11
    omega
  · change S.size ≤ growthSCCCircuitSize model x G γ n L _
    unfold growthSCCCircuitSize
    dsimp only
    omega

def growthSCCShortCircuitSize {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (s : Q) (G γ : ℝ) (n : ℕ) (δ : ℝ) : ℕ :=
  seededBridgeSize (Fintype.card (SCCState W s)) n (growthRoundingSeed G γ n δ) +
    (n + 1) * Fintype.card (SCCState W s) + 2 * ((n + 1) * Fintype.card Q)

/-- Short bridges use the same growth estimate in the restricted SCC;
they are then embedded, so the seed bound never pays for impossible
ambient paths or extraneous states. -/
theorem growth_scc_short_bridge {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (h01 : ∀ x y, W x y = 0 ∨ W x y = 1)
    (s : Q) (G γ : ℝ) (hG : 1 ≤ G) (hγ : 1 ≤ γ)
    (hgrowth : ∀ (b : ℕ) (x y : SCCState W s), (sccMatrix W s ^ b) x y ≤ G * γ ^ b)
    (x y : SCCState W s) (n : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1)
    (hpart : 0 < bridgePartition W x.val y.val n) :
    ∃ B : CertifiedBridgeSampler W x.val y.val n δ,
      B.seedLength = growthRoundingSeed G γ n δ ∧
      (B.seedLength : ℝ) ≤ n * (Real.log γ / Real.log 2) + logInv δ + Real.log G / Real.log 2 + 1 ∧
      B.circuit.depth ≤ 7 ∧ B.circuit.size ≤ growthSCCShortCircuitSize W s G γ n δ := by
  have hW : ∀ i j, 0 ≤ W i j := by
    intro i j
    rcases h01 i j with h | h <;> simp [h]
  have hpart' : 0 < bridgePartition (sccMatrix W s) x y n := by
    rw [scc_bridgePartition W hW]
    exact hpart
  obtain ⟨R⟩ := growth_seededBridgeFamily_exists (sccMatrix W s) (fun i j => h01 i.val j.val)
    G γ (zero_lt_one.trans_le hG) (zero_lt_one.trans_le hγ) hgrowth δ hδ
  let B := R x y n hpart'
  obtain ⟨g, S, hbits, he, hD, hsize, hpos, herror⟩ := scc_endpoint_circuit_transport
    W hW s x y B.sample B.circuit B.randomBits_eq B.eval_eq B.sample_positive δ B.error
  refine ⟨{ seedLength := growthRoundingSeed G γ n δ
            sample := g
            circuit := S
            randomBits_eq := hbits
            eval_eq := he
            sample_positive := hpos
            error := herror }, rfl,
    growthRoundingSeed_upper G γ hG hγ n δ hδ hδle, ?_, ?_⟩
  · change S.depth ≤ 7
    have hd := B.depth_le
    omega
  · change S.size ≤ growthSCCShortCircuitSize W s G γ n δ
    have hs : B.circuit.size ≤ seededBridgeSize (Fintype.card (SCCState W s)) n
        (growthRoundingSeed G γ n δ) := B.size_le
    unfold growthSCCShortCircuitSize
    omega

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_GrowthComponentSampler
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

def growthSeedOverhead (q : ℕ) (G δ : ℝ) : ℝ :=
  stateLog q + Real.log G / Real.log 2 + logInv δ + 1

theorem growthSeedOverhead_nonneg (q : ℕ) (hq : 0 < q) (G δ : ℝ)
    (hG : 1 ≤ G) (hδ : 0 < δ) (hδle : δ ≤ 1) : 0 ≤ growthSeedOverhead q G δ := by
  have hqlog := stateLog_nonneg hq
  have hGlog := div_nonneg (Real.log_nonneg hG) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hδlog := logInv_nonneg_of_le_one δ hδ hδle
  unfold growthSeedOverhead
  linarith

def growthComponentSeedBudget {Q : Type} [Fintype Q] [DecidableEq Q]
    {W : Matrix Q Q ℝ} (models : ∀ c : CyclicSCCIndex W, SCCPeriodicModel W c.val)
    (G γ : ℝ) (s : Q) (N n L : ℕ) (ε : ℝ) : ℕ := by
  classical
  exact if n ≤ 1 then 0 else if hc : CyclicSCC W s then
    if n < L then growthRoundingSeed G γ n (ε / 2)
    else growthSCCSeedBudget (models ⟨s, hc⟩) ⟨s, rfl⟩ G γ n L (ε / (8 * (N + 1 : ℕ)))
    else 0

def growthComponentCircuitSize {Q : Type} [Fintype Q] [DecidableEq Q]
    {W : Matrix Q Q ℝ} (models : ∀ c : CyclicSCCIndex W, SCCPeriodicModel W c.val)
    (G γ : ℝ) (s : Q) (N n L : ℕ) (ε : ℝ) : ℕ := by
  classical
  exact if n ≤ 1 then 2 * ((n + 1) * Fintype.card Q) else if hc : CyclicSCC W s then
    if n < L then growthSCCShortCircuitSize W s G γ n (ε / 2)
    else growthSCCCircuitSize (models ⟨s, hc⟩) ⟨s, rfl⟩ G γ n L (ε / (8 * (N + 1 : ℕ)))
    else 0

/-- Every actual category segment has a constructed growth-budget
sampler. The uniform overhead is independent of the chosen cutoff
multiplier and of the segment endpoints. -/
theorem growth_component_segment_sampler {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (h01 : ∀ x y, W x y = 0 ∨ W x y = 1)
    (models : ∀ c : CyclicSCCIndex W, SCCPeriodicModel W c.val)
    (G γ : ℝ) (hG : 1 ≤ G) (hγ : 1 ≤ γ)
    (hgrowth : ∀ (c : CyclicSCCIndex W) (b : ℕ) (x y : SCCState W c.val),
      (sccMatrix W c.val ^ b) x y ≤ G * γ ^ b)
    (s t : Q) (N n L : ℕ) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1)
    (hL : 0 < L) (hn : n ≤ N)
    (hmix : ∀ c, (models c).blockExponent ∣ L ∧
      (models c).coefficient * (models c).rate ^ (L / (models c).blockExponent) ≤ ε / (8 * (N + 1 : ℕ)))
    (hkind : n ≤ 1 ∨ graphComponent (fun i j => 0 < W i j) s = graphComponent (fun i j => 0 < W i j) t)
    (hpart : 0 < bridgePartition W s t n) :
    ∃ B : CertifiedBridgeSampler W s t n (ε / 2),
      B.seedLength = growthComponentSeedBudget models G γ s N n L ε ∧
      (B.seedLength : ℝ) ≤ n * (Real.log γ / Real.log 2) +
        (2 * ((n : ℝ) / L) + 1) * growthSeedOverhead (Fintype.card Q) G (ε / (8 * (N + 1 : ℕ))) ∧
      B.circuit.depth ≤ 11 ∧ B.circuit.size ≤ growthComponentCircuitSize models G γ s N n L ε := by
  classical
  have hW : ∀ i j, 0 ≤ W i j := by
    intro i j
    rcases h01 i j with h | h <;> simp [h]
  have hq : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨s⟩
  have hδ := localRoundingTolerance_bounds N hε hεle
  have hover := growthSeedOverhead_nonneg (Fintype.card Q) hq G _ hG hδ.1 (hδ.2.1.trans hδ.2.2)
  have hrate : 0 ≤ Real.log γ / Real.log 2 :=
    div_nonneg (Real.log_nonneg hγ) (Real.log_pos (by norm_num)).le
  have hfactor : 1 ≤ 2 * ((n : ℝ) / L) + 1 := by
    have hdiv : 0 ≤ (n : ℝ) / L := by positivity
    linarith
  by_cases hfixed : n ≤ 1
  · obtain ⟨B, hm, hD, hsize⟩ := certified_fixed_bridge W hW s t hfixed hpart (ε / 2) (by positivity)
    refine ⟨B, ?_, ?_, hD.trans (by omega), ?_⟩
    · simpa only [growthComponentSeedBudget, if_pos hfixed] using hm
    · rw [hm]
      simp only [Nat.cast_zero]
      exact add_nonneg (mul_nonneg (Nat.cast_nonneg n) hrate)
        (mul_nonneg (zero_le_one.trans hfactor) hover)
    · simpa only [growthComponentCircuitSize, if_pos hfixed] using hsize.le
  · have hst := hkind.resolve_left hfixed
    let x : SCCState W s := ⟨s, rfl⟩
    let y : SCCState W s := ⟨t, hst.symm⟩
    have hc : CyclicSCC W s := by
      by_contra hnc
      have hz := acyclic_scc_bridge_length_zero W hW s hnc x y n hpart
      omega
    let c : CyclicSCCIndex W := ⟨s, hc⟩
    by_cases hshort : n < L
    · obtain ⟨B, hm, hseed, hD, hsize⟩ := growth_scc_short_bridge W h01 s G γ hG hγ
        (hgrowth c) x y n (ε / 2) (by positivity) hδ.2.2 hpart
      refine ⟨B, ?_, ?_, hD.trans (by omega), ?_⟩
      · simpa only [growthComponentSeedBudget, if_neg hfixed, dif_pos hc, if_pos hshort] using hm
      · have hprec := logInv_antitone hδ.1 hδ.2.1
        have hqlog := stateLog_nonneg hq
        have hpay := mul_le_mul_of_nonneg_right hfactor hover
        unfold growthSeedOverhead at hover hpay ⊢
        nlinarith
      · simpa only [growthComponentCircuitSize, if_neg hfixed, dif_pos hc, if_pos hshort] using hsize
    · obtain ⟨B, hm, hseed, hD, hsize⟩ := growth_scc_periodic_bridge W h01 s (models c) G γ hG hγ
        (hgrowth c) x y N n L ε hε hεle hL (hmix c).1 (hmix c).2 hn (by omega) hpart
      refine ⟨B, ?_, ?_, hD, ?_⟩
      · simpa only [growthComponentSeedBudget, if_neg hfixed, dif_pos hc, if_neg hshort] using hm
      · have hlog := stateLog_mono (Fintype.card_pos_iff.mpr ⟨x⟩)
          (Fintype.card_subtype_le (fun z => graphComponent (fun i j => 0 < W i j) z =
            graphComponent (fun i j => 0 < W i j) s))
        apply hseed.trans
        unfold growthSeedOverhead
        gcongr
      · simpa only [growthComponentCircuitSize, if_neg hfixed, dif_pos hc, if_neg hshort] using hsize

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_GrowthCategorySegments
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

theorem growth_category_segment_samplers {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (h01 : ∀ x y, W x y = 0 ∨ W x y = 1)
    (models : ∀ c : CyclicSCCIndex W, SCCPeriodicModel W c.val)
    (G σ : ℝ) (hG : 1 ≤ G) (hσ : 1 ≤ σ)
    (hgrowth : ∀ (c : CyclicSCCIndex W) (b : ℕ) (x y : SCCState W c.val),
      (sccMatrix W c.val ^ b) x y ≤ G * σ ^ b)
    {n : ℕ} (γ : Fin (n + 1) → Q) (hγ : 0 < edgePathWeight W γ)
    (L : ℕ) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1) (hL : 0 < L)
    (hmix : ∀ c, (models c).blockExponent ∣ L ∧
      (models c).coefficient * (models c).rate ^ (L / (models c).blockExponent) ≤ ε / (8 * (n + 1 : ℕ))) :
    let R := fun i j => 0 < W i j
    ∀ i : Fin ((graphInteriorCuts R γ).card + 1),
      ∃ B : CertifiedBridgeSampler W (categorySegmentStart R γ i)
        (categorySegmentEnd R γ i) (graphCategoryBlockLengths R γ i) (ε / 2),
        B.seedLength = growthComponentSeedBudget models G σ (categorySegmentStart R γ i) n
          (graphCategoryBlockLengths R γ i) L ε ∧
        (B.seedLength : ℝ) ≤ (graphCategoryBlockLengths R γ i) * (Real.log σ / Real.log 2) +
          (2 * ((graphCategoryBlockLengths R γ i : ℝ) / L) + 1) *
            growthSeedOverhead (Fintype.card Q) G (ε / (8 * (n + 1 : ℕ))) ∧
        B.circuit.depth ≤ 11 ∧ B.circuit.size ≤ growthComponentCircuitSize models G σ
          (categorySegmentStart R γ i) n (graphCategoryBlockLengths R γ i) L ε := by
  have hW : ∀ x y, 0 ≤ W x y := by
    intro x y
    rcases h01 x y with h | h <;> simp [h]
  dsimp only
  intro i
  apply growth_component_segment_sampler W h01 models G σ hG hσ hgrowth _ _ n _ L ε
    hε hεle hL (category_segment_length_le _ γ i) hmix (category_segment_kind _ γ i)
  exact positive_observed_block_partitions W hW
    (graphCategoryBlockLengths (fun i j => 0 < W i j) γ)
    (graphCategoryBlockLengths_total (fun i j => 0 < W i j) γ) γ hγ i

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_GrowthCategoryCircuit
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

def growthCategorySeedBudget {Q : Type} [Fintype Q] [DecidableEq Q]
    {W : Matrix Q Q ℝ} (models : ∀ c : CyclicSCCIndex W, SCCPeriodicModel W c.val)
    (G σ : ℝ)
    {n : ℕ} (γ : Fin (n + 1) → Q) (L : ℕ) (ε : ℝ) : ℕ :=
  ∑ i : Fin ((graphInteriorCuts (fun i j => 0 < W i j) γ).card + 1),
    growthComponentSeedBudget models G σ (categorySegmentStart (fun i j => 0 < W i j) γ i) n
      (graphCategoryBlockLengths (fun i j => 0 < W i j) γ i) L ε

def growthCategoryCircuitSize {Q : Type} [Fintype Q] [DecidableEq Q]
    {W : Matrix Q Q ℝ} (models : ∀ c : CyclicSCCIndex W, SCCPeriodicModel W c.val)
    (G σ : ℝ)
    {n : ℕ} (γ : Fin (n + 1) → Q) (L : ℕ) (ε : ℝ) : ℕ :=
  let R := fun i j => 0 < W i j
  let l := graphCategoryBlockLengths R γ
  growthCategorySeedBudget models G σ γ L ε +
    (∑ i, ((l i + 1) * Fintype.card Q) *
      growthComponentCircuitSize models G σ (categorySegmentStart R γ i) n (l i) L ε) +
    (∑ i, (l i + 1) * Fintype.card Q) + (n + 1) * Fintype.card Q

/-- A complete category sampler now consists of constructed segment
functions and one actual parallel concatenation circuit. It has depth
eleven, explicit resources, correct category support, and the sum of the
segment error allocations. No unknown block laws are supplied. -/
theorem growth_constructed_category_circuit {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (h01 : ∀ x y, W x y = 0 ∨ W x y = 1)
    (models : ∀ c : CyclicSCCIndex W, SCCPeriodicModel W c.val)
    (G σ : ℝ) (hG : 1 ≤ G) (hσ : 1 ≤ σ)
    (hgrowth : ∀ (c : CyclicSCCIndex W) (b : ℕ) (x y : SCCState W c.val),
      (sccMatrix W c.val ^ b) x y ≤ G * σ ^ b)
    {n : ℕ} (γ : Fin (n + 1) → Q) (hγ : 0 < edgePathWeight (fun i j => W i j) γ)
    (L : ℕ) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1) (hL : 0 < L)
    (hmix : ∀ c, (models c).blockExponent ∣ L ∧
      (models c).coefficient * (models c).rate ^ (L / (models c).blockExponent) ≤ ε / (8 * (n + 1 : ℕ))) :
    ∃ f : Bits (growthCategorySeedBudget models G σ γ L ε) → (Fin (n + 1) → Q),
      ∃ S : Circuit (Fin (n + 1) × Q), ∃ hbits : S.randomBits = growthCategorySeedBudget models G σ γ L ε,
      (∀ seed i x, S.eval (fun j => seed (Fin.cast hbits j)) (i, x) = decide (f seed i = x)) ∧
      S.depth ≤ 11 ∧ S.size ≤ growthCategoryCircuitSize models G σ γ L ε ∧
      (∀ seed, CategoryBlockMatches (fun i j => 0 < W i j) γ (f seed) ∧
        0 < edgePathWeight (fun i j => W i j) (f seed)) ∧
      tv (finiteSeedLaw f) (normalizeWeights (fun η =>
        if CategoryBlockMatches (fun i j => 0 < W i j) γ η then edgePathWeight (fun i j => W i j) η else 0)) ≤
        ((graphInteriorCuts (fun i j => 0 < W i j) γ).card + 1 : ℕ) * (ε / 2) := by
  classical
  have hW : ∀ x y, 0 ≤ W x y := by
    intro x y
    rcases h01 x y with h | h <;> simp [h]
  let R := fun i j => 0 < W i j
  let l := graphCategoryBlockLengths R γ
  let y := bridgeBoundaryObservation l (graphCategoryBlockLengths_total R γ) γ
  choose B hBm hSeed hBD hBsize using growth_category_segment_samplers W h01 models G σ hG hσ hgrowth γ hγ L ε hε hεle hL hmix
  let g0 := certifiedConcatenatedSample (fun i j => W i j) l (graphCategoryBlockLengths_total R γ)
    (γ 0) (γ (Fin.last n)) y (fun _ => ε / 2) B
  have hg0 : finiteSeedLaw g0 = categoryApproximateLaw R γ (fun i => finiteSeedLaw (B i).sample) :=
    certifiedConcatenatedSample_law (fun i j => W i j) l (graphCategoryBlockLengths_total R γ)
      (γ 0) (γ (Fin.last n)) y (fun _ => ε / 2) B
  obtain ⟨S, hbits, he, hD, hsize⟩ := certified_concatenation_circuit (fun i j => W i j) l
    (graphCategoryBlockLengths_total R γ) (γ 0) (γ (Fin.last n)) y (fun _ => ε / 2) B 11 hBD
  have hr : (∑ i, (B i).seedLength) = growthCategorySeedBudget models G σ γ L ε := by
    simp only [hBm]
    rfl
  let f := fun seed : Bits (growthCategorySeedBudget models G σ γ L ε) =>
    g0 (fun j => seed (Fin.cast hr j))
  have hf : finiteSeedLaw f = categoryApproximateLaw R γ (fun i => finiteSeedLaw (B i).sample) :=
    (finiteSeedLaw_cast hr g0).trans hg0
  obtain ⟨_, _, hsupp, htv⟩ := approximate_constructed_category (fun i j => W i j) hW R γ hγ
    (fun i => finiteSeedLaw (B i).sample) (fun i => finiteSeedLaw_nonneg (B i).sample)
    (fun i => finiteSeedLaw_sum (B i).sample) (by
      intro i b hb
      obtain ⟨seed, rfl⟩ := (finiteSeedLaw_pos_iff (B i).sample b).mp hb
      exact (B i).sample_positive seed)
    (fun _ => ε / 2) (fun i => (B i).error)
  refine ⟨f, S, hbits.trans hr, ?_, hD, ?_, ?_, ?_⟩
  · intro seed i x
    have he' := he (fun j => seed (Fin.cast hr j)) i x
    have hcast : (fun j => seed (Fin.cast hr (Fin.cast hbits j))) =
        fun j => seed (Fin.cast (hbits.trans hr) j) := by
      funext j
      congr 1
    rw [hcast] at he'
    exact he'
  · have hbsize := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      Nat.mul_le_mul_left ((l i + 1) * Fintype.card Q) (hBsize i))
    rw [hr] at hsize
    unfold growthCategoryCircuitSize
    dsimp only
    dsimp only [l, R] at hbsize hsize
    omega
  · intro seed
    apply hsupp
    rw [← hf]
    exact (finiteSeedLaw_pos_iff f (f seed)).mpr ⟨seed, rfl⟩
  · rw [hf]
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using htv

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_GrowthCategorySeed
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

/-- Summing all constructed segment seeds charges the total path length
once. There are at most twice the state count many segments, and the
overhead coefficient is independent of the cutoff multiplier. -/
theorem growthCategorySeedBudget_bound {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (h01 : ∀ x y, W x y = 0 ∨ W x y = 1)
    (models : ∀ c : CyclicSCCIndex W, SCCPeriodicModel W c.val)
    (G σ : ℝ) (hG : 1 ≤ G) (hσ : 1 ≤ σ)
    (hgrowth : ∀ (c : CyclicSCCIndex W) (b : ℕ) (x y : SCCState W c.val),
      (sccMatrix W c.val ^ b) x y ≤ G * σ ^ b)
    {n : ℕ} (γ : Fin (n + 1) → Q) (hγ : 0 < edgePathWeight W γ)
    (L : ℕ) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1) (hL : 0 < L)
    (hmix : ∀ c, (models c).blockExponent ∣ L ∧
      (models c).coefficient * (models c).rate ^ (L / (models c).blockExponent) ≤ ε / (8 * (n + 1 : ℕ))) :
    (growthCategorySeedBudget models G σ γ L ε : ℝ) ≤
      n * (Real.log σ / Real.log 2) +
        (2 * ((n : ℝ) / L) + 2 * Fintype.card Q) *
          growthSeedOverhead (Fintype.card Q) G (ε / (8 * (n + 1 : ℕ))) := by
  have hW : ∀ x y, 0 ≤ W x y := by
    intro x y
    rcases h01 x y with h | h <;> simp [h]
  let R := fun i j => 0 < W i j
  let l := graphCategoryBlockLengths R γ
  let cost := growthSeedOverhead (Fintype.card Q) G (ε / (8 * (n + 1 : ℕ)))
  have hq : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨γ 0⟩
  have hδ := localRoundingTolerance_bounds n hε hεle
  have hcost : 0 ≤ cost := growthSeedOverhead_nonneg _ hq G _ hG hδ.1 (hδ.2.1.trans hδ.2.2)
  have hcount : (graphInteriorCuts R γ).card + 1 ≤ 2 * Fintype.card Q :=
    (graphCategoryBlockLengths_count R γ ((edgePathWeight_pos_iff W hW γ).mp hγ)).trans (Nat.sub_le _ _)
  have hcount' : ((graphInteriorCuts R γ).card + 1 : ℕ) ≤ (2 * Fintype.card Q : ℝ) := by
    exact_mod_cast hcount
  have hlen : ∑ i, (l i : ℝ) = n := by
    have hh : ∑ i, l i = n := (bridgeBlockLength_eq_sum l).symm.trans (graphCategoryBlockLengths_total R γ)
    exact_mod_cast hh
  have hlocal (i : Fin ((graphInteriorCuts R γ).card + 1)) :
      (growthComponentSeedBudget models G σ (categorySegmentStart R γ i) n (l i) L ε : ℝ) ≤
        (l i) * (Real.log σ / Real.log 2) + (2 * ((l i : ℝ) / L) + 1) * cost := by
    obtain ⟨B, hm, hseed, _, _⟩ := growth_category_segment_samplers W h01 models G σ hG hσ
      hgrowth γ hγ L ε hε hεle hL hmix i
    rw [← hm]
    exact hseed
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hlocal i)
  have he : (∑ i : Fin ((graphInteriorCuts R γ).card + 1),
      ((l i : ℝ) * (Real.log σ / Real.log 2) + (2 * ((l i : ℝ) / L) + 1) * cost)) =
      n * (Real.log σ / Real.log 2) +
        (2 * ((n : ℝ) / L) + ((graphInteriorCuts R γ).card + 1 : ℕ)) * cost := by
    simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hlen,
      ← Finset.mul_sum, ← Finset.sum_div, mul_one]
  rw [he] at hsum
  change ((∑ i, growthComponentSeedBudget models G σ (categorySegmentStart R γ i) n (l i) L ε : ℕ) : ℝ) ≤ _
  rw [Nat.cast_sum]
  apply hsum.trans
  change (n : ℝ) * (Real.log σ / Real.log 2) +
    (2 * ((n : ℝ) / L) + ((graphInteriorCuts R γ).card + 1 : ℕ)) * cost ≤
    n * (Real.log σ / Real.log 2) + (2 * ((n : ℝ) / L) + 2 * Fintype.card Q) * cost
  gcongr

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_GrowthAcceptedCategory
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

local instance growthAcceptedCategoryDecEq {Q : Type} [Fintype Q] {n : ℕ} :
    DecidableEq (GraphCategory Q n) := Classical.decEq _

/-- Each positive accepting category of a possibly incomplete graph has
an actual depth-eleven circuit. Its target is the original accepted-path
fiber, with a uniform epsilon/2 error allocation. -/
theorem growth_accepted_category_circuit {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (h01 : ∀ x y, W x y = 0 ∨ W x y = 1)
    (s : Q) (F : Finset Q) {n : ℕ} (c : AcceptedGraphCategory W s F n)
    (models : ∀ d : CyclicSCCIndex W, SCCPeriodicModel W d.val)
    (G σ : ℝ) (hG : 1 ≤ G) (hσ : 1 ≤ σ)
    (hgrowth : ∀ (d : CyclicSCCIndex W) (b : ℕ) (x y : SCCState W d.val),
      (sccMatrix W d.val ^ b) x y ≤ G * σ ^ b)
    (L : ℕ) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1) (hL : 0 < L)
    (hmix : ∀ d, (models d).blockExponent ∣ L ∧
      (models d).coefficient * (models d).rate ^ (L / (models d).blockExponent) ≤
        categorySegmentTolerance (Fintype.card Q) ε / (8 * (n + 1 : ℕ))) :
    let η := categorySegmentTolerance (Fintype.card Q) ε
    let γ := acceptedGraphRepresentative W hW s F c
    ∃ f : Bits (growthCategorySeedBudget models G σ γ L η) → (Fin (n + 1) → Q),
      ∃ S : Circuit (Fin (n + 1) × Q), ∃ hbits : S.randomBits = growthCategorySeedBudget models G σ γ L η,
      (∀ seed i x, S.eval (fun j => seed (Fin.cast hbits j)) (i, x) = decide (f seed i = x)) ∧
      S.depth ≤ 11 ∧ S.size ≤ growthCategoryCircuitSize models G σ γ L η ∧
      (∀ seed, 0 < fiberWeight (graphCategory (fun x y => 0 < W x y))
        (acceptedGraphWeight W s F) c.val (f seed)) ∧
      tv (finiteSeedLaw f) (normalizeWeights (fiberWeight (graphCategory (fun x y => 0 < W x y))
        (acceptedGraphWeight W s F) c.val)) ≤ ε / 2 := by
  classical
  dsimp only
  let γ := acceptedGraphRepresentative W hW s F c
  have hspec := acceptedGraphRepresentative_spec W hW s F c
  have hq : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨s⟩
  obtain ⟨hη, hηle, hηeq⟩ := categorySegmentTolerance_bounds (Fintype.card Q) hq ε hε hεle
  obtain ⟨f, S, hbits, he, hD, hsize, hsupp, htv⟩ := growth_constructed_category_circuit
    W h01 models G σ hG hσ hgrowth γ hspec.2.2.2 L
    (categorySegmentTolerance (Fintype.card Q) ε) hη hηle hL hmix
  have hfiber := accepted_graph_category_fiber W hW s F γ hspec.2.1 hspec.2.2.1 hspec.2.2.2
  refine ⟨f, S, hbits, he, hD, hsize, ?_, ?_⟩
  · intro seed
    rw [← hspec.1, hfiber]
    dsimp only
    rw [if_pos (hsupp seed).1]
    exact (hsupp seed).2
  · rw [← hspec.1, hfiber]
    apply htv.trans
    have hgraph := (edgePathWeight_pos_iff W hW γ).mp hspec.2.2.2
    have hk : (graphInteriorCuts (fun x y => 0 < W x y) γ).card + 1 ≤ 2 * Fintype.card Q :=
      (graphCategoryBlockLengths_count _ γ hgraph).trans (Nat.sub_le _ _)
    have hk' : ((graphInteriorCuts (fun x y => 0 < W x y) γ).card + 1 : ℕ) ≤ (2 * Fintype.card Q : ℝ) := by
      exact_mod_cast hk
    exact (mul_le_mul_of_nonneg_right hk' (div_nonneg hη.le (by norm_num))).trans hηeq.le

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ConditionalSamplerCircuit
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- The actual conditional circuit computes the same shared-seed sampler
whose law is the mixture of the branch laws. Branches may use different
seed lengths; their maximum is charged once. -/
theorem conditional_sampler_circuit {I Ω Out : Type} [Fintype I] [DecidableEq I]
    [Fintype Out] {r M : ℕ} (m : I → ℕ) (hm : ∀ i, m i ≤ M)
    (encode : Ω → Out → Bool) (f : Bits r → I) (g : ∀ i, Bits (m i) → Ω)
    (A : Circuit I) (ha : A.randomBits = r)
    (hA : ∀ seed i, A.eval (fun j => seed (Fin.cast ha j)) i = decide (f seed = i))
    (B : I → Circuit Out) (hb : ∀ i, (B i).randomBits = m i)
    (hB : ∀ i seed o, (B i).eval (fun j => seed (Fin.cast (hb i) j)) o = encode (g i seed) o)
    (D : ℕ) (hD : ∀ i, (B i).depth ≤ D) :
    ∃ S : Circuit Out, ∃ hbits : S.randomBits = r + M,
      (∀ seed o, S.eval (fun j => seed (Fin.cast hbits j)) o =
        encode (sharedConditionalSeedSample m hm f g seed) o) ∧
      S.depth ≤ max A.depth D + 2 ∧
      S.size ≤ (r + M) + Fintype.card I * A.size +
        Fintype.card Out * (∑ i, (B i).size) +
        2 * (Fintype.card I + Fintype.card I * Fintype.card Out) +
        Fintype.card Out * (4 * Fintype.card I + 2) := by
  subst r
  have hmB : ∀ i, (B i).randomBits ≤ M := fun i => (hb i).trans_le (hm i)
  obtain ⟨S, hbits, he, hdepth, hsize⟩ :=
    conditional_circuit_assembly A B f hA M D hmB hD
  refine ⟨S, hbits, ?_, hdepth, hsize⟩
  intro seed o
  rw [he]
  let c := f (seedPairEquiv A.randomBits M seed).1
  let z : Bits (m c) := fun j => (seedPairEquiv A.randomBits M seed).2 (Fin.castLE (hm c) j)
  have hz : (fun j => z (Fin.cast (hb c) j)) =
      (fun j => (seedPairEquiv A.randomBits M seed).2 (Fin.castLE (hmB c) j)) := by
    funext j
    apply congrArg (seedPairEquiv A.randomBits M seed).2
    apply Fin.ext
    rfl
  have h := hB c z o
  rw [hz] at h
  exact h

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SamplerCircuitLaw
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

/-- Pointwise realization of an injectively encoded sampler identifies
the original circuit mass with the sampler's finite fair-bit law. -/
theorem sampler_circuit_mass {Ω Out : Type} [Fintype Ω] [DecidableEq Ω]
    {m : ℕ} (f : Bits m → Ω) (encode : Ω → Out → Bool)
    (hinj : Function.Injective encode) (S : Circuit Out) (hbits : S.randomBits = m)
    (he : ∀ seed, S.eval (fun j => seed (Fin.cast hbits j)) = encode (f seed)) :
    mass S encode = finiteSeedLaw f := by
  classical
  subst m
  funext x
  unfold mass finiteSeedLaw
  congr 2
  rw [Fintype.card_subtype]
  congr 1
  apply Finset.filter_congr
  intro seed _
  have he' : S.eval seed = encode (f seed) := he seed
  rw [he']
  exact hinj.eq_iff

/-- A pointwise support certificate for the actual sampler is also the
support certificate required by the original circuit definitions. -/
theorem sampler_circuit_support {Ω Out : Type} {m : ℕ}
    (f : Bits m → Ω) (encode : Ω → Out → Bool) (p : Ω → ℝ)
    (S : Circuit Out) (hbits : S.randomBits = m)
    (he : ∀ seed, S.eval (fun j => seed (Fin.cast hbits j)) = encode (f seed))
    (hs : ∀ seed, 0 < p (f seed)) : SupportPreserving S encode p := by
  subst m
  exact fun seed => ⟨f seed, he seed, hs seed⟩

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_GrowthAcceptedCircuit
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

local instance growthAcceptedCircuitDecEq {Q : Type} [Fintype Q] {n : ℕ} :
    DecidableEq (GraphCategory Q n) := Classical.decEq _

def graphPathEncode {Q : Type} [DecidableEq Q] {n : ℕ}
    (γ : Fin (n + 1) → Q) : (Fin (n + 1) × Q) → Bool :=
  fun z => decide (γ z.1 = z.2)

theorem graphPathEncode_injective {Q : Type} [DecidableEq Q] (n : ℕ) :
    Function.Injective (@graphPathEncode Q _ n) := by
  intro γ η h
  funext i
  have hi := congrFun h (i, γ i)
  have hval : η i = γ i := of_decide_eq_true (by
    simpa only [graphPathEncode, decide_true] using hi.symm)
  exact hval.symm

def growthAcceptedConditionalSeed {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (s : Q) (F : Finset Q)
    (models : ∀ d : CyclicSCCIndex W, SCCPeriodicModel W d.val)
    (G σ : ℝ) (n L : ℕ) (ε : ℝ) : ℕ :=
  Finset.univ.sup (fun c : AcceptedGraphCategory W s F n =>
    growthCategorySeedBudget models G σ (acceptedGraphRepresentative W hW s F c) L
      (categorySegmentTolerance (Fintype.card Q) ε))

def growthAcceptedSeedBudget {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (s : Q) (F : Finset Q)
    (models : ∀ d : CyclicSCCIndex W, SCCPeriodicModel W d.val)
    (G σ : ℝ) (n L : ℕ) (ε : ℝ) : ℕ :=
  acceptedGraphChoiceSeed W s F n ε + growthAcceptedConditionalSeed W hW s F models G σ n L ε

def growthAcceptedCircuitSize {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (s : Q) (F : Finset Q)
    (models : ∀ d : CyclicSCCIndex W, SCCPeriodicModel W d.val)
    (G σ : ℝ) (n L : ℕ) (ε : ℝ) : ℕ :=
  let c := Fintype.card (AcceptedGraphCategory W s F n)
  let o := (n + 1) * Fintype.card Q
  growthAcceptedSeedBudget W hW s F models G σ n L ε + c * acceptedGraphChoiceSize W s F n ε +
    o * (∑ d : AcceptedGraphCategory W s F n,
      growthCategoryCircuitSize models G σ (acceptedGraphRepresentative W hW s F d) L
        (categorySegmentTolerance (Fintype.card Q) ε)) +
    2 * (c + c * o) + o * (4 * c + 2)

/-- Complete full-path sampler for an incomplete zero-one graph. The
category selector and every conditional branch are actual circuits, and
the shared conditional seed is their maximum rather than their sum.
Uniform asymptotic size bounds remain a separate obligation. -/
theorem growth_accepted_graph_circuit {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (h01 : ∀ x y, W x y = 0 ∨ W x y = 1)
    (s : Q) (F : Finset Q) {n : ℕ}
    (hZ : 0 < ∑ γ : Fin (n + 1) → Q, acceptedGraphWeight W s F γ)
    (models : ∀ d : CyclicSCCIndex W, SCCPeriodicModel W d.val)
    (G σ : ℝ) (hG : 1 ≤ G) (hσ : 1 ≤ σ)
    (hgrowth : ∀ (d : CyclicSCCIndex W) (b : ℕ) (x y : SCCState W d.val),
      (sccMatrix W d.val ^ b) x y ≤ G * σ ^ b)
    (L : ℕ) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1) (hL : 0 < L)
    (hmix : ∀ d, (models d).blockExponent ∣ L ∧
      (models d).coefficient * (models d).rate ^ (L / (models d).blockExponent) ≤
        categorySegmentTolerance (Fintype.card Q) ε / (8 * (n + 1 : ℕ))) :
    ∃ f : Bits (growthAcceptedSeedBudget W hW s F models G σ n L ε) → (Fin (n + 1) → Q),
      ∃ S : Circuit (Fin (n + 1) × Q),
      ∃ hbits : S.randomBits = growthAcceptedSeedBudget W hW s F models G σ n L ε,
      (∀ seed, S.eval (fun j => seed (Fin.cast hbits j)) = graphPathEncode (f seed)) ∧
      S.depth ≤ 13 ∧ S.size ≤ growthAcceptedCircuitSize W hW s F models G σ n L ε ∧
      (∀ seed, 0 < acceptedGraphWeight W s F (f seed)) ∧
      mass S graphPathEncode = finiteSeedLaw f ∧
      tv (finiteSeedLaw f) (normalizeWeights (acceptedGraphWeight W s F)) ≤ ε := by
  classical
  let m := fun c : AcceptedGraphCategory W s F n =>
    growthCategorySeedBudget models G σ (acceptedGraphRepresentative W hW s F c) L
      (categorySegmentTolerance (Fintype.card Q) ε)
  have hm : ∀ c, m c ≤ growthAcceptedConditionalSeed W hW s F models G σ n L ε :=
    fun c => Finset.le_sup (Finset.mem_univ c)
  choose g B hb he hD hsize hs ht using fun c =>
    growth_accepted_category_circuit W hW h01 s F c models G σ hG hσ hgrowth L ε hε hεle hL hmix
  obtain ⟨a, A, ha, hea, hcat, hAD, hAsize⟩ := accepted_graph_category_selector W hW s F hZ ε hε
  let f := sharedConditionalSeedSample m hm a g
  have hflaw : finiteSeedLaw f = mixtureLaw (finiteSeedLaw a) (fun c => finiteSeedLaw (g c)) :=
    sharedConditionalSeedSample_law m hm a g
  obtain ⟨S, hbits, hSe, hSD, hSs⟩ := conditional_sampler_circuit m hm graphPathEncode a g A ha hea
    B hb (fun c seed z => he c seed z.1 z.2) 11 hD
  have hsupp : ∀ c γ, 0 < finiteSeedLaw (g c) γ →
      0 < fiberWeight (graphCategory (fun x y => 0 < W x y))
        (acceptedGraphWeight W s F) c.val γ := by
    intro c γ hp
    obtain ⟨seed, rfl⟩ := (finiteSeedLaw_pos_iff (g c) γ).mp hp
    exact hs c seed
  obtain ⟨_, _, hsupport, htv⟩ := approximate_disintegration
    (graphCategory (fun x y => 0 < W x y)) (acceptedGraphWeight W s F)
    (acceptedGraphWeight_nonneg W hW s F) hZ
    (finiteSeedLaw a) (fun c => finiteSeedLaw (g c)) (finiteSeedLaw_nonneg a)
    (finiteSeedLaw_sum a) (fun c => finiteSeedLaw_nonneg (g c))
    (fun c => finiteSeedLaw_sum (g c)) hsupp (ε / 2) (ε / 2) hcat ht
  have hencode : ∀ seed, S.eval (fun j => seed (Fin.cast hbits j)) = graphPathEncode (f seed) :=
    fun seed => funext (hSe seed)
  refine ⟨f, S, hbits, hencode, ?_, ?_, ?_,
    sampler_circuit_mass f graphPathEncode (graphPathEncode_injective n) S hbits hencode, ?_⟩
  · omega
  · apply hSs.trans
    simp only [Fintype.card_prod, Fintype.card_fin]
    unfold growthAcceptedCircuitSize growthAcceptedSeedBudget
    dsimp only
    gcongr
    exact hsize _
  · intro seed
    apply hsupport
    rw [← hflaw]
    exact (finiteSeedLaw_pos_iff f (f seed)).mpr ⟨seed, rfl⟩
  · exact (congrArg (fun p => tv p (normalizeWeights (acceptedGraphWeight W s F))) hflaw).trans_le
      (by linarith)

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SubcriticalSeedSlack
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

/-- A global, explicit linear envelope with any positive slope. -/
theorem log_succ_arbitrary_slope (a : ℝ) (ha : 0 < a) (n : ℕ) :
    Real.log (n + 1 : ℕ) ≤ a * n + (a - 1 - Real.log a) := by
  have h := Real.log_le_sub_one_of_pos
    (mul_pos ha (by positivity : (0 : ℝ) < (n + 1 : ℕ)))
  rw [Real.log_mul ha.ne' (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0)] at h
  push_cast at h ⊢
  nlinarith

theorem logarithmic_overhead_linear_slack (K κ : ℝ) (hK : 0 ≤ K) (hκ : 0 < κ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ,
      K * (Real.log (n + 1 : ℕ) / Real.log 2) ≤ κ * n + D := by
  by_cases hzero : K = 0
  · subst K
    exact ⟨0, le_rfl, fun n => by simpa using mul_nonneg hκ.le (Nat.cast_nonneg n)⟩
  have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hzero)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  let a := κ * Real.log 2 / K
  have ha : 0 < a := div_pos (mul_pos hκ hlog2) hKpos
  let D := |(K / Real.log 2) * (a - 1 - Real.log a)|
  refine ⟨D, abs_nonneg _, ?_⟩
  intro n
  have h := mul_le_mul_of_nonneg_left (log_succ_arbitrary_slope a ha n)
    (div_nonneg hK hlog2.le)
  have he : (K / Real.log 2) * a = κ := by
    dsimp only [a]
    field_simp
  calc
    K * (Real.log (n + 1 : ℕ) / Real.log 2) =
      (K / Real.log 2) * Real.log (n + 1 : ℕ) := by ring
    _ ≤ (K / Real.log 2) * (a * n + (a - 1 - Real.log a)) := h
    _ = κ * n + (K / Real.log 2) * (a - 1 - Real.log a) := by
      rw [mul_add, ← mul_assoc, he]
    _ ≤ κ * n + D := add_le_add le_rfl (le_abs_self _)

theorem log_accuracy_ratio_split (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Real.log ((n + 1 : ℕ) / ε) / Real.log 2 =
      Real.log (n + 1 : ℕ) / Real.log 2 + logInv ε := by
  rw [Real.log_div (by positivity) hε.ne']
  simp only [logInv, Real.log_div one_ne_zero hε.ne', Real.log_one, zero_sub]
  ring

/-- A strictly subunit linear coefficient pays for all logarithmic length
overhead, leaving exactly coefficient one and a log-accuracy remainder. -/
theorem subunit_seed_coefficient_absorbs_log (h K : ℝ) (hh : h < 1) (hK : 0 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
      h * n + K * (Real.log ((n + 1 : ℕ) / ε) / Real.log 2) ≤ n + C * logInv ε := by
  obtain ⟨D, hD, hslack⟩ := logarithmic_overhead_linear_slack K (1 - h) hK (by linarith)
  refine ⟨K + D, add_nonneg hK hD, ?_⟩
  intro n ε hε hεle
  rw [log_accuracy_ratio_split n ε hε]
  have hlog := logInv_ge_one hε hεle
  have hDlog : D ≤ D * logInv ε := by nlinarith
  have hn := hslack n
  nlinarith

/-- The arithmetic end of the C.3 proof. The cutoff factor and final
accuracy coefficient are chosen before n, epsilon and the actual seed.
The separate circuit construction must establish the displayed premise. -/
theorem subcritical_block_budget_absorption (h C₁ C₂ : ℝ)
    (hh : h < 1) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧
      ∀ (n B : ℕ) (ε r : ℝ), 0 < ε → ε ≤ 1 / 2 → 0 < B →
        a * (Real.log ((n + 1 : ℕ) / ε) / Real.log 2) ≤ B →
        r ≤ h * n + C₁ * n * (Real.log ((n + 1 : ℕ) / ε) / Real.log 2) / B +
          C₂ * (Real.log ((n + 1 : ℕ) / ε) / Real.log 2) →
        r ≤ n + C * logInv ε := by
  let κ := (1 - h) / 2
  have hκ : 0 < κ := by dsimp [κ]; linarith
  let a := 1 + C₁ / κ
  have ha : 0 < a := by dsimp [a]; positivity
  have hCa : C₁ ≤ κ * a := by
    dsimp only [a]
    rw [mul_add, mul_one, mul_div_cancel₀ _ hκ.ne']
    linarith
  obtain ⟨C, hC, hfinal⟩ := subunit_seed_coefficient_absorbs_log (h + κ) C₂
    (by dsimp only [κ]; linarith) hC₂
  refine ⟨a, C, ha, hC, ?_⟩
  intro n B ε r hε hεle hB hcut hr
  let t := Real.log ((n + 1 : ℕ) / ε) / Real.log 2
  have ht : 0 ≤ t := by
    dsimp only [t]
    rw [log_accuracy_ratio_split n ε hε]
    exact add_nonneg
      (div_nonneg (Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)))
        (Real.log_pos (by norm_num)).le)
      (logInv_nonneg_of_le_one ε hε (by linarith))
  have hBt : (0 : ℝ) < B := Nat.cast_pos.mpr hB
  have hcost : C₁ * n * t / B ≤ κ * n := by
    apply (div_le_iff₀ hBt).mpr
    have h1 := mul_le_mul_of_nonneg_right hCa ht
    have h2 := mul_le_mul_of_nonneg_left hcut hκ.le
    have h3 : C₁ * t ≤ κ * B := by nlinarith
    have h4 := mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg n)
    nlinarith
  have hf := hfinal n ε hε hεle
  change r ≤ h * n + C₁ * n * t / B + C₂ * t at hr
  change (h + κ) * n + C₂ * t ≤ n + C * logInv ε at hf
  nlinarith

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_PrecisionLogBudget
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

def samplingLogRatio (n : ℕ) (ε : ℝ) : ℝ :=
  Real.log ((n + 1 : ℕ) / ε) / Real.log 2

theorem samplingLogRatio_bounds (n : ℕ) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1 / 2) :
    1 ≤ samplingLogRatio n ε ∧ logInv ε ≤ samplingLogRatio n ε ∧
      Real.log (n + 1 : ℕ) / Real.log 2 ≤ samplingLogRatio n ε := by
  have hn : 0 ≤ Real.log (n + 1 : ℕ) / Real.log 2 :=
    div_nonneg (Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)))
      (Real.log_pos (by norm_num)).le
  have he := logInv_ge_one hε hεle
  unfold samplingLogRatio
  rw [log_accuracy_ratio_split n ε hε]
  constructor
  · linarith
  constructor <;> linarith

theorem logInv_scaled_precision (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) (n : ℕ) :
    logInv (ε / (c * (n + 1 : ℕ))) = Real.log c / Real.log 2 + samplingLogRatio n ε := by
  have he : 1 / (ε / (c * (n + 1 : ℕ))) = c * ((n + 1 : ℕ) / ε) := by
    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  unfold logInv samplingLogRatio
  rw [he, Real.log_mul hc.ne' (by positivity), add_div]

/-- Local precision overhead is a constant times t=log2((n+1)/epsilon),
with a constant independent of the cutoff multiplier. -/
theorem growthSeedOverhead_log_bound (q : ℕ) (hq : 0 < q) (G c : ℝ)
    (hG : 1 ≤ G) (hc : 1 ≤ c) (n : ℕ) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1 / 2) :
    growthSeedOverhead q G (ε / (c * (n + 1 : ℕ))) ≤
      (stateLog q + Real.log G / Real.log 2 + Real.log c / Real.log 2 + 2) * samplingLogRatio n ε := by
  have ht := (samplingLogRatio_bounds n ε hε hεle).1
  have hqlog := stateLog_nonneg hq
  have hGlog := div_nonneg (Real.log_nonneg hG) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hclog := div_nonneg (Real.log_nonneg hc) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hpay := mul_nonneg (by linarith : 0 ≤ stateLog q + Real.log G / Real.log 2 + Real.log c / Real.log 2 + 1)
    (sub_nonneg.mpr ht)
  unfold growthSeedOverhead
  rw [logInv_scaled_precision c ε (zero_lt_one.trans_le hc) hε n]
  nlinarith

/-- Selecting from polynomially many categories costs O(t) fair bits.
The logarithmic bound is retained here so it can be paid by subcritical
linear savings, unlike a coarser O(n+log(1/epsilon)) estimate. -/
theorem roundingSeed_polynomial_log_bound (K d M n : ℕ) (hK : 0 < K) (hM : 0 < M)
    (hcard : M ≤ K * (n + 1) ^ d) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1 / 2) :
    (roundingSeed M (ε / 2) : ℝ) ≤ (stateLog K + d + 3) * samplingLogRatio n ε := by
  have hb := roundingSeed_upper_of_card_le M (K * (n + 1) ^ d) hM hcard
    (ε / 2) (by positivity) (by linarith)
  have hlog : Real.log (K * (n + 1) ^ d : ℕ) / Real.log 2 =
      stateLog K + d * (Real.log (n + 1 : ℕ) / Real.log 2) := by
    rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (Nat.cast_pos.mpr hK).ne' (by positivity), Real.log_pow]
    unfold stateLog
    ring
  rw [hlog, logInv_half hε] at hb
  have ht := samplingLogRatio_bounds n ε hε hεle
  have hd := mul_le_mul_of_nonneg_left ht.2.2 (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have hKlog := stateLog_nonneg hK
  have hpay := mul_nonneg (by linarith : 0 ≤ stateLog K + 2) (sub_nonneg.mpr ht.1)
  nlinarith

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_GrowthAcceptedSeed
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix



def acceptedGraphCardCoefficient (q : ℕ) : ℕ := q * q * (q * q + 1) ^ q

def growthAcceptedOverhead (q : ℕ) (G : ℝ) : ℝ :=
  stateLog q + Real.log G / Real.log 2 + Real.log (16 * q : ℝ) / Real.log 2 + 2

def acceptedGraphSelectorCoefficient (q : ℕ) : ℝ :=
  stateLog (acceptedGraphCardCoefficient q) + q + 3

theorem growthAcceptedOverhead_nonneg (q : ℕ) (hq : 0 < q) (G : ℝ) (hG : 1 ≤ G) :
    0 ≤ growthAcceptedOverhead q G := by
  have hq' : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr hq
  have hqlog := stateLog_nonneg hq
  have hGlog := div_nonneg (Real.log_nonneg hG) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hclog := div_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 16 * q))
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  unfold growthAcceptedOverhead
  linarith

theorem acceptedGraphSelectorCoefficient_nonneg (q : ℕ) (hq : 0 < q) :
    0 ≤ acceptedGraphSelectorCoefficient q := by
  have hK : 0 < acceptedGraphCardCoefficient q := by
    unfold acceptedGraphCardCoefficient
    positivity
  have hlog := stateLog_nonneg hK
  unfold acceptedGraphSelectorCoefficient
  positivity

theorem acceptedGraph_local_precision_eq (q n : ℕ) (ε : ℝ) :
    categorySegmentTolerance q ε / (8 * (n + 1 : ℕ)) = ε / ((16 * q : ℝ) * (n + 1 : ℕ)) := by
  unfold categorySegmentTolerance
  rw [div_div]
  congr 1
  ring

theorem acceptedGraphChoiceSeed_log_bound {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s : Q) (F : Finset Q) (n : ℕ)
    (hZ : 0 < ∑ γ : Fin (n + 1) → Q, acceptedGraphWeight W s F γ)
    (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1 / 2) :
    (acceptedGraphChoiceSeed W s F n ε : ℝ) ≤
      acceptedGraphSelectorCoefficient (Fintype.card Q) * samplingLogRatio n ε := by
  have hq : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨s⟩
  have hK : 0 < acceptedGraphCardCoefficient (Fintype.card Q) := by
    unfold acceptedGraphCardCoefficient
    positivity
  have hM : 0 < Fintype.card (AcceptedGraphCategory W s F n) :=
    Fintype.card_pos_iff.mpr (acceptedGraphCategory_nonempty W hW s F n hZ)
  exact roundingSeed_polynomial_log_bound _ _ _ _ hK hM
    (acceptedGraphCategory_card_polynomial W s F n) ε hε hεle

/-- A single shared seed serves all positive accepting categories. Its
maximum obeys the same bound as each branch, with no category-count
factor in the random-bit cost. -/
theorem growthAcceptedConditionalSeed_bound {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (h01 : ∀ x y, W x y = 0 ∨ W x y = 1)
    (s : Q) (F : Finset Q) {n : ℕ}
    (hZ : 0 < ∑ γ : Fin (n + 1) → Q, acceptedGraphWeight W s F γ)
    (models : ∀ d : CyclicSCCIndex W, SCCPeriodicModel W d.val)
    (G σ : ℝ) (hG : 1 ≤ G) (hσ : 1 ≤ σ)
    (hgrowth : ∀ (d : CyclicSCCIndex W) (b : ℕ) (x y : SCCState W d.val),
      (sccMatrix W d.val ^ b) x y ≤ G * σ ^ b)
    (L : ℕ) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1) (hL : 0 < L)
    (hmix : ∀ d, (models d).blockExponent ∣ L ∧
      (models d).coefficient * (models d).rate ^ (L / (models d).blockExponent) ≤
        categorySegmentTolerance (Fintype.card Q) ε / (8 * (n + 1 : ℕ))) :
    (growthAcceptedConditionalSeed W hW s F models G σ n L ε : ℝ) ≤
      n * (Real.log σ / Real.log 2) + (2 * ((n : ℝ) / L) + 2 * Fintype.card Q) *
        growthSeedOverhead (Fintype.card Q) G
          (categorySegmentTolerance (Fintype.card Q) ε / (8 * (n + 1 : ℕ))) := by
  classical
  letI : Nonempty (AcceptedGraphCategory W s F n) := acceptedGraphCategory_nonempty W hW s F n hZ
  let m := fun c : AcceptedGraphCategory W s F n =>
    growthCategorySeedBudget models G σ (acceptedGraphRepresentative W hW s F c) L
      (categorySegmentTolerance (Fintype.card Q) ε)
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty m
  change ((Finset.univ.sup m : ℕ) : ℝ) ≤ _
  rw [hc]
  have hq : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨s⟩
  obtain ⟨hη, hηle, _⟩ := categorySegmentTolerance_bounds (Fintype.card Q) hq ε hε hεle
  exact growthCategorySeedBudget_bound W h01 models G σ hG hσ hgrowth
    (acceptedGraphRepresentative W hW s F c) (acceptedGraphRepresentative_spec W hW s F c).2.2.2
    L (categorySegmentTolerance (Fintype.card Q) ε) hη hηle hL hmix

/-- Exact outer seed accounting in the form needed for the coefficient-one
subcritical argument. Both overhead coefficients are fixed before the
cutoff multiplier, length and accuracy are chosen. -/
theorem growthAcceptedSeedBudget_log_bound {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (h01 : ∀ x y, W x y = 0 ∨ W x y = 1)
    (s : Q) (F : Finset Q) {n : ℕ}
    (hZ : 0 < ∑ γ : Fin (n + 1) → Q, acceptedGraphWeight W s F γ)
    (models : ∀ d : CyclicSCCIndex W, SCCPeriodicModel W d.val)
    (G σ : ℝ) (hG : 1 ≤ G) (hσ : 1 ≤ σ)
    (hgrowth : ∀ (d : CyclicSCCIndex W) (b : ℕ) (x y : SCCState W d.val),
      (sccMatrix W d.val ^ b) x y ≤ G * σ ^ b)
    (L : ℕ) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1 / 2) (hL : 0 < L)
    (hmix : ∀ d, (models d).blockExponent ∣ L ∧
      (models d).coefficient * (models d).rate ^ (L / (models d).blockExponent) ≤
        categorySegmentTolerance (Fintype.card Q) ε / (8 * (n + 1 : ℕ))) :
    (growthAcceptedSeedBudget W hW s F models G σ n L ε : ℝ) ≤
      (Real.log σ / Real.log 2) * n +
        (2 * growthAcceptedOverhead (Fintype.card Q) G) * n * samplingLogRatio n ε / L +
        (2 * Fintype.card Q * growthAcceptedOverhead (Fintype.card Q) G +
          acceptedGraphSelectorCoefficient (Fintype.card Q)) * samplingLogRatio n ε := by
  have hq : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨s⟩
  have hq' : (1 : ℝ) ≤ Fintype.card Q := Nat.one_le_cast.mpr hq
  have hbranch := growthAcceptedConditionalSeed_bound W hW h01 s F hZ models G σ hG hσ hgrowth
    L ε hε (by linarith) hL hmix
  have hselector := acceptedGraphChoiceSeed_log_bound W hW s F n hZ ε hε hεle
  have hover := growthSeedOverhead_log_bound (Fintype.card Q) hq G (16 * Fintype.card Q)
    hG (by linarith) n ε hε hεle
  rw [acceptedGraph_local_precision_eq] at hbranch
  have hfactor : 0 ≤ 2 * ((n : ℝ) / L) + 2 * Fintype.card Q := by positivity
  have hpay := mul_le_mul_of_nonneg_left hover hfactor
  unfold growthAcceptedSeedBudget
  rw [Nat.cast_add]
  apply (add_le_add hselector hbranch).trans
  change acceptedGraphSelectorCoefficient (Fintype.card Q) * samplingLogRatio n ε +
    ((n : ℝ) * (Real.log σ / Real.log 2) + _) ≤ _
  calc
    _ ≤ acceptedGraphSelectorCoefficient (Fintype.card Q) * samplingLogRatio n ε +
        (n * (Real.log σ / Real.log 2) +
          (2 * ((n : ℝ) / L) + 2 * Fintype.card Q) *
            (growthAcceptedOverhead (Fintype.card Q) G * samplingLogRatio n ε)) := by
      exact add_le_add le_rfl (add_le_add le_rfl hpay)
    _ = _ := by ring

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SeedDominatingCutoff
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

theorem logInv_le_of_dyadic_lower_bound (δ : ℝ) (hδ : 0 < δ) (L : ℕ)
    (h : (1 : ℝ) / 2 ^ L ≤ δ) : logInv δ ≤ L := by
  have hpow : (0 : ℝ) < 2 ^ L := by positivity
  have hr : (1 : ℝ) / δ ≤ 2 ^ L := by
    apply (div_le_iff₀ hδ).mpr
    simpa only [mul_comm] using (div_le_iff₀ hpow).mp h
  have hl := Real.log_le_log (by positivity : (0 : ℝ) < 1 / δ) hr
  rw [Real.log_pow] at hl
  exact (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr hl

/-- A dummy geometric rate 1/2 makes the common cutoff dominate the
logarithmic local rounding cost as well as every actual mixing error. -/
theorem common_geometric_block_seed_cost {I : Type} [Fintype I]
    (a : I → ℕ) (ha : ∀ i, 0 < a i)
    (C ρ : I → ℝ) (hC : ∀ i, 0 < C i) (hρ : ∀ i, 0 < ρ i) (hρlt : ∀ i, ρ i < 1) :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
        ∃ L : ℕ, 0 < L ∧ (L : ℝ) ≤ A * Real.log ((n + 1 : ℕ) / ε) + D ∧
          logInv (ε / (8 * (n + 1 : ℕ))) ≤ L ∧
          ∀ i, a i ∣ L ∧ 0 < L / a i ∧
            C i * ρ i ^ (L / a i) ≤ ε / (8 * (n + 1 : ℕ)) := by
  let a' : Option I → ℕ := Option.elim' 1 a
  let C' : Option I → ℝ := Option.elim' 1 C
  let ρ' : Option I → ℝ := Option.elim' (1 / 2) ρ
  have ha' : ∀ i, 0 < a' i := by intro i; cases i <;> simp [a', ha]
  have hC' : ∀ i, 0 < C' i := by intro i; cases i <;> simp [C', hC]
  have hρ' : ∀ i, 0 < ρ' i := by intro i; cases i <;> simp [ρ', hρ]
  have hρlt' : ∀ i, ρ' i < 1 := by intro i; cases i <;> simp [ρ', hρlt] <;> norm_num
  obtain ⟨A, D, hA, hD, hcut⟩ := common_geometric_block_nonempty a' (fun _ => 0) ha' C' ρ' hC' hρ' hρlt'
  refine ⟨A, D, hA, hD, ?_⟩
  intro n ε hε hεle
  obtain ⟨L, hL, hlen, hall⟩ := hcut n ε hε hεle
  refine ⟨L, hL, hlen, ?_, fun i => ⟨(hall (some i)).1, (hall (some i)).2.1,
    (hall (some i)).2.2.2⟩⟩
  apply logInv_le_of_dyadic_lower_bound _ (by positivity)
  simpa [a', C', ρ', one_div_pow] using (hall none).2.2.2



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ScaledSeedCutoff
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- The common periodic cutoff may be enlarged by any fixed factor.
Its upper bound stays logarithmic, every divisibility/mixing certificate
is retained, and it dominates the requested multiple of the precision cost. -/
theorem common_geometric_block_scaled_seed_cost {I : Type} [Fintype I]
    (a : I → ℕ) (ha : ∀ i, 0 < a i)
    (C ρ : I → ℝ) (hC : ∀ i, 0 < C i) (hρ : ∀ i, 0 < ρ i) (hρlt : ∀ i, ρ i < 1)
    (H : ℝ) (hH : 0 < H) :
    ∃ A D : ℝ, 0 < A ∧ 0 < D ∧
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
        ∃ L : ℕ, 0 < L ∧ (L : ℝ) ≤ A * Real.log ((n + 1 : ℕ) / ε) + D ∧
          logInv (ε / (8 * (n + 1 : ℕ))) ≤ L ∧
          H * logInv (ε / (8 * (n + 1 : ℕ))) ≤ L ∧
          ∀ i, a i ∣ L ∧ 0 < L / a i ∧
            C i * ρ i ^ (L / a i) ≤ ε / (8 * (n + 1 : ℕ)) := by
  obtain ⟨A, D, hA, hD, hcut⟩ := common_geometric_block_seed_cost a ha C ρ hC hρ hρlt
  let k := ⌈H⌉₊
  have hk : 0 < k := Nat.ceil_pos.mpr hH
  have hkreal : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hHk : H ≤ k := Nat.le_ceil H
  refine ⟨k * A, k * D, mul_pos hkreal hA, mul_pos hkreal hD, ?_⟩
  intro n ε hε hεle
  obtain ⟨B, hB, hlen, hcost, hall⟩ := hcut n ε hε hεle
  have hBL : B ≤ k * B := by
    simpa using Nat.mul_le_mul_right B (show 1 ≤ k from hk)
  have hlocal := localRoundingTolerance_bounds n hε hεle
  have hlog : 0 ≤ logInv (ε / (8 * (n + 1 : ℕ))) :=
    logInv_nonneg_of_le_one _ hlocal.1 (hlocal.2.1.trans hlocal.2.2)
  refine ⟨k * B, Nat.mul_pos hk hB, ?_, hcost.trans (Nat.cast_le.mpr hBL), ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left hlen hkreal.le
    simpa only [Nat.cast_mul, mul_add, mul_assoc] using hh
  · calc
      H * logInv (ε / (8 * (n + 1 : ℕ))) ≤
        k * logInv (ε / (8 * (n + 1 : ℕ))) := mul_le_mul_of_nonneg_right hHk hlog
      _ ≤ k * B := mul_le_mul_of_nonneg_left hcost hkreal.le
      _ = _ := (Nat.cast_mul k B).symm
  · intro i
    have hquot : B / a i ≤ k * B / a i := Nat.div_le_div_right hBL
    refine ⟨dvd_mul_of_dvd_right (hall i).1 k, (hall i).2.1.trans_le hquot, ?_⟩
    apply le_trans _ (hall i).2.2
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (hρ i).le (hρlt i).le hquot) (hC i).le

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_PerronSpectralBound
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix ENNReal NNReal







/-- Recover the actual eigenvector identity from the normalized Doob
rows already stored in each periodic SCC model. -/
theorem sccPeriodicModel_eigenvector {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (s : Q) (model : SCCPeriodicModel W s) :
    sccMatrix W s *ᵥ model.right = model.lam • model.right := by
  funext x
  have hx := model.stochastic x
  simp only [doobMatrix, ← Finset.sum_div] at hx
  have hd : model.lam * model.right x ≠ 0 := (mul_pos model.lam_pos (model.right_pos x)).ne'
  exact (div_eq_one_iff_eq hd).mp hx



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ComponentSeedBounds
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

theorem sccPeriodicModel_support_card_pos {Q : Type} [Fintype Q] [DecidableEq Q]
    {W : Matrix Q Q ℝ} {s : Q} (model : SCCPeriodicModel W s) (x : SCCState W s) :
    0 < Fintype.card (PositiveSupportClass
      (doobMatrix (sccMatrix W s) model.lam model.right ^ model.blockExponent) x) := by
  obtain ⟨ν, _, hsum, _⟩ := model.approximation x
  by_contra h
  have hz : Fintype.card (PositiveSupportClass
      (doobMatrix (sccMatrix W s) model.lam model.right ^ model.blockExponent) x) = 0 := by omega
  haveI := Fintype.card_eq_zero_iff.mp hz
  simp at hsum





end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_CategorySelectorSeedBound
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

def polynomialSeedCoefficient (K d : ℕ) : ℝ := stateLog K + d / Real.log 2 + 3

theorem polynomialSeedCoefficient_pos {K : ℕ} (hK : 0 < K) (d : ℕ) :
    0 < polynomialSeedCoefficient K d := by
  have h := stateLog_nonneg hK
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  unfold polynomialSeedCoefficient
  positivity

/-- Rounding a polynomial-size outcome space costs at most a constant
times n+logInv(epsilon), including n=0 and epsilon<=1/2. -/
theorem roundingSeed_polynomial_card_bound (K d m n : ℕ) (hK : 0 < K) (hm : 0 < m)
    (hcard : m ≤ K * (n + 1) ^ d) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1 / 2) :
    (roundingSeed m (ε / 2) : ℝ) ≤ polynomialSeedCoefficient K d * (n + logInv ε) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hK' : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hb := stateLog_nonneg hK
  have hd : (0 : ℝ) ≤ d / Real.log 2 := div_nonneg (Nat.cast_nonneg _) hlog2.le
  have ht := logInv_ge_one hε hεle
  have h := roundingSeed_upper_of_card_le m (K * (n + 1) ^ d) hm hcard
    (ε / 2) (by positivity) (by linarith)
  have hlog : Real.log (K * (n + 1) ^ d : ℕ) / Real.log 2 =
      stateLog K + (d / Real.log 2) * Real.log (n + 1 : ℕ) := by
    rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul hK'.ne' (by positivity), Real.log_pow]
    unfold stateLog
    ring
  rw [hlog, logInv_half hε] at h
  have hn := mul_le_mul_of_nonneg_left (log_succ_le n) hd
  apply h.trans
  unfold polynomialSeedCoefficient
  nlinarith [mul_nonneg (by positivity : 0 ≤ stateLog K + 2) (sub_nonneg.mpr ht),
    mul_nonneg (by positivity : 0 ≤ stateLog K + 3) (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
    mul_nonneg hd (le_trans (by norm_num : (0 : ℝ) ≤ 1) ht)]

def categoryChoiceCoefficient (q : ℕ) : ℝ :=
  polynomialSeedCoefficient (q * q * (q * q + 1) ^ q) q

theorem categoryChoiceCoefficient_pos {q : ℕ} (hq : 0 < q) : 0 < categoryChoiceCoefficient q :=
  polynomialSeedCoefficient_pos (by positivity) q



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_LogarithmicBlockCardinality
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

/-- A logarithmic block cutoff gives a uniform polynomial support bound.
Both coefficient and integer exponent are fixed before length, accuracy
and the actual cutoff are chosen. -/
theorem exponential_logarithmic_cutoff_bound (q : ℕ) (hq : 0 < q) (A D : ℝ) :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (X : ℝ), 1 ≤ X → ∀ L : ℕ, (L : ℝ) ≤ A * Real.log X + D →
        (q ^ (2 * L + 1) : ℝ) ≤ C * X ^ k := by
  let C := Real.exp ((2 * D + 1) * Real.log q)
  let k : ℕ := ⌈2 * A * Real.log q⌉₊
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (Nat.one_le_cast.mpr hq)
  refine ⟨C, k, Real.exp_pos _, ?_⟩
  intro X hX L hL
  have hX' : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hlX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hk : 2 * A * Real.log q ≤ (k : ℝ) := Nat.le_ceil _
  have h1 := mul_le_mul_of_nonneg_right hL (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hlq)
  have h2 := mul_le_mul_of_nonneg_right hk hlX
  calc
    _ = Real.exp ((2 * L + 1 : ℕ) * Real.log q) := by
      rw [Real.exp_nat_mul, Real.exp_log hq']
    _ ≤ Real.exp ((2 * D + 1) * Real.log q + (k : ℝ) * Real.log X) := by
      apply Real.exp_le_exp.mpr
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      nlinarith
    _ = C * X ^ k := by rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hX']

theorem accuracy_ratio_ge_one (n : ℕ) {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1) :
    1 ≤ (n + 1 : ℕ) / ε := by
  apply (le_div_iff₀ hε).mpr
  have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  simpa only [one_mul] using hεle.trans hn





end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SamplingResourceScale
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

def acceptingCategoryCountBound (q n : ℕ) : ℕ := (q * q * (q * q + 1) ^ q) * (n + 1) ^ q

def localSamplingTolerance (q n : ℕ) (ε : ℝ) : ℝ :=
  categorySegmentTolerance q ε / (8 * (n + 1 : ℕ))

/-- A common integer scale for every primitive in the explicit circuit
costs. It includes category choices, local paths and both kinds of seed. -/
def samplingResourceScale (q n L : ℕ) (ε : ℝ) : ℕ :=
  (n + 1) + 2 * q + roundingSeed (q ^ (2 * L + 1)) (localSamplingTolerance q n ε) +
    q ^ (2 * L + 1) + acceptingCategoryCountBound q n +
    roundingSeed (acceptingCategoryCountBound q n) (ε / 2) + 1

theorem samplingResourceScale_spec (q n L : ℕ) (ε : ℝ) :
    let t := samplingResourceScale q n L ε
    0 < t ∧ n + 1 ≤ t ∧ 2 * q ≤ t ∧
      roundingSeed (q ^ (2 * L + 1)) (localSamplingTolerance q n ε) ≤ t ∧
      q ^ (2 * L + 1) ≤ t ∧ acceptingCategoryCountBound q n ≤ t ∧
      roundingSeed (acceptingCategoryCountBound q n) (ε / 2) ≤ t := by
  dsimp only [samplingResourceScale]
  omega

theorem roundingSeed_mono_card_precision {p q : ℕ} (hp : 0 < p) (hpq : p ≤ q)
    {δ η : ℝ} (hδ : 0 < δ) (hδη : δ ≤ η) : roundingSeed p η ≤ roundingSeed q δ := by
  apply Nat.ceil_mono
  exact add_le_add (stateLog_mono hp hpq) (logInv_antitone hδ hδη)

theorem localSamplingTolerance_bounds (q n : ℕ) (hq : 0 < q) {ε : ℝ}
    (hε : 0 < ε) (hεle : ε ≤ 1) :
    0 < localSamplingTolerance q n ε ∧
      localSamplingTolerance q n ε ≤ categorySegmentTolerance q ε / 2 ∧
      categorySegmentTolerance q ε / 2 ≤ 1 := by
  obtain ⟨hη, hηle, _⟩ := categorySegmentTolerance_bounds q hq ε hε hεle
  exact localRoundingTolerance_bounds n hη hηle

theorem samplingResourceScale_block (q n L p b : ℕ) (hp : 0 < p) (hpq : p ≤ q)
    (hb : b ≤ 2 * L) (ε η : ℝ) (hδ : 0 < localSamplingTolerance q n ε)
    (hδη : localSamplingTolerance q n ε ≤ η) :
    p ^ (b + 1) ≤ samplingResourceScale q n L ε ∧
      bridgeRoundingSeed p b η ≤ samplingResourceScale q n L ε := by
  have hq : 1 ≤ q := hp.trans_le hpq
  have hcard : p ^ (b + 1) ≤ q ^ (2 * L + 1) :=
    (Nat.pow_le_pow_left hpq _).trans (pow_le_pow_right₀ hq (by omega))
  have hs := samplingResourceScale_spec q n L ε
  exact ⟨hcard.trans hs.2.2.2.2.1,
    (roundingSeed_mono_card_precision (pow_pos hp _) hcard hδ hδη).trans hs.2.2.2.1⟩

theorem samplingResourceScale_boundary (q n L M : ℕ) (hM : 0 < M) (hMq : M ≤ q)
    (ε : ℝ) (hδ : 0 < localSamplingTolerance q n ε) :
    roundingSeed M (localSamplingTolerance q n ε) ≤ samplingResourceScale q n L ε := by
  have hq : 1 ≤ q := hM.trans_le hMq
  have hcard : M ≤ q ^ (2 * L + 1) := hMq.trans (by
    simpa only [pow_one] using pow_le_pow_right₀ hq (by omega : 1 ≤ 2 * L + 1))
  exact (roundingSeed_mono_card_precision hM hcard hδ le_rfl).trans
    (samplingResourceScale_spec q n L ε).2.2.2.1



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ResourceScalePolynomial
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

theorem accuracy_ratio_controls_length (n : ℕ) {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1) :
    (n + 1 : ℕ) ≤ (n + 1 : ℕ) / ε ∧ (1 : ℝ) / ε ≤ (n + 1 : ℕ) / ε := by
  have hn : (1 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  constructor
  · apply (le_div_iff₀ hε).mpr
    exact mul_le_of_le_one_right (by positivity) hεle
  · exact div_le_div_of_nonneg_right hn hε.le

theorem length_logInv_accuracy_bound (n : ℕ) {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1) :
    (n : ℝ) + logInv ε ≤ (1 + 1 / Real.log 2) * ((n + 1 : ℕ) / ε) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨hn, hr⟩ := accuracy_ratio_controls_length n hε hεle
  have hlog := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 / ε)
  have hi : logInv ε ≤ ((n + 1 : ℕ) / ε) / Real.log 2 := by
    apply div_le_div_of_nonneg_right _ hlog2.le
    linarith
  simp only [Nat.cast_add, Nat.cast_one] at hn
  have he : (1 + 1 / Real.log 2) * ((n + 1 : ℕ) / ε) =
      (n + 1 : ℕ) / ε + ((n + 1 : ℕ) / ε) / Real.log 2 := by ring
  rw [he]
  simp only [Nat.cast_add, Nat.cast_one] at *
  linarith

theorem cutoff_length_accuracy_bound (n L : ℕ) (A D ε : ℝ) (hA : 0 < A) (hD : 0 < D)
    (hε : 0 < ε) (hεle : ε ≤ 1)
    (hL : (L : ℝ) ≤ A * Real.log ((n + 1 : ℕ) / ε) + D) :
    (L + 1 : ℕ) ≤ (A + D + 1) * ((n + 1 : ℕ) / ε) := by
  have hX := accuracy_ratio_ge_one n hε hεle
  have hlog := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < (n + 1 : ℕ) / ε)
  have hm := mul_le_mul_of_nonneg_left hlog hA.le
  simp only [Nat.cast_add, Nat.cast_one] at *
  nlinarith [mul_nonneg hD.le (sub_nonneg.mpr hX)]

theorem maximal_local_seed_cutoff_bound (q n L : ℕ) (hq : 0 < q) (ε : ℝ)
    (hδ : 0 < localSamplingTolerance q n ε) (hδle : localSamplingTolerance q n ε ≤ 1)
    (hcost : logInv (localSamplingTolerance q n ε) ≤ L) :
    (roundingSeed (q ^ (2 * L + 1)) (localSamplingTolerance q n ε) : ℝ) ≤
      (2 * stateLog q + 2) * (L + 1 : ℕ) := by
  have h := bridgeRoundingSeed_linear_bound q (2 * L) hq (localSamplingTolerance q n ε) hδ hδle
  have hb := stateLog_nonneg hq
  change (roundingSeed (q ^ (2 * L + 1)) (localSamplingTolerance q n ε) : ℝ) ≤
    ((2 * L + 1 : ℕ) : ℝ) * stateLog q + logInv (localSamplingTolerance q n ε) + 1 at h
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h ⊢
  nlinarith

/-- One polynomial scale bounds all primitives uniformly over accepting
sets and SCC choices. Its constants are fixed by q,A,D before n,L,epsilon. -/
theorem samplingResourceScale_polynomial (q : ℕ) (hq : 0 < q) (A D : ℝ)
    (hA : 0 < A) (hD : 0 < D) :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (n L : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
        (L : ℝ) ≤ A * Real.log ((n + 1 : ℕ) / ε) + D →
        logInv (localSamplingTolerance q n ε) ≤ L →
        (samplingResourceScale q n L ε : ℝ) ≤ C * (((n + 1 : ℕ) : ℝ) / ε) ^ k := by
  obtain ⟨Cp, kp, hCp, hpow⟩ := exponential_logarithmic_cutoff_bound q hq A D
  let K := q * q * (q * q + 1) ^ q
  let B := 2 * stateLog q + 2
  let V := 1 + 1 / Real.log 2
  let C := 2 + 2 * (q : ℝ) + B * (A + D + 1) + Cp + K + categoryChoiceCoefficient q * V
  have hK : 0 < K := by dsimp only [K]; positivity
  have hb := stateLog_nonneg hq
  have hB : 0 < B := by dsimp only [B]; positivity
  have hV : 0 < V := by dsimp only [V]; have h := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity
  have hchoice := categoryChoiceCoefficient_pos hq
  refine ⟨C, max kp q, by dsimp only [C]; positivity, ?_⟩
  intro n L ε hε hεle hlen hcost
  let X : ℝ := (n + 1 : ℕ) / ε
  let Z := X ^ max kp q
  have hε1 : ε ≤ 1 := by linarith
  have hX : 1 ≤ X := accuracy_ratio_ge_one n hε hε1
  have hXZ : X ≤ Z := by
    simpa only [pow_one] using pow_le_pow_right₀ hX
      (show 1 ≤ max kp q from (show 1 ≤ q from hq).trans (Nat.le_max_right _ _))
  have hZ : 1 ≤ Z := hX.trans hXZ
  have hkp : X ^ kp ≤ Z := pow_le_pow_right₀ hX (Nat.le_max_left _ _)
  have hkq : X ^ q ≤ Z := pow_le_pow_right₀ hX (Nat.le_max_right _ _)
  have hn : ((n + 1 : ℕ) : ℝ) ≤ Z := (accuracy_ratio_controls_length n hε hε1).1.trans hXZ
  have hqZ : 2 * (q : ℝ) ≤ 2 * q * Z := by nlinarith [mul_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q) (sub_nonneg.mpr hZ)]
  obtain ⟨hδ, hδhalf, hhalf⟩ := localSamplingTolerance_bounds q n hq hε hε1
  have hlocal := maximal_local_seed_cutoff_bound q n L hq ε hδ (hδhalf.trans hhalf) hcost
  have hlen' := cutoff_length_accuracy_bound n L A D ε hA hD hε hε1 hlen
  have hlocalZ : (roundingSeed (q ^ (2 * L + 1)) (localSamplingTolerance q n ε) : ℝ) ≤ B * (A + D + 1) * Z := by
    apply hlocal.trans
    dsimp only [B]
    calc
      _ ≤ (2 * stateLog q + 2) * ((A + D + 1) * X) := mul_le_mul_of_nonneg_left hlen' hB.le
      _ = B * (A + D + 1) * X := by dsimp only [B]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hXZ (by positivity)
  have hsupport : (q ^ (2 * L + 1) : ℝ) ≤ Cp * Z :=
    (hpow X hX L hlen).trans (mul_le_mul_of_nonneg_left hkp hCp.le)
  have hcategory : (acceptingCategoryCountBound q n : ℝ) ≤ (K : ℝ) * Z := by
    unfold acceptingCategoryCountBound
    rw [Nat.cast_mul, Nat.cast_pow]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact (pow_le_pow_left₀ (by positivity) (accuracy_ratio_controls_length n hε hε1).1 _).trans hkq
  have hselector := roundingSeed_polynomial_card_bound K q (acceptingCategoryCountBound q n) n hK
    (by unfold acceptingCategoryCountBound; positivity) le_rfl ε hε hεle
  have hselectorZ : (roundingSeed (acceptingCategoryCountBound q n) (ε / 2) : ℝ) ≤ categoryChoiceCoefficient q * V * Z := by
    apply hselector.trans
    have hbase := (length_logInv_accuracy_bound n hε hε1).trans (mul_le_mul_of_nonneg_left hXZ hV.le)
    exact (mul_le_mul_of_nonneg_left hbase hchoice.le).trans_eq (by dsimp only [categoryChoiceCoefficient, K, V]; ring)
  unfold samplingResourceScale
  dsimp only [C, Z, X] at hn hqZ hlocalZ hsupport hcategory hselectorZ hZ ⊢
  push_cast at hn hqZ hlocalZ hsupport hcategory hselectorZ hZ ⊢
  nlinarith only [hn, hqZ, hlocalZ, hsupport, hcategory, hselectorZ, hZ]

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_GrowthResourceScale
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def growthResourceScale (q n L : ℕ) (G σ ε : ℝ) : ℕ :=
  samplingResourceScale q n L ε + growthRoundingSeed G σ (2 * L) (localSamplingTolerance q n ε)

theorem growthResourceScale_spec (q n L : ℕ) (G σ ε : ℝ) :
    0 < growthResourceScale q n L G σ ε ∧
      samplingResourceScale q n L ε ≤ growthResourceScale q n L G σ ε ∧
      growthRoundingSeed G σ (2 * L) (localSamplingTolerance q n ε) ≤ growthResourceScale q n L G σ ε := by
  have h := (samplingResourceScale_spec q n L ε).1
  unfold growthResourceScale
  omega

theorem growthRoundingSeed_mono_length_precision (G σ : ℝ) (hσ : 1 ≤ σ)
    {b B : ℕ} (hb : b ≤ B) {δ η : ℝ} (hδ : 0 < δ) (hδη : δ ≤ η) :
    growthRoundingSeed G σ b η ≤ growthRoundingSeed G σ B δ := by
  apply Nat.ceil_mono
  have hlog := div_nonneg (Real.log_nonneg hσ) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hb) hlog))
    (logInv_antitone hδ hδη)

theorem growthResourceScale_block (q n L p b : ℕ) (hp : 0 < p) (hpq : p ≤ q)
    (hb : b ≤ 2 * L) (G σ ε η : ℝ) (hσ : 1 ≤ σ)
    (hδ : 0 < localSamplingTolerance q n ε) (hδη : localSamplingTolerance q n ε ≤ η) :
    p ^ (b + 1) ≤ growthResourceScale q n L G σ ε ∧
      growthRoundingSeed G σ b η ≤ growthResourceScale q n L G σ ε := by
  have hs := growthResourceScale_spec q n L G σ ε
  exact ⟨(samplingResourceScale_block q n L p b hp hpq hb ε η hδ hδη).1.trans hs.2.1,
    (growthRoundingSeed_mono_length_precision G σ hσ hb hδ hδη).trans hs.2.2⟩

theorem growthResourceScale_category {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s : Q) (F : Finset Q) (n L : ℕ)
    (hZ : 0 < ∑ γ : Fin (n + 1) → Q, acceptedGraphWeight W s F γ)
    (G σ ε : ℝ) (hε : 0 < ε) :
    Fintype.card (AcceptedGraphCategory W s F n) ≤ growthResourceScale (Fintype.card Q) n L G σ ε ∧
      acceptedGraphChoiceSeed W s F n ε ≤ growthResourceScale (Fintype.card Q) n L G σ ε := by
  have hcard := acceptedGraphCategory_card_polynomial W s F n
  have hpos : 0 < Fintype.card (AcceptedGraphCategory W s F n) :=
    Fintype.card_pos_iff.mpr (acceptedGraphCategory_nonempty W hW s F n hZ)
  have hs := samplingResourceScale_spec (Fintype.card Q) n L ε
  have hg := (growthResourceScale_spec (Fintype.card Q) n L G σ ε).2.1
  exact ⟨hcard.trans (hs.2.2.2.2.2.1.trans hg),
    (roundingSeed_mono_card_precision hpos hcard (by positivity : 0 < ε / 2) le_rfl).trans
      (hs.2.2.2.2.2.2.trans hg)⟩

/-- Growth seeds add only a linear-in-cutoff term to the previous common
size scale; the coefficient is independent of length and accuracy. -/
theorem maximal_growth_seed_cutoff_bound (q n L : ℕ) (G σ ε : ℝ) (hG : 1 ≤ G) (hσ : 1 ≤ σ)
    (hδ : 0 < localSamplingTolerance q n ε) (hδle : localSamplingTolerance q n ε ≤ 1)
    (hcost : logInv (localSamplingTolerance q n ε) ≤ L) :
    (growthRoundingSeed G σ (2 * L) (localSamplingTolerance q n ε) : ℝ) ≤
      (2 * (Real.log σ / Real.log 2) + Real.log G / Real.log 2 + 2) * (L + 1 : ℕ) := by
  have h := growthRoundingSeed_upper G σ hG hσ (2 * L) _ hδ hδle
  have hg := div_nonneg (Real.log_nonneg hG) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hs := div_nonneg (Real.log_nonneg hσ) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h ⊢
  nlinarith

theorem growthResourceScale_polynomial (q : ℕ) (hq : 0 < q) (G σ A D : ℝ)
    (hG : 1 ≤ G) (hσ : 1 ≤ σ) (hA : 0 < A) (hD : 0 < D) :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (n L : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
        (L : ℝ) ≤ A * Real.log ((n + 1 : ℕ) / ε) + D →
        logInv (localSamplingTolerance q n ε) ≤ L →
        (growthResourceScale q n L G σ ε : ℝ) ≤ C * (((n + 1 : ℕ) : ℝ) / ε) ^ k := by
  obtain ⟨B, k, hB, hbase⟩ := samplingResourceScale_polynomial q hq A D hA hD
  let K := 2 * (Real.log σ / Real.log 2) + Real.log G / Real.log 2 + 2
  have hg := div_nonneg (Real.log_nonneg hG) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hs := div_nonneg (Real.log_nonneg hσ) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨B + K * (A + D + 1), max k 1, by positivity, ?_⟩
  intro n L ε hε hεle hlen hcost
  let X : ℝ := (n + 1 : ℕ) / ε
  have hε1 : ε ≤ 1 := by linarith
  have hX : 1 ≤ X := accuracy_ratio_ge_one n hε hε1
  have hk : X ^ k ≤ X ^ max k 1 := pow_le_pow_right₀ hX (Nat.le_max_left _ _)
  have hx : X ≤ X ^ max k 1 := by
    simpa only [pow_one] using pow_le_pow_right₀ hX (Nat.le_max_right k 1)
  obtain ⟨hδ, hδhalf, hhalf⟩ := localSamplingTolerance_bounds q n hq hε hε1
  have hseed := maximal_growth_seed_cutoff_bound q n L G σ ε hG hσ hδ (hδhalf.trans hhalf) hcost
  have hlength := cutoff_length_accuracy_bound n L A D ε hA hD hε hε1 hlen
  have hseedX : (growthRoundingSeed G σ (2 * L) (localSamplingTolerance q n ε) : ℝ) ≤
      K * (A + D + 1) * X ^ max k 1 := by
    apply hseed.trans
    calc
      K * (L + 1 : ℕ) ≤ K * ((A + D + 1) * X) := mul_le_mul_of_nonneg_left hlength hK.le
      _ = K * (A + D + 1) * X := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hx (by positivity)
  have hbaseX := (hbase n L ε hε hεle hlen hcost).trans (mul_le_mul_of_nonneg_left hk hB.le)
  unfold growthResourceScale
  rw [Nat.cast_add]
  exact (add_le_add hbaseX hseedX).trans_eq (by ring)

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_BridgeSizeEnvelopes
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- Polynomial envelopes for the actual gate-and-wire cost formulas.
The common parameter bounds lengths, state counts, local seeds and local
support sizes; no boundary tuple enumeration is introduced. -/
def roundedSizeEnvelope (t : ℕ) : ℕ :=
  t + (t * t) * (t * (2 * (t * (3 * t + 2) + 1) + 6) + 2)

def repeatedBoundarySizeEnvelope (t : ℕ) : ℕ :=
  t * t + (t * t) * roundedSizeEnvelope t + t * t

def selectedBlockSizeEnvelope (t : ℕ) : ℕ :=
  (t * t + t) + (t * t) * (repeatedBoundarySizeEnvelope t + t * t + 6 * (t * t)) +
    (t * t) * ((t * t) * roundedSizeEnvelope t) +
    2 * (t * t + (t * t) * (t * t)) + (t * t) * (4 * (t * t) + 2)

def parallelBlockSizeEnvelope (t : ℕ) : ℕ :=
  (t * t + t * t) + t * ((t * t) * selectedBlockSizeEnvelope t) + t * (t * t)

def periodicSizeEnvelope (t : ℕ) : ℕ := parallelBlockSizeEnvelope t + t * t



theorem boundaryRoundingCircuitSize_envelope (q M t : ℕ) (δ : ℝ) (ht : 0 < t)
    (hq : q ≤ t) (hM : M ≤ t) (hm : roundingSeed M δ ≤ t) :
    boundaryRoundingCircuitSize q M δ ≤ roundedSizeEnvelope t := by
  have hqq : q ≤ t * t := hq.trans (by nlinarith)
  unfold boundaryRoundingCircuitSize roundedSizeEnvelope
  dsimp only
  gcongr









end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SeededSizeEnvelopes
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

theorem seededBridgeSize_envelope (q n t m : ℕ)
    (hq : q ≤ t) (hn : n + 1 ≤ t) (hm : m ≤ t) (hs : q ^ (n + 1) ≤ t) :
    seededBridgeSize q n m ≤ roundedSizeEnvelope t := by
  unfold seededBridgeSize roundedSizeEnvelope
  gcongr

theorem seededBoundarySelectedSize_envelope (r boundarySize k q n t : ℕ) (m : ℕ → ℕ)
    (hr : r ≤ t * t) (hB : boundarySize ≤ repeatedBoundarySizeEnvelope t)
    (hk : k ≤ t) (hq : q ≤ t) (hn : n + 1 ≤ t)
    (hm : m n ≤ t) (hs : q ^ (n + 1) ≤ t) :
    seededBoundarySelectedSize r boundarySize k q n m ≤ selectedBlockSizeEnvelope t := by
  have hleaf := seededBridgeSize_envelope q n t (m n) hq hn hm hs
  unfold seededBoundarySelectedSize seededEndpointSelectedSize selectedBlockSizeEnvelope
  gcongr

theorem seededBlockSeedBudget_envelope {k : ℕ} (t : ℕ) (l : Fin (k + 1) → ℕ) (m : ℕ → ℕ)
    (hk : k + 1 ≤ t) (hm : ∀ i, m (l i) ≤ t) :
    seededBlockSeedBudget m l ≤ t * t := by
  unfold seededBlockSeedBudget
  calc
    _ ≤ ∑ _i : Fin (k + 1), t := Finset.sum_le_sum (fun i _ => hm i)
    _ = (k + 1) * t := by simp
    _ ≤ t * t := Nat.mul_le_mul_right t hk

theorem parallelSeededBlockSize_envelope {k : ℕ} (r boundarySize q t : ℕ)
    (l : Fin (k + 1) → ℕ) (m : ℕ → ℕ)
    (hr : r ≤ t * t) (hB : boundarySize ≤ repeatedBoundarySizeEnvelope t)
    (hk : k + 1 ≤ t) (hq : q ≤ t) (hn : ∀ i, l i + 1 ≤ t)
    (hm : ∀ i, m (l i) ≤ t) (hs : ∀ i, q ^ (l i + 1) ≤ t) :
    parallelSeededBlockSize r boundarySize q l m ≤ parallelBlockSizeEnvelope t := by
  have hseeds := seededBlockSeedBudget_envelope t l m hk hm
  have hblocks : ∀ i, seededBoundarySelectedSize r boundarySize k q (l i) m ≤ selectedBlockSizeEnvelope t :=
    fun i => seededBoundarySelectedSize_envelope r boundarySize k q (l i) t m hr hB (by omega) hq
      (hn i) (hm i) (hs i)
  have hsum : (∑ i, ((l i + 1) * q) * seededBoundarySelectedSize r boundarySize k q (l i) m) ≤
      t * ((t * t) * selectedBlockSizeEnvelope t) := by
    calc
      _ ≤ ∑ _i : Fin (k + 1), (t * t) * selectedBlockSizeEnvelope t := by
        apply Finset.sum_le_sum
        intro i _
        gcongr
        · exact hn i
        · exact hblocks i
      _ = (k + 1) * ((t * t) * selectedBlockSizeEnvelope t) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hk
  have hout : (∑ i, (l i + 1) * q) ≤ t * (t * t) := by
    calc
      _ ≤ ∑ _i : Fin (k + 1), t * t := Finset.sum_le_sum (fun i _ => Nat.mul_le_mul (hn i) hq)
      _ = (k + 1) * (t * t) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hk
  unfold parallelSeededBlockSize parallelBlockSizeEnvelope
  omega

/-- The polynomial gate-and-wire envelopes also cover arbitrary supplied
local seed budgets; growth-based rounding therefore uses the same
polynomial envelope once its primitive sizes are bounded. -/
theorem seededPeriodicCircuitSize_envelope (q M n L t : ℕ) (δ : ℝ) (m : ℕ → ℕ) (ht : 0 < t)
    (hq : q ≤ t) (hM : M ≤ t) (hn : n + 1 ≤ t)
    (hm : roundingSeed M δ ≤ t)
    (hblen : ∀ i, cutoffBlockLengths n L i + 1 ≤ t)
    (hbseed : ∀ i, m (cutoffBlockLengths n L i) ≤ t)
    (hbsupp : ∀ i, q ^ (cutoffBlockLengths n L i + 1) ≤ t) :
    seededPeriodicCircuitSize q M (boundaryRoundingCircuitSize q M δ) n L δ m ≤ periodicSizeEnvelope t := by
  let k := cutoffBoundaryCount n L
  let b := roundingSeed M δ
  have hk : k + 1 ≤ t := by have h := (cutoff_block_count_bound n L).2; dsimp only [k]; omega
  have hk' : k ≤ t := by omega
  have hr : k * b ≤ t * t := Nat.mul_le_mul hk' hm
  have hleaf := boundaryRoundingCircuitSize_envelope q M t δ ht hq hM hm
  have hB : k * b + (k * q) * boundaryRoundingCircuitSize q M δ + k * q ≤
      repeatedBoundarySizeEnvelope t := by
    unfold repeatedBoundarySizeEnvelope
    gcongr
  have h := parallelSeededBlockSize_envelope (k * b) _ q t (cutoffBlockLengths n L) m
    hr hB hk hq hblen hbseed hbsupp
  unfold seededPeriodicCircuitSize periodicSizeEnvelope
  dsimp only
  exact Nat.add_le_add h (Nat.mul_le_mul hn hq)

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ComponentSizeEnvelope
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

def componentSizeEnvelope (t : ℕ) : ℕ :=
  roundedSizeEnvelope t + periodicSizeEnvelope t + 5 * (t * t)



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_GrowthComponentEnvelope
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

/-- The actual growth-based segment costs fit the same fixed polynomial
envelope, including short SCC bridges and their embedding wires. -/
theorem growthComponent_resource_envelope {Q : Type} [Fintype Q] [DecidableEq Q]
    {W : Matrix Q Q ℝ} (models : ∀ c : CyclicSCCIndex W, SCCPeriodicModel W c.val)
    (G σ : ℝ) (hσ : 1 ≤ σ) (s : Q) (N n L : ℕ) (hn : n ≤ N) (hL : 0 < L)
    (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1) :
    let t := growthResourceScale (Fintype.card Q) N L G σ ε
    growthComponentSeedBudget models G σ s N n L (categorySegmentTolerance (Fintype.card Q) ε) ≤ 2 * (t * t) ∧
      growthComponentCircuitSize models G σ s N n L (categorySegmentTolerance (Fintype.card Q) ε) ≤ componentSizeEnvelope t := by
  classical
  dsimp only
  let q := Fintype.card Q
  let t := growthResourceScale q N L G σ ε
  change growthComponentSeedBudget models G σ s N n L (categorySegmentTolerance q ε) ≤ 2 * (t * t) ∧
    growthComponentCircuitSize models G σ s N n L (categorySegmentTolerance q ε) ≤ componentSizeEnvelope t
  have hq : 0 < q := Fintype.card_pos_iff.mpr ⟨s⟩
  have hscale := samplingResourceScale_spec q N L ε
  have hg := growthResourceScale_spec q N L G σ ε
  have ht : 0 < t := hg.1
  have hnt : n + 1 ≤ t := by omega
  have hqt : q ≤ t := by omega
  obtain ⟨hδ, hδhalf, _⟩ := localSamplingTolerance_bounds q N hq hε hεle
  let x : SCCState W s := ⟨s, rfl⟩
  let p := Fintype.card (SCCState W s)
  have hp : 0 < p := Fintype.card_pos_iff.mpr ⟨x⟩
  have hpq : p ≤ q := Fintype.card_subtype_le _
  have hpt : p ≤ t := hpq.trans hqt
  unfold growthComponentSeedBudget growthComponentCircuitSize
  split_ifs with hfixed hc hshort
  · refine ⟨Nat.zero_le _, ?_⟩
    change 2 * ((n + 1) * q) ≤ componentSizeEnvelope t
    have h := Nat.mul_le_mul_left 2 (Nat.mul_le_mul hnt hqt)
    unfold componentSizeEnvelope
    omega
  · obtain ⟨hcard, hseed⟩ := growthResourceScale_block q N L p n hp hpq (by omega)
      G σ ε (categorySegmentTolerance q ε / 2) hσ hδ hδhalf
    refine ⟨hseed.trans (by change t ≤ 2 * (t * t); nlinarith), ?_⟩
    have h := seededBridgeSize_envelope p n t _ hpt hnt hseed hcard
    have h1 := Nat.mul_le_mul hnt hpt
    have h2 := Nat.mul_le_mul hnt hqt
    change seededBridgeSize p n (growthRoundingSeed G σ n (categorySegmentTolerance q ε / 2)) +
      (n + 1) * p + 2 * ((n + 1) * q) ≤ componentSizeEnvelope t
    unfold componentSizeEnvelope
    omega
  · let model := models ⟨s, hc⟩
    let c := Fintype.card (PositiveSupportClass
      (doobMatrix (sccMatrix W s) model.lam model.right ^ model.blockExponent) x)
    let δ := localSamplingTolerance q N ε
    have hcpos : 0 < c := sccPeriodicModel_support_card_pos model x
    have hcp : c ≤ p := Fintype.card_subtype_le _
    have hct : c ≤ t := hcp.trans hpt
    have hboundary : roundingSeed c δ ≤ t :=
      (samplingResourceScale_boundary q N L c hcpos (hcp.trans hpq) ε hδ).trans hg.2.1
    have hblocks : ∀ i, p ^ (cutoffBlockLengths n L i + 1) ≤ t ∧
        growthRoundingSeed G σ (cutoffBlockLengths n L i) δ ≤ t := by
      intro i
      exact growthResourceScale_block q N L p _ hp hpq
        (Nat.le_of_lt (cutoffBlockLengths_upper n L hL i)) G σ ε δ hσ hδ le_rfl
    have hlength : ∀ i, cutoffBlockLengths n L i + 1 ≤ t := by
      intro i
      have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (cutoffBlockLengths n L j))
        (Finset.mem_univ i)
      rw [← bridgeBlockLength_eq_sum, cutoffBlockLengths_total] at h
      omega
    have hk : cutoffBoundaryCount n L + 1 ≤ t := by
      have h := (cutoff_block_count_bound n L).2
      omega
    have hseeds := seededBlockSeedBudget_envelope t (cutoffBlockLengths n L)
      (fun b => growthRoundingSeed G σ b δ) hk (fun i => (hblocks i).2)
    have hprefix : cutoffBoundaryCount n L * roundingSeed c δ ≤ t * t :=
      Nat.mul_le_mul (by omega) hboundary
    have hsize := seededPeriodicCircuitSize_envelope p c n L t δ
      (fun b => growthRoundingSeed G σ b δ) ht hpt hct hnt hboundary
      hlength (fun i => (hblocks i).2) (fun i => (hblocks i).1)
    change growthSCCSeedBudget model x G σ n L δ ≤ 2 * (t * t) ∧
      growthSCCCircuitSize model x G σ n L δ ≤ componentSizeEnvelope t
    constructor
    · change cutoffBoundaryCount n L * roundingSeed c δ +
        seededBlockSeedBudget (fun b => growthRoundingSeed G σ b δ) (cutoffBlockLengths n L) ≤ _
      omega
    · unfold growthSCCCircuitSize
      dsimp only
      change seededPeriodicCircuitSize p c (boundaryRoundingCircuitSize p c δ) n L δ
        (fun b => growthRoundingSeed G σ b δ) + (n + 1) * p + 2 * ((n + 1) * q) ≤ _
      have h1 := Nat.mul_le_mul hnt hpt
      have h2 := Nat.mul_le_mul hnt hqt
      unfold componentSizeEnvelope
      omega
  · exact ⟨Nat.zero_le _, Nat.zero_le _⟩

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ConditionedSizeEnvelope
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

def categorySizeEnvelope (t : ℕ) : ℕ :=
  t * (2 * (t * t)) + t * ((t * t) * componentSizeEnvelope t) + t * (t * t) + t * t

def conditionedSizeEnvelope (t : ℕ) : ℕ :=
  (t + t * (2 * (t * t))) + t * roundedSizeEnvelope t +
    (t * t) * (t * categorySizeEnvelope t) +
    2 * (t + t * (t * t)) + (t * t) * (4 * t + 2)





end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_GrowthAcceptedEnvelope
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

theorem growthCategory_resource_envelope {Q : Type} [Fintype Q] [DecidableEq Q] {n : ℕ}
    {W : Matrix Q Q ℝ} (models : ∀ c : CyclicSCCIndex W, SCCPeriodicModel W c.val)
    (G σ : ℝ) (hσ : 1 ≤ σ) (γ : Fin (n + 1) → Q)
    (hγ : RespectsGraph (fun i j => 0 < W i j) γ)
    (L : ℕ) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1) :
    let t := growthResourceScale (Fintype.card Q) n L G σ ε
    growthCategorySeedBudget models G σ γ L (categorySegmentTolerance (Fintype.card Q) ε) ≤ t * (2 * (t * t)) ∧
      growthCategoryCircuitSize models G σ γ L (categorySegmentTolerance (Fintype.card Q) ε) ≤ categorySizeEnvelope t := by
  dsimp only
  let q := Fintype.card Q
  let t := growthResourceScale q n L G σ ε
  change growthCategorySeedBudget models G σ γ L (categorySegmentTolerance q ε) ≤ t * (2 * (t * t)) ∧
    growthCategoryCircuitSize models G σ γ L (categorySegmentTolerance q ε) ≤ categorySizeEnvelope t
  let R := fun i j => 0 < W i j
  let l := graphCategoryBlockLengths R γ
  have hscale := samplingResourceScale_spec q n L ε
  have hg := growthResourceScale_spec q n L G σ ε
  have hqT : q ≤ t := by omega
  have hnT : n + 1 ≤ t := hscale.2.1.trans hg.2.1
  have hk : (graphInteriorCuts R γ).card + 1 ≤ t := by
    have h := graphCategoryBlockLengths_count R γ hγ
    change (graphInteriorCuts R γ).card + 1 ≤ 2 * q - 1 at h
    omega
  have hblocks := fun i => growthComponent_resource_envelope models G σ hσ (categorySegmentStart R γ i)
    n (l i) L (category_segment_length_le R γ i) hL ε hε hεle
  have hseed : growthCategorySeedBudget models G σ γ L (categorySegmentTolerance q ε) ≤ t * (2 * (t * t)) := by
    unfold growthCategorySeedBudget
    calc
      _ ≤ ∑ _i : Fin ((graphInteriorCuts R γ).card + 1), 2 * (t * t) :=
        Finset.sum_le_sum (fun i _ => (hblocks i).1)
      _ = ((graphInteriorCuts R γ).card + 1) * (2 * (t * t)) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hk
  have hlength : ∀ i, l i + 1 ≤ t := fun i => (Nat.add_le_add_right (category_segment_length_le R γ i) 1).trans hnT
  have hweighted : (∑ i, ((l i + 1) * q) * growthComponentCircuitSize models G σ (categorySegmentStart R γ i)
      n (l i) L (categorySegmentTolerance q ε)) ≤ t * ((t * t) * componentSizeEnvelope t) := by
    calc
      _ ≤ ∑ _i : Fin ((graphInteriorCuts R γ).card + 1), (t * t) * componentSizeEnvelope t := by
        apply Finset.sum_le_sum
        intro i _
        exact Nat.mul_le_mul (Nat.mul_le_mul (hlength i) hqT) (hblocks i).2
      _ = ((graphInteriorCuts R γ).card + 1) * ((t * t) * componentSizeEnvelope t) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hk
  have hout : (∑ i, (l i + 1) * q) ≤ t * (t * t) := by
    calc
      _ ≤ ∑ _i : Fin ((graphInteriorCuts R γ).card + 1), t * t :=
        Finset.sum_le_sum (fun i _ => Nat.mul_le_mul (hlength i) hqT)
      _ = ((graphInteriorCuts R γ).card + 1) * (t * t) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hk
  refine ⟨hseed, ?_⟩
  have hfinal := Nat.mul_le_mul hnT hqT
  unfold growthCategoryCircuitSize categorySizeEnvelope
  dsimp only
  change growthCategorySeedBudget models G σ γ L (categorySegmentTolerance q ε) +
    (∑ i, ((l i + 1) * q) * growthComponentCircuitSize models G σ (categorySegmentStart R γ i)
      n (l i) L (categorySegmentTolerance q ε)) + (∑ i, (l i + 1) * q) + (n + 1) * q ≤ _
  omega

/-- The complete actual accepted-graph circuit, including all copied
category circuits and selector wires, has a fixed polynomial envelope.
Only the primitive growth resource scale depends on the input length. -/
theorem growthAcceptedCircuitSize_envelope {Q : Type} [Fintype Q] [DecidableEq Q] {n : ℕ}
    (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (s : Q) (F : Finset Q)
    (hZ : 0 < ∑ γ : Fin (n + 1) → Q, acceptedGraphWeight W s F γ)
    (models : ∀ d : CyclicSCCIndex W, SCCPeriodicModel W d.val)
    (G σ : ℝ) (hσ : 1 ≤ σ) (L : ℕ) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1) :
    growthAcceptedCircuitSize W hW s F models G σ n L ε ≤
      conditionedSizeEnvelope (growthResourceScale (Fintype.card Q) n L G σ ε) := by
  classical
  let q := Fintype.card Q
  let t := growthResourceScale q n L G σ ε
  let c := Fintype.card (AcceptedGraphCategory W s F n)
  have hscale := samplingResourceScale_spec q n L ε
  have hg := growthResourceScale_spec q n L G σ ε
  have ht : 0 < t := hg.1
  have hqT : q ≤ t := by omega
  have ho : (n + 1) * q ≤ t * t := Nat.mul_le_mul (hscale.2.1.trans hg.2.1) hqT
  obtain ⟨hc, ha⟩ := growthResourceScale_category W hW s F n L hZ G σ ε hε
  have hcat : ∀ d : AcceptedGraphCategory W s F n,
      growthCategorySeedBudget models G σ (acceptedGraphRepresentative W hW s F d) L
        (categorySegmentTolerance q ε) ≤ t * (2 * (t * t)) ∧
      growthCategoryCircuitSize models G σ (acceptedGraphRepresentative W hW s F d) L
        (categorySegmentTolerance q ε) ≤ categorySizeEnvelope t := by
    intro d
    have hs := acceptedGraphRepresentative_spec W hW s F d
    have hgraph := (edgePathWeight_pos_iff W hW (acceptedGraphRepresentative W hW s F d)).mp hs.2.2.2
    exact growthCategory_resource_envelope models G σ hσ
      (acceptedGraphRepresentative W hW s F d) hgraph L hL ε hε hεle
  have hmax : growthAcceptedConditionalSeed W hW s F models G σ n L ε ≤ t * (2 * (t * t)) :=
    Finset.sup_le (fun d _ => (hcat d).1)
  have hr : growthAcceptedSeedBudget W hW s F models G σ n L ε ≤ t + t * (2 * (t * t)) :=
    Nat.add_le_add ha hmax
  have hAsize : acceptedGraphChoiceSize W s F n ε ≤ roundedSizeEnvelope t := by
    change boundaryRoundingCircuitSize c c (ε / 2) ≤ roundedSizeEnvelope t
    exact boundaryRoundingCircuitSize_envelope c c t _ ht hc hc ha
  have hsum : (∑ d : AcceptedGraphCategory W s F n,
      growthCategoryCircuitSize models G σ (acceptedGraphRepresentative W hW s F d) L (categorySegmentTolerance q ε)) ≤
      t * categorySizeEnvelope t := by
    calc
      _ ≤ ∑ _d : AcceptedGraphCategory W s F n, categorySizeEnvelope t := Finset.sum_le_sum (fun d _ => (hcat d).2)
      _ = c * categorySizeEnvelope t := by simp [c]
      _ ≤ _ := Nat.mul_le_mul_right _ hc
  unfold growthAcceptedCircuitSize conditionedSizeEnvelope
  dsimp only
  gcongr

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ConditionedSizePolynomial
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped Matrix

theorem conditionedSizeEnvelope_polynomial (t : ℕ) (ht : 0 < t) :
    (conditionedSizeEnvelope t : ℝ) ≤ 131 * (t : ℝ) ^ 18 := by
  have ht' : (1 : ℝ) ≤ t := Nat.one_le_cast.mpr ht
  have h1 := pow_le_pow_right₀ ht' (by norm_num : 1 ≤ 18)
  have h2 := pow_le_pow_right₀ ht' (by norm_num : 2 ≤ 18)
  have h3 := pow_le_pow_right₀ ht' (by norm_num : 3 ≤ 18)
  have h4 := pow_le_pow_right₀ ht' (by norm_num : 4 ≤ 18)
  have h5 := pow_le_pow_right₀ ht' (by norm_num : 5 ≤ 18)
  have h6 := pow_le_pow_right₀ ht' (by norm_num : 6 ≤ 18)
  have h7 := pow_le_pow_right₀ ht' (by norm_num : 7 ≤ 18)
  have h8 := pow_le_pow_right₀ ht' (by norm_num : 8 ≤ 18)
  have h9 := pow_le_pow_right₀ ht' (by norm_num : 9 ≤ 18)
  have h10 := pow_le_pow_right₀ ht' (by norm_num : 10 ≤ 18)
  have h11 := pow_le_pow_right₀ ht' (by norm_num : 11 ≤ 18)
  have h12 := pow_le_pow_right₀ ht' (by norm_num : 12 ≤ 18)
  have h13 := pow_le_pow_right₀ ht' (by norm_num : 13 ≤ 18)
  have h14 := pow_le_pow_right₀ ht' (by norm_num : 14 ≤ 18)
  have h15 := pow_le_pow_right₀ ht' (by norm_num : 15 ≤ 18)
  have h16 := pow_le_pow_right₀ ht' (by norm_num : 16 ≤ 18)
  have h17 := pow_le_pow_right₀ ht' (by norm_num : 17 ≤ 18)
  simp only [pow_one] at h1
  unfold conditionedSizeEnvelope categorySizeEnvelope componentSizeEnvelope periodicSizeEnvelope
    parallelBlockSizeEnvelope selectedBlockSizeEnvelope repeatedBoundarySizeEnvelope roundedSizeEnvelope
  push_cast
  ring_nf
  linarith only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_GrowthAcceptedPolynomial
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

/-- Uniform polynomial size for the actual accepted-graph circuit, with
constants chosen before start state, accepting set, length and accuracy. -/
theorem growthAcceptedCircuitSize_polynomial {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y)
    (models : ∀ d : CyclicSCCIndex W, SCCPeriodicModel W d.val)
    (G σ A D : ℝ) (hG : 1 ≤ G) (hσ : 1 ≤ σ) (hA : 0 < A) (hD : 0 < D) :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (n L : ℕ) (s : Q) (F : Finset Q) (ε : ℝ),
        0 < ∑ γ : Fin (n + 1) → Q, acceptedGraphWeight W s F γ →
        0 < L → 0 < ε → ε ≤ 1 / 2 →
        (L : ℝ) ≤ A * Real.log ((n + 1 : ℕ) / ε) + D →
        logInv (localSamplingTolerance (Fintype.card Q) n ε) ≤ L →
        (growthAcceptedCircuitSize W hW s F models G σ n L ε : ℝ) ≤
          C * (((n + 1 : ℕ) : ℝ) / ε) ^ k := by
  obtain ⟨B, k, hB, hscale⟩ := growthResourceScale_polynomial (Fintype.card Q) Fintype.card_pos
    G σ A D hG hσ hA hD
  refine ⟨131 * B ^ 18, k * 18, by positivity, ?_⟩
  intro n L s F ε hZ hL hε hεle hlen hcost
  let t := growthResourceScale (Fintype.card Q) n L G σ ε
  have henv := growthAcceptedCircuitSize_envelope W hW s F hZ models G σ hσ L hL ε hε (by linarith)
  have henv' : (growthAcceptedCircuitSize W hW s F models G σ n L ε : ℝ) ≤ (conditionedSizeEnvelope t : ℝ) := by
    exact_mod_cast henv
  have ht := (growthResourceScale_spec (Fintype.card Q) n L G σ ε).1
  have htbound := hscale n L ε hε hεle hlen hcost
  calc
    _ ≤ 131 * (t : ℝ) ^ 18 := henv'.trans (conditionedSizeEnvelope_polynomial t ht)
    _ ≤ 131 * (B * (((n + 1 : ℕ) : ℝ) / ε) ^ k) ^ 18 := by gcongr
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_LabelRecording
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

/-- A deterministic partial binary graph retains each label separately,
including two labels that lead to the same original state. -/
abbrev LabeledTrajectory (Q : Type) (n : ℕ) := (Fin (n + 1) → Q) × Bits n

def AcceptedLabeledTrajectory {Q : Type} (step : Q → Bool → Option Q)
    (s : Q) (F : Finset Q) {n : ℕ} (p : LabeledTrajectory Q n) : Prop :=
  p.1 0 = s ∧ p.1 (Fin.last n) ∈ F ∧
    ∀ i : Fin n, step (p.1 i.castSucc) (p.2 i) = some (p.1 i.succ)

def labeledTrajectoryWeight {Q : Type} (step : Q → Bool → Option Q)
    (s : Q) (F : Finset Q) {n : ℕ} (p : LabeledTrajectory Q n) : ℝ := by
  classical
  exact if AcceptedLabeledTrajectory step s F p then 1 else 0

theorem labeledTrajectoryWeight_nonneg {Q : Type} (step : Q → Bool → Option Q)
    (s : Q) (F : Finset Q) {n : ℕ} (p : LabeledTrajectory Q n) :
    0 ≤ labeledTrajectoryWeight step s F p := by
  classical
  unfold labeledTrajectoryWeight
  split_ifs <;> norm_num

theorem labeledTrajectoryWeight_pos_iff {Q : Type} (step : Q → Bool → Option Q)
    (s : Q) (F : Finset Q) {n : ℕ} (p : LabeledTrajectory Q n) :
    0 < labeledTrajectoryWeight step s F p ↔ AcceptedLabeledTrajectory step s F p := by
  classical
  unfold labeledTrajectoryWeight
  split_ifs <;> simp_all

def recordedLabelMatrix {Q : Type} [DecidableEq Q] (step : Q → Bool → Option Q) :
    Matrix (Q × Bool) (Q × Bool) ℝ :=
  fun x y => if step x.1 y.2 = some y.1 then 1 else 0

theorem recordedLabelMatrix_zero_one {Q : Type} [DecidableEq Q] (step : Q → Bool → Option Q)
    (x y : Q × Bool) : recordedLabelMatrix step x y = 0 ∨ recordedLabelMatrix step x y = 1 := by
  unfold recordedLabelMatrix
  split_ifs <;> simp

theorem recordedLabelMatrix_nonneg {Q : Type} [DecidableEq Q] (step : Q → Bool → Option Q)
    (x y : Q × Bool) : 0 ≤ recordedLabelMatrix step x y := by
  rcases recordedLabelMatrix_zero_one step x y with h | h <;> simp [h]

theorem recordedLabelMatrix_pos_iff {Q : Type} [DecidableEq Q] (step : Q → Bool → Option Q)
    (x y : Q × Bool) : 0 < recordedLabelMatrix step x y ↔ step x.1 y.2 = some y.1 := by
  unfold recordedLabelMatrix
  split_ifs <;> simp_all

def recordedAccepting {Q : Type} [Fintype Q] [DecidableEq Q] (F : Finset Q) : Finset (Q × Bool) :=
  Finset.univ.filter (fun x => x.1 ∈ F)

theorem mem_recordedAccepting {Q : Type} [Fintype Q] [DecidableEq Q]
    (F : Finset Q) (x : Q × Bool) : x ∈ recordedAccepting F ↔ x.1 ∈ F := by
  simp [recordedAccepting]

def recordTrajectory {Q : Type} {n : ℕ} (p : LabeledTrajectory Q n) : Fin (n + 1) → Q × Bool :=
  Fin.cons (p.1 0, false) (fun i => (p.1 i.succ, p.2 i))

def unrecordTrajectory {Q : Type} {n : ℕ} (γ : Fin (n + 1) → Q × Bool) : LabeledTrajectory Q n :=
  (fun i => (γ i).1, fun i => (γ i.succ).2)

theorem recordTrajectory_zero {Q : Type} {n : ℕ} (p : LabeledTrajectory Q n) :
    recordTrajectory p 0 = (p.1 0, false) := rfl

theorem recordTrajectory_succ {Q : Type} {n : ℕ} (p : LabeledTrajectory Q n) (i : Fin n) :
    recordTrajectory p i.succ = (p.1 i.succ, p.2 i) := by simp [recordTrajectory]

theorem recordTrajectory_state {Q : Type} {n : ℕ} (p : LabeledTrajectory Q n) (i : Fin (n + 1)) :
    (recordTrajectory p i).1 = p.1 i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [recordTrajectory_succ]

theorem unrecord_recordTrajectory {Q : Type} {n : ℕ} (p : LabeledTrajectory Q n) :
    unrecordTrajectory (recordTrajectory p) = p := by
  apply Prod.ext
  · funext i
    exact recordTrajectory_state p i
  · funext i
    simp [unrecordTrajectory, recordTrajectory_succ]

theorem recordTrajectory_injective {Q : Type} {n : ℕ} :
    Function.Injective (@recordTrajectory Q n) :=
  Function.LeftInverse.injective unrecord_recordTrajectory

theorem record_unrecordTrajectory {Q : Type} {n : ℕ} (γ : Fin (n + 1) → Q × Bool)
    (hzero : (γ 0).2 = false) : recordTrajectory (unrecordTrajectory γ) = γ := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · apply Prod.ext
    · rfl
    · exact hzero.symm
  · simp [recordTrajectory_succ, unrecordTrajectory]

theorem recorded_acceptance_iff {Q : Type} [Fintype Q] [DecidableEq Q]
    (step : Q → Bool → Option Q) (s : Q) (F : Finset Q) {n : ℕ} (p : LabeledTrajectory Q n) :
    0 < acceptedGraphWeight (recordedLabelMatrix step) (s, false) (recordedAccepting F) (recordTrajectory p) ↔
      AcceptedLabeledTrajectory step s F p := by
  rw [acceptedGraphWeight_pos_iff (recordedLabelMatrix step) (s, false) (recordedAccepting F)
    (recordTrajectory p), edgePathWeight_pos_iff _ (recordedLabelMatrix_nonneg step)]
  simp only [recordTrajectory_zero, Prod.mk.injEq, and_true, mem_recordedAccepting,
    recordTrajectory_state, RespectsGraph, recordedLabelMatrix_pos_iff, recordTrajectory_succ,
    AcceptedLabeledTrajectory]

theorem recorded_weight_lift {Q : Type} [Fintype Q] [DecidableEq Q]
    (step : Q → Bool → Option Q) (s : Q) (F : Finset Q) {n : ℕ} (p : LabeledTrajectory Q n) :
    acceptedGraphWeight (recordedLabelMatrix step) (s, false) (recordedAccepting F) (recordTrajectory p) =
      labeledTrajectoryWeight step s F p := by
  classical
  have h01 : acceptedGraphWeight (recordedLabelMatrix step) (s, false) (recordedAccepting F)
      (recordTrajectory p) = 0 ∨ acceptedGraphWeight (recordedLabelMatrix step) (s, false)
        (recordedAccepting F) (recordTrajectory p) = 1 := by
    unfold acceptedGraphWeight
    split_ifs
    · exact edgePathWeight_zero_or_one _ (recordedLabelMatrix_zero_one step) _ _
    · exact Or.inl rfl
  have hp := recorded_acceptance_iff step s F p
  by_cases h : AcceptedLabeledTrajectory step s F p
  · rw [labeledTrajectoryWeight, if_pos h]
    exact h01.resolve_left (ne_of_gt (hp.mpr h))
  · rw [labeledTrajectoryWeight, if_neg h]
    exact h01.resolve_right (fun h1 => h (hp.mp (by rw [h1]; norm_num)))

theorem recorded_weight_supported {Q : Type} [Fintype Q] [DecidableEq Q]
    (step : Q → Bool → Option Q) (s : Q) (F : Finset Q) {n : ℕ}
    (γ : Fin (n + 1) → Q × Bool) (hγ : ¬ ∃ p : LabeledTrajectory Q n, recordTrajectory p = γ) :
    acceptedGraphWeight (recordedLabelMatrix step) (s, false) (recordedAccepting F) γ = 0 := by
  have hz : γ 0 ≠ (s, false) := by
    intro h
    apply hγ
    exact ⟨unrecordTrajectory γ, record_unrecordTrajectory γ (congrArg Prod.snd h)⟩
  unfold acceptedGraphWeight
  rw [if_neg (fun h => hz h.1)]

/-- Length is unchanged, including the empty trajectory. The extra label
at the start is fixed, so it creates no extra accepted paths. -/
theorem recorded_weight_sum {Q : Type} [Fintype Q] [DecidableEq Q]
    (step : Q → Bool → Option Q) (s : Q) (F : Finset Q) (n : ℕ) :
    (∑ p : LabeledTrajectory Q n, labeledTrajectoryWeight step s F p) =
      ∑ γ : Fin (n + 1) → Q × Bool,
        acceptedGraphWeight (recordedLabelMatrix step) (s, false) (recordedAccepting F) γ := by
  have h := embedded_weight_sum recordTrajectory recordTrajectory_injective
    (acceptedGraphWeight (recordedLabelMatrix step) (s, false) (recordedAccepting F))
    (recorded_weight_supported step s F (n := n))
  simpa only [recorded_weight_lift] using h

theorem recorded_normalized_law {Q : Type} [Fintype Q] [DecidableEq Q]
    (step : Q → Bool → Option Q) (s : Q) (F : Finset Q) {n : ℕ} (γ : Fin (n + 1) → Q × Bool) :
    (∑ p : LabeledTrajectory Q n, if recordTrajectory p = γ then
      normalizeWeights (labeledTrajectoryWeight step s F) p else 0) =
      normalizeWeights (acceptedGraphWeight (recordedLabelMatrix step) (s, false) (recordedAccepting F)) γ := by
  have h := embedded_normalized_weights recordTrajectory recordTrajectory_injective
    (acceptedGraphWeight (recordedLabelMatrix step) (s, false) (recordedAccepting F))
    (recorded_weight_supported step s F (n := n)) γ
  simpa only [recorded_weight_lift] using h

/-- Projecting expanded state paths recovers the uniform law on labeled
trajectories. Labels with identical original endpoints remain distinct. -/
theorem unrecorded_normalized_law {Q : Type} [Fintype Q] [DecidableEq Q]
    (step : Q → Bool → Option Q) (s : Q) (F : Finset Q) {n : ℕ} (p : LabeledTrajectory Q n) :
    (∑ γ : Fin (n + 1) → Q × Bool, if unrecordTrajectory γ = p then
      normalizeWeights (acceptedGraphWeight (recordedLabelMatrix step) (s, false) (recordedAccepting F)) γ else 0) =
      normalizeWeights (labeledTrajectoryWeight step s F) p := by
  classical
  simp_rw [← recorded_normalized_law step s F]
  rw [finite_pushforward_comp]
  simp only [unrecord_recordTrajectory]
  simp

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_SubcriticalRateConstruction
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix ENNReal NNReal

/-- The common growth argument only needs the actual model eigenvalues.
This interface permits spectral hypotheses to be transported through a
label-recording representation using positive subinvariant vectors. -/
theorem scc_uniform_subcritical_growth_of_rates {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y)
    (models : ∀ s : CyclicSCCIndex W, SCCPeriodicModel W s.val)
    (hmodel : ∀ s : CyclicSCCIndex W, (models s).lam < 2) :
    ∃ C γ : ℝ, 1 ≤ C ∧ 1 < γ ∧ γ < 2 ∧
      ∀ (s : CyclicSCCIndex W) (n : ℕ) (x y : SCCState W s.val),
        (sccMatrix W s.val ^ n) x y ≤ C * γ ^ n := by
  classical
  let rates : Option (CyclicSCCIndex W) → ℝ := Option.elim' 1 (fun s => (models s).lam)
  have hrates : ∀ s, rates s < 2 := by
    intro s
    cases s with
    | none => norm_num [rates]
    | some s => exact hmodel s
  let upper := Finset.univ.sup' Finset.univ_nonempty rates
  have hu : upper < 2 := (Finset.sup'_lt_iff _).mpr (fun s _ => hrates s)
  have h1 : 1 ≤ upper := Finset.le_sup' rates (Finset.mem_univ none)
  obtain ⟨γ, hγu, hγ2⟩ := exists_between hu
  have hγ1 : 1 < γ := h1.trans_lt hγu
  have hγlam (s : CyclicSCCIndex W) : (models s).lam ≤ γ :=
    (Finset.le_sup' rates (Finset.mem_univ (some s))).trans hγu.le
  have hc (s : CyclicSCCIndex W) :
      ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ) (x y : SCCState W s.val),
        (sccMatrix W s.val ^ n) x y ≤ C * γ ^ n :=
    positive_eigenvector_uniform_growth (sccMatrix W s.val) (fun x y => hW x.val y.val)
      (models s).lam (models s).lam_pos.le (models s).right (models s).right_pos
      (sccPeriodicModel_eigenvector W s.val (models s)) γ (hγlam s)
  choose c hc hg using hc
  let C := 1 + ∑ s, c s
  have hcn (s : CyclicSCCIndex W) : 0 ≤ c s := zero_le_one.trans (hc s)
  have hC : 1 ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg (fun s _ => hcn s))
  refine ⟨C, γ, hC, hγ1, hγ2, ?_⟩
  intro s n x y
  have hcs : c s ≤ C := by
    have hh := Finset.single_le_sum (fun s _ => hcn s) (Finset.mem_univ s)
    dsimp only [C]
    linarith
  exact (hg s n x y).trans
    (mul_le_mul_of_nonneg_right hcs (pow_nonneg (zero_lt_one.trans hγ1).le n))

/-- Actual circuit construction from the chosen subcritical SCC models. -/
theorem subcritical_accepted_graph_circuit_with_cutoff_of_rates {Q : Type}
    [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y)
    (h01 : ∀ x y, W x y = 0 ∨ W x y = 1)
    (models : ∀ d : CyclicSCCIndex W, SCCPeriodicModel W d.val)
    (hmodel : ∀ d : CyclicSCCIndex W, (models d).lam < 2) :
    ∃ G σ A D C : ℝ,
      1 ≤ G ∧ 1 < σ ∧ σ < 2 ∧ 0 < A ∧ 0 < D ∧ 0 ≤ C ∧
      ∀ (n : ℕ) (s : Q) (F : Finset Q) (ε : ℝ),
        0 < ∑ γ : Fin (n + 1) → Q, acceptedGraphWeight W s F γ → 0 < ε → ε ≤ 1 / 2 →
        ∃ L : ℕ, 0 < L ∧ (L : ℝ) ≤ A * Real.log ((n + 1 : ℕ) / ε) + D ∧
          logInv (categorySegmentTolerance (Fintype.card Q) ε / (8 * (n + 1 : ℕ))) ≤ L ∧
          ∃ S : Circuit (Fin (n + 1) × Q),
            S.randomBits = growthAcceptedSeedBudget W hW s F models G σ n L ε ∧
            (S.randomBits : ℝ) ≤ n + C * logInv ε ∧
            S.depth ≤ 13 ∧ S.size ≤ growthAcceptedCircuitSize W hW s F models G σ n L ε ∧
            SupportPreserving S graphPathEncode (normalizeWeights (acceptedGraphWeight W s F)) ∧
            tv (mass S graphPathEncode) (normalizeWeights (acceptedGraphWeight W s F)) ≤ ε := by
  classical
  obtain ⟨G, σ, hG, hσ, hσ2, hgrowth⟩ := scc_uniform_subcritical_growth_of_rates W hW models hmodel
  have hq : 0 < Fintype.card Q := Fintype.card_pos
  have hq' : (1 : ℝ) ≤ Fintype.card Q := Nat.one_le_cast.mpr hq
  have h2q : (0 : ℝ) < 2 * Fintype.card Q := by positivity
  have hlogq : 0 ≤ Real.log (2 * Fintype.card Q : ℝ) := Real.log_nonneg (by linarith)
  have hK := growthAcceptedOverhead_nonneg (Fintype.card Q) hq G hG
  have hJ := acceptedGraphSelectorCoefficient_nonneg (Fintype.card Q) hq
  obtain ⟨a, C, ha, hC, hpay⟩ := subcritical_block_budget_absorption
    (Real.log σ / Real.log 2) (2 * growthAcceptedOverhead (Fintype.card Q) G)
    (2 * Fintype.card Q * growthAcceptedOverhead (Fintype.card Q) G +
      acceptedGraphSelectorCoefficient (Fintype.card Q))
    (subcritical_log_rate hσ hσ2).2 (by positivity) (by positivity)
  obtain ⟨A, D, hA, hD, hcut⟩ := common_geometric_block_scaled_seed_cost
    (fun d => (models d).blockExponent) (fun d => (models d).exponent_pos)
    (fun d => (models d).coefficient) (fun d => (models d).rate)
    (fun d => (models d).coefficient_pos) (fun d => (models d).rate_pos)
    (fun d => (models d).rate_lt_one) a ha
  refine ⟨G, σ, A, D + A * Real.log (2 * Fintype.card Q : ℝ), C,
    hG, hσ, hσ2, hA, add_pos_of_pos_of_nonneg hD (mul_nonneg hA.le hlogq), hC, ?_⟩
  intro n s F ε hZ hε hεle
  have hε1 : ε ≤ 1 := by linarith
  obtain ⟨hη, hηle, _⟩ := categorySegmentTolerance_bounds (Fintype.card Q) hq ε hε hε1
  obtain ⟨L, hL, hlen, hcost, hforced, hmix⟩ :=
    hcut n (categorySegmentTolerance (Fintype.card Q) ε) hη hηle
  have hratio : (n + 1 : ℕ) / categorySegmentTolerance (Fintype.card Q) ε =
      ((n + 1 : ℕ) / ε) * (2 * Fintype.card Q : ℝ) := by
    unfold categorySegmentTolerance
    field_simp
  have hlog : Real.log ((n + 1 : ℕ) / categorySegmentTolerance (Fintype.card Q) ε) =
      Real.log ((n + 1 : ℕ) / ε) + Real.log (2 * Fintype.card Q : ℝ) := by
    rw [hratio, Real.log_mul (by positivity) h2q.ne']
  have hlen' : (L : ℝ) ≤ A * Real.log ((n + 1 : ℕ) / ε) +
      (D + A * Real.log (2 * Fintype.card Q : ℝ)) := by
    rw [hlog] at hlen
    linarith
  have hdom : a * samplingLogRatio n ε ≤ L := by
    have h16q : (1 : ℝ) ≤ 16 * Fintype.card Q := by linarith
    have hlog16 := div_nonneg (Real.log_nonneg h16q) (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    rw [acceptedGraph_local_precision_eq,
      logInv_scaled_precision _ ε (zero_lt_one.trans_le h16q) hε n] at hforced
    nlinarith
  have hmix' : ∀ d, (models d).blockExponent ∣ L ∧
      (models d).coefficient * (models d).rate ^ (L / (models d).blockExponent) ≤
        categorySegmentTolerance (Fintype.card Q) ε / (8 * (n + 1 : ℕ)) :=
    fun d => ⟨(hmix d).1, (hmix d).2.2⟩
  have hseed := hpay n L ε (growthAcceptedSeedBudget W hW s F models G σ n L ε)
    hε hεle hL hdom
    (growthAcceptedSeedBudget_log_bound W hW h01 s F hZ models G σ hG hσ.le hgrowth L ε hε hεle hL hmix')
  obtain ⟨f, S, hbits, he, hdepth, hsize, hs, hlaw, htv⟩ :=
    growth_accepted_graph_circuit W hW h01 s F hZ models G σ hG hσ.le hgrowth L ε hε hε1 hL hmix'
  refine ⟨L, hL, hlen', hcost, S, hbits, ?_, hdepth, hsize, ?_, ?_⟩
  · rw [hbits]
    exact hseed
  · apply sampler_circuit_support f graphPathEncode (normalizeWeights (acceptedGraphWeight W s F)) S hbits he
    intro seed
    exact div_pos (hs seed) hZ
  · rw [hlaw]
    exact htv

/-- Full resource guarantees from those same actual SCC models. -/
theorem subcritical_accepted_graph_sampling_of_rates {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (W : Matrix Q Q ℝ) (h01 : ∀ x y, W x y = 0 ∨ W x y = 1)
    (models : ∀ d : CyclicSCCIndex W, SCCPeriodicModel W d.val)
    (hmodel : ∀ d : CyclicSCCIndex W, (models d).lam < 2) :
    ∃ D C k : ℕ, ∀ (s : Q) (F : Finset Q) (n : ℕ),
      0 < ∑ γ : Fin (n + 1) → Q, acceptedGraphWeight W s F γ →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ S : Circuit (Fin (n + 1) × Q),
        S.depth ≤ D ∧
        (S.size : ℝ) ≤ (C : ℝ) * (((n + 1 : ℕ) : ℝ) / ε) ^ k ∧
        (S.randomBits : ℝ) ≤ n + (C : ℝ) * logInv ε ∧
        SupportPreserving S graphPathEncode (normalizeWeights (acceptedGraphWeight W s F)) ∧
        tv (mass S graphPathEncode) (normalizeWeights (acceptedGraphWeight W s F)) ≤ ε := by
  have hW : ∀ x y, 0 ≤ W x y := by
    intro x y
    rcases h01 x y with h | h <;> simp [h]
  obtain ⟨G, σ, A, B, R, hG, hσ, _, hA, hB, hR, hconstruct⟩ :=
    subcritical_accepted_graph_circuit_with_cutoff_of_rates W hW h01 models hmodel
  obtain ⟨V, k, hV, hsize⟩ := growthAcceptedCircuitSize_polynomial W hW models G σ A B hG hσ.le hA hB
  let C : ℕ := ⌈V⌉₊ + ⌈R⌉₊ + 1
  have hVC : V ≤ (C : ℝ) := by
    have h := Nat.le_ceil V
    dsimp only [C]
    simp only [Nat.cast_add, Nat.cast_one]
    linarith [(Nat.cast_nonneg ⌈R⌉₊ : (0 : ℝ) ≤ ⌈R⌉₊)]
  have hRC : R ≤ (C : ℝ) := by
    have h := Nat.le_ceil R
    dsimp only [C]
    simp only [Nat.cast_add, Nat.cast_one]
    linarith [(Nat.cast_nonneg ⌈V⌉₊ : (0 : ℝ) ≤ ⌈V⌉₊)]
  refine ⟨13, C, k, ?_⟩
  intro s F n hZ ε hε hεle
  obtain ⟨L, hL, hlen, hcost, S, _, hbits, hdepth, hSsize, hs, htv⟩ :=
    hconstruct n s F ε hZ hε hεle
  refine ⟨S, hdepth, ?_, ?_, hs, htv⟩
  · have hSsize' : (S.size : ℝ) ≤ growthAcceptedCircuitSize W hW s F models G σ n L ε := by
      exact_mod_cast hSsize
    exact (hSsize'.trans (hsize n L s F ε hZ hL hε hεle hlen hcost)).trans
      (mul_le_mul_of_nonneg_right hVC (by positivity))
  · apply hbits.trans
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hRC
      (zero_le_one.trans (logInv_ge_one hε hεle)))

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_LabeledTrajectorySampling
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix ENNReal NNReal



/-- The full state-and-label trajectory is encoded at each position by
the pair consisting of the state and its incoming label. The artificial
incoming label at position zero is fixed to false. -/
def labeledTrajectoryEncode {Q : Type} [DecidableEq Q] {n : ℕ} (p : LabeledTrajectory Q n) :
    (Fin (n + 1) × (Q × Bool)) → Bool := graphPathEncode (recordTrajectory p)

theorem labeledTrajectoryEncode_injective {Q : Type} [DecidableEq Q] (n : ℕ) :
    Function.Injective (@labeledTrajectoryEncode Q _ n) :=
  (graphPathEncode_injective n).comp recordTrajectory_injective



/-- A circuit already producing valid recorded paths is exactly the same
circuit on the injectively encoded original labeled trajectories. No
gates or random bits are added during this transport. -/
theorem recorded_sampler_transport {Q : Type} [Fintype Q] [DecidableEq Q]
    (step : Q → Bool → Option Q) (s : Q) (F : Finset Q) {n : ℕ}
    (hZ : 0 < ∑ p : LabeledTrajectory Q n, labeledTrajectoryWeight step s F p)
    (S : Circuit (Fin (n + 1) × (Q × Bool))) (ε : ℝ)
    (hs : SupportPreserving S graphPathEncode
      (normalizeWeights (acceptedGraphWeight (recordedLabelMatrix step) (s, false) (recordedAccepting F))))
    (htv : tv (mass S graphPathEncode)
      (normalizeWeights (acceptedGraphWeight (recordedLabelMatrix step) (s, false) (recordedAccepting F))) ≤ ε) :
    SupportPreserving S labeledTrajectoryEncode (normalizeWeights (labeledTrajectoryWeight step s F)) ∧
      tv (mass S labeledTrajectoryEncode) (normalizeWeights (labeledTrajectoryWeight step s F)) ≤ ε := by
  classical
  have heZ : 0 < ∑ γ : Fin (n + 1) → Q × Bool,
      acceptedGraphWeight (recordedLabelMatrix step) (s, false) (recordedAccepting F) γ := by
    rwa [← recorded_weight_sum step s F n]
  choose f hf hpos using hs
  have hw (seed : Bits S.randomBits) :
      0 < acceptedGraphWeight (recordedLabelMatrix step) (s, false) (recordedAccepting F) (f seed) :=
    (div_pos_iff_of_pos_right heZ).mp (hpos seed)
  have hrecord (seed : Bits S.randomBits) : recordTrajectory (unrecordTrajectory (f seed)) = f seed := by
    have hstart := ((acceptedGraphWeight_pos_iff _ _ _ _).mp (hw seed)).1
    exact record_unrecordTrajectory (f seed) (congrArg Prod.snd hstart)
  let g := unrecordTrajectory ∘ f
  have hge : ∀ seed : Bits S.randomBits, S.eval seed = labeledTrajectoryEncode (g seed) := by
    intro seed
    rw [hf seed]
    unfold labeledTrajectoryEncode
    dsimp only [g, Function.comp_apply]
    rw [hrecord]
  have hgs : ∀ seed : Bits S.randomBits, 0 < normalizeWeights (labeledTrajectoryWeight step s F) (g seed) := by
    intro seed
    apply div_pos _ hZ
    rw [← recorded_weight_lift step s F]
    dsimp only [g, Function.comp_apply]
    rw [hrecord]
    exact hw seed
  have hmass : mass S graphPathEncode = finiteSeedLaw f :=
    sampler_circuit_mass f graphPathEncode (graphPathEncode_injective n) S rfl hf
  have hgmass : mass S labeledTrajectoryEncode = finiteSeedLaw g :=
    sampler_circuit_mass g labeledTrajectoryEncode (labeledTrajectoryEncode_injective n) S rfl hge
  refine ⟨sampler_circuit_support g labeledTrajectoryEncode _ S rfl hge hgs, ?_⟩
  have hm := tv_map_le unrecordTrajectory (finiteSeedLaw f)
    (normalizeWeights (acceptedGraphWeight (recordedLabelMatrix step) (s, false) (recordedAccepting F)))
  simp only [unrecorded_normalized_law step s F] at hm
  rw [hmass] at htv
  rw [hgmass]
  change tv (finiteSeedLaw (unrecordTrajectory ∘ f)) _ ≤ ε
  rw [finiteSeedLaw_map]
  exact hm.trans htv



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_LabeledWordLaw
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def AcceptedPartialWord {Q : Type} (step : Q → Bool → Option Q)
    (s : Q) (F : Finset Q) {n : ℕ} (w : Bits n) : Prop :=
  ∃ γ : Fin (n + 1) → Q, AcceptedLabeledTrajectory step s F (γ, w)

def partialWordWeight {Q : Type} (step : Q → Bool → Option Q)
    (s : Q) (F : Finset Q) {n : ℕ} (w : Bits n) : ℝ := by
  classical
  exact if AcceptedPartialWord step s F w then 1 else 0

local instance partialWordLawDecidable {Q : Type} (step : Q → Bool → Option Q)
    (s : Q) (F : Finset Q) {n : ℕ} (w : Bits n) :
    Decidable (AcceptedPartialWord step s F w) := Classical.propDecidable _

theorem accepted_labeled_states_unique {Q : Type} (step : Q → Bool → Option Q)
    (s : Q) (F : Finset Q) {n : ℕ} (γ η : Fin (n + 1) → Q) (w : Bits n)
    (hγ : AcceptedLabeledTrajectory step s F (γ, w))
    (hη : AcceptedLabeledTrajectory step s F (η, w)) : γ = η := by
  funext t
  refine Fin.induction ?_ (fun i hi => ?_) t
  · exact hγ.1.trans hη.1.symm
  · have h1 := hγ.2.2 i
    have h2 := hη.2.2 i
    change step (γ i.castSucc) (w i) = some (γ i.succ) at h1
    rw [hi] at h1
    exact Option.some.inj (h1.symm.trans h2)

theorem accepted_labeled_same_word {Q : Type} (step : Q → Bool → Option Q)
    (s : Q) (F : Finset Q) {n : ℕ} (p q : LabeledTrajectory Q n)
    (hp : AcceptedLabeledTrajectory step s F p) (hq : AcceptedLabeledTrajectory step s F q)
    (hw : p.2 = q.2) : p = q := by
  apply Prod.ext _ hw
  apply accepted_labeled_states_unique step s F p.1 q.1 p.2 hp
  simpa only [hw] using hq

/-- Determinism, not the number of outgoing states, makes each accepted
word have exactly one labeled trajectory. -/
theorem labeled_word_fiber_mass {Q : Type} [Fintype Q]
    (step : Q → Bool → Option Q) (s : Q) (F : Finset Q) {n : ℕ} (w : Bits n) :
    fiberMass (fun p : LabeledTrajectory Q n => p.2) (labeledTrajectoryWeight step s F) w =
      partialWordWeight step s F w := by
  classical
  by_cases hw : AcceptedPartialWord step s F w
  · obtain ⟨γ, hγ⟩ := hw
    have hw' : AcceptedPartialWord step s F w := ⟨γ, hγ⟩
    rw [partialWordWeight, if_pos hw']
    unfold fiberMass
    rw [Finset.sum_eq_single (γ, w)]
    · simp [fiberWeight, labeledTrajectoryWeight, hγ]
    · intro p _ hne
      unfold fiberWeight
      by_cases hpw : p.2 = w
      · rw [if_pos hpw]
        have hp : ¬ AcceptedLabeledTrajectory step s F p := fun h =>
          hne (accepted_labeled_same_word step s F p (γ, w) h hγ hpw)
        exact if_neg hp
      · exact if_neg hpw
    · simp
  · rw [partialWordWeight, if_neg hw]
    unfold fiberMass
    apply Finset.sum_eq_zero
    intro p _
    unfold fiberWeight
    by_cases hpw : p.2 = w
    · rw [if_pos hpw]
      have hp : ¬ AcceptedLabeledTrajectory step s F p := by
        intro h
        apply hw
        exact ⟨p.1, by simpa only [← hpw] using h⟩
      exact if_neg hp
    · exact if_neg hpw

theorem labeled_word_weight_sum {Q : Type} [Fintype Q]
    (step : Q → Bool → Option Q) (s : Q) (F : Finset Q) (n : ℕ) :
    (∑ w : Bits n, partialWordWeight step s F w) =
      ∑ p : LabeledTrajectory Q n, labeledTrajectoryWeight step s F p := by
  simp_rw [← labeled_word_fiber_mass step s F]
  exact fiberMass_sum _ _

theorem normalized_fiberMass {Ω C : Type} [Fintype Ω] [Fintype C] [DecidableEq C]
    (f : Ω → C) (w : Ω → ℝ) (c : C) :
    fiberMass f (normalizeWeights w) c = normalizeWeights (fiberMass f w) c := by
  classical
  simp only [fiberMass, fiberWeight, normalizeWeights]
  have hz : (∑ c, ∑ x, if f x = c then w x else 0) = ∑ x, w x := fiberMass_sum f w
  rw [hz, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

/-- Uniform trajectory sampling projects to uniform accepted words;
this exact identity would fail without deterministic labeled transitions. -/
theorem labeled_word_normalized_law {Q : Type} [Fintype Q]
    (step : Q → Bool → Option Q) (s : Q) (F : Finset Q) {n : ℕ} (w : Bits n) :
    (∑ p : LabeledTrajectory Q n, if p.2 = w then
      normalizeWeights (labeledTrajectoryWeight step s F) p else 0) =
      normalizeWeights (partialWordWeight step s F) w := by
  have h := normalized_fiberMass (fun p : LabeledTrajectory Q n => p.2)
    (labeledTrajectoryWeight step s F) w
  have he : fiberMass (fun p : LabeledTrajectory Q n => p.2) (labeledTrajectoryWeight step s F) =
      partialWordWeight step s F := funext (labeled_word_fiber_mass step s F)
  rw [he] at h
  exact h



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_LabeledWordCircuit
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- Decode every label by one OR gate on the recorded one-hot state.
All labels are decoded in parallel, with no new fair bits. -/
theorem labeled_word_projection_circuit {Q : Type} [Fintype Q] [DecidableEq Q] {n : ℕ}
    (C : Circuit (Fin (n + 1) × (Q × Bool)))
    (f : Bits C.randomBits → LabeledTrajectory Q n)
    (hf : ∀ seed, C.eval seed = labeledTrajectoryEncode (f seed)) :
    ∃ S : Circuit (Fin n), ∃ hbits : S.randomBits = C.randomBits,
      (∀ (seed : Bits C.randomBits) i, S.eval (fun j => seed (Fin.cast hbits j)) i = (f seed).2 i) ∧
      S.depth ≤ C.depth + 1 ∧
      S.size ≤ C.size + ((n + 1) * (Fintype.card Q * 2)) + n * (Fintype.card Q + 2) := by
  let e := Fintype.equivFin (Fin (n + 1) × (Q × Bool))
  let fs := fun i : Fin n => formulaIndexedAny (fun x : Q => CircuitFormula.input (e (i.succ, (x, true))))
  have hd : ∀ i, formulaDepth (fs i) ≤ 1 := fun i =>
    formulaIndexedAny_depth _ 0 (fun x => le_rfl)
  obtain ⟨B, hBbits, hBeval, hBD, hBsize⟩ := formula_fintype_family_circuit fs 1 hd
  let input := fun j : Fin B.randomBits => e.symm (Fin.cast hBbits j)
  obtain ⟨S, hbits, he, hD, hsize⟩ := circuit_compose C B input
  refine ⟨S, hbits, ?_, hD.trans (Nat.add_le_add_left hBD C.depth), ?_⟩
  · intro seed i
    rw [he]
    have hb := hBeval (fun j => C.eval seed (e.symm j)) i
    change B.eval (fun j => C.eval seed (input j)) i = _ at hb
    rw [hb]
    apply Bool.eq_iff_iff.mpr
    rw [formulaIndexedAny_eval]
    simp only [formulaEval, Equiv.symm_apply_apply, hf seed,
      labeledTrajectoryEncode, graphPathEncode, recordTrajectory_succ, decide_eq_true_eq,
      Prod.mk.injEq]
    simp
  · have hleaf (i : Fin n) : formulaCost (fs i) ≤ Fintype.card Q + 1 := by
      have h := formulaIndexedAny_cost (fun x : Q => CircuitFormula.input (e (i.succ, (x, true))))
        0 (fun x => le_rfl)
      simpa only [Nat.zero_add, Nat.mul_one] using h
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hleaf i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hBsize
    nlinarith

/-- The actual decoded word circuit inherits support and joint TV error
from the full labeled-trajectory sampler. -/
theorem labeled_word_sampler_transport {Q : Type} [Fintype Q] [DecidableEq Q]
    (step : Q → Bool → Option Q) (s : Q) (F : Finset Q) {n : ℕ}
    (hZ : 0 < ∑ p : LabeledTrajectory Q n, labeledTrajectoryWeight step s F p)
    (C : Circuit (Fin (n + 1) × (Q × Bool))) (ε : ℝ)
    (hs : SupportPreserving C labeledTrajectoryEncode (normalizeWeights (labeledTrajectoryWeight step s F)))
    (ht : tv (mass C labeledTrajectoryEncode) (normalizeWeights (labeledTrajectoryWeight step s F)) ≤ ε) :
    ∃ S : Circuit (Fin n), S.randomBits = C.randomBits ∧
      S.depth ≤ C.depth + 1 ∧
      S.size ≤ C.size + ((n + 1) * (Fintype.card Q * 2)) + n * (Fintype.card Q + 2) ∧
      SupportPreserving S (fun w : Bits n => w) (normalizeWeights (partialWordWeight step s F)) ∧
      tv (mass S (fun w : Bits n => w)) (normalizeWeights (partialWordWeight step s F)) ≤ ε := by
  classical
  choose f hf hp using hs
  obtain ⟨S, hbits, he, hD, hsize⟩ := labeled_word_projection_circuit C f hf
  let g := fun seed : Bits C.randomBits => (f seed).2
  have hge : ∀ seed, S.eval (fun j => seed (Fin.cast hbits j)) = g seed :=
    fun seed => funext (he seed)
  have hmass := sampler_circuit_mass f labeledTrajectoryEncode (labeledTrajectoryEncode_injective n) C rfl hf
  have hgmass := sampler_circuit_mass g (fun w : Bits n => w) Function.injective_id S hbits hge
  have hwordZ : 0 < ∑ w : Bits n, partialWordWeight step s F w := by
    rwa [labeled_word_weight_sum step s F n]
  refine ⟨S, hbits, hD, hsize, ?_, ?_⟩
  · apply sampler_circuit_support g (fun w : Bits n => w) _ S hbits hge
    intro seed
    have hraw := (div_pos_iff_of_pos_right hZ).mp (hp seed)
    have hvalid := (labeledTrajectoryWeight_pos_iff step s F (f seed)).mp hraw
    have hword : AcceptedPartialWord step s F (g seed) := ⟨(f seed).1, hvalid⟩
    apply div_pos _ hwordZ
    simp only [partialWordWeight, if_pos hword, zero_lt_one]
  · have hm := tv_map_le (fun p : LabeledTrajectory Q n => p.2)
      (finiteSeedLaw f) (normalizeWeights (labeledTrajectoryWeight step s F))
    simp only [labeled_word_normalized_law step s F] at hm
    rw [hmass] at ht
    rw [hgmass]
    change tv (finiteSeedLaw ((fun p : LabeledTrajectory Q n => p.2) ∘ f)) _ ≤ ε
    rw [finiteSeedLaw_map]
    exact hm.trans ht

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_FormulaSubstitution
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_FiniteStateEncoding
section
set_option autoImplicit false
noncomputable section
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







end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_StateLookupFormulas
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_HiddenLocalOutputs
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_HiddenRunCircuits
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

abbrev FullRunOutput (q n : ℕ) := Fin n ⊕ (Fin (n + 1) × Fin q)

def fullRunEncode {q n : ℕ} (z : Bits n × Path q n) : FullRunOutput q n → Bool :=
  Sum.elim z.1 (pathEncode z.2)





end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_MonotoneBlockRealization
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_TerminalSplitCounts
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_TerminalCountOrdering
section
set_option autoImplicit false
noncomputable section
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
derivation is not treated as an axiom or a completed result here. -/
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

end
end

-- Source module: Solutions.FSS23105365_PositiveTransitionHiddenModel
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_ComponentAperiodicity
section
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

end

-- Source module: Solutions.FSS23105365_TransientBlockAllocation
section
set_option autoImplicit false
noncomputable section
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



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_TransientMassDecay
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_SupportComponents
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_TransitionTransport
section
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

end

-- Source module: Solutions.FSS23105365_TerminalComponentModel
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_ComponentModelAssembly
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_TransitiveSupportHiddenModel
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_HiddenBlockRepresentation
section
set_option autoImplicit false
noncomputable section
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



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_DFARunFormulas
section
set_option autoImplicit false
noncomputable section
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

end
end

-- Source module: Solutions.FSS23105365_PairSampling
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

theorem drivenPath_last_run {q n : ℕ} (A : BinaryDFA q) (w : Bits n) :
    drivenPath A.step n A.start w (Fin.last n) = A.run w := by
  rw [← drivenPath_prefix]
  change ((List.ofFn w).take n).foldl A.step A.start = _
  rw [List.take_of_length_le (by simp)]
  rfl











end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_DFAAcceptedWordProjection
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def dfaPartialStep {q : ℕ} (A : BinaryDFA q) : Fin q → Bool → Option (Fin q) :=
  fun x b => some (A.step x b)

theorem dfa_accepted_trajectory_iff {q n : ℕ} (A : BinaryDFA q) (γ : Path q n) (w : Bits n) :
    AcceptedLabeledTrajectory (dfaPartialStep A) A.start A.accepting (γ, w) ↔
      γ = drivenPath A.step n A.start w ∧ A.accepts w = true := by
  constructor
  · intro h
    have he : drivenPath A.step n A.start w = γ := (drivenPath_eq_iff A.step n A.start w γ).mpr
      ⟨h.1.symm, fun i => Option.some.inj (h.2.2 i)⟩
    refine ⟨he.symm, ?_⟩
    apply decide_eq_true
    rw [← drivenPath_last_run A w, he]
    exact h.2.1
  · rintro ⟨rfl, hw⟩
    refine ⟨drivenPath_zero A.step n A.start w, ?_, ?_⟩
    · change drivenPath A.step n A.start w (Fin.last n) ∈ A.accepting
      rw [drivenPath_last_run A w]
      exact of_decide_eq_true hw
    · intro i
      simp [dfaPartialStep, drivenPath_step]

theorem acceptedPartialWord_dfa_iff {q n : ℕ} (A : BinaryDFA q) (w : Bits n) :
    AcceptedPartialWord (dfaPartialStep A) A.start A.accepting w ↔ A.accepts w = true := by
  simp only [AcceptedPartialWord, dfa_accepted_trajectory_iff, exists_eq_left]

/-- The abstract word law is exactly the canonical E.2 wordLaw, including
the normalization by the number of accepted words and zero mass outside. -/
theorem dfa_partialWordLaw_eq {q n : ℕ} (A : BinaryDFA q) :
    normalizeWeights (partialWordWeight (dfaPartialStep A) A.start A.accepting) = (wordLaw A : Bits n → ℝ) := by
  classical
  funext w
  by_cases hw : A.accepts w = true <;>
    simp [normalizeWeights, partialWordWeight, acceptedPartialWord_dfa_iff, wordLaw, acceptedWords, hw]

/-- A full accepted DFA-trajectory sampler can be converted to the
original E.2 output format with unchanged random bits and TV error.
This lemma itself does not assume the as-yet-open general trajectory
sampler exists. -/
theorem dfa_accepted_word_sampler_projection {q n : ℕ} (A : BinaryDFA q)
    (hnonempty : (acceptedWords A n).Nonempty)
    (C : Circuit (Fin (n + 1) × (Fin q × Bool))) (ε : ℝ)
    (hs : SupportPreserving C labeledTrajectoryEncode
      (normalizeWeights (labeledTrajectoryWeight (dfaPartialStep A) A.start A.accepting)))
    (ht : tv (mass C labeledTrajectoryEncode)
      (normalizeWeights (labeledTrajectoryWeight (dfaPartialStep A) A.start A.accepting)) ≤ ε) :
    ∃ S : Circuit (Fin n), S.randomBits = C.randomBits ∧
      S.depth ≤ C.depth + 1 ∧ S.size ≤ C.size + ((n + 1) * (q * 2)) + n * (q + 2) ∧
      SupportPreserving S (fun w : Bits n => w) (wordLaw A) ∧
      tv (mass S (fun w : Bits n => w)) (wordLaw A) ≤ ε := by
  classical
  obtain ⟨w, hw⟩ := hnonempty
  have hacc : A.accepts w = true := (Finset.mem_filter.mp hw).2
  have hp := (dfa_accepted_trajectory_iff A (drivenPath A.step n A.start w) w).mpr ⟨rfl, hacc⟩
  have hZ : 0 < ∑ p : LabeledTrajectory (Fin q) n,
      labeledTrajectoryWeight (dfaPartialStep A) A.start A.accepting p :=
    ((labeledTrajectoryWeight_pos_iff _ _ _ _).mpr hp).trans_le
      (Finset.single_le_sum (fun p _ => labeledTrajectoryWeight_nonneg _ _ _ p)
        (Finset.mem_univ (drivenPath A.step n A.start w, w)))
  obtain ⟨S, hbits, hD, hsize, hs', ht'⟩ := labeled_word_sampler_transport
    (dfaPartialStep A) A.start A.accepting hZ C ε hs ht
  rw [dfa_partialWordLaw_eq A] at hs' ht'
  exact ⟨S, hbits, hD, by simpa only [Fintype.card_fin] using hsize, hs', ht'⟩

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_FairRecordedChain
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

def recordedFairKernel {Q : Type} [DecidableEq Q] (step : Q → Bool → Option Q) :
    Matrix (Q × Bool) (Q × Bool) ℝ := fun x y => (1 / 2 : ℝ) * recordedLabelMatrix step x y

theorem recordedFairKernel_nonneg {Q : Type} [DecidableEq Q] (step : Q → Bool → Option Q)
    (x y : Q × Bool) : 0 ≤ recordedFairKernel step x y :=
  mul_nonneg (by norm_num) (recordedLabelMatrix_nonneg step x y)

theorem recordedFairKernel_pos_iff {Q : Type} [DecidableEq Q] (step : Q → Bool → Option Q)
    (x y : Q × Bool) : 0 < recordedFairKernel step x y ↔ 0 < recordedLabelMatrix step x y := by
  exact mul_pos_iff_of_pos_left (by norm_num)

/-- The two labels have different expanded successors even when their
original successors coincide, so a complete graph has exactly two edges. -/
theorem recordedLabelMatrix_complete_rows {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (x : Q × Bool) :
    ∑ y, recordedLabelMatrix (fun q b => some (δ q b)) x y = 2 := by
  simp only [Fintype.sum_prod_type, recordedLabelMatrix, Option.some.injEq]
  rw [Finset.sum_comm]
  simp [eq_comm]

theorem recordedFairKernel_complete_rows {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (x : Q × Bool) :
    ∑ y, recordedFairKernel (fun q b => some (δ q b)) x y = 1 := by
  simp only [recordedFairKernel, ← Finset.mul_sum, recordedLabelMatrix_complete_rows]
  norm_num

theorem finitePathWeight_transition_scale {Q : Type} (μ : Q → ℝ) (W : Q → Q → ℝ)
    (c : ℝ) {n : ℕ} (γ : Fin (n + 1) → Q) :
    finitePathWeight μ (fun x y => c * W x y) γ = c ^ n * finitePathWeight μ W γ := by
  simp only [finitePathWeight, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  ring

def recordedFairPathWeight {Q : Type} [DecidableEq Q] (step : Q → Bool → Option Q)
    (s : Q) {n : ℕ} (γ : Fin (n + 1) → Q × Bool) : ℝ :=
  finitePathWeight (fun x => if x = (s, false) then 1 else 0) (recordedFairKernel step) γ

def recordedFairAcceptedWeight {Q : Type} [Fintype Q] [DecidableEq Q]
    (step : Q → Bool → Option Q) (s : Q) (F : Finset Q) {n : ℕ}
    (γ : Fin (n + 1) → Q × Bool) : ℝ :=
  if γ (Fin.last n) ∈ recordedAccepting F then recordedFairPathWeight step s γ else 0

theorem recordedFairPathWeight_scale {Q : Type} [DecidableEq Q]
    (step : Q → Bool → Option Q) (s : Q) {n : ℕ} (γ : Fin (n + 1) → Q × Bool) :
    recordedFairPathWeight step s γ = (1 / 2 : ℝ) ^ n *
      (if γ 0 = (s, false) then edgePathWeight (recordedLabelMatrix step) γ else 0) := by
  change finitePathWeight (fun x => if x = (s, false) then 1 else 0)
    (fun x y => (1 / 2 : ℝ) * recordedLabelMatrix step x y) γ = _
  rw [finitePathWeight_transition_scale (fun x => if x = (s, false) then 1 else 0)
    (recordedLabelMatrix step) (1 / 2) γ]
  simp only [finitePathWeight, edgePathWeight]
  split_ifs <;> simp

theorem recordedFairAcceptedWeight_scale {Q : Type} [Fintype Q] [DecidableEq Q]
    (step : Q → Bool → Option Q) (s : Q) (F : Finset Q) {n : ℕ}
    (γ : Fin (n + 1) → Q × Bool) :
    recordedFairAcceptedWeight step s F γ = (1 / 2 : ℝ) ^ n *
      acceptedGraphWeight (recordedLabelMatrix step) (s, false) (recordedAccepting F) γ := by
  change (if γ (Fin.last n) ∈ recordedAccepting F then recordedFairPathWeight step s γ else 0) =
    (1 / 2 : ℝ) ^ n * (if γ 0 = (s, false) ∧ γ (Fin.last n) ∈ recordedAccepting F
      then edgePathWeight (recordedLabelMatrix step) γ else 0)
  rw [recordedFairPathWeight_scale]
  by_cases hi : γ 0 = (s, false) <;> by_cases ht : γ (Fin.last n) ∈ recordedAccepting F <;> simp [hi, ht]















end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_GraphTerminal
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

/-- A state belongs to a terminal SCC when every reachable state can
return. This definition does not require the SCC to contain an edge. -/
def IsGraphTerminal {Q : Type} (R : Q → Q → Prop) (s : Q) : Prop :=
  ∀ y, Relation.ReflTransGen R s y → Relation.ReflTransGen R y s

theorem graphTerminal_of_reachable {Q : Type} (R : Q → Q → Prop) {x y : Q}
    (hx : IsGraphTerminal R x) (hxy : Relation.ReflTransGen R x y) :
    IsGraphTerminal R y := by
  intro z hyz
  exact (hx z (hxy.trans hyz)).trans hxy





/-- Choose a reachable state with the smallest reachable set. No further
strict loss of reachable states is possible, so its SCC is terminal. -/
theorem exists_reachable_graphTerminal {Q : Type} [Fintype Q] (R : Q → Q → Prop) (s : Q) :
    ∃ t, Relation.ReflTransGen R s t ∧ IsGraphTerminal R t := by
  classical
  obtain ⟨t, ht, hmin⟩ := Finset.exists_min_image (graphComponent R s)
    (fun x => (graphComponent R x).card) ⟨s, graphComponent_self R s⟩
  have hst := (mem_graphComponent R s t).mp ht
  refine ⟨t, hst, ?_⟩
  intro y hty
  have hy : y ∈ graphComponent R s := (mem_graphComponent R s y).mpr (hst.trans hty)
  have he : graphComponent R y = graphComponent R t :=
    Finset.eq_of_subset_of_card_le (graphComponent_subset R hty) (hmin y hy)
  exact ((graphComponent_eq_iff R y t).mp he).1

theorem graphTerminal_path_suffix {Q : Type} (R : Q → Q → Prop) {n : ℕ}
    (γ : Fin (n + 1) → Q) (hγ : RespectsGraph R γ) (i j : Fin (n + 1))
    (hij : i ≤ j) (hi : IsGraphTerminal R (γ i)) : IsGraphTerminal R (γ j) :=
  graphTerminal_of_reachable R hi (graph_path_reaches R γ hγ i j hij)

/-- A closed set consisting of one mutually reachable class is terminal.
This also supplies the contrapositive used to find a row-sum defect. -/
theorem graphTerminal_of_closed_class {Q : Type} (R : Q → Q → Prop) (s : Q)
    (S : Q → Prop) (hs : S s)
    (hclosed : ∀ x y, S x → R x y → S y)
    (hreturn : ∀ y, S y → Relation.ReflTransGen R y s) : IsGraphTerminal R s := by
  intro y hsy
  apply hreturn y
  induction hsy with
  | refl => exact hs
  | @tail x y _ hxy ih => exact hclosed x y ih hxy

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_TerminalSCCMixing
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

theorem terminal_scc_edge_closed {Q : Type} [Fintype Q] (W : Matrix Q Q ℝ) (s : Q)
    (hs : IsGraphTerminal (fun i j => 0 < W i j) s)
    (x : SCCState W s) (y : Q) (hxy : 0 < W x.val y) :
    graphComponent (fun i j => 0 < W i j) y = graphComponent (fun i j => 0 < W i j) s := by
  have hsx := ((graphComponent_eq_iff _ x.val s).mp x.property).2
  have hsy := hsx.tail hxy
  exact (graphComponent_eq_iff _ y s).mpr ⟨hs y hsy, hsy⟩

theorem terminal_scc_weight_zero_outside {Q : Type} [Fintype Q]
    (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (s : Q)
    (hs : IsGraphTerminal (fun i j => 0 < W i j) s)
    (x : SCCState W s) (y : Q)
    (hy : graphComponent (fun i j => 0 < W i j) y ≠ graphComponent (fun i j => 0 < W i j) s) :
    W x.val y = 0 := by
  apply le_antisymm _ (hW _ _)
  exact le_of_not_gt (fun hxy => hy (terminal_scc_edge_closed W s hs x y hxy))

/-- Restriction to a terminal SCC keeps every row sum exactly. -/
theorem terminal_scc_row_sum {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (s : Q)
    (hs : IsGraphTerminal (fun i j => 0 < W i j) s) (x : SCCState W s) :
    (∑ y, sccMatrix W s x y) = ∑ y, W x.val y := by
  classical
  apply embedded_weight_sum (fun y : SCCState W s => y.val) Subtype.val_injective (W x.val)
  intro y hy
  apply terminal_scc_weight_zero_outside W hW s hs x y
  intro he
  exact hy ⟨⟨y, he⟩, rfl⟩

theorem terminal_scc_cyclic_of_positive_rows {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y)
    (hrows : ∀ x, 0 < ∑ y, W x y) (s : Q)
    (hs : IsGraphTerminal (fun i j => 0 < W i j) s) : CyclicSCC W s := by
  classical
  have hsum : 0 < ∑ y : SCCState W s, sccMatrix W s ⟨s, rfl⟩ y := by
    rw [terminal_scc_row_sum W hW s hs]
    exact hrows s
  obtain ⟨y, _, hy⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun y _ => hW s y.val)).mp hsum
  exact cyclicSCC_of_internal_edge W hW s ⟨s, rfl⟩ y hy

/-- An irreducible stochastic matrix has a strictly positive stationary
probability vector. It is obtained from the proved Perron construction;
the stochastic row equation identifies its eigenvalue as exactly one. -/
theorem irreducible_stochastic_stationary {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (P : Matrix Q Q ℝ) (hirr : P.IsIrreducible) (hrows : ∀ x, ∑ y, P x y = 1) :
    ∃ π : Q → ℝ, (∀ x, 0 < π x) ∧ (∑ x, π x = 1) ∧
      ∀ y, ∑ x, π x * P x y = π y := by
  obtain ⟨μ, l, u, _, hl, _, _, _, hleft⟩ := irreducible_perron_vectors P hirr
  have he : μ = 1 := positive_left_right_eigenvalue_eq P μ 1 l (fun _ => 1) hl
    (fun _ => zero_lt_one) hleft (by intro x; simpa only [mul_one] using hrows x)
  have hsum : 0 < ∑ x, l x := Finset.sum_pos (fun x _ => hl x) Finset.univ_nonempty
  refine ⟨fun x => l x / (∑ z, l z), fun x => div_pos (hl x) hsum, ?_, ?_⟩
  · rw [← Finset.sum_div, div_self hsum.ne']
  · intro y
    simp only [div_mul_eq_mul_div, ← Finset.sum_div, hleft, he, one_mul]

theorem terminal_scc_stationary {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1)
    (s : Q) (hs : IsGraphTerminal (fun i j => 0 < P i j) s) :
    ∃ π : SCCState P s → ℝ, (∀ x, 0 < π x) ∧ (∑ x, π x = 1) ∧
      ∀ y, ∑ x, π x * sccMatrix P s x y = π y := by
  classical
  letI : Nonempty (SCCState P s) := ⟨⟨s, rfl⟩⟩
  have hc := terminal_scc_cyclic_of_positive_rows P hP
    (fun x => by rw [hrows x]; exact zero_lt_one) s hs
  exact irreducible_stochastic_stationary (sccMatrix P s)
    (cyclic_sccMatrix_irreducible P hP s hc)
    (fun x => (terminal_scc_row_sum P hP s hs x).trans (hrows x.val))



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ClosedSetMass
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

/-- Probability of ending in A after n transitions from the given state. -/
def kernelSetMass {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (A : Finset Q) (n : ℕ) (x : Q) : ℝ :=
  ∑ y ∈ A, (P ^ n) x y

theorem kernelSetMass_nonneg {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (A : Finset Q) (n : ℕ) (x : Q) :
    0 ≤ kernelSetMass P A n x :=
  Finset.sum_nonneg (fun y _ => Matrix.pow_apply_nonneg hP n x y)

theorem kernelSetMass_le_one {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1)
    (A : Finset Q) (n : ℕ) (x : Q) : kernelSetMass P A n x ≤ 1 := by
  calc
    _ ≤ ∑ y, (P ^ n) x y := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
      (fun y _ _ => Matrix.pow_apply_nonneg hP n x y)
    _ = 1 := stochastic_matrix_power_rows P hrows n x



theorem kernelSetMass_add {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (A : Finset Q) (m n : ℕ) (x : Q) :
    kernelSetMass P A (m + n) x = ∑ z, (P ^ m) x z * kernelSetMass P A n z := by
  simp only [kernelSetMass, pow_add, Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

theorem closed_set_power_zero_outside {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (A : Finset Q)
    (hclosed : ∀ x ∈ A, ∀ y, 0 < P x y → y ∈ A)
    (n : ℕ) (x y : Q) (hx : x ∈ A) (hy : y ∉ A) : (P ^ n) x y = 0 := by
  induction n generalizing x with
  | zero =>
    have hne : x ≠ y := fun h => hy (h ▸ hx)
    simp [hne]
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hp : 0 < P x z
    · rw [ih z (hclosed x hx z hp), mul_zero]
    · have hz : P x z = 0 := le_antisymm (le_of_not_gt hp) (hP x z)
      rw [hz, zero_mul]

theorem closed_set_mass_one {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1)
    (A : Finset Q) (hclosed : ∀ x ∈ A, ∀ y, 0 < P x y → y ∈ A)
    (n : ℕ) (x : Q) (hx : x ∈ A) : kernelSetMass P A n x = 1 := by
  calc
    _ = ∑ y, (P ^ n) x y := Finset.sum_subset (Finset.subset_univ A)
      (fun y _ hy => closed_set_power_zero_outside P hP A hclosed n x y hx hy)
    _ = 1 := stochastic_matrix_power_rows P hrows n x

theorem closed_set_mass_mono_add {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1)
    (A : Finset Q) (hclosed : ∀ x ∈ A, ∀ y, 0 < P x y → y ∈ A)
    (m n : ℕ) (x : Q) : kernelSetMass P A m x ≤ kernelSetMass P A (m + n) x := by
  rw [kernelSetMass_add]
  calc
    _ = ∑ z ∈ A, (P ^ m) x z * kernelSetMass P A n z := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [closed_set_mass_one P hP hrows A hclosed n z hz, mul_one]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
      (fun z _ _ => mul_nonneg (Matrix.pow_apply_nonneg hP m x z) (kernelSetMass_nonneg P hP A n z))

theorem closed_set_mass_mono {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1)
    (A : Finset Q) (hclosed : ∀ x ∈ A, ∀ y, 0 < P x y → y ∈ A)
    {m n : ℕ} (hmn : m ≤ n) (x : Q) : kernelSetMass P A m x ≤ kernelSetMass P A n x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact closed_set_mass_mono_add P hP hrows A hclosed m k x

/-- A finite closed set reachable from every state receives a uniformly
positive probability in one common positive block length. -/
theorem closed_set_uniform_hitting {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1)
    (A : Finset Q) (hclosed : ∀ x ∈ A, ∀ y, 0 < P x y → y ∈ A)
    (hreach : ∀ x, ∃ y ∈ A, Relation.ReflTransGen (fun i j => 0 < P i j) x y) :
    ∃ m : ℕ, ∃ η : ℝ, 0 < m ∧ 0 < η ∧ η < 1 ∧ ∀ x, η ≤ kernelSetMass P A m x := by
  classical
  have hh : ∀ x, ∃ n : ℕ, 0 < kernelSetMass P A n x := by
    intro x
    obtain ⟨y, hy, hxy⟩ := hreach x
    obtain ⟨n, hn⟩ := positive_power_of_reachable P hP hxy
    exact ⟨n, hn.trans_le (Finset.single_le_sum (fun z _ => Matrix.pow_apply_nonneg hP n x z) hy)⟩
  choose len hlen using hh
  let m := 1 + ∑ x, len x
  have hm : 0 < m := by dsimp only [m]; omega
  have hp (x : Q) : 0 < kernelSetMass P A m x := by
    have hx : len x ≤ m := by
      have := Finset.single_le_sum (fun z _ => Nat.zero_le (len z)) (Finset.mem_univ x)
      dsimp only [m]
      omega
    exact (hlen x).trans_le (closed_set_mass_mono P hP hrows A hclosed hx x)
  obtain ⟨x, _, hx⟩ := Finset.exists_min_image Finset.univ (kernelSetMass P A m) Finset.univ_nonempty
  refine ⟨m, kernelSetMass P A m x / 2, hm, div_pos (hp x) (by norm_num), ?_, ?_⟩
  · have hu := kernelSetMass_le_one P hP hrows A m x
    linarith
  · intro y
    have hxy := hx y (Finset.mem_univ y)
    linarith [hp x]

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_FairChainConditioning
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

















theorem recordedFairAcceptedWeight_eq_graph {Q : Type} [Fintype Q] [DecidableEq Q]
    (step : Q → Bool → Option Q) (s : Q) (F : Finset Q) {n : ℕ} (γ : Fin (n + 1) → Q × Bool) :
    recordedFairAcceptedWeight step s F γ =
      acceptedGraphWeight (recordedFairKernel step) (s, false) (recordedAccepting F) γ := by
  unfold recordedFairAcceptedWeight recordedFairPathWeight acceptedGraphWeight edgePathWeight finitePathWeight
  by_cases hs : γ 0 = (s, false) <;>
    by_cases ht : γ (Fin.last n) ∈ recordedAccepting F <;> simp [hs, ht]



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_WordKernelSemantics
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

theorem wordEnd_append {Q U : Type} (δ : Q → U → Q) (s : Q)
    {m n : ℕ} (u : Fin m → U) (v : Fin n → U) :
    wordEnd δ s (Fin.append u v) = wordEnd δ (wordEnd δ s u) v := by
  simp only [wordEnd, List.ofFn_fin_append, List.foldl_append]

theorem drivenPath_last_wordEnd {Q U : Type} (δ : Q → U → Q) (s : Q)
    {n : ℕ} (w : Fin n → U) : drivenPath δ n s w (Fin.last n) = wordEnd δ s w := by
  induction n generalizing s with
  | zero => simp [drivenPath, wordEnd]
  | succ n ih =>
    change drivenPath δ n (δ s (w 0)) (fun i => w i.succ) (Fin.last n) = _
    simpa only [wordEnd,
      List.ofFn_succ, List.foldl_cons] using ih (δ s (w 0)) (fun i => w i.succ)

def fairWordKernel {Q : Type} [DecidableEq Q] (δ : Q → Bool → Q) : Matrix Q Q ℝ :=
  uniformStepKernel δ

/-- Fair word fibers give the original stochastic kernel powers, even
when the two labels have the same successor. -/
theorem uniform_word_endpoint_power {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (n : ℕ) (s t : Q) :
    finiteSeedLaw (wordEnd δ s : Bits n → Q) t =
      (fairWordKernel δ ^ n) s t := by
  classical
  change (wordCount δ n s t : ℝ) / 2 ^ n = _
  induction n generalizing t with
  | zero =>
    by_cases h : s = t
    · subst t; simp [wordCount, wordEnd]
    · simp [wordCount, wordEnd, h, Ne.symm h, Matrix.one_apply]
  | succ n ih =>
    rw [wordCount_succ, Nat.cast_sum, pow_succ, Finset.sum_div, pow_succ,
      Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro u _
    rw [Nat.cast_mul, ← div_mul_div_comm, ih]
    simp only [fairWordKernel, uniformStepKernel, Fintype.card_bool, Nat.cast_ofNat]

theorem uniform_word_endpoint_positive {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) {n : ℕ} (w : Bits n) :
    0 < (fairWordKernel δ ^ n) s (wordEnd δ s w) := by
  rw [← uniform_word_endpoint_power]
  exact (finiteSeedLaw_pos_iff _ _).mpr ⟨w, rfl⟩

theorem uniform_word_average {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (n : ℕ) (f : Q → ℝ) :
    (∑ w : Bits n, (1 / (2 : ℝ) ^ n) * f (wordEnd δ s w)) =
      ∑ t, (fairWordKernel δ ^ n) s t * f t := by
  simp_rw [← uniform_word_endpoint_power, finiteSeedLaw_as_fiberMass]
  simp only [fiberMass, fiberWeight, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  simp

def fairAcceptedWordWeight {Q : Type} [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) {n : ℕ} (w : Bits n) : ℝ :=
  if wordEnd δ s w ∈ F then 1 / (2 : ℝ) ^ n else 0

theorem fairAcceptedWordWeight_nonneg {Q : Type} [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) {n : ℕ} (w : Bits n) :
    0 ≤ fairAcceptedWordWeight δ s F w := by
  unfold fairAcceptedWordWeight
  split_ifs <;> positivity

theorem fairAcceptedWordWeight_pos_iff {Q : Type} [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) {n : ℕ} (w : Bits n) :
    0 < fairAcceptedWordWeight δ s F w ↔ wordEnd δ s w ∈ F := by
  unfold fairAcceptedWordWeight
  split_ifs <;> simp_all

theorem fairAcceptedWordWeight_sum {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (n : ℕ) :
    (∑ w : Bits n, fairAcceptedWordWeight δ s F w) =
      kernelSetMass (fairWordKernel δ) F n s := by
  have h := uniform_word_average δ s n (fun t => if t ∈ F then 1 else 0)
  simpa [fairAcceptedWordWeight, kernelSetMass, mul_ite] using h

theorem fairAcceptedWordWeight_append {Q : Type} [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) {m n : ℕ}
    (u : Bits m) (v : Bits n) :
    fairAcceptedWordWeight δ s F (Fin.append u v) =
      (1 / (2 : ℝ) ^ m) * fairAcceptedWordWeight δ (wordEnd δ s u) F v := by
  simp only [fairAcceptedWordWeight, wordEnd_append, pow_add]
  split_ifs <;> simp [mul_comm]

theorem uniform_word_continuation {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (m n : ℕ) :
    (∑ w : Bits m, (1 / (2 : ℝ) ^ m) *
      kernelSetMass (fairWordKernel δ) F n (wordEnd δ s w)) =
      kernelSetMass (fairWordKernel δ) F (m + n) s := by
  rw [uniform_word_average]
  exact (kernelSetMass_add _ F m n s).symm

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_DFAWordKernel
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

theorem fairAcceptedWordWeight_dfa {q n : ℕ} (A : BinaryDFA q) (w : Bits n) :
    fairAcceptedWordWeight A.step A.start A.accepting w =
      (1 / (2 : ℝ) ^ n) * partialWordWeight (dfaPartialStep A) A.start A.accepting w := by
  classical
  have ha : A.accepts w = true ↔ wordEnd A.step A.start w ∈ A.accepting := by
    constructor
    · exact of_decide_eq_true
    · exact decide_eq_true
  simp only [fairAcceptedWordWeight, partialWordWeight, acceptedPartialWord_dfa_iff, ha]
  split_ifs <;> simp

/-- The fair-weight target of the positive branch is the canonical E.2
uniform accepted-word law after normalization. -/
theorem fairAcceptedWordWeight_normalized_dfa {q n : ℕ} (A : BinaryDFA q) :
    normalizeWeights (fairAcceptedWordWeight (n := n) A.step A.start A.accepting) = wordLaw A := by
  have he : fairAcceptedWordWeight (n := n) A.step A.start A.accepting =
      fun w => (1 / (2 : ℝ) ^ n) * partialWordWeight (dfaPartialStep A) A.start A.accepting w :=
    funext (fairAcceptedWordWeight_dfa A)
  rw [he, normalizeWeights_scale _ _ (by positivity), dfa_partialWordLaw_eq]

def recordingStep {Q : Type} (δ : Q → Bool → Q) : (Q × Bool) → Bool → (Q × Bool) :=
  fun x b => (δ x.1 b, b)

/-- Expanding the state by the last label turns even coincident labeled
successors into distinct fair edges. This is the same kernel used by the
terminal-avoiding branch, with no row renormalization. -/
theorem fairWordKernel_recording {Q : Type} [DecidableEq Q] (δ : Q → Bool → Q) :
    fairWordKernel (recordingStep δ) = recordedFairKernel (fun q b => some (δ q b)) := by
  funext x y
  rcases y with ⟨y, b⟩
  by_cases hf : δ x.1 false = y <;> by_cases ht : δ x.1 true = y <;> cases b <;>
    simp [fairWordKernel, uniformStepKernel, recordingStep, recordedFairKernel,
      recordedLabelMatrix, Fintype.card_subtype, Finset.filter_insert, Finset.filter_singleton,
      hf, ht]

theorem wordEnd_recording_fst {Q : Type} (δ : Q → Bool → Q) (s : Q × Bool)
    {n : ℕ} (w : Bits n) : (wordEnd (recordingStep δ) s w).1 = wordEnd δ s.1 w :=
  wordEnd_transition_map (recordingStep δ) δ Prod.fst (fun _ _ => rfl) w s

theorem fairAcceptedWordWeight_recording {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q × Bool) (F : Finset Q) {n : ℕ} (w : Bits n) :
    fairAcceptedWordWeight (recordingStep δ) s (recordedAccepting F) w =
      fairAcceptedWordWeight δ s.1 F w := by
  simp only [fairAcceptedWordWeight, mem_recordedAccepting, wordEnd_recording_fst]

theorem recorded_kernel_word_acceptance {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q × Bool) (F : Finset Q) (n : ℕ) :
    kernelSetMass (recordedFairKernel (fun q b => some (δ q b))) (recordedAccepting F) n s =
      kernelSetMass (fairWordKernel δ) F n s.1 := by
  rw [← fairWordKernel_recording, ← fairAcceptedWordWeight_sum, ← fairAcceptedWordWeight_sum]
  simp only [fairAcceptedWordWeight_recording]

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_WeightConditioning
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def eventRestriction {Q : Type} [DecidableEq Q] (w : Q → ℝ) (G : Finset Q) : Q → ℝ :=
  fun x => if x ∈ G then w x else 0



theorem eventRestriction_sum {Q : Type} [Fintype Q] [DecidableEq Q]
    (w : Q → ℝ) (G : Finset Q) : (∑ x, eventRestriction w G x) = ∑ x ∈ G, w x := by
  simp [eventRestriction]

theorem normalize_eventRestriction {Q : Type} [Fintype Q] [DecidableEq Q]
    (w : Q → ℝ) (G : Finset Q) (x : Q) :
    normalizeWeights (eventRestriction w G) x = if x ∈ G then w x / (∑ y ∈ G, w y) else 0 := by
  simp [normalizeWeights, eventRestriction, ite_div]

theorem eventRestriction_normalize_twice {Q : Type} [Fintype Q] [DecidableEq Q]
    (w : Q → ℝ) (hZ : 0 < ∑ x, w x) (G : Finset Q) :
    normalizeWeights (eventRestriction (normalizeWeights w) G) = normalizeWeights (eventRestriction w G) := by
  have he : eventRestriction (normalizeWeights w) G =
      fun x => (1 / ∑ y, w y) * eventRestriction w G x := by
    funext x
    simp only [eventRestriction, normalizeWeights]
    split_ifs <;> ring
  rw [he]
  exact normalizeWeights_scale _ _ (by positivity)

/-- Conditioning a normalized nonnegative weight law on G costs exactly
the discarded unnormalized mass divided by the original total mass. -/
theorem tv_normalized_event_restriction {Q : Type} [Fintype Q] [DecidableEq Q]
    (w : Q → ℝ) (hw : ∀ x, 0 ≤ w x) (hZ : 0 < ∑ x, w x) (G : Finset Q)
    (hG : 0 < ∑ x ∈ G, w x) :
    tv (normalizeWeights w) (normalizeWeights (eventRestriction w G)) =
      (∑ x ∈ Gᶜ, w x) / (∑ x, w x) := by
  classical
  have hG' : 0 < ∑ x ∈ G, normalizeWeights w x := by
    simp only [normalizeWeights, ← Finset.sum_div]
    exact div_pos hG hZ
  have h := tv_conditioning (normalizeWeights w) (normalizeWeights_nonneg w hw)
    (normalizeWeights_sum w hZ) G hG'
  have he : (fun x => if x ∈ G then normalizeWeights w x / (∑ y ∈ G, normalizeWeights w y) else 0) =
      normalizeWeights (eventRestriction w G) := by
    rw [← eventRestriction_normalize_twice w hZ G]
    funext x
    exact (normalize_eventRestriction (normalizeWeights w) G x).symm
  rw [he] at h
  rw [h]
  simp only [normalizeWeights]
  have ht (x : Q) : (if x ∈ G then 0 else w x / (∑ y, w y)) =
      (if x ∈ Gᶜ then w x else 0) / (∑ y, w y) := by
    by_cases hx : x ∈ G <;> simp [hx]
  simp_rw [ht]
  rw [← Finset.sum_div]
  congr 1
  simpa only [Finset.univ_inter] using Finset.sum_ite_mem Finset.univ Gᶜ w

theorem event_restriction_bound {Q : Type} [Fintype Q] [DecidableEq Q]
    (w : Q → ℝ) (hw : ∀ x, 0 ≤ w x) (hZ : 0 < ∑ x, w x)
    (G : Finset Q) (δ : ℝ) (hδ : δ < 1)
    (hbad : (∑ x ∈ Gᶜ, w x) ≤ δ * (∑ x, w x)) :
    (0 < ∑ x, eventRestriction w G x) ∧
      tv (normalizeWeights w) (normalizeWeights (eventRestriction w G)) ≤ δ := by
  have hsplit := Finset.sum_add_sum_compl G w
  have hgood : 0 < ∑ x ∈ G, w x := by nlinarith
  refine ⟨by rwa [eventRestriction_sum], ?_⟩
  rw [tv_normalized_event_restriction w hw hZ G hgood]
  exact (div_le_iff₀ hZ).mpr hbad

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_TerminalHittingDecay
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

theorem kernelSetMass_add_compl {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hrows : ∀ x, ∑ y, P x y = 1)
    (A : Finset Q) (n : ℕ) (x : Q) :
    kernelSetMass P A n x + kernelSetMass P Aᶜ n x = 1 := by
  unfold kernelSetMass
  rw [Finset.sum_add_sum_compl]
  exact stochastic_matrix_power_rows P hrows n x

theorem closed_set_compl_mass_zero {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (A : Finset Q) (hclosed : ∀ x ∈ A, ∀ y, 0 < P x y → y ∈ A)
    (n : ℕ) (x : Q) (hx : x ∈ A) : kernelSetMass P Aᶜ n x = 0 := by
  apply Finset.sum_eq_zero
  intro y hy
  exact closed_set_power_zero_outside P hP A hclosed n x y hx (Finset.mem_compl.mp hy)

theorem closed_set_compl_mass_antitone {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1)
    (A : Finset Q) (hclosed : ∀ x ∈ A, ∀ y, 0 < P x y → y ∈ A)
    {m n : ℕ} (hmn : m ≤ n) (x : Q) : kernelSetMass P Aᶜ n x ≤ kernelSetMass P Aᶜ m x := by
  have hh := closed_set_mass_mono P hP hrows A hclosed hmn x
  have hm := kernelSetMass_add_compl P hrows A m x
  have hn := kernelSetMass_add_compl P hrows A n x
  linarith

theorem closed_set_compl_mass_contract {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (A : Finset Q) (hclosed : ∀ x ∈ A, ∀ y, 0 < P x y → y ∈ A)
    (m : ℕ) (ρ : ℝ) (hbound : ∀ x, kernelSetMass P Aᶜ m x ≤ ρ)
    (n : ℕ) (x : Q) : kernelSetMass P Aᶜ (n + m) x ≤ ρ * kernelSetMass P Aᶜ n x := by
  rw [kernelSetMass_add]
  calc
    _ = ∑ z ∈ Aᶜ, (P ^ n) x z * kernelSetMass P Aᶜ m z := by
      symm
      apply Finset.sum_subset (Finset.subset_univ Aᶜ)
      intro z _ hz
      have hz' : z ∈ A := by simpa using hz
      rw [closed_set_compl_mass_zero P hP A hclosed m z hz', mul_zero]
    _ ≤ ∑ z ∈ Aᶜ, (P ^ n) x z * ρ := Finset.sum_le_sum
      (fun z _ => mul_le_mul_of_nonneg_left (hbound z) (Matrix.pow_apply_nonneg hP n x z))
    _ = _ := by rw [← Finset.sum_mul, mul_comm]; rfl

theorem closed_set_compl_mass_geometric {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1)
    (A : Finset Q) (hclosed : ∀ x ∈ A, ∀ y, 0 < P x y → y ∈ A)
    (m : ℕ) (hm : 0 < m) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hbound : ∀ x, kernelSetMass P Aᶜ m x ≤ ρ) (n : ℕ) (x : Q) :
    kernelSetMass P Aᶜ n x ≤ ρ ^ (n / m) := by
  have hblocks : ∀ k : ℕ, kernelSetMass P Aᶜ (k * m) x ≤ ρ ^ k := by
    intro k
    induction k with
    | zero => simpa using kernelSetMass_le_one P hP hrows Aᶜ 0 x
    | succ k ih =>
      rw [Nat.succ_mul]
      calc
        _ ≤ ρ * kernelSetMass P Aᶜ (k * m) x :=
          closed_set_compl_mass_contract P hP A hclosed m ρ hbound (k * m) x
        _ ≤ ρ * ρ ^ k := mul_le_mul_of_nonneg_left ih hρ
        _ = ρ ^ (k + 1) := (pow_succ' ρ k).symm
  exact (closed_set_compl_mass_antitone P hP hrows A hclosed (Nat.div_mul_le_self n m) x).trans
    (hblocks (n / m))

def graphTerminalSet {Q : Type} [Fintype Q] (P : Matrix Q Q ℝ) : Finset Q := by
  classical
  exact Finset.univ.filter (IsGraphTerminal (fun x y => 0 < P x y))

theorem mem_graphTerminalSet {Q : Type} [Fintype Q] (P : Matrix Q Q ℝ) (x : Q) :
    x ∈ graphTerminalSet P ↔ IsGraphTerminal (fun i j => 0 < P i j) x := by
  classical
  simp [graphTerminalSet]

theorem graphTerminalSet_closed {Q : Type} [Fintype Q] (P : Matrix Q Q ℝ)
    (x : Q) (hx : x ∈ graphTerminalSet P) (y : Q) (hxy : 0 < P x y) : y ∈ graphTerminalSet P :=
  (mem_graphTerminalSet P y).mpr
    (graphTerminal_of_reachable _ ((mem_graphTerminalSet P x).mp hx) (.single hxy))

theorem graphTerminalSet_reachable {Q : Type} [Fintype Q] (P : Matrix Q Q ℝ) (x : Q) :
    ∃ y ∈ graphTerminalSet P, Relation.ReflTransGen (fun i j => 0 < P i j) x y := by
  obtain ⟨y, hxy, hy⟩ := exists_reachable_graphTerminal (fun i j => 0 < P i j) x
  exact ⟨y, (mem_graphTerminalSet P y).mpr hy, hxy⟩

/-- Uniform exponential escape from transient states, for every start
and every time. It is derived from finite reachability and stochasticity. -/
theorem terminal_hitting_geometric_decay {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1) :
    ∃ m : ℕ, ∃ ρ : ℝ, 0 < m ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ n x, kernelSetMass P (graphTerminalSet P)ᶜ n x ≤ ρ ^ (n / m) := by
  classical
  obtain ⟨m, η, hm, hη, hη1, hhit⟩ := closed_set_uniform_hitting P hP hrows
    (graphTerminalSet P) (graphTerminalSet_closed P) (graphTerminalSet_reachable P)
  refine ⟨m, 1 - η, hm, by linarith, by linarith, ?_⟩
  intro n x
  apply closed_set_compl_mass_geometric P hP hrows (graphTerminalSet P) (graphTerminalSet_closed P)
    m hm (1 - η) (by linarith) _ n x
  intro y
  have he := kernelSetMass_add_compl P hrows (graphTerminalSet P) m y
  linarith [hhit y]

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_GeometricAccuracyCutoff
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

/-- A fixed geometric error coefficient can be reduced to epsilon/16
with a positive number of blocks logarithmic in inverse accuracy. -/
theorem geometric_accuracy_cutoff {C ρ : ℝ} (hC : 0 < C) (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ K * logInv ε ∧ C * ρ ^ k ≤ ε / 16 := by
  obtain ⟨A, B, hA, hB, hcut⟩ := logarithmic_geometric_block hρ hρ1 hC 1 0 (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2 * A * Real.log 2 + B, by positivity, ?_⟩
  intro ε hε hεle
  obtain ⟨k, _, _, hk, hsmall, hsize⟩ := hcut 0 (ε / 2) (by positivity) (by linarith)
  refine ⟨k, hk, ?_, by norm_num at hsmall; linarith⟩
  have hlog : Real.log (((0 + 1 : ℕ) : ℝ) / (ε / 2)) = (logInv ε + 1) * Real.log 2 := by
    rw [← logInv_half hε]
    simp only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add, logInv]
    field_simp
  rw [hlog] at hsize
  have hge := logInv_ge_one hε hεle
  have hh := mul_le_mul_of_nonneg_left hge (show 0 ≤ A * Real.log 2 + B by positivity)
  nlinarith

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_WordHeadConditioning
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

def wordHeadEvent {Q : Type} [DecidableEq Q] (δ : Q → Bool → Q) (s : Q)
    (T N : ℕ) (G : Finset Q) : Finset (Bits (T + N)) :=
  Finset.univ.filter (fun w => wordEnd δ s (seedPairEquiv T N w).1 ∈ G)

theorem mem_wordHeadEvent {Q : Type} [DecidableEq Q] (δ : Q → Bool → Q) (s : Q)
    (T N : ℕ) (G : Finset Q) (w : Bits (T + N)) :
    w ∈ wordHeadEvent δ s T N G ↔ wordEnd δ s (seedPairEquiv T N w).1 ∈ G := by
  simp [wordHeadEvent]

theorem wordHeadEvent_compl {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (T N : ℕ) (G : Finset Q) :
    (wordHeadEvent δ s T N G)ᶜ = wordHeadEvent δ s T N Gᶜ := by
  ext w
  simp [mem_wordHeadEvent]

/-- The accepted full-word mass factors at the head boundary. The
suffix remains acceptance-conditioned; it has not been made uniform. -/
theorem accepted_word_head_mass {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F G : Finset Q) (T N : ℕ) :
    (∑ w : Bits (T + N), eventRestriction (fairAcceptedWordWeight δ s F)
      (wordHeadEvent δ s T N G) w) =
      ∑ h : Bits T, if wordEnd δ s h ∈ G then
        (1 / (2 : ℝ) ^ T) * kernelSetMass (fairWordKernel δ) F N (wordEnd δ s h) else 0 := by
  classical
  rw [← (seedPairEquiv T N).symm.sum_comp]
  simp only [Fintype.sum_prod_type, eventRestriction, mem_wordHeadEvent,
    Equiv.apply_symm_apply]
  change (∑ h : Bits T, ∑ v : Bits N, if wordEnd δ s h ∈ G then
    fairAcceptedWordWeight δ s F (Fin.append h v) else 0) = _
  simp_rw [fairAcceptedWordWeight_append]
  apply Finset.sum_congr rfl
  intro h _
  by_cases hg : wordEnd δ s h ∈ G
  · simp only [if_pos hg, ← Finset.mul_sum, fairAcceptedWordWeight_sum]
  · simp [hg]

theorem accepted_word_head_mass_le {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F G : Finset Q) (T N : ℕ) :
    (∑ w : Bits (T + N), eventRestriction (fairAcceptedWordWeight δ s F)
      (wordHeadEvent δ s T N G) w) ≤ kernelSetMass (fairWordKernel δ) G T s := by
  rw [accepted_word_head_mass, ← fairAcceptedWordWeight_sum δ s G T]
  apply Finset.sum_le_sum
  intro h _
  by_cases hg : wordEnd δ s h ∈ G
  · simp only [if_pos hg, fairAcceptedWordWeight]
    exact mul_le_of_le_one_right (by positivity)
      (kernelSetMass_le_one (fairWordKernel δ) (uniformStepKernel_nonneg δ)
        (uniformStepKernel_row_sum δ) F N (wordEnd δ s h))
  · simp [hg, fairAcceptedWordWeight]

theorem accepted_word_head_restriction_tv {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F G : Finset Q) (T N : ℕ)
    (c η : ℝ) (hc : 0 < c) (hη : 0 ≤ η) (hη1 : η < 1)
    (hacc : c ≤ kernelSetMass (fairWordKernel δ) F (T + N) s)
    (hbad : kernelSetMass (fairWordKernel δ) Gᶜ T s ≤ η * c) :
    (0 < ∑ w : Bits (T + N), eventRestriction (fairAcceptedWordWeight δ s F)
      (wordHeadEvent δ s T N G) w) ∧
      tv (normalizeWeights (fairAcceptedWordWeight δ s F))
        (normalizeWeights (eventRestriction (fairAcceptedWordWeight δ s F)
          (wordHeadEvent δ s T N G))) ≤ η := by
  apply event_restriction_bound _ (fairAcceptedWordWeight_nonneg δ s F)
    (by rw [fairAcceptedWordWeight_sum]; exact hc.trans_le hacc) _ η hη1
  rw [← eventRestriction_sum, wordHeadEvent_compl, fairAcceptedWordWeight_sum]
  exact (accepted_word_head_mass_le δ s F Gᶜ T N).trans
    (hbad.trans (mul_le_mul_of_nonneg_left hacc hη))

/-- Actual word-law version of the logarithmic terminal head cutoff. -/
theorem terminal_word_head_logarithmic_restriction {Q : Type} [Fintype Q]
    [DecidableEq Q] [Nonempty Q] (δ : Q → Bool → Q) (c : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ T : ℕ, 0 < T ∧ (T : ℝ) ≤ K * logInv ε ∧
        ∀ (s : Q) (F : Finset Q) (N : ℕ), c ≤ kernelSetMass (fairWordKernel δ) F (T + N) s →
          (0 < ∑ w : Bits (T + N), eventRestriction (fairAcceptedWordWeight δ s F)
            (wordHeadEvent δ s T N (graphTerminalSet (fairWordKernel δ))) w) ∧
          tv (normalizeWeights (fairAcceptedWordWeight δ s F))
            (normalizeWeights (eventRestriction (fairAcceptedWordWeight δ s F)
              (wordHeadEvent δ s T N (graphTerminalSet (fairWordKernel δ))))) ≤ ε / 4 := by
  obtain ⟨m, ρ, hm, hρ, hρ1, hdecay⟩ := terminal_hitting_geometric_decay
    (fairWordKernel δ) (uniformStepKernel_nonneg δ) (uniformStepKernel_row_sum δ)
  obtain ⟨K, hK, hcut⟩ := geometric_accuracy_cutoff (one_div_pos.mpr hc) hρ hρ1
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  refine ⟨m * K, mul_pos hm' hK, ?_⟩
  intro ε hε hεle
  obtain ⟨k, hk, hlen, hsmall⟩ := hcut ε hε hεle
  refine ⟨m * k, Nat.mul_pos hm hk, ?_, ?_⟩
  · push_cast
    nlinarith [mul_le_mul_of_nonneg_left hlen hm'.le]
  · intro s F N hacc
    apply accepted_word_head_restriction_tv δ s F _ (m * k) N c (ε / 4) hc
      (by positivity) (by linarith) hacc
    have hpow : ρ ^ k ≤ (ε / 16) * c := by
      apply (div_le_iff₀ hc).mp
      simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using hsmall
    calc
      _ ≤ ρ ^ ((m * k) / m) := hdecay (m * k) s
      _ = ρ ^ k := by rw [Nat.mul_div_cancel_left k hm]
      _ ≤ (ε / 16) * c := hpow
      _ ≤ (ε / 4) * c := by nlinarith

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_HeadMiddleTailLaw
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def headContinuation {H U V : Type} [Fintype U] [Fintype V]
    (K : H → U → ℝ) (b : H → U → V → ℝ) (h : H) : ℝ :=
  ∑ u, K h u * ∑ v, b h u v

def headMiddleTailWeight {H U V : Type}
    (a : H → ℝ) (K : H → U → ℝ) (b : H → U → V → ℝ) (x : H × (U × V)) : ℝ :=
  a x.1 * K x.1 x.2.1 * b x.1 x.2.1 x.2.2

def headMiddleTailIdeal {H U V : Type} [Fintype H] [Fintype U] [Fintype V]
    (a : H → ℝ) (K : H → U → ℝ) (b : H → U → V → ℝ) (x : H × (U × V)) : ℝ :=
  normalizeWeights (fun h => a h * headContinuation K b h) x.1 * K x.1 x.2.1 *
    normalizeWeights (b x.1 x.2.1) x.2.2

theorem headContinuation_nonneg {H U V : Type} [Fintype U] [Fintype V]
    (K : H → U → ℝ) (b : H → U → V → ℝ)
    (hK : ∀ h u, 0 ≤ K h u) (hb : ∀ h u v, 0 ≤ b h u v) (h : H) :
    0 ≤ headContinuation K b h :=
  Finset.sum_nonneg (fun u _ => mul_nonneg (hK h u) (Finset.sum_nonneg (fun v _ => hb h u v)))

theorem headMiddleTailWeight_nonneg {H U V : Type}
    (a : H → ℝ) (K : H → U → ℝ) (b : H → U → V → ℝ)
    (ha : ∀ h, 0 ≤ a h) (hK : ∀ h u, 0 ≤ K h u) (hb : ∀ h u v, 0 ≤ b h u v)
    (x : H × (U × V)) : 0 ≤ headMiddleTailWeight a K b x :=
  mul_nonneg (mul_nonneg (ha x.1) (hK x.1 x.2.1)) (hb x.1 x.2.1 x.2.2)

theorem headMiddleTailWeight_sum {H U V : Type} [Fintype H] [Fintype U] [Fintype V]
    (a : H → ℝ) (K : H → U → ℝ) (b : H → U → V → ℝ) :
    (∑ x : H × (U × V), headMiddleTailWeight a K b x) =
      ∑ h, a h * headContinuation K b h := by
  simp only [Fintype.sum_prod_type, headMiddleTailWeight, headContinuation, Finset.mul_sum, mul_assoc]





/-- Exact likelihood identity on the complete triple, including zero
weights. The same continuation/tail ratio as in the source appears. -/
theorem headMiddleTailIdeal_ratio {H U V : Type} [Fintype H] [Fintype U] [Fintype V]
    (a : H → ℝ) (K : H → U → ℝ) (b : H → U → V → ℝ) (x : H × (U × V)) :
    headMiddleTailIdeal a K b x = normalizeWeights (headMiddleTailWeight a K b) x *
      (headContinuation K b x.1 / (∑ v, b x.1 x.2.1 v)) := by
  simp only [headMiddleTailIdeal, normalizeWeights]
  rw [headMiddleTailWeight_sum]
  simp only [headMiddleTailWeight]
  ring



theorem headMiddleTailIdeal_tv {H U V : Type} [Fintype H] [Fintype U] [Fintype V]
    (a : H → ℝ) (K : H → U → ℝ) (b : H → U → V → ℝ)
    (ha : ∀ h, 0 ≤ a h) (hK : ∀ h u, 0 ≤ K h u) (hb : ∀ h u v, 0 ≤ b h u v)
    (hZ : 0 < ∑ h, a h * headContinuation K b h) (δ : ℝ)
    (herr : ∀ h u, |headContinuation K b h / (∑ v, b h u v) - 1| ≤ δ) :
    tv (headMiddleTailIdeal a K b) (normalizeWeights (headMiddleTailWeight a K b)) ≤ δ / 2 := by
  let p := normalizeWeights (headMiddleTailWeight a K b)
  have hp : ∀ x, 0 ≤ p x := normalizeWeights_nonneg _ (headMiddleTailWeight_nonneg a K b ha hK hb)
  have hsum : ∑ x, p x = 1 := normalizeWeights_sum _ (by rwa [headMiddleTailWeight_sum])
  have hpoint (x : H × (U × V)) : |headMiddleTailIdeal a K b x - p x| ≤ δ * p x := by
    rw [headMiddleTailIdeal_ratio]
    change |p x * (headContinuation K b x.1 / (∑ v, b x.1 x.2.1 v)) - p x| ≤ _
    rw [← mul_sub_one, abs_mul, abs_of_nonneg (hp x)]
    exact (mul_le_mul_of_nonneg_left (herr x.1 x.2.1) (hp x)).trans_eq (mul_comm _ _)
  calc
    _ ≤ (∑ x, δ * p x) / 2 := div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => hpoint x)) (by norm_num)
    _ = δ / 2 := by rw [← Finset.mul_sum, hsum, mul_one]

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_HeadMiddleTailPerturbation
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def headMiddleTailRounded {H U V : Type}
    (q : H → ℝ) (K : H → U → ℝ) (L : H → U → V → ℝ) (x : H × (U × V)) : ℝ :=
  q x.1 * K x.1 x.2.1 * L x.1 x.2.1 x.2.2

theorem headMiddleTailRounded_nonneg {H U V : Type}
    (q : H → ℝ) (K : H → U → ℝ) (L : H → U → V → ℝ)
    (hq : ∀ h, 0 ≤ q h) (hK : ∀ h u, 0 ≤ K h u) (hL : ∀ h u v, 0 ≤ L h u v)
    (x : H × (U × V)) : 0 ≤ headMiddleTailRounded q K L x :=
  mul_nonneg (mul_nonneg (hq x.1) (hK x.1 x.2.1)) (hL x.1 x.2.1 x.2.2)



/-- Head and tail rounding errors add while the middle law is retained
exactly. The comparison is on the full triple, not only its marginals. -/
theorem headMiddleTailRounded_tv_ideal {H U V : Type} [Fintype H] [Fintype U] [Fintype V]
    (a q : H → ℝ) (K : H → U → ℝ) (b L : H → U → V → ℝ)
    (ha : ∀ h, 0 ≤ a h) (hK : ∀ h u, 0 ≤ K h u) (hb : ∀ h u v, 0 ≤ b h u v)
    (hZ : 0 < ∑ h, a h * headContinuation K b h)
    (hKsum : ∀ h, ∑ u, K h u = 1)
    (hL : ∀ h u v, 0 ≤ L h u v) (hLsum : ∀ h u, ∑ v, L h u v = 1)
    (δ η : ℝ)
    (hhead : tv q (normalizeWeights (fun h => a h * headContinuation K b h)) ≤ δ)
    (htail : ∀ h u, tv (L h u) (normalizeWeights (b h u)) ≤ η) :
    tv (headMiddleTailRounded q K L) (headMiddleTailIdeal a K b) ≤ δ + η := by
  let p := normalizeWeights (fun h => a h * headContinuation K b h)
  let U₁ := fun h (x : U × V) => K h x.1 * L h x.1 x.2
  let U₂ := fun h (x : U × V) => K h x.1 * normalizeWeights (b h x.1) x.2
  have hp : ∀ h, 0 ≤ p h := normalizeWeights_nonneg _
    (fun h => mul_nonneg (ha h) (headContinuation_nonneg K b hK hb h))
  have hpsum : ∑ h, p h = 1 := normalizeWeights_sum _ hZ
  have hU₁ : ∀ h x, 0 ≤ U₁ h x := fun h x => mul_nonneg (hK h x.1) (hL h x.1 x.2)
  have hU₁sum : ∀ h, ∑ x, U₁ h x = 1 := by
    intro h
    simp only [U₁, Fintype.sum_prod_type, ← Finset.mul_sum, hLsum, mul_one]
    exact hKsum h
  have hlocal (h : H) : tv (U₁ h) (U₂ h) ≤ η := by
    have hh := tv_joint_le (K h) (K h) (L h) (fun u => normalizeWeights (b h u))
      (hK h) (hL h) (hLsum h)
    have hz : tv (K h) (K h) = 0 := by simp [tv]
    rw [hz, zero_add] at hh
    calc
      _ ≤ ∑ u, K h u * tv (L h u) (normalizeWeights (b h u)) := hh
      _ ≤ ∑ u, K h u * η := Finset.sum_le_sum
        (fun u _ => mul_le_mul_of_nonneg_left (htail h u) (hK h u))
      _ = η := by rw [← Finset.sum_mul, hKsum, one_mul]
  have hh := tv_joint_le q p U₁ U₂ hp hU₁ hU₁sum
  have hsum : (∑ h, p h * tv (U₁ h) (U₂ h)) ≤ η := by
    calc
      _ ≤ ∑ h, p h * η := Finset.sum_le_sum
        (fun h _ => mul_le_mul_of_nonneg_left (hlocal h) (hp h))
      _ = η := by rw [← Finset.sum_mul, hpsum, one_mul]
  have hbnd := hh.trans (add_le_add hhead hsum)
  change tv (fun z : H × (U × V) => q z.1 * K z.1 z.2.1 * L z.1 z.2.1 z.2.2)
    (fun z => p z.1 * K z.1 z.2.1 * normalizeWeights (b z.1 z.2.1) z.2.2) ≤ δ + η
  simpa only [U₁, U₂, mul_assoc] using hbnd

theorem headMiddleTailRounded_tv_target {H U V : Type} [Fintype H] [Fintype U] [Fintype V]
    (a q : H → ℝ) (K : H → U → ℝ) (b L : H → U → V → ℝ)
    (ha : ∀ h, 0 ≤ a h) (hK : ∀ h u, 0 ≤ K h u) (hb : ∀ h u v, 0 ≤ b h u v)
    (hZ : 0 < ∑ h, a h * headContinuation K b h)
    (hKsum : ∀ h, ∑ u, K h u = 1)
    (hL : ∀ h u v, 0 ≤ L h u v) (hLsum : ∀ h u, ∑ v, L h u v = 1)
    (δ η θ : ℝ)
    (hhead : tv q (normalizeWeights (fun h => a h * headContinuation K b h)) ≤ δ)
    (htail : ∀ h u, tv (L h u) (normalizeWeights (b h u)) ≤ η)
    (hratio : ∀ h u, |headContinuation K b h / (∑ v, b h u v) - 1| ≤ θ) :
    tv (headMiddleTailRounded q K L) (normalizeWeights (headMiddleTailWeight a K b)) ≤ δ + η + θ / 2 :=
  (tv_triangle _ (headMiddleTailIdeal a K b) _).trans (add_le_add
    (headMiddleTailRounded_tv_ideal a q K b L ha hK hb hZ hKsum hL hLsum δ η hhead htail)
    (headMiddleTailIdeal_tv a K b ha hK hb hZ θ hratio))



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_WordTripleWeights
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

def wordTripleEquiv (T M R : ℕ) : Bits (T + (M + R)) ≃ Bits T × (Bits M × Bits R) :=
  (seedPairEquiv T (M + R)).trans (Equiv.prodCongr (Equiv.refl _) (seedPairEquiv M R))



def terminalWordHeads {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T N : ℕ) : Finset (Bits T) := by
  classical
  exact Finset.univ.filter (fun h => wordEnd δ s h ∈ graphTerminalSet (fairWordKernel δ) ∧
    0 < kernelSetMass (fairWordKernel δ) F N (wordEnd δ s h))

abbrev TerminalWordHead {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T N : ℕ) :=
  {h : Bits T // h ∈ terminalWordHeads δ s F T N}

theorem mem_terminalWordHeads {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T N : ℕ) (h : Bits T) :
    h ∈ terminalWordHeads δ s F T N ↔
      wordEnd δ s h ∈ graphTerminalSet (fairWordKernel δ) ∧
        0 < kernelSetMass (fairWordKernel δ) F N (wordEnd δ s h) := by
  classical
  simp [terminalWordHeads]

def terminalWordConcat {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T M R : ℕ)
    (x : TerminalWordHead δ s F T (M + R) × (Bits M × Bits R)) : Bits (T + (M + R)) :=
  (wordTripleEquiv T M R).symm (x.1.val, x.2)

theorem terminalWordConcat_injective {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T M R : ℕ) :
    Function.Injective (terminalWordConcat δ s F T M R) := by
  intro x y h
  have he := (wordTripleEquiv T M R).symm.injective h
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst he)
  · exact congrArg (fun z : Bits T × (Bits M × Bits R) => z.2) he

def terminalWordTailWeight {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T M R : ℕ)
    (h : TerminalWordHead δ s F T (M + R)) (u : Bits M) (v : Bits R) : ℝ :=
  fairAcceptedWordWeight δ (wordEnd δ (wordEnd δ s h.val) u) F v

def terminalWordTripleWeight {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T M R : ℕ) :=
  headMiddleTailWeight (fun _ : TerminalWordHead δ s F T (M + R) => 1 / (2 : ℝ) ^ T)
    (fun _ (_ : Bits M) => 1 / (2 : ℝ) ^ M) (terminalWordTailWeight δ s F T M R)

def terminalRestrictedWordWeight {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T N : ℕ) : Bits (T + N) → ℝ :=
  eventRestriction (fairAcceptedWordWeight δ s F)
    (wordHeadEvent δ s T N (graphTerminalSet (fairWordKernel δ)))

theorem terminalRestrictedWordWeight_concat {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T M R : ℕ)
    (x : TerminalWordHead δ s F T (M + R) × (Bits M × Bits R)) :
    terminalRestrictedWordWeight δ s F T (M + R) (terminalWordConcat δ s F T M R x) =
      terminalWordTripleWeight δ s F T M R x := by
  have hh := ((mem_terminalWordHeads δ s F T (M + R) x.1.val).mp x.1.property).1
  have he : (seedPairEquiv T (M + R) (terminalWordConcat δ s F T M R x)).1 = x.1.val := by
    exact congrArg Prod.fst ((seedPairEquiv T (M + R)).apply_symm_apply
      (x.1.val, (seedPairEquiv M R).symm x.2))
  unfold terminalRestrictedWordWeight eventRestriction
  rw [if_pos ((mem_wordHeadEvent _ _ _ _ _ _).mpr (by rwa [he]))]
  change fairAcceptedWordWeight δ s F (Fin.append x.1.val (Fin.append x.2.1 x.2.2)) = _
  rw [fairAcceptedWordWeight_append, fairAcceptedWordWeight_append]
  simp only [terminalWordTripleWeight, headMiddleTailWeight, terminalWordTailWeight, mul_assoc]

/-- Removing heads with zero continuation removes no accepted full word. -/
theorem terminalRestrictedWordWeight_supported {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T M R : ℕ)
    (w : Bits (T + (M + R)))
    (hout : ¬ ∃ x, terminalWordConcat δ s F T M R x = w) :
    terminalRestrictedWordWeight δ s F T (M + R) w = 0 := by
  classical
  let z := wordTripleEquiv T M R w
  have hw : Fin.append z.1 (Fin.append z.2.1 z.2.2) = w :=
    (wordTripleEquiv T M R).symm_apply_apply w
  have hsplit : (seedPairEquiv T (M + R) w).1 = z.1 := rfl
  by_cases ht : wordEnd δ s z.1 ∈ graphTerminalSet (fairWordKernel δ)
  · by_cases ha : wordEnd δ (wordEnd δ s z.1) (Fin.append z.2.1 z.2.2) ∈ F
    · have hpos : 0 < kernelSetMass (fairWordKernel δ) F (M + R) (wordEnd δ s z.1) := by
        rw [← fairAcceptedWordWeight_sum]
        exact ((fairAcceptedWordWeight_pos_iff _ _ _ _).mpr ha).trans_le
          (Finset.single_le_sum (fun v _ => fairAcceptedWordWeight_nonneg δ _ F v)
            (Finset.mem_univ (Fin.append z.2.1 z.2.2)))
      let h : TerminalWordHead δ s F T (M + R) :=
        ⟨z.1, (mem_terminalWordHeads δ s F T (M + R) z.1).mpr ⟨ht, hpos⟩⟩
      exact False.elim (hout ⟨(h, z.2), hw⟩)
    · have hacc : fairAcceptedWordWeight δ s F w = 0 := by
        rw [← hw, fairAcceptedWordWeight, wordEnd_append, if_neg ha]
      simp only [terminalRestrictedWordWeight, eventRestriction, hacc, ite_self]
  · have hn : w ∉ wordHeadEvent δ s T (M + R) (graphTerminalSet (fairWordKernel δ)) := by
      simpa only [mem_wordHeadEvent, hsplit] using ht
    exact if_neg hn

theorem terminalWordTripleWeight_sum {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T M R : ℕ) :
    (∑ x, terminalWordTripleWeight δ s F T M R x) =
      ∑ w, terminalRestrictedWordWeight δ s F T (M + R) w := by
  simp_rw [← terminalRestrictedWordWeight_concat]
  exact embedded_weight_sum _ (terminalWordConcat_injective δ s F T M R) _
    (terminalRestrictedWordWeight_supported δ s F T M R)

/-- Concatenation transports the normalized triple target to exactly the
full accepted word law conditioned on a terminal head endpoint. -/
theorem terminalWordTripleWeight_normalized {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T M R : ℕ) (w : Bits (T + (M + R))) :
    (∑ x, if terminalWordConcat δ s F T M R x = w then
      normalizeWeights (terminalWordTripleWeight δ s F T M R) x else 0) =
      normalizeWeights (terminalRestrictedWordWeight δ s F T (M + R)) w := by
  have he : (fun x => terminalRestrictedWordWeight δ s F T (M + R)
      (terminalWordConcat δ s F T M R x)) = terminalWordTripleWeight δ s F T M R :=
    funext (terminalRestrictedWordWeight_concat δ s F T M R)
  simpa only [he] using embedded_normalized_weights _
    (terminalWordConcat_injective δ s F T M R) _
    (terminalRestrictedWordWeight_supported δ s F T M R) w

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_CommonTerminalPeriod
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

/-- One idempotent support power of the full chain works in every
terminal SCC, allowing all acceptance residues to use one common period. -/
theorem terminal_scc_mixing_at_idempotent_power {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1)
    (p : ℕ) (hid : ∀ x y, (∃ z, 0 < (P ^ p) x z ∧ 0 < (P ^ p) z y) ↔ 0 < (P ^ p) x y)
    (s : Q) (hs : IsGraphTerminal (fun i j => 0 < P i j) s) :
    Equivalence (fun x y => 0 < (sccMatrix P s ^ p) x y) ∧
      ∀ t : SCCState P s,
        ∃ (ν : PositiveSupportClass (sccMatrix P s ^ p) t → ℝ) (C ρ : ℝ),
          (∀ x, 0 < ν x) ∧ (∑ x, ν x = 1) ∧ 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
          ∀ n x y, |(supportClassMatrix (sccMatrix P s ^ p) t ^ n) x y / ν y - 1| ≤ C * ρ ^ n := by
  classical
  obtain ⟨π, hπ, _, hstat⟩ := terminal_scc_stationary P hP hrows s hs
  have hr : ∀ x, ∑ y, sccMatrix P s x y = 1 :=
    fun x => (terminal_scc_row_sum P hP s hs x).trans (hrows x.val)
  have hp : ∀ x y, 0 ≤ (sccMatrix P s ^ p) x y :=
    Matrix.pow_apply_nonneg (fun x y : SCCState P s => hP x.val y.val) p
  have htrans : ∀ x y z : SCCState P s, 0 < (sccMatrix P s ^ p) x y →
      0 < (sccMatrix P s ^ p) y z → 0 < (sccMatrix P s ^ p) x z := by
    intro x y z hxy hyz
    rw [sccMatrix_power P hP] at hxy hyz ⊢
    exact (hid x.val z.val).mp ⟨y.val, hxy, hyz⟩
  have he := stationary_transitive_support_equivalence (fun x y => (sccMatrix P s ^ p) x y)
    hp (stochastic_matrix_power_rows (sccMatrix P s) hr p) π hπ
    (stationary_matrix_power (sccMatrix P s) π hstat p) htrans
  refine ⟨he, ?_⟩
  intro t
  letI : Nonempty (PositiveSupportClass (sccMatrix P s ^ p) t) := ⟨⟨t, he.refl t⟩⟩
  exact positive_matrix_relative_mixing (supportClassMatrix (sccMatrix P s ^ p) t)
    (supportClassMatrix_pos _ he t)
    (supportClassMatrix_rows _ hp (stochastic_matrix_power_rows _ hr p) he t)



/-- Along the common period a terminal accepting endpoint can be revisited
with probability bounded away from zero for every sufficiently long block. -/
theorem terminal_periodic_return_lower_bound {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1)
    (p : ℕ) (hid : ∀ x y, (∃ z, 0 < (P ^ p) x z ∧ 0 < (P ^ p) z y) ↔ 0 < (P ^ p) x y)
    (s : Q) (hs : IsGraphTerminal (fun i j => 0 < P i j) s) :
    ∃ c : ℝ, ∃ J : ℕ, 0 < c ∧ ∀ j, J ≤ j → c ≤ (P ^ (p * j)) s s := by
  classical
  obtain ⟨he, hmix⟩ := terminal_scc_mixing_at_idempotent_power P hP hrows p hid s hs
  let t : SCCState P s := ⟨s, rfl⟩
  let u : PositiveSupportClass (sccMatrix P s ^ p) t := ⟨t, he.refl t⟩
  obtain ⟨ν, C, ρ, hν, _, hC, hρ, hρ1, hbound⟩ := hmix t
  let J := geometricCutoff ρ (1 / (2 * C))
  have hJ : C * ρ ^ J ≤ 1 / 2 := by
    have hh := geometricCutoff_bound hρ hρ1 (by positivity : 0 < 1 / (2 * C))
    have hh' := mul_le_mul_of_nonneg_left hh hC.le
    have heq : C * (1 / (2 * C)) = 1 / 2 := by field_simp
    rw [heq] at hh'
    exact hh'
  refine ⟨ν u / 2, J, div_pos (hν u) (by norm_num), ?_⟩
  intro j hj
  have herr := hbound j u u
  rw [supportClass_block_power (sccMatrix P s) (fun x y => hP x.val y.val) p he,
    sccMatrix_power P hP] at herr
  change |(P ^ (p * j)) s s / ν u - 1| ≤ C * ρ ^ j at herr
  have hsmall : C * ρ ^ j ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hρ.le hρ1.le hj) hC.le).trans hJ
  have hlo := (abs_le.mp (herr.trans hsmall)).1
  have hratio : 1 / 2 ≤ (P ^ (p * j)) s s / ν u := by linarith
  have := (le_div_iff₀ (hν u)).mp hratio
  linarith

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_PeriodicPhaseCompatibility
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

theorem positive_power_reachable {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (n : ℕ) (s t : Q)
    (hp : 0 < (P ^ n) s t) : Relation.ReflTransGen (fun x y => 0 < P x y) s t := by
  rw [← bridgePartition_eq_matrix_power P n] at hp
  obtain ⟨γ, _, hγ⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun γ _ => bridgeWeight_nonneg P hP s t n γ)).mp hp
  have hg := (bridgeWeight_pos_iff P hP s t n γ).mp hγ
  have hr := graph_path_reaches (fun x y => 0 < P x y) γ hg.2.2 0 (Fin.last n) (Fin.zero_le _)
  simpa only [hg.1, hg.2.1] using hr

/-- Every multiple of the blocked time stays inside the same powered
support class, including the zero-length identity case. -/
theorem powered_support_of_multiple {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : ℕ)
    (he : Equivalence (fun x y => 0 < (P ^ p) x y))
    (k : ℕ) (x y : Q) (hxy : 0 < (P ^ (p * k)) x y) : 0 < (P ^ p) x y := by
  classical
  by_contra hn
  have hz := supportClass_power_no_exit (P ^ p) (Matrix.pow_apply_nonneg hP p) he x k
    ⟨x, he.refl x⟩ y hn
  rw [← pow_mul] at hz
  exact hxy.ne' hz

/-- Equal-length positive paths from one state end in one powered
support class. The proof completes a path to a multiple of p and uses
the reversibility of the support relation, not reversibility of P. -/
theorem same_time_endpoints_same_power_class {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1)
    (p : ℕ) (hp : 0 < p) (he : Equivalence (fun x y => 0 < (P ^ p) x y))
    (M : ℕ) (q s t : Q) (hqs : 0 < (P ^ M) q s) (hqt : 0 < (P ^ M) q t) :
    0 < (P ^ p) s t := by
  let r := M * (p - 1)
  have hsum : 0 < ∑ z, (P ^ r) s z := by rw [stochastic_matrix_power_rows P hrows]; norm_num
  obtain ⟨z, _, hsz⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun z _ => Matrix.pow_apply_nonneg hP r s z)).mp hsum
  have hlen : M + r = p * M := by
    dsimp only [r]
    have hh : p - 1 + 1 = p := Nat.sub_add_cancel (by omega)
    nlinarith
  have hqz := matrix_power_positive_comp P hP M r q s z hqs hsz
  rw [hlen] at hqz
  have hzq := he.symm (powered_support_of_multiple P hP p he M q z hqz)
  have hst := matrix_power_positive_comp P hP (r + p) M s q t
    (matrix_power_positive_comp P hP r p s z q hsz hzq) hqt
  have hlen' : r + p + M = p * (M + 1) := by nlinarith [hlen]
  rw [hlen'] at hst
  exact powered_support_of_multiple P hP p he (M + 1) s t hst

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_RelativeAcceptanceRatio
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- A probability-weighted average retains a common relative error;
only positive-weight indices need satisfy the pointwise estimate. -/
theorem probability_average_relative_error {Q : Type} [Fintype Q]
    (w v : Q → ℝ) (β δ : ℝ) (hw : ∀ x, 0 ≤ w x) (hsum : ∑ x, w x = 1)
    (hv : ∀ x, 0 < w x → |v x / β - 1| ≤ δ) :
    |(∑ x, w x * v x) / β - 1| ≤ δ := by
  have he : (∑ x, w x * (v x / β - 1)) = (∑ x, w x * v x) / β - 1 := by
    simp only [mul_sub, ← mul_div_assoc, mul_one, Finset.sum_sub_distrib, ← Finset.sum_div, hsum]
  rw [← he]
  calc
    _ ≤ ∑ x, |w x * (v x / β - 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, w x * δ := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hp : 0 < w x
      · rw [abs_mul, abs_of_nonneg (hw x)]
        exact mul_le_mul_of_nonneg_left (hv x hp) (hw x)
      · have hz : w x = 0 := le_antisymm (le_of_not_gt hp) (hw x)
        simp [hz]
    _ = δ := by rw [← Finset.sum_mul, hsum, one_mul]

/-- Two numbers close to the same positive reference have a controlled
ratio. The denominator is proved strictly positive as part of the result. -/
theorem relative_ratio_error {x y β δ : ℝ} (hβ : 0 < β) (hδ : 0 ≤ δ) (hδle : δ ≤ 1 / 2)
    (hx : |x / β - 1| ≤ δ) (hy : |y / β - 1| ≤ δ) :
    0 < y ∧ |x / y - 1| ≤ 4 * δ := by
  have hxa : |x - β| ≤ δ * β := by
    rw [div_sub_one hβ.ne', abs_div, abs_of_pos hβ] at hx
    exact (div_le_iff₀ hβ).mp hx
  have hya : |y - β| ≤ δ * β := by
    rw [div_sub_one hβ.ne', abs_div, abs_of_pos hβ] at hy
    exact (div_le_iff₀ hβ).mp hy
  have hyl : β / 2 ≤ y := by
    have hh := (abs_le.mp hya).1
    nlinarith
  have hyp : 0 < y := (half_pos hβ).trans_le hyl
  refine ⟨hyp, ?_⟩
  rw [div_sub_one hyp.ne', abs_div, abs_of_pos hyp]
  apply (div_le_iff₀ hyp).mpr
  have hxy : |x - y| ≤ 2 * δ * β := by
    have hh := abs_sub_le x β y
    rw [abs_sub_comm β y] at hh
    linarith
  exact hxy.trans (by nlinarith)

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_PowerClassAcceptance
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

def powerClassAcceptanceCoefficient {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (p : ℕ) (s : Q)
    (ν : PositiveSupportClass (P ^ p) s → ℝ) (F : Finset Q) : ℝ :=
  ∑ z, if z.val ∈ F then ν z else 0

theorem kernelSetMass_powerClass {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : ℕ)
    (he : Equivalence (fun x y => 0 < (P ^ p) x y)) (s : Q)
    (F : Finset Q) (k : ℕ) (x : PositiveSupportClass (P ^ p) s) :
    kernelSetMass P F (p * k) x.val =
      ∑ z : PositiveSupportClass (P ^ p) s,
        if z.val ∈ F then (supportClassMatrix (P ^ p) s ^ k) x z else 0 := by
  classical
  have hz (y : Q) (hy : ¬ 0 < (P ^ p) s y) :
      (if y ∈ F then (P ^ (p * k)) x.val y else 0) = 0 := by
    have hh := supportClass_power_no_exit (P ^ p) (Matrix.pow_apply_nonneg hP p) he s k x y hy
    rw [← pow_mul] at hh
    simp [hh]
  calc
    _ = ∑ y, if y ∈ F then (P ^ (p * k)) x.val y else 0 := by simp [kernelSetMass]
    _ = ∑ z : PositiveSupportClass (P ^ p) s,
        if z.val ∈ F then (P ^ (p * k)) x.val z.val else 0 :=
      (sum_supportClass_eq (P ^ p) s _ hz).symm
    _ = _ := by simp_rw [supportClass_block_power P hP p he]

theorem powerClassAcceptanceCoefficient_pos_iff {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (p : ℕ) (s : Q)
    (ν : PositiveSupportClass (P ^ p) s → ℝ) (hν : ∀ z, 0 < ν z) (F : Finset Q) :
    0 < powerClassAcceptanceCoefficient P p s ν F ↔
      ∃ z : PositiveSupportClass (P ^ p) s, z.val ∈ F := by
  classical
  unfold powerClassAcceptanceCoefficient
  rw [Finset.sum_pos_iff_of_nonneg (by intro z _; split_ifs <;> simp_all [(hν z).le])]
  simp only [Finset.mem_univ, true_and]
  apply exists_congr
  intro z
  by_cases hz : z.val ∈ F <;> simp [hz, hν z]

theorem powerClassAcceptanceCoefficient_pos_of_mass {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : ℕ)
    (he : Equivalence (fun x y => 0 < (P ^ p) x y)) (s : Q)
    (ν : PositiveSupportClass (P ^ p) s → ℝ) (hν : ∀ z, 0 < ν z)
    (F : Finset Q) (k : ℕ) (x : PositiveSupportClass (P ^ p) s)
    (hmass : 0 < kernelSetMass P F (p * k) x.val) :
    0 < powerClassAcceptanceCoefficient P p s ν F := by
  classical
  apply (powerClassAcceptanceCoefficient_pos_iff P p s ν hν F).mpr
  by_contra hn
  push Not at hn
  rw [kernelSetMass_powerClass P hP p he s F k x] at hmass
  simp [hn] at hmass

theorem powerClass_acceptance_relative_mixing {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (p : ℕ)
    (he : Equivalence (fun x y => 0 < (P ^ p) x y)) (s : Q)
    (ν : PositiveSupportClass (P ^ p) s → ℝ) (hν : ∀ z, 0 < ν z)
    (F : Finset Q) (k : ℕ) (x : PositiveSupportClass (P ^ p) s) (δ : ℝ)
    (hmix : ∀ z, |(supportClassMatrix (P ^ p) s ^ k) x z / ν z - 1| ≤ δ)
    (hβ : 0 < powerClassAcceptanceCoefficient P p s ν F) :
    |kernelSetMass P F (p * k) x.val / powerClassAcceptanceCoefficient P p s ν F - 1| ≤ δ := by
  classical
  have h := weighted_relative_error (fun z => (supportClassMatrix (P ^ p) s ^ k) x z) ν
    (fun z => if z.val ∈ F then 1 else 0) hν (by intro z; split_ifs <;> norm_num) δ hmix
    (by simpa only [mul_ite, mul_one, mul_zero, powerClassAcceptanceCoefficient] using hβ)
  simpa only [mul_ite, mul_one, mul_zero, ← kernelSetMass_powerClass P hP p he,
    powerClassAcceptanceCoefficient] using h

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_PeriodicAcceptanceRatio
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

/-- After a tail of p*k steps, all possible middle endpoints use the
same acceptance coefficient. Averaging the middle law and comparing to
one endpoint costs at most four times the class mixing error. -/
theorem periodic_acceptance_ratio {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1)
    (p : ℕ) (hp : 0 < p) (he : Equivalence (fun x y => 0 < (P ^ p) x y))
    (F : Finset Q) (M k : ℕ) (q s : Q) (hqs : 0 < (P ^ M) q s)
    (ν : PositiveSupportClass (P ^ p) s → ℝ) (hν : ∀ z, 0 < ν z)
    (δ : ℝ) (hδ : 0 ≤ δ) (hδle : δ ≤ 1 / 2)
    (hmix : ∀ x y, |(supportClassMatrix (P ^ p) s ^ k) x y / ν y - 1| ≤ δ)
    (hacc : 0 < kernelSetMass P F (M + p * k) q) :
    0 < kernelSetMass P F (p * k) s ∧
      |kernelSetMass P F (M + p * k) q / kernelSetMass P F (p * k) s - 1| ≤ 4 * δ := by
  classical
  let β := powerClassAcceptanceCoefficient P p s ν F
  have hβ : 0 < β := by
    rw [kernelSetMass_add] at hacc
    obtain ⟨t, _, ht⟩ := (Finset.sum_pos_iff_of_nonneg (fun t _ =>
      mul_nonneg (Matrix.pow_apply_nonneg hP M q t) (kernelSetMass_nonneg P hP F (p * k) t))).mp hacc
    have hqt := pos_of_mul_pos_left ht (kernelSetMass_nonneg P hP F (p * k) t)
    have hmass := pos_of_mul_pos_right ht (Matrix.pow_apply_nonneg hP M q t)
    let u : PositiveSupportClass (P ^ p) s :=
      ⟨t, same_time_endpoints_same_power_class P hP hrows p hp he M q s t hqs hqt⟩
    exact powerClassAcceptanceCoefficient_pos_of_mass P hP p he s ν hν F k u hmass
  have hnum : |kernelSetMass P F (M + p * k) q / β - 1| ≤ δ := by
    rw [kernelSetMass_add]
    apply probability_average_relative_error (fun t => (P ^ M) q t)
      (kernelSetMass P F (p * k)) β δ (Matrix.pow_apply_nonneg hP M q)
      (stochastic_matrix_power_rows P hrows M q)
    intro t ht
    let u : PositiveSupportClass (P ^ p) s :=
      ⟨t, same_time_endpoints_same_power_class P hP hrows p hp he M q s t hqs ht⟩
    exact powerClass_acceptance_relative_mixing P hP p he s ν hν F k u δ (hmix u) hβ
  have hden : |kernelSetMass P F (p * k) s / β - 1| ≤ δ :=
    powerClass_acceptance_relative_mixing P hP p he s ν hν F k ⟨s, he.refl s⟩ δ
      (hmix ⟨s, he.refl s⟩) hβ
  exact relative_ratio_error hβ hδ hδle hnum hden

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_TerminalAcceptanceRestriction
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

def sccAccepting {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (s : Q) (F : Finset Q) : Finset (SCCState P s) :=
  Finset.univ.filter (fun x => x.val ∈ F)



theorem terminal_power_endpoint_component {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (s : Q)
    (hs : IsGraphTerminal (fun x y => 0 < P x y) s) (n : ℕ) (t : Q)
    (hst : 0 < (P ^ n) s t) :
    graphComponent (fun x y => 0 < P x y) t = graphComponent (fun x y => 0 < P x y) s := by
  have hr := positive_power_reachable P hP n s t hst
  exact (graphComponent_eq_iff _ t s).mpr ⟨hs t hr, hr⟩

theorem terminal_scc_power_zero_outside {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (s : Q)
    (hs : IsGraphTerminal (fun x y => 0 < P x y) s) (n : ℕ)
    (x : SCCState P s) (y : Q)
    (hy : graphComponent (fun i j => 0 < P i j) y ≠ graphComponent (fun i j => 0 < P i j) s) :
    (P ^ n) x.val y = 0 := by
  apply le_antisymm _ (Matrix.pow_apply_nonneg hP n _ _)
  apply le_of_not_gt
  intro hp
  have hsx := ((graphComponent_eq_iff _ x.val s).mp x.property).2
  have hx := graphTerminal_of_reachable _ hs hsx
  exact hy ((terminal_power_endpoint_component P hP x.val hx n y hp).trans x.property)

/-- Acceptance probabilities within a terminal SCC equal the original
chain probabilities, since all mass outside that SCC is zero. -/
theorem terminal_scc_acceptance_mass {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (s : Q)
    (hs : IsGraphTerminal (fun x y => 0 < P x y) s) (F : Finset Q)
    (n : ℕ) (x : SCCState P s) :
    kernelSetMass (sccMatrix P s) (sccAccepting P s F) n x = kernelSetMass P F n x.val := by
  classical
  calc
    _ = ∑ y : SCCState P s, if y.val ∈ F then (P ^ n) x.val y.val else 0 := by
      simp only [kernelSetMass, sccAccepting, Finset.sum_filter, sccMatrix_power P hP]
    _ = ∑ y, if y ∈ F then (P ^ n) x.val y else 0 := by
      apply embedded_weight_sum (fun y : SCCState P s => y.val) Subtype.val_injective
        (fun y => if y ∈ F then (P ^ n) x.val y else 0)
      intro y hy
      have hout : graphComponent (fun i j => 0 < P i j) y ≠ graphComponent (fun i j => 0 < P i j) s :=
        fun he => hy ⟨⟨y, he⟩, rfl⟩
      simp [terminal_scc_power_zero_outside P hP s hs n x y hout]
    _ = _ := by simp [kernelSetMass]

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_UniformTerminalMixing
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

abbrev TerminalPowerClassIndex {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) := Σ s : {s : Q // s ∈ graphTerminalSet P}, SCCState P s.val

/-- All terminal components and all their cyclic classes admit one
geometric coefficient and rate for the chosen common support period. -/
theorem terminal_power_classes_uniform {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1)
    (p : ℕ) (hid : ∀ x y, (∃ z, 0 < (P ^ p) x z ∧ 0 < (P ^ p) z y) ↔ 0 < (P ^ p) x y) :
    ∃ C ρ : ℝ, 1 ≤ C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ s, IsGraphTerminal (fun i j => 0 < P i j) s →
        Equivalence (fun x y => 0 < (sccMatrix P s ^ p) x y) ∧
          ∀ t : SCCState P s, ∃ ν : PositiveSupportClass (sccMatrix P s ^ p) t → ℝ,
            (∀ x, 0 < ν x) ∧ (∑ x, ν x = 1) ∧
            ∀ n x y, |(supportClassMatrix (sccMatrix P s ^ p) t ^ n) x y / ν y - 1| ≤ C * ρ ^ n := by
  classical
  have hfamily (i : TerminalPowerClassIndex P) :
      ∃ (ν : PositiveSupportClass (sccMatrix P i.1.val ^ p) i.2 → ℝ) (C ρ : ℝ),
        (∀ x, 0 < ν x) ∧ (∑ x, ν x = 1) ∧ 0 < C ∧ 0 < ρ ∧ ρ < 1 ∧
        ∀ n x y, |(supportClassMatrix (sccMatrix P i.1.val ^ p) i.2 ^ n) x y / ν y - 1| ≤ C * ρ ^ n :=
    (terminal_scc_mixing_at_idempotent_power P hP hrows p hid i.1.val
      ((mem_graphTerminalSet P i.1.val).mp i.1.property)).2 i.2
  choose ν c r hν hsum hc hr hr1 hmix using hfamily
  let C := 1 + ∑ i, c i
  have hC : 1 ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => (hc i).le))
  have hcC (i : TerminalPowerClassIndex P) : c i ≤ C := by
    have hh := Finset.single_le_sum (fun j _ => (hc j).le) (Finset.mem_univ i)
    dsimp only [C]
    linarith
  let rates : Option (TerminalPowerClassIndex P) → ℝ := Option.elim' (1 / 2) r
  let ρ := Finset.univ.sup' Finset.univ_nonempty rates
  have hρ : 0 < ρ := by
    have hh := Finset.le_sup' rates (Finset.mem_univ none)
    change (1 / 2 : ℝ) ≤ ρ at hh
    linarith
  have hρ1 : ρ < 1 := by
    apply (Finset.sup'_lt_iff _).mpr
    intro i _
    cases i with
    | none => norm_num [rates]
    | some i => exact hr1 i
  have hrρ (i : TerminalPowerClassIndex P) : r i ≤ ρ :=
    Finset.le_sup' rates (Finset.mem_univ (some i))
  refine ⟨C, ρ, hC, hρ, hρ1, ?_⟩
  intro s hs
  refine ⟨(terminal_scc_mixing_at_idempotent_power P hP hrows p hid s hs).1, ?_⟩
  intro t
  let i : TerminalPowerClassIndex P := ⟨⟨s, (mem_graphTerminalSet P s).mpr hs⟩, t⟩
  refine ⟨ν i, hν i, hsum i, ?_⟩
  intro n x y
  exact (hmix i n x y).trans (mul_le_mul (hcC i)
    (pow_le_pow_left₀ (hr i).le (hrρ i) n) (pow_nonneg (hr i).le n) (zero_le_one.trans hC))

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_TerminalAcceptanceTail
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

/-- A single logarithmic tail length works for every terminal component,
accepting set, middle length and reachable middle endpoint. The full
acceptance probability and every tail denominator refer to the original
kernel; positivity of the head continuation is the only support premise. -/
theorem terminal_acceptance_logarithmic_tail {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1)
    (p : ℕ) (hp : 0 < p)
    (hid : ∀ x y, (∃ z, 0 < (P ^ p) x z ∧ 0 < (P ^ p) z y) ↔ 0 < (P ^ p) x y) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ R : ℕ, 0 < R ∧ p ∣ R ∧ (R : ℝ) ≤ K * logInv ε ∧
        ∀ (F : Finset Q) (q : Q), IsGraphTerminal (fun x y => 0 < P x y) q →
          ∀ (M : ℕ) (s : Q), 0 < (P ^ M) q s →
            0 < kernelSetMass P F (M + R) q →
            0 < kernelSetMass P F R s ∧
              |kernelSetMass P F (M + R) q / kernelSetMass P F R s - 1| ≤ ε / 4 := by
  classical
  obtain ⟨C, ρ, hC, hρ, hρ1, hclasses⟩ := terminal_power_classes_uniform P hP hrows p hid
  obtain ⟨K, hK, hcut⟩ := geometric_accuracy_cutoff (zero_lt_one.trans_le hC) hρ hρ1
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  refine ⟨p * K, mul_pos hp' hK, ?_⟩
  intro ε hε hεle
  obtain ⟨k, hk, hlen, hsmall⟩ := hcut ε hε hεle
  refine ⟨p * k, Nat.mul_pos hp hk, dvd_mul_right p k, ?_, ?_⟩
  · push_cast
    nlinarith [mul_le_mul_of_nonneg_left hlen hp'.le]
  · intro F q hq M s hqs hacc
    let x : SCCState P q := ⟨q, rfl⟩
    let y : SCCState P q := ⟨s, terminal_power_endpoint_component P hP q hq M s hqs⟩
    obtain ⟨he, hmixing⟩ := hclasses q hq
    obtain ⟨ν, hν, _, hmix⟩ := hmixing y
    have hqs' : 0 < (sccMatrix P q ^ M) x y := by
      rw [sccMatrix_power P hP]
      exact hqs
    have hacc' : 0 < kernelSetMass (sccMatrix P q) (sccAccepting P q F) (M + p * k) x := by
      rw [terminal_scc_acceptance_mass P hP q hq]
      exact hacc
    have hδ : 0 ≤ C * ρ ^ k := mul_nonneg (zero_le_one.trans hC) (pow_nonneg hρ.le k)
    have hδle : C * ρ ^ k ≤ 1 / 2 := by linarith
    have hh := periodic_acceptance_ratio (sccMatrix P q) (fun x y => hP x.val y.val)
      (fun z => (terminal_scc_row_sum P hP q hq z).trans (hrows z.val)) p hp he
      (sccAccepting P q F) M k x y hqs' ν hν (C * ρ ^ k) hδ hδle (hmix k) hacc'
    rw [terminal_scc_acceptance_mass P hP q hq,
      terminal_scc_acceptance_mass P hP q hq] at hh
    exact ⟨hh.1, hh.2.trans (by linarith)⟩

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_WordTripleApproximation
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

theorem terminalWordTailWeight_sum {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T M R : ℕ)
    (h : TerminalWordHead δ s F T (M + R)) (u : Bits M) :
    (∑ v, terminalWordTailWeight δ s F T M R h u v) =
      kernelSetMass (fairWordKernel δ) F R (wordEnd δ (wordEnd δ s h.val) u) :=
  fairAcceptedWordWeight_sum δ _ F R

theorem terminalWordHead_continuation {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T M R : ℕ)
    (h : TerminalWordHead δ s F T (M + R)) :
    headContinuation (fun _ (_ : Bits M) => 1 / (2 : ℝ) ^ M)
      (terminalWordTailWeight δ s F T M R) h =
      kernelSetMass (fairWordKernel δ) F (M + R) (wordEnd δ s h.val) := by
  simp only [headContinuation, terminalWordTailWeight_sum]
  exact uniform_word_continuation δ _ F M R

def terminalWordHeadLaw {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T N : ℕ) :
    TerminalWordHead δ s F T N → ℝ :=
  normalizeWeights (fun h => (1 / (2 : ℝ) ^ T) *
    kernelSetMass (fairWordKernel δ) F N (wordEnd δ s h.val))

theorem terminalWordHead_mass {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T M R : ℕ) :
    (∑ h : TerminalWordHead δ s F T (M + R), (1 / (2 : ℝ) ^ T) *
      kernelSetMass (fairWordKernel δ) F (M + R) (wordEnd δ s h.val)) =
      ∑ w, terminalRestrictedWordWeight δ s F T (M + R) w := by
  rw [← terminalWordTripleWeight_sum δ s F T M R]
  change _ = ∑ x, headMiddleTailWeight _ _ _ x
  rw [headMiddleTailWeight_sum]
  simp only [terminalWordHead_continuation]

/-- The uniform logarithmic tail theorem now applies to actual middle
words, with every denominator positive and all finite-state choices uniform. -/
theorem terminal_word_logarithmic_tail {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ R : ℕ, 0 < R ∧ (R : ℝ) ≤ K * logInv ε ∧
        ∀ (s : Q) (F : Finset Q) (T M : ℕ)
          (h : TerminalWordHead δ s F T (M + R)) (u : Bits M),
          (0 < ∑ v, terminalWordTailWeight δ s F T M R h u v) ∧
          |headContinuation (fun _ (_ : Bits M) => 1 / (2 : ℝ) ^ M)
            (terminalWordTailWeight δ s F T M R) h /
              (∑ v, terminalWordTailWeight δ s F T M R h u v) - 1| ≤ ε / 4 := by
  obtain ⟨p, hp, hid⟩ := exists_idempotent_matrix_support (fairWordKernel δ)
    (uniformStepKernel_nonneg δ)
  obtain ⟨K, hK, htail⟩ := terminal_acceptance_logarithmic_tail (fairWordKernel δ)
    (uniformStepKernel_nonneg δ) (uniformStepKernel_row_sum δ) p hp hid
  refine ⟨K, hK, ?_⟩
  intro ε hε hεle
  obtain ⟨R, hR, _, hlen, hr⟩ := htail ε hε hεle
  refine ⟨R, hR, hlen, ?_⟩
  intro s F T M h u
  rw [terminalWordHead_continuation, terminalWordTailWeight_sum]
  have hh := (mem_terminalWordHeads δ s F T (M + R) h.val).mp h.property
  exact hr F (wordEnd δ s h.val) ((mem_graphTerminalSet _ _).mp hh.1) M _
    (uniform_word_endpoint_positive δ _ u) hh.2

def terminalRoundedWordLaw {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T M R : ℕ)
    (q : TerminalWordHead δ s F T (M + R) → ℝ) (L : Q → Bits R → ℝ) :
    Bits (T + (M + R)) → ℝ :=
  fiberMass (terminalWordConcat δ s F T M R)
    (headMiddleTailRounded q (fun _ (_ : Bits M) => 1 / (2 : ℝ) ^ M)
      (fun h u => L (wordEnd δ (wordEnd δ s h.val) u)))

/-- Actual complete-word error, for tail laws that depend only on the
finite middle endpoint. This preserves the finite circuit selector interface. -/
theorem terminalRoundedWordLaw_tv {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T M R : ℕ)
    (q : TerminalWordHead δ s F T (M + R) → ℝ) (L : Q → Bits R → ℝ)
    (hZ : 0 < ∑ w, terminalRestrictedWordWeight δ s F T (M + R) w)
    (hL : ∀ t v, 0 ≤ L t v) (hLsum : ∀ t, ∑ v, L t v = 1)
    (ζ η θ ξ : ℝ)
    (hhead : tv q (terminalWordHeadLaw δ s F T (M + R)) ≤ ζ)
    (htail : ∀ h u, tv (L (wordEnd δ (wordEnd δ s h.val) u))
      (normalizeWeights (terminalWordTailWeight δ s F T M R h u)) ≤ η)
    (hratio : ∀ h u, |headContinuation (fun _ (_ : Bits M) => 1 / (2 : ℝ) ^ M)
      (terminalWordTailWeight δ s F T M R) h /
        (∑ v, terminalWordTailWeight δ s F T M R h u v) - 1| ≤ θ)
    (hrestriction : tv (normalizeWeights (fairAcceptedWordWeight δ s F))
      (normalizeWeights (terminalRestrictedWordWeight δ s F T (M + R))) ≤ ξ) :
    tv (terminalRoundedWordLaw δ s F T M R q L)
      (normalizeWeights (fairAcceptedWordWeight δ s F)) ≤ ζ + η + θ / 2 + ξ := by
  classical
  let a := fun _ : TerminalWordHead δ s F T (M + R) => 1 / (2 : ℝ) ^ T
  let K := fun _ : TerminalWordHead δ s F T (M + R) => fun _ : Bits M => 1 / (2 : ℝ) ^ M
  let b := terminalWordTailWeight δ s F T M R
  let L' := fun h : TerminalWordHead δ s F T (M + R) => fun u : Bits M =>
    L (wordEnd δ (wordEnd δ s h.val) u)
  have hZ' : 0 < ∑ h, a h * headContinuation K b h := by
    simp only [a, K, b, terminalWordHead_continuation, terminalWordHead_mass]
    exact hZ
  have hhead' : tv q (normalizeWeights (fun h => a h * headContinuation K b h)) ≤ ζ := by
    simpa only [a, K, b, terminalWordHead_continuation, terminalWordHeadLaw] using hhead
  have hK : ∀ h, ∑ u, K h u = 1 := by
    intro h
    simp [K, Bits]
  have ht := headMiddleTailRounded_tv_target a q K b L' (fun _ => by positivity)
    (fun _ _ => by positivity) (fun _ _ v => fairAcceptedWordWeight_nonneg δ _ F v)
    hZ' hK (fun h u => hL _) (fun h u => hLsum _) ζ η θ hhead' htail hratio
  have hm := tv_map_le (terminalWordConcat δ s F T M R)
    (headMiddleTailRounded q K L') (normalizeWeights (headMiddleTailWeight a K b))
  have he : headMiddleTailWeight a K b = terminalWordTripleWeight δ s F T M R := rfl
  rw [he] at hm
  simp_rw [terminalWordTripleWeight_normalized] at hm
  have hb : tv (terminalRoundedWordLaw δ s F T M R q L)
      (normalizeWeights (terminalRestrictedWordWeight δ s F T (M + R))) ≤ ζ + η + θ / 2 :=
    hm.trans ht
  exact (tv_triangle _ (normalizeWeights (terminalRestrictedWordWeight δ s F T (M + R))) _).trans
    (add_le_add hb (by rwa [tv_symm]))

theorem terminalRoundedWordLaw_support {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T M R : ℕ)
    (q : TerminalWordHead δ s F T (M + R) → ℝ) (L : Q → Bits R → ℝ)
    (hq : ∀ h, 0 ≤ q h) (hL : ∀ t v, 0 ≤ L t v)
    (htail : ∀ h u v, 0 < L (wordEnd δ (wordEnd δ s h.val) u) v →
      0 < terminalWordTailWeight δ s F T M R h u v)
    (w : Bits (T + (M + R))) (hw : 0 < terminalRoundedWordLaw δ s F T M R q L w) :
    0 < fairAcceptedWordWeight δ s F w := by
  classical
  obtain ⟨x, hx, hp⟩ := (fiberMass_pos_iff _ _
    (headMiddleTailRounded_nonneg q _ _ hq (fun _ _ => by positivity)
      (fun h u => hL _)) w).mp hw
  have hLp : 0 < L (wordEnd δ (wordEnd δ s x.1.val) x.2.1) x.2.2 :=
    pos_of_mul_pos_right hp (mul_nonneg (hq x.1) (by positivity))
  have hb := htail x.1 x.2.1 x.2.2 hLp
  rw [← hx]
  change 0 < fairAcceptedWordWeight δ s F (Fin.append x.1.val (Fin.append x.2.1 x.2.2))
  rw [fairAcceptedWordWeight_append, fairAcceptedWordWeight_append]
  exact mul_pos (by positivity) (mul_pos (by positivity) hb)

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_HeadMiddleTailSeeds
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def jointSeedSample {H U : Type} {a b : ℕ} (f : Bits a → H) (g : H → Bits b → U) :
    Bits (a + b) → H × U := fun seed =>
  let z := seedPairEquiv a b seed
  (f z.1, g (f z.1) z.2)

theorem jointSeedSample_law {H U : Type} [Fintype H] [Fintype U]
    [DecidableEq H] [DecidableEq U] {a b : ℕ}
    (f : Bits a → H) (g : H → Bits b → U) (h : H) (u : U) :
    finiteSeedLaw (jointSeedSample f g) (h, u) = finiteSeedLaw f h * finiteSeedLaw (g h) u := by
  rw [← uniformSourceLaw_bits]
  have he := uniformSourceLaw_reindex (seedPairEquiv a b)
    (fun z : Bits a × Bits b => (f z.1, g (f z.1) z.2))
  change uniformSourceLaw (jointSeedSample f g) = _ at he
  rw [congrFun he (h, u), uniformSourceLaw_joint, uniformSourceLaw_bits, uniformSourceLaw_bits]

def headMiddleTailSeedSample {H U V : Type} {a b c : ℕ}
    (f : Bits a → H) (g : H → Bits b → U) (l : H → U → Bits c → V) :
    Bits (a + (b + c)) → H × (U × V) :=
  jointSeedSample f (fun h => jointSeedSample (g h) (l h))

/-- Three disjoint bit slices realize the sequential law. Conditional
branches reuse their slice; the number of branches adds no random bits. -/
theorem headMiddleTailSeedSample_law {H U V : Type} [Fintype H] [Fintype U] [Fintype V]
    [DecidableEq H] [DecidableEq U] [DecidableEq V] {a b c : ℕ}
    (f : Bits a → H) (g : H → Bits b → U) (l : H → U → Bits c → V) :
    finiteSeedLaw (headMiddleTailSeedSample f g l) =
      headMiddleTailRounded (finiteSeedLaw f) (fun h => finiteSeedLaw (g h))
        (fun h u => finiteSeedLaw (l h u)) := by
  funext ⟨h, u, v⟩
  simp only [headMiddleTailSeedSample, jointSeedSample_law, headMiddleTailRounded, mul_assoc]

theorem finiteSeedLaw_identity (n : ℕ) (w : Bits n) :
    finiteSeedLaw (fun u : Bits n => u) w = 1 / (2 : ℝ) ^ n := by
  simp [finiteSeedLaw]

def terminalWordSeedSample {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T M R a c : ℕ)
    (f : Bits a → TerminalWordHead δ s F T (M + R))
    (g : Q → Bits M → Bits M) (l : Q → Bits c → Bits R) :
    Bits (a + (M + c)) → Bits (T + (M + R)) :=
  terminalWordConcat δ s F T M R ∘ headMiddleTailSeedSample f
    (fun h => g (wordEnd δ s h.val))
    (fun h u => l (wordEnd δ (wordEnd δ s h.val) u))

/-- The middle output word may be any exact uniform sampler for its
start state. It need not be the input seed word; this matches the DFA-run
sampler that will implement the middle and supply its endpoint. -/
theorem terminalWordSeedSample_law {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T M R a c : ℕ)
    (f : Bits a → TerminalWordHead δ s F T (M + R))
    (g : Q → Bits M → Bits M) (l : Q → Bits c → Bits R)
    (hg : ∀ q w, finiteSeedLaw (g q) w = 1 / (2 : ℝ) ^ M) :
    finiteSeedLaw (terminalWordSeedSample δ s F T M R a c f g l) =
      terminalRoundedWordLaw δ s F T M R (finiteSeedLaw f) (fun q => finiteSeedLaw (l q)) := by
  rw [terminalWordSeedSample, finiteSeedLaw_map, headMiddleTailSeedSample_law]
  have he (q : Q) : finiteSeedLaw (g q) = fun _ => 1 / (2 : ℝ) ^ M := funext (hg q)
  simp only [he, terminalRoundedWordLaw]

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_FiniteStateRunFormulas
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

abbrev FiniteRunOutput (Q : Type) (n : ℕ) := Fin n ⊕ (Fin (n + 1) × Q)

def finiteRunEncode {Q : Type} [DecidableEq Q] {n : ℕ}
    (w : Bits n) (γ : Fin (n + 1) → Q) : FiniteRunOutput Q n → Bool :=
  Sum.elim w (fun z => decide (γ z.1 = z.2))

/-- Reindexing a finite state type preserves the full run, not just its
endpoint or acceptance bit. -/
theorem drivenPath_state_equiv {Q H : Type} (e : Q ≃ H) (δ : Q → Bool → Q)
    (s : Q) {n : ℕ} (w : Bits n) :
    drivenPath (fun h b => e (δ (e.symm h) b)) n (e s) w =
      fun i => e (drivenPath δ n s w i) := by
  apply (drivenPath_eq_iff _ _ _ _ _).mpr
  constructor
  · simp
  · intro i
    simp only [Equiv.symm_apply_apply, drivenPath_step]

theorem exact_finite_state_run_formulas_at_start {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) :
    ∃ D C k : ℕ, ∀ n : ℕ, ∃ fs : FiniteRunOutput Q n → CircuitFormula n,
      (∀ o, formulaDepth (fs o) ≤ D) ∧
      (∀ o, formulaCost (fs o) ≤ C * (n + 1) ^ k) ∧
      ∃ e : Bits n ≃ Bits n, ∀ seed o, formulaEval (fs o) seed =
        finiteRunEncode (e seed) (drivenPath δ n s (e seed)) o := by
  classical
  let eQ := Fintype.equivFin Q
  let A : BinaryDFA (Fintype.card Q) := {
    start := eQ s
    step := fun t b => eQ (δ (eQ.symm t) b)
    accepting := Finset.univ }
  obtain ⟨D, C, k, hall⟩ := exact_dfa_run_formulas A
  refine ⟨D, C, k, ?_⟩
  intro n
  obtain ⟨fs, hd, hc, e, he⟩ := hall n
  let out : FiniteRunOutput Q n → FullRunOutput (Fintype.card Q) n :=
    Sum.map id (fun z => (z.1, eQ z.2))
  refine ⟨fs ∘ out, fun o => hd (out o), fun o => hc (out o), e, ?_⟩
  intro seed o
  rw [Function.comp_apply, he]
  have hp := drivenPath_state_equiv eQ δ s (e seed)
  cases o with
  | inl i => rfl
  | inr z =>
    change decide (drivenPath A.step n A.start (e seed) z.1 = eQ z.2) =
      decide (drivenPath δ n s (e seed) z.1 = z.2)
    change drivenPath A.step n A.start (e seed) = _ at hp
    rw [hp]
    simp only [eQ.injective.eq_iff]

/-- A single depth and polynomial bound works for every possible middle
start state. All branches read the same n-bit seed. -/
theorem exact_finite_state_run_formulas {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) :
    ∃ D C k : ℕ, ∀ n : ℕ,
      ∃ fs : Q → FiniteRunOutput Q n → CircuitFormula n,
        (∀ s o, formulaDepth (fs s o) ≤ D) ∧
        (∀ s o, formulaCost (fs s o) ≤ C * (n + 1) ^ k) ∧
        ∃ e : Q → Bits n ≃ Bits n, ∀ s seed o, formulaEval (fs s o) seed =
          finiteRunEncode (e s seed) (drivenPath δ n s (e s seed)) o := by
  classical
  choose D C k hs using exact_finite_state_run_formulas_at_start δ
  refine ⟨∑ s, D s, ∑ s, C s, ∑ s, k s, ?_⟩
  intro n
  choose fs hd hc e he using fun s => hs s n
  refine ⟨fs, ?_, ?_, e, he⟩
  · intro s o
    exact (hd s o).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ s))
  · intro s o
    have hk : k s ≤ ∑ t, k t := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
    have hC : C s ≤ ∑ t, C t := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
    exact (hc s o).trans ((monomial_bound_mono (C s) n n (k s) (∑ t, k t) le_rfl hk).trans
      (Nat.mul_le_mul_right _ hC))

theorem finiteSeedLaw_word_equiv {n : ℕ} (e : Bits n ≃ Bits n) (w : Bits n) :
    finiteSeedLaw e w = 1 / (2 : ℝ) ^ n := by
  have h := finiteSeedLaw_equiv (fun u : Bits n => u) e w
  simpa only [finiteSeedLaw_identity, Function.comp_def] using h

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_FormulaSelection
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

def wireFormula {k r : ℕ} (wire : Fin k → Fin r) (f : CircuitFormula k) : CircuitFormula r :=
  substituteFormula (fun i => .input (wire i)) f

theorem wireFormula_eval {k r : ℕ} (wire : Fin k → Fin r) (f : CircuitFormula k) (seed : Bits r) :
    formulaEval (wireFormula wire f) seed = formulaEval f (seed ∘ wire) :=
  substituteFormula_eval _ f seed

theorem wireFormula_depth {k r : ℕ} (wire : Fin k → Fin r) (f : CircuitFormula k) :
    formulaDepth (wireFormula wire f) ≤ formulaDepth f := by
  simpa only [wireFormula, Nat.zero_add] using substituteFormula_depth (fun i => .input (wire i)) 0 (fun _ => le_rfl) f

theorem wireFormula_cost {k r : ℕ} (wire : Fin k → Fin r) (f : CircuitFormula k) :
    formulaCost (wireFormula wire f) ≤ formulaCost f := by
  simpa only [wireFormula, Nat.zero_add, Nat.mul_one, Nat.add_zero] using
    substituteFormula_cost (fun i => .input (wire i)) 0 (fun _ => le_rfl) f

def selectFormula {I : Type} [Fintype I] {r : ℕ}
    (select branch : I → CircuitFormula r) : CircuitFormula r :=
  formulaIndexedAny (fun i => formulaAnd (select i) (branch i))

theorem selectFormula_eval {I : Type} [Fintype I] [DecidableEq I] {r : ℕ}
    (select branch : I → CircuitFormula r) (seed : Bits r) (chosen : I)
    (hs : ∀ i, formulaEval (select i) seed = decide (chosen = i)) :
    formulaEval (selectFormula select branch) seed = formulaEval (branch chosen) seed := by
  apply Bool.eq_iff_iff.mpr
  rw [selectFormula, formulaIndexedAny_eval]
  simp only [formulaAnd_eval, Bool.and_eq_true, hs, decide_eq_true_eq]
  constructor
  · rintro ⟨i, rfl, hi⟩; exact hi
  · intro h; exact ⟨chosen, rfl, h⟩

theorem selectFormula_depth {I : Type} [Fintype I] {r : ℕ}
    (select branch : I → CircuitFormula r) (Ds Db : ℕ)
    (hs : ∀ i, formulaDepth (select i) ≤ Ds) (hb : ∀ i, formulaDepth (branch i) ≤ Db) :
    formulaDepth (selectFormula select branch) ≤ max Ds Db + 2 := by
  apply (formulaIndexedAny_depth _ (max Ds Db + 1) ?_).trans (by omega)
  intro i
  rw [formulaAnd_depth]
  exact Nat.add_le_add_right (max_le_max (hs i) (hb i)) 1

theorem selectFormula_cost {I : Type} [Fintype I] {r : ℕ}
    (select branch : I → CircuitFormula r) (Ks Kb : ℕ)
    (hs : ∀ i, formulaCost (select i) ≤ Ks) (hb : ∀ i, formulaCost (branch i) ≤ Kb) :
    formulaCost (selectFormula select branch) ≤ Fintype.card I * (Ks + Kb + 4) + 1 := by
  have hh := formulaIndexedAny_cost (fun i => formulaAnd (select i) (branch i)) (Ks + Kb + 3)
    (fun i => by rw [formulaAnd_cost]; exact Nat.add_le_add_right (Nat.add_le_add (hs i) (hb i)) 3)
  simpa only [selectFormula, Nat.add_assoc] using hh

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_WordBoundaryRounding
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

theorem terminal_word_head_rounding {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T M R : ℕ)
    (hZ : 0 < ∑ w, terminalRestrictedWordWeight δ s F T (M + R) w)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : Bits (binaryBoundarySeed T ε) → TerminalWordHead δ s F T (M + R),
      (∀ seed, 0 < terminalWordHeadLaw δ s F T (M + R) (f seed)) ∧
      tv (finiteSeedLaw f) (terminalWordHeadLaw δ s F T (M + R)) ≤ ε / 4 := by
  classical
  apply binary_boundary_rounding _ _ _ T _ ε hε
  · exact normalizeWeights_nonneg _ (fun h => mul_nonneg (by positivity)
      (kernelSetMass_nonneg _ (uniformStepKernel_nonneg δ) F (M + R) (wordEnd δ s h.val)))
  · apply normalizeWeights_sum
    rwa [terminalWordHead_mass]
  · exact (Fintype.card_subtype_le _).trans (by simp [Bits])

/-- All endpoint branches use the same number of tail random bits.
Zero-acceptance states get a total fallback function and are never used
by the terminal-head construction. -/
theorem accepting_word_tail_rounding {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (F : Finset Q) (R : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ l : Q → Bits (binaryBoundarySeed R ε) → Bits R,
      ∀ q, 0 < kernelSetMass (fairWordKernel δ) F R q →
        (∀ seed, 0 < fairAcceptedWordWeight δ q F (l q seed)) ∧
        tv (finiteSeedLaw (l q)) (normalizeWeights (fairAcceptedWordWeight δ q F)) ≤ ε / 4 := by
  classical
  have hall : ∀ q : Q, ∃ l : Bits (binaryBoundarySeed R ε) → Bits R,
      0 < kernelSetMass (fairWordKernel δ) F R q →
        (∀ seed, 0 < fairAcceptedWordWeight δ q F (l seed)) ∧
        tv (finiteSeedLaw l) (normalizeWeights (fairAcceptedWordWeight δ q F)) ≤ ε / 4 := by
    intro q
    by_cases hp : 0 < kernelSetMass (fairWordKernel δ) F R q
    · have hZ : 0 < ∑ w : Bits R, fairAcceptedWordWeight δ q F w := by
        rwa [fairAcceptedWordWeight_sum]
      obtain ⟨l, hl, he⟩ := binary_boundary_rounding
        (normalizeWeights (fairAcceptedWordWeight δ q F))
        (normalizeWeights_nonneg _ (fairAcceptedWordWeight_nonneg δ q F))
        (normalizeWeights_sum _ hZ) R (by simp [Bits]) ε hε
      refine ⟨l, fun _ => ⟨?_, he⟩⟩
      intro seed
      exact (div_pos_iff_of_pos_right hZ).mp (hl seed)
    · exact ⟨fun _ _ => false, fun h => False.elim (hp h)⟩
  choose l hl using hall
  exact ⟨l, hl⟩

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_PositiveDensityWordSeed
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

structure TerminalWordBoundaryModel {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T M R : ℕ) (ε : ℝ) where
  head : Bits (binaryBoundarySeed T ε) → TerminalWordHead δ s F T (M + R)
  tail : Q → Bits (binaryBoundarySeed R ε) → Bits R
  head_positive : ∀ seed, 0 < terminalWordHeadLaw δ s F T (M + R) (head seed)
  head_error : tv (finiteSeedLaw head) (terminalWordHeadLaw δ s F T (M + R)) ≤ ε / 4
  tail_positive : ∀ q, 0 < kernelSetMass (fairWordKernel δ) F R q →
    ∀ seed, 0 < fairAcceptedWordWeight δ q F (tail q seed)
  tail_error : ∀ q, 0 < kernelSetMass (fairWordKernel δ) F R q →
    tv (finiteSeedLaw (tail q)) (normalizeWeights (fairAcceptedWordWeight δ q F)) ≤ ε / 4

theorem terminalWordBoundaryModel_nonempty {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (F : Finset Q) (T M R : ℕ)
    (hZ : 0 < ∑ w, terminalRestrictedWordWeight δ s F T (M + R) w)
    (ε : ℝ) (hε : 0 < ε) : Nonempty (TerminalWordBoundaryModel δ s F T M R ε) := by
  obtain ⟨f, hf, he⟩ := terminal_word_head_rounding δ s F T M R hZ ε hε
  obtain ⟨l, hl⟩ := accepting_word_tail_rounding δ F R ε hε
  exact ⟨{
    head := f
    tail := l
    head_positive := hf
    head_error := he
    tail_positive := fun q hq => (hl q hq).1
    tail_error := fun q hq => (hl q hq).2 }⟩

def terminalWordModelSample {Q : Type} [Fintype Q] [DecidableEq Q]
    {δ : Q → Bool → Q} {s : Q} {F : Finset Q} {T M R : ℕ} {ε : ℝ}
    (B : TerminalWordBoundaryModel δ s F T M R ε) (g : Q → Bits M → Bits M) :
    Bits (binaryBoundarySeed T ε + (M + binaryBoundarySeed R ε)) → Bits (T + (M + R)) :=
  terminalWordSeedSample δ s F T M R _ _ B.head g B.tail

theorem terminalWordModelSample_law {Q : Type} [Fintype Q] [DecidableEq Q]
    {δ : Q → Bool → Q} {s : Q} {F : Finset Q} {T M R : ℕ} {ε : ℝ}
    (B : TerminalWordBoundaryModel δ s F T M R ε) (g : Q → Bits M → Bits M)
    (hg : ∀ q w, finiteSeedLaw (g q) w = 1 / (2 : ℝ) ^ M) :
    finiteSeedLaw (terminalWordModelSample B g) =
      terminalRoundedWordLaw δ s F T M R (finiteSeedLaw B.head) (fun q => finiteSeedLaw (B.tail q)) :=
  terminalWordSeedSample_law δ s F T M R _ _ B.head g B.tail hg

theorem terminalWordModelSample_correct {Q : Type} [Fintype Q] [DecidableEq Q]
    {δ : Q → Bool → Q} {s : Q} {F : Finset Q} {T M R : ℕ} {ε : ℝ}
    (B : TerminalWordBoundaryModel δ s F T M R ε) (hε : 0 < ε)
    (hZ : 0 < ∑ w, terminalRestrictedWordWeight δ s F T (M + R) w)
    (htail : ∀ (h : TerminalWordHead δ s F T (M + R)) (u : Bits M),
      (0 < ∑ v, terminalWordTailWeight δ s F T M R h u v) ∧
      |headContinuation (fun _ (_ : Bits M) => 1 / (2 : ℝ) ^ M)
        (terminalWordTailWeight δ s F T M R) h /
          (∑ v, terminalWordTailWeight δ s F T M R h u v) - 1| ≤ ε / 4)
    (hrestriction : tv (normalizeWeights (fairAcceptedWordWeight δ s F))
      (normalizeWeights (terminalRestrictedWordWeight δ s F T (M + R))) ≤ ε / 4)
    (g : Q → Bits M → Bits M) (hg : ∀ q w, finiteSeedLaw (g q) w = 1 / (2 : ℝ) ^ M) :
    (∀ seed, 0 < fairAcceptedWordWeight δ s F (terminalWordModelSample B g seed)) ∧
      tv (finiteSeedLaw (terminalWordModelSample B g))
        (normalizeWeights (fairAcceptedWordWeight δ s F)) ≤ ε := by
  have hp (h : TerminalWordHead δ s F T (M + R)) (u : Bits M) :
      0 < kernelSetMass (fairWordKernel δ) F R (wordEnd δ (wordEnd δ s h.val) u) := by
    simpa only [terminalWordTailWeight_sum] using (htail h u).1
  have hs (h : TerminalWordHead δ s F T (M + R)) (u : Bits M) (v : Bits R)
      (hv : 0 < finiteSeedLaw (B.tail (wordEnd δ (wordEnd δ s h.val) u)) v) :
      0 < terminalWordTailWeight δ s F T M R h u v := by
    obtain ⟨seed, rfl⟩ := (finiteSeedLaw_pos_iff _ v).mp hv
    exact B.tail_positive _ (hp h u) seed
  refine ⟨?_, ?_⟩
  · intro seed
    apply terminalRoundedWordLaw_support δ s F T M R (finiteSeedLaw B.head)
      (fun q => finiteSeedLaw (B.tail q)) (finiteSeedLaw_nonneg B.head)
      (fun q => finiteSeedLaw_nonneg (B.tail q)) hs
    rw [← terminalWordModelSample_law B g hg]
    exact (finiteSeedLaw_pos_iff _ _).mpr ⟨seed, rfl⟩
  · rw [terminalWordModelSample_law B g hg]
    have hb := terminalRoundedWordLaw_tv δ s F T M R (finiteSeedLaw B.head)
      (fun q => finiteSeedLaw (B.tail q)) hZ (fun q => finiteSeedLaw_nonneg (B.tail q))
      (fun q => finiteSeedLaw_sum (B.tail q)) (ε / 4) (ε / 4) (ε / 4) (ε / 4)
      B.head_error (fun h u => B.tail_error _ (hp h u)) (fun h u => (htail h u).2) hrestriction
    exact hb.trans (by linarith)

/-- The actual positive-density word sampler, including positive
logarithmic head/tail lengths, support, full-word TV, and a coefficient-one
fair-bit budget. This is a sampling-function theorem; circuit resource
bounds remain a separate obligation. -/
theorem positive_density_word_seed_sampling {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (δ : Q → Bool → Q) (c : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ T R : ℕ, 0 < T ∧ 0 < R ∧ (T + R : ℕ) ≤ K * logInv ε ∧
        ∀ (s : Q) (F : Finset Q) (M : ℕ),
          c ≤ kernelSetMass (fairWordKernel δ) F (T + (M + R)) s →
          ∃ B : TerminalWordBoundaryModel δ s F T M R ε,
            ((binaryBoundarySeed T ε + (M + binaryBoundarySeed R ε) : ℕ) : ℝ) ≤
              (T + (M + R) : ℕ) + 8 * logInv ε ∧
            ∀ (g : Q → Bits M → Bits M),
              (∀ q w, finiteSeedLaw (g q) w = 1 / (2 : ℝ) ^ M) →
              (∀ seed, 0 < fairAcceptedWordWeight δ s F (terminalWordModelSample B g seed)) ∧
              tv (finiteSeedLaw (terminalWordModelSample B g))
                (normalizeWeights (fairAcceptedWordWeight δ s F)) ≤ ε := by
  obtain ⟨Kh, hKh, hhead⟩ := terminal_word_head_logarithmic_restriction δ c hc
  obtain ⟨Kt, hKt, htail⟩ := terminal_word_logarithmic_tail δ
  refine ⟨Kh + Kt, add_pos hKh hKt, ?_⟩
  intro ε hε hεle
  obtain ⟨T, hT, hTl, hh⟩ := hhead ε hε hεle
  obtain ⟨R, hR, hRl, ht⟩ := htail ε hε hεle
  refine ⟨T, R, hT, hR, ?_, ?_⟩
  · push_cast
    nlinarith
  · intro s F M hacc
    obtain ⟨hZ, herr⟩ := hh s F (M + R) hacc
    obtain ⟨B⟩ := terminalWordBoundaryModel_nonempty δ s F T M R hZ ε hε
    exact ⟨B, head_middle_tail_seed_bound T M R hε hεle,
      fun g hg => terminalWordModelSample_correct B hε hZ (ht s F T M) herr g hg⟩

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ThreeStageWordCircuit
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def threeStageWordSample {Q : Type} (δ : Q → Bool → Q) (s : Q)
    {T M R a c : ℕ} (f : Bits a → Bits T) (e : Q → Bits M ≃ Bits M)
    (l : Q → Bits c → Bits R) (seed : Bits (a + (M + c))) : Bits (T + (M + R)) :=
  let z := wordTripleEquiv a M c seed
  let h := f z.1
  let u := e (wordEnd δ s h) z.2.1
  let v := l (wordEnd δ (wordEnd δ s h) u) z.2.2
  Fin.append h (Fin.append u v)

def boundaryLookupCost (a : ℕ) : ℕ := 2 ^ a * (3 * a + 2) + 1

def threeStageWordFormulaCost (q a c B : ℕ) : ℕ :=
  let H := boundaryLookupCost a
  let L := boundaryLookupCost c
  let U := q * (H + B + 4) + 1
  H + U + (q * (U + L + 4) + 1)

/-- Compile short head and endpoint-dependent short tail lookups around
the exact run sampler. Only the a-bit and c-bit boundary tables are
enumerated; the M-bit middle uses the given polynomial formulas. -/
theorem three_stage_word_circuit {Q : Type} [Fintype Q] [DecidableEq Q]
    (δ : Q → Bool → Q) (s : Q) (T M R a c D B : ℕ)
    (f : Bits a → Bits T) (e : Q → Bits M ≃ Bits M) (l : Q → Bits c → Bits R)
    (middle : Q → FiniteRunOutput Q M → CircuitFormula M)
    (hD : ∀ q o, formulaDepth (middle q o) ≤ D)
    (hB : ∀ q o, formulaCost (middle q o) ≤ B)
    (he : ∀ q seed o, formulaEval (middle q o) seed =
      finiteRunEncode (e q seed) (drivenPath δ M q (e q seed)) o) :
    ∃ S : Circuit (Fin (T + (M + R))), ∃ hbits : S.randomBits = a + (M + c),
      (∀ seed, S.eval (fun j => seed (Fin.cast hbits j)) = threeStageWordSample δ s f e l seed) ∧
      S.depth ≤ D + 7 ∧ S.size ≤ a + (M + c) +
        (T + (M + R)) * (threeStageWordFormulaCost (Fintype.card Q) a c B + 1) := by
  classical
  let hw : Fin a → Fin (a + (M + c)) := Fin.castAdd (M + c)
  let mw : Fin M → Fin (a + (M + c)) := fun i => Fin.natAdd a (Fin.castAdd c i)
  let tw : Fin c → Fin (a + (M + c)) := fun i => Fin.natAdd a (Fin.natAdd M i)
  let hs : Q → CircuitFormula (a + (M + c)) := fun q =>
    wireFormula hw (truthTableFormula (fun seed => decide (wordEnd δ s (f seed) = q)))
  let hf : Fin T → CircuitFormula (a + (M + c)) := fun i =>
    wireFormula hw (truthTableFormula (fun seed => f seed i))
  let mb : Q → FiniteRunOutput Q M → CircuitFormula (a + (M + c)) :=
    fun q o => wireFormula mw (middle q o)
  let mf : FiniteRunOutput Q M → CircuitFormula (a + (M + c)) :=
    fun o => selectFormula hs (fun q => mb q o)
  let ts : Q → CircuitFormula (a + (M + c)) := fun q => mf (.inr (Fin.last M, q))
  let tb : Q → Fin R → CircuitFormula (a + (M + c)) := fun q i =>
    wireFormula tw (truthTableFormula (fun seed => l q seed i))
  let tf : Fin R → CircuitFormula (a + (M + c)) := fun i => selectFormula ts (fun q => tb q i)
  let fs : Fin (T + (M + R)) → CircuitFormula (a + (M + c)) :=
    Fin.append hf (Fin.append (fun i => mf (.inl i)) tf)
  have hhD (q : Q) : formulaDepth (hs q) ≤ 3 :=
    (wireFormula_depth _ _).trans (truthTableFormula_depth _)
  have hhB (q : Q) : formulaCost (hs q) ≤ boundaryLookupCost a :=
    (wireFormula_cost _ _).trans (truthTableFormula_cost _)
  have hmfD (o : FiniteRunOutput Q M) : formulaDepth (mf o) ≤ D + 5 :=
    (selectFormula_depth _ _ 3 D hhD (fun q => (wireFormula_depth _ _).trans (hD q o))).trans (by omega)
  let U := Fintype.card Q * (boundaryLookupCost a + B + 4) + 1
  have hmfB (o : FiniteRunOutput Q M) : formulaCost (mf o) ≤ U :=
    selectFormula_cost _ _ _ _ hhB (fun q => (wireFormula_cost _ _).trans (hB q o))
  have htfD (i : Fin R) : formulaDepth (tf i) ≤ D + 7 :=
    (selectFormula_depth _ _ (D + 5) 3 (fun q => hmfD (.inr (Fin.last M, q)))
      (fun _ => (wireFormula_depth _ _).trans (truthTableFormula_depth _))).trans (by omega)
  have htfB (i : Fin R) : formulaCost (tf i) ≤
      Fintype.card Q * (U + boundaryLookupCost c + 4) + 1 :=
    selectFormula_cost _ _ _ _ (fun q => hmfB (.inr (Fin.last M, q)))
      (fun _ => (wireFormula_cost _ _).trans (truthTableFormula_cost _))
  have hfsD (i : Fin (T + (M + R))) : formulaDepth (fs i) ≤ D + 7 := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [fs, Fin.append_left]
      exact ((wireFormula_depth _ _).trans (truthTableFormula_depth _)).trans (by omega)
    · simp only [fs, Fin.append_right]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa only [Fin.append_left] using (hmfD (.inl j)).trans (by omega : D + 5 ≤ D + 7)
      · simpa only [Fin.append_right] using htfD j
  have hfsB (i : Fin (T + (M + R))) :
      formulaCost (fs i) ≤ threeStageWordFormulaCost (Fintype.card Q) a c B := by
    change formulaCost (fs i) ≤ boundaryLookupCost a + U +
      (Fintype.card Q * (U + boundaryLookupCost c + 4) + 1)
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [fs, Fin.append_left]
      have hh : formulaCost (hf j) ≤ boundaryLookupCost a :=
        (wireFormula_cost _ _).trans (truthTableFormula_cost _)
      omega
    · simp only [fs, Fin.append_right]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [Fin.append_left]
        have hh := hmfB (.inl j)
        omega
      · simp only [Fin.append_right]
        have hh := htfB j
        omega
  have hseval (seed : Bits (a + (M + c))) (q : Q) : formulaEval (hs q) seed =
      decide (wordEnd δ s (f (wordTripleEquiv a M c seed).1) = q) := by
    rw [wireFormula_eval, truthTableFormula_eval]
    rfl
  have hmeval (seed : Bits (a + (M + c))) (o : FiniteRunOutput Q M) :
      formulaEval (mf o) seed =
        let z := wordTripleEquiv a M c seed
        let q := wordEnd δ s (f z.1)
        finiteRunEncode (e q z.2.1) (drivenPath δ M q (e q z.2.1)) o := by
    rw [selectFormula_eval _ _ seed _ (hseval seed), wireFormula_eval, he]
    rfl
  have htseval (seed : Bits (a + (M + c))) (q : Q) : formulaEval (ts q) seed =
      let z := wordTripleEquiv a M c seed
      let start := wordEnd δ s (f z.1)
      decide (wordEnd δ start (e start z.2.1) = q) := by
    change formulaEval (mf (.inr (Fin.last M, q))) seed = _
    rw [hmeval]
    simp only [finiteRunEncode, Sum.elim_inr, drivenPath_last_wordEnd]
  have hteval (seed : Bits (a + (M + c))) (i : Fin R) : formulaEval (tf i) seed =
      let z := wordTripleEquiv a M c seed
      let start := wordEnd δ s (f z.1)
      l (wordEnd δ start (e start z.2.1)) z.2.2 i := by
    rw [selectFormula_eval _ _ seed _ (htseval seed), wireFormula_eval, truthTableFormula_eval]
    rfl
  obtain ⟨S, hbits, hEval, hd, hsize⟩ := formula_fintype_family_circuit fs (D + 7) hfsD
  refine ⟨S, hbits, ?_, hd, ?_⟩
  · intro seed
    funext i
    rw [hEval]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp only [fs, threeStageWordSample, Fin.append_left]
      rw [wireFormula_eval, truthTableFormula_eval]
      rfl
    · simp only [fs, threeStageWordSample, Fin.append_right]
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp only [Fin.append_left, hmeval, finiteRunEncode, Sum.elim_inl]
      · simp only [Fin.append_right, hteval]
  · have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hfsB i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    rw [hsize]
    simp only [Fintype.card_fin]
    nlinarith

theorem threeStageWordSample_boundaryModel {Q : Type} [Fintype Q] [DecidableEq Q]
    {δ : Q → Bool → Q} {s : Q} {F : Finset Q} {T M R : ℕ} {ε : ℝ}
    (B : TerminalWordBoundaryModel δ s F T M R ε) (e : Q → Bits M ≃ Bits M) :
    threeStageWordSample δ s (fun seed => (B.head seed).val) e B.tail =
      terminalWordModelSample B (fun q => e q) := rfl

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_BoundaryLookupPolynomial
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

theorem logInv_accuracy_ratio_bound (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    logInv ε ≤ Real.log ((n + 1 : ℕ) / ε) / Real.log 2 := by
  apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  apply Real.log_le_log (by positivity)
  exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.succ_pos n : (1 : ℝ) ≤ (n + 1 : ℕ)) hε.le

/-- Both boundary seed length and its full truth-table cost have one
polynomial bound, fixed before the accuracy, full length or local seed. -/
theorem logarithmic_boundary_lookup_polynomial (K : ℝ) (hK : 0 < K) :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (n a : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 / 2 → (a : ℝ) ≤ K * logInv ε →
        (a + 1 : ℕ) ≤ C * (((n + 1 : ℕ) : ℝ) / ε) ^ k ∧
        (boundaryLookupCost a : ℝ) ≤ C * (((n + 1 : ℕ) : ℝ) / ε) ^ k := by
  let A := K / Real.log 2
  have hA : 0 < A := div_pos hK (Real.log_pos (by norm_num))
  obtain ⟨Cp, kp, hCp, hpow⟩ := exponential_logarithmic_cutoff_bound 2 (by norm_num) A 1
  let C := (A + 2) + (3 * Cp * (A + 2) + 1)
  refine ⟨C, kp + 1, by dsimp [C]; positivity, ?_⟩
  intro n a ε hε hεle ha
  let X : ℝ := (n + 1 : ℕ) / ε
  have hX : 1 ≤ X := accuracy_ratio_ge_one n hε (by linarith)
  have hXa : X ≤ X ^ (kp + 1) := by
    simpa only [pow_one] using pow_le_pow_right₀ hX (show 1 ≤ kp + 1 by omega)
  have hXpow : 1 ≤ X ^ (kp + 1) := one_le_pow₀ hX
  have halog : (a : ℝ) ≤ A * Real.log X + 1 := by
    have h := mul_le_mul_of_nonneg_left (logInv_accuracy_ratio_bound n hε) hK.le
    change K * logInv ε ≤ K * (Real.log X / Real.log 2) at h
    dsimp only [A]
    nlinarith only [ha, h, show K * (Real.log X / Real.log 2) = (K / Real.log 2) * Real.log X by ring]
  have hal : (a + 1 : ℕ) ≤ (A + 2) * X := by
    simpa only [show A + 1 + 1 = A + 2 by ring] using
      cutoff_length_accuracy_bound n a A 1 ε hA (by norm_num) hε (by linarith) halog
  have hapow : (2 : ℝ) ^ a ≤ Cp * X ^ kp :=
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show a ≤ 2 * a + 1 by omega)).trans
      (hpow X hX a halog)
  have hcost : (boundaryLookupCost a : ℝ) ≤ (3 * Cp * (A + 2) + 1) * X ^ (kp + 1) := by
    have hlin : (3 * a + 2 : ℕ) ≤ 3 * (A + 2) * X := by
      push_cast at hal ⊢
      linarith
    have hm := mul_le_mul hapow hlin (by positivity) (by positivity)
    have he : (Cp * X ^ kp) * (3 * (A + 2) * X) =
        3 * Cp * (A + 2) * X ^ (kp + 1) := by rw [pow_succ]; ring
    rw [he] at hm
    push_cast at hm
    unfold boundaryLookupCost
    push_cast
    nlinarith only [hm, hXpow]
  refine ⟨hal.trans ((mul_le_mul_of_nonneg_left hXa (by positivity)).trans ?_), hcost.trans ?_⟩
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    dsimp only [C]
    exact le_add_of_nonneg_right (by positivity)
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    dsimp only [C]
    linarith

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_NonterminalMatrix
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

/-- Delete all edges incident to terminal states, retaining the ambient
finite state type and every surviving weight. No row is renormalized. -/
def nonterminalMatrix {Q : Type} (W : Matrix Q Q ℝ) : Matrix Q Q ℝ := by
  classical
  exact fun x y => if ¬ IsGraphTerminal (fun i j => 0 < W i j) x ∧
    ¬ IsGraphTerminal (fun i j => 0 < W i j) y then W x y else 0

theorem nonterminalMatrix_nonneg {Q : Type} (W : Matrix Q Q ℝ)
    (hW : ∀ x y, 0 ≤ W x y) (x y : Q) : 0 ≤ nonterminalMatrix W x y := by
  classical
  unfold nonterminalMatrix
  split_ifs <;> simp_all

theorem nonterminalMatrix_le {Q : Type} (W : Matrix Q Q ℝ)
    (hW : ∀ x y, 0 ≤ W x y) (x y : Q) : nonterminalMatrix W x y ≤ W x y := by
  classical
  unfold nonterminalMatrix
  split_ifs <;> simp_all

theorem nonterminalMatrix_zero_one {Q : Type} (W : Matrix Q Q ℝ)
    (h01 : ∀ x y, W x y = 0 ∨ W x y = 1) (x y : Q) :
    nonterminalMatrix W x y = 0 ∨ nonterminalMatrix W x y = 1 := by
  classical
  unfold nonterminalMatrix
  split_ifs
  · exact h01 x y
  · exact Or.inl rfl

theorem nonterminalMatrix_pos_iff {Q : Type} (W : Matrix Q Q ℝ) (x y : Q) :
    0 < nonterminalMatrix W x y ↔
      ¬ IsGraphTerminal (fun i j => 0 < W i j) x ∧
      ¬ IsGraphTerminal (fun i j => 0 < W i j) y ∧ 0 < W x y := by
  classical
  unfold nonterminalMatrix
  split_ifs <;> simp_all

theorem nonterminalMatrix_reach_projects {Q : Type} (W : Matrix Q Q ℝ) {x y : Q}
    (h : Relation.ReflTransGen (fun i j => 0 < nonterminalMatrix W i j) x y) :
    Relation.ReflTransGen (fun i j => 0 < W i j) x y :=
  Relation.ReflTransGen.mono (fun i j hij => ((nonterminalMatrix_pos_iff W i j).mp hij).2.2) x y h



theorem nonterminalMatrix_cyclic_representative {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (s : Q)
    (hc : CyclicSCC (nonterminalMatrix W) s) :
    ¬ IsGraphTerminal (fun i j => 0 < W i j) s := by
  obtain ⟨y, hy⟩ := irreducible_row_positive (sccMatrix (nonterminalMatrix W) s)
    (cyclic_sccMatrix_irreducible (nonterminalMatrix W) (nonterminalMatrix_nonneg W hW) s hc)
    ⟨s, rfl⟩
  exact ((nonterminalMatrix_pos_iff W s y.val).mp hy).1

/-- Any SCC remaining after deletion has an original outgoing edge
outside that remaining SCC. Otherwise its representative was terminal. -/
theorem nonterminalMatrix_scc_exit {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (s : Q) (hs : ¬ IsGraphTerminal (fun i j => 0 < W i j) s) :
    ∃ (x : SCCState (nonterminalMatrix W) s) (y : Q), 0 < W x.val y ∧
      graphComponent (fun i j => 0 < nonterminalMatrix W i j) y ≠
        graphComponent (fun i j => 0 < nonterminalMatrix W i j) s := by
  classical
  by_contra hn
  push Not at hn
  apply hs
  apply graphTerminal_of_closed_class (fun i j => 0 < W i j) s
    (fun x => graphComponent (fun i j => 0 < nonterminalMatrix W i j) x =
      graphComponent (fun i j => 0 < nonterminalMatrix W i j) s) rfl
  · intro x y hx hxy
    exact hn ⟨x, hx⟩ y hxy
  · intro y hy
    exact nonterminalMatrix_reach_projects W ((graphComponent_eq_iff _ y s).mp hy).1

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_NonterminalSubcritical
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

theorem finite_subtype_sum_le {Q : Type} [Fintype Q] (P : Q → Prop)
    [DecidablePred P] (f : Q → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ x : {x // P x}, f x.val) ≤ ∑ x, f x := by
  classical
  let g : {x // P x} → Q := Subtype.val
  calc
    _ = ∑ x ∈ Finset.univ.image g, f x :=
      (Finset.sum_image (fun _ _ _ _ he => Subtype.val_injective he)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hf x)

theorem finite_subtype_sum_lt_of_missing {Q : Type} [Fintype Q] (P : Q → Prop)
    [DecidablePred P] (f : Q → ℝ) (hf : ∀ x, 0 ≤ f x)
    (y : Q) (hy : ¬ P y) (hfy : 0 < f y) :
    (∑ x : {x // P x}, f x.val) < ∑ x, f x := by
  classical
  let g : {x // P x} → Q := Subtype.val
  have hnot : y ∉ Finset.univ.image g := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro x hxy
    exact hy (hxy ▸ x.property)
  calc
    _ = ∑ x ∈ Finset.univ.image g, f x :=
      (Finset.sum_image (fun _ _ _ _ he => Subtype.val_injective he)).symm
    _ < _ := Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ y)
      hnot hfy (fun x _ _ => hf x)

theorem nonterminal_scc_rows_le {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (s : Q)
    (x : SCCState (nonterminalMatrix W) s) :
    (∑ y, sccMatrix (nonterminalMatrix W) s x y) ≤ ∑ y, W x.val y := by
  classical
  calc
    _ ≤ ∑ y : SCCState (nonterminalMatrix W) s, W x.val y.val :=
      Finset.sum_le_sum (fun y _ => nonterminalMatrix_le W hW x.val y.val)
    _ ≤ _ := finite_subtype_sum_le _ (W x.val) (hW x.val)

theorem nonterminal_scc_strict_row {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (s : Q)
    (hs : ¬ IsGraphTerminal (fun i j => 0 < W i j) s) :
    ∃ x : SCCState (nonterminalMatrix W) s,
      (∑ y, sccMatrix (nonterminalMatrix W) s x y) < ∑ y, W x.val y := by
  classical
  obtain ⟨x, y, hxy, hy⟩ := nonterminalMatrix_scc_exit W s hs
  refine ⟨x, ?_⟩
  calc
    _ ≤ ∑ y : SCCState (nonterminalMatrix W) s, W x.val y.val :=
      Finset.sum_le_sum (fun y _ => nonterminalMatrix_le W hW x.val y.val)
    _ < _ := finite_subtype_sum_lt_of_missing _ (W x.val) (hW x.val) y hy hxy

/-- Every remaining cyclic SCC has a strict row defect relative to the
original common row sum. Positive left Perron vectors transfer it to the
actual model eigenvalue used in the circuit construction. -/
theorem nonterminal_scc_model_rate_lt {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (c : ℝ)
    (hrows : ∀ x, ∑ y, W x y = c) (s : Q)
    (hc : CyclicSCC (nonterminalMatrix W) s)
    (model : SCCPeriodicModel (nonterminalMatrix W) s) : model.lam < c := by
  classical
  letI : Nonempty (SCCState (nonterminalMatrix W) s) := ⟨⟨s, rfl⟩⟩
  obtain ⟨μ, l, u, _, hl, _, _, _, hleft⟩ :=
    irreducible_perron_vectors (sccMatrix (nonterminalMatrix W) s)
      (cyclic_sccMatrix_irreducible (nonterminalMatrix W) (nonterminalMatrix_nonneg W hW) s hc)
  have he : μ = model.lam := positive_left_right_eigenvalue_eq
    (sccMatrix (nonterminalMatrix W) s) μ model.lam l model.right hl model.right_pos hleft
      (fun x => congrFun (sccPeriodicModel_eigenvector (nonterminalMatrix W) s model) x)
  rw [← he]
  apply perron_strict_row_bound (sccMatrix (nonterminalMatrix W) s) μ l hl hleft c
  · intro x
    exact (nonterminal_scc_rows_le W hW s x).trans_eq (hrows x.val)
  · obtain ⟨x, hx⟩ := nonterminal_scc_strict_row W hW s
      (nonterminalMatrix_cyclic_representative W hW s hc)
    exact ⟨x, hx.trans_eq (hrows x.val)⟩

/-- The completed subcritical construction applies to the graph obtained
by removing terminal SCCs of a two-outgoing-edge zero-one graph. -/
theorem nonterminal_accepted_graph_sampling {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (W : Matrix Q Q ℝ) (h01 : ∀ x y, W x y = 0 ∨ W x y = 1)
    (hrows : ∀ x, ∑ y, W x y = 2) :
    ∃ D C k : ℕ, ∀ (s : Q) (F : Finset Q) (n : ℕ),
      0 < ∑ γ : Fin (n + 1) → Q, acceptedGraphWeight (nonterminalMatrix W) s F γ →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ S : Circuit (Fin (n + 1) × Q),
        S.depth ≤ D ∧
        (S.size : ℝ) ≤ (C : ℝ) * (((n + 1 : ℕ) : ℝ) / ε) ^ k ∧
        (S.randomBits : ℝ) ≤ n + (C : ℝ) * logInv ε ∧
        SupportPreserving S graphPathEncode
          (normalizeWeights (acceptedGraphWeight (nonterminalMatrix W) s F)) ∧
        tv (mass S graphPathEncode)
          (normalizeWeights (acceptedGraphWeight (nonterminalMatrix W) s F)) ≤ ε := by
  classical
  have hW : ∀ x y, 0 ≤ W x y := by
    intro x y
    rcases h01 x y with h | h <;> simp [h]
  let models : ∀ s : CyclicSCCIndex (nonterminalMatrix W),
      SCCPeriodicModel (nonterminalMatrix W) s.val := fun s =>
    Classical.choice (cyclic_scc_periodic_model_exists (nonterminalMatrix W)
      (nonterminalMatrix_nonneg W hW) s.val s.property)
  exact subcritical_accepted_graph_sampling_of_rates (nonterminalMatrix W)
    (nonterminalMatrix_zero_one W h01) models
    (fun s => nonterminal_scc_model_rate_lt W hW 2 hrows s.val s.property (models s))

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_NonterminalAcceptedSampling
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

def AcceptedPathsAvoidTerminal {Q : Type} [DecidableEq Q] (W : Matrix Q Q ℝ)
    (s : Q) (F : Finset Q) (n : ℕ) : Prop :=
  ∀ γ : Fin (n + 1) → Q, 0 < acceptedGraphWeight W s F γ →
    ∀ i, ¬ IsGraphTerminal (fun x y => 0 < W x y) (γ i)

/-- It suffices that every accepting endpoint is nonterminal: an earlier
visit to a terminal SCC would force the endpoint to be terminal as well. -/
theorem acceptedPathsAvoidTerminal_of_endpoints {Q : Type} [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (s : Q) (F : Finset Q) (n : ℕ)
    (hend : ∀ γ : Fin (n + 1) → Q, 0 < acceptedGraphWeight W s F γ →
      ¬ IsGraphTerminal (fun x y => 0 < W x y) (γ (Fin.last n))) :
    AcceptedPathsAvoidTerminal W s F n := by
  intro γ hγ i hi
  have hp := (acceptedGraphWeight_pos_iff W s F γ).mp hγ
  have hg := (edgePathWeight_pos_iff W hW γ).mp hp.2.2
  exact hend γ hγ (graphTerminal_path_suffix _ γ hg i (Fin.last n) (Fin.le_last i) hi)

theorem nonterminal_edgePathWeight_le {Q : Type} (W : Matrix Q Q ℝ)
    (hW : ∀ x y, 0 ≤ W x y) {n : ℕ} (γ : Fin (n + 1) → Q) :
    edgePathWeight (nonterminalMatrix W) γ ≤ edgePathWeight W γ := by
  simp only [edgePathWeight, finitePathWeight, one_mul]
  exact Finset.prod_le_prod (fun i _ => nonterminalMatrix_nonneg W hW _ _)
    (fun i _ => nonterminalMatrix_le W hW _ _)

theorem nonterminal_edgePathWeight_eq {Q : Type} (W : Matrix Q Q ℝ)
    {n : ℕ} (γ : Fin (n + 1) → Q)
    (hγ : ∀ i, ¬ IsGraphTerminal (fun x y => 0 < W x y) (γ i)) :
    edgePathWeight (nonterminalMatrix W) γ = edgePathWeight W γ := by
  classical
  simp only [edgePathWeight, finitePathWeight, one_mul]
  apply Finset.prod_congr rfl
  intro i _
  exact if_pos ⟨hγ i.castSucc, hγ i.succ⟩

theorem nonterminal_acceptedGraphWeight_le {Q : Type} [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (s : Q) (F : Finset Q)
    {n : ℕ} (γ : Fin (n + 1) → Q) :
    acceptedGraphWeight (nonterminalMatrix W) s F γ ≤ acceptedGraphWeight W s F γ := by
  unfold acceptedGraphWeight
  split_ifs
  · exact nonterminal_edgePathWeight_le W hW γ
  · exact le_rfl

/-- Deleting terminal SCCs preserves the entire accepted-path weight
function whenever the accepting slice avoids them. This includes n=0;
the deletion alone is not claimed to remove zero-length terminal paths. -/
theorem nonterminal_acceptedGraphWeight_eq {Q : Type} [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (s : Q) (F : Finset Q) (n : ℕ)
    (havoid : AcceptedPathsAvoidTerminal W s F n) :
    acceptedGraphWeight (n := n) (nonterminalMatrix W) s F = acceptedGraphWeight W s F := by
  funext γ
  by_cases hp : 0 < acceptedGraphWeight W s F γ
  · have he := nonterminal_edgePathWeight_eq W γ (havoid γ hp)
    simp only [acceptedGraphWeight, he]
  · have hz : acceptedGraphWeight W s F γ = 0 :=
      le_antisymm (le_of_not_gt hp) (acceptedGraphWeight_nonneg W hW s F γ)
    apply le_antisymm (nonterminal_acceptedGraphWeight_le W hW s F γ)
    rw [hz]
    exact acceptedGraphWeight_nonneg (nonterminalMatrix W) (nonterminalMatrix_nonneg W hW) s F γ

/-- The zero-terminal-visit branch already has all the required circuit
and random-bit bounds. Its constants precede lengths and accuracy; only
the source's residue/density classification remains to supply havoid. -/
theorem terminal_avoiding_accepted_graph_sampling {Q : Type} [Fintype Q]
    [DecidableEq Q] [Nonempty Q]
    (W : Matrix Q Q ℝ) (h01 : ∀ x y, W x y = 0 ∨ W x y = 1)
    (hrows : ∀ x, ∑ y, W x y = 2) :
    ∃ D C k : ℕ, ∀ (s : Q) (F : Finset Q) (n : ℕ),
      AcceptedPathsAvoidTerminal W s F n →
      0 < ∑ γ : Fin (n + 1) → Q, acceptedGraphWeight W s F γ →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ S : Circuit (Fin (n + 1) × Q),
        S.depth ≤ D ∧
        (S.size : ℝ) ≤ (C : ℝ) * (((n + 1 : ℕ) : ℝ) / ε) ^ k ∧
        (S.randomBits : ℝ) ≤ n + (C : ℝ) * logInv ε ∧
        SupportPreserving S graphPathEncode (normalizeWeights (acceptedGraphWeight W s F)) ∧
        tv (mass S graphPathEncode) (normalizeWeights (acceptedGraphWeight W s F)) ≤ ε := by
  have hW : ∀ x y, 0 ≤ W x y := by
    intro x y
    rcases h01 x y with h | h <;> simp [h]
  obtain ⟨D, C, k, hall⟩ := nonterminal_accepted_graph_sampling W h01 hrows
  refine ⟨D, C, k, ?_⟩
  intro s F n havoid hZ ε hε hεle
  have he := nonterminal_acceptedGraphWeight_eq W hW s F n havoid
  have hZ' : 0 < ∑ γ : Fin (n + 1) → Q, acceptedGraphWeight (nonterminalMatrix W) s F γ := by
    rw [he]
    exact hZ
  have h := hall s F n hZ' ε hε hεle
  rw [he] at h
  exact h

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_PositiveDensityWordCircuit
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- The positive-density branch is now an actual bounded-depth circuit
with the original support and full-word TV guarantees. The explicit size
bound contains only short-boundary truth tables and polynomial middle
formulas; uniform polynomial closure and short-length cases are separate. -/
theorem positive_density_word_circuit_explicit {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (δ : Q → Bool → Q) (c : ℝ) (hc : 0 < c) :
    ∃ D C k : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ T R : ℕ, 0 < T ∧ 0 < R ∧ (T + R : ℕ) ≤ K * logInv ε ∧
        ∀ (s : Q) (F : Finset Q) (M : ℕ),
          c ≤ kernelSetMass (fairWordKernel δ) F (T + (M + R)) s →
          ∃ S : Circuit (Fin (T + (M + R))),
            S.randomBits = binaryBoundarySeed T ε + (M + binaryBoundarySeed R ε) ∧
            S.depth ≤ D + 7 ∧
            S.size ≤ binaryBoundarySeed T ε + (M + binaryBoundarySeed R ε) +
              (T + (M + R)) * (threeStageWordFormulaCost (Fintype.card Q)
                (binaryBoundarySeed T ε) (binaryBoundarySeed R ε) (C * (M + 1) ^ k) + 1) ∧
            (S.randomBits : ℝ) ≤ (T + (M + R) : ℕ) + 8 * logInv ε ∧
            SupportPreserving S (fun w : Bits (T + (M + R)) => w)
              (normalizeWeights (fairAcceptedWordWeight δ s F)) ∧
            tv (mass S (fun w : Bits (T + (M + R)) => w))
              (normalizeWeights (fairAcceptedWordWeight δ s F)) ≤ ε := by
  obtain ⟨D, C, k, hmiddle⟩ := exact_finite_state_run_formulas δ
  obtain ⟨K, hK, hsampler⟩ := positive_density_word_seed_sampling δ c hc
  refine ⟨D, C, k, K, hK, ?_⟩
  intro ε hε hεle
  obtain ⟨T, R, hT, hR, hlen, hdraw⟩ := hsampler ε hε hεle
  refine ⟨T, R, hT, hR, hlen, ?_⟩
  intro s F M hacc
  obtain ⟨B, hbitsbound, hcorrect⟩ := hdraw s F M hacc
  obtain ⟨middle, hD, hC, e, he⟩ := hmiddle M
  obtain ⟨hsupport, herror⟩ := hcorrect (fun q => e q) (fun q => finiteSeedLaw_word_equiv (e q))
  obtain ⟨S, hbits, heval, hdepth, hsize⟩ := three_stage_word_circuit δ s T M R
    (binaryBoundarySeed T ε) (binaryBoundarySeed R ε) D (C * (M + 1) ^ k)
    (fun seed => (B.head seed).val) e B.tail middle hD hC he
  have hev : ∀ seed, S.eval (fun j => seed (Fin.cast hbits j)) =
      terminalWordModelSample B (fun q => e q) seed := by
    intro seed
    rw [heval, threeStageWordSample_boundaryModel]
  have hZ : 0 < ∑ w : Bits (T + (M + R)), fairAcceptedWordWeight δ s F w := by
    rw [fairAcceptedWordWeight_sum]
    exact hc.trans_le hacc
  refine ⟨S, hbits, hdepth, hsize, ?_, ?_, ?_⟩
  · rwa [hbits]
  · apply sampler_circuit_support (terminalWordModelSample B (fun q => e q))
      (fun w => w) _ S hbits hev
    intro seed
    exact div_pos (hsupport seed) hZ
  · rw [sampler_circuit_mass (terminalWordModelSample B (fun q => e q))
      (fun w => w) (fun _ _ h => h) S hbits hev]
    exact herror

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ThreeStageSizePolynomial
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

def threeStageWordSize (q n M a c B : ℕ) : ℕ :=
  a + (M + c) + n * (threeStageWordFormulaCost q a c B + 1)

theorem threeStageWordSize_envelope (q n M a c B : ℕ) (Z : ℝ) (hZ : 1 ≤ Z)
    (hn : (n : ℝ) ≤ Z) (hM : (M : ℝ) ≤ Z) (ha : (a : ℝ) ≤ Z)
    (hc : (c : ℝ) ≤ Z) (hB : (B : ℝ) ≤ Z)
    (hH : (boundaryLookupCost a : ℝ) ≤ Z) (hL : (boundaryLookupCost c : ℝ) ≤ Z) :
    (threeStageWordSize q n M a c B : ℝ) ≤ (6 * (q + 1 : ℝ) ^ 2 + 1) * Z ^ 2 := by
  let H : ℝ := boundaryLookupCost a
  let L : ℝ := boundaryLookupCost c
  let U : ℝ := q * (H + B + 4) + 1
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have hU : U ≤ (6 * q + 1) * Z := by
    calc
      _ ≤ q * (Z + Z + 4 * Z) + Z := by dsimp only [U]; gcongr <;> linarith
      _ = _ := by ring
  have hcost : (threeStageWordFormulaCost q a c B : ℝ) + 1 ≤
      (6 * (q : ℝ) ^ 2 + 12 * q + 4) * Z := by
    change (↑(boundaryLookupCost a + (q * (boundaryLookupCost a + B + 4) + 1) +
      (q * ((q * (boundaryLookupCost a + B + 4) + 1) + boundaryLookupCost c + 4) + 1)) : ℝ) + 1 ≤ _
    push_cast
    change H + U + ((q : ℝ) * (U + L + 4) + 1) + 1 ≤ _
    calc
      _ ≤ Z + (6 * q + 1) * Z +
        ((q : ℝ) * ((6 * q + 1) * Z + Z + 4 * Z) + Z) + Z := by gcongr <;> linarith
      _ = _ := by ring
  have hm := mul_le_mul hn hcost (by positivity) hZ0
  have hsmall : Z ≤ Z ^ 2 := by nlinarith
  unfold threeStageWordSize
  push_cast
  nlinarith only [hm, ha, hM, hc, hsmall]

/-- Uniform polynomial closure of the explicit positive-branch circuit
size. The coefficient and exponent precede all lengths and accuracies. -/
theorem threeStageWordSize_polynomial (q C k : ℕ) (K : ℝ) (hK : 0 < K) :
    ∃ (Cp : ℝ) (kp : ℕ), 0 < Cp ∧
      ∀ (T M R : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
        (T + R : ℕ) ≤ K * logInv ε →
        (threeStageWordSize q (T + (M + R)) M (binaryBoundarySeed T ε)
          (binaryBoundarySeed R ε) (C * (M + 1) ^ k) : ℝ) ≤
            Cp * (((T + (M + R) + 1 : ℕ) : ℝ) / ε) ^ kp := by
  obtain ⟨Cb, kb, hCb, hb⟩ := logarithmic_boundary_lookup_polynomial (K + 4) (by linarith)
  let E := max kb (k + 1)
  let V : ℝ := Cb + C + 1
  refine ⟨(6 * (q + 1 : ℝ) ^ 2 + 1) * V ^ 2, 2 * E, by dsimp [V]; positivity, ?_⟩
  intro T M R ε hε hεle hTR
  let n := T + (M + R)
  let X : ℝ := (n + 1 : ℕ) / ε
  let Z := V * X ^ E
  have hX : 1 ≤ X := accuracy_ratio_ge_one n hε (by linarith)
  have hE : 1 ≤ E := (by omega : 1 ≤ k + 1).trans (Nat.le_max_right _ _)
  have hXE : X ≤ X ^ E := by simpa only [pow_one] using pow_le_pow_right₀ hX hE
  have hpow : 1 ≤ X ^ E := one_le_pow₀ hX
  have hV : 1 ≤ V := by dsimp only [V]; linarith [Nat.cast_nonneg C (α := ℝ)]
  have hZ : 1 ≤ Z := one_le_mul_of_one_le_of_one_le hV hpow
  have hXZ : X ≤ Z := hXE.trans (le_mul_of_one_le_left (by positivity) hV)
  have hn : (n : ℝ) ≤ Z := by
    exact (Nat.cast_le.mpr (Nat.le_succ n)).trans
      ((accuracy_ratio_controls_length n hε (by linarith)).1.trans hXZ)
  have hM : (M : ℝ) ≤ Z := (Nat.cast_le.mpr (by dsimp [n]; omega : M ≤ n)).trans hn
  have hlog := logInv_nonneg_of_le_one ε hε (by linarith)
  have ha : (binaryBoundarySeed T ε : ℝ) ≤ (K + 4) * logInv ε := by
    have h := binaryBoundarySeed_bound T hε hεle
    push_cast at hTR
    nlinarith
  have hc : (binaryBoundarySeed R ε : ℝ) ≤ (K + 4) * logInv ε := by
    have h := binaryBoundarySeed_bound R hε hεle
    push_cast at hTR
    nlinarith
  obtain ⟨haL, haH⟩ := hb n (binaryBoundarySeed T ε) ε hε hεle ha
  obtain ⟨hcL, hcH⟩ := hb n (binaryBoundarySeed R ε) ε hε hεle hc
  have hboundary : Cb * X ^ kb ≤ Z := by
    change Cb * X ^ kb ≤ V * X ^ E
    apply mul_le_mul (by dsimp only [V]; linarith [Nat.cast_nonneg C (α := ℝ)])
      (pow_le_pow_right₀ hX (Nat.le_max_left _ _)) (by positivity) (by dsimp only [V]; positivity)
  have haZ : (binaryBoundarySeed T ε : ℝ) ≤ Z := by
    have h := haL.trans hboundary
    push_cast at h
    linarith
  have hcZ : (binaryBoundarySeed R ε : ℝ) ≤ Z := by
    have h := hcL.trans hboundary
    push_cast at h
    linarith
  have hB : (C * (M + 1) ^ k : ℕ) ≤ Z := by
    have hmX : ((M + 1 : ℕ) : ℝ) ≤ X :=
      (Nat.cast_le.mpr (by dsimp [n]; omega : M + 1 ≤ n + 1)).trans
        (accuracy_ratio_controls_length n hε (by linarith)).1
    push_cast
    push_cast at hmX
    change (C : ℝ) * (M + 1 : ℝ) ^ k ≤ V * X ^ E
    apply mul_le_mul (by dsimp only [V]; linarith)
      ((pow_le_pow_left₀ (by positivity) hmX k).trans
        (pow_le_pow_right₀ hX (show k ≤ E by dsimp [E]; omega)))
      (by positivity) (by dsimp only [V]; positivity)
  have hsize := threeStageWordSize_envelope q n M (binaryBoundarySeed T ε) (binaryBoundarySeed R ε)
    (C * (M + 1) ^ k) Z hZ hn hM haZ hcZ hB (haH.trans hboundary) (hcH.trans hboundary)
  apply hsize.trans_eq
  dsimp only [Z, X, n]
  rw [mul_pow, ← pow_mul, Nat.mul_comm E 2]
  ring

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ShortWordCircuit
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- Direct support-preserving rounding at logarithmic word lengths is an
actual depth-three circuit. The distribution may be arbitrary, so this
also covers every bounded exceptional length and the empty word. -/
theorem short_word_rounding_circuit (K : ℝ) (hK : 0 < K) :
    ∃ C k : ℕ, ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 / 2 →
      (n : ℝ) ≤ K * logInv ε →
      ∀ p : Bits n → ℝ, (∀ w, 0 ≤ p w) → (∑ w, p w = 1) →
        ∃ S : Circuit (Fin n), S.depth ≤ 3 ∧
          (S.size : ℝ) ≤ C * (((n + 1 : ℕ) : ℝ) / ε) ^ k ∧
          (S.randomBits : ℝ) ≤ n + C * logInv ε ∧
          SupportPreserving S (fun w : Bits n => w) p ∧ tv (mass S (fun w : Bits n => w)) p ≤ ε := by
  obtain ⟨Cb, kb, hCb, hb⟩ := logarithmic_boundary_lookup_polynomial (K + 4) (by linarith)
  let C : ℕ := ⌈2 * Cb + 1⌉₊ + 4
  have hC : 2 * Cb + 1 ≤ (C : ℝ) := by
    have h := Nat.le_ceil (2 * Cb + 1)
    dsimp only [C]
    push_cast
    linarith
  have hC4 : (4 : ℝ) ≤ C := by exact_mod_cast (show 4 ≤ C by dsimp [C]; omega)
  refine ⟨C, kb + 1, ?_⟩
  intro n ε hε hεle hn p hp hsum
  obtain ⟨f, hf, herr⟩ := binary_boundary_rounding p hp hsum n (by simp [Bits]) ε hε
  let a := binaryBoundarySeed n ε
  obtain ⟨S, hbits, he, hD, hsize⟩ := local_maps_circuit
    (fun (_ : Fin n) (j : Fin a) => j) (fun i seed => f seed i)
  have hev : ∀ seed, S.eval (fun j => seed (Fin.cast hbits j)) = f seed := by
    intro seed
    funext i
    exact he seed i
  have hmass := sampler_circuit_mass f (fun w => w) (fun _ _ h => h) S hbits hev
  refine ⟨S, hD, ?_, ?_, sampler_circuit_support f (fun w => w) p S hbits hev hf, ?_⟩
  · let X : ℝ := (n + 1 : ℕ) / ε
    have hX : 1 ≤ X := accuracy_ratio_ge_one n hε (by linarith)
    have ha : (a : ℝ) ≤ (K + 4) * logInv ε := by
      have h := binaryBoundarySeed_bound n hε hεle
      change (a : ℝ) ≤ _ at h
      nlinarith
    obtain ⟨haL, haH⟩ := hb n a ε hε hεle ha
    have ha' : (a : ℝ) ≤ Cb * X ^ kb := (Nat.cast_le.mpr (Nat.le_succ a)).trans haL
    have hnX : (n : ℝ) ≤ X :=
      (Nat.cast_le.mpr (Nat.le_succ n)).trans (accuracy_ratio_controls_length n hε (by linarith)).1
    have hpow : X ^ kb ≤ X ^ (kb + 1) := pow_le_pow_right₀ hX (by omega)
    have hXp : X ≤ X ^ (kb + 1) := by
      simpa only [pow_one] using pow_le_pow_right₀ hX (show 1 ≤ kb + 1 by omega)
    have hH : (boundaryLookupCost a : ℝ) + 1 ≤ Cb * X ^ kb + 1 := by
      change (boundaryLookupCost a : ℝ) ≤ Cb * X ^ kb at haH
      linarith
    have hm := mul_le_mul hnX hH (by positivity) (by positivity)
    have hs : (S.size : ℝ) ≤ (a : ℝ) + n * ((boundaryLookupCost a : ℝ) + 1) := by
      exact_mod_cast hsize
    have heq : X * (Cb * X ^ kb + 1) = Cb * X ^ (kb + 1) + X := by rw [pow_succ]; ring
    change (n : ℝ) * ((boundaryLookupCost a : ℝ) + 1) ≤ X * (Cb * X ^ kb + 1) at hm
    rw [heq] at hm
    have ha'' := ha'.trans (mul_le_mul_of_nonneg_left hpow hCb.le)
    have hbnd : (S.size : ℝ) ≤ (2 * Cb + 1) * X ^ (kb + 1) := by nlinarith only [hs, hm, ha'', hXp]
    exact hbnd.trans (mul_le_mul_of_nonneg_right hC (by positivity))
  · rw [hbits]
    have hb := binaryBoundarySeed_bound n hε hεle
    change (a : ℝ) ≤ _ at hb
    have hh := mul_le_mul_of_nonneg_right hC4 (logInv_nonneg_of_le_one ε hε (by linarith))
    linarith
  · rw [hmass]
    exact herr.trans (by linarith)

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_PositiveDensityWordSampling
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- Complete positive-density branch, at every length including zero.
The depth, natural polynomial constants and coefficient-one random-bit
constant are fixed before starts, accepting sets, lengths and accuracy. -/
theorem positive_density_word_sampling {Q : Type} [Fintype Q] [DecidableEq Q] [Nonempty Q]
    (δ : Q → Bool → Q) (c : ℝ) (hc : 0 < c) :
    ∃ D C k : ℕ, ∀ (s : Q) (F : Finset Q) (n : ℕ),
      c ≤ kernelSetMass (fairWordKernel δ) F n s →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ S : Circuit (Fin n),
        S.depth ≤ D ∧ (S.size : ℝ) ≤ C * (((n + 1 : ℕ) : ℝ) / ε) ^ k ∧
        (S.randomBits : ℝ) ≤ n + C * logInv ε ∧
        SupportPreserving S (fun w : Bits n => w) (normalizeWeights (fairAcceptedWordWeight δ s F)) ∧
        tv (mass S (fun w : Bits n => w)) (normalizeWeights (fairAcceptedWordWeight δ s F)) ≤ ε := by
  obtain ⟨D, C₀, k₀, K, hK, hlong⟩ := positive_density_word_circuit_explicit δ c hc
  obtain ⟨Cp, kp, hCp, hpoly⟩ := threeStageWordSize_polynomial (Fintype.card Q) C₀ k₀ K hK
  obtain ⟨Cs, ks, hshort⟩ := short_word_rounding_circuit K hK
  let C : ℕ := ⌈Cp⌉₊ + Cs + 8
  let k := max kp ks
  have hCpC : Cp ≤ (C : ℝ) := by
    have h := Nat.le_ceil Cp
    dsimp only [C]
    push_cast
    linarith [Nat.cast_nonneg Cs (α := ℝ)]
  have hCsC : (Cs : ℝ) ≤ C := by exact_mod_cast (show Cs ≤ C by dsimp [C]; omega)
  have h8C : (8 : ℝ) ≤ C := by exact_mod_cast (show 8 ≤ C by dsimp [C]; omega)
  refine ⟨D + 7, C, k, ?_⟩
  intro s F n hacc ε hε hεle
  obtain ⟨T, R, _, _, hlen, hsample⟩ := hlong ε hε hεle
  have hX : 1 ≤ ((n + 1 : ℕ) : ℝ) / ε := accuracy_ratio_ge_one n hε (by linarith)
  have hlog : 0 ≤ logInv ε := logInv_nonneg_of_le_one ε hε (by linarith)
  by_cases hn : T + R ≤ n
  · let M := n - (T + R)
    have hn' : T + (M + R) = n := by dsimp only [M]; omega
    have hacc' : c ≤ kernelSetMass (fairWordKernel δ) F (T + (M + R)) s := by rwa [hn']
    obtain ⟨S, _, hD, hsize, hbits, hs, ht⟩ := hsample s F M hacc'
    have hsz : (S.size : ℝ) ≤ Cp * (((T + (M + R) + 1 : ℕ) : ℝ) / ε) ^ kp :=
      (Nat.cast_le.mpr hsize).trans (hpoly T M R ε hε hεle hlen)
    have hXe : 1 ≤ ((T + (M + R) + 1 : ℕ) : ℝ) / ε := by rwa [hn']
    have hxpow := pow_le_pow_right₀ hXe (Nat.le_max_left kp ks)
    have hsize' : (S.size : ℝ) ≤ C * (((T + (M + R) + 1 : ℕ) : ℝ) / ε) ^ k :=
      hsz.trans (mul_le_mul hCpC hxpow (by positivity) (Nat.cast_nonneg C))
    have hbits' : (S.randomBits : ℝ) ≤ (T + (M + R) : ℕ) + C * logInv ε := by
      have hh := mul_le_mul_of_nonneg_right h8C hlog
      linarith
    let P := fun ℓ : ℕ => ∃ S : Circuit (Fin ℓ), S.depth ≤ D + 7 ∧
      (S.size : ℝ) ≤ C * (((ℓ + 1 : ℕ) : ℝ) / ε) ^ k ∧
      (S.randomBits : ℝ) ≤ ℓ + C * logInv ε ∧
      SupportPreserving S (fun w : Bits ℓ => w) (normalizeWeights (fairAcceptedWordWeight δ s F)) ∧
      tv (mass S (fun w : Bits ℓ => w)) (normalizeWeights (fairAcceptedWordWeight δ s F)) ≤ ε
    have hall : P (T + (M + R)) := ⟨S, hD, hsize', hbits', hs, ht⟩
    exact Eq.mp (congrArg P hn') hall
  · have hnK : (n : ℝ) ≤ K * logInv ε :=
      (Nat.cast_le.mpr (show n ≤ T + R by omega)).trans hlen
    have hZ : 0 < ∑ w : Bits n, fairAcceptedWordWeight δ s F w := by
      rw [fairAcceptedWordWeight_sum]
      exact hc.trans_le hacc
    obtain ⟨S, hD, hsize, hbits, hs, ht⟩ := hshort n ε hε hεle hnK
      (normalizeWeights (fairAcceptedWordWeight δ s F))
      (normalizeWeights_nonneg _ (fairAcceptedWordWeight_nonneg δ s F)) (normalizeWeights_sum _ hZ)
    refine ⟨S, hD.trans (by omega), ?_, ?_, hs, ht⟩
    · exact hsize.trans (mul_le_mul hCsC (pow_le_pow_right₀ hX (Nat.le_max_right kp ks))
        (by positivity) (Nat.cast_nonneg C))
    · have hh := mul_le_mul_of_nonneg_right hCsC hlog
      linarith

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ZeroDensityTerminalAvoidance
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix Topology

theorem acceptedGraphWeight_positive_endpoint_power {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (s : Q) (F : Finset Q)
    {n : ℕ} (γ : Fin (n + 1) → Q) (hγ : 0 < acceptedGraphWeight P s F γ) :
    0 < (P ^ n) s (γ (Fin.last n)) := by
  have hp := (acceptedGraphWeight_pos_iff P s F γ).mp hγ
  have hb : 0 < bridgeWeight P s (γ (Fin.last n)) n γ := by
    simpa only [bridgeWeight, hp.1, and_self, if_true] using hp.2.2
  rw [← bridgePartition_eq_matrix_power P n]
  exact hb.trans_le (Finset.single_le_sum
    (fun z _ => bridgeWeight_nonneg P hP s (γ (Fin.last n)) n z) (Finset.mem_univ γ))

/-- Once a positive trajectory reaches an accepting terminal state, its
acceptance probability stays bounded below along all sufficiently long
extensions by the common period. -/
theorem terminal_acceptance_periodic_lower_bound {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1)
    (p : ℕ) (hid : ∀ x y, (∃ z, 0 < (P ^ p) x z ∧ 0 < (P ^ p) z y) ↔ 0 < (P ^ p) x y)
    (s t : Q) (F : Finset Q) (n : ℕ) (ht : t ∈ F)
    (hterminal : IsGraphTerminal (fun i j => 0 < P i j) t) (hpath : 0 < (P ^ n) s t) :
    ∃ c : ℝ, ∃ J : ℕ, 0 < c ∧ ∀ j, J ≤ j → c ≤ kernelSetMass P F (n + p * j) s := by
  obtain ⟨c, J, hc, hreturn⟩ := terminal_periodic_return_lower_bound P hP hrows p hid t hterminal
  refine ⟨(P ^ n) s t * c, J, mul_pos hpath hc, ?_⟩
  intro j hj
  calc
    _ ≤ (P ^ n) s t * (P ^ (p * j)) t t := mul_le_mul_of_nonneg_left (hreturn j hj) hpath.le
    _ ≤ (P ^ (n + p * j)) s t := by
      rw [pow_add, Matrix.mul_apply]
      exact Finset.single_le_sum (fun z _ => mul_nonneg (Matrix.pow_apply_nonneg hP n s z)
        (Matrix.pow_apply_nonneg hP (p * j) z t)) (Finset.mem_univ t)
    _ ≤ _ := Finset.single_le_sum (fun z _ => Matrix.pow_apply_nonneg hP (n + p * j) s z) ht



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ResidueAcceptanceDichotomy
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

def TerminalAcceptanceResidue {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (s : Q) (F : Finset Q) (p a : ℕ) : Prop :=
  ∃ n : ℕ, n % p = a ∧ ∃ t ∈ F,
    IsGraphTerminal (fun i j => 0 < P i j) t ∧ 0 < (P ^ n) s t

theorem no_terminal_acceptance_residue_avoids {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (s : Q) (F : Finset Q) (p a : ℕ)
    (hno : ¬ TerminalAcceptanceResidue P s F p a) (n : ℕ) (hn : n % p = a) :
    AcceptedPathsAvoidTerminal P s F n := by
  apply acceptedPathsAvoidTerminal_of_endpoints P hP s F n
  intro γ hγ ht
  exact hno ⟨n, hn, γ (Fin.last n), ((acceptedGraphWeight_pos_iff P s F γ).mp hγ).2.1,
    ht, acceptedGraphWeight_positive_endpoint_power P hP s F γ hγ⟩

theorem terminal_acceptance_residue_lower_bound {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1)
    (p : ℕ) (hp : 0 < p)
    (hid : ∀ x y, (∃ z, 0 < (P ^ p) x z ∧ 0 < (P ^ p) z y) ↔ 0 < (P ^ p) x y)
    (s : Q) (F : Finset Q) (a : ℕ) (ha : TerminalAcceptanceResidue P s F p a) :
    ∃ c : ℝ, ∃ N : ℕ, 0 < c ∧
      ∀ n, N ≤ n → n % p = a → c ≤ kernelSetMass P F n s := by
  obtain ⟨b, hb, t, htF, ht, hbt⟩ := ha
  obtain ⟨c, J, hc, hlower⟩ := terminal_acceptance_periodic_lower_bound P hP hrows p hid s t F b htF ht hbt
  refine ⟨c, b + p * J, hc, ?_⟩
  intro n hN hn
  have hbn : b ≤ n := by omega
  have hk : b / p ≤ n / p := Nat.div_le_div_right hbn
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hk
  have hn' : n = b + p * j := by
    have hb' := Nat.mod_add_div b p
    have hn' := Nat.mod_add_div n p
    rw [hb] at hb'
    rw [hn, hj] at hn'
    nlinarith
  have hJ : J ≤ j := by
    rw [hn'] at hN
    have hh : p * J ≤ p * j := Nat.le_of_add_le_add_left hN
    exact Nat.le_of_mul_le_mul_left hh hp
  rw [hn']
  exact hlower j hJ

/-- A direct structural version of the two source cases. For each
residue either all accepting trajectories avoid terminal SCCs, or every
sufficiently large accepting probability has one common positive lower
bound. This suffices for the sampling construction without requiring an
additional proof that the entire sequence of residue limits exists. -/
theorem residue_acceptance_dichotomy {Q : Type} [Fintype Q] [DecidableEq Q]
    (P : Matrix Q Q ℝ) (hP : ∀ x y, 0 ≤ P x y) (hrows : ∀ x, ∑ y, P x y = 1) :
    ∃ p : ℕ, 0 < p ∧
      (∀ x y, (∃ z, 0 < (P ^ p) x z ∧ 0 < (P ^ p) z y) ↔ 0 < (P ^ p) x y) ∧
      ∀ (s : Q) (F : Finset Q), ∃ c : ℝ, ∃ N : ℕ, 0 < c ∧
        ∀ a : Fin p,
          (∀ n, n % p = a.val → AcceptedPathsAvoidTerminal P s F n) ∨
          (∀ n, N ≤ n → n % p = a.val → c ≤ kernelSetMass P F n s) := by
  classical
  obtain ⟨p, hp, hid⟩ := exists_idempotent_matrix_support P hP
  refine ⟨p, hp, hid, ?_⟩
  intro s F
  letI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  have hcases : ∀ a : Fin p, ∃ c : ℝ, ∃ N : ℕ, 0 < c ∧
      ((∀ n, n % p = a.val → AcceptedPathsAvoidTerminal P s F n) ∨
       (∀ n, N ≤ n → n % p = a.val → c ≤ kernelSetMass P F n s)) := by
    intro a
    by_cases ha : TerminalAcceptanceResidue P s F p a.val
    · obtain ⟨c, N, hc, hb⟩ := terminal_acceptance_residue_lower_bound P hP hrows p hp hid s F a.val ha
      exact ⟨c, N, hc, Or.inr hb⟩
    · exact ⟨1, 0, zero_lt_one, Or.inl (no_terminal_acceptance_residue_avoids P hP s F p a.val ha)⟩
  choose c threshold hc hcase using hcases
  obtain ⟨a, _, hmin⟩ := Finset.exists_min_image Finset.univ c Finset.univ_nonempty
  refine ⟨c a, ∑ b, threshold b, hc a, ?_⟩
  intro b
  rcases hcase b with hb | hb
  · exact Or.inl hb
  · right
    intro n hn hmod
    have ht : threshold b ≤ ∑ d, threshold d :=
      Finset.single_le_sum (fun d _ => Nat.zero_le (threshold d)) (Finset.mem_univ b)
    exact (hmin b (Finset.mem_univ b)).trans (hb n (ht.trans hn) hmod)

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_TerminalAvoidingWordSampling
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

/-- Structural zero-density branch. The residue dichotomy supplies this
terminal-avoidance premise directly, without assuming residue limits. -/
theorem terminal_avoiding_labeled_trajectory_sampling {Q : Type} [Fintype Q]
    [DecidableEq Q] [Nonempty Q] (δ : Q → Bool → Q) :
    ∃ D C k : ℕ, ∀ (s : Q) (F : Finset Q) (n : ℕ),
      AcceptedPathsAvoidTerminal (recordedFairKernel (fun q b => some (δ q b)))
        (s, false) (recordedAccepting F) n →
      (∃ z : LabeledTrajectory Q n, AcceptedLabeledTrajectory (fun q b => some (δ q b)) s F z) →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ∃ S : Circuit (Fin (n + 1) × (Q × Bool)), S.depth ≤ D ∧
          (S.size : ℝ) ≤ C * (((n + 1 : ℕ) : ℝ) / ε) ^ k ∧
          (S.randomBits : ℝ) ≤ n + C * logInv ε ∧
          SupportPreserving S labeledTrajectoryEncode
            (normalizeWeights (labeledTrajectoryWeight (fun q b => some (δ q b)) s F)) ∧
          tv (mass S labeledTrajectoryEncode)
            (normalizeWeights (labeledTrajectoryWeight (fun q b => some (δ q b)) s F)) ≤ ε := by
  classical
  let step := fun q b => some (δ q b)
  let W := recordedLabelMatrix step
  let P := recordedFairKernel step
  obtain ⟨D, C, k, hall⟩ := terminal_avoiding_accepted_graph_sampling W
    (recordedLabelMatrix_zero_one step) (recordedLabelMatrix_complete_rows δ)
  refine ⟨D, C, k, ?_⟩
  intro s F n havoid hnonempty ε hε hεle
  obtain ⟨z, hz⟩ := hnonempty
  have hZ : 0 < ∑ z : LabeledTrajectory Q n, labeledTrajectoryWeight step s F z :=
    ((labeledTrajectoryWeight_pos_iff step s F z).mpr hz).trans_le
      (Finset.single_le_sum (fun z _ => labeledTrajectoryWeight_nonneg step s F z) (Finset.mem_univ z))
  have hZW : 0 < ∑ γ : Fin (n + 1) → Q × Bool,
      acceptedGraphWeight W (s, false) (recordedAccepting F) γ := by
    rw [← recorded_weight_sum step s F n]
    exact hZ
  have hR : (fun x y => 0 < P x y) = (fun x y => 0 < W x y) := by
    funext x y
    exact propext (recordedFairKernel_pos_iff step x y)
  have havoidW : AcceptedPathsAvoidTerminal W (s, false) (recordedAccepting F) n := by
    intro γ hγ i
    have hγP : 0 < acceptedGraphWeight P (s, false) (recordedAccepting F) γ := by
      change 0 < acceptedGraphWeight (recordedFairKernel step) (s, false) (recordedAccepting F) γ
      rw [← recordedFairAcceptedWeight_eq_graph step s F γ, recordedFairAcceptedWeight_scale step s F γ]
      exact mul_pos (by positivity) hγ
    have ht := havoid γ hγP i
    change ¬ IsGraphTerminal (fun x y => 0 < P x y) (γ i) at ht
    rw [hR] at ht
    exact ht
  obtain ⟨S, hd, hsize, hbits, hs, ht⟩ := hall (s, false) (recordedAccepting F) n havoidW hZW ε hε hεle
  have htransfer := recorded_sampler_transport step s F hZ S ε hs ht
  exact ⟨S, hd, hsize, hbits, htransfer.1, htransfer.2⟩

theorem terminal_avoiding_dfa_word_sampling {q : ℕ} (A : BinaryDFA q) :
    ∃ D C k : ℕ, ∀ n : ℕ,
      AcceptedPathsAvoidTerminal (recordedFairKernel (dfaPartialStep A))
        (A.start, false) (recordedAccepting A.accepting) n →
      (acceptedWords A n).Nonempty →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ S : Circuit (Fin n), S.depth ≤ D ∧
        (S.size : ℝ) ≤ C * (((n + 1 : ℕ) : ℝ) / ε) ^ k ∧
        (S.randomBits : ℝ) ≤ n + C * logInv ε ∧
        SupportPreserving S (fun w : Bits n => w) (wordLaw A) ∧
        tv (mass S (fun w : Bits n => w)) (wordLaw A) ≤ ε := by
  letI : Nonempty (Fin q) := ⟨A.start⟩
  obtain ⟨D, C, k, hall⟩ := terminal_avoiding_labeled_trajectory_sampling A.step
  let C' : ℕ := C + 3 * q + 2
  have hCC : (C : ℝ) ≤ C' := by exact_mod_cast (show C ≤ C' by dsimp [C']; omega)
  refine ⟨D + 1, C', max k 1, ?_⟩
  intro n havoid hn ε hε hεle
  obtain ⟨w, hw⟩ := hn
  have hacc : A.accepts w = true := (Finset.mem_filter.mp hw).2
  have hγ := (dfa_accepted_trajectory_iff A (drivenPath A.step n A.start w) w).mpr ⟨rfl, hacc⟩
  obtain ⟨T, hTD, hTS, hTB, hs, ht⟩ := hall A.start A.accepting n havoid
    ⟨(drivenPath A.step n A.start w, w), hγ⟩ ε hε hεle
  obtain ⟨S, hbits, hSD, hSS, hsupport, htv⟩ := dfa_accepted_word_sampler_projection A ⟨w, hw⟩ T ε hs ht
  refine ⟨S, hSD.trans (Nat.add_le_add_right hTD 1), ?_, ?_, hsupport, htv⟩
  · let X : ℝ := (n + 1 : ℕ) / ε
    have hX : 1 ≤ X := accuracy_ratio_ge_one n hε (by linarith)
    have hk : X ^ k ≤ X ^ max k 1 := pow_le_pow_right₀ hX (Nat.le_max_left _ _)
    have hx : X ≤ X ^ max k 1 := by
      simpa only [pow_one] using pow_le_pow_right₀ hX (Nat.le_max_right k 1)
    have hnp : ((n + 1 : ℕ) : ℝ) ≤ X ^ max k 1 :=
      (accuracy_ratio_controls_length n hε (by linarith)).1.trans hx
    have hcp := mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
    have hextra : (3 * (q : ℝ) + 2) * (n + 1 : ℕ) ≤ (3 * q + 2) * X ^ max k 1 :=
      mul_le_mul_of_nonneg_left hnp (by positivity)
    have hSS' : (S.size : ℝ) ≤ T.size + ((n + 1) * (q * 2) : ℕ) + (n * (q + 2) : ℕ) := by
      exact_mod_cast hSS
    change (T.size : ℝ) ≤ C * X ^ k at hTS
    change (S.size : ℝ) ≤ C' * X ^ max k 1
    dsimp only [C']
    push_cast at hSS' hextra ⊢
    nlinarith [Nat.cast_nonneg q (α := ℝ)]
  · rw [hbits]
    exact hTB.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hCC
      (logInv_nonneg_of_le_one ε hε (by linarith))))

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_WordSampling
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

theorem wordLaw_nonneg {q n : ℕ} (A : BinaryDFA q) :
    ∀ w : Bits n, 0 ≤ wordLaw A w := by
  rw [← fairAcceptedWordWeight_normalized_dfa A]
  exact normalizeWeights_nonneg _ (fairAcceptedWordWeight_nonneg A.step A.start A.accepting)

theorem wordLaw_sum {q n : ℕ} (A : BinaryDFA q)
    (hn : (acceptedWords A n).Nonempty) : ∑ w : Bits n, wordLaw A w = 1 := by
  obtain ⟨w, hw⟩ := hn
  have hacc : A.accepts w = true := (Finset.mem_filter.mp hw).2
  have hmem : wordEnd A.step A.start w ∈ A.accepting := of_decide_eq_true hacc
  have hpos := (fairAcceptedWordWeight_pos_iff A.step A.start A.accepting w).mpr hmem
  have hZ : 0 < ∑ v : Bits n, fairAcceptedWordWeight A.step A.start A.accepting v :=
    hpos.trans_le (Finset.single_le_sum
      (fun v _ => fairAcceptedWordWeight_nonneg A.step A.start A.accepting v) (Finset.mem_univ w))
  rw [← fairAcceptedWordWeight_normalized_dfa A]
  exact normalizeWeights_sum _ hZ

/-- Appendix E.2, with the original circuit model and accepted-word law.
All constants precede length and accuracy; in particular the coefficient
of the word length in the random-bit bound is one. The finite exceptional
lengths and length zero are included. -/
theorem approximate_regular_word_sampling (q : ℕ) (A : BinaryDFA q) :
    ∃ D C k : ℕ, ∀ n : ℕ, (acceptedWords A n).Nonempty →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ S : Circuit (Fin n),
        S.depth ≤ D ∧
        (S.size : ℝ) ≤ (C : ℝ) * (((n + 1 : ℕ) : ℝ) / ε) ^ k ∧
        (S.randomBits : ℝ) ≤ (n : ℝ) + (C : ℝ) * logInv ε ∧
        SupportPreserving S (fun x : Bits n => x) (wordLaw A) ∧
        tv (mass S (fun x : Bits n => x)) (wordLaw A) ≤ ε := by
  letI : Nonempty (Fin q) := ⟨A.start⟩
  obtain ⟨p, hp, _, hcases⟩ := residue_acceptance_dichotomy
    (recordedFairKernel (dfaPartialStep A)) (recordedFairKernel_nonneg _)
    (recordedFairKernel_complete_rows A.step)
  obtain ⟨c, N, hc, hcase⟩ := hcases (A.start, false) (recordedAccepting A.accepting)
  obtain ⟨Dz, Cz, kz, hzero⟩ := terminal_avoiding_dfa_word_sampling A
  obtain ⟨Dp, Cp, kp, hpositive⟩ := positive_density_word_sampling A.step c hc
  obtain ⟨Cs, ks, hshort⟩ := short_word_rounding_circuit ((N : ℝ) + 1) (by positivity)
  let D := max Dz (max Dp 3)
  let C := Cz + Cp + Cs
  let k := max kz (max kp ks)
  refine ⟨D, C, k, ?_⟩
  intro n hn ε hε hεle
  have hX : 1 ≤ ((n + 1 : ℕ) : ℝ) / ε := accuracy_ratio_ge_one n hε (by linarith)
  have hlog : 0 ≤ logInv ε := logInv_nonneg_of_le_one ε hε (by linarith)
  have upgrade (D₀ C₀ k₀ : ℕ) (hD : D₀ ≤ D) (hC : C₀ ≤ C) (hk : k₀ ≤ k)
      (hsample : ∃ S : Circuit (Fin n), S.depth ≤ D₀ ∧
        (S.size : ℝ) ≤ C₀ * (((n + 1 : ℕ) : ℝ) / ε) ^ k₀ ∧
        (S.randomBits : ℝ) ≤ n + C₀ * logInv ε ∧
        SupportPreserving S (fun x : Bits n => x) (wordLaw A) ∧
        tv (mass S (fun x : Bits n => x)) (wordLaw A) ≤ ε) :
      ∃ S : Circuit (Fin n), S.depth ≤ D ∧
        (S.size : ℝ) ≤ C * (((n + 1 : ℕ) : ℝ) / ε) ^ k ∧
        (S.randomBits : ℝ) ≤ n + C * logInv ε ∧
        SupportPreserving S (fun x : Bits n => x) (wordLaw A) ∧
        tv (mass S (fun x : Bits n => x)) (wordLaw A) ≤ ε := by
    obtain ⟨S, hSD, hSS, hSB, hs, ht⟩ := hsample
    refine ⟨S, hSD.trans hD, ?_, ?_, hs, ht⟩
    · exact hSS.trans (mul_le_mul (Nat.cast_le.mpr hC) (pow_le_pow_right₀ hX hk)
        (by positivity) (Nat.cast_nonneg C))
    · exact hSB.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hC) hlog))
  by_cases hN : n < N
  · have hnK : (n : ℝ) ≤ ((N : ℝ) + 1) * logInv ε := by
      have hle : (n : ℝ) ≤ N := Nat.cast_le.mpr (Nat.le_of_lt hN)
      have hlog1 := logInv_ge_one hε hεle
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith
    exact upgrade 3 Cs ks (by dsimp [D]; omega) (by dsimp [C]; omega)
      (by dsimp [k]; omega)
      (hshort n ε hε hεle hnK (wordLaw A) (wordLaw_nonneg A) (wordLaw_sum A hn))
  · let a : Fin p := ⟨n % p, Nat.mod_lt n hp⟩
    rcases hcase a with hz | hpos
    · exact upgrade Dz Cz kz (by dsimp [D]; omega) (by dsimp [C]; omega)
        (by dsimp [k]; omega) (hzero n (hz n rfl) hn ε hε hεle)
    · have hacc := hpos n (by omega) rfl
      change c ≤ kernelSetMass (recordedFairKernel (fun s b => some (A.step s b)))
        (recordedAccepting A.accepting) n (A.start, false) at hacc
      rw [recorded_kernel_word_acceptance] at hacc
      have hs := hpositive A.start A.accepting n hacc ε hε hεle
      rw [fairAcceptedWordWeight_normalized_dfa A] at hs
      exact upgrade Dp Cp kp (by dsimp [D]; omega) (by dsimp [C]; omega)
        (by dsimp [k]; omega) hs

end FSS23105365

end
end

open FSS23105365
local notation "Path" => FSS23105365.Path
theorem solution (q : ℕ) (A : BinaryDFA q) :
    ∃ D C k : ℕ, ∀ n : ℕ, (acceptedWords A n).Nonempty →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ∃ S : Circuit (Fin n),
        S.depth ≤ D ∧
        (S.size : ℝ) ≤ (C : ℝ) * (((n + 1 : ℕ) : ℝ) / ε) ^ k ∧
        (S.randomBits : ℝ) ≤ (n : ℝ) + (C : ℝ) * logInv ε ∧
        SupportPreserving S (fun x : Bits n => x) (wordLaw A) ∧
        tv (mass S (fun x : Bits n => x)) (wordLaw A) ≤ ε := FSS23105365.approximate_regular_word_sampling q A
