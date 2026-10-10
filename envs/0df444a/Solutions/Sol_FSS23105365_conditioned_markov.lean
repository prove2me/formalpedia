-- Prove2me | solution 1 for FSS23105365.conditioned_markov
-- status  : ACCEPTED   (prove)
-- author  : @YY
-- created : 2026-10-09T16:02:47.40388+00:00
-- url     : https://prove2.me/submissions/9b197dec-db7f-4710-8be2-d0338576cb6c

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
import Mathlib.Algebra.Order.Floor.Semiring
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
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Relation
import Mathlib.NumberTheory.Padics.PadicVal.Basic
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

theorem finitePathWeight_pos_iff {Q : Type} (μ : Q → ℝ) (W : Q → Q → ℝ)
    (hμ : ∀ x, 0 ≤ μ x) (hW : ∀ x y, 0 ≤ W x y) {n : ℕ}
    (γ : Fin (n + 1) → Q) :
    0 < finitePathWeight μ W γ ↔
      0 < μ (γ 0) ∧ RespectsGraph (fun x y => 0 < W x y) γ := by
  have he : finitePathWeight μ W γ = μ (γ 0) * edgePathWeight W γ := by
    simp [finitePathWeight, edgePathWeight]
  rw [he]
  constructor
  · intro hp
    rcases mul_pos_iff.mp hp with h | h
    · exact ⟨h.1, (edgePathWeight_pos_iff W hW γ).mp h.2⟩
    · exact False.elim ((not_lt_of_ge (hμ _)) h.1)
  · rintro ⟨hμγ, hγ⟩
    exact mul_pos hμγ ((edgePathWeight_pos_iff W hW γ).mpr hγ)

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

-- Source module: Solutions.FSS23105365_PathReachability
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

theorem pathLaw_nonneg {q n : ℕ} (M : MarkovChain q) (γ : Path q n) :
    0 ≤ pathLaw M γ := by
  apply mul_nonneg (M.initial_nonneg _)
  exact Finset.prod_nonneg (fun _ _ => M.transition_nonneg _ _)









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



theorem lookupLiteral_true_iff {r : ℕ} (a x : Bits r) (i : Fin r) :
    formulaEval (lookupLiteral a i) x = true ↔ x i = a i := by
  cases ha : a i <;> cases hx : x i <;> simp [lookupLiteral, formulaEval, ha, hx]

















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



theorem formulaAnd_eval {r : ℕ} (f g : CircuitFormula r) (x : Bits r) :
    formulaEval (formulaAnd f g) x = (formulaEval f x && formulaEval g x) := by
  simp [formulaAnd, formulaEval, List.ofFn_succ]



theorem formulaAnd_depth {r : ℕ} (f g : CircuitFormula r) :
    formulaDepth (formulaAnd f g) = max (formulaDepth f) (formulaDepth g) + 1 := by
  simp [formulaAnd, formulaDepth, Finset.univ_fin2]



theorem formulaAnd_cost {r : ℕ} (f g : CircuitFormula r) :
    formulaCost (formulaAnd f g) = formulaCost f + formulaCost g + 3 := by
  simp [formulaAnd, formulaCost, Fin.sum_univ_succ]



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

/-- A category is exactly the initial/final states and the block-boundary
observation for its constructed ordered length vector, on valid paths. -/
theorem graphCategory_eq_block_observation {Q : Type} [Fintype Q]
    (R : Q → Q → Prop) {n : ℕ} (γ η : Fin (n + 1) → Q)
    (hγ : RespectsGraph R γ) (hη : RespectsGraph R η) :
    graphCategory R γ = graphCategory R η ↔ γ 0 = η 0 ∧ γ (Fin.last n) = η (Fin.last n) ∧
      bridgeBoundaryObservation (graphCategoryBlockLengths R γ) (graphCategoryBlockLengths_total R γ) γ =
      bridgeBoundaryObservation (graphCategoryBlockLengths R γ) (graphCategoryBlockLengths_total R γ) η := by
  exact (graphCategory_eq_boundary_iff R γ η hγ hη).trans
    (categoryBoundaryMatches_iff_block_observation R γ η)

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

theorem normalized_category_constructed_blocks {Q : Type} [Fintype Q] [DecidableEq Q]
    (μ : Q → ℝ) (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) {n : ℕ}
    (γ : Fin (n + 1) → Q) (hγ : RespectsGraph (fun x y => 0 < W x y) γ)
    (hμ : μ (γ 0) ≠ 0) :
    normalizeWeights (fun η => if graphCategory (fun x y => 0 < W x y) γ =
      graphCategory (fun x y => 0 < W x y) η then finitePathWeight μ W η else 0) =
    normalizeWeights (fun η => if CategoryBlockMatches (fun x y => 0 < W x y) γ η
      then edgePathWeight W η else 0) := by
  classical
  have he : (fun η => if graphCategory (fun x y => 0 < W x y) γ =
      graphCategory (fun x y => 0 < W x y) η then finitePathWeight μ W η else 0) =
      fun η => μ (γ 0) * (if CategoryBlockMatches (fun x y => 0 < W x y) γ η
        then edgePathWeight W η else 0) := by
    funext η
    exact category_path_weight_constructed_blocks μ W hW γ η hγ
  rw [he]
  exact normalizeWeights_scale _ _ hμ

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_AcceptingCategoryMixture
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

local instance {q n : ℕ} : DecidableEq (GraphCategory (Fin q) n) := Classical.decEq _

def acceptingPathWeight {q n : ℕ} (M : MarkovChain q) (F : Finset (Fin q)) : Path q n → ℝ :=
  fun γ => if γ (Fin.last n) ∈ F then pathLaw M γ else 0

theorem acceptingPathWeight_nonneg {q n : ℕ} (M : MarkovChain q) (F : Finset (Fin q)) :
    ∀ γ : Path q n, 0 ≤ acceptingPathWeight M F γ := by
  intro γ
  unfold acceptingPathWeight
  split_ifs
  · exact pathLaw_nonneg M γ
  · exact le_rfl

theorem acceptingPathWeight_sum {q n : ℕ} (M : MarkovChain q) (F : Finset (Fin q)) :
    (∑ γ : Path q n, acceptingPathWeight M F γ) = acceptanceProbability M F n := rfl

theorem conditionedPathLaw_normalize {q n : ℕ} (M : MarkovChain q) (F : Finset (Fin q)) :
    (conditionedPathLaw M F : Path q n → ℝ) = normalizeWeights (acceptingPathWeight M F) := by
  funext γ
  change (if γ (Fin.last n) ∈ F then pathLaw M γ / acceptanceProbability M F n else 0) =
    (if γ (Fin.last n) ∈ F then pathLaw M γ else 0) / acceptanceProbability M F n
  split_ifs <;> simp

theorem acceptingPathWeight_pos_iff {q n : ℕ} (M : MarkovChain q) (F : Finset (Fin q)) (γ : Path q n) :
    0 < acceptingPathWeight M F γ ↔ γ (Fin.last n) ∈ F ∧ 0 < pathLaw M γ := by
  unfold acceptingPathWeight
  by_cases h : γ (Fin.last n) ∈ F <;> simp [h]

abbrev AcceptingCategory {q : ℕ} (M : MarkovChain q) (F : Finset (Fin q)) (n : ℕ) :=
  PositiveFiber (graphCategory (fun x y => 0 < M.transition x y)) (acceptingPathWeight (n := n) M F)



theorem acceptingCategory_has_path {q n : ℕ} (M : MarkovChain q) (F : Finset (Fin q))
    (c : AcceptingCategory M F n) :
    ∃ γ : Path q n, graphCategory (fun x y => 0 < M.transition x y) γ = c.val ∧
      γ (Fin.last n) ∈ F ∧ 0 < pathLaw M γ := by
  obtain ⟨γ, hcat, hp⟩ := (fiberMass_pos_iff _ _ (acceptingPathWeight_nonneg M F) c.val).mp c.property
  exact ⟨γ, hcat, (acceptingPathWeight_pos_iff M F γ).mp hp⟩

/-- Conditioning on a category already fixes its accepting final state,
so the final-event indicator disappears inside that category fiber. -/
theorem accepting_category_fiber {q n : ℕ} (M : MarkovChain q) (F : Finset (Fin q))
    (γ : Path q n) (hγ : γ (Fin.last n) ∈ F) :
    fiberWeight (graphCategory (fun x y => 0 < M.transition x y)) (acceptingPathWeight M F)
      (graphCategory (fun x y => 0 < M.transition x y) γ) =
    fiberWeight (graphCategory (fun x y => 0 < M.transition x y)) (pathLaw M)
      (graphCategory (fun x y => 0 < M.transition x y) γ) := by
  classical
  funext η
  unfold fiberWeight
  by_cases hc : graphCategory (fun x y => 0 < M.transition x y) η =
      graphCategory (fun x y => 0 < M.transition x y) γ
  · have ht : η (Fin.last n) = γ (Fin.last n) :=
      congrArg (fun c : GraphCategory (Fin q) n => c.2.1) hc
    rw [if_pos hc, if_pos hc, acceptingPathWeight, if_pos (ht ▸ hγ)]
  · rw [if_neg hc, if_neg hc]

theorem accepting_category_normalize_of_path {q n : ℕ} (M : MarkovChain q) (F : Finset (Fin q))
    (γ : Path q n) (hγF : γ (Fin.last n) ∈ F) (hγ : 0 < pathLaw M γ) :
    normalizeWeights (fiberWeight (graphCategory (fun x y => 0 < M.transition x y))
        (acceptingPathWeight M F) (graphCategory (fun x y => 0 < M.transition x y) γ)) =
      normalizeWeights (fun η => if CategoryBlockMatches (fun x y => 0 < M.transition x y) γ η
        then edgePathWeight M.transition η else 0) := by
  classical
  have hpos := (finitePathWeight_pos_iff M.initial M.transition M.initial_nonneg
    M.transition_nonneg γ).mp hγ
  rw [accepting_category_fiber M F γ hγF]
  have he : fiberWeight (graphCategory (fun x y => 0 < M.transition x y)) (pathLaw M)
      (graphCategory (fun x y => 0 < M.transition x y) γ) =
      (fun η => if graphCategory (fun x y => 0 < M.transition x y) γ =
        graphCategory (fun x y => 0 < M.transition x y) η then
          finitePathWeight M.initial M.transition η else 0) := by
    funext η
    simp only [fiberWeight, eq_comm, pathLaw_eq_finitePathWeight]
  rw [he]
  convert normalized_category_constructed_blocks M.initial M.transition M.transition_nonneg γ
    hpos.2 hpos.1.ne' using 1
  apply congrArg normalizeWeights
  funext η
  split_ifs <;> rfl



theorem acceptingCategory_nonempty {q n : ℕ} (M : MarkovChain q) (F : Finset (Fin q))
    (hF : 0 < acceptanceProbability M F n) : Nonempty (AcceptingCategory M F n) := by
  classical
  have hp : 0 < ∑ γ : Path q n, acceptingPathWeight M F γ := hF
  obtain ⟨γ, _, hγ⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun γ _ => acceptingPathWeight_nonneg M F γ)).mp hp
  exact ⟨⟨_, fiberMass_pos_of_weight_pos _ _ (acceptingPathWeight_nonneg M F) γ hγ⟩⟩

theorem acceptingCategory_card_polynomial {q n : ℕ} (M : MarkovChain q) (F : Finset (Fin q)) :
    Fintype.card (AcceptingCategory M F n) ≤ (q * q * (q * q + 1) ^ q) * (n + 1) ^ q := by
  classical
  apply (Fintype.card_subtype_le _).trans
  simpa only [Fintype.card_fin] using (graphCategory_card_polynomial (Q := Fin q) n)

/-- Approximate category selection and approximate sampling within each
positive accepting category suffice. This is a composition theorem; the
existence and resources of implementing circuits are separate obligations. -/
theorem approximate_conditioned_category_mixture {q n : ℕ} (M : MarkovChain q)
    (F : Finset (Fin q)) (hF : 0 < acceptanceProbability M F n)
    (p : AcceptingCategory M F n → ℝ) (L : AcceptingCategory M F n → Path q n → ℝ)
    (hp : ∀ c, 0 ≤ p c) (hpsum : ∑ c, p c = 1)
    (hL : ∀ c γ, 0 ≤ L c γ) (hLsum : ∀ c, ∑ γ, L c γ = 1)
    (hsupp : ∀ c γ, 0 < L c γ →
      0 < fiberWeight (graphCategory (fun x y => 0 < M.transition x y))
        (acceptingPathWeight M F) c.val γ)
    (δ η : ℝ)
    (hcat : tv p (normalizeWeights (fun c : AcceptingCategory M F n =>
      fiberMass (graphCategory (fun x y => 0 < M.transition x y)) (acceptingPathWeight M F) c.val)) ≤ δ)
    (hcond : ∀ c, tv (L c) (normalizeWeights
      (fiberWeight (graphCategory (fun x y => 0 < M.transition x y))
        (acceptingPathWeight M F) c.val)) ≤ η) :
    (∀ γ, 0 ≤ mixtureLaw p L γ) ∧ (∑ γ, mixtureLaw p L γ = 1) ∧
    (∀ γ, 0 < mixtureLaw p L γ → γ (Fin.last n) ∈ F ∧ 0 < pathLaw M γ) ∧
    tv (mixtureLaw p L) (conditionedPathLaw M F) ≤ δ + η := by
  classical
  obtain ⟨hnonneg, hsum, hs, htv⟩ := approximate_disintegration
    (graphCategory (fun x y => 0 < M.transition x y)) (acceptingPathWeight M F)
    (acceptingPathWeight_nonneg M F) hF p L hp hpsum hL hLsum hsupp δ η hcat hcond
  refine ⟨hnonneg, hsum, ?_, ?_⟩
  · exact fun γ hγ => (acceptingPathWeight_pos_iff M F γ).mp (hs γ hγ)
  · simpa only [conditionedPathLaw_normalize] using htv

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

/-- A normalized positive weight must come from the original support,
including when the total mass is zero and normalization is identically zero. -/
theorem normalizeWeights_positive_support {Ω : Type} [Fintype Ω] (w : Ω → ℝ)
    (hw : ∀ x, 0 ≤ w x) (x : Ω) (hx : 0 < normalizeWeights w x) : 0 < w x := by
  have hs : 0 ≤ ∑ x, w x := Finset.sum_nonneg (fun x _ => hw x)
  rcases div_pos_iff.mp hx with h | h
  · exact h.1
  · exact False.elim ((not_lt_of_ge hs) h.2)

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

theorem bridgeRoundingSeed_budget {Q : Type} [Fintype Q] [DecidableEq Q]
    (s t : Q) (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (Fintype.card (EndpointPath Q s t n) : ℝ) / 2 ^ bridgeRoundingSeed (Fintype.card Q) n δ ≤ δ := by
  have hq : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨s⟩
  calc
    _ ≤ (Fintype.card Q ^ (n + 1) : ℕ) / (2 : ℝ) ^ bridgeRoundingSeed (Fintype.card Q) n δ :=
      div_le_div_of_nonneg_right (Nat.cast_le.mpr (endpointPath_card_bound s t n)) (by positivity)
    _ ≤ δ := roundingSeed_denominator_bound _ (pow_pos hq _) δ hδ

/-- All positive bridges of the same length use the same prescribed seed
budget, regardless of their endpoints or probabilities. The output circuit
has depth six and emits every coordinate of the sampled path. -/
theorem rounded_bridge_block_circuit {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ)
    (hpart : 0 < bridgePartition W s t n) (δ : ℝ) (hδ : 0 < δ) :
    ∃ f : Bits (bridgeRoundingSeed (Fintype.card Q) n δ) → EndpointPath Q s t n,
      ∃ S : Circuit (Fin (n + 1) × Q), ∃ hbits : S.randomBits = bridgeRoundingSeed (Fintype.card Q) n δ,
        (∀ seed i x, S.eval (fun j => seed (Fin.cast hbits j)) (i, x) = decide ((f seed).val i = x)) ∧
        (∀ seed, 0 < edgePathWeight W (f seed).val) ∧
        tv (finiteSeedLaw f) (normalizeWeights (fun γ : EndpointPath Q s t n => edgePathWeight W γ.val)) ≤ δ ∧
        S.depth ≤ 6 ∧
        S.size ≤ bridgeRoundingSeed (Fintype.card Q) n δ + ((n + 1) * Fintype.card Q) *
          (Fintype.card Q ^ (n + 1) * (2 * (bridgeRoundingSeed (Fintype.card Q) n δ *
            (3 * bridgeRoundingSeed (Fintype.card Q) n δ + 2) + 1) + 6) + 2) := by
  classical
  let w := fun γ : EndpointPath Q s t n => edgePathWeight W γ.val
  have hw : ∀ γ, 0 ≤ w γ := fun γ => edgePathWeight_nonneg W hW γ.val
  have hsum : ∑ γ, normalizeWeights w γ = 1 := normalizeWeights_sum w (by
    rw [endpointPath_weight_sum]
    exact hpart)
  obtain ⟨f, S, hbits, he, hs, htv, hD, hsize⟩ := rounding_AC0_function_budget
    (fun γ : EndpointPath Q s t n => fun o : Fin (n + 1) × Q => decide (γ.val o.1 = o.2))
    (normalizeWeights w) (normalizeWeights_nonneg w hw) hsum _ δ (bridgeRoundingSeed_budget s t n δ hδ)
  refine ⟨f, S, hbits, (fun seed i x => congrFun (he seed) (i, x)),
    (fun seed => normalizeWeights_positive_support w hw (f seed) (hs seed)), htv, hD, ?_⟩
  simp only [Fintype.card_prod, Fintype.card_fin] at hsize
  exact hsize.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ (endpointPath_card_bound s t n)) 2)) _)

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

theorem roundedBridgeModel_nonempty {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ)
    (hp : 0 < bridgePartition W s t n) (δ : ℝ) (hδ : 0 < δ) :
    Nonempty (RoundedBridgeModel W s t n δ) := by
  obtain ⟨f, S, hbits, he, hs, htv, hD, hsize⟩ := rounded_bridge_block_circuit W hW s t n hp δ hδ
  exact ⟨{ sample := f
           circuit := S
           randomBits_eq := hbits
           eval_eq := he
           sample_positive := hs
           error := htv
           depth_le := hD
           size_le := hsize }⟩

def chooseRoundedBridgeModel {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ)
    (hp : 0 < bridgePartition W s t n) (δ : ℝ) (hδ : 0 < δ) : RoundedBridgeModel W s t n δ :=
  Classical.choice (roundedBridgeModel_nonempty W hW s t n hp δ hδ)

/-- Impossible endpoint requests have zero kernel mass. Every positive
request uses the actual certified finite-bit sampler above. -/
def roundedBridgeKernel {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ)
    (δ : ℝ) (hδ : 0 < δ) : EndpointPath Q s t n → ℝ := by
  classical
  exact if hp : 0 < bridgePartition W s t n then
    finiteSeedLaw (chooseRoundedBridgeModel W hW s t n hp δ hδ).sample else fun _ => 0

theorem roundedBridgeKernel_nonneg {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∀ γ, 0 ≤ roundedBridgeKernel W hW s t n δ hδ γ := by
  classical
  intro γ
  unfold roundedBridgeKernel
  split_ifs
  · exact finiteSeedLaw_nonneg _ γ
  · exact le_rfl

theorem roundedBridgeKernel_eq {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ)
    (hp : 0 < bridgePartition W s t n) (δ : ℝ) (hδ : 0 < δ) :
    roundedBridgeKernel W hW s t n δ hδ =
      finiteSeedLaw (chooseRoundedBridgeModel W hW s t n hp δ hδ).sample := dif_pos hp

theorem roundedBridgeKernel_sum {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ)
    (hp : 0 < bridgePartition W s t n) (δ : ℝ) (hδ : 0 < δ) :
    ∑ γ, roundedBridgeKernel W hW s t n δ hδ γ = 1 := by
  rw [roundedBridgeKernel_eq W hW s t n hp δ hδ]
  exact finiteSeedLaw_sum _

theorem roundedBridgeKernel_support {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (γ : EndpointPath Q s t n) (hγ : 0 < roundedBridgeKernel W hW s t n δ hδ γ) :
    0 < edgePathWeight W γ.val := by
  classical
  unfold roundedBridgeKernel at hγ
  split_ifs at hγ with hp
  · obtain ⟨seed, rfl⟩ := (finiteSeedLaw_pos_iff _ γ).mp hγ
    exact (chooseRoundedBridgeModel W hW s t n hp δ hδ).sample_positive seed
  · exact False.elim ((lt_irrefl 0) hγ)

theorem roundedBridgeKernel_error {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ)
    (hp : 0 < bridgePartition W s t n) (δ : ℝ) (hδ : 0 < δ) :
    tv (roundedBridgeKernel W hW s t n δ hδ)
      (normalizeWeights (fun γ : EndpointPath Q s t n => edgePathWeight W γ.val)) ≤ δ := by
  rw [roundedBridgeKernel_eq W hW s t n hp δ hδ]
  exact (chooseRoundedBridgeModel W hW s t n hp δ hδ).error

def roundedBlocksKernel {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y)
    (l : Fin (k + 1) → ℕ) (s t : Q) (δ : ℝ) (hδ : 0 < δ)
    (y : Fin k → Q) (i : Fin (k + 1)) : BridgeBlockPath Q l s t y i → ℝ :=
  roundedBridgeKernel W hW ((Fin.cons s y : Fin (k + 1) → Q) i)
    ((Fin.snoc y t : Fin (k + 1) → Q) i) (l i) δ hδ

/-- Substituting the actual rounded block laws removes all conditional
sampler-existence hypotheses from the internal boundary/block assembly. -/
theorem rounded_boundary_block_sampler {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y)
    (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n) (s t : Q)
    (hpart : 0 < bridgePartition W s t n)
    (a : (Fin k → Q) → ℝ) (ha : ∀ y, 0 ≤ a y) (hasum : ∑ y, a y = 1)
    (hasupp : ∀ y, 0 < a y → 0 < bridgeBoundaryMass W l s t y)
    (η δ : ℝ) (hδ : 0 < δ)
    (hboundary : tv a (normalizeWeights (bridgeBoundaryMass W l s t)) ≤ η) :
    let law := boundaryBlockMixtureLaw l hlen s t a (roundedBlocksKernel W hW l s t δ hδ)
    (∀ γ, 0 ≤ law γ) ∧ (∑ γ, law γ = 1) ∧
    (∀ γ, 0 < law γ → 0 < bridgeWeight W s t n γ) ∧
    tv law (normalizeWeights (bridgeWeight W s t n)) ≤ η + (k + 1 : ℕ) * δ := by
  apply approximate_boundary_block_mixture W hW l hlen s t hpart a ha hasum hasupp
    (roundedBlocksKernel W hW l s t δ hδ)
    (fun y i => roundedBridgeKernel_nonneg W hW _ _ _ δ hδ)
    (fun y hy i => roundedBridgeKernel_sum W hW _ _ _
      ((bridgeBoundaryMass_pos_iff W hW l s t y).mp (hasupp y hy) i) δ hδ)
    (fun y i b => roundedBridgeKernel_support W hW _ _ _ δ hδ b)
    η ((k + 1 : ℕ) * δ) (fun _ _ => δ) hboundary
    (fun y hy i => roundedBridgeKernel_error W hW _ _ _
      ((bridgeBoundaryMass_pos_iff W hW l s t y).mp (hasupp y hy) i) δ hδ)
  intro y hy
  simp

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

/-- Conditional endpoint branches reuse these slots: the block seed count
depends on its length, the original state count, and the common tolerance. -/
def bridgeBlockSeedBudget {k : ℕ} (q : ℕ) (l : Fin (k + 1) → ℕ) (δ : ℝ) : ℕ :=
  ∑ i, bridgeRoundingSeed q (l i) δ

theorem bridgeBlockSeedBudget_bound {k n : ℕ} (q : ℕ) (hq : 0 < q)
    (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1) :
    (bridgeBlockSeedBudget q l δ : ℝ) ≤
      n * (Real.log q / Real.log 2) + (k + 1 : ℕ) * (Real.log q / Real.log 2 + logInv δ + 1) := by
  have hlen' : (∑ i, l i) = n := (bridgeBlockLength_eq_sum l).symm.trans hlen
  have hsum : (∑ i, (l i : ℝ)) = n := by exact_mod_cast hlen'
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => bridgeRoundingSeed_linear_bound q (l i) hq δ hδ hδle)
  simp only [bridgeBlockSeedBudget, Nat.cast_sum]
  calc
    _ ≤ ∑ i : Fin (k + 1), ((l i + 1 : ℕ) * (Real.log q / Real.log 2) + logInv δ + 1) := hb
    _ = _ := by
      simp only [Nat.cast_add, Nat.cast_one, add_mul, Finset.sum_add_distrib, ← Finset.sum_mul,
        hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, one_mul]
      ring

def periodicBridgeSeedBudget {k : ℕ} (q M : ℕ) (l : Fin (k + 1) → ℕ) (δ : ℝ) : ℕ :=
  k * roundingSeed M δ + bridgeBlockSeedBudget q l δ

theorem periodicBridgeSeedBudget_bound {k n : ℕ} (q M : ℕ) (hq : 0 < q) (hM : 0 < M) (hMq : M ≤ q)
    (l : Fin (k + 1) → ℕ) (hlen : bridgeBlockLength l = n)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1) :
    (periodicBridgeSeedBudget q M l δ : ℝ) ≤ n * (Real.log q / Real.log 2) +
      (2 * k + 1 : ℕ) * (Real.log q / Real.log 2 + logInv δ + 1) := by
  have hb := bridgeBlockSeedBudget_bound q hq l hlen δ hδ hδle
  have hc := mul_le_mul_of_nonneg_left (roundingSeed_upper_of_card_le M q hM hMq δ hδ hδle)
    (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  simp only [periodicBridgeSeedBudget, Nat.cast_add, Nat.cast_mul]
  have h := add_le_add hc hb
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at h ⊢
  linarith

/-- Once the common logarithmic cutoff dominates each local seed cost,
the complete segment budget is linear in its length plus one cutoff. -/
theorem cutoffBridgeSeedBudget_linear (q M n L : ℕ) (hq : 0 < q) (hM : 0 < M) (hMq : M ≤ q)
    (δ A : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1) (hA : 0 ≤ A)
    (hcost : Real.log q / Real.log 2 + logInv δ + 1 ≤ A * L) :
    (periodicBridgeSeedBudget q M (cutoffBlockLengths n L) δ : ℝ) ≤
      n * (Real.log q / Real.log 2 + 2 * A) + A * L := by
  have hb := periodicBridgeSeedBudget_bound q M hq hM hMq (cutoffBlockLengths n L)
    (cutoffBlockLengths_total n L) δ hδ hδle
  have hc := cutoff_boundary_length_le n L
  have hc' : (cutoffBoundaryCount n L : ℝ) * L ≤ n := by exact_mod_cast hc
  have hs := mul_le_mul_of_nonneg_left hcost
    (Nat.cast_nonneg (2 * cutoffBoundaryCount n L + 1) :
      (0 : ℝ) ≤ (2 * cutoffBoundaryCount n L + 1 : ℕ))
  have ha := mul_le_mul_of_nonneg_left hc' hA
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at hb hs
  nlinarith

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

-- Source module: Solutions.FSS23105365_DrawnRoundedBlocks
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def drawnRoundedBlocks {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (s t : Q) (y : Fin k → Q) (hy : 0 < bridgeBoundaryMass W l s t y) (δ : ℝ) (hδ : 0 < δ) :
    Bits (bridgeBlockSeedBudget (Fintype.card Q) l δ) → BoundaryBlocks Q l s t y :=
  parallelSeedSample (fun i => bridgeRoundingSeed (Fintype.card Q) (l i) δ)
    (fun i => (chooseRoundedBridgeModel W hW ((Fin.cons s y : Fin (k + 1) → Q) i)
      ((Fin.snoc y t : Fin (k + 1) → Q) i) (l i)
      ((bridgeBoundaryMass_pos_iff W hW l s t y).mp hy i) δ hδ).sample)

theorem drawnRoundedBlocks_law {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (s t : Q) (y : Fin k → Q) (hy : 0 < bridgeBoundaryMass W l s t y) (δ : ℝ) (hδ : 0 < δ) :
    finiteSeedLaw (drawnRoundedBlocks W hW l s t y hy δ hδ) =
      fun b : BoundaryBlocks Q l s t y => ∏ i, roundedBlocksKernel W hW l s t δ hδ y i (b i) := by
  funext b
  change finiteSeedLaw (parallelSeedSample
    (fun i => bridgeRoundingSeed (Fintype.card Q) (l i) δ)
    (fun i => (chooseRoundedBridgeModel W hW _ _ _
      ((bridgeBoundaryMass_pos_iff W hW l s t y).mp hy i) δ hδ).sample)) b = _
  rw [parallelSeedSample_law]
  apply Finset.prod_congr rfl
  intro i _
  exact (congrFun (roundedBridgeKernel_eq W hW _ _ _
    ((bridgeBoundaryMass_pos_iff W hW l s t y).mp hy i) δ hδ) (b i)).symm

def drawnRoundedBridge {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (hlen : bridgeBlockLength l = n) (s t : Q) (y : Fin k → Q)
    (hy : 0 < bridgeBoundaryMass W l s t y) (δ : ℝ) (hδ : 0 < δ) :
    Bits (bridgeBlockSeedBudget (Fintype.card Q) l δ) → (Fin (n + 1) → Q) :=
  concatenateBridgeBlocksAtLength l hlen s t y ∘ drawnRoundedBlocks W hW l s t y hy δ hδ

/-- The explicit flat seed and block-index wiring realize exactly the
previously assembled conditional bridge distribution. -/
theorem drawnRoundedBridge_law {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (hlen : bridgeBlockLength l = n) (s t : Q) (y : Fin k → Q)
    (hy : 0 < bridgeBoundaryMass W l s t y) (δ : ℝ) (hδ : 0 < δ) :
    finiteSeedLaw (drawnRoundedBridge W hW l hlen s t y hy δ hδ) =
      concatenateBlockLaw l hlen s t y (roundedBlocksKernel W hW l s t δ hδ y) := by
  rw [drawnRoundedBridge, finiteSeedLaw_map, drawnRoundedBlocks_law]
  rfl



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_DrawnBoundaryBridge
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- Totalize a conditional draw with a constant path on impossible boundary
tuples. The support hypothesis below proves these branches are never selected. -/
def conditionalRoundedBridge {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (hlen : bridgeBlockLength l = n) (s t : Q) (δ : ℝ) (hδ : 0 < δ)
    (y : Fin k → Q) : Bits (bridgeBlockSeedBudget (Fintype.card Q) l δ) → (Fin (n + 1) → Q) :=
  if hy : 0 < bridgeBoundaryMass W l s t y then
    drawnRoundedBridge W hW l hlen s t y hy δ hδ
  else fun _ _ => s

def drawnBoundaryBridge {Q : Type} [Fintype Q] [DecidableEq Q] {k n r : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (hlen : bridgeBlockLength l = n) (s t : Q) (δ : ℝ) (hδ : 0 < δ)
    (f : Bits r → (Fin k → Q)) :
    Bits (r + bridgeBlockSeedBudget (Fintype.card Q) l δ) → (Fin (n + 1) → Q) :=
  sequentialSeedSample f (conditionalRoundedBridge W hW l hlen s t δ hδ)

/-- The whole bridge has one flat fair seed. Its second slice is reused
across conditional choices; its law is exactly the earlier hierarchical law. -/
theorem drawnBoundaryBridge_law {Q : Type} [Fintype Q] [DecidableEq Q] {k n r : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (hlen : bridgeBlockLength l = n) (s t : Q) (δ : ℝ) (hδ : 0 < δ)
    (f : Bits r → (Fin k → Q))
    (hf : ∀ seed, 0 < bridgeBoundaryMass W l s t (f seed)) :
    finiteSeedLaw (drawnBoundaryBridge W hW l hlen s t δ hδ f) =
      boundaryBlockMixtureLaw l hlen s t (finiteSeedLaw f) (roundedBlocksKernel W hW l s t δ hδ) := by
  rw [drawnBoundaryBridge, sequentialSeedSample_law]
  funext γ
  unfold boundaryBlockMixtureLaw mixtureLaw
  apply Finset.sum_congr rfl
  intro y _
  dsimp only
  by_cases hy : 0 < bridgeBoundaryMass W l s t y
  · have hg : conditionalRoundedBridge W hW l hlen s t δ hδ y =
        drawnRoundedBridge W hW l hlen s t y hy δ hδ := dif_pos hy
    rw [hg, drawnRoundedBridge_law]
  · have hz : finiteSeedLaw f y = 0 := by
      apply le_antisymm _ (finiteSeedLaw_nonneg f y)
      by_contra h
      obtain ⟨seed, rfl⟩ := (finiteSeedLaw_pos_iff f y).mp (lt_of_not_ge h)
      exact hy (hf seed)
    rw [hz, zero_mul, zero_mul]



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

def roundedPeriodicBridgeLaw {Q : Type} [Fintype Q] [DecidableEq Q]
    (W K : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (a : ℕ) (s t : Q) (n L : ℕ)
    (δ : ℝ) (hδ : 0 < δ)
    (f : Bits (roundingSeed (Fintype.card (PositiveSupportClass (K ^ a) s)) δ) →
      PositiveSupportClass (K ^ a) s) : (Fin (n + 1) → Q) → ℝ :=
  boundaryBlockMixtureLaw (cutoffBlockLengths n L) (cutoffBlockLengths_total n L) s t
    (embeddedProductLaw (fun z : PositiveSupportClass (K ^ a) s => z.val) (fun _ => finiteSeedLaw f))
    (roundedBlocksKernel (fun x y => W x y) hW (cutoffBlockLengths n L) s t δ hδ)



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

-- Source module: Solutions.FSS23105365_DrawnPeriodicBridge
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

def drawnPeriodicBridge {Q : Type} [Fintype Q] [DecidableEq Q]
    (W K : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (a : ℕ) (s t : Q) (n L : ℕ)
    (δ : ℝ) (hδ : 0 < δ)
    (f : Bits (roundingSeed (Fintype.card (PositiveSupportClass (K ^ a) s)) δ) →
      PositiveSupportClass (K ^ a) s) :
    Bits (periodicBridgeSeedBudget (Fintype.card Q)
      (Fintype.card (PositiveSupportClass (K ^ a) s)) (cutoffBlockLengths n L) δ) → (Fin (n + 1) → Q) :=
  drawnBoundaryBridge (fun x y => W x y) hW (cutoffBlockLengths n L) (cutoffBlockLengths_total n L)
    s t δ hδ (embeddedRepeatedSeedSample (cutoffBoundaryCount n L)
      (fun z : PositiveSupportClass (K ^ a) s => z.val) f)

theorem drawnPeriodicBridge_law {Q : Type} [Fintype Q] [DecidableEq Q]
    (W K : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (a : ℕ) (s t : Q) (n L : ℕ)
    (δ : ℝ) (hδ : 0 < δ)
    (f : Bits (roundingSeed (Fintype.card (PositiveSupportClass (K ^ a) s)) δ) →
      PositiveSupportClass (K ^ a) s)
    (hf : ∀ y, 0 < embeddedProductLaw (k := cutoffBoundaryCount n L)
      (fun z : PositiveSupportClass (K ^ a) s => z.val) (fun _ => finiteSeedLaw f) y →
      0 < bridgeBoundaryMass (fun x y => W x y) (cutoffBlockLengths n L) s t y) :
    finiteSeedLaw (drawnPeriodicBridge W K hW a s t n L δ hδ f) =
      roundedPeriodicBridgeLaw W K hW a s t n L δ hδ f := by
  let b := embeddedRepeatedSeedSample (cutoffBoundaryCount n L)
    (fun z : PositiveSupportClass (K ^ a) s => z.val) f
  have hb : ∀ seed, 0 < bridgeBoundaryMass (fun x y => W x y) (cutoffBlockLengths n L) s t (b seed) := by
    intro seed
    apply hf
    rw [← embeddedRepeatedSeedSample_law]
    exact (finiteSeedLaw_pos_iff b (b seed)).mpr ⟨seed, rfl⟩
  have he := drawnBoundaryBridge_law (fun x y => W x y) hW (cutoffBlockLengths n L)
    (cutoffBlockLengths_total n L) s t δ hδ b hb
  dsimp only [b] at he
  rw [embeddedRepeatedSeedSample_law] at he
  exact he



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

-- Source module: Solutions.FSS23105365_EndpointSelectedBlocks
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

/-- A common-domain block sampler for every endpoint pair. Impossible
pairs return a constant path and are excluded by the eventual selector's
support certificate. All endpoint branches use the same number of bits. -/
def totalRoundedBridgeSample {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    Bits (bridgeRoundingSeed (Fintype.card Q) n δ) → (Fin (n + 1) → Q) :=
  if hp : 0 < bridgePartition W s t n then
    fun seed => (chooseRoundedBridgeModel W hW s t n hp δ hδ).sample seed |>.val
  else fun _ _ => s

theorem totalRoundedBridgeSample_eq {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ)
    (hp : 0 < bridgePartition W s t n) (δ : ℝ) (hδ : 0 < δ) :
    totalRoundedBridgeSample W hW s t n δ hδ =
      fun seed => ((chooseRoundedBridgeModel W hW s t n hp δ hδ).sample seed).val := dif_pos hp

theorem totalRoundedBridgeSample_circuit {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : Circuit (Fin (n + 1) × Q), ∃ hbits : B.randomBits = bridgeRoundingSeed (Fintype.card Q) n δ,
      (∀ seed i x, B.eval (fun j => seed (Fin.cast hbits j)) (i, x) =
        decide (totalRoundedBridgeSample W hW s t n δ hδ seed i = x)) ∧
      B.depth ≤ 6 ∧ B.size ≤ bridgeRoundingSize (Fintype.card Q) n δ := by
  by_cases hp : 0 < bridgePartition W s t n
  · let M := chooseRoundedBridgeModel W hW s t n hp δ hδ
    refine ⟨M.circuit, M.randomBits_eq, ?_, M.depth_le, M.size_le⟩
    intro seed i x
    rw [totalRoundedBridgeSample_eq W hW s t n hp δ hδ]
    exact M.eval_eq seed i x
  · let fs : (Fin (n + 1) × Q) → CircuitFormula (bridgeRoundingSeed (Fintype.card Q) n δ) :=
      fun o => .constant (decide (s = o.2))
    obtain ⟨B, hbits, he, hD, hsize⟩ := formula_fintype_family_circuit fs 1 (fun _ => le_rfl)
    refine ⟨B, hbits, ?_, hD.trans (by omega), ?_⟩
    · intro seed i x
      rw [he]
      have hs : totalRoundedBridgeSample W hW s t n δ hδ = fun _ _ => s := dif_neg hp
      rw [hs]
      rfl
    · simp only [fs, formulaCost, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, Fintype.card_prod, Fintype.card_fin, Nat.cast_id] at hsize
      rw [hsize]
      unfold bridgeRoundingSize
      have h : 2 ≤ Fintype.card Q ^ (n + 1) *
          (2 * (bridgeRoundingSeed (Fintype.card Q) n δ *
            (3 * bridgeRoundingSeed (Fintype.card Q) n δ + 2) + 1) + 6) + 2 := by omega
      have hh := Nat.mul_le_mul_left ((n + 1) * Fintype.card Q) h
      simpa only [Nat.mul_two, Nat.add_assoc] using
        Nat.add_le_add_left hh (bridgeRoundingSeed (Fintype.card Q) n δ)

/-- Local endpoint selection has only |Q|^2 branches, regardless of the
number of blocks in the full path. Branches share one block seed and add
two selector layers. No enumeration of complete boundary tuples occurs. -/
theorem endpoint_selected_block_circuit {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (A : Circuit (Q × Q)) (f : Bits A.randomBits → Q × Q)
    (hselect : ∀ seed z, A.eval seed z = decide (f seed = z)) :
    ∃ S : Circuit (Fin (n + 1) × Q),
      ∃ hbits : S.randomBits = A.randomBits + bridgeRoundingSeed (Fintype.card Q) n δ,
      (∀ (seed : Bits (A.randomBits + bridgeRoundingSeed (Fintype.card Q) n δ)) i x,
        let split := seedPairEquiv A.randomBits (bridgeRoundingSeed (Fintype.card Q) n δ) seed
        let z := f split.1
        S.eval (fun j => seed (Fin.cast hbits j)) (i, x) =
          decide (totalRoundedBridgeSample W hW z.1 z.2 n δ hδ split.2 i = x)) ∧
      S.depth ≤ max A.depth 6 + 2 ∧
      S.size ≤ (A.randomBits + bridgeRoundingSeed (Fintype.card Q) n δ) +
        (Fintype.card Q * Fintype.card Q) * A.size +
        ((n + 1) * Fintype.card Q) *
          ((Fintype.card Q * Fintype.card Q) * bridgeRoundingSize (Fintype.card Q) n δ) +
        2 * ((Fintype.card Q * Fintype.card Q) +
          (Fintype.card Q * Fintype.card Q) * ((n + 1) * Fintype.card Q)) +
        ((n + 1) * Fintype.card Q) * (4 * (Fintype.card Q * Fintype.card Q) + 2) := by
  choose B hBbits hBeval hBD hBsize using
    fun z : Q × Q => totalRoundedBridgeSample_circuit W hW z.1 z.2 n δ hδ
  obtain ⟨S, hbits, he, hD, hsize⟩ := conditional_circuit_assembly A B f hselect
    (bridgeRoundingSeed (Fintype.card Q) n δ) 6 (fun z => (hBbits z).le) hBD
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

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_BoundarySelectedBlocks
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

def endpointSelectedBlockSize (r selectorSize q n : ℕ) (δ : ℝ) : ℕ :=
  (r + bridgeRoundingSeed q n δ) + (q * q) * selectorSize +
    ((n + 1) * q) * ((q * q) * bridgeRoundingSize q n δ) +
    2 * ((q * q) + (q * q) * ((n + 1) * q)) + ((n + 1) * q) * (4 * (q * q) + 2)

theorem endpointSelectedBlockSize_mono (r q n A B : ℕ) (δ : ℝ) (h : A ≤ B) :
    endpointSelectedBlockSize r A q n δ ≤ endpointSelectedBlockSize r B q n δ := by
  unfold endpointSelectedBlockSize
  gcongr

theorem endpoint_selected_block_circuit_budget {Q : Type} [Fintype Q] [DecidableEq Q] {r : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (n : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (A : Circuit (Q × Q)) (hA : A.randomBits = r) (f : Bits r → Q × Q)
    (hselect : ∀ seed z, A.eval (fun j => seed (Fin.cast hA j)) z = decide (f seed = z)) :
    ∃ S : Circuit (Fin (n + 1) × Q), ∃ hbits : S.randomBits = r + bridgeRoundingSeed (Fintype.card Q) n δ,
      (∀ (seed : Bits (r + bridgeRoundingSeed (Fintype.card Q) n δ)) i x,
        let split := seedPairEquiv r (bridgeRoundingSeed (Fintype.card Q) n δ) seed
        let z := f split.1
        S.eval (fun j => seed (Fin.cast hbits j)) (i, x) =
          decide (totalRoundedBridgeSample W hW z.1 z.2 n δ hδ split.2 i = x)) ∧
      S.depth ≤ max A.depth 6 + 2 ∧
      S.size ≤ endpointSelectedBlockSize r A.size (Fintype.card Q) n δ := by
  subst r
  exact endpoint_selected_block_circuit W hW n δ hδ A f hselect

def boundarySelectedBlockSize (r boundarySize k q n : ℕ) (δ : ℝ) : ℕ :=
  endpointSelectedBlockSize r (boundarySize + k * q + 6 * (q * q)) q n δ

/-- A local block now reads its two actual boundary states from a single
shared boundary circuit. Its separate tail contains only this block's seed. -/
theorem boundary_selected_block_circuit {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (δ : ℝ) (hδ : 0 < δ)
    (C : Circuit (Fin k × Q)) (f : Bits C.randomBits → (Fin k → Q))
    (hC : ∀ seed i x, C.eval seed (i, x) = decide (f seed i = x))
    (s t : Q) (i : Fin (k + 1)) (n : ℕ) :
    ∃ S : Circuit (Fin (n + 1) × Q),
      ∃ hbits : S.randomBits = C.randomBits + bridgeRoundingSeed (Fintype.card Q) n δ,
      (∀ (seed : Bits (C.randomBits + bridgeRoundingSeed (Fintype.card Q) n δ)) j x,
        let split := seedPairEquiv C.randomBits (bridgeRoundingSeed (Fintype.card Q) n δ) seed
        let y := f split.1
        S.eval (fun p => seed (Fin.cast hbits p)) (j, x) = decide
          (totalRoundedBridgeSample W hW ((Fin.cons s y : Fin (k + 1) → Q) i)
            ((Fin.snoc y t : Fin (k + 1) → Q) i) n δ hδ split.2 j = x)) ∧
      S.depth ≤ max (C.depth + 2) 6 + 2 ∧
      S.size ≤ boundarySelectedBlockSize C.randomBits C.size k (Fintype.card Q) n δ := by
  obtain ⟨A, hA, hAe, hAD, hAsize⟩ := boundary_pair_circuit C f hC s t i
  let pair := fun seed => ((Fin.cons s (f seed) : Fin (k + 1) → Q) i,
    (Fin.snoc (f seed) t : Fin (k + 1) → Q) i)
  obtain ⟨S, hbits, he, hD, hsize⟩ := endpoint_selected_block_circuit_budget W hW n δ hδ A hA pair hAe
  refine ⟨S, hbits, he, ?_, ?_⟩
  · exact hD.trans (Nat.add_le_add_right (max_le_max_right 6 hAD) 2)
  · exact hsize.trans (endpointSelectedBlockSize_mono _ _ _ _ _ δ hAsize)

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

-- Source module: Solutions.FSS23105365_ParallelBridgeBlockCircuit
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

def locallyDrawnBridgeBlocks {Q : Type} [Fintype Q] [DecidableEq Q] {k r : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (s t : Q) (δ : ℝ) (hδ : 0 < δ) (f : Bits r → (Fin k → Q))
    (seed : Bits (r + bridgeBlockSeedBudget (Fintype.card Q) l δ)) (i : Fin (k + 1)) :
    Fin (l i + 1) → Q :=
  let split := seedPairEquiv r (bridgeBlockSeedBudget (Fintype.card Q) l δ) seed
  let y := f split.1
  totalRoundedBridgeSample W hW ((Fin.cons s y : Fin (k + 1) → Q) i)
    ((Fin.snoc y t : Fin (k + 1) → Q) i) (l i) δ hδ
    (seedSlotsEquiv (fun j => bridgeRoundingSeed (Fintype.card Q) (l j) δ) split.2 i)

theorem locallyDrawnBridgeBlocks_eq {Q : Type} [Fintype Q] [DecidableEq Q] {k r : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (s t : Q) (δ : ℝ) (hδ : 0 < δ) (f : Bits r → (Fin k → Q))
    (seed : Bits (r + bridgeBlockSeedBudget (Fintype.card Q) l δ))
    (hy : 0 < bridgeBoundaryMass W l s t (f (seedPairEquiv r (bridgeBlockSeedBudget (Fintype.card Q) l δ) seed).1))
    (i : Fin (k + 1)) :
    locallyDrawnBridgeBlocks W hW l s t δ hδ f seed i =
      (drawnRoundedBlocks W hW l s t
        (f (seedPairEquiv r (bridgeBlockSeedBudget (Fintype.card Q) l δ) seed).1) hy δ hδ
        (seedPairEquiv r (bridgeBlockSeedBudget (Fintype.card Q) l δ) seed).2 i).val := by
  unfold locallyDrawnBridgeBlocks
  dsimp only
  rw [totalRoundedBridgeSample_eq W hW _ _ _ ((bridgeBoundaryMass_pos_iff W hW l s t _).mp hy i) δ hδ]
  rfl

def parallelBridgeBlockSize {k : ℕ} (r boundarySize q : ℕ) (l : Fin (k + 1) → ℕ) (δ : ℝ) : ℕ :=
  (r + bridgeBlockSeedBudget q l δ) +
    (∑ i, ((l i + 1) * q) * boundarySelectedBlockSize r boundarySize k q (l i) δ) +
    (∑ i, (l i + 1) * q)

/-- Every block is now evaluated in parallel. Its boundary prefix is
shared, its conditional seed slots are disjoint, and its endpoint choice
uses only local pairs. This circuit computes all coordinates of all blocks. -/
theorem parallel_bridge_block_circuit {Q : Type} [Fintype Q] [DecidableEq Q] {k : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (s t : Q) (δ : ℝ) (hδ : 0 < δ)
    (C : Circuit (Fin k × Q)) (f : Bits C.randomBits → (Fin k → Q))
    (hC : ∀ seed i x, C.eval seed (i, x) = decide (f seed i = x)) :
    ∃ S : Circuit (Σ i : Fin (k + 1), Fin (l i + 1) × Q),
      ∃ hbits : S.randomBits = C.randomBits + bridgeBlockSeedBudget (Fintype.card Q) l δ,
      (∀ (seed : Bits (C.randomBits + bridgeBlockSeedBudget (Fintype.card Q) l δ)) i j x,
        S.eval (fun p => seed (Fin.cast hbits p)) ⟨i, (j, x)⟩ =
          decide (locallyDrawnBridgeBlocks W hW l s t δ hδ f seed i j = x)) ∧
      S.depth ≤ max (C.depth + 2) 6 + 2 ∧
      S.size ≤ parallelBridgeBlockSize C.randomBits C.size (Fintype.card Q) l δ := by
  choose B hBbits hBe hBD hBsize using
    fun i => boundary_selected_block_circuit W hW δ hδ C f hC s t i (l i)
  let m := fun i => bridgeRoundingSeed (Fintype.card Q) (l i) δ
  obtain ⟨S, hbits, he, hD, hsize⟩ := shared_prefix_circuit_family C.randomBits m B hBbits _ hBD
  refine ⟨S, hbits, ?_, hD, ?_⟩
  · intro seed i j x
    have hb := hBe i (fun p => seed (sharedPrefixSlot C.randomBits m i p)) j x
    dsimp only at hb
    rw [sharedPrefixSlot_split C.randomBits m i seed] at hb
    exact (he seed i (j, x)).trans hb
  · have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      Nat.mul_le_mul_left ((l i + 1) * Fintype.card Q) (hBsize i))
    simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin] at hsize
    unfold parallelBridgeBlockSize
    change S.size ≤ (C.randomBits + ∑ i, m i) + _ + _
    omega

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

-- Source module: Solutions.FSS23105365_DrawnBridgeCircuit
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

theorem drawnBoundaryBridge_wire {Q : Type} [Fintype Q] [DecidableEq Q] {k n r : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (hlen : bridgeBlockLength l = n) (s t : Q) (δ : ℝ) (hδ : 0 < δ)
    (f : Bits r → (Fin k → Q)) (hf : ∀ seed, 0 < bridgeBoundaryMass W l s t (f seed))
    (seed : Bits (r + bridgeBlockSeedBudget (Fintype.card Q) l δ)) (j : Fin (n + 1)) :
    drawnBoundaryBridge W hW l hlen s t δ hδ f seed j =
      locallyDrawnBridgeBlocks W hW l s t δ hδ f seed
        (concatenationWire l hlen j).1 (concatenationWire l hlen j).2 := by
  unfold drawnBoundaryBridge sequentialSeedSample conditionalRoundedBridge
  rw [dif_pos (hf _)]
  change concatenateBridgeBlocksAtLength l hlen s t _
    (drawnRoundedBlocks W hW l s t _ (hf _) δ hδ _) j = _
  rw [concatenateBridgeBlocksAtLength_wire,
    locallyDrawnBridgeBlocks_eq W hW l s t δ hδ f seed (hf _)]

/-- An actual circuit for the complete flat-seed bridge function, given
the boundary circuit. All short blocks execute in parallel and the final
path is fixed output wiring, so depth is independent of the block count. -/
theorem drawn_boundary_bridge_circuit {Q : Type} [Fintype Q] [DecidableEq Q] {k n : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (hlen : bridgeBlockLength l = n) (s t : Q) (δ : ℝ) (hδ : 0 < δ)
    (C : Circuit (Fin k × Q)) (f : Bits C.randomBits → (Fin k → Q))
    (hC : ∀ seed i x, C.eval seed (i, x) = decide (f seed i = x))
    (hf : ∀ seed, 0 < bridgeBoundaryMass W l s t (f seed)) :
    ∃ S : Circuit (Fin (n + 1) × Q),
      ∃ hbits : S.randomBits = C.randomBits + bridgeBlockSeedBudget (Fintype.card Q) l δ,
      (∀ (seed : Bits (C.randomBits + bridgeBlockSeedBudget (Fintype.card Q) l δ)) j x,
        S.eval (fun p => seed (Fin.cast hbits p)) (j, x) =
          decide (drawnBoundaryBridge W hW l hlen s t δ hδ f seed j = x)) ∧
      S.depth ≤ max (C.depth + 2) 6 + 2 ∧
      S.size ≤ parallelBridgeBlockSize C.randomBits C.size (Fintype.card Q) l δ + (n + 1) * Fintype.card Q := by
  obtain ⟨B, hBbits, hBe, hBD, hBsize⟩ := parallel_bridge_block_circuit W hW l s t δ hδ C f hC
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
    rw [drawnBoundaryBridge_wire W hW l hlen s t δ hδ f hf seed j]
    exact he
  · simp only [Fintype.card_prod, Fintype.card_fin] at hSsize
    omega

theorem drawn_boundary_bridge_circuit_budget {Q : Type} [Fintype Q] [DecidableEq Q] {k n r : ℕ}
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (l : Fin (k + 1) → ℕ)
    (hlen : bridgeBlockLength l = n) (s t : Q) (δ : ℝ) (hδ : 0 < δ)
    (C : Circuit (Fin k × Q)) (hCbits : C.randomBits = r) (f : Bits r → (Fin k → Q))
    (hC : ∀ seed i x, C.eval (fun j => seed (Fin.cast hCbits j)) (i, x) = decide (f seed i = x))
    (hf : ∀ seed, 0 < bridgeBoundaryMass W l s t (f seed)) :
    ∃ S : Circuit (Fin (n + 1) × Q),
      ∃ hbits : S.randomBits = r + bridgeBlockSeedBudget (Fintype.card Q) l δ,
      (∀ (seed : Bits (r + bridgeBlockSeedBudget (Fintype.card Q) l δ)) j x,
        S.eval (fun p => seed (Fin.cast hbits p)) (j, x) =
          decide (drawnBoundaryBridge W hW l hlen s t δ hδ f seed j = x)) ∧
      S.depth ≤ max (C.depth + 2) 6 + 2 ∧
      S.size ≤ parallelBridgeBlockSize r C.size (Fintype.card Q) l δ + (n + 1) * Fintype.card Q := by
  subst r
  exact drawn_boundary_bridge_circuit W hW l hlen s t δ hδ C f hC hf

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

theorem parallelBridgeBlockSize_mono {k : ℕ} (r q A B : ℕ)
    (l : Fin (k + 1) → ℕ) (δ : ℝ) (hAB : A ≤ B) :
    parallelBridgeBlockSize r A q l δ ≤ parallelBridgeBlockSize r B q l δ := by
  have hs : (∑ i, ((l i + 1) * q) * boundarySelectedBlockSize r A k q (l i) δ) ≤
      ∑ i, ((l i + 1) * q) * boundarySelectedBlockSize r B k q (l i) δ := by
    apply Finset.sum_le_sum
    intro i _
    apply Nat.mul_le_mul_left
    exact endpointSelectedBlockSize_mono _ _ _ _ _ δ (by omega)
  unfold parallelBridgeBlockSize
  omega

def periodicBridgeCircuitSize (q M boundarySize n L : ℕ) (δ : ℝ) : ℕ :=
  let k := cutoffBoundaryCount n L
  let m := roundingSeed M δ
  parallelBridgeBlockSize (k * m) (k * m + (k * q) * boundarySize + k * q)
    q (cutoffBlockLengths n L) δ + (n + 1) * q

theorem periodicBridgeCircuitSize_mono (q M A B n L : ℕ) (δ : ℝ) (hAB : A ≤ B) :
    periodicBridgeCircuitSize q M A n L δ ≤ periodicBridgeCircuitSize q M B n L δ := by
  apply Nat.add_le_add_right
  apply parallelBridgeBlockSize_mono
  gcongr

/-- The complete periodic bridge sampler has depth at most ten. The
boundary circuit is copied on disjoint bits; local endpoint selection and
all short blocks run in parallel; concatenation uses fixed output wires. -/
theorem drawn_periodic_bridge_circuit {Q : Type} [Fintype Q] [DecidableEq Q]
    (W K : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (a : ℕ) (s t : Q) (n L : ℕ)
    (δ : ℝ) (hδ : 0 < δ)
    (f : Bits (roundingSeed (Fintype.card (PositiveSupportClass (K ^ a) s)) δ) →
      PositiveSupportClass (K ^ a) s)
    (C : Circuit Q) (hCbits : C.randomBits = roundingSeed (Fintype.card (PositiveSupportClass (K ^ a) s)) δ)
    (hCe : ∀ seed x, C.eval (fun j => seed (Fin.cast hCbits j)) x = decide ((f seed).val = x))
    (hCD : C.depth ≤ 6)
    (hf : ∀ y, 0 < embeddedProductLaw (k := cutoffBoundaryCount n L)
      (fun z : PositiveSupportClass (K ^ a) s => z.val) (fun _ => finiteSeedLaw f) y →
      0 < bridgeBoundaryMass (fun x y => W x y) (cutoffBlockLengths n L) s t y) :
    ∃ S : Circuit (Fin (n + 1) × Q),
      ∃ hbits : S.randomBits = periodicBridgeSeedBudget (Fintype.card Q)
        (Fintype.card (PositiveSupportClass (K ^ a) s)) (cutoffBlockLengths n L) δ,
      (∀ seed i x, S.eval (fun j => seed (Fin.cast hbits j)) (i, x) =
        decide (drawnPeriodicBridge W K hW a s t n L δ hδ f seed i = x)) ∧
      S.depth ≤ 10 ∧ S.size ≤ periodicBridgeCircuitSize (Fintype.card Q)
        (Fintype.card (PositiveSupportClass (K ^ a) s)) C.size n L δ := by
  let embed := fun z : PositiveSupportClass (K ^ a) s => z.val
  let b := embeddedRepeatedSeedSample (cutoffBoundaryCount n L) embed f
  obtain ⟨B, hBbits, hBe, hBD, hBsize⟩ := repeated_boundary_circuit (cutoffBoundaryCount n L) embed f C hCbits hCe
  have hb : ∀ seed, 0 < bridgeBoundaryMass (fun x y => W x y) (cutoffBlockLengths n L) s t (b seed) := by
    intro seed
    apply hf
    rw [← embeddedRepeatedSeedSample_law]
    exact (finiteSeedLaw_pos_iff b (b seed)).mpr ⟨seed, rfl⟩
  obtain ⟨S, hbits, he, hD, hsize⟩ := drawn_boundary_bridge_circuit_budget (fun x y => W x y) hW
    (cutoffBlockLengths n L) (cutoffBlockLengths_total n L) s t δ hδ B hBbits b hBe hb
  refine ⟨S, hbits, he, ?_, ?_⟩
  · omega
  · exact hsize.trans (Nat.add_le_add_right (parallelBridgeBlockSize_mono _ _ _ _ _ δ hBsize) _)

def boundaryRoundingCircuitSize (q M : ℕ) (δ : ℝ) : ℕ :=
  let m := roundingSeed M δ
  m + q * (M * (2 * (m * (3 * m + 2) + 1) + 6) + 2)

/-- Complete internal long-bridge realization: the same function has an
explicit fair-bit domain, a depth-ten actual circuit, positive support,
and the full internal TV bound. Global SCC/category assembly and the
asymptotic polynomial estimates remain separate obligations. -/
theorem periodic_bridge_circuit_realization {Q : Type} [Fintype Q] [DecidableEq Q]
    (W K : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (a : ℕ) (ha : 0 < a)
    (C ρ : ℝ) (hC : 0 < C) (hρ : 0 < ρ)
    (happ : PeriodicBridgeBoundaryApproximation W K a C ρ)
    (s t : Q) (N n L : ℕ) (ε δ : ℝ) (hL : 0 < L) (had : a ∣ L)
    (hεle : ε ≤ 1) (herr : C * ρ ^ (L / a) ≤ ε / (8 * (N + 1 : ℕ)))
    (hn : n ≤ N) (hLn : L ≤ n) (hpart : 0 < bridgePartition (fun x y => W x y) s t n)
    (hδ : 0 < δ) :
    ∃ g : Bits (periodicBridgeSeedBudget (Fintype.card Q)
      (Fintype.card (PositiveSupportClass (K ^ a) s)) (cutoffBlockLengths n L) δ) → (Fin (n + 1) → Q),
      ∃ S : Circuit (Fin (n + 1) × Q),
      ∃ hbits : S.randomBits = periodicBridgeSeedBudget (Fintype.card Q)
        (Fintype.card (PositiveSupportClass (K ^ a) s)) (cutoffBlockLengths n L) δ,
      (∀ seed i x, S.eval (fun j => seed (Fin.cast hbits j)) (i, x) = decide (g seed i = x)) ∧
      S.depth ≤ 10 ∧ S.size ≤ periodicBridgeCircuitSize (Fintype.card Q)
        (Fintype.card (PositiveSupportClass (K ^ a) s))
        (boundaryRoundingCircuitSize (Fintype.card Q) (Fintype.card (PositiveSupportClass (K ^ a) s)) δ) n L δ ∧
      (∀ seed, 0 < bridgeWeight (fun x y => W x y) s t n (g seed)) ∧
      tv (finiteSeedLaw g) (normalizeWeights (bridgeWeight (fun x y => W x y) s t n)) ≤
        ε / 4 + (2 * cutoffBoundaryCount n L + 1 : ℕ) * δ := by
  obtain ⟨f, B, hBbits, hBe, hBD, hBsize, hb, hsum, hsupp, htv⟩ :=
    rounded_periodic_boundary_sampler W K hW a ha C ρ hC hρ happ s t N n L ε δ
      hL had hεle herr hn hLn hpart hδ
  obtain ⟨S, hbits, he, hD, hsize⟩ := drawn_periodic_bridge_circuit W K hW a s t n L δ hδ
    f B hBbits hBe hBD hsupp
  let g := drawnPeriodicBridge W K hW a s t n L δ hδ f
  have hg := drawnPeriodicBridge_law W K hW a s t n L δ hδ f hsupp
  obtain ⟨_, _, hsupport, herror⟩ := rounded_boundary_block_sampler (fun x y => W x y) hW
    (cutoffBlockLengths n L) (cutoffBlockLengths_total n L) s t hpart
    (embeddedProductLaw (fun z : PositiveSupportClass (K ^ a) s => z.val) (fun _ => finiteSeedLaw f))
    hb hsum hsupp (ε / 4 + cutoffBoundaryCount n L * δ) δ hδ htv
  refine ⟨g, S, hbits, he, hD,
    hsize.trans (periodicBridgeCircuitSize_mono _ _ _ _ _ _ δ hBsize), ?_, ?_⟩
  · intro seed
    apply hsupport
    change 0 < roundedPeriodicBridgeLaw W K hW a s t n L δ hδ f (g seed)
    rw [← hg]
    exact (finiteSeedLaw_pos_iff g (g seed)).mpr ⟨seed, rfl⟩
  · change tv (finiteSeedLaw (drawnPeriodicBridge W K hW a s t n L δ hδ f)) _ ≤ _
    rw [hg]
    apply herror.trans
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
    ring_nf
    exact le_rfl

/-- The same complete circuit computes the endpoint-path sampler with
its allocated internal error. Endpoint transport changes no output value
or random bit; the size remains the explicit construction bound. -/
theorem periodic_endpoint_bridge_circuit {Q : Type} [Fintype Q] [DecidableEq Q]
    (W K : Matrix Q Q ℝ) (hW : ∀ x y, 0 ≤ W x y) (a : ℕ) (ha : 0 < a)
    (C ρ : ℝ) (hC : 0 < C) (hρ : 0 < ρ)
    (happ : PeriodicBridgeBoundaryApproximation W K a C ρ)
    (s t : Q) (N n L : ℕ) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1)
    (hL : 0 < L) (had : a ∣ L)
    (herr : C * ρ ^ (L / a) ≤ ε / (8 * (N + 1 : ℕ)))
    (hn : n ≤ N) (hLn : L ≤ n) (hpart : 0 < bridgePartition (fun x y => W x y) s t n) :
    let δ := ε / (8 * (N + 1 : ℕ))
    ∃ g : Bits (periodicBridgeSeedBudget (Fintype.card Q)
      (Fintype.card (PositiveSupportClass (K ^ a) s)) (cutoffBlockLengths n L) δ) → EndpointPath Q s t n,
      ∃ S : Circuit (Fin (n + 1) × Q),
      ∃ hbits : S.randomBits = periodicBridgeSeedBudget (Fintype.card Q)
        (Fintype.card (PositiveSupportClass (K ^ a) s)) (cutoffBlockLengths n L) δ,
      (∀ seed i x, S.eval (fun j => seed (Fin.cast hbits j)) (i, x) = decide ((g seed).val i = x)) ∧
      S.depth ≤ 10 ∧ S.size ≤ periodicBridgeCircuitSize (Fintype.card Q)
        (Fintype.card (PositiveSupportClass (K ^ a) s))
        (boundaryRoundingCircuitSize (Fintype.card Q) (Fintype.card (PositiveSupportClass (K ^ a) s)) δ) n L δ ∧
      (∀ seed, 0 < edgePathWeight (fun x y => W x y) (g seed).val) ∧
      tv (finiteSeedLaw g)
        (normalizeWeights (fun γ : EndpointPath Q s t n => edgePathWeight (fun x y => W x y) γ.val)) ≤ ε / 2 := by
  dsimp only
  have hk := ((cutoff_block_count_bound n L).2).trans hn
  obtain ⟨hδ, hbudget⟩ := internal_bridge_rounding_error_budget N (cutoffBoundaryCount n L) hk ε hε
  obtain ⟨f, S, hbits, he, hD, hsize, hf, htv⟩ := periodic_bridge_circuit_realization W K hW a ha C ρ hC hρ
    happ s t N n L ε (ε / (8 * (N + 1 : ℕ))) hL had hεle herr hn hLn hpart hδ
  obtain ⟨g, hval, hpos, hdist⟩ := endpoint_seed_transport (fun x y => W x y) hW s t f hf
  refine ⟨g, S, hbits, ?_, hD, hsize, hpos, ?_⟩
  · intro seed i x
    rw [hval]
    exact he seed i x
  · rw [hdist]
    exact htv.trans hbudget

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

def sccPeriodicSeedBudget {Q : Type} [Fintype Q] [DecidableEq Q]
    {W : Matrix Q Q ℝ} {s : Q} (model : SCCPeriodicModel W s) (x : SCCState W s)
    (n L : ℕ) (δ : ℝ) : ℕ :=
  periodicBridgeSeedBudget (Fintype.card (SCCState W s))
    (Fintype.card (PositiveSupportClass (doobMatrix (sccMatrix W s) model.lam model.right ^ model.blockExponent) x))
    (cutoffBlockLengths n L) δ

def sccPeriodicCircuitSize {Q : Type} [Fintype Q] [DecidableEq Q]
    {W : Matrix Q Q ℝ} {s : Q} (model : SCCPeriodicModel W s) (x : SCCState W s)
    (n L : ℕ) (δ : ℝ) : ℕ :=
  let q := Fintype.card (SCCState W s)
  let M := Fintype.card (PositiveSupportClass
    (doobMatrix (sccMatrix W s) model.lam model.right ^ model.blockExponent) x)
  periodicBridgeCircuitSize q M (boundaryRoundingCircuitSize q M δ) n L δ +
    (n + 1) * q + 2 * ((n + 1) * Fintype.card Q)

/-- A long bridge in an actual SCC is sampled in the original state
alphabet by a depth-eleven circuit. The statement retains the explicit
seed and size formulas and the common-cutoff mixing condition. -/
theorem scc_periodic_bridge_circuit {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j) (s : Q) (model : SCCPeriodicModel W s)
    (x y : SCCState W s) (N n L : ℕ) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1)
    (hL : 0 < L) (had : model.blockExponent ∣ L)
    (hmix : model.coefficient * model.rate ^ (L / model.blockExponent) ≤ ε / (8 * (N + 1 : ℕ)))
    (hn : n ≤ N) (hLn : L ≤ n) (hpart : 0 < bridgePartition (fun i j => W i j) x.val y.val n) :
    let δ := ε / (8 * (N + 1 : ℕ))
    ∃ g : Bits (sccPeriodicSeedBudget model x n L δ) → EndpointPath Q x.val y.val n,
      ∃ S : Circuit (Fin (n + 1) × Q), ∃ hbits : S.randomBits = sccPeriodicSeedBudget model x n L δ,
      (∀ seed i z, S.eval (fun j => seed (Fin.cast hbits j)) (i, z) = decide ((g seed).val i = z)) ∧
      S.depth ≤ 11 ∧ S.size ≤ sccPeriodicCircuitSize model x n L δ ∧
      (∀ seed, 0 < edgePathWeight (fun i j => W i j) (g seed).val) ∧
      tv (finiteSeedLaw g) (normalizeWeights
        (fun γ : EndpointPath Q x.val y.val n => edgePathWeight (fun i j => W i j) γ.val)) ≤ ε / 2 := by
  have hWr : ∀ i j, 0 ≤ sccMatrix W s i j := fun i j => hW i.val j.val
  have hpart' : 0 < bridgePartition (fun i j => sccMatrix W s i j) x y n := by
    rw [scc_bridgePartition W hW]
    exact hpart
  obtain ⟨f, C, hCbits, hCe, hCD, hCsize, hf, herr⟩ := periodic_endpoint_bridge_circuit
    (sccMatrix W s) (doobMatrix (sccMatrix W s) model.lam model.right) hWr
    model.blockExponent model.exponent_pos model.coefficient model.rate model.coefficient_pos model.rate_pos
    model.approximation x y N n L ε hε hεle hL had hmix hn hLn hpart'
  obtain ⟨g, S, hbits, he, hD, hsize, hpos, herror⟩ :=
    scc_endpoint_circuit_transport W hW s x y f C hCbits hCe hf (ε / 2) herr
  refine ⟨g, S, hbits, he, by omega, ?_, hpos, herror⟩
  unfold sccPeriodicCircuitSize
  dsimp only
  omega

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

theorem certified_rounded_bridge {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Q → Q → ℝ) (hW : ∀ x y, 0 ≤ W x y) (s t : Q) (n : ℕ)
    (hpart : 0 < bridgePartition W s t n) (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : CertifiedBridgeSampler W s t n δ,
      B.seedLength = bridgeRoundingSeed (Fintype.card Q) n δ ∧
      B.circuit.depth ≤ 6 ∧ B.circuit.size ≤ bridgeRoundingSize (Fintype.card Q) n δ := by
  let R := chooseRoundedBridgeModel W hW s t n hpart δ hδ
  exact ⟨{ seedLength := bridgeRoundingSeed (Fintype.card Q) n δ
           sample := R.sample
           circuit := R.circuit
           randomBits_eq := R.randomBits_eq
           eval_eq := R.eval_eq
           sample_positive := R.sample_positive
           error := R.error }, rfl, R.depth_le, R.size_le⟩

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

-- Source module: Solutions.FSS23105365_ComponentSegmentSampler
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped Matrix

def componentSegmentSeedBudget {Q : Type} [Fintype Q] [DecidableEq Q]
    {W : Matrix Q Q ℝ} (models : ∀ c : CyclicSCCIndex W, SCCPeriodicModel W c.val)
    (s : Q) (N n L : ℕ) (ε : ℝ) : ℕ := by
  classical
  exact if n ≤ 1 then 0 else if n < L then bridgeRoundingSeed (Fintype.card Q) n (ε / 2)
    else if hc : CyclicSCC W s then
      sccPeriodicSeedBudget (models ⟨s, hc⟩) ⟨s, rfl⟩ n L (ε / (8 * (N + 1 : ℕ)))
    else 0

def componentSegmentCircuitSize {Q : Type} [Fintype Q] [DecidableEq Q]
    {W : Matrix Q Q ℝ} (models : ∀ c : CyclicSCCIndex W, SCCPeriodicModel W c.val)
    (s : Q) (N n L : ℕ) (ε : ℝ) : ℕ := by
  classical
  exact if n ≤ 1 then 2 * ((n + 1) * Fintype.card Q)
    else if n < L then bridgeRoundingSize (Fintype.card Q) n (ε / 2)
    else if hc : CyclicSCC W s then
      sccPeriodicCircuitSize (models ⟨s, hc⟩) ⟨s, rfl⟩ n L (ε / (8 * (N + 1 : ℕ)))
    else 0

/-- Every positive category segment is covered: fixed zero/one-edge
paths, short rounded bridges, or long bridges in an actual cyclic SCC.
The same selected model carries its function, circuit and error proof. -/
theorem component_segment_sampler {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j)
    (models : ∀ c : CyclicSCCIndex W, SCCPeriodicModel W c.val)
    (s t : Q) (N n L : ℕ) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1)
    (hL : 0 < L) (hn : n ≤ N)
    (hmix : ∀ c, (models c).blockExponent ∣ L ∧
      (models c).coefficient * (models c).rate ^ (L / (models c).blockExponent) ≤ ε / (8 * (N + 1 : ℕ)))
    (hkind : n ≤ 1 ∨ graphComponent (fun i j => 0 < W i j) s = graphComponent (fun i j => 0 < W i j) t)
    (hpart : 0 < bridgePartition (fun i j => W i j) s t n) :
    ∃ B : CertifiedBridgeSampler (fun i j => W i j) s t n (ε / 2),
      B.seedLength = componentSegmentSeedBudget models s N n L ε ∧
      B.circuit.depth ≤ 11 ∧ B.circuit.size ≤ componentSegmentCircuitSize models s N n L ε := by
  classical
  by_cases hfixed : n ≤ 1
  · obtain ⟨B, hm, hD, hsize⟩ := certified_fixed_bridge (fun i j => W i j) hW s t hfixed hpart
      (ε / 2) (by positivity)
    refine ⟨B, ?_, hD.trans (by omega), ?_⟩
    · simpa only [componentSegmentSeedBudget, if_pos hfixed] using hm
    · simpa only [componentSegmentCircuitSize, if_pos hfixed] using hsize.le
  · by_cases hshort : n < L
    · obtain ⟨B, hm, hD, hsize⟩ := certified_rounded_bridge (fun i j => W i j) hW s t n hpart
        (ε / 2) (by positivity)
      refine ⟨B, ?_, hD.trans (by omega), ?_⟩
      · simpa only [componentSegmentSeedBudget, if_neg hfixed, if_pos hshort] using hm
      · simpa only [componentSegmentCircuitSize, if_neg hfixed, if_pos hshort] using hsize
    · have hst := hkind.resolve_left hfixed
      let x : SCCState W s := ⟨s, rfl⟩
      let y : SCCState W s := ⟨t, hst.symm⟩
      have hc : CyclicSCC W s := by
        by_contra hnc
        have hz := acyclic_scc_bridge_length_zero W hW s hnc x y n hpart
        omega
      let c : CyclicSCCIndex W := ⟨s, hc⟩
      obtain ⟨f, S, hbits, he, hD, hsize, hf, herr⟩ := scc_periodic_bridge_circuit W hW s (models c)
        x y N n L ε hε hεle hL (hmix c).1 (hmix c).2 hn (by omega) hpart
      let B : CertifiedBridgeSampler (fun i j => W i j) s t n (ε / 2) := {
        seedLength := sccPeriodicSeedBudget (models c) x n L (ε / (8 * (N + 1 : ℕ)))
        sample := f
        circuit := S
        randomBits_eq := hbits
        eval_eq := he
        sample_positive := hf
        error := herr }
      refine ⟨B, ?_, hD, ?_⟩
      · simp only [componentSegmentSeedBudget, if_neg hfixed, if_neg hshort, dif_pos hc]
        rfl
      · simpa only [componentSegmentCircuitSize, if_neg hfixed, if_neg hshort, dif_pos hc] using hsize

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_CategoryBridgeApproximation
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

local instance {q n : ℕ} : DecidableEq (GraphCategory (Fin q) n) := Classical.decEq _

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

/-- Positive paths in the constructed boundary fiber belong to the actual
accepting category. Invalid paths contribute zero and are never output. -/
theorem accepting_category_support_of_blocks {q n : ℕ} (M : MarkovChain q)
    (F : Finset (Fin q)) (γ : Path q n) (hF : γ (Fin.last n) ∈ F) (hγ : 0 < pathLaw M γ)
    (η : Path q n) (hmatch : CategoryBlockMatches (fun x y => 0 < M.transition x y) γ η)
    (hη : 0 < edgePathWeight M.transition η) :
    0 < fiberWeight (graphCategory (fun x y => 0 < M.transition x y)) (acceptingPathWeight M F)
      (graphCategory (fun x y => 0 < M.transition x y) γ) η := by
  classical
  have hg := (finitePathWeight_pos_iff M.initial M.transition M.initial_nonneg
    M.transition_nonneg γ).mp hγ
  have hi : 0 < M.initial (η 0) := hmatch.1 ▸ hg.1
  have he := (edgePathWeight_pos_iff M.transition M.transition_nonneg η).mp hη
  have hp : 0 < pathLaw M η := (finitePathWeight_pos_iff M.initial M.transition
    M.initial_nonneg M.transition_nonneg η).mpr ⟨hi, he⟩
  have hc : graphCategory (fun x y => 0 < M.transition x y) γ =
      graphCategory (fun x y => 0 < M.transition x y) η := by
    apply (graphCategory_eq_block_observation _ γ η hg.2 he).mpr
    exact hmatch
  have hηF : η (Fin.last n) ∈ F := hmatch.2.1 ▸ hF
  rw [fiberWeight, if_pos hc.symm, acceptingPathWeight, if_pos hηF]
  exact hp



end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_AssembledCategorySampler
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators



def acceptingCategoryRepresentative {q n : ℕ} (M : MarkovChain q) (F : Finset (Fin q))
    (c : AcceptingCategory M F n) : Path q n := (acceptingCategory_has_path M F c).choose

theorem acceptingCategoryRepresentative_spec {q n : ℕ} (M : MarkovChain q) (F : Finset (Fin q))
    (c : AcceptingCategory M F n) :
    graphCategory (fun x y => 0 < M.transition x y) (acceptingCategoryRepresentative M F c) = c.val ∧
    acceptingCategoryRepresentative M F c (Fin.last n) ∈ F ∧
    0 < pathLaw M (acceptingCategoryRepresentative M F c) := (acceptingCategory_has_path M F c).choose_spec









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

/-- The actual category decomposition supplies every hypothesis of the
uniform segment construction. No unknown block-sampler existence remains
in this theorem: fixed, short and long SCC cases are all instantiated. -/
theorem category_segment_samplers {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j)
    (models : ∀ c : CyclicSCCIndex W, SCCPeriodicModel W c.val)
    {n : ℕ} (γ : Fin (n + 1) → Q) (hγ : 0 < edgePathWeight (fun i j => W i j) γ)
    (L : ℕ) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1) (hL : 0 < L)
    (hmix : ∀ c, (models c).blockExponent ∣ L ∧
      (models c).coefficient * (models c).rate ^ (L / (models c).blockExponent) ≤ ε / (8 * (n + 1 : ℕ))) :
    let R := fun i j => 0 < W i j
    ∀ i : Fin ((graphInteriorCuts R γ).card + 1),
      ∃ B : CertifiedBridgeSampler (fun i j => W i j) (categorySegmentStart R γ i)
        (categorySegmentEnd R γ i) (graphCategoryBlockLengths R γ i) (ε / 2),
        B.seedLength = componentSegmentSeedBudget models (categorySegmentStart R γ i) n
          (graphCategoryBlockLengths R γ i) L ε ∧ B.circuit.depth ≤ 11 ∧
        B.circuit.size ≤ componentSegmentCircuitSize models (categorySegmentStart R γ i) n
          (graphCategoryBlockLengths R γ i) L ε := by
  dsimp only
  intro i
  apply component_segment_sampler W hW models _ _ n _ L ε hε hεle hL
    (category_segment_length_le _ γ i) hmix (category_segment_kind _ γ i)
  exact positive_observed_block_partitions (fun i j => W i j) hW
    (graphCategoryBlockLengths (fun i j => 0 < W i j) γ)
    (graphCategoryBlockLengths_total (fun i j => 0 < W i j) γ) γ hγ i

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

-- Source module: Solutions.FSS23105365_ConstructedCategoryCircuit
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

def categorySamplerSeedBudget {Q : Type} [Fintype Q] [DecidableEq Q]
    {W : Matrix Q Q ℝ} (models : ∀ c : CyclicSCCIndex W, SCCPeriodicModel W c.val)
    {n : ℕ} (γ : Fin (n + 1) → Q) (L : ℕ) (ε : ℝ) : ℕ :=
  ∑ i : Fin ((graphInteriorCuts (fun i j => 0 < W i j) γ).card + 1),
    componentSegmentSeedBudget models (categorySegmentStart (fun i j => 0 < W i j) γ i) n
      (graphCategoryBlockLengths (fun i j => 0 < W i j) γ i) L ε

def categorySamplerCircuitSize {Q : Type} [Fintype Q] [DecidableEq Q]
    {W : Matrix Q Q ℝ} (models : ∀ c : CyclicSCCIndex W, SCCPeriodicModel W c.val)
    {n : ℕ} (γ : Fin (n + 1) → Q) (L : ℕ) (ε : ℝ) : ℕ :=
  let R := fun i j => 0 < W i j
  let l := graphCategoryBlockLengths R γ
  categorySamplerSeedBudget models γ L ε +
    (∑ i, ((l i + 1) * Fintype.card Q) *
      componentSegmentCircuitSize models (categorySegmentStart R γ i) n (l i) L ε) +
    (∑ i, (l i + 1) * Fintype.card Q) + (n + 1) * Fintype.card Q

/-- A complete category sampler now consists of constructed segment
functions and one actual parallel concatenation circuit. It has depth
eleven, explicit resources, correct category support, and the sum of the
segment error allocations. No unknown block laws are supplied. -/
theorem constructed_category_circuit {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j)
    (models : ∀ c : CyclicSCCIndex W, SCCPeriodicModel W c.val)
    {n : ℕ} (γ : Fin (n + 1) → Q) (hγ : 0 < edgePathWeight (fun i j => W i j) γ)
    (L : ℕ) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1) (hL : 0 < L)
    (hmix : ∀ c, (models c).blockExponent ∣ L ∧
      (models c).coefficient * (models c).rate ^ (L / (models c).blockExponent) ≤ ε / (8 * (n + 1 : ℕ))) :
    ∃ f : Bits (categorySamplerSeedBudget models γ L ε) → (Fin (n + 1) → Q),
      ∃ S : Circuit (Fin (n + 1) × Q), ∃ hbits : S.randomBits = categorySamplerSeedBudget models γ L ε,
      (∀ seed i x, S.eval (fun j => seed (Fin.cast hbits j)) (i, x) = decide (f seed i = x)) ∧
      S.depth ≤ 11 ∧ S.size ≤ categorySamplerCircuitSize models γ L ε ∧
      (∀ seed, CategoryBlockMatches (fun i j => 0 < W i j) γ (f seed) ∧
        0 < edgePathWeight (fun i j => W i j) (f seed)) ∧
      tv (finiteSeedLaw f) (normalizeWeights (fun η =>
        if CategoryBlockMatches (fun i j => 0 < W i j) γ η then edgePathWeight (fun i j => W i j) η else 0)) ≤
        ((graphInteriorCuts (fun i j => 0 < W i j) γ).card + 1 : ℕ) * (ε / 2) := by
  classical
  let R := fun i j => 0 < W i j
  let l := graphCategoryBlockLengths R γ
  let y := bridgeBoundaryObservation l (graphCategoryBlockLengths_total R γ) γ
  choose B hBm hBD hBsize using category_segment_samplers W hW models γ hγ L ε hε hεle hL hmix
  let g0 := certifiedConcatenatedSample (fun i j => W i j) l (graphCategoryBlockLengths_total R γ)
    (γ 0) (γ (Fin.last n)) y (fun _ => ε / 2) B
  have hg0 : finiteSeedLaw g0 = categoryApproximateLaw R γ (fun i => finiteSeedLaw (B i).sample) :=
    certifiedConcatenatedSample_law (fun i j => W i j) l (graphCategoryBlockLengths_total R γ)
      (γ 0) (γ (Fin.last n)) y (fun _ => ε / 2) B
  obtain ⟨S, hbits, he, hD, hsize⟩ := certified_concatenation_circuit (fun i j => W i j) l
    (graphCategoryBlockLengths_total R γ) (γ 0) (γ (Fin.last n)) y (fun _ => ε / 2) B 11 hBD
  have hr : (∑ i, (B i).seedLength) = categorySamplerSeedBudget models γ L ε := by
    simp only [hBm]
    rfl
  let f := fun seed : Bits (categorySamplerSeedBudget models γ L ε) =>
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
    unfold categorySamplerCircuitSize
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

-- Source module: Solutions.FSS23105365_AcceptingCategoryCircuit
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

local instance {q n : ℕ} : DecidableEq (GraphCategory (Fin q) n) := Classical.decEq _

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

/-- For every actual positive accepting category, all its segment
samplers and its depth-eleven circuit are constructed. The number of
segments is bounded by the original state count, so allocating epsilon
over 2*q gives total conditional error at most epsilon/2. -/
theorem constructed_accepting_category_circuit {q n : ℕ} (hq : 0 < q)
    (M : MarkovChain q) (F : Finset (Fin q)) (c : AcceptingCategory M F n)
    (models : ∀ d : CyclicSCCIndex (M.transition : Matrix (Fin q) (Fin q) ℝ),
      SCCPeriodicModel M.transition d.val)
    (L : ℕ) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1) (hL : 0 < L)
    (hmix : ∀ d, (models d).blockExponent ∣ L ∧
      (models d).coefficient * (models d).rate ^ (L / (models d).blockExponent) ≤
        categorySegmentTolerance q ε / (8 * (n + 1 : ℕ))) :
    ∃ f : Bits (categorySamplerSeedBudget models (acceptingCategoryRepresentative M F c) L
      (categorySegmentTolerance q ε)) → Path q n,
      ∃ S : Circuit (Fin (n + 1) × Fin q),
      ∃ hbits : S.randomBits = categorySamplerSeedBudget models (acceptingCategoryRepresentative M F c) L
        (categorySegmentTolerance q ε),
      (∀ seed i x, S.eval (fun j => seed (Fin.cast hbits j)) (i, x) = decide (f seed i = x)) ∧
      S.depth ≤ 11 ∧ S.size ≤ categorySamplerCircuitSize models (acceptingCategoryRepresentative M F c) L
        (categorySegmentTolerance q ε) ∧
      (∀ seed, 0 < fiberWeight (graphCategory (fun x y => 0 < M.transition x y))
        (acceptingPathWeight M F) c.val (f seed)) ∧
      tv (finiteSeedLaw f) (normalizeWeights (fiberWeight (graphCategory (fun x y => 0 < M.transition x y))
        (acceptingPathWeight M F) c.val)) ≤ ε / 2 := by
  classical
  let γ := acceptingCategoryRepresentative M F c
  have hspec := acceptingCategoryRepresentative_spec M F c
  have hgraph := ((finitePathWeight_pos_iff M.initial M.transition M.initial_nonneg
    M.transition_nonneg γ).mp hspec.2.2).2
  have hedge := (edgePathWeight_pos_iff M.transition M.transition_nonneg γ).mpr hgraph
  obtain ⟨hη, hηle, hηeq⟩ := categorySegmentTolerance_bounds q hq ε hε hεle
  obtain ⟨f, S, hbits, he, hD, hsize, hsupp, htv⟩ := constructed_category_circuit
    (M.transition : Matrix (Fin q) (Fin q) ℝ) M.transition_nonneg models γ hedge L
    (categorySegmentTolerance q ε) hη hηle hL hmix
  refine ⟨f, S, hbits, he, hD, hsize, ?_, ?_⟩
  · intro seed
    rw [← hspec.1]
    exact accepting_category_support_of_blocks M F γ hspec.2.1 hspec.2.2 (f seed)
      (hsupp seed).1 (hsupp seed).2
  · rw [← hspec.1, accepting_category_normalize_of_path M F γ hspec.2.1 hspec.2.2]
    apply htv.trans
    have hk : (graphInteriorCuts (fun x y => 0 < M.transition x y) γ).card + 1 ≤ 2 * q := by
      have h := graphCategoryBlockLengths_count (fun x y => 0 < M.transition x y) γ hgraph
      simpa only [Fintype.card_fin] using h.trans (Nat.sub_le _ _)
    have hk' : ((graphInteriorCuts (fun x y => 0 < M.transition x y) γ).card + 1 : ℕ) ≤ (2 * q : ℝ) := by
      exact_mod_cast hk
    exact (mul_le_mul_of_nonneg_right hk' (div_nonneg hη.le (by norm_num))).trans hηeq.le

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_AcceptingCategorySelector
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators

local instance categorySelectorDecEq {q n : ℕ} : DecidableEq (GraphCategory (Fin q) n) := Classical.decEq _

def acceptingCategoryChoiceLaw {q n : ℕ} (M : MarkovChain q) (F : Finset (Fin q)) :
    AcceptingCategory M F n → ℝ :=
  normalizeWeights (fun c => fiberMass (graphCategory (fun x y => 0 < M.transition x y))
    (acceptingPathWeight M F) c.val)

theorem acceptingCategoryChoiceLaw_nonneg {q n : ℕ} (M : MarkovChain q) (F : Finset (Fin q)) :
    ∀ c : AcceptingCategory M F n, 0 ≤ acceptingCategoryChoiceLaw M F c :=
  normalizeWeights_nonneg _ (fun c => c.property.le)

theorem acceptingCategoryChoiceLaw_sum {q n : ℕ} (M : MarkovChain q) (F : Finset (Fin q))
    (hF : 0 < acceptanceProbability M F n) :
    ∑ c : AcceptingCategory M F n, acceptingCategoryChoiceLaw M F c = 1 := by
  apply normalizeWeights_sum
  rw [positiveFiber_mass_sum _ _ (acceptingPathWeight_nonneg M F), acceptingPathWeight_sum]
  exact hF

def acceptingCategoryChoiceSeed {q : ℕ} (M : MarkovChain q) (F : Finset (Fin q)) (n : ℕ) (ε : ℝ) : ℕ :=
  roundingSeed (Fintype.card (AcceptingCategory M F n)) (ε / 2)

def acceptingCategoryChoiceSize {q : ℕ} (M : MarkovChain q) (F : Finset (Fin q)) (n : ℕ) (ε : ℝ) : ℕ :=
  let c := Fintype.card (AcceptingCategory M F n)
  let r := acceptingCategoryChoiceSeed M F n ε
  r + c * (c * (2 * (r * (3 * r + 2) + 1) + 6) + 2)

/-- The category probabilities are hardwired conditional probabilities.
Only positive acceptance, with no quantitative lower bound, is needed. -/
theorem accepting_category_selector {q n : ℕ} (M : MarkovChain q) (F : Finset (Fin q))
    (hF : 0 < acceptanceProbability M F n) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : Bits (acceptingCategoryChoiceSeed M F n ε) → AcceptingCategory M F n,
      ∃ A : Circuit (AcceptingCategory M F n),
      ∃ hbits : A.randomBits = acceptingCategoryChoiceSeed M F n ε,
      (∀ seed c, A.eval (fun j => seed (Fin.cast hbits j)) c = decide (f seed = c)) ∧
      tv (finiteSeedLaw f) (acceptingCategoryChoiceLaw M F) ≤ ε / 2 ∧
      A.depth ≤ 6 ∧ A.size ≤ acceptingCategoryChoiceSize M F n ε := by
  classical
  obtain ⟨f, A, hbits, he, _, htv, hD, hsize⟩ := rounding_AC0_function
    (fun c d : AcceptingCategory M F n => decide (c = d)) (acceptingCategoryChoiceLaw M F)
    (acceptingCategoryChoiceLaw_nonneg M F) (acceptingCategoryChoiceLaw_sum M F hF)
    (ε / 2) (by positivity)
  exact ⟨f, A, hbits, fun seed c => congrFun (he seed) c, htv, hD, hsize⟩

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

theorem bridgeRoundingSize_envelope (q n t : ℕ) (δ : ℝ)
    (hq : q ≤ t) (hn : n + 1 ≤ t) (hm : bridgeRoundingSeed q n δ ≤ t)
    (hs : q ^ (n + 1) ≤ t) : bridgeRoundingSize q n δ ≤ roundedSizeEnvelope t := by
  unfold bridgeRoundingSize roundedSizeEnvelope
  gcongr

theorem boundaryRoundingCircuitSize_envelope (q M t : ℕ) (δ : ℝ) (ht : 0 < t)
    (hq : q ≤ t) (hM : M ≤ t) (hm : roundingSeed M δ ≤ t) :
    boundaryRoundingCircuitSize q M δ ≤ roundedSizeEnvelope t := by
  have hqq : q ≤ t * t := hq.trans (by nlinarith)
  unfold boundaryRoundingCircuitSize roundedSizeEnvelope
  dsimp only
  gcongr

theorem boundarySelectedBlockSize_envelope (r boundarySize k q n t : ℕ) (δ : ℝ)
    (hr : r ≤ t * t) (hB : boundarySize ≤ repeatedBoundarySizeEnvelope t)
    (hk : k ≤ t) (hq : q ≤ t) (hn : n + 1 ≤ t)
    (hm : bridgeRoundingSeed q n δ ≤ t) (hs : q ^ (n + 1) ≤ t) :
    boundarySelectedBlockSize r boundarySize k q n δ ≤ selectedBlockSizeEnvelope t := by
  have hleaf := bridgeRoundingSize_envelope q n t δ hq hn hm hs
  unfold boundarySelectedBlockSize endpointSelectedBlockSize selectedBlockSizeEnvelope
  gcongr

theorem bridgeBlockSeedBudget_envelope {k : ℕ} (q t : ℕ) (l : Fin (k + 1) → ℕ) (δ : ℝ)
    (hk : k + 1 ≤ t) (hm : ∀ i, bridgeRoundingSeed q (l i) δ ≤ t) :
    bridgeBlockSeedBudget q l δ ≤ t * t := by
  unfold bridgeBlockSeedBudget
  calc
    _ ≤ ∑ _i : Fin (k + 1), t := Finset.sum_le_sum (fun i _ => hm i)
    _ = (k + 1) * t := by simp
    _ ≤ t * t := Nat.mul_le_mul_right t hk

theorem parallelBridgeBlockSize_envelope {k : ℕ} (r boundarySize q t : ℕ)
    (l : Fin (k + 1) → ℕ) (δ : ℝ)
    (hr : r ≤ t * t) (hB : boundarySize ≤ repeatedBoundarySizeEnvelope t)
    (hk : k + 1 ≤ t) (hq : q ≤ t) (hn : ∀ i, l i + 1 ≤ t)
    (hm : ∀ i, bridgeRoundingSeed q (l i) δ ≤ t) (hs : ∀ i, q ^ (l i + 1) ≤ t) :
    parallelBridgeBlockSize r boundarySize q l δ ≤ parallelBlockSizeEnvelope t := by
  have hseeds := bridgeBlockSeedBudget_envelope q t l δ hk hm
  have hblocks : ∀ i, boundarySelectedBlockSize r boundarySize k q (l i) δ ≤ selectedBlockSizeEnvelope t :=
    fun i => boundarySelectedBlockSize_envelope r boundarySize k q (l i) t δ hr hB (by omega) hq
      (hn i) (hm i) (hs i)
  have hsum : (∑ i, ((l i + 1) * q) * boundarySelectedBlockSize r boundarySize k q (l i) δ) ≤
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
  unfold parallelBridgeBlockSize parallelBlockSizeEnvelope
  omega

theorem periodicBridgeCircuitSize_envelope (q M n L t : ℕ) (δ : ℝ) (ht : 0 < t)
    (hq : q ≤ t) (hM : M ≤ t) (hn : n + 1 ≤ t)
    (hm : roundingSeed M δ ≤ t)
    (hblen : ∀ i, cutoffBlockLengths n L i + 1 ≤ t)
    (hbseed : ∀ i, bridgeRoundingSeed q (cutoffBlockLengths n L i) δ ≤ t)
    (hbsupp : ∀ i, q ^ (cutoffBlockLengths n L i + 1) ≤ t) :
    periodicBridgeCircuitSize q M (boundaryRoundingCircuitSize q M δ) n L δ ≤ periodicSizeEnvelope t := by
  let k := cutoffBoundaryCount n L
  let m := roundingSeed M δ
  have hk : k + 1 ≤ t := by have h := (cutoff_block_count_bound n L).2; dsimp only [k]; omega
  have hk' : k ≤ t := by omega
  have hr : k * m ≤ t * t := Nat.mul_le_mul hk' hm
  have hleaf := boundaryRoundingCircuitSize_envelope q M t δ ht hq hM hm
  have hB : k * m + (k * q) * boundaryRoundingCircuitSize q M δ + k * q ≤
      repeatedBoundarySizeEnvelope t := by
    unfold repeatedBoundarySizeEnvelope
    gcongr
  have h := parallelBridgeBlockSize_envelope (k * m) _ q t (cutoffBlockLengths n L) δ
    hr hB hk hq hblen hbseed hbsupp
  unfold periodicBridgeCircuitSize periodicSizeEnvelope
  dsimp only
  exact Nat.add_le_add h (Nat.mul_le_mul hn hq)

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

theorem log_accuracy_ratio_le (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Real.log ((n + 1 : ℕ) / ε) ≤ n + Real.log 2 * logInv ε := by
  have he : Real.log ((n + 1 : ℕ) / ε) =
      Real.log (n + 1 : ℕ) + Real.log 2 * logInv ε := by
    rw [Real.log_div (by positivity) hε.ne']
    simp only [logInv, Real.log_div one_ne_zero hε.ne', Real.log_one, zero_sub]
    field_simp
    ring
  rw [he]
  linarith [log_succ_le n]

theorem localRoundingTolerance_bounds (N : ℕ) {ε : ℝ} (hε : 0 < ε) (hεle : ε ≤ 1) :
    0 < ε / (8 * (N + 1 : ℕ)) ∧ ε / (8 * (N + 1 : ℕ)) ≤ ε / 2 ∧ ε / 2 ≤ 1 := by
  have hN : (1 : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
  refine ⟨by positivity, ?_, by linarith⟩
  apply div_le_div_of_nonneg_left hε.le (by norm_num)
  nlinarith

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

/-- A long SCC segment uses a constant multiple of its length plus one
cutoff, uniformly in the SCC, endpoints and conditioning probabilities. -/
theorem sccPeriodicSeedBudget_linear {Q : Type} [Fintype Q] [DecidableEq Q]
    {W : Matrix Q Q ℝ} {s : Q} (model : SCCPeriodicModel W s) (x : SCCState W s)
    (q n L : ℕ) (hq : 0 < q) (hcard : Fintype.card (SCCState W s) ≤ q)
    (δ : ℝ) (hδ : 0 < δ) (hδle : δ ≤ 1) (hL : 0 < L) (hcost : logInv δ ≤ L) :
    (sccPeriodicSeedBudget model x n L δ : ℝ) ≤
      n * (3 * stateLog q + 4) + (stateLog q + 2) * L := by
  have hS : 0 < Fintype.card (SCCState W s) := Fintype.card_pos_iff.mpr ⟨x⟩
  have hM := sccPeriodicModel_support_card_pos model x
  have hMq := Fintype.card_subtype_le (fun y =>
    0 < (doobMatrix (sccMatrix W s) model.lam model.right ^ model.blockExponent) x y)
  have hb := stateLog_nonneg hq
  have hl := stateLog_mono hS hcard
  have hL' : (1 : ℝ) ≤ L := Nat.one_le_cast.mpr hL
  have hpay : stateLog (Fintype.card (SCCState W s)) + logInv δ + 1 ≤ (stateLog q + 2) * L := by
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hL')]
  have h := cutoffBridgeSeedBudget_linear (Fintype.card (SCCState W s)) _ n L hS hM hMq
    δ (stateLog q + 2) hδ hδle (by positivity) hpay
  apply h.trans
  change (n : ℝ) * (stateLog (Fintype.card (SCCState W s)) + 2 * (stateLog q + 2)) +
    (stateLog q + 2) * L ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- The same bound covers zero/one-edge, short rounded, long cyclic and
unused acyclic branches of the exact piecewise segment budget. -/
theorem componentSegmentSeedBudget_linear {Q : Type} [Fintype Q] [DecidableEq Q]
    {W : Matrix Q Q ℝ} (models : ∀ c : CyclicSCCIndex W, SCCPeriodicModel W c.val)
    (s : Q) (N n L : ℕ) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1)
    (hL : 0 < L) (hcost : logInv (ε / (8 * (N + 1 : ℕ))) ≤ L) :
    (componentSegmentSeedBudget models s N n L ε : ℝ) ≤
      n * (3 * stateLog (Fintype.card Q) + 4) + (stateLog (Fintype.card Q) + 2) * L := by
  classical
  have hq : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨s⟩
  have hb := stateLog_nonneg hq
  have hL' : (1 : ℝ) ≤ L := Nat.one_le_cast.mpr hL
  obtain ⟨hδ, hδhalf, hhalf⟩ := localRoundingTolerance_bounds N hε hεle
  have hshortcost : logInv (ε / 2) ≤ L := (logInv_antitone hδ hδhalf).trans hcost
  unfold componentSegmentSeedBudget
  split_ifs with hfixed hshort hc
  · simp only [Nat.cast_zero]
    positivity
  · have h := bridgeRoundingSeed_linear_bound (Fintype.card Q) n hq (ε / 2) (by positivity) hhalf
    apply h.trans
    change ((n + 1 : ℕ) : ℝ) * stateLog (Fintype.card Q) + logInv (ε / 2) + 1 ≤ _
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hL'),
      mul_nonneg hb (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · exact sccPeriodicSeedBudget_linear (models ⟨s, hc⟩) ⟨s, rfl⟩ (Fintype.card Q) n L hq
      (Fintype.card_subtype_le _) _ hδ (hδhalf.trans hhalf) hL hcost
  · simp only [Nat.cast_zero]
    positivity

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

-- Source module: Solutions.FSS23105365_EncodingFacts
section
set_option autoImplicit false
namespace FSS23105365



theorem pathEncode_injective (q n : ℕ) :
    Function.Injective (@pathEncode q n) := by
  intro γ η h
  funext i
  have hi := congrFun h (i, γ i)
  have hval : η i = γ i := of_decide_eq_true (by
    simpa only [pathEncode, decide_true] using hi.symm)
  exact hval.symm

end FSS23105365

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

-- Source module: Solutions.FSS23105365_ConditionedMarkovCircuit
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

local instance conditionedCircuitDecEq {q n : ℕ} : DecidableEq (GraphCategory (Fin q) n) := Classical.decEq _

def acceptingConditionalSeedBudget {q : ℕ} (M : MarkovChain q) (F : Finset (Fin q))
    (models : ∀ d : CyclicSCCIndex (M.transition : Matrix (Fin q) (Fin q) ℝ),
      SCCPeriodicModel M.transition d.val) (n L : ℕ) (ε : ℝ) : ℕ :=
  Finset.univ.sup (fun c : AcceptingCategory M F n =>
    categorySamplerSeedBudget models (acceptingCategoryRepresentative M F c) L
      (categorySegmentTolerance q ε))

def conditionedMarkovSeedBudget {q : ℕ} (M : MarkovChain q) (F : Finset (Fin q))
    (models : ∀ d : CyclicSCCIndex (M.transition : Matrix (Fin q) (Fin q) ℝ),
      SCCPeriodicModel M.transition d.val) (n L : ℕ) (ε : ℝ) : ℕ :=
  acceptingCategoryChoiceSeed M F n ε + acceptingConditionalSeedBudget M F models n L ε

def conditionedMarkovCircuitSize {q : ℕ} (M : MarkovChain q) (F : Finset (Fin q))
    (models : ∀ d : CyclicSCCIndex (M.transition : Matrix (Fin q) (Fin q) ℝ),
      SCCPeriodicModel M.transition d.val) (n L : ℕ) (ε : ℝ) : ℕ :=
  let c := Fintype.card (AcceptingCategory M F n)
  let o := (n + 1) * q
  conditionedMarkovSeedBudget M F models n L ε + c * acceptingCategoryChoiceSize M F n ε +
    o * (∑ d : AcceptingCategory M F n,
      categorySamplerCircuitSize models (acceptingCategoryRepresentative M F d) L
        (categorySegmentTolerance q ε)) +
    2 * (c + c * o) + o * (4 * c + 2)

/-- Complete acceptance-conditioned sampler and actual depth-thirteen
circuit, with explicit finite resource formulas. The conditional branch
seed is the maximum of the branch budgets. Uniform asymptotic bounds on
these formulas are a separate obligation. -/
theorem constructed_conditioned_markov_circuit {q n : ℕ} (hq : 0 < q)
    (M : MarkovChain q) (F : Finset (Fin q)) (hF : 0 < acceptanceProbability M F n)
    (models : ∀ d : CyclicSCCIndex (M.transition : Matrix (Fin q) (Fin q) ℝ),
      SCCPeriodicModel M.transition d.val)
    (L : ℕ) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1) (hL : 0 < L)
    (hmix : ∀ d, (models d).blockExponent ∣ L ∧
      (models d).coefficient * (models d).rate ^ (L / (models d).blockExponent) ≤
        categorySegmentTolerance q ε / (8 * (n + 1 : ℕ))) :
    ∃ f : Bits (conditionedMarkovSeedBudget M F models n L ε) → Path q n,
      ∃ S : Circuit (Fin (n + 1) × Fin q),
      ∃ hbits : S.randomBits = conditionedMarkovSeedBudget M F models n L ε,
      (∀ seed, S.eval (fun j => seed (Fin.cast hbits j)) = pathEncode (f seed)) ∧
      S.depth ≤ 13 ∧ S.size ≤ conditionedMarkovCircuitSize M F models n L ε ∧
      (∀ seed, (f seed) (Fin.last n) ∈ F ∧ 0 < pathLaw M (f seed)) ∧
      mass S pathEncode = finiteSeedLaw f ∧
      tv (finiteSeedLaw f) (conditionedPathLaw M F) ≤ ε := by
  classical
  let m := fun c : AcceptingCategory M F n =>
    categorySamplerSeedBudget models (acceptingCategoryRepresentative M F c) L
      (categorySegmentTolerance q ε)
  have hm : ∀ c, m c ≤ acceptingConditionalSeedBudget M F models n L ε :=
    fun c => Finset.le_sup (Finset.mem_univ c)
  choose g B hb he hD hsize hs ht using
    fun c => constructed_accepting_category_circuit hq M F c models L ε hε hεle hL hmix
  obtain ⟨a, A, ha, hea, hcat, hAD, hAsize⟩ := accepting_category_selector M F hF ε hε
  let f := sharedConditionalSeedSample m hm a g
  have hflaw : finiteSeedLaw f = mixtureLaw (finiteSeedLaw a) (fun c => finiteSeedLaw (g c)) :=
    sharedConditionalSeedSample_law m hm a g
  obtain ⟨S, hbits, hSe, hSD, hSs⟩ := conditional_sampler_circuit m hm pathEncode a g A ha hea
    B hb (fun c seed z => he c seed z.1 z.2) 11 hD
  have hsupp : ∀ c γ, 0 < finiteSeedLaw (g c) γ →
      0 < fiberWeight (graphCategory (fun x y => 0 < M.transition x y))
        (acceptingPathWeight M F) c.val γ := by
    intro c γ hp
    obtain ⟨seed, rfl⟩ := (finiteSeedLaw_pos_iff (g c) γ).mp hp
    exact hs c seed
  obtain ⟨_, _, hsupport, htv⟩ := approximate_conditioned_category_mixture M F hF
    (finiteSeedLaw a) (fun c => finiteSeedLaw (g c)) (finiteSeedLaw_nonneg a)
    (finiteSeedLaw_sum a) (fun c => finiteSeedLaw_nonneg (g c))
    (fun c => finiteSeedLaw_sum (g c)) hsupp (ε / 2) (ε / 2) hcat ht
  have hencode : ∀ seed, S.eval (fun j => seed (Fin.cast hbits j)) = pathEncode (f seed) :=
    fun seed => funext (hSe seed)
  refine ⟨f, S, hbits, hencode, ?_, ?_, ?_,
    sampler_circuit_mass f pathEncode (pathEncode_injective q n) S hbits hencode, ?_⟩
  · omega
  · apply hSs.trans
    simp only [Fintype.card_prod, Fintype.card_fin]
    unfold conditionedMarkovCircuitSize conditionedMarkovSeedBudget
    dsimp only
    gcongr
    exact hsize _
  · intro seed
    apply hsupport
    rw [← hflaw]
    exact (finiteSeedLaw_pos_iff f (f seed)).mpr ⟨seed, rfl⟩
  · exact (congrArg (fun p => tv p (conditionedPathLaw M F)) hflaw).trans_le (by linarith)

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_CategorySeedBounds
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

def categorySeedCoefficient (q : ℕ) : ℝ := 3 * stateLog q + 4 + 2 * q * (stateLog q + 2)

theorem categorySeedCoefficient_pos {q : ℕ} (hq : 0 < q) : 0 < categorySeedCoefficient q := by
  have h := stateLog_nonneg hq
  unfold categorySeedCoefficient
  positivity

theorem categorySamplerSeedBudget_linear {Q : Type} [Fintype Q] [DecidableEq Q]
    {W : Matrix Q Q ℝ} (models : ∀ c : CyclicSCCIndex W, SCCPeriodicModel W c.val)
    {n : ℕ} (γ : Fin (n + 1) → Q) (hγ : RespectsGraph (fun i j => 0 < W i j) γ)
    (L : ℕ) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1) (hL : 0 < L)
    (hcost : logInv (ε / (8 * (n + 1 : ℕ))) ≤ L) :
    (categorySamplerSeedBudget models γ L ε : ℝ) ≤
      categorySeedCoefficient (Fintype.card Q) * (n + (L : ℝ)) := by
  let R := fun i j => 0 < W i j
  let l := graphCategoryBlockLengths R γ
  have hq : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨γ 0⟩
  have hb := stateLog_nonneg hq
  have hcount : (graphInteriorCuts R γ).card + 1 ≤ 2 * Fintype.card Q :=
    (graphCategoryBlockLengths_count R γ hγ).trans (Nat.sub_le _ _)
  have hcount' : ((graphInteriorCuts R γ).card + 1 : ℕ) ≤ (2 * Fintype.card Q : ℝ) := by
    exact_mod_cast hcount
  have hlen : ∑ i, (l i : ℝ) = n := by
    have h : ∑ i, l i = n := (bridgeBlockLength_eq_sum l).symm.trans (graphCategoryBlockLengths_total R γ)
    exact_mod_cast h
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    componentSegmentSeedBudget_linear models (categorySegmentStart R γ i) n (l i) L ε hε hεle hL hcost)
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, hlen, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  unfold categorySamplerSeedBudget
  rw [Nat.cast_sum]
  apply hsum.trans
  have hc := mul_le_mul_of_nonneg_right hcount'
    (by positivity : 0 ≤ (stateLog (Fintype.card Q) + 2) * (L : ℝ))
  unfold categorySeedCoefficient
  nlinarith [mul_nonneg (by positivity : 0 ≤ 2 * (Fintype.card Q : ℝ) * (stateLog (Fintype.card Q) + 2))
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
    mul_nonneg (by positivity : 0 ≤ 3 * stateLog (Fintype.card Q) + 4) (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]

/-- Taking the maximum over all accepting categories preserves the
uniform bound; it does not multiply it by the number of categories. -/
theorem acceptingConditionalSeedBudget_linear {q n : ℕ} (M : MarkovChain q)
    (F : Finset (Fin q)) (hF : 0 < acceptanceProbability M F n)
    (models : ∀ d : CyclicSCCIndex (M.transition : Matrix (Fin q) (Fin q) ℝ),
      SCCPeriodicModel M.transition d.val)
    (L : ℕ) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1) (hL : 0 < L)
    (hcost : logInv (categorySegmentTolerance q ε / (8 * (n + 1 : ℕ))) ≤ L) :
    (acceptingConditionalSeedBudget M F models n L ε : ℝ) ≤
      categorySeedCoefficient q * (n + (L : ℝ)) := by
  classical
  letI : Nonempty (AcceptingCategory M F n) := acceptingCategory_nonempty M F hF
  let m := fun c : AcceptingCategory M F n =>
    categorySamplerSeedBudget models (acceptingCategoryRepresentative M F c) L
      (categorySegmentTolerance q ε)
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty m
  change ((Finset.univ.sup m : ℕ) : ℝ) ≤ _
  rw [hc]
  have hq : 0 < q := by
    have h : Fin q := (acceptingCategoryRepresentative M F c) 0
    exact Nat.zero_lt_of_lt h.isLt
  obtain ⟨hη, hηle, _⟩ := categorySegmentTolerance_bounds q hq ε hε hεle
  have hspec := acceptingCategoryRepresentative_spec M F c
  have hgraph := ((finitePathWeight_pos_iff M.initial M.transition M.initial_nonneg
    M.transition_nonneg (acceptingCategoryRepresentative M F c)).mp hspec.2.2).2
  simpa only [Fintype.card_fin] using categorySamplerSeedBudget_linear models
    (acceptingCategoryRepresentative M F c) hgraph L (categorySegmentTolerance q ε) hη hηle hL hcost

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

theorem acceptingCategoryChoiceSeed_linear {q n : ℕ} (hq : 0 < q)
    (M : MarkovChain q) (F : Finset (Fin q)) (hF : 0 < acceptanceProbability M F n)
    (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1 / 2) :
    (acceptingCategoryChoiceSeed M F n ε : ℝ) ≤ categoryChoiceCoefficient q * (n + logInv ε) := by
  classical
  have hcard : 0 < Fintype.card (AcceptingCategory M F n) :=
    Fintype.card_pos_iff.mpr (acceptingCategory_nonempty M F hF)
  exact roundingSeed_polynomial_card_bound _ q _ n (by positivity) hcard
    (acceptingCategory_card_polynomial M F) ε hε hεle

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

/-- Models and constants are fixed by the matrix, before n, accuracy,
accepting sets or endpoint choices. The cutoff also pays all local
logarithmic precision costs. -/
theorem scc_periodic_models_seed_cutoff {Q : Type} [Fintype Q] [DecidableEq Q]
    (W : Matrix Q Q ℝ) (hW : ∀ i j, 0 ≤ W i j) :
    ∃ (models : ∀ s : CyclicSCCIndex W, SCCPeriodicModel W s.val) (A D : ℝ),
      0 < A ∧ 0 < D ∧
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε ≤ 1 →
        ∃ L : ℕ, 0 < L ∧ (L : ℝ) ≤ A * Real.log ((n + 1 : ℕ) / ε) + D ∧
          logInv (ε / (8 * (n + 1 : ℕ))) ≤ L ∧
          ∀ s : CyclicSCCIndex W,
            (models s).blockExponent ∣ L ∧ 0 < L / (models s).blockExponent ∧
            (models s).coefficient * (models s).rate ^ (L / (models s).blockExponent) ≤
              ε / (8 * (n + 1 : ℕ)) := by
  classical
  let models : ∀ s : CyclicSCCIndex W, SCCPeriodicModel W s.val := fun s =>
    Classical.choice (cyclic_scc_periodic_model_exists W hW s.val s.property)
  obtain ⟨A, D, hA, hD, hcut⟩ := common_geometric_block_seed_cost
    (fun s => (models s).blockExponent) (fun s => (models s).exponent_pos)
    (fun s => (models s).coefficient) (fun s => (models s).rate)
    (fun s => (models s).coefficient_pos) (fun s => (models s).rate_pos)
    (fun s => (models s).rate_lt_one)
  exact ⟨models, A, D, hA, hD, hcut⟩

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ConditionedMarkovConstruction
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

theorem markovChain_stateCount_pos {q : ℕ} (M : MarkovChain q) : 0 < q := by
  by_contra h
  have hz : q = 0 := by omega
  subst q
  simpa using M.initial_sum

/-- The actual construction works for every positive acceptance event,
including n=0. Models and cutoff constants depend only on the chain.
The displayed seed and size formulas still need uniform asymptotic bounds
before this can be promoted to the complete E.6 theorem. -/
theorem conditioned_markov_circuit_with_cutoff {q : ℕ} (M : MarkovChain q) :
    ∃ (models : ∀ d : CyclicSCCIndex (M.transition : Matrix (Fin q) (Fin q) ℝ),
      SCCPeriodicModel M.transition d.val) (A D : ℝ),
      0 < A ∧ 0 < D ∧
      ∀ (n : ℕ) (F : Finset (Fin q)) (ε : ℝ),
        0 < acceptanceProbability M F n → 0 < ε → ε ≤ 1 / 2 →
        ∃ L : ℕ, 0 < L ∧ (L : ℝ) ≤ A * Real.log ((n + 1 : ℕ) / ε) + D ∧
          logInv (categorySegmentTolerance q ε / (8 * (n + 1 : ℕ))) ≤ L ∧
          ∃ S : Circuit (Fin (n + 1) × Fin q),
            S.randomBits = conditionedMarkovSeedBudget M F models n L ε ∧
            S.depth ≤ 13 ∧ S.size ≤ conditionedMarkovCircuitSize M F models n L ε ∧
            SupportPreserving S pathEncode (conditionedPathLaw M F) ∧
            tv (mass S pathEncode) (conditionedPathLaw M F) ≤ ε := by
  have hq := markovChain_stateCount_pos M
  have hq' : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr hq
  have h2q : (0 : ℝ) < 2 * q := by positivity
  have hlogq : 0 ≤ Real.log (2 * q : ℝ) := Real.log_nonneg (by linarith)
  obtain ⟨models, A, D, hA, hD, hcut⟩ :=
    scc_periodic_models_seed_cutoff (M.transition : Matrix (Fin q) (Fin q) ℝ) M.transition_nonneg
  refine ⟨models, A, D + A * Real.log (2 * q : ℝ), hA,
    add_pos_of_pos_of_nonneg hD (mul_nonneg hA.le hlogq), ?_⟩
  intro n F ε hF hε hεle
  have hε1 : ε ≤ 1 := by linarith
  obtain ⟨hη, hηle, _⟩ := categorySegmentTolerance_bounds q hq ε hε hε1
  obtain ⟨L, hL, hlen, hcost, hmix⟩ := hcut n (categorySegmentTolerance q ε) hη hηle
  have hratio : (n + 1 : ℕ) / categorySegmentTolerance q ε =
      ((n + 1 : ℕ) / ε) * (2 * q : ℝ) := by
    unfold categorySegmentTolerance
    field_simp
  have hlog : Real.log ((n + 1 : ℕ) / categorySegmentTolerance q ε) =
      Real.log ((n + 1 : ℕ) / ε) + Real.log (2 * q : ℝ) := by
    rw [hratio, Real.log_mul (by positivity) h2q.ne']
  have hlen' : (L : ℝ) ≤ A * Real.log ((n + 1 : ℕ) / ε) + (D + A * Real.log (2 * q : ℝ)) := by
    rw [hlog] at hlen
    linarith
  obtain ⟨f, S, hbits, he, hdepth, hsize, hs, hlaw, htv⟩ :=
    constructed_conditioned_markov_circuit hq M F hF models L ε hε hε1 hL
      (fun d => ⟨(hmix d).1, (hmix d).2.2⟩)
  refine ⟨L, hL, hlen', hcost, S, hbits, hdepth, hsize, ?_, ?_⟩
  · apply sampler_circuit_support f pathEncode (conditionedPathLaw M F) S hbits he
    intro seed
    have hs' := hs seed
    change 0 < if (f seed) (Fin.last n) ∈ F then
      pathLaw M (f seed) / acceptanceProbability M F n else 0
    rw [if_pos hs'.1]
    exact div_pos hs'.2 hF
  · rw [hlaw]
    exact htv

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ConditionedMarkovSeedBound
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365
open scoped BigOperators Matrix

def logarithmicCutoffCoefficient (A D : ℝ) : ℝ := 1 + A + A * Real.log 2 + D



theorem length_add_cutoff_bound (n L : ℕ) (A D ε : ℝ) (hA : 0 < A) (hD : 0 < D)
    (hε : 0 < ε) (hεle : ε ≤ 1 / 2)
    (hlen : (L : ℝ) ≤ A * Real.log ((n + 1 : ℕ) / ε) + D) :
    (n : ℝ) + L ≤ logarithmicCutoffCoefficient A D * (n + logInv ε) := by
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have ht := logInv_ge_one hε hεle
  have hlog := mul_le_mul_of_nonneg_left (log_accuracy_ratio_le n hε) hA.le
  unfold logarithmicCutoffCoefficient
  nlinarith [mul_nonneg hD.le (sub_nonneg.mpr ht),
    mul_nonneg (by positivity : 0 ≤ A * Real.log 2 + D) (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
    mul_nonneg (by positivity : 0 ≤ 1 + A) (le_trans (by norm_num : (0 : ℝ) ≤ 1) ht)]

def conditionedSeedCoefficient (q : ℕ) (A D : ℝ) : ℝ :=
  categoryChoiceCoefficient q + categorySeedCoefficient q * logarithmicCutoffCoefficient A D



/-- The complete selector-plus-maximum-branch budget has the source
linear-logarithmic bound. Constants depend only on state count and the
chain's cutoff constants, never on accepting probabilities. -/
theorem conditionedMarkovSeedBudget_linear {q n : ℕ} (hq : 0 < q)
    (M : MarkovChain q) (F : Finset (Fin q)) (hF : 0 < acceptanceProbability M F n)
    (models : ∀ d : CyclicSCCIndex (M.transition : Matrix (Fin q) (Fin q) ℝ),
      SCCPeriodicModel M.transition d.val)
    (L : ℕ) (A D ε : ℝ) (hA : 0 < A) (hD : 0 < D)
    (hε : 0 < ε) (hεle : ε ≤ 1 / 2) (hL : 0 < L)
    (hlen : (L : ℝ) ≤ A * Real.log ((n + 1 : ℕ) / ε) + D)
    (hcost : logInv (categorySegmentTolerance q ε / (8 * (n + 1 : ℕ))) ≤ L) :
    (conditionedMarkovSeedBudget M F models n L ε : ℝ) ≤
      conditionedSeedCoefficient q A D * (n + logInv ε) := by
  have hchoice := acceptingCategoryChoiceSeed_linear hq M F hF ε hε hεle
  have hbranch := acceptingConditionalSeedBudget_linear M F hF models L ε hε (by linarith) hL hcost
  have hlenadd := length_add_cutoff_bound n L A D ε hA hD hε hεle hlen
  have hcombined := mul_le_mul_of_nonneg_left hlenadd (categorySeedCoefficient_pos hq).le
  unfold conditionedMarkovSeedBudget
  rw [Nat.cast_add]
  unfold conditionedSeedCoefficient
  nlinarith

/-- Full actual construction with the complete E.6 random-bit bound.
Only the polynomial bound on the displayed size formula remains before
the E.6 circuit-complexity target is fully closed. -/
theorem conditioned_markov_linear_seed {q : ℕ} (M : MarkovChain q) :
    ∃ (models : ∀ d : CyclicSCCIndex (M.transition : Matrix (Fin q) (Fin q) ℝ),
      SCCPeriodicModel M.transition d.val) (A D : ℝ) (C : ℕ),
      0 < A ∧ 0 < D ∧ 0 < C ∧
      ∀ (n : ℕ) (F : Finset (Fin q)) (ε : ℝ),
        0 < acceptanceProbability M F n → 0 < ε → ε ≤ 1 / 2 →
        ∃ L : ℕ, 0 < L ∧ (L : ℝ) ≤ A * Real.log ((n + 1 : ℕ) / ε) + D ∧
          logInv (categorySegmentTolerance q ε / (8 * (n + 1 : ℕ))) ≤ L ∧
          ∃ S : Circuit (Fin (n + 1) × Fin q),
            S.randomBits = conditionedMarkovSeedBudget M F models n L ε ∧
            (S.randomBits : ℝ) ≤ (C : ℝ) * (n + logInv ε) ∧
            S.depth ≤ 13 ∧ S.size ≤ conditionedMarkovCircuitSize M F models n L ε ∧
            SupportPreserving S pathEncode (conditionedPathLaw M F) ∧
            tv (mass S pathEncode) (conditionedPathLaw M F) ≤ ε := by
  have hq := markovChain_stateCount_pos M
  obtain ⟨models, A, D, hA, hD, hconstruct⟩ := conditioned_markov_circuit_with_cutoff M
  let C : ℕ := ⌈conditionedSeedCoefficient q A D⌉₊ + 1
  have hC : conditionedSeedCoefficient q A D ≤ (C : ℝ) := by
    have h := Nat.le_ceil (conditionedSeedCoefficient q A D)
    dsimp only [C]
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  refine ⟨models, A, D, C, hA, hD, by dsimp [C]; omega, ?_⟩
  intro n F ε hF hε hεle
  obtain ⟨L, hL, hlen, hcost, S, hbits, hdepth, hsize, hs, htv⟩ := hconstruct n F ε hF hε hεle
  refine ⟨L, hL, hlen, hcost, S, hbits, ?_, hdepth, hsize, hs, htv⟩
  rw [hbits]
  apply (conditionedMarkovSeedBudget_linear hq M F hF models L A D ε hA hD hε hεle hL hlen hcost).trans
  exact mul_le_mul_of_nonneg_right hC (by
    have h := logInv_ge_one hε hεle
    positivity)

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

theorem samplingResourceScale_category {q n : ℕ} (M : MarkovChain q)
    (F : Finset (Fin q)) (hF : 0 < acceptanceProbability M F n) (L : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    Fintype.card (AcceptingCategory M F n) ≤ samplingResourceScale q n L ε ∧
      acceptingCategoryChoiceSeed M F n ε ≤ samplingResourceScale q n L ε := by
  classical
  have hcard := acceptingCategory_card_polynomial (n := n) M F
  have hpos : 0 < Fintype.card (AcceptingCategory M F n) :=
    Fintype.card_pos_iff.mpr (acceptingCategory_nonempty M F hF)
  have hs := samplingResourceScale_spec q n L ε
  exact ⟨hcard.trans hs.2.2.2.2.2.1,
    (roundingSeed_mono_card_precision hpos hcard (by positivity : 0 < ε / 2) le_rfl).trans hs.2.2.2.2.2.2⟩

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

/-- Every actual segment cost is bounded by the same polynomial
envelope, including short direct rounding and SCC state embedding. -/
theorem componentSegment_resource_envelope {q : ℕ} (hq : 0 < q)
    {W : Matrix (Fin q) (Fin q) ℝ}
    (models : ∀ c : CyclicSCCIndex W, SCCPeriodicModel W c.val)
    (s : Fin q) (N n L : ℕ) (hn : n ≤ N) (hL : 0 < L)
    (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1) :
    let t := samplingResourceScale q N L ε
    componentSegmentSeedBudget models s N n L (categorySegmentTolerance q ε) ≤ 2 * (t * t) ∧
      componentSegmentCircuitSize models s N n L (categorySegmentTolerance q ε) ≤ componentSizeEnvelope t := by
  classical
  dsimp only
  let t := samplingResourceScale q N L ε
  change componentSegmentSeedBudget models s N n L (categorySegmentTolerance q ε) ≤ 2 * (t * t) ∧
    componentSegmentCircuitSize models s N n L (categorySegmentTolerance q ε) ≤ componentSizeEnvelope t
  have hscale := samplingResourceScale_spec q N L ε
  have ht : 0 < t := hscale.1
  have hnt : n + 1 ≤ t := by dsimp only [t]; omega
  have hqt : q ≤ t := by dsimp only [t]; omega
  obtain ⟨hδ, hδhalf, _⟩ := localSamplingTolerance_bounds q N hq hε hεle
  unfold componentSegmentSeedBudget componentSegmentCircuitSize
  simp only [Fintype.card_fin]
  split_ifs with hfixed hshort hc
  · refine ⟨Nat.zero_le _, ?_⟩
    have h := Nat.mul_le_mul_left 2 (Nat.mul_le_mul hnt hqt)
    unfold componentSizeEnvelope
    omega
  · obtain ⟨hcard, hseed⟩ := samplingResourceScale_block q N L q n hq le_rfl (by omega)
      ε (categorySegmentTolerance q ε / 2) hδ hδhalf
    refine ⟨hseed.trans (by change t ≤ 2 * (t * t); nlinarith), ?_⟩
    have h := bridgeRoundingSize_envelope q n t _ hqt hnt hseed hcard
    unfold componentSizeEnvelope
    omega
  · let model := models ⟨s, hc⟩
    let x : SCCState W s := ⟨s, rfl⟩
    let p := Fintype.card (SCCState W s)
    let c := Fintype.card (PositiveSupportClass
      (doobMatrix (sccMatrix W s) model.lam model.right ^ model.blockExponent) x)
    let δ := localSamplingTolerance q N ε
    have hp : 0 < p := Fintype.card_pos_iff.mpr ⟨x⟩
    have hpq : p ≤ q := by
      simpa only [Fintype.card_fin] using (Fintype.card_subtype_le
        (fun z => graphComponent (fun i j => 0 < W i j) z = graphComponent (fun i j => 0 < W i j) s))
    have hcpos : 0 < c := sccPeriodicModel_support_card_pos model x
    have hcp : c ≤ p := Fintype.card_subtype_le _
    have hpt : p ≤ t := hpq.trans hqt
    have hct : c ≤ t := hcp.trans hpt
    have hboundary : roundingSeed c δ ≤ t := samplingResourceScale_boundary q N L c hcpos
      (hcp.trans hpq) ε hδ
    have hblocks : ∀ i, p ^ (cutoffBlockLengths n L i + 1) ≤ t ∧
        bridgeRoundingSeed p (cutoffBlockLengths n L i) δ ≤ t := by
      intro i
      exact samplingResourceScale_block q N L p _ hp hpq (Nat.le_of_lt (cutoffBlockLengths_upper n L hL i))
        ε δ hδ le_rfl
    have hlength : ∀ i, cutoffBlockLengths n L i + 1 ≤ t := by
      intro i
      have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (cutoffBlockLengths n L j))
        (Finset.mem_univ i)
      rw [← bridgeBlockLength_eq_sum, cutoffBlockLengths_total] at h
      omega
    have hk : cutoffBoundaryCount n L + 1 ≤ t := by
      have h := (cutoff_block_count_bound n L).2
      omega
    have hseeds := bridgeBlockSeedBudget_envelope p t (cutoffBlockLengths n L) δ hk (fun i => (hblocks i).2)
    have hprefix : cutoffBoundaryCount n L * roundingSeed c δ ≤ t * t :=
      Nat.mul_le_mul (by omega) hboundary
    have hsize := periodicBridgeCircuitSize_envelope p c n L t δ ht hpt hct hnt hboundary
      hlength (fun i => (hblocks i).2) (fun i => (hblocks i).1)
    change sccPeriodicSeedBudget model x n L δ ≤ 2 * (t * t) ∧
      sccPeriodicCircuitSize model x n L δ ≤ componentSizeEnvelope t
    constructor
    · change cutoffBoundaryCount n L * roundingSeed c δ + bridgeBlockSeedBudget p (cutoffBlockLengths n L) δ ≤ _
      omega
    · unfold sccPeriodicCircuitSize
      dsimp only
      simp only [Fintype.card_fin]
      change periodicBridgeCircuitSize p c (boundaryRoundingCircuitSize p c δ) n L δ +
        (n + 1) * p + 2 * ((n + 1) * q) ≤ _
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

theorem categorySampler_resource_envelope {q n : ℕ} (hq : 0 < q)
    {W : Matrix (Fin q) (Fin q) ℝ}
    (models : ∀ c : CyclicSCCIndex W, SCCPeriodicModel W c.val)
    (γ : Path q n) (hγ : RespectsGraph (fun i j => 0 < W i j) γ)
    (L : ℕ) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1) :
    let t := samplingResourceScale q n L ε
    categorySamplerSeedBudget models γ L (categorySegmentTolerance q ε) ≤ t * (2 * (t * t)) ∧
      categorySamplerCircuitSize models γ L (categorySegmentTolerance q ε) ≤ categorySizeEnvelope t := by
  dsimp only
  let t := samplingResourceScale q n L ε
  change categorySamplerSeedBudget models γ L (categorySegmentTolerance q ε) ≤ t * (2 * (t * t)) ∧
    categorySamplerCircuitSize models γ L (categorySegmentTolerance q ε) ≤ categorySizeEnvelope t
  let R := fun i j => 0 < W i j
  let l := graphCategoryBlockLengths R γ
  have hscale := samplingResourceScale_spec q n L ε
  have hqT : q ≤ t := by dsimp only [t]; omega
  have hnT : n + 1 ≤ t := hscale.2.1
  have hk : (graphInteriorCuts R γ).card + 1 ≤ t := by
    have h := graphCategoryBlockLengths_count R γ hγ
    simp only [Fintype.card_fin] at h
    dsimp only [t]
    omega
  have hblocks := fun i => componentSegment_resource_envelope hq models (categorySegmentStart R γ i)
    n (l i) L (category_segment_length_le R γ i) hL ε hε hεle
  have hseed : categorySamplerSeedBudget models γ L (categorySegmentTolerance q ε) ≤ t * (2 * (t * t)) := by
    unfold categorySamplerSeedBudget
    calc
      _ ≤ ∑ _i : Fin ((graphInteriorCuts R γ).card + 1), 2 * (t * t) :=
        Finset.sum_le_sum (fun i _ => (hblocks i).1)
      _ = ((graphInteriorCuts R γ).card + 1) * (2 * (t * t)) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hk
  have hlength : ∀ i, l i + 1 ≤ t := fun i => (Nat.add_le_add_right (category_segment_length_le R γ i) 1).trans hnT
  have hweighted : (∑ i, ((l i + 1) * q) * componentSegmentCircuitSize models (categorySegmentStart R γ i)
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
  unfold categorySamplerCircuitSize categorySizeEnvelope
  dsimp only
  simp only [Fintype.card_fin]
  change categorySamplerSeedBudget models γ L (categorySegmentTolerance q ε) +
    (∑ i, ((l i + 1) * q) * componentSegmentCircuitSize models (categorySegmentStart R γ i)
      n (l i) L (categorySegmentTolerance q ε)) + (∑ i, (l i + 1) * q) + (n + 1) * q ≤ _
  omega

theorem conditionedMarkovCircuitSize_envelope {q n : ℕ} (hq : 0 < q)
    (M : MarkovChain q) (F : Finset (Fin q)) (hF : 0 < acceptanceProbability M F n)
    (models : ∀ d : CyclicSCCIndex (M.transition : Matrix (Fin q) (Fin q) ℝ),
      SCCPeriodicModel M.transition d.val)
    (L : ℕ) (hL : 0 < L) (ε : ℝ) (hε : 0 < ε) (hεle : ε ≤ 1) :
    conditionedMarkovCircuitSize M F models n L ε ≤ conditionedSizeEnvelope (samplingResourceScale q n L ε) := by
  classical
  let t := samplingResourceScale q n L ε
  let c := Fintype.card (AcceptingCategory M F n)
  have hscale := samplingResourceScale_spec q n L ε
  have ht : 0 < t := hscale.1
  have hqT : q ≤ t := by dsimp only [t]; omega
  have ho : (n + 1) * q ≤ t * t := Nat.mul_le_mul hscale.2.1 hqT
  obtain ⟨hc, ha⟩ := samplingResourceScale_category M F hF L ε hε
  have hcat : ∀ d : AcceptingCategory M F n,
      categorySamplerSeedBudget models (acceptingCategoryRepresentative M F d) L (categorySegmentTolerance q ε) ≤ t * (2 * (t * t)) ∧
      categorySamplerCircuitSize models (acceptingCategoryRepresentative M F d) L (categorySegmentTolerance q ε) ≤ categorySizeEnvelope t := by
    intro d
    have hs := acceptingCategoryRepresentative_spec M F d
    have hgraph := ((finitePathWeight_pos_iff M.initial M.transition M.initial_nonneg M.transition_nonneg
      (acceptingCategoryRepresentative M F d)).mp hs.2.2).2
    exact categorySampler_resource_envelope hq models (acceptingCategoryRepresentative M F d) hgraph L hL ε hε hεle
  have hmax : acceptingConditionalSeedBudget M F models n L ε ≤ t * (2 * (t * t)) :=
    Finset.sup_le (fun d _ => (hcat d).1)
  have hr : conditionedMarkovSeedBudget M F models n L ε ≤ t + t * (2 * (t * t)) :=
    Nat.add_le_add ha hmax
  have hAsize : acceptingCategoryChoiceSize M F n ε ≤ roundedSizeEnvelope t := by
    change boundaryRoundingCircuitSize c c (ε / 2) ≤ roundedSizeEnvelope t
    exact boundaryRoundingCircuitSize_envelope c c t _ ht hc hc ha
  have hsum : (∑ d : AcceptingCategory M F n,
      categorySamplerCircuitSize models (acceptingCategoryRepresentative M F d) L (categorySegmentTolerance q ε)) ≤
      t * categorySizeEnvelope t := by
    calc
      _ ≤ ∑ _d : AcceptingCategory M F n, categorySizeEnvelope t := Finset.sum_le_sum (fun d _ => (hcat d).2)
      _ = c * categorySizeEnvelope t := by simp [c]
      _ ≤ _ := Nat.mul_le_mul_right _ hc
  unfold conditionedMarkovCircuitSize conditionedSizeEnvelope
  dsimp only
  gcongr

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

/-- Uniform polynomial gate-and-wire size for the complete actual
acceptance-conditioned sampler. The constants precede all acceptance
events, lengths, cutoffs and accuracies. -/
theorem conditionedMarkovCircuitSize_polynomial {q : ℕ} (hq : 0 < q) (M : MarkovChain q)
    (models : ∀ d : CyclicSCCIndex (M.transition : Matrix (Fin q) (Fin q) ℝ),
      SCCPeriodicModel M.transition d.val) (A D : ℝ) (hA : 0 < A) (hD : 0 < D) :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ (n L : ℕ) (F : Finset (Fin q)) (ε : ℝ),
        0 < acceptanceProbability M F n → 0 < L → 0 < ε → ε ≤ 1 / 2 →
        (L : ℝ) ≤ A * Real.log ((n + 1 : ℕ) / ε) + D →
        logInv (localSamplingTolerance q n ε) ≤ L →
        (conditionedMarkovCircuitSize M F models n L ε : ℝ) ≤ C * (((n + 1 : ℕ) : ℝ) / ε) ^ k := by
  obtain ⟨B, k, hB, hscale⟩ := samplingResourceScale_polynomial q hq A D hA hD
  refine ⟨131 * B ^ 18, k * 18, by positivity, ?_⟩
  intro n L F ε hF hL hε hεle hlen hcost
  let t := samplingResourceScale q n L ε
  have henv := conditionedMarkovCircuitSize_envelope hq M F hF models L hL ε hε (by linarith)
  have henv' : (conditionedMarkovCircuitSize M F models n L ε : ℝ) ≤ (conditionedSizeEnvelope t : ℝ) := by
    exact_mod_cast henv
  have ht := (samplingResourceScale_spec q n L ε).1
  have htbound := hscale n L ε hε hεle hlen hcost
  calc
    _ ≤ 131 * (t : ℝ) ^ 18 := henv'.trans (conditionedSizeEnvelope_polynomial t ht)
    _ ≤ 131 * (B * (((n + 1 : ℕ) : ℝ) / ε) ^ k) ^ 18 := by gcongr
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end FSS23105365

end
end

-- Source module: Solutions.FSS23105365_ConditionedMarkovSampling
section
set_option autoImplicit false
noncomputable section
namespace FSS23105365

/-- Appendix E.6 in full, with the original circuit, path encoding,
support predicate and TV distance. The constants are chosen before F,
n and epsilon; positive acceptance is the only conditioning assumption. -/
theorem conditioned_markov (q : ℕ) (hq : 0 < q) (M : MarkovChain q) :
    ∃ D C k : ℕ, ∀ F : Finset (Fin q), ∀ n : ℕ,
      0 < acceptanceProbability M F n →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ S : Circuit (Fin (n + 1) × Fin q),
        S.depth ≤ D ∧
        (S.size : ℝ) ≤ (C : ℝ) * (((n + 1 : ℕ) : ℝ) / ε) ^ k ∧
        (S.randomBits : ℝ) ≤ (C : ℝ) * ((n : ℝ) + logInv ε) ∧
        SupportPreserving S pathEncode (conditionedPathLaw M F) ∧
        tv (mass S pathEncode) (conditionedPathLaw M F) ≤ ε := by
  obtain ⟨models, A, B, R, hA, hB, _, hconstruct⟩ := conditioned_markov_linear_seed M
  obtain ⟨V, k, hV, hsize⟩ := conditionedMarkovCircuitSize_polynomial hq M models A B hA hB
  let C : ℕ := ⌈V⌉₊ + R + 1
  have hVC : V ≤ (C : ℝ) := by
    have h := Nat.le_ceil V
    dsimp only [C]
    simp only [Nat.cast_add, Nat.cast_one]
    linarith [(Nat.cast_nonneg R : (0 : ℝ) ≤ R)]
  have hRC : (R : ℝ) ≤ C := by
    exact_mod_cast (show R ≤ C by dsimp only [C]; omega)
  refine ⟨13, C, k, ?_⟩
  intro F n hF ε hε hεle
  obtain ⟨L, hL, hlen, hcost, S, _, hbits, hdepth, hSsize, hs, htv⟩ :=
    hconstruct n F ε hF hε hεle
  refine ⟨S, hdepth, ?_, ?_, hs, htv⟩
  · have hSsize' : (S.size : ℝ) ≤ conditionedMarkovCircuitSize M F models n L ε := by
      exact_mod_cast hSsize
    exact (hSsize'.trans (hsize n L F ε hF hL hε hεle hlen hcost)).trans
      (mul_le_mul_of_nonneg_right hVC (by positivity))
  · apply hbits.trans
    exact mul_le_mul_of_nonneg_right hRC (by
      have h := logInv_ge_one hε hεle
      positivity)

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





















def recordTrajectory {Q : Type} {n : ℕ} (p : LabeledTrajectory Q n) : Fin (n + 1) → Q × Bool :=
  Fin.cons (p.1 0, false) (fun i => (p.1 i.succ, p.2 i))



theorem recordTrajectory_zero {Q : Type} {n : ℕ} (p : LabeledTrajectory Q n) :
    recordTrajectory p 0 = (p.1 0, false) := rfl























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

theorem localDivisor_one_val {M : Type} [Monoid M] (c : M) :
    (1 : LocalDivisor c).val = c := rfl















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
theorem solution (q : ℕ) (hq : 0 < q) (M : MarkovChain q) :
    ∃ D C k : ℕ, ∀ F : Finset (Fin q), ∀ n : ℕ,
      0 < acceptanceProbability M F n →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ S : Circuit (Fin (n + 1) × Fin q),
        S.depth ≤ D ∧
        (S.size : ℝ) ≤ (C : ℝ) * (((n + 1 : ℕ) : ℝ) / ε) ^ k ∧
        (S.randomBits : ℝ) ≤ (C : ℝ) * ((n : ℝ) + logInv ε) ∧
        SupportPreserving S pathEncode (conditionedPathLaw M F) ∧
        tv (mass S pathEncode) (conditionedPathLaw M F) ≤ ε := FSS23105365.conditioned_markov q hq M
