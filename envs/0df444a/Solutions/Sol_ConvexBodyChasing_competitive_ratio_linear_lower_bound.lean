-- Prove2me | solution 1 for ConvexBodyChasing.competitive_ratio_linear_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @nhc
-- created : 2026-11-13T13:44:38.348506+00:00
-- url     : https://prove2.me/submissions/a087c0f9-57c7-40b8-9096-70d718a0c287

import Definitions.Def_CBCCompactChasingModel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Chain
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Lipschitz

set_option autoImplicit false

namespace CBCProve2MeProofs.FiniteLp
open ConvexBodyChasing

/- Component source: ConvexBodyChasing.Pairing -/
section BundledModule003
/-! # Finite signed measures and coordinate tests

This module is independent of the recursive graph construction. It records the
finite dimensional dual calculation behind the transportation estimate.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators

namespace ConvexBodyChasing
namespace SignedMass

variable {V I : Type*} [Fintype V] [Fintype I]

def pairing (μ f : V → ℝ) : ℝ := ∑ v, μ v * f v

theorem pairing_const (μ : V → ℝ) (hμ : ∑ v, μ v = 0) (b : ℝ) :
    pairing μ (fun _ => b) = 0 := by
  simp [pairing, ← Finset.sum_mul, hμ]

theorem pairing_add (μ f g : V → ℝ) :
    pairing μ (f + g) = pairing μ f + pairing μ g := by
  simp [pairing, mul_add, Finset.sum_add_distrib]

theorem pairing_coordinates (μ : V → ℝ) (Ψ : V → I → ℝ) (a : I → ℝ) :
    pairing μ (fun v => ∑ i, a i * Ψ v i) = ∑ i, a i * pairing μ (fun v => Ψ v i) := by
  simp only [pairing, Finset.mul_sum, ← mul_assoc]
  simpa only [mul_comm (μ _) (a _)] using!
    (Finset.sum_comm (f := fun v i => μ v * a i * Ψ v i))

theorem pairing_congr_support (μ f g : V → ℝ)
    (h : ∀ v, μ v ≠ 0 → f v = g v) : pairing μ f = pairing μ g := by
  apply Finset.sum_congr rfl
  exact fun v _ => if hv : μ v = 0 then by simp [hv] else by rw [h v hv]

/-- A bounded coordinate representation controls the pairing with any zero-mass measure. -/
theorem abs_pairing_le_of_representation (μ f : V → ℝ) (hμ : ∑ v, μ v = 0)
    (Ψ : V → I → ℝ) (a : I → ℝ) (b C : ℝ)
    (ha : ∀ i, |a i| ≤ C)
    (hrep : ∀ v, μ v ≠ 0 → f v = b + ∑ i, a i * Ψ v i) :
    |pairing μ f| ≤ C * ∑ i, |pairing μ (fun v => Ψ v i)| := by
  rw [pairing_congr_support μ f (fun v => b + ∑ i, a i * Ψ v i) hrep]
  change |pairing μ ((fun _ => b) + (fun v => ∑ i, a i * Ψ v i))| ≤ _
  rw [pairing_add, pairing_const μ hμ, zero_add, pairing_coordinates]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (by
    simpa only [abs_mul, Finset.mul_sum] using!
      Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
        mul_le_mul_of_nonneg_right (ha i) (abs_nonneg (pairing μ (fun v => Ψ v i)))))

end SignedMass
end ConvexBodyChasing

end
end BundledModule003

/- Component source: ConvexBodyChasing.Barycenter -/
section BundledModule004
/-! # Probability weights on a finite request

Weights are indexed by the original vertices, including when their images
coincide. Every point of a finite request's convex hull has such a representation.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
namespace ConvexBodyChasing

structure RequestWeights {V : Type*} [Fintype V] (S : Finset V) where
  weight : V → ℝ
  nonneg : ∀ v, 0 ≤ weight v
  total : ∑ v, weight v = 1
  supported : ∀ v, v ∉ S → weight v = 0

namespace RequestWeights
variable {V E : Type*} [Fintype V]
variable [AddCommGroup E] [Module ℝ E]
variable {S : Finset V}

def mean (P : RequestWeights S) (f : V → ℝ) : ℝ := SignedMass.pairing P.weight f

def barycenter (P : RequestWeights S) (φ : V → E) : E := ∑ v, P.weight v • φ v

def point [DecidableEq V] (x : V) (hx : x ∈ S) : RequestWeights S where
  weight v := if v = x then 1 else 0
  nonneg v := by split_ifs <;> norm_num
  total := by simp
  supported v hv := by
    simp only [ite_eq_right_iff, one_ne_zero, imp_false]
    exact fun h => hv (h.symm ▸ hx)

@[simp] theorem mean_point [DecidableEq V] (x : V) (hx : x ∈ S) (f : V → ℝ) :
    (point x hx).mean f = f x := by
  simp [mean, point, SignedMass.pairing]

@[simp] theorem barycenter_point [DecidableEq V] (x : V) (hx : x ∈ S) (φ : V → E) :
    (point x hx).barycenter φ = φ x := by
  simp [barycenter, point]

def mix (P Q : RequestWeights S) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : RequestWeights S where
  weight v := a * P.weight v + b * Q.weight v
  nonneg v := add_nonneg (mul_nonneg ha (P.nonneg v)) (mul_nonneg hb (Q.nonneg v))
  total := by simp [Finset.sum_add_distrib, ← Finset.mul_sum, P.total, Q.total, hab]
  supported v hv := by simp [P.supported v hv, Q.supported v hv]

theorem barycenter_mix (P Q : RequestWeights S) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (φ : V → E) :
    (mix P Q a b ha hb hab).barycenter φ = a • P.barycenter φ + b • Q.barycenter φ := by
  simp [barycenter, mix, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

/-- No injectivity of the vertex embedding is required. -/
theorem exists_of_mem_convexHull [DecidableEq V] (φ : V → E) {x : E}
    (hx : x ∈ convexHull ℝ (φ '' (↑S : Set V))) :
    ∃ P : RequestWeights S, P.barycenter φ = x := by
  apply convexHull_min (t := {y | ∃ P : RequestWeights S, P.barycenter φ = y}) ?_ ?_ hx
  · rintro _ ⟨v, hv, rfl⟩
    exact ⟨point v hv, barycenter_point v hv φ⟩
  · rintro _ ⟨P, rfl⟩ _ ⟨Q, rfl⟩ a b ha hb hab
    exact ⟨mix P Q a b ha hb hab, barycenter_mix P Q a b ha hb hab φ⟩

theorem mean_congr (P : RequestWeights S) {f g : V → ℝ}
    (h : ∀ v ∈ S, f v = g v) : P.mean f = P.mean g := by
  apply SignedMass.pairing_congr_support
  exact fun v hv => h v (not_not.mp (fun hnot => hv (P.supported v hnot)))

@[simp] theorem mean_zero (P : RequestWeights S) : P.mean (fun _ => 0) = 0 := by
  simp [mean, SignedMass.pairing]

theorem mean_add (P : RequestWeights S) (f g : V → ℝ) :
    P.mean (fun v => f v + g v) = P.mean f + P.mean g := by
  exact SignedMass.pairing_add P.weight f g

theorem mean_div (P : RequestWeights S) (f : V → ℝ) (c : ℝ) :
    P.mean (fun v => f v / c) = P.mean f / c := by
  simp [mean, SignedMass.pairing, Finset.sum_div, ← mul_div_assoc]

theorem difference_total {T : Finset V} (P : RequestWeights S) (Q : RequestWeights T) :
    ∑ v, (P.weight v - Q.weight v) = 0 := by
  simp [Finset.sum_sub_distrib, P.total, Q.total]

theorem difference_supported [DecidableEq V] {T : Finset V}
    (P : RequestWeights S) (Q : RequestWeights T) (v : V)
    (hv : P.weight v - Q.weight v ≠ 0) : v ∈ S ∪ T := by
  by_contra h
  exact hv (by rw [P.supported v (fun hv => h (Finset.mem_union_left _ hv)),
    Q.supported v (fun hv => h (Finset.mem_union_right _ hv)), sub_self])

theorem pairing_difference {T : Finset V} (P : RequestWeights S) (Q : RequestWeights T)
    (f : V → ℝ) : SignedMass.pairing (fun v => P.weight v - Q.weight v) f =
      P.mean f - Q.mean f := by
  simp [SignedMass.pairing, mean, sub_mul, Finset.sum_sub_distrib]

theorem barycenter_difference {T : Finset V} (P : RequestWeights S) (Q : RequestWeights T)
    (φ : V → E) : (∑ v, (P.weight v - Q.weight v) • φ v) =
      P.barycenter φ - Q.barycenter φ := by
  simp [barycenter, sub_smul, Finset.sum_sub_distrib]

end RequestWeights
end ConvexBodyChasing

end
end BundledModule004

/- Component source: ConvexBodyChasing.FiniteGame -/
section BundledModule005
/-! # Finite oblivious distributions of discrete requests

`request` is an online decision and `coin` is a fresh fair coin. The entire tree
is fixed before the algorithm acts. Its evaluation is the optimal expected
movement with a specified terminal cost. This separates finite probability
bookkeeping from the graph and convex geometry.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace ConvexBodyChasing

inductive FiniteGame (V : Type*) where
  | stop
  | request (S : Finset V) (nonempty : S.Nonempty) (next : FiniteGame V)
  | coin (left right : FiniteGame V)

namespace FiniteGame

variable {V : Type*}

variable {W : Type*}

/-- Push every request through a map of the underlying spaces. -/
def map (f : V → W) [DecidableEq W] : FiniteGame V → FiniteGame W
  | .stop => .stop
  | .request S hS next => .request (S.image f) (hS.image f) (map f next)
  | .coin left right => .coin (map f left) (map f right)

/-- Keep a waiting vertex feasible throughout a recursive call. -/
def withWaiting [DecidableEq V] (z : V) : FiniteGame V → FiniteGame V
  | .stop => .stop
  | .request S _ next => .request (insert z S) (Finset.insert_nonempty _ _)
    (withWaiting z next)
  | .coin left right => .coin (withWaiting z left) (withWaiting z right)







variable [MetricSpace V]

/-- Bellman evaluation; a request is served before any later coin is revealed. -/
def eval (terminal : V → ℝ) : FiniteGame V → V → ℝ
  | .stop, x => terminal x
  | .request S hS next, x => S.inf' hS (fun y => dist x y + eval terminal next y)
  | .coin left right, x => (eval terminal left x + eval terminal right x) / 2

def append : FiniteGame V → FiniteGame V → FiniteGame V
  | .stop, H => H
  | .request S hS G, H => .request S hS (append G H)
  | .coin G₁ G₂, H => .coin (append G₁ H) (append G₂ H)



/-- A strategy may depend on all coin outcomes that have already occurred.
Giving this information can only strengthen an online algorithm. -/
def Strategy : FiniteGame V → Type _
  | .stop => PUnit
  | .request S _ next => {y // y ∈ S} × Strategy next
  | .coin left right => Strategy left × Strategy right

def strategyCost (terminal : V → ℝ) :
    (G : FiniteGame V) → Strategy G → V → ℝ
  | .stop, _, x => terminal x
  | .request _ _ next, π, x => dist x π.1.val + strategyCost terminal next π.2 π.1.val
  | .coin left right, π, x =>
    (strategyCost terminal left π.1 x + strategyCost terminal right π.2 x) / 2

theorem eval_le_strategyCost (G : FiniteGame V) (f : V → ℝ) :
    ∀ (π : Strategy G) (x : V), eval f G x ≤ strategyCost f G π x := by
  induction G with
  | stop => exact fun _ _ => le_rfl
  | request S hS G ih =>
    exact fun π x => (Finset.inf'_le _ π.1.property).trans (add_le_add le_rfl (ih π.2 _))
  | coin G₁ G₂ ih₁ ih₂ =>
    exact fun π x => div_le_div_of_nonneg_right (add_le_add (ih₁ π.1 x) (ih₂ π.2 x))
      (by norm_num)

theorem exists_optimal_strategy (G : FiniteGame V) (f : V → ℝ) :
    ∀ x, ∃ π : Strategy G, strategyCost f G π x = eval f G x := by
  induction G with
  | stop => exact fun _ => ⟨PUnit.unit, rfl⟩
  | request S hS G ih =>
    intro x
    obtain ⟨y, hy, hmin⟩ := Finset.exists_mem_eq_inf' hS (fun y => dist x y + eval f G y)
    obtain ⟨π, hπ⟩ := ih y
    exact ⟨(⟨y, hy⟩, π), by simpa only [strategyCost, eval, hπ] using! hmin.symm⟩
  | coin G₁ G₂ ih₁ ih₂ =>
    intro x
    obtain ⟨π₁, hπ₁⟩ := ih₁ x
    obtain ⟨π₂, hπ₂⟩ := ih₂ x
    exact ⟨(π₁, π₂), by simp only [strategyCost, eval, hπ₁, hπ₂]⟩







/-- Triangle inequality for the minimum-cost response to a request. -/
theorem request_eval_le (S : Finset V) (hS : S.Nonempty) (f : V → ℝ) (x y : V) :
    S.inf' hS (fun z => dist x z + f z) ≤
      dist x y + S.inf' hS (fun z => dist y z + f z) := by
  obtain ⟨z, hz, heq⟩ := Finset.exists_mem_eq_inf' hS (fun z => dist y z + f z)
  exact (Finset.inf'_le _ hz).trans (by linarith [dist_triangle x y z])

theorem eval_lipschitz (G : FiniteGame V) {f : V → ℝ} (hf : LipschitzWith 1 f) :
    LipschitzWith 1 (eval f G) := by
  induction G with
  | stop => exact hf
  | request S hS G ih =>
    exact LipschitzWith.of_le_add (fun x y => by
      simpa only [eval, add_comm] using! request_eval_le S hS (eval f G) x y)
  | coin G₁ G₂ ih₁ ih₂ =>
    apply LipschitzWith.of_le_add
    exact fun x y => by
      have h₁ := ih₁.le_add_mul x y
      have h₂ := ih₂.le_add_mul x y
      simpa only [eval] using!
        (show (eval f G₁ x + eval f G₂ x) / 2 ≤
          (eval f G₁ y + eval f G₂ y) / 2 + dist x y from by
          norm_num at h₁ h₂
          linarith)

/-- The game in which the player may pay `price` to abandon all remaining requests.
At a coin node immediate escape is redundant: both child values are at most the price. -/
def escapeEval (price : ℝ) : FiniteGame V → V → ℝ
  | .stop, _ => 0
  | .request S hS next, x =>
    min price (S.inf' hS (fun y => dist x y + escapeEval price next y))
  | .coin left right, x => (escapeEval price left x + escapeEval price right x) / 2



theorem escapeEval_le_price {price : ℝ} (hp : 0 ≤ price) (G : FiniteGame V) :
    ∀ x, escapeEval price G x ≤ price := by
  induction G with
  | stop => exact fun _ => hp
  | request S hS G ih => exact fun _ => min_le_left _ _
  | coin G₁ G₂ ih₁ ih₂ =>
    exact fun x => by dsimp only [escapeEval]; linarith [ih₁ x, ih₂ x]

theorem escapeEval_le_eval (price : ℝ) (G : FiniteGame V) :
    ∀ x, escapeEval price G x ≤ eval (fun _ => 0) G x := by
  induction G with
  | stop => exact fun _ => le_rfl
  | request S hS G ih =>
    intro x
    exact (min_le_right _ _).trans (Finset.le_inf' hS _ (fun y hy =>
      (Finset.inf'_le _ hy).trans (add_le_add le_rfl (ih y))))
  | coin G₁ G₂ ih₁ ih₂ =>
    exact fun x => div_le_div_of_nonneg_right (add_le_add (ih₁ x) (ih₂ x)) (by norm_num)

end FiniteGame
end ConvexBodyChasing

end
end BundledModule005

/- Component source: ConvexBodyChasing.Requests -/
section BundledModule006
/-! # The three-stage request generator

All random choices below are fair coins in a fixed finite tree, independent of
the online algorithm. Endpoints are retained, so repeated requests are explicit.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing

structure Call (V : Type*) where
  source : V
  target : V
  game : FiniteGame V

namespace Call

variable {V W : Type*}

def map [DecidableEq W] (f : V → W) (C : Call V) : Call W :=
  ⟨f C.source, f C.target, C.game.map f⟩

end Call

namespace Requests

variable {V : Type*} [DecidableEq V]

def singleton (v : V) (next : FiniteGame V) : FiniteGame V :=
  .request {v} (Finset.singleton_nonempty v) next

def sequence : List (Call V) → FiniteGame V
  | [] => .stop
  | C :: Cs => C.game.append (sequence Cs)

/-- Stage 1. Each pair advances first the left branch and then the right branch. -/
def alternating : List (Call V × Call V) → V → FiniteGame V → FiniteGame V
  | [], _, next => next
  | (L, R) :: rest, waiting, next =>
    (L.game.withWaiting waiting).append
      ((R.game.withWaiting L.target).append (alternating rest R.target next))

/-- Stage 3 chooses the branch with more calls remaining (left in a tie). -/
def finish (left right : List (Call V)) (u v : V) : FiniteGame V :=
  if right.length ≤ left.length then singleton u (sequence left)
  else singleton v (sequence right)

/-- Stage 2. With enough remaining calls, there is one fresh fair coin in every
round. The empty-list cases make the definition total; the constructed branches
have `2m` large copies for only `m` rounds. -/
def randomStage : ℕ → List (Call V) → List (Call V) → V → V → FiniteGame V
  | 0, left, right, u, v => finish left right u v
  | n + 1, L :: left, R :: right, u, v =>
    .coin
      ((L.game.withWaiting v).append (randomStage n left (R :: right) L.target v))
      ((R.game.withWaiting u).append (randomStage n (L :: left) right u R.target))
  | _ + 1, [], right, u, v => finish [] right u v
  | _ + 1, left, [], u, v => finish left [] u v

def lastTarget (fallback : V) (calls : List (Call V)) : V :=
  calls.foldl (fun _ C => C.target) fallback

/-- The request sequence in one recursive call, including its initial singleton. -/
def threeStage (source u v : V) (smallLeft smallRight largeLeft largeRight : List (Call V))
    (rounds : ℕ) : FiniteGame V :=
  singleton source <|
    .request {u, v} (by simp) <|
      alternating (smallLeft.zip smallRight) v <|
        randomStage rounds largeLeft largeRight
          (lastTarget u smallLeft) (lastTarget v smallRight)

end Requests
end ConvexBodyChasing

end
end BundledModule006

/- Component source: ConvexBodyChasing.Escape -/
section BundledModule007
/-! # Escape-price Bellman comparisons

An escape option is available after observing any prefix. Consequently these
comparisons do not condition an expected-cost bound on the event of finishing
a recursive call.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing.FiniteGame

variable {V : Type*} [MetricSpace V]

/-- Bellman evaluation with both an escape price and a terminal continuation cost. -/
def capEval (price : ℝ) (terminal : V → ℝ) : FiniteGame V → V → ℝ
  | .stop, x => terminal x
  | .request S hS next, x =>
    min price (S.inf' hS (fun y => dist x y + capEval price terminal next y))
  | .coin left right, x => (capEval price terminal left x + capEval price terminal right x) / 2

theorem capEval_zero (price : ℝ) (G : FiniteGame V) :
    capEval price (fun _ => 0) G = escapeEval price G := by
  induction G with
  | stop => rfl
  | request S hS G ih => simp only [capEval, escapeEval, ih]
  | coin G H ihG ihH => simp only [capEval, escapeEval, ihG, ihH]

theorem capEval_append (price : ℝ) (G H : FiniteGame V) (f : V → ℝ) :
    capEval price f (G.append H) = capEval price (capEval price f H) G := by
  induction G with
  | stop => rfl
  | request S hS G ih => simp only [append, capEval, ih]
  | coin G H ihG ihH => simp only [append, capEval, ihG, ihH]

theorem add_inf' {ι : Type*} (S : Finset ι) (hS : S.Nonempty) (f : ι → ℝ) (c : ℝ) :
    S.inf' hS f + c = S.inf' hS (fun x => f x + c) := by
  refine Finset.apply_inf'_eq_inf'_comp hS (fun x : ℝ => x + c) ?_
  exact fun x y => (min_add_add_right x y c).symm

theorem capEval_shift (G : FiniteGame V) (price c : ℝ) (f : V → ℝ) :
    ∀ x, capEval (price + c) (fun y => f y + c) G x = capEval price f G x + c := by
  induction G with
  | stop => exact fun _ => rfl
  | request S hS G ih =>
    intro x
    simp only [capEval, ih, ← add_assoc, ← add_inf', min_add_add_right]
  | coin G H ihG ihH =>
    intro x
    simp only [capEval, ihG, ihH]
    ring

theorem capEval_mono (G : FiniteGame V) {p q : ℝ} (hpq : p ≤ q)
    {f g : V → ℝ} (hfg : ∀ x, f x ≤ g x) : ∀ x, capEval p f G x ≤ capEval q g G x := by
  induction G with
  | stop => exact hfg
  | request S hS G ih =>
    intro x
    exact min_le_min hpq (Finset.le_inf' hS _ (fun y hy =>
      (Finset.inf'_le _ hy).trans (add_le_add le_rfl (ih y))))
  | coin G H ihG ihH =>
    exact fun x => div_le_div_of_nonneg_right (add_le_add (ihG x) (ihH x)) (by norm_num)

theorem escapeEval_mono_price (G : FiniteGame V) {p q : ℝ} (hpq : p ≤ q) (x : V) :
    escapeEval p G x ≤ escapeEval q G x := by
  simpa only [capEval_zero] using! capEval_mono G hpq (fun _ => le_refl (0 : ℝ)) x

theorem capEval_ge_escape_add (G : FiniteGame V) {p c price : ℝ} (hp : p + c ≤ price)
    {f : V → ℝ} (hf : ∀ x, c ≤ f x) (x : V) :
    escapeEval p G x + c ≤ capEval price f G x := by
  calc
    escapeEval p G x + c = capEval (p + c) (fun _ => c) G x := by
      simpa only [capEval_zero, zero_add] using! (capEval_shift G p c (fun _ => 0) x).symm
    _ ≤ capEval price f G x := capEval_mono G hp hf x

theorem capEval_ge_const (G : FiniteGame V) {price c : ℝ} (hp : c ≤ price)
    {f : V → ℝ} (hf : ∀ x, c ≤ f x) : ∀ x, c ≤ capEval price f G x := by
  induction G with
  | stop => exact hf
  | request S hS G ih =>
    exact fun x => le_min hp (Finset.le_inf' hS _ (fun y _ =>
      (ih y).trans (le_add_of_nonneg_left dist_nonneg)))
  | coin G H ihG ihH =>
    intro x
    change c ≤ (capEval price f G x + capEval price f H x) / 2
    linarith [ihG x, ihH x]





/-- A request leaves a 1-Lipschitz continuation unchanged at any feasible point. -/
theorem request_eval_at_mem (S : Finset V) (hS : S.Nonempty) {f : V → ℝ}
    (hf : LipschitzWith 1 f) {x : V} (hx : x ∈ S) :
    S.inf' hS (fun y => dist x y + f y) = f x := by
  apply le_antisymm
  · simpa only [dist_self, zero_add] using! Finset.inf'_le (fun y => dist x y + f y) hx
  · exact Finset.le_inf' hS _ (fun y _ => by
      simpa only [NNReal.coe_one, one_mul, add_comm] using! hf.le_add_mul x y)





/-- All requests lie in a specified part of the ambient metric space. -/
def Supported (A : Set V) : FiniteGame V → Prop
  | .stop => True
  | .request S _ G => (↑S : Set V) ⊆ A ∧ Supported A G
  | .coin G H => Supported A G ∧ Supported A H

/-- Reaching the waiting vertex is at least as costly as escaping the recursive
game. The comparison permits a later continuation cost and a larger outer price. -/
theorem capEval_withWaiting_ge [DecidableEq V] (G : FiniteGame V) (A : Set V) (z : V)
    {p price c : ℝ} (hp : 0 ≤ p) (hprice : p + c ≤ price)
    {f : V → ℝ} (hf : ∀ x, c ≤ f x)
    (hsupport : Supported A G) (hsep : ∀ x ∈ A, p ≤ dist x z) :
    ∀ x ∈ A, escapeEval p G x + c ≤ capEval price f (G.withWaiting z) x := by
  induction G with
  | stop => exact fun x _ => by simpa only [escapeEval, withWaiting, capEval, zero_add] using! hf x
  | request S hS G ih =>
    intro x hx
    refine le_min ((add_le_add (escapeEval_le_price hp _ x) le_rfl).trans hprice) ?_
    refine Finset.le_inf' _ _ (fun y hy => ?_)
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact add_le_add ((escapeEval_le_price hp _ x).trans (hsep x hx))
        (capEval_ge_const _ ((le_add_of_nonneg_left hp).trans hprice) hf y)
    · calc
        escapeEval p (request S hS G) x + c ≤ (dist x y + escapeEval p G y) + c :=
          add_le_add ((min_le_right _ _).trans (Finset.inf'_le _ hy)) le_rfl
        _ ≤ dist x y + capEval price f (withWaiting z G) y := by
          simpa only [add_assoc] using! add_le_add le_rfl (ih hsupport.2 y (hsupport.1 hy))
  | coin G H ihG ihH =>
    intro x hx
    simp only [escapeEval, withWaiting, capEval]
    linarith [ihG hsupport.1 x hx, ihH hsupport.2 x hx]



theorem capEval_map {W : Type*} [MetricSpace W] [DecidableEq W] (ι : V → W)
    (hι : Isometry ι) (G : FiniteGame V) (price : ℝ) (f : W → ℝ) :
    ∀ x, capEval price f (G.map ι) (ι x) = capEval price (f ∘ ι) G x := by
  induction G with
  | stop => exact fun _ => rfl
  | request S hS G ih =>
    intro x
    simp only [map, capEval, Finset.inf'_image, Function.comp_apply, hι.dist_eq, ih]
  | coin G H ihG ihH =>
    exact fun x => by simp only [map, capEval, ihG, ihH]

theorem escapeEval_map {W : Type*} [MetricSpace W] [DecidableEq W] (ι : V → W)
    (hι : Isometry ι) (G : FiniteGame V) (price : ℝ) (x : V) :
    escapeEval price (G.map ι) (ι x) = escapeEval price G x := by
  simpa only [capEval_zero, Function.comp_def] using! capEval_map ι hι G price (fun _ => 0) x

theorem mul_inf' {ι : Type*} (S : Finset ι) (hS : S.Nonempty) (f : ι → ℝ)
    {c : ℝ} (hc : 0 ≤ c) : c * S.inf' hS f = S.inf' hS (fun x => c * f x) := by
  apply Finset.apply_inf'_eq_inf'_comp
  exact fun x y => mul_min_of_nonneg x y hc

theorem escapeEval_map_scale {W : Type*} [MetricSpace W] [DecidableEq W]
    (ι : V → W) {c : ℝ} (hc : 0 ≤ c)
    (hdist : ∀ x y, dist (ι x) (ι y) = c * dist x y) (G : FiniteGame V) (price : ℝ) :
    ∀ x, escapeEval (c * price) (G.map ι) (ι x) = c * escapeEval price G x := by
  induction G with
  | stop => exact fun _ => (mul_zero c).symm
  | request S hS G ih =>
    intro x
    simp only [map, escapeEval, Finset.inf'_image, Function.comp_apply, hdist, ih,
      ← mul_add, ← mul_inf' _ _ _ hc, mul_min_of_nonneg _ _ hc]
  | coin G H ihG ihH =>
    intro x
    simp only [map, escapeEval, ihG, ihH]
    ring

omit [MetricSpace V] in
theorem Supported.mono {A B : Set V} {G : FiniteGame V}
    (h : Supported A G) (hAB : A ⊆ B) : Supported B G := by
  induction G with
  | stop => trivial
  | request S hS G ih => exact ⟨fun _ hx => hAB (h.1 hx), ih h.2⟩
  | coin G H ihG ihH => exact ⟨ihG h.1, ihH h.2⟩

omit [MetricSpace V] in
theorem Supported.map {W : Type*} [DecidableEq W] {A : Set V} {G : FiniteGame V}
    (h : Supported A G) (f : V → W) : Supported (f '' A) (G.map f) := by
  induction G with
  | stop => trivial
  | request S hS G ih =>
    refine ⟨?_, ih h.2⟩
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact ⟨x, h.1 hx, rfl⟩
  | coin G H ihG ihH => exact ⟨ihG h.1, ihH h.2⟩





/-- An escape-price lower bound remains valid when the first request fixes the
starting point, regardless of the location before that request. -/
theorem escapeEval_singleton_ge [DecidableEq V] (s : V) (G : FiniteGame V) (price : ℝ)
    (x : V) :
    escapeEval price (request {s} (Finset.singleton_nonempty s) G) s ≤
      escapeEval price (request {s} (Finset.singleton_nonempty s) G) x := by
  simp only [escapeEval, Finset.inf'_singleton, dist_self, zero_add]
  exact min_le_min le_rfl (le_add_of_nonneg_left dist_nonneg)

end ConvexBodyChasing.FiniteGame

end
end BundledModule007

/- Component source: ConvexBodyChasing.Trace -/
section BundledModule008
/-! # Realized requests and feasible directed paths

The realization relation records all outcomes of a finite fair-coin tree.
Offline paths may depend on the complete realized list. They are not required
to form an online strategy in the tree.
-/

namespace ConvexBodyChasing
namespace FiniteGame

variable {V W : Type*}

def Realizes : FiniteGame V → List (Finset V) → Prop
  | .stop, requests => requests = []
  | .request S _ next, requests => ∃ rest, requests = S :: rest ∧ next.Realizes rest
  | .coin left right, requests => left.Realizes requests ∨ right.Realizes requests

theorem realizes_append (G H : FiniteGame V) (requests : List (Finset V)) :
    (G.append H).Realizes requests ↔
      ∃ first rest, G.Realizes first ∧ H.Realizes rest ∧ requests = first ++ rest := by
  induction G generalizing requests with
  | stop => simp [append, Realizes]
  | request S hS G ih =>
    simp only [append, Realizes, ih]
    aesop
  | coin G₁ G₂ ih₁ ih₂ =>
    simp only [append, Realizes, ih₁, ih₂]
    aesop

theorem realizes_map [DecidableEq W] (f : V → W) (G : FiniteGame V)
    (requests : List (Finset W)) :
    (G.map f).Realizes requests ↔
      ∃ original, G.Realizes original ∧ requests = original.map (fun S => S.image f) := by
  induction G generalizing requests with
  | stop => simp [map, Realizes]
  | request S hS G ih =>
    simp only [map, Realizes, ih]
    aesop
  | coin G₁ G₂ ih₁ ih₂ =>
    simp only [map, Realizes, ih₁, ih₂]
    aesop

theorem realizes_withWaiting [DecidableEq V] (z : V) (G : FiniteGame V)
    (requests : List (Finset V)) :
    (G.withWaiting z).Realizes requests ↔
      ∃ original, G.Realizes original ∧ requests = original.map (insert z) := by
  induction G generalizing requests with
  | stop => simp [withWaiting, Realizes]
  | request S hS G ih =>
    simp only [withWaiting, Realizes, ih]
    aesop
  | coin G₁ G₂ ih₁ ih₂ =>
    simp only [withWaiting, Realizes, ih₁, ih₂]
    aesop

end FiniteGame

/-- A feasible offline path whose every move satisfies the relation `R`. -/
inductive ServesAlong {V : Type*} (R : V → V → Prop) :
    V → List (Finset V) → V → Prop where
  | nil (x : V) : ServesAlong R x [] x
  | cons {x y z : V} {S : Finset V} {requests : List (Finset V)}
      (mem : y ∈ S) (move : R x y) (rest : ServesAlong R y requests z) :
      ServesAlong R x (S :: requests) z

namespace ServesAlong

variable {V W : Type*} {R : V → V → Prop}

theorem append {x y z : V} {first rest : List (Finset V)}
    (h₁ : ServesAlong R x first y) (h₂ : ServesAlong R y rest z) :
    ServesAlong R x (first ++ rest) z := by
  induction h₁ with
  | nil => exact h₂
  | cons hmem hmove hpath ih => exact .cons hmem hmove (ih h₂)

theorem map [DecidableEq W] {T : W → W → Prop} (f : V → W)
    (hf : ∀ {x y}, R x y → T (f x) (f y)) {x y : V} {requests : List (Finset V)}
    (h : ServesAlong R x requests y) :
    ServesAlong T (f x) (requests.map (fun S => S.image f)) (f y) := by
  induction h with
  | nil => exact .nil _
  | cons hmem hmove hpath ih => exact .cons (Finset.mem_image_of_mem f hmem) (hf hmove) ih

theorem enlarge (F : Finset V → Finset V) (hF : ∀ S, S ⊆ F S)
    {x y : V} {requests : List (Finset V)} (h : ServesAlong R x requests y) :
    ServesAlong R x (requests.map F) y := by
  induction h with
  | nil => exact .nil _
  | cons hmem hmove hpath ih => exact .cons (hF _ hmem) hmove ih

theorem wait (z : V) (hzz : R z z) (requests : List (Finset V)) :
    (∀ S ∈ requests, z ∈ S) → ServesAlong R z requests z := by
  induction requests with
  | nil => exact fun _ => .nil z
  | cons S requests ih =>
    exact fun h => .cons (h S (List.mem_cons_self ..)) hzz
      (ih (fun T hT => h T (List.mem_cons_of_mem _ hT)))

end ServesAlong

section MetricPaths

variable {V : Type*} [PseudoMetricSpace V]

def metricMovement (start : V) : List V → ℝ
  | [] => 0
  | x :: xs => dist start x + metricMovement x xs

/-- The direction relation induced by a depth function. -/
def Forward (height : V → ℝ) (x y : V) : Prop := dist x y = height y - height x

theorem forward_refl (height : V → ℝ) (x : V) : Forward height x x := by
  simp only [Forward, dist_self, sub_self]

theorem ServesAlong.exists_path {height : V → ℝ} {x y : V} {requests : List (Finset V)}
    (h : ServesAlong (Forward height) x requests y) :
    ∃ path : List V, List.Forall₂ (fun S z => z ∈ S) requests path ∧
      metricMovement x path = height y - height x := by
  induction h with
  | nil x => exact ⟨[], .nil, by simp only [metricMovement, sub_self]⟩
  | @cons x y z S requests hmem hmove hpath ih =>
    obtain ⟨path, hfeas, hcost⟩ := ih
    refine ⟨y :: path, .cons hmem hfeas, ?_⟩
    simp only [metricMovement, hcost]
    linarith [show dist x y = height y - height x from hmove]

end MetricPaths
end ConvexBodyChasing

end BundledModule008

/- Component source: ConvexBodyChasing.Transitions -/
section BundledModule009
/-! # Consecutive-request relations on the entire finite tree

The previous request is explicit. At a stop node it must equal the specified
final request, so sequential composition also checks the joins between calls.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing
namespace FiniteGame
variable {V W : Type*}

def TransitionChain (R : Finset V → Finset V → Prop) :
    FiniteGame V → Finset V → Finset V → Prop
  | .stop, S, T => S = T
  | .request U _ next, S, T => R S U ∧ TransitionChain R next U T
  | .coin left right, S, T => TransitionChain R left S T ∧ TransitionChain R right S T

theorem TransitionChain.mono {R Q : Finset V → Finset V → Prop}
    {game : FiniteGame V} {S T : Finset V} (h : TransitionChain R game S T)
    (hRQ : ∀ A B, R A B → Q A B) : TransitionChain Q game S T := by
  induction game generalizing S with
  | stop => exact h
  | request U hU game ih => exact ⟨hRQ S U h.1, ih h.2⟩
  | coin left right ihl ihr => exact ⟨ihl h.1, ihr h.2⟩

theorem TransitionChain.append {R : Finset V → Finset V → Prop}
    {left right : FiniteGame V} {S M T : Finset V}
    (hl : TransitionChain R left S M) (hr : TransitionChain R right M T) :
    TransitionChain R (left.append right) S T := by
  induction left generalizing S with
  | stop => exact hl.symm ▸ hr
  | request U hU left ih => exact ⟨hl.1, ih hl.2⟩
  | coin left right ihl ihr => exact ⟨ihl hl.1, ihr hl.2⟩

theorem TransitionChain.map [DecidableEq W] {R : Finset V → Finset V → Prop}
    {Q : Finset W → Finset W → Prop} {game : FiniteGame V} {S T : Finset V}
    (h : TransitionChain R game S T) (f : V → W)
    (hRQ : ∀ A B, R A B → Q (A.image f) (B.image f)) :
    TransitionChain Q (game.map f) (S.image f) (T.image f) := by
  induction game generalizing S with
  | stop => exact congrArg (Finset.image f) h
  | request U hU game ih => exact ⟨hRQ S U h.1, ih h.2⟩
  | coin left right ihl ihr => exact ⟨ihl h.1, ihr h.2⟩

theorem TransitionChain.withWaiting [DecidableEq V] {R Q : Finset V → Finset V → Prop}
    {game : FiniteGame V} {S T : Finset V} (h : TransitionChain R game S T) (z : V)
    (hRQ : ∀ A B, R A B → Q (insert z A) (insert z B)) :
    TransitionChain Q (game.withWaiting z) (insert z S) (insert z T) := by
  induction game generalizing S with
  | stop => exact congrArg (insert z) h
  | request U hU game ih => exact ⟨hRQ S U h.1, ih h.2⟩
  | coin left right ihl ihr => exact ⟨ihl h.1, ihr h.2⟩

theorem TransitionChain.supported [DecidableEq V] {R : Finset V → Finset V → Prop}
    {game : FiniteGame V} {S T : Finset V} (h : TransitionChain R game S T)
    {A : Set V} (hgame : Supported A game) (hS : (↑S : Set V) ⊆ A) :
    TransitionChain (fun U W => R U W ∧ (↑(U ∪ W) : Set V) ⊆ A) game S T := by
  induction game generalizing S with
  | stop => exact h
  | request U hU game ih =>
    refine ⟨⟨h.1, ?_⟩, ih h.2 hgame.2 hgame.1⟩
    exact fun _ hx => (Finset.mem_union.mp hx).elim (fun hx => hS hx) (fun hx => hgame.1 hx)
  | coin left right ihl ihr => exact ⟨ihl h.1 hgame.1 hS, ihr h.2 hgame.2 hS⟩



end FiniteGame
end ConvexBodyChasing

end
end BundledModule009

/- Component source: ConvexBodyChasing.ConvexGame -/
section BundledModule010
/-! # Bellman comparison for convexified finite games

At a request a convex strategy chooses any point of the embedded convex hull.
A local dual estimate bounds the drop in the discrete Bellman potential by
the movement of this point. Induction over the fixed finite tree aggregates
these estimates, including its fair coin nodes.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
namespace ConvexBodyChasing

variable {V E : Type*} [Fintype V] [MetricSpace V] [DecidableEq V]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The norm version of the consecutive-request signed-pairing estimate. -/
def DualStep (φ : V → E) (C : ℝ) (S T : Finset V) : Prop :=
  ∀ μ f : V → ℝ, (∑ v, μ v) = 0 →
    (∀ v, μ v ≠ 0 → v ∈ S ∪ T) → LipschitzWith 1 f →
    |SignedMass.pairing μ f| ≤ C * ‖∑ v, μ v • φ v‖

theorem DualStep.mean_le {φ : V → E} {C : ℝ} {S T : Finset V}
    (h : DualStep φ C S T) (P : RequestWeights S) (Q : RequestWeights T)
    (f : V → ℝ) (hf : LipschitzWith 1 f) :
    P.mean f - Q.mean f ≤ C * dist (P.barycenter φ) (Q.barycenter φ) := by
  have hb := h (fun v => P.weight v - Q.weight v) f (P.difference_total Q)
    (P.difference_supported Q) hf
  simpa only [P.pairing_difference Q f, P.barycenter_difference Q φ, dist_eq_norm] using!
    (le_abs_self _).trans hb

namespace FiniteGame

/-- Choices may depend on preceding coin outcomes, but not future outcomes. -/
def ConvexStrategy (φ : V → E) : FiniteGame V → Type _
  | .stop => PUnit
  | .request S _ next =>
    {x // x ∈ convexHull ℝ (φ '' (↑S : Set V))} × ConvexStrategy φ next
  | .coin left right => ConvexStrategy φ left × ConvexStrategy φ right

def convexCost (φ : V → E) : (game : FiniteGame V) → ConvexStrategy φ game → E → ℝ
  | .stop, _, _ => 0
  | .request _ _ next, π, x => dist x π.1.val + convexCost φ next π.2 π.1.val
  | .coin left right, π, x => (convexCost φ left π.1 x + convexCost φ right π.2 x) / 2

/-- A local geometric estimate transfers the discrete value to every convex strategy. -/
theorem mean_eval_le_convexCost (φ : V → E) (C : ℝ) (game : FiniteGame V)
    {S T : Finset V} (h : TransitionChain (DualStep φ C) game S T)
    (P : RequestWeights S) (π : ConvexStrategy φ game) :
    P.mean (eval (fun _ => 0) game) ≤ C * convexCost φ game π (P.barycenter φ) := by
  induction game generalizing S with
  | stop => simp [eval, convexCost]
  | request U hU game ih =>
    obtain ⟨Q, hQ⟩ := RequestWeights.exists_of_mem_convexHull φ π.1.property
    have hf : LipschitzWith 1 (fun _ : V => (0 : ℝ)) := by
      exact (LipschitzWith.const 0).weaken (by norm_num)
    have hstep := h.1.mean_le P Q _ ((request U hU game).eval_lipschitz hf)
    have hmean : Q.mean (eval (fun _ => 0) (request U hU game)) =
        Q.mean (eval (fun _ => 0) game) := Q.mean_congr
      (fun v hv => request_eval_at_mem U hU (game.eval_lipschitz hf) hv)
    rw [hmean] at hstep
    have htotal := (sub_le_iff_le_add.mp hstep).trans (add_le_add le_rfl (ih h.2 Q π.2))
    simpa only [hQ, convexCost, mul_add] using! htotal
  | coin left right ihl ihr =>
    simp only [eval, RequestWeights.mean_div, RequestWeights.mean_add, convexCost]
    linarith [ihl h.1 P π.1, ihr h.2 P π.2]

theorem eval_le_convexCost (φ : V → E) (C : ℝ) (game : FiniteGame V)
    {start : V} {T : Finset V} (h : TransitionChain (DualStep φ C) game {start} T)
    (π : ConvexStrategy φ game) :
    eval (fun _ => 0) game start ≤ C * convexCost φ game π (φ start) := by
  simpa only [RequestWeights.mean_point, RequestWeights.barycenter_point] using!
    mean_eval_le_convexCost φ C game h (RequestWeights.point start (Finset.mem_singleton_self _)) π

end FiniteGame

end ConvexBodyChasing

end
end BundledModule010

/- Component source: ConvexBodyChasing.Geometry -/
section BundledModule011
/-! # Finite metric spaces with two terminals

Every vertex of the manuscript's graphs lies on a shortest source-to-target
path. This module packages that property and constructs series composition
using mathlib's metric gluing, so triangle inequalities are not assumptions.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace ConvexBodyChasing

structure TwoTerminal where
  Point : Type
  metric : MetricSpace Point
  finite : Finite Point
  source : Point
  target : Point
  distinct : source ≠ target
  on_geodesic : ∀ x, dist source x + dist x target = dist source target

attribute [instance] TwoTerminal.metric TwoTerminal.finite

instance : CoeSort TwoTerminal Type := ⟨TwoTerminal.Point⟩

namespace TwoTerminal

def length (G : TwoTerminal) : ℝ := dist G.source G.target
def depth (G : TwoTerminal) (x : G) : ℝ := dist G.source x

theorem length_pos (G : TwoTerminal) : 0 < G.length := dist_pos.mpr G.distinct

theorem depth_nonneg (G : TwoTerminal) (x : G) : 0 ≤ G.depth x := dist_nonneg

theorem depth_le_length (G : TwoTerminal) (x : G) : G.depth x ≤ G.length := by
  have := G.on_geodesic x
  exact le_add_of_nonneg_right (dist_nonneg (x := x) (y := G.target)) |>.trans_eq this

theorem dist_target (G : TwoTerminal) (x : G) : dist x G.target = G.length - G.depth x :=
  eq_sub_of_add_eq' (G.on_geodesic x)

theorem depth_lipschitz (G : TwoTerminal) : LipschitzWith 1 G.depth :=
  LipschitzWith.dist_right G.source

theorem dist_le_via_source (G : TwoTerminal) (x y : G) :
    dist x y ≤ G.depth x + G.depth y := by
  simpa only [depth, dist_comm x G.source] using! dist_triangle x G.source y

theorem dist_le_via_target (G : TwoTerminal) (x y : G) :
    dist x y ≤ 2 * G.length - G.depth x - G.depth y := by
  have := dist_triangle x G.target y
  linarith [G.dist_target x, G.dist_target y, dist_comm G.target y]

theorem dist_le_length (G : TwoTerminal) (x y : G) : dist x y ≤ G.length := by
  linarith [G.dist_le_via_source x y, G.dist_le_via_target x y]

namespace Series

variable (G H : TwoTerminal)

def leftAttachment : Unit → G := fun _ => G.target
def rightAttachment : Unit → H := fun _ => H.source

theorem left_isometry : Isometry (leftAttachment G) :=
  Isometry.of_dist_eq (fun _ _ => by simp [leftAttachment])

theorem right_isometry : Isometry (rightAttachment H) :=
  Isometry.of_dist_eq (fun _ _ => by simp [rightAttachment])

abbrev Point := Metric.GlueSpace (left_isometry G) (right_isometry H)

def inl : G → Point G H := Metric.toGlueL _ _
def inr : H → Point G H := Metric.toGlueR _ _

theorem inl_isometry : Isometry (inl G H) := Metric.toGlueL_isometry _ _
theorem inr_isometry : Isometry (inr G H) := Metric.toGlueR_isometry _ _

theorem dist_inl_inr (x : G) (y : H) :
    dist (inl G H x) (inr G H y) = dist x G.target + dist H.source y := by
  change (⨅ _ : Unit, dist x G.target + dist y H.source) + 0 = _
  simp only [ciInf_const, add_zero, dist_comm y H.source]

theorem joint : inl G H G.target = inr G H H.source :=
  congr_fun (Metric.toGlue_commute (left_isometry G) (right_isometry H)) ()

instance : Finite (Point G H) := by
  unfold Point Metric.GlueSpace SeparationQuotient
  infer_instance

theorem cases (x : Point G H) :
    (∃ y : G, x = inl G H y) ∨ (∃ y : H, x = inr G H y) := by
  induction x using Quotient.inductionOn'
  rename_i a
  exact match a with
    | .inl y => Or.inl ⟨y, rfl⟩
    | .inr y => Or.inr ⟨y, rfl⟩

theorem terminal_distance :
    dist (inl G H G.source) (inr G H H.target) = G.length + H.length :=
  dist_inl_inr G H G.source H.target

theorem on_geodesic (x : Point G H) :
    dist (inl G H G.source) x + dist x (inr G H H.target) =
      dist (inl G H G.source) (inr G H H.target) := by
  rcases cases G H x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · simpa only [(inl_isometry G H).dist_eq, dist_inl_inr, ← add_assoc] using!
      congrArg (fun z => z + H.length) (G.on_geodesic y)
  · simpa only [(inr_isometry G H).dist_eq, dist_inl_inr, add_assoc] using!
      congrArg (fun z => G.length + z) (H.on_geodesic y)

end Series

/-- Concatenating two two-terminal spaces identifies just their adjacent terminals. -/
def series (G H : TwoTerminal) : TwoTerminal where
  Point := Series.Point G H
  metric := inferInstance
  finite := inferInstance
  source := Series.inl G H G.source
  target := Series.inr G H H.target
  distinct := by
    apply dist_pos.mp
    simpa only [Series.terminal_distance] using! add_pos G.length_pos H.length_pos
  on_geodesic := Series.on_geodesic G H


namespace Parallel

variable (G : TwoTerminal)

def Endpoints := {x : G // x = G.source ∨ x = G.target}

instance : MetricSpace (Endpoints G) :=
  inferInstanceAs (MetricSpace {x : G // x = G.source ∨ x = G.target})
instance : Nonempty (Endpoints G) := ⟨⟨G.source, Or.inl rfl⟩⟩

def attachment : Endpoints G → G := Subtype.val

theorem attachment_isometry : Isometry (attachment G) :=
  Isometry.of_dist_eq (fun _ _ => rfl)

abbrev Point := Metric.GlueSpace (attachment_isometry G) (attachment_isometry G)
def inl : G → Point G := Metric.toGlueL _ _
def inr : G → Point G := Metric.toGlueR _ _

theorem inl_isometry : Isometry (inl G) := Metric.toGlueL_isometry _ _
theorem inr_isometry : Isometry (inr G) := Metric.toGlueR_isometry _ _

theorem joint_source : inl G G.source = inr G G.source :=
  congrFun (Metric.toGlue_commute (attachment_isometry G) (attachment_isometry G))
    (⟨G.source, Or.inl rfl⟩ : Endpoints G)

theorem joint_target : inl G G.target = inr G G.target :=
  congrFun (Metric.toGlue_commute (attachment_isometry G) (attachment_isometry G))
    (⟨G.target, Or.inr rfl⟩ : Endpoints G)

instance : Finite (Point G) := by
  unfold Point Metric.GlueSpace SeparationQuotient
  infer_instance

theorem cases (x : Point G) : (∃ y : G, x = inl G y) ∨ (∃ y : G, x = inr G y) := by
  induction x using Quotient.inductionOn' with
  | h a => exact match a with
    | .inl y => Or.inl ⟨y, rfl⟩
    | .inr y => Or.inr ⟨y, rfl⟩

theorem on_geodesic (x : Point G) :
    dist (inl G G.source) x + dist x (inl G G.target) =
      dist (inl G G.source) (inl G G.target) := by
  rcases cases G x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · simpa only [(inl_isometry G).dist_eq] using! G.on_geodesic y
  · simpa only [joint_source G, joint_target G, (inr_isometry G).dist_eq] using!
      G.on_geodesic y

/-- A lower bound on both routes through the terminals is a lower bound on
the distance between opposite branches. -/
theorem le_dist_inl_inr (x y : G) {a : ℝ}
    (hs : a ≤ G.depth x + G.depth y)
    (ht : a ≤ 2 * G.length - G.depth x - G.depth y) :
    a ≤ dist (inl G x) (inr G y) := by
  change a ≤ (⨅ z : Endpoints G, dist x z.val + dist y z.val) + 0
  simp only [add_zero]
  apply le_ciInf
  rintro ⟨z, rfl | rfl⟩
  · simpa only [depth, dist_comm x G.source, dist_comm y G.source] using! hs
  · simpa only [dist_target] using!
      (show a ≤ (G.length - G.depth x) + (G.length - G.depth y) by linarith)

end Parallel

/-- Two isometric branches sharing just their source and target. -/
def parallel (G : TwoTerminal) : TwoTerminal where
  Point := Parallel.Point G
  metric := inferInstance
  finite := inferInstance
  source := Parallel.inl G G.source
  target := Parallel.inl G G.target
  distinct := fun h => G.distinct ((Parallel.inl_isometry G).injective h)
  on_geodesic := Parallel.on_geodesic G

@[simp] theorem length_series (G H : TwoTerminal) :
    (series G H).length = G.length + H.length := Series.terminal_distance G H

@[simp] theorem length_parallel (G : TwoTerminal) : (parallel G).length = G.length :=
  (Parallel.inl_isometry G).dist_eq _ _

end TwoTerminal
end ConvexBodyChasing

end
end BundledModule011

/- Component source: ConvexBodyChasing.GluedFunctions -/
section BundledModule012
/-! # Lipschitz functions on metric gluings

Functions that agree along the identified subset descend to the metric gluing
without increasing their Lipschitz constant.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing

section
variable {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z] [Nonempty Z]
    {ι : Z → X} {κ : Z → Y}
    (hι : Isometry ι) (hκ : Isometry κ)
    (f : X → ℝ) (g : Y → ℝ) (hf : LipschitzWith 1 f) (hg : LipschitzWith 1 g)
    (hglue : ∀ z, f (ι z) = g (κ z))

omit [MetricSpace Z] in
include hf hg hglue in
theorem glue_function_cross (x : X) (y : Y) :
    dist (f x) (g y) ≤ Metric.glueDist ι κ 0 (.inl x) (.inr y) := by
  change dist (f x) (g y) ≤ (⨅ z, dist x (ι z) + dist y (κ z)) + 0
  simp only [add_zero]
  refine le_ciInf (fun z => ?_)
  calc
    dist (f x) (g y) ≤ dist (f x) (f (ι z)) + dist (f (ι z)) (g y) := dist_triangle ..
    _ ≤ dist x (ι z) + dist y (κ z) := by
      simpa only [hglue, NNReal.coe_one, one_mul, dist_comm (κ z) y] using!
        add_le_add (hf.dist_le_mul x (ι z)) (hg.dist_le_mul (κ z) y)

include hf hg hglue in
theorem glue_function_sum_lipschitz :
    letI := Metric.gluePremetric hι hκ
    LipschitzWith 1 (Sum.elim f g) := by
  letI := Metric.gluePremetric hι hκ
  refine LipschitzWith.of_dist_le_mul ?_
  rintro (x | x) (y | y)
  · exact hf.dist_le_mul x y
  · simpa only [NNReal.coe_one, one_mul] using! glue_function_cross f g hf hg hglue x y
  · simpa only [Sum.elim_inl, Sum.elim_inr, NNReal.coe_one, one_mul,
      dist_comm (g x) (f y)] using! glue_function_cross f g hf hg hglue y x
  · exact hg.dist_le_mul x y

def glueFunction : Metric.GlueSpace hι hκ → ℝ :=
  letI := Metric.gluePremetric hι hκ
  letI : TopologicalSpace (X ⊕ Y) := (Metric.gluePremetric hι hκ).toUniformSpace.toTopologicalSpace
  SeparationQuotient.lift (Sum.elim f g) (fun _ _ h =>
    (h.map (glue_function_sum_lipschitz hι hκ f g hf hg hglue).continuous).eq)





theorem glueFunction_lipschitz : LipschitzWith 1 (glueFunction hι hκ f g hf hg hglue) := by
  letI := Metric.gluePremetric hι hκ
  refine LipschitzWith.of_dist_le_mul ?_
  exact fun x y => Quotient.inductionOn₂' x y (fun a b =>
    (glue_function_sum_lipschitz hι hκ f g hf hg hglue).dist_le_mul a b)

end
end ConvexBodyChasing

end
end BundledModule012

/- Component source: ConvexBodyChasing.BranchFunctions -/
section BundledModule013
/-! # The branch tent functions

On a doubled branch, distance to the other branch is exactly distance to the
nearer terminal. Defining the function this way proves its global Lipschitz
property without assuming that a piecewise extension remains Lipschitz.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing.TwoTerminal

def tent (G : TwoTerminal) (x : G) : ℝ := min (dist G.source x) (dist x G.target)

theorem tent_nonneg (G : TwoTerminal) (x : G) : 0 ≤ G.tent x :=
  le_min dist_nonneg dist_nonneg

theorem tent_eq (G : TwoTerminal) (x : G) :
    G.tent x = min (G.depth x) (G.length - G.depth x) := by
  exact congrArg (min (G.depth x)) (G.dist_target x)

theorem tent_lipschitz (G : TwoTerminal) : LipschitzWith 1 G.tent := by
  simpa only [max_self] using!
    (LipschitzWith.dist_right G.source).min (LipschitzWith.dist_left G.target)









/-- The Stage 1 numerical estimate used in Lemma 7. -/
theorem stage1_distance_bound (G : TwoTerminal) (u v : G) {m b δ : ℝ}
    (hL : G.length = 3 * m + b) (hb : b ≤ m) (hδ : δ ≤ b)
    (hu₀ : b ≤ G.depth u) (hu₁ : G.depth u ≤ b + m)
    (hv : G.depth v ≤ G.depth u + δ) : dist u v ≤ 3 * G.tent u := by
  rw [tent_eq, min_eq_left (show G.depth u ≤ G.length - G.depth u by linarith)]
  linarith [G.dist_le_via_source u v]

/-- The Stage 2/removal numerical estimate used in Lemma 7. -/
theorem stage2_distance_bound (G : TwoTerminal) (u v : G) {m b : ℝ}
    (hL : G.length = 3 * m + b) (hb₀ : 0 ≤ b) (hb₁ : b ≤ m)
    (hu₀ : b + m ≤ G.depth u) (hu₁ : G.depth u ≤ b + 2 * m) :
    dist u v ≤ 4 * G.tent u := by
  have ht : m ≤ G.tent u := by
    rw [tent_eq]
    exact le_min (by linarith) (by linarith)
  linarith [G.dist_le_length u v]

end ConvexBodyChasing.TwoTerminal

end
end BundledModule013

/- Component source: ConvexBodyChasing.Scaling -/
section BundledModule014
/-! # Scaling and the base edge -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing.TwoTerminal

@[ext] structure ScaledPoint (G : TwoTerminal) (c : ℝ) where
  val : G

def scaledMetric (G : TwoTerminal) (c : ℝ) (hc : 0 < c) : MetricSpace (ScaledPoint G c) where
  dist x y := c * dist x.val y.val
  dist_self x := by simp
  dist_comm x y := by rw [dist_comm]
  dist_triangle x y z := by
    simpa only [mul_add] using! mul_le_mul_of_nonneg_left (dist_triangle x.val y.val z.val) hc.le
  eq_of_dist_eq_zero h := by
    have hval := dist_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hc.ne')
    exact ScaledPoint.ext hval

instance (G : TwoTerminal) (c : ℝ) : Finite (ScaledPoint G c) :=
  Finite.of_injective ScaledPoint.val (fun _ _ => ScaledPoint.ext)

def scale (G : TwoTerminal) (c : ℝ) (hc : 0 < c) : TwoTerminal where
  Point := ScaledPoint G c
  metric := scaledMetric G c hc
  finite := inferInstance
  source := ⟨G.source⟩
  target := ⟨G.target⟩
  distinct := fun h => G.distinct (congrArg ScaledPoint.val h)
  on_geodesic x := by
    change c * dist G.source x.val + c * dist x.val G.target = c * dist G.source G.target
    rw [← mul_add, G.on_geodesic]

@[simp] theorem length_scale (G : TwoTerminal) (c : ℝ) (hc : 0 < c) :
    (G.scale c hc).length = c * G.length := rfl

/-- Rescale a gadget to a prescribed positive terminal distance. -/
def normalize (G : TwoTerminal) (L : ℝ) (hL : 0 < L) : TwoTerminal :=
  G.scale (L / G.length) (div_pos hL G.length_pos)

@[simp] theorem length_normalize (G : TwoTerminal) (L : ℝ) (hL : 0 < L) :
    (G.normalize L hL).length = L := by
  exact div_mul_cancel₀ L G.length_pos.ne'

/-- The unit edge, with its ordinary distance inherited from the real line. -/
def edge : TwoTerminal where
  Point := Fin 2
  metric := MetricSpace.induced (fun i : Fin 2 => (i.val : ℝ))
    (fun i j h => Fin.ext (Nat.cast_injective h)) inferInstance
  finite := inferInstance
  source := 0
  target := 1
  distinct := by decide
  on_geodesic x := by
    change dist ((0 : ℕ) : ℝ) x.val + dist (x.val : ℝ) ((1 : ℕ) : ℝ) =
      dist ((0 : ℕ) : ℝ) ((1 : ℕ) : ℝ)
    fin_cases x <;> norm_num

@[simp] theorem length_edge : edge.length = 1 := by
  change dist ((0 : ℕ) : ℝ) ((1 : ℕ) : ℝ) = 1
  norm_num

end ConvexBodyChasing.TwoTerminal

end
end BundledModule014

/- Component source: ConvexBodyChasing.RecursiveGraph -/
section BundledModule015
/-! # The graph family of Section 2.1

This is an actual finite metric-space construction. Copies are glued at their
terminals, rescaling multiplies their metric, and the two branches are glued
at both ends. No graph-distance properties are postulated.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing
namespace TwoTerminal

/-- Append `n` isometric copies of `G` to the end of `initial`. -/
def appendCopies (initial G : TwoTerminal) : ℕ → TwoTerminal
  | 0 => initial
  | n + 1 => series (appendCopies initial G n) G

theorem length_appendCopies (initial G : TwoTerminal) (n : ℕ) :
    (appendCopies initial G n).length = initial.length + n * G.length := by
  induction n with
  | zero => simp only [appendCopies, Nat.cast_zero, zero_mul, add_zero]
  | succ n ih =>
    simp only [appendCopies, length_series, ih, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      add_assoc]

/-- One branch: an entrance edge, `m²` short copies, and `2m` unit-length copies. -/
def branch (G : TwoTerminal) (m : ℕ) (hm : 0 < m) (b : ℝ) (hb : 0 < b) : TwoTerminal :=
  appendCopies
    (appendCopies (edge.scale b hb)
      (G.normalize (1 / m) (one_div_pos.mpr (Nat.cast_pos.mpr hm))) (m ^ 2))
    (G.normalize 1 zero_lt_one) (2 * m)

theorem length_branch (G : TwoTerminal) (m : ℕ) (hm : 0 < m) (b : ℝ) (hb : 0 < b) :
    (branch G m hm b hb).length = 3 * m + b := by
  simp only [branch, length_appendCopies, length_normalize, length_scale, length_edge,
    mul_one, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
  field_simp
  ring

def step (G : TwoTerminal) (m : ℕ) (hm : 0 < m) (b : ℝ) (hb : 0 < b) : TwoTerminal :=
  parallel (branch G m hm b hb)

theorem length_step (G : TwoTerminal) (m : ℕ) (hm : 0 < m) (b : ℝ) (hb : 0 < b) :
    (step G m hm b hb).length = 3 * m + b := by
  exact length_branch G m hm b hb

end TwoTerminal

/-- The parameters that determine the graph family. Additional inequalities are
needed for the lower-bound analysis, but not for construction of the metric. -/
structure GraphParameters where
  copies : ℕ → ℕ
  copies_pos : ∀ r, 0 < copies r
  entrance : ℕ → ℝ
  entrance_pos : ∀ r, 0 < entrance r

def recursiveGraph (P : GraphParameters) : ℕ → TwoTerminal
  | 0 => TwoTerminal.edge
  | r + 1 => TwoTerminal.step (recursiveGraph P r)
    (P.copies r) (P.copies_pos r) (P.entrance r) (P.entrance_pos r)



theorem recursiveGraph_length_succ (P : GraphParameters) (r : ℕ) :
    (recursiveGraph P (r + 1)).length = 3 * P.copies r + P.entrance r :=
  TwoTerminal.length_step _ _ _ _ _

end ConvexBodyChasing

end
end BundledModule015

/- Component source: ConvexBodyChasing.AnchoredFunctions -/
section BundledModule016
/-! # Nonnegative Lipschitz coordinates vanishing at both terminals -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing.TwoTerminal

structure AnchoredFunction (G : TwoTerminal) where
  toFun : G → ℝ
  lipschitz : LipschitzWith 1 toFun
  nonneg : ∀ x, 0 ≤ toFun x
  source_zero : toFun G.source = 0
  target_zero : toFun G.target = 0

instance (G : TwoTerminal) : CoeFun (AnchoredFunction G) (fun _ => G → ℝ) := ⟨(·.toFun)⟩

namespace AnchoredFunction

def zero (G : TwoTerminal) : AnchoredFunction G where
  toFun := fun _ => 0
  lipschitz := LipschitzWith.const' 0
  nonneg := fun _ => le_rfl
  source_zero := rfl
  target_zero := rfl

def tent (G : TwoTerminal) : AnchoredFunction G where
  toFun := G.tent
  lipschitz := G.tent_lipschitz
  nonneg := G.tent_nonneg
  source_zero := by simp only [TwoTerminal.tent, dist_self, min_eq_left dist_nonneg]
  target_zero := by simp only [TwoTerminal.tent, dist_self, min_eq_right dist_nonneg]

def series {G H : TwoTerminal} (f : AnchoredFunction G) (g : AnchoredFunction H) :
    AnchoredFunction (G.series H) where
  toFun := glueFunction (Series.left_isometry G) (Series.right_isometry H)
    f g f.lipschitz g.lipschitz (fun _ => f.target_zero.trans g.source_zero.symm)
  lipschitz := glueFunction_lipschitz _ _ _ _ _ _ _
  nonneg := by
    intro x
    rcases Series.cases G H x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact f.nonneg y
    · exact g.nonneg y
  source_zero := f.source_zero
  target_zero := g.target_zero

@[simp] theorem series_inl {G H : TwoTerminal} (f : AnchoredFunction G)
    (g : AnchoredFunction H) (x : G) : f.series g (Series.inl G H x) = f x := rfl



theorem parallel_agree {G : TwoTerminal} (f g : AnchoredFunction G) (z : Parallel.Endpoints G) :
    f (Parallel.attachment G z) = g (Parallel.attachment G z) := by
  rcases z with ⟨z, rfl | rfl⟩
  · exact f.source_zero.trans g.source_zero.symm
  · exact f.target_zero.trans g.target_zero.symm

def parallel {G : TwoTerminal} (f g : AnchoredFunction G) : AnchoredFunction G.parallel where
  toFun := glueFunction (Parallel.attachment_isometry G) (Parallel.attachment_isometry G)
    f g f.lipschitz g.lipschitz (parallel_agree f g)
  lipschitz := glueFunction_lipschitz _ _ _ _ _ _ _
  nonneg := by
    intro x
    rcases Parallel.cases G x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact f.nonneg y
    · exact g.nonneg y
  source_zero := f.source_zero
  target_zero := f.target_zero





def scale {G : TwoTerminal} (f : AnchoredFunction G) (c : ℝ) (hc : 0 < c) :
    AnchoredFunction (G.scale c hc) where
  toFun := fun x => c * f x.val
  lipschitz := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    change |c * f x.val - c * f y.val| ≤ (1 : ℝ) * (c * dist x.val y.val)
    simpa only [← mul_sub, abs_mul, abs_of_pos hc, one_mul, Real.dist_eq,
      NNReal.coe_one] using! mul_le_mul_of_nonneg_left (f.lipschitz.dist_le_mul x.val y.val) hc.le

  nonneg := fun x => mul_nonneg hc.le (f.nonneg x.val)
  source_zero := by simp only [TwoTerminal.scale, f.source_zero, mul_zero]
  target_zero := by simp only [TwoTerminal.scale, f.target_zero, mul_zero]

def normalize {G : TwoTerminal} (f : AnchoredFunction G) (L : ℝ) (hL : 0 < L) :
    AnchoredFunction (G.normalize L hL) := f.scale (L / G.length) (div_pos hL G.length_pos)

def appendCopies {initial G : TwoTerminal} (f : AnchoredFunction initial)
    (g : AnchoredFunction G) : (n : ℕ) → AnchoredFunction (initial.appendCopies G n)
  | 0 => f
  | n + 1 => (appendCopies f g n).series g

/-- Reuse a coordinate on every short and long copy, with zero on the entrance. -/
def branch {G : TwoTerminal} (f : AnchoredFunction G) (m : ℕ) (hm : 0 < m)
    (b : ℝ) (hb : 0 < b) : AnchoredFunction (G.branch m hm b hb) :=
  ((zero (edge.scale b hb)).appendCopies
    (f.normalize (1 / m) (one_div_pos.mpr (Nat.cast_pos.mpr hm))) (m ^ 2)).appendCopies
    (f.normalize 1 zero_lt_one) (2 * m)

/-- Reuse a lower-level coordinate on both branches. -/
def step {G : TwoTerminal} (f : AnchoredFunction G) (m : ℕ) (hm : 0 < m)
    (b : ℝ) (hb : 0 < b) : AnchoredFunction (G.step m hm b hb) :=
  (f.branch m hm b hb).parallel (f.branch m hm b hb)

end AnchoredFunction
end ConvexBodyChasing.TwoTerminal

end
end BundledModule016

/- Component source: ConvexBodyChasing.Coordinates -/
section BundledModule017
/-! # The full recursive coordinate map

There is one depth coordinate and two branch coordinates per nonzero level.
Lower-level coordinates are reused on every copy through metric gluing; the
defining restriction equations express this reuse without a sum over copies.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing

/-- Two new branch coordinates at each level. -/
def BranchCoordinate : ℕ → Type
  | 0 => Empty
  | r + 1 => Bool ⊕ BranchCoordinate r

instance branchCoordinateFintype : (r : ℕ) → Fintype (BranchCoordinate r)
  | 0 => inferInstanceAs (Fintype Empty)
  | r + 1 =>
    letI := branchCoordinateFintype r
    inferInstanceAs (Fintype (Bool ⊕ BranchCoordinate r))

theorem card_branchCoordinate (r : ℕ) : Fintype.card (BranchCoordinate r) = 2 * r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change Fintype.card (Bool ⊕ BranchCoordinate r) = 2 * (r + 1)
    simp only [Fintype.card_sum, Fintype.card_bool, ih, Nat.mul_add, Nat.mul_one, Nat.add_comm]

open TwoTerminal.AnchoredFunction

/-- The branch coordinates, including their checked Lipschitz and endpoint properties. -/
def branchCoordinate (P : GraphParameters) :
    (r : ℕ) → BranchCoordinate r → TwoTerminal.AnchoredFunction (recursiveGraph P r)
  | 0 => Empty.elim
  | r + 1 =>
    let G := recursiveGraph P r
    let whole := G.branch (P.copies r) (P.copies_pos r) (P.entrance r) (P.entrance_pos r)
    Sum.elim
      (fun side => if side then (tent whole).parallel (zero whole)
        else (zero whole).parallel (tent whole))
      (fun i => (branchCoordinate P r i).step (P.copies r) (P.copies_pos r)
        (P.entrance r) (P.entrance_pos r))

abbrev Coordinate (r : ℕ) := Option (BranchCoordinate r)

theorem card_coordinate (r : ℕ) : Fintype.card (Coordinate r) = 2 * r + 1 := by
  simp only [Coordinate, Fintype.card_option, card_branchCoordinate]

/-- The manuscript's map, indexed by one depth slot and two branch slots per level. -/
def Ψ (P : GraphParameters) (r : ℕ) (x : recursiveGraph P r) : Coordinate r → ℝ
  | none => (recursiveGraph P r).depth x
  | some i => branchCoordinate P r i x

theorem coordinate_lipschitz (P : GraphParameters) (r : ℕ) (i : Coordinate r) :
    LipschitzWith 1 (fun x => Ψ P r x i) := by
  cases i with
  | none => exact (recursiveGraph P r).depth_lipschitz
  | some i => exact (branchCoordinate P r i).lipschitz

@[simp] theorem Ψ_source (P : GraphParameters) (r : ℕ) :
    Ψ P r (recursiveGraph P r).source = 0 := by
  funext i
  cases i with
  | none => exact dist_self _
  | some i => exact (branchCoordinate P r i).source_zero





/-- A fixed enumeration exposes the map in the usual `2r + 1` real coordinates. -/
def coordinateEquiv (r : ℕ) : Coordinate r ≃ Fin (2 * r + 1) :=
  Fintype.equivFinOfCardEq (card_coordinate r)

def ΨFin (P : GraphParameters) (r : ℕ) (x : recursiveGraph P r) : Fin (2 * r + 1) → ℝ :=
  fun i => Ψ P r x ((coordinateEquiv r).symm i)

theorem ΨFin_lipschitz (P : GraphParameters) (r : ℕ) : LipschitzWith 1 (ΨFin P r) := by
  exact LipschitzWith.of_dist_le_mul (fun x y =>
    (dist_pi_le_iff (mul_nonneg (by norm_num) dist_nonneg)).mpr
      (fun i => (coordinate_lipschitz P r ((coordinateEquiv r).symm i)).dist_le_mul x y))

@[simp] theorem ΨFin_source (P : GraphParameters) (r : ℕ) :
    ΨFin P r (recursiveGraph P r).source = 0 := by
  exact congrArg (fun f : Coordinate r → ℝ => fun i => f ((coordinateEquiv r).symm i))
    (Ψ_source P r)

end ConvexBodyChasing

end
end BundledModule017

/- Component source: ConvexBodyChasing.EmbeddedCalls -/
section BundledModule019
/-! # Embedding the recursive calls into the graph

The calls are actual images of the smaller request games, under the canonical
maps of the metric gluing construction.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing

local instance (α : Type*) : DecidableEq α := Classical.decEq α

namespace TwoTerminal

def initialEmbedding (initial G : TwoTerminal) : (n : ℕ) → initial → appendCopies initial G n
  | 0 => id
  | n + 1 => Series.inl (appendCopies initial G n) G ∘ initialEmbedding initial G n

theorem initialEmbedding_isometry (initial G : TwoTerminal) (n : ℕ) :
    Isometry (initialEmbedding initial G n) := by
  induction n with
  | zero => exact isometry_id
  | succ n ih => exact (Series.inl_isometry _ _).comp ih

def copyCalls (initial G : TwoTerminal) (g : FiniteGame G) :
    (n : ℕ) → List (Call (appendCopies initial G n))
  | 0 => []
  | n + 1 =>
    (copyCalls initial G g n).map (Call.map (Series.inl (appendCopies initial G n) G)) ++
      [⟨Series.inr (appendCopies initial G n) G G.source,
        Series.inr (appendCopies initial G n) G G.target,
        g.map (Series.inr (appendCopies initial G n) G)⟩]

theorem length_copyCalls (initial G : TwoTerminal) (g : FiniteGame G) (n : ℕ) :
    (copyCalls initial G g n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [copyCalls, List.length_append, List.length_map,
      List.length_cons, List.length_nil, zero_add, ih]



def normalizeGame (G : TwoTerminal) (g : FiniteGame G) (L : ℝ) (hL : 0 < L) :
    FiniteGame (G.normalize L hL) :=
  g.map (fun x => (⟨x⟩ : ScaledPoint G (L / G.length)))



/-- Place the smaller games in the concrete short and long copies, and run the
three-stage distribution on the doubled branch. -/
def stepGame (G : TwoTerminal) (g : FiniteGame G) (m : ℕ) (hm : 0 < m)
    (b : ℝ) (hb : 0 < b) : FiniteGame (G.step m hm b hb) :=
  let hsmall : (0 : ℝ) < 1 / m := one_div_pos.mpr (Nat.cast_pos.mpr hm)
  let entrance := edge.scale b hb
  let small := G.normalize (1 / m) hsmall
  let large := G.normalize 1 zero_lt_one
  let first := appendCopies entrance small (m ^ 2)
  let whole := appendCopies first large (2 * m)
  let lift := initialEmbedding first large (2 * m)
  let smallCalls := (copyCalls entrance small (G.normalizeGame g (1 / m) hsmall) (m ^ 2)).map
    (Call.map lift)
  let largeCalls := copyCalls first large (G.normalizeGame g 1 zero_lt_one) (2 * m)
  let u := lift (initialEmbedding entrance small (m ^ 2) entrance.target)
  let left := Parallel.inl whole
  let right := Parallel.inr whole
  Requests.threeStage (left whole.source) (left u) (right u)
    (smallCalls.map (Call.map left)) (smallCalls.map (Call.map right))
    (largeCalls.map (Call.map left)) (largeCalls.map (Call.map right)) m



end TwoTerminal

/-- The complete, finite, oblivious request distribution from Section 2.2. -/
def recursiveGame (P : GraphParameters) : (r : ℕ) → FiniteGame (recursiveGraph P r)
  | 0 => Requests.singleton TwoTerminal.edge.source
    (Requests.singleton TwoTerminal.edge.target .stop)
  | r + 1 => TwoTerminal.stepGame (recursiveGraph P r) (recursiveGame P r)
    (P.copies r) (P.copies_pos r) (P.entrance r) (P.entrance_pos r)



end ConvexBodyChasing

end
end BundledModule019

/- Component source: ConvexBodyChasing.DirectedGeometry -/
section BundledModule020
/-! # Forward paths under the graph embeddings -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing.TwoTerminal

theorem forward_source (G : TwoTerminal) (x : G) : Forward G.depth G.source x := by
  simp only [Forward, depth, dist_self, sub_zero]

theorem forward_target (G : TwoTerminal) (x : G) : Forward G.depth x G.target :=
  G.dist_target x

@[simp] theorem depth_series_inl (G H : TwoTerminal) (x : G) :
    (G.series H).depth (Series.inl G H x) = G.depth x :=
  (Series.inl_isometry G H).dist_eq _ _

@[simp] theorem depth_series_inr (G H : TwoTerminal) (x : H) :
    (G.series H).depth (Series.inr G H x) = G.length + H.depth x :=
  Series.dist_inl_inr G H G.source x

theorem forward_series_inl (G H : TwoTerminal) {x y : G} (h : Forward G.depth x y) :
    Forward (G.series H).depth (Series.inl G H x) (Series.inl G H y) := by
  simpa only [Forward, depth_series_inl, (Series.inl_isometry G H).dist_eq] using! h

theorem forward_series_inr (G H : TwoTerminal) {x y : H} (h : Forward H.depth x y) :
    Forward (G.series H).depth (Series.inr G H x) (Series.inr G H y) := by
  simpa only [Forward, depth_series_inr, (Series.inr_isometry G H).dist_eq,
    add_sub_add_left_eq_sub] using! h

@[simp] theorem depth_parallel_inl (G : TwoTerminal) (x : G) :
    G.parallel.depth (Parallel.inl G x) = G.depth x :=
  (Parallel.inl_isometry G).dist_eq _ _

@[simp] theorem depth_parallel_inr (G : TwoTerminal) (x : G) :
    G.parallel.depth (Parallel.inr G x) = G.depth x := by
  change dist (Parallel.inl G G.source) (Parallel.inr G x) = _
  rw [Parallel.joint_source, (Parallel.inr_isometry G).dist_eq, depth]

theorem forward_parallel_inl (G : TwoTerminal) {x y : G} (h : Forward G.depth x y) :
    Forward G.parallel.depth (Parallel.inl G x) (Parallel.inl G y) := by
  simpa only [Forward, depth_parallel_inl, (Parallel.inl_isometry G).dist_eq] using! h

theorem forward_parallel_inr (G : TwoTerminal) {x y : G} (h : Forward G.depth x y) :
    Forward G.parallel.depth (Parallel.inr G x) (Parallel.inr G y) := by
  simpa only [Forward, depth_parallel_inr, (Parallel.inr_isometry G).dist_eq] using! h

theorem forward_scale (G : TwoTerminal) (c : ℝ) (hc : 0 < c) {x y : G}
    (h : Forward G.depth x y) :
    Forward (G.scale c hc).depth (⟨x⟩ : ScaledPoint G c) (⟨y⟩ : ScaledPoint G c) := by
  change c * dist x y = c * G.depth y - c * G.depth x
  exact (congrArg (c * ·) h).trans (mul_sub c (G.depth y) (G.depth x))

theorem forward_initialEmbedding (initial G : TwoTerminal) (n : ℕ) {x y : initial}
    (h : Forward initial.depth x y) :
    Forward (appendCopies initial G n).depth
      (initialEmbedding initial G n x) (initialEmbedding initial G n y) := by
  induction n with
  | zero => exact h
  | succ n ih => exact forward_series_inl _ _ ih



@[simp] theorem depth_initialEmbedding (initial G : TwoTerminal) (n : ℕ) (x : initial) :
    (appendCopies initial G n).depth (initialEmbedding initial G n x) = initial.depth x := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [initialEmbedding, Function.comp_apply, appendCopies, depth_series_inl] using! ih

end ConvexBodyChasing.TwoTerminal

end
end BundledModule020

/- Component source: ConvexBodyChasing.CopyCoordinates -/
section BundledModule021
/-! # Exact coordinate restrictions on recursive copies -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing

theorem FiniteGame.map_map {U V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : U → V) (g : V → W) (game : FiniteGame U) :
    (game.map f).map g = game.map (g ∘ f) := by
  induction game <;> simp [FiniteGame.map, *, Finset.image_image, Function.comp_def]

theorem Call.map_map {U V W : Type*} [DecidableEq V] [DecidableEq W]
    (f : U → V) (g : V → W) (C : Call U) : (C.map f).map g = C.map (g ∘ f) := by
  cases C
  simp only [Call.map, FiniteGame.map_map, Function.comp_apply]

namespace TwoTerminal
local instance copyCoordinatesDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

@[simp] theorem AnchoredFunction.appendCopies_initial {initial G : TwoTerminal}
    (f : AnchoredFunction initial) (g : AnchoredFunction G) (n : ℕ) (x : initial) :
    f.appendCopies g n (initialEmbedding initial G n x) = f x := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [AnchoredFunction.appendCopies, initialEmbedding,
      Function.comp_apply, AnchoredFunction.series_inl] using! ih

/-- Every listed call is the image of a single copy, with the depth translated
and every reused anchored coordinate restricted exactly to that copy. -/
theorem copyCalls_restriction (initial G : TwoTerminal) (g : FiniteGame G) (n : ℕ)
    (C : Call (appendCopies initial G n)) (hC : C ∈ copyCalls initial G g n) :
    ∃ ι : G → appendCopies initial G n,
      Isometry ι ∧ C = (⟨G.source, G.target, g⟩ : Call G).map ι ∧
      (∀ x, (appendCopies initial G n).depth (ι x) =
        (appendCopies initial G n).depth (ι G.source) + G.depth x) ∧
      (∀ (f : AnchoredFunction initial) (h : AnchoredFunction G) x,
        f.appendCopies h n (ι x) = h x) := by
  induction n with
  | zero => simp only [copyCalls, List.not_mem_nil] at hC
  | succ n ih =>
    simp only [copyCalls, List.mem_append, List.mem_map, List.mem_singleton] at hC
    rcases hC with ⟨D, hD, rfl⟩ | rfl
    · obtain ⟨ι, hι, rfl, hdepth, hcoord⟩ := ih D hD
      refine ⟨Series.inl (appendCopies initial G n) G ∘ ι,
        (Series.inl_isometry _ _).comp hι, Call.map_map _ _ _, ?_, ?_⟩
      · simpa only [appendCopies, Function.comp_apply, depth_series_inl] using! hdepth
      · exact hcoord
    · refine ⟨Series.inr (appendCopies initial G n) G, Series.inr_isometry _ _, rfl, ?_,
        fun _ _ _ => rfl⟩
      simp only [appendCopies, depth_series_inr,
        show G.depth G.source = 0 from dist_self _, add_zero, implies_true]

theorem copyCalls_endpoints {initial G : TwoTerminal} {g : FiniteGame G} {n : ℕ}
    {C : Call (appendCopies initial G n)} (hC : C ∈ copyCalls initial G g n)
    (f : AnchoredFunction initial) (h : AnchoredFunction G) :
    f.appendCopies h n C.source = 0 ∧ f.appendCopies h n C.target = 0 := by
  obtain ⟨ι, _, rfl, _, hcoord⟩ := copyCalls_restriction initial G g n C hC
  exact ⟨(hcoord f h G.source).trans h.source_zero, (hcoord f h G.target).trans h.target_zero⟩

end TwoTerminal
end ConvexBodyChasing

end
end BundledModule021

/- Component source: ConvexBodyChasing.CoordinateTests -/
section BundledModule022
/-! # Coordinate tests on two requests

A bounded affine representation of every scalar Lipschitz test controls
Bellman potential differences between barycentric distributions. The anchor
form is preserved when a higher-level waiting vertex is added.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
namespace ConvexBodyChasing

structure CoordinateTest {V I : Type*} [DecidableEq V] [Fintype I]
    (height : V → ℝ) (coords : V → I → ℝ) (S T : Finset V) (f : V → ℝ) where
  anchor : V
  anchor_mem : anchor ∈ S ∪ T
  depthCoeff : ℝ
  depthCoeff_bound : |depthCoeff| ≤ 1
  coeff : I → ℝ
  coeff_bound : ∀ i, |coeff i| ≤ 8
  equation : ∀ v ∈ S ∪ T, f v = f anchor + depthCoeff * (height v - height anchor) +
    ∑ i, coeff i * coords v i

def HasCoordinateTests {V I : Type*} [MetricSpace V] [DecidableEq V] [Fintype I]
    (height : V → ℝ) (coords : V → I → ℝ) (S T : Finset V) : Prop :=
  ∀ f : V → ℝ, LipschitzWith 1 f → Nonempty (CoordinateTest height coords S T f)

namespace CoordinateTest
variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V]

def fullCoords (height : V → ℝ) (coords : V → I → ℝ) (v : V) : Option I → ℝ
  | none => height v
  | some i => coords v i

theorem abs_pairing_le {height : V → ℝ} {coords : V → I → ℝ} {S T : Finset V}
    {f : V → ℝ} (h : CoordinateTest height coords S T f) (μ : V → ℝ)
    (hμ : ∑ v, μ v = 0) (hsupp : ∀ v, μ v ≠ 0 → v ∈ S ∪ T) :
    |SignedMass.pairing μ f| ≤ 8 * ∑ i, |SignedMass.pairing μ (fun v => fullCoords height coords v i)| := by
  apply SignedMass.abs_pairing_le_of_representation μ f hμ (fullCoords height coords)
    (fun i => match i with | none => h.depthCoeff | some j => h.coeff j)
    (f h.anchor - h.depthCoeff * height h.anchor) 8
  · rintro (_ | i)
    · exact h.depthCoeff_bound.trans (by norm_num)
    · exact h.coeff_bound i
  · intro v hv
    rw [Fintype.sum_option, fullCoords, h.equation v (hsupp v hv)]
    simp only [fullCoords]
    ring

end CoordinateTest

namespace HasCoordinateTests
variable {V I : Type*} [MetricSpace V] [DecidableEq V] [Fintype I]

theorem singleton (height : V → ℝ) (coords : V → I → ℝ) (v : V) :
    HasCoordinateTests height coords {v} {v} := by
  intro f _
  refine ⟨⟨v, by simp, 0, by norm_num, fun _ => 0, fun _ => by norm_num, ?_⟩⟩
  intro w hw
  have hw' : w = v := by simpa only [Finset.union_self, Finset.mem_singleton] using! hw
  simp only [hw', sub_self, zero_mul, Finset.sum_const_zero, add_zero]



theorem of_forward (height : V → ℝ) (coords : V → I → ℝ) (u v : V)
    (hforward : dist u v = height v - height u) : HasCoordinateTests height coords {u} {v} := by
  by_cases huv : u = v
  · subst v
    exact singleton height coords u
  · intro f hf
    have hd : 0 < dist u v := dist_pos.mpr huv
    have hdiff : |f v - f u| ≤ dist u v := by
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul, abs_sub_comm] using! hf.dist_le_mul u v
    refine ⟨⟨u, by simp, (f v - f u) / dist u v, ?_, fun _ => 0, fun _ => by norm_num, ?_⟩⟩
    · simpa only [abs_div, abs_of_pos hd] using! (div_le_one hd).mpr hdiff
    · intro w hw
      rcases (show w = u ∨ w = v by simpa only [Finset.mem_union, Finset.mem_singleton] using! hw) with rfl | rfl
      · simp
      · rw [← hforward, div_mul_cancel₀ _ hd.ne']
        simp

end HasCoordinateTests
end ConvexBodyChasing

end
end BundledModule022

/- Component source: ConvexBodyChasing.TestEmbedding -/
section BundledModule023
/-! # Transferring coordinate tests through scaled copy embeddings -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
namespace ConvexBodyChasing
variable {V W I : Type*} [MetricSpace V] [MetricSpace W]
  [DecidableEq V] [DecidableEq W] [Fintype I]

omit [DecidableEq V] [DecidableEq W] in
theorem lipschitz_pullback_scaled (ι : V → W) {scale : ℝ} (hscale : 0 < scale)
    (hdist : ∀ x y, dist (ι x) (ι y) = scale * dist x y)
    {f : W → ℝ} (hf : LipschitzWith 1 f) :
    LipschitzWith 1 (fun x => f (ι x) / scale) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, ← sub_div, abs_div, abs_of_pos hscale, NNReal.coe_one, one_mul, div_le_iff₀ hscale]
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul, mul_one, hdist, mul_comm] using! hf.dist_le_mul (ι x) (ι y)

theorem HasCoordinateTests.map_scaled {height : V → ℝ} {coords : V → I → ℝ}
    {S T : Finset V} (h : HasCoordinateTests height coords S T)
    (ι : V → W) {scale : ℝ} (hscale : 0 < scale)
    (hdist : ∀ x y, dist (ι x) (ι y) = scale * dist x y)
    (newHeight : W → ℝ) (newCoords : W → I → ℝ) (offset : ℝ)
    (hheight : ∀ x, newHeight (ι x) = offset + scale * height x)
    (hcoords : ∀ x i, newCoords (ι x) i = scale * coords x i) :
    HasCoordinateTests newHeight newCoords (S.image ι) (T.image ι) := by
  intro f hf
  obtain ⟨test⟩ := h _ (lipschitz_pullback_scaled ι hscale hdist hf)
  refine ⟨⟨ι test.anchor, ?_, test.depthCoeff, test.depthCoeff_bound,
    test.coeff, test.coeff_bound, ?_⟩⟩
  · rw [← Finset.image_union]
    exact Finset.mem_image_of_mem ι test.anchor_mem
  · intro w hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (show w ∈ (S ∪ T).image ι by
      simpa only [Finset.image_union] using! hw)
    have heq := congrArg (scale * ·) (test.equation x hx)
    simp only [mul_add, mul_div_cancel₀ _ hscale.ne'] at heq
    simp_rw [hheight, hcoords]
    rw [heq, Finset.mul_sum]
    ring_nf

end ConvexBodyChasing

end
end BundledModule023

/- Component source: ConvexBodyChasing.WaitingTests -/
section BundledModule024
/-! # Adding an isolated waiting-vertex coordinate -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
namespace ConvexBodyChasing
namespace CoordinateTest
variable {V I : Type*} [Fintype I]

def extendCoeffs (a : I → ℝ) (side : Bool) (c : ℝ) : Bool ⊕ I → ℝ :=
  Sum.elim (fun b => if b = side then c else 0) a

theorem sum_extendCoeffs (a : I → ℝ) (side : Bool) (c : ℝ) (coords : Bool ⊕ I → ℝ) :
    ∑ j, extendCoeffs a side c j * coords j =
      c * coords (.inl side) + ∑ i, a i * coords (.inr i) := by
  rw [Fintype.sum_sum_type]
  cases side <;> simp [extendCoeffs]

omit [Fintype I] in
theorem extendCoeffs_bound {a : I → ℝ} {c : ℝ} (ha : ∀ i, |a i| ≤ 8) (hc : |c| ≤ 8)
    (side : Bool) : ∀ j, |extendCoeffs a side c j| ≤ 8 := by
  rintro (b | i)
  · by_cases hb : b = side <;> simp [extendCoeffs, hb, hc]
  · exact ha i

end CoordinateTest

theorem anchored_difference_le {V : Type*} [MetricSpace V] {f height : V → ℝ}
    (hf : LipschitzWith 1 f) (hh : LipschitzWith 1 height) {a : ℝ} (ha : |a| ≤ 1)
    (x z : V) : |f z - f x - a * (height z - height x)| ≤ 2 * dist z x := by
  have hdf : |f z - f x| ≤ dist z x := by simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using! hf.dist_le_mul z x
  have hdh : |height z - height x| ≤ dist z x := by simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using! hh.dist_le_mul z x
  calc
    _ ≤ |f z - f x| + |a| * |height z - height x| := by
      simpa only [abs_mul] using! abs_sub (f z - f x) (a * (height z - height x))
    _ ≤ dist z x + 1 * dist z x := add_le_add hdf (mul_le_mul ha hdh (abs_nonneg _) zero_le_one)
    _ = 2 * dist z x := by ring

namespace HasCoordinateTests
variable {V I : Type*} [MetricSpace V] [DecidableEq V] [Fintype I]

theorem extend {height : V → ℝ} {coords : V → Bool ⊕ I → ℝ} {S T : Finset V}
    (h : HasCoordinateTests height (fun v i => coords v (.inr i)) S T) :
    HasCoordinateTests height coords S T := by
  intro f hf
  obtain ⟨test⟩ := h f hf
  refine ⟨⟨test.anchor, test.anchor_mem, test.depthCoeff, test.depthCoeff_bound,
    CoordinateTest.extendCoeffs test.coeff false 0,
    CoordinateTest.extendCoeffs_bound test.coeff_bound (by norm_num) false, ?_⟩⟩
  intro v hv
  simpa only [CoordinateTest.sum_extendCoeffs, zero_mul, zero_add] using! test.equation v hv

theorem withWaiting {height : V → ℝ} {coords : V → Bool ⊕ I → ℝ} {S T : Finset V}
    (h : HasCoordinateTests height (fun v i => coords v (.inr i)) S T)
    (hh : LipschitzWith 1 height) (z : V) (side : Bool)
    (hq : 0 < coords z (.inl side))
    (hzero : ∀ v ∈ S ∪ T, coords v (.inl side) = 0)
    (hz : ∀ i, coords z (.inr i) = 0)
    (hclose : ∀ v ∈ S ∪ T, dist z v ≤ 4 * coords z (.inl side)) :
    HasCoordinateTests height coords (insert z S) (insert z T) := by
  intro f hf
  obtain ⟨test⟩ := h f hf
  let c := (f z - f test.anchor - test.depthCoeff * (height z - height test.anchor)) / coords z (.inl side)
  have hc : |c| ≤ 8 := by
    rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]
    linarith [anchored_difference_le hf hh test.depthCoeff_bound test.anchor z,
      hclose test.anchor test.anchor_mem]
  refine ⟨⟨test.anchor, ?_, test.depthCoeff, test.depthCoeff_bound,
    CoordinateTest.extendCoeffs test.coeff side c,
    CoordinateTest.extendCoeffs_bound test.coeff_bound hc side, ?_⟩⟩
  · simpa only [Finset.insert_union, Finset.union_insert, Finset.insert_idem] using!
      (show test.anchor ∈ insert z (S ∪ T) from Finset.mem_insert_of_mem test.anchor_mem)
  · intro v hv
    rw [CoordinateTest.sum_extendCoeffs]
    rcases (show v = z ∨ v ∈ S ∪ T by
      simpa only [Finset.insert_union, Finset.union_insert, Finset.insert_idem, Finset.mem_insert] using! hv)
      with heq | hv
    · rw [heq]
      simp only [c, hz, mul_zero, Finset.sum_const_zero, add_zero, div_mul_cancel₀ _ hq.ne']
      ring
    · simpa only [hzero v hv, mul_zero, zero_add] using! test.equation v hv

end HasCoordinateTests
end ConvexBodyChasing

end
end BundledModule024

/- Component source: ConvexBodyChasing.TransitionTests -/
section BundledModule025
/-! # Coordinate tests at every decision of a game -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing
namespace FiniteGame
variable {V W I : Type*} [MetricSpace V] [MetricSpace W]
  [DecidableEq V] [DecidableEq W] [Fintype I]

theorem TransitionChain.map_tests {height : V → ℝ} {coords : V → I → ℝ}
    {game : FiniteGame V} {S T : Finset V}
    (h : TransitionChain (HasCoordinateTests height coords) game S T)
    (ι : V → W) {scale : ℝ} (hscale : 0 < scale)
    (hdist : ∀ x y, dist (ι x) (ι y) = scale * dist x y)
    (newHeight : W → ℝ) (newCoords : W → I → ℝ) (offset : ℝ)
    (hheight : ∀ x, newHeight (ι x) = offset + scale * height x)
    (hcoords : ∀ x i, newCoords (ι x) i = scale * coords x i) :
    TransitionChain (HasCoordinateTests newHeight newCoords)
      (game.map ι) (S.image ι) (T.image ι) := by
  exact h.map ι (fun _ _ h => h.map_scaled ι hscale hdist newHeight newCoords offset hheight hcoords)

omit [MetricSpace W] [DecidableEq W] in
theorem TransitionChain.waiting_tests {height : V → ℝ} {coords : V → Bool ⊕ I → ℝ}
    {game : FiniteGame V} {S T : Finset V}
    (h : TransitionChain (HasCoordinateTests height (fun v i => coords v (.inr i))) game S T)
    (hh : LipschitzWith 1 height) {A : Set V}
    (hgame : Supported A game) (hS : (↑S : Set V) ⊆ A) (z : V) (side : Bool)
    (hq : 0 < coords z (.inl side)) (hzero : ∀ v ∈ A, coords v (.inl side) = 0)
    (hz : ∀ i, coords z (.inr i) = 0)
    (hclose : ∀ v ∈ A, dist z v ≤ 4 * coords z (.inl side)) :
    TransitionChain (HasCoordinateTests height coords)
      (game.withWaiting z) (insert z S) (insert z T) := by
  exact (h.supported hgame hS).withWaiting z (fun _ _ h => h.1.withWaiting hh z side hq
    (fun v hv => hzero v (h.2 hv)) hz (fun v hv => hclose v (h.2 hv)))

end FiniteGame
end ConvexBodyChasing

end
end BundledModule025

/- Component source: ConvexBodyChasing.ParallelTests -/
section BundledModule026
/-! # Tests on one branch with a waiting vertex on the other -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing.TwoTerminal
namespace Parallel

def embed (G : TwoTerminal) (side : Bool) : G → G.parallel :=
  if side then inl G else inr G

theorem embed_isometry (G : TwoTerminal) (side : Bool) : Isometry (embed G side) := by
  cases side with
  | false => exact inr_isometry G
  | true => exact inl_isometry G

@[simp] theorem depth_embed (G : TwoTerminal) (side : Bool) (x : G) :
    G.parallel.depth (embed G side x) = G.depth x := by
  cases side with
  | false => exact depth_parallel_inr G x
  | true => exact depth_parallel_inl G x



@[simp] theorem embed_target (G : TwoTerminal) (side : Bool) :
    embed G side G.target = G.parallel.target := by
  cases side with
  | false => exact (joint_target G).symm
  | true => rfl

end Parallel

@[simp] theorem tent_parallel_embed (G : TwoTerminal) (side : Bool) (x : G) :
    G.parallel.tent (Parallel.embed G side x) = G.tent x := by
  simp only [tent_eq, Parallel.depth_embed, length_parallel]

def parallelCoordinate {I : Type*} {G : TwoTerminal} (coords : I → AnchoredFunction G) :
    Bool ⊕ I → AnchoredFunction G.parallel :=
  Sum.elim (fun side => if side then (AnchoredFunction.tent G).parallel (AnchoredFunction.zero G)
    else (AnchoredFunction.zero G).parallel (AnchoredFunction.tent G))
    (fun i => (coords i).parallel (coords i))

@[simp] theorem parallelCoordinate_lower {I : Type*} {G : TwoTerminal}
    (coords : I → AnchoredFunction G) (side : Bool) (x : G) (i : I) :
    parallelCoordinate coords (.inr i) (Parallel.embed G side x) = coords i x := by
  cases side <;> rfl

@[simp] theorem parallelCoordinate_top {I : Type*} {G : TwoTerminal}
    (coords : I → AnchoredFunction G) (side slot : Bool) (x : G) :
    parallelCoordinate coords (.inl slot) (Parallel.embed G side x) =
      if slot = side then G.tent x else 0 := by
  cases side <;> cases slot <;> rfl

theorem parallel_lower_tests {I : Type*} [Fintype I] {G : TwoTerminal}
    [DecidableEq G] [DecidableEq G.parallel] (coords : I → AnchoredFunction G)
    {game : FiniteGame G} {S T : Finset G}
    (h : FiniteGame.TransitionChain (HasCoordinateTests G.depth (fun x i => coords i x)) game S T)
    (side : Bool) :
    FiniteGame.TransitionChain
      (HasCoordinateTests G.parallel.depth (fun x i => parallelCoordinate coords (.inr i) x))
      (game.map (Parallel.embed G side)) (S.image (Parallel.embed G side))
      (T.image (Parallel.embed G side)) := by
  exact h.map_tests (Parallel.embed G side) (scale := 1) zero_lt_one
    (fun x y => by simp only [(Parallel.embed_isometry G side).dist_eq, one_mul])
    _ _ 0 (fun x => by simp only [Parallel.depth_embed, one_mul, zero_add])
    (fun x i => by simp only [parallelCoordinate_lower, one_mul])

theorem parallel_waiting_tests {I : Type*} [Fintype I] {G : TwoTerminal}
    [DecidableEq G] [DecidableEq G.parallel] (coords : I → AnchoredFunction G)
    {game : FiniteGame G} {S T : Finset G}
    (h : FiniteGame.TransitionChain (HasCoordinateTests G.depth (fun x i => coords i x)) game S T)
    {A : Set G} (hgame : FiniteGame.Supported A game) (hS : (↑S : Set G) ⊆ A)
    (side : Bool) (z : G) (hq : 0 < G.tent z) (hz : ∀ i, coords i z = 0)
    (hclose : ∀ x ∈ A,
      dist (Parallel.embed G (!side) z) (Parallel.embed G side x) ≤ 4 * G.tent z) :
    FiniteGame.TransitionChain
      (HasCoordinateTests G.parallel.depth (fun x j => parallelCoordinate coords j x))
      ((game.map (Parallel.embed G side)).withWaiting (Parallel.embed G (!side) z))
      (insert (Parallel.embed G (!side) z) (S.image (Parallel.embed G side)))
      (insert (Parallel.embed G (!side) z) (T.image (Parallel.embed G side))) := by
  apply (parallel_lower_tests coords h side).waiting_tests G.parallel.depth_lipschitz
    (hgame.map (Parallel.embed G side))
    (by simpa only [Finset.coe_image] using! Set.image_mono (f := Parallel.embed G side) hS)
    (Parallel.embed G (!side) z) (!side)
  · simpa only [parallelCoordinate_top, ↓reduceIte] using! hq
  · rintro _ ⟨x, hx, rfl⟩
    cases side <;> rfl
  · simpa only [parallelCoordinate_lower] using! hz
  · simpa only [Set.forall_mem_image, parallelCoordinate_top, ↓reduceIte] using! hclose

/-- The short-copy phase controls the waiting distance by its branch coordinate. -/
theorem stage1_parallel_close (G : TwoTerminal) (side other : Bool) (z x : G) {m b δ : ℝ}
    (hL : G.length = 3 * m + b) (hb : b ≤ m) (hδ : δ ≤ b)
    (hz₀ : b ≤ G.depth z) (hz₁ : G.depth z ≤ b + m)
    (hx : G.depth x ≤ G.depth z + δ) :
    dist (Parallel.embed G other z) (Parallel.embed G side x) ≤ 4 * G.tent z := by
  have h3 : dist (Parallel.embed G other z) (Parallel.embed G side x) ≤ 3 * G.tent z := by
    simpa only [tent_parallel_embed] using! stage1_distance_bound G.parallel
      (Parallel.embed G other z) (Parallel.embed G side x) hL hb hδ
      (by simpa only [Parallel.depth_embed] using! hz₀)
      (by simpa only [Parallel.depth_embed] using! hz₁)
      (by simpa only [Parallel.depth_embed] using! hx)
  linarith [G.tent_nonneg z]

/-- The long-copy phase and branch removal use the same distance estimate. -/
theorem stage2_parallel_close (G : TwoTerminal) (side other : Bool) (z x : G) {m b : ℝ}
    (hL : G.length = 3 * m + b) (hb₀ : 0 ≤ b) (hb₁ : b ≤ m)
    (hz₀ : b + m ≤ G.depth z) (hz₁ : G.depth z ≤ b + 2 * m) :
    dist (Parallel.embed G other z) (Parallel.embed G side x) ≤ 4 * G.tent z := by
  simpa only [tent_parallel_embed] using! stage2_distance_bound G.parallel
    (Parallel.embed G other z) (Parallel.embed G side x) hL hb₀ hb₁
    (by simpa only [Parallel.depth_embed] using! hz₀)
    (by simpa only [Parallel.depth_embed] using! hz₁)

end ConvexBodyChasing.TwoTerminal

end
end BundledModule026

/- Component source: ConvexBodyChasing.EndpointTests -/
section BundledModule027
/-! # Coordinate tests for entering and removing a branch -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
namespace ConvexBodyChasing.TwoTerminal
local instance endpointTestsDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem parallel_removal_tests {I : Type*} [Fintype I] (G : TwoTerminal)
    (coords : I → AnchoredFunction G) (side : Bool) (x z : G)
    (hq : 0 < G.tent z)
    (hclose : dist (Parallel.embed G (!side) z) (Parallel.embed G side x) ≤ 4 * G.tent z) :
    HasCoordinateTests G.parallel.depth (fun v j => parallelCoordinate coords j v)
      (insert (Parallel.embed G (!side) z) {Parallel.embed G side x})
      {Parallel.embed G side x} := by
  intro f hf
  have hc : |(f (Parallel.embed G (!side) z) - f (Parallel.embed G side x)) / G.tent z| ≤ 8 := by
    rw [abs_div, abs_of_pos hq, div_le_iff₀ hq]
    calc
      _ ≤ dist (Parallel.embed G (!side) z) (Parallel.embed G side x) := by
        simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using!
          hf.dist_le_mul (Parallel.embed G (!side) z) (Parallel.embed G side x)
      _ ≤ 4 * G.tent z := hclose
      _ ≤ 8 * G.tent z := by linarith
  refine ⟨⟨Parallel.embed G side x, Finset.mem_union_right _ (Finset.mem_singleton_self _),
    0, by norm_num, CoordinateTest.extendCoeffs (fun _ : I => 0) (!side)
      ((f (Parallel.embed G (!side) z) - f (Parallel.embed G side x)) / G.tent z),
    CoordinateTest.extendCoeffs_bound (fun _ => by norm_num) hc (!side), ?_⟩⟩
  simp only [Finset.insert_union, Finset.union_self, Finset.mem_insert, Finset.mem_singleton,
    forall_eq_or_imp, forall_eq, CoordinateTest.sum_extendCoeffs, zero_mul,
    Finset.sum_const_zero, add_zero]
  cases side <;> simp [parallelCoordinate_top, div_mul_cancel₀ _ hq.ne']

theorem parallel_entrance_tests {I : Type*} [Fintype I] (G : TwoTerminal)
    (coords : I → AnchoredFunction G) (u : G) (hu : 0 < G.depth u)
    (ht : G.tent u = G.depth u) :
    HasCoordinateTests G.parallel.depth (fun v j => parallelCoordinate coords j v)
      {G.parallel.source} {Parallel.embed G true u, Parallel.embed G false u} := by
  intro f hf
  have hc (side : Bool) :
      |(f (Parallel.embed G side u) - f G.parallel.source) / G.depth u| ≤ 8 := by
    rw [abs_div, abs_of_pos hu, div_le_iff₀ hu]
    calc
      _ ≤ dist (Parallel.embed G side u) G.parallel.source := by
        simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using!
          hf.dist_le_mul (Parallel.embed G side u) G.parallel.source
      _ = G.depth u := (dist_comm ..).trans (Parallel.depth_embed G side u)
      _ ≤ 8 * G.depth u := by linarith
  refine ⟨⟨G.parallel.source, Finset.mem_union_left _ (Finset.mem_singleton_self _),
    0, by norm_num, Sum.elim (fun side =>
      (f (Parallel.embed G side u) - f G.parallel.source) / G.depth u) (fun _ : I => 0),
    Sum.rec hc (fun _ => by norm_num), ?_⟩⟩
  simp [Fintype.sum_sum_type, parallelCoordinate_top, ht,
    div_mul_cancel₀ _ hu.ne', AnchoredFunction.source_zero]

end ConvexBodyChasing.TwoTerminal

end
end BundledModule027

/- Component source: ConvexBodyChasing.Segments -/
section BundledModule028
/-! # Depth intervals of sequential recursive calls -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing
namespace Call
variable {V W : Type*}

/-- Calls form a connected chain of equal depth increments, and each request
stays in its own closed depth interval. -/
def Segments (height : V → ℝ) (length : ℝ) : List (Call V) → V → V → Prop
  | [], x, y => x = y
  | C :: rest, x, y => x = C.source ∧ height C.target = height x + length ∧
      FiniteGame.Supported {z | height x ≤ height z ∧ height z ≤ height x + length} C.game ∧
      Segments height length rest C.target y

theorem Segments.map [DecidableEq W] {height : V → ℝ} {length : ℝ}
    {calls : List (Call V)} {x y : V} (h : Segments height length calls x y)
    (f : V → W) (newHeight : W → ℝ) (offset : ℝ)
    (hf : ∀ z, newHeight (f z) = offset + height z) :
    Segments newHeight length (calls.map (Call.map f)) (f x) (f y) := by
  induction calls generalizing x with
  | nil => exact congrArg f h
  | cons C calls ih =>
    rcases h with ⟨rfl, htarget, hsupp, hrest⟩
    refine ⟨rfl, ?_, (hsupp.map f).mono ?_, ih hrest⟩
    · simp only [Call.map, hf, htarget, add_assoc]
    · rintro _ ⟨z, hz, rfl⟩
      simpa only [Set.mem_setOf_eq, hf, add_assoc, add_le_add_iff_left] using! hz

theorem Segments.append {height : V → ℝ} {length : ℝ} {left right : List (Call V)}
    {x middle y : V} (hleft : Segments height length left x middle)
    (hright : Segments height length right middle y) :
    Segments height length (left ++ right) x y := by
  induction left generalizing x with
  | nil => exact hleft ▸ hright
  | cons C left ih => exact ⟨hleft.1, hleft.2.1, hleft.2.2.1, ih hleft.2.2.2⟩

theorem Segments.height_target {height : V → ℝ} {length : ℝ} {calls : List (Call V)}
    {x y : V} (h : Segments height length calls x y) :
    height y = height x + calls.length * length := by
  induction calls generalizing x with
  | nil => simpa only [List.length_nil, Nat.cast_zero, zero_mul, add_zero] using! congrArg height h.symm
  | cons C calls ih =>
    rw [ih h.2.2.2, h.2.1, List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    ring

theorem Segments.height_le {height : V → ℝ} {length : ℝ} {calls : List (Call V)}
    {x y : V} (h : Segments height length calls x y) (hlength : 0 ≤ length) :
    height x ≤ height y := by
  rw [h.height_target]
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hlength)

theorem Segments.lastTarget {height : V → ℝ} {length : ℝ} {calls : List (Call V)}
    {x y : V} (h : Segments height length calls x y) : Requests.lastTarget x calls = y := by
  induction calls generalizing x with
  | nil => exact h
  | cons C calls ih => exact ih h.2.2.2

end Call

namespace TwoTerminal
local instance segmentsDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem supported_depth (G : TwoTerminal) (g : FiniteGame G) :
    FiniteGame.Supported {z | 0 ≤ G.depth z ∧ G.depth z ≤ G.length} g := by
  induction g with
  | stop => trivial
  | request S hS g ih => exact ⟨fun z _ => ⟨G.depth_nonneg z, G.depth_le_length z⟩, ih⟩
  | coin g h ihg ihh => exact ⟨ihg, ihh⟩

theorem game_segment (G : TwoTerminal) (g : FiniteGame G) :
    Call.Segments G.depth G.length [⟨G.source, G.target, g⟩] G.source G.target := by
  refine ⟨rfl, ?_, ?_, rfl⟩
  · simp only [depth, length, dist_self, zero_add]
  · simpa only [depth, dist_self, zero_add] using! supported_depth G g

theorem copyCalls_segments (initial G : TwoTerminal) (g : FiniteGame G) (n : ℕ) :
    Call.Segments (appendCopies initial G n).depth G.length (copyCalls initial G g n)
      (initialEmbedding initial G n initial.target) (appendCopies initial G n).target := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Call.Segments.append (ih.map (Series.inl _ G) _ 0 (fun z => by simp [appendCopies]))
    simpa only [List.map_cons, List.map_nil, Call.map, ← Series.joint] using!
      (game_segment G g).map (Series.inr (appendCopies initial G n) G) _
        (appendCopies initial G n).length (depth_series_inr _ G)

end TwoTerminal
end ConvexBodyChasing

end
end BundledModule028

/- Component source: ConvexBodyChasing.PhaseTransitions -/
section BundledModule029
/-! # Joining request transitions across phase boundaries -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing.Requests
variable {V : Type*} [DecidableEq V] {R : Finset V → Finset V → Prop}

omit [DecidableEq V] in
theorem sequence_transition {height : V → ℝ} {length : ℝ}
    {calls : List (Call V)} {x y : V} (hseg : Call.Segments height length calls x y)
    (hc : ∀ C ∈ calls, FiniteGame.TransitionChain R C.game {C.source} {C.target}) :
    FiniteGame.TransitionChain R (sequence calls) {x} {y} := by
  induction calls generalizing x with
  | nil => exact congrArg (fun x => ({x} : Finset V)) hseg
  | cons C calls ih =>
    rcases hseg with ⟨rfl, _, _, htail⟩
    exact (hc C (List.mem_cons_self ..)).append
      (ih htail (fun D hD => hc D (List.mem_cons_of_mem C hD)))

theorem finish_transition {left right : List (Call V)} {u v target : V}
    (hleft : FiniteGame.TransitionChain R (sequence left) {u} {target})
    (hright : FiniteGame.TransitionChain R (sequence right) {v} {target})
    (hremoveLeft : R {u, v} {u}) (hremoveRight : R {u, v} {v}) :
    FiniteGame.TransitionChain R (finish left right u v) {u, v} {target} := by
  by_cases hlen : right.length ≤ left.length
  · simpa only [finish, if_pos hlen, singleton, FiniteGame.TransitionChain] using!
      And.intro hremoveLeft hleft
  · simpa only [finish, if_neg hlen, singleton, FiniteGame.TransitionChain] using!
      And.intro hremoveRight hright

end ConvexBodyChasing.Requests

end
end BundledModule029

/- Component source: ConvexBodyChasing.InitialRequests -/
section BundledModule030
/-! # Initial requests of recursive calls -/

namespace ConvexBodyChasing
namespace FiniteGame

variable {V W : Type*}

def StartsWith (S : Finset V) (G : FiniteGame V) : Prop :=
  ∃ (hS : S.Nonempty) (next : FiniteGame V), G = request S hS next

theorem StartsWith.append {S : Finset V} {G : FiniteGame V}
    (h : StartsWith S G) (H : FiniteGame V) : StartsWith S (G.append H) := by
  rcases h with ⟨hS, next, rfl⟩
  exact ⟨hS, next.append H, rfl⟩

theorem StartsWith.map [DecidableEq W] {S : Finset V} {G : FiniteGame V}
    (h : StartsWith S G) (f : V → W) : StartsWith (S.image f) (G.map f) := by
  rcases h with ⟨hS, next, rfl⟩
  exact ⟨hS.image f, next.map f, rfl⟩

theorem StartsWith.withWaiting [DecidableEq V] {S : Finset V} {G : FiniteGame V}
    (h : StartsWith S G) (z : V) : StartsWith (insert z S) (G.withWaiting z) := by
  rcases h with ⟨hS, next, rfl⟩
  exact ⟨Finset.insert_nonempty _ _, next.withWaiting z, rfl⟩

end FiniteGame

theorem recursiveGame_starts (P : GraphParameters) (r : ℕ) :
    FiniteGame.StartsWith {(recursiveGraph P r).source} (recursiveGame P r) := by
  cases r with
  | zero => exact ⟨Finset.singleton_nonempty _, _, rfl⟩
  | succ r => exact ⟨Finset.singleton_nonempty _, _, rfl⟩

end ConvexBodyChasing

end BundledModule030

/- Component source: ConvexBodyChasing.WaitingLower -/
section BundledModule031
/-! # Charging a call and its waiting point

These Bellman inequalities apply before any random outcome in a call is known.
They will be used for alternating pairs and randomly selected branches.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing.FiniteGame

variable {V : Type*} [MetricSpace V]

theorem capEval_request_le_response (price : ℝ) (f : V → ℝ) (S : Finset V)
    (hS : S.Nonempty) (G : FiniteGame V) (x y : V) (hy : y ∈ S) :
    capEval price f (request S hS G) x ≤ dist x y + capEval price f G y :=
  (min_le_right _ _).trans (Finset.inf'_le _ hy)

theorem capEval_request_ge_of_mem (price a : ℝ) (f : V → ℝ) (S : Finset V)
    (hS : S.Nonempty) (G : FiniteGame V) (ha : a ≤ price)
    (h : ∀ y ∈ S, a ≤ capEval price f (request S hS G) y) :
    ∀ x, a ≤ capEval price f (request S hS G) x := by
  intro x
  refine le_min ha (Finset.le_inf' hS _ (fun y hy => ?_))
  have hy' : a ≤ capEval price f G y := by
    simpa only [dist_self, zero_add] using!
      (h y hy).trans (capEval_request_le_response price f S hS G y y hy)
  exact hy'.trans (le_add_of_nonneg_left dist_nonneg)

theorem capEval_ge_of_startsWith (price a : ℝ) (f : V → ℝ) {S : Finset V}
    {G : FiniteGame V} (hstart : StartsWith S G) (ha : a ≤ price)
    (h : ∀ y ∈ S, a ≤ capEval price f G y) : ∀ x, a ≤ capEval price f G x := by
  rcases hstart with ⟨hS, next, rfl⟩
  exact capEval_request_ge_of_mem price a f S hS next ha h

theorem capEval_withWaiting_at_wait_ge [DecidableEq V] (G : FiniteGame V) (A : Set V) (z : V)
    {a c price : ℝ} (ha : 0 ≤ a) (hprice : a + c ≤ price) {f : V → ℝ}
    (hf : ∀ x, c ≤ f x) (hz : a + c ≤ f z)
    (hsupport : Supported A G) (hsep : ∀ x ∈ A, a ≤ dist x z) :
    a + c ≤ capEval price f (G.withWaiting z) z := by
  induction G with
  | stop => exact hz
  | request S hS G ih =>
    refine le_min hprice (Finset.le_inf' _ _ (fun x hx => ?_))
    rcases Finset.mem_insert.mp hx with rfl | hx
    · simpa only [dist_self, zero_add] using! ih hsupport.2
    · exact add_le_add (by simpa only [dist_comm] using! hsep x (hsupport.1 hx))
        (capEval_ge_const _ ((le_add_of_nonneg_left ha).trans hprice) hf x)
  | coin G H ihG ihH =>
    simp only [withWaiting, capEval]
    linarith [ihG hsupport.1, ihH hsupport.2]

/-- A two-point initial request turns a charge at one endpoint into a truncated
distance charge measured from the other endpoint. -/
theorem capEval_pair_ge [DecidableEq V] (G : FiniteGame V) (u v : V)
    {a c price : ℝ} (hprice : a + c ≤ price) {f : V → ℝ}
    (hu : a + c ≤ capEval price f (request {u, v} (by simp) G) u)
    (hv : c ≤ capEval price f (request {u, v} (by simp) G) v) :
    ∀ x, c + min a (dist x v) ≤ capEval price f (request {u, v} (by simp) G) x := by
  intro x
  have hu' : a + c ≤ capEval price f G u := by
    simpa only [dist_self, zero_add] using!
      hu.trans (capEval_request_le_response price f _ _ G u u (by simp))
  have hv' : c ≤ capEval price f G v := by
    simpa only [dist_self, zero_add] using!
      hv.trans (capEval_request_le_response price f _ _ G v v (by simp))
  refine le_min (by linarith [min_le_left a (dist x v)]) (Finset.le_inf' _ _ (fun y hy => ?_))
  rcases (show y = u ∨ y = v by simpa only [Finset.mem_insert, Finset.mem_singleton] using! hy)
    with rfl | rfl
  · linarith [min_le_left a (dist x v), dist_nonneg (x := x) (y := y)]
  · linarith [min_le_right a (dist x y)]

theorem truncated_distance_sum_ge (u v x : V) {a : ℝ} (ha : 0 ≤ a)
    (huv : a ≤ dist u v) : a ≤ min a (dist x u) + min a (dist x v) := by
  by_cases hu : a ≤ dist x u
  · simpa only [min_eq_left hu] using! le_add_of_nonneg_right (le_min ha (dist_nonneg (x := x) (y := v)))
  · by_cases hv : a ≤ dist x v
    · simpa only [min_eq_left hv] using!
        le_add_of_nonneg_left (le_min ha (dist_nonneg (x := x) (y := u)))
    · simpa only [min_eq_right (le_of_not_ge hu), min_eq_right (le_of_not_ge hv),
        dist_comm u x] using! huv.trans (dist_triangle u x v)

theorem coin_pair_lower [DecidableEq V] (G H : FiniteGame V) (u v : V)
    {a cL cR price : ℝ} (ha : 0 ≤ a) (huv : a ≤ dist u v)
    (hpL : a + cL ≤ price) (hpR : a + cR ≤ price) (f : V → ℝ)
    (hLu : a + cL ≤ capEval price f (request {u, v} (by simp) G) u)
    (hLv : cL ≤ capEval price f (request {u, v} (by simp) G) v)
    (hRv : a + cR ≤ capEval price f (request {v, u} (by simp) H) v)
    (hRu : cR ≤ capEval price f (request {v, u} (by simp) H) u) :
    ∀ x, (a + cL + cR) / 2 ≤ capEval price f
      (.coin (request {u, v} (by simp) G) (request {v, u} (by simp) H)) x := by
  intro x
  rw [capEval]
  linarith [capEval_pair_ge G u v hpL hLu hLv x, capEval_pair_ge H v u hpR hRv hRu x,
    truncated_distance_sum_ge u v x ha huv]

theorem coin_startsPair_lower [DecidableEq V] (G H : FiniteGame V) (u v : V)
    (hG : StartsWith {u, v} G) (hH : StartsWith {v, u} H)
    {a cL cR price : ℝ} (ha : 0 ≤ a) (huv : a ≤ dist u v)
    (hpL : a + cL ≤ price) (hpR : a + cR ≤ price) (f : V → ℝ)
    (hLu : a + cL ≤ capEval price f G u) (hLv : cL ≤ capEval price f G v)
    (hRv : a + cR ≤ capEval price f H v) (hRu : cR ≤ capEval price f H u) :
    ∀ x, (a + cL + cR) / 2 ≤ capEval price f (.coin G H) x := by
  rcases hG with ⟨hS, G, rfl⟩
  rcases hH with ⟨hT, H, rfl⟩
  exact coin_pair_lower G H u v ha huv hpL hpR f hLu hLv hRv hRu

/-- One alternating pair charges at least one recursive-call lower bound,
uniformly over the state before the pair starts. -/
theorem alternating_pair_lower [DecidableEq V] (L R : FiniteGame V) (A B : Set V)
    (u v u' : V) {a p c price : ℝ} (ha : 0 ≤ a) (hap : a ≤ p)
    (hprice : p + c ≤ price) (f : V → ℝ) (hf : ∀ x, c ≤ f x)
    (hstart : StartsWith {u} L) (hL : Supported A L) (hR : Supported B R)
    (hu : u ∈ A) (hv : v ∈ B)
    (hsepL : ∀ x ∈ A, p ≤ dist x v) (hsepR : ∀ x ∈ B, p ≤ dist x u')
    (hcostL : a ≤ escapeEval p L u) (hcostR : a ≤ escapeEval p R v) :
    ∀ x, a + c ≤ capEval price f ((L.withWaiting v).append (R.withWaiting u')) x := by
  rw [capEval_append]
  have hbase : ∀ x, c ≤ capEval price f (R.withWaiting u') x :=
    capEval_ge_const _ ((le_add_of_nonneg_left (ha.trans hap)).trans hprice) hf
  have hRv : a + c ≤ capEval price f (R.withWaiting u') v :=
    (add_le_add hcostR le_rfl).trans
      (capEval_withWaiting_ge R B u' (ha.trans hap) hprice hf hR hsepR v hv)
  apply capEval_ge_of_startsWith price (a + c) _ (hstart.withWaiting v)
    ((add_le_add hap le_rfl).trans hprice)
  intro y hy
  rcases (show y = v ∨ y = u by simpa only [Finset.mem_insert, Finset.mem_singleton] using! hy)
    with hy | hy
  · rw [hy]
    exact capEval_withWaiting_at_wait_ge L A v ha ((add_le_add hap le_rfl).trans hprice)
      hbase hRv hL (fun x hx => hap.trans (hsepL x hx))
  · rw [hy]
    exact (add_le_add hcostL le_rfl).trans
      (capEval_withWaiting_ge L A v (ha.trans hap) hprice hbase hL hsepL u hu)

/-- One fair branch choice charges half a recursive-call lower bound in
expectation, together with the two corresponding continuation bounds. -/
theorem random_pair_lower [DecidableEq V] (L R HL HR : FiniteGame V) (A B : Set V)
    (u v : V) {a p cL cR price : ℝ} (ha : 0 ≤ a) (hap : a ≤ p)
    (hpL : p + cL ≤ price) (hpR : p + cR ≤ price) (f : V → ℝ)
    (hfL : ∀ x, cL ≤ capEval price f HL x) (hfR : ∀ x, cR ≤ capEval price f HR x)
    (hstartL : StartsWith {u} L) (hstartR : StartsWith {v} R)
    (hL : Supported A L) (hR : Supported B R) (hu : u ∈ A) (hv : v ∈ B)
    (hsepL : ∀ x ∈ A, p ≤ dist x v) (hsepR : ∀ x ∈ B, p ≤ dist x u)
    (hcostL : a ≤ escapeEval p L u) (hcostR : a ≤ escapeEval p R v) :
    ∀ x, (a + cL + cR) / 2 ≤ capEval price f
      (.coin ((L.withWaiting v).append HL) ((R.withWaiting u).append HR)) x := by
  apply coin_startsPair_lower _ _ u v
    (by simpa only [Finset.pair_comm] using! (hstartL.withWaiting v).append HL)
    (by simpa only [Finset.pair_comm] using! (hstartR.withWaiting u).append HR)
    ha (hap.trans (hsepL u hu)) ((add_le_add hap le_rfl).trans hpL)
    ((add_le_add hap le_rfl).trans hpR) f
  all_goals rw [capEval_append]
  · exact (add_le_add hcostL le_rfl).trans
      (capEval_withWaiting_ge L A v (ha.trans hap) hpL hfL hL hsepL u hu)
  · exact capEval_ge_const _ ((le_add_of_nonneg_left (ha.trans hap)).trans hpL) hfL v
  · exact (add_le_add hcostR le_rfl).trans
      (capEval_withWaiting_ge R B u (ha.trans hap) hpR hfR hR hsepR v hv)
  · exact capEval_ge_const _ ((le_add_of_nonneg_left (ha.trans hap)).trans hpR) hfR u

end ConvexBodyChasing.FiniteGame

end
end BundledModule031

/- Component source: ConvexBodyChasing.SequenceLower -/
section BundledModule032
/-! # Lower bounds for sequences of recursive calls -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing

namespace Call
variable {V : Type*} [MetricSpace V]

/-- A call starts at its designated source and has an escape-robust lower bound. -/
def EscapeBound (C : Call V) (amount price : ℝ) : Prop :=
  FiniteGame.StartsWith {C.source} C.game ∧
    amount ≤ FiniteGame.escapeEval price C.game C.source

theorem EscapeBound.all_starts {C : Call V} {amount price : ℝ}
    (h : C.EscapeBound amount price) (x : V) : amount ≤ FiniteGame.escapeEval price C.game x := by
  classical
  rcases h with ⟨⟨hS, next, hgame⟩, hcost⟩
  rw [hgame] at hcost ⊢
  exact hcost.trans (FiniteGame.escapeEval_singleton_ge C.source next price x)

theorem EscapeBound.map {W : Type*} [MetricSpace W] [DecidableEq W]
    {C : Call V} {amount price : ℝ} (h : C.EscapeBound amount price)
    (f : V → W) (hf : Isometry f) : (C.map f).EscapeBound amount price := by
  refine ⟨?_, ?_⟩
  · simpa only [Call.map, Finset.image_singleton] using! h.1.map f
  · simpa only [Call.map, FiniteGame.escapeEval_map f hf] using! h.2

theorem EscapeBound.map_scale {W : Type*} [MetricSpace W] [DecidableEq W]
    {C : Call V} {amount price scale : ℝ} (h : C.EscapeBound amount price)
    (f : V → W) (hscale : 0 ≤ scale)
    (hf : ∀ x y, dist (f x) (f y) = scale * dist x y) :
    (C.map f).EscapeBound (scale * amount) (scale * price) := by
  refine ⟨?_, ?_⟩
  · simpa only [Call.map, Finset.image_singleton] using! h.1.map f
  · simpa only [Call.map, FiniteGame.escapeEval_map_scale f hscale hf] using!
      mul_le_mul_of_nonneg_left h.2 hscale

end Call

namespace Requests
variable {V : Type*} [MetricSpace V]

theorem sequence_cap_lower (calls : List (Call V)) {a p c price : ℝ}
    (ha : 0 ≤ a) (hbudget : p + a * calls.length + c ≤ price)
    (hcall : ∀ C ∈ calls, C.EscapeBound a p) (f : V → ℝ) (hf : ∀ x, c ≤ f x) :
    ∀ x, a * calls.length + c ≤ FiniteGame.capEval price f (sequence calls) x := by
  induction calls with
  | nil => exact fun x => by simpa only [List.length_nil, Nat.cast_zero, mul_zero, zero_add] using! hf x
  | cons C calls ih =>
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, mul_add, mul_one] at hbudget ⊢
    have htail := ih (by linarith) (fun D hD => hcall D (List.mem_cons_of_mem C hD))
    intro x
    rw [sequence, FiniteGame.capEval_append]
    have h := FiniteGame.capEval_ge_escape_add C.game (p := p) (by linarith) htail x
    linarith [(hcall C (List.mem_cons_self ..)).all_starts x]

theorem singleton_cap_ge (G : FiniteGame V) (u : V) (f : V → ℝ) {c price : ℝ}
    (hprice : c ≤ price) (hu : c ≤ FiniteGame.capEval price f G u) :
    ∀ x, c ≤ FiniteGame.capEval price f (singleton u G) x := by
  intro x
  simp only [singleton, FiniteGame.capEval, Finset.inf'_singleton]
  exact le_min hprice (hu.trans (le_add_of_nonneg_left dist_nonneg))

/-- Stage 3 charges all calls remaining on the less advanced branch. -/
theorem finish_cap_lower (left right : List (Call V)) (u v : V) {a p c price : ℝ}
    (ha : 0 ≤ a) (hp : 0 ≤ p)
    (hbudget : p + a * max left.length right.length + c ≤ price)
    (hleft : ∀ C ∈ left, C.EscapeBound a p) (hright : ∀ C ∈ right, C.EscapeBound a p)
    (f : V → ℝ) (hf : ∀ x, c ≤ f x) :
    ∀ x, a * max left.length right.length + c ≤ FiniteGame.capEval price f (finish left right u v) x := by
  by_cases hlen : right.length ≤ left.length
  · simp only [finish, if_pos hlen, max_eq_left hlen] at hbudget ⊢
    exact singleton_cap_ge _ u f (by linarith) (sequence_cap_lower left ha hbudget hleft f hf u)
  · simp only [finish, if_neg hlen, max_eq_right (le_of_not_ge hlen)] at hbudget ⊢
    exact singleton_cap_ge _ v f (by linarith) (sequence_cap_lower right ha hbudget hright f hf v)

end Requests

end ConvexBodyChasing

end
end BundledModule032

/- Component source: ConvexBodyChasing.CopyLower -/
section BundledModule033
/-! # Escape lower bounds in the actual graph copies -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing.TwoTerminal
local instance copyLowerDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem copyCalls_escapeBound (initial G : TwoTerminal) (g : FiniteGame G)
    {amount price : ℝ} (hg : (⟨G.source, G.target, g⟩ : Call G).EscapeBound amount price)
    (n : ℕ) : ∀ C ∈ copyCalls initial G g n, C.EscapeBound amount price := by
  induction n with
  | zero => simp only [copyCalls, List.not_mem_nil, false_implies, implies_true]
  | succ n ih =>
    intro C hC
    simp only [copyCalls, List.mem_append, List.mem_map, List.mem_singleton] at hC
    rcases hC with ⟨D, hD, rfl⟩ | rfl
    · exact (ih D hD).map _ (Series.inl_isometry _ _)
    · exact hg.map _ (Series.inr_isometry _ _)

theorem normalizeGame_escapeBound (G : TwoTerminal) (g : FiniteGame G)
    (L : ℝ) (hL : 0 < L) {amount price : ℝ}
    (hg : (⟨G.source, G.target, g⟩ : Call G).EscapeBound (amount * G.length) (price * G.length)) :
    (⟨(G.normalize L hL).source, (G.normalize L hL).target, G.normalizeGame g L hL⟩ :
      Call (G.normalize L hL)).EscapeBound (amount * L) (price * L) := by
  convert! hg.map_scale (W := G.normalize L hL) (fun x => (⟨x⟩ : G.normalize L hL))
    (div_pos hL G.length_pos).le (fun _ _ => rfl) using 1
  all_goals field_simp [G.length_pos.ne']

end ConvexBodyChasing.TwoTerminal

end
end BundledModule033

/- Component source: ConvexBodyChasing.PhaseBounds -/
section BundledModule034
/-! # Iterating the three phase inequalities

The separation certificates in this module are explicit geometric obligations.
They are not hypotheses of the target convex-body-chasing theorem.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing

namespace Call
variable {V : Type*} [MetricSpace V]

/-- The source and all requests in a call are at least `p` from its waiting point. -/
def Separated (C : Call V) (z : V) (p : ℝ) : Prop :=
  ∃ A : Set V, FiniteGame.Supported A C.game ∧ C.source ∈ A ∧ ∀ x ∈ A, p ≤ dist x z

end Call

namespace Requests
variable {V : Type*} [MetricSpace V] [DecidableEq V]

/-- Expected call count charged by the random stage and the final surviving branch. -/
def randomCharge : ℕ → ℕ → ℕ → ℝ
  | 0, left, right => (max left right : ℕ)
  | n + 1, left, right =>
    (1 + randomCharge n (left - 1) right + randomCharge n left (right - 1)) / 2



theorem randomCharge_le (n left right : ℕ) : randomCharge n left right ≤ max left right + n := by
  induction n generalizing left right with
  | zero => simp only [randomCharge, Nat.cast_zero, add_zero, le_refl]
  | succ n ih =>
    have hL : ((max (left - 1) right : ℕ) : ℝ) ≤ max left right := by
      exact_mod_cast max_le_max (Nat.sub_le left 1) (le_refl right)
    have hR : ((max left (right - 1) : ℕ) : ℝ) ≤ max left right := by
      exact_mod_cast max_le_max (le_refl left) (Nat.sub_le right 1)
    simp only [randomCharge, Nat.cast_add, Nat.cast_one]
    linarith [ih (left - 1) right, ih left (right - 1)]

def AlternatingSafe (a p : ℝ) : List (Call V × Call V) → V → Prop
  | [], _ => True
  | (L, R) :: rest, waiting => L.EscapeBound a p ∧ R.EscapeBound a p ∧
      waiting = R.source ∧ L.Separated waiting p ∧ R.Separated L.target p ∧
      AlternatingSafe a p rest R.target

theorem alternating_cap_lower (pairs : List (Call V × Call V)) (waiting : V)
    {a p c price : ℝ} (ha : 0 ≤ a) (hap : a ≤ p)
    (hbudget : p + a * pairs.length + c ≤ price)
    (hsafe : AlternatingSafe a p pairs waiting) (next : FiniteGame V) (f : V → ℝ)
    (hnext : ∀ x, c ≤ FiniteGame.capEval price f next x) :
    ∀ x, a * pairs.length + c ≤ FiniteGame.capEval price f (alternating pairs waiting next) x := by
  induction pairs generalizing waiting with
  | nil => exact fun x => by simpa only [List.length_nil, Nat.cast_zero, mul_zero, zero_add] using! hnext x
  | cons pair pairs ih =>
    rcases pair with ⟨L, R⟩
    rcases hsafe with ⟨hL, hR, rfl, ⟨A, hA, hu, hsepL⟩, ⟨B, hB, hv, hsepR⟩, hrest⟩
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, mul_add, mul_one] at hbudget ⊢
    have htail := ih R.target (by linarith) hrest
    have h := FiniteGame.alternating_pair_lower L.game R.game A B L.source R.source L.target
      ha hap (by linarith) _ htail hL.1 hA hB hu hv hsepL hsepR hL.2 hR.2
    simpa only [alternating, FiniteGame.capEval_append, add_comm, add_left_comm, add_assoc] using! h

/-- Every branch that can be called during the random stage is separated from
the other branch's current waiting point. -/
def RandomSafe (a p : ℝ) : ℕ → List (Call V) → List (Call V) → V → V → Prop
  | 0, _, _, _, _ => True
  | n + 1, L :: left, R :: right, u, v =>
      u = L.source ∧ v = R.source ∧ L.Separated v p ∧ R.Separated u p ∧
      RandomSafe a p n left (R :: right) L.target v ∧
      RandomSafe a p n (L :: left) right u R.target
  | _ + 1, [], _, _, _ => False
  | _ + 1, _, [], _, _ => False

theorem randomStage_cap_lower (rounds : ℕ) (left right : List (Call V)) (u v : V)
    {a p c price : ℝ} (ha : 0 ≤ a) (hap : a ≤ p)
    (hbudget : p + a * ((max left.length right.length : ℕ) + rounds) + c ≤ price)
    (hsafe : RandomSafe a p rounds left right u v)
    (hleft : ∀ C ∈ left, C.EscapeBound a p) (hright : ∀ C ∈ right, C.EscapeBound a p)
    (f : V → ℝ) (hf : ∀ x, c ≤ f x) :
    ∀ x, a * randomCharge rounds left.length right.length + c ≤
      FiniteGame.capEval price f (randomStage rounds left right u v) x := by
  induction rounds generalizing left right u v with
  | zero =>
    simpa only [randomStage, randomCharge, Nat.cast_zero, add_zero, Nat.cast_max] using!
      finish_cap_lower left right u v ha (ha.trans hap)
        (by simpa only [Nat.cast_zero, add_zero, Nat.cast_max] using! hbudget) hleft hright f hf
  | succ rounds ih =>
    cases left with
    | nil => exact hsafe.elim
    | cons L left =>
      cases right with
      | nil => exact hsafe.elim
      | cons R right =>
        rcases hsafe with ⟨rfl, rfl, ⟨A, hA, hu, hsepL⟩, ⟨B, hB, hv, hsepR⟩, hsL, hsR⟩
        have hbL : p + a * ((max left.length (R :: right).length : ℕ) + rounds) + c ≤ price := by
          calc
            _ ≤ p + a * ((max (L :: left).length (R :: right).length : ℕ) + (rounds + 1)) + c := by
              gcongr <;> simp
            _ ≤ price := by simpa only [Nat.cast_add, Nat.cast_one] using! hbudget
        have hbR : p + a * ((max (L :: left).length right.length : ℕ) + rounds) + c ≤ price := by
          calc
            _ ≤ p + a * ((max (L :: left).length (R :: right).length : ℕ) + (rounds + 1)) + c := by
              gcongr <;> simp
            _ ≤ price := by simpa only [Nat.cast_add, Nat.cast_one] using! hbudget
        have hcontL := ih left (R :: right) L.target R.source hbL hsL
          (fun C hC => hleft C (List.mem_cons_of_mem L hC)) hright
        have hcontR := ih (L :: left) right L.source R.target hbR hsR hleft
          (fun C hC => hright C (List.mem_cons_of_mem R hC))
        have hpL : p + (a * randomCharge rounds left.length (R :: right).length + c) ≤ price := by
          nlinarith [mul_le_mul_of_nonneg_left (randomCharge_le rounds left.length (R :: right).length) ha]
        have hpR : p + (a * randomCharge rounds (L :: left).length right.length + c) ≤ price := by
          nlinarith [mul_le_mul_of_nonneg_left (randomCharge_le rounds (L :: left).length right.length) ha]
        have h := FiniteGame.random_pair_lower L.game R.game _ _ A B L.source R.source
          ha hap hpL hpR f hcontL hcontR
          (hleft L (List.mem_cons_self ..)).1 (hright R (List.mem_cons_self ..)).1
          hA hB hu hv hsepL hsepR
          (hleft L (List.mem_cons_self ..)).2 (hright R (List.mem_cons_self ..)).2
        intro x
        convert! h x using 1
        simp only [randomCharge, List.length_cons, Nat.add_sub_cancel]
        ring

end Requests
end ConvexBodyChasing

end
end BundledModule034

/- Component source: ConvexBodyChasing.Separation -/
section BundledModule035
/-! # Separation certificates from depth intervals -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing.TwoTerminal
local instance separationDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem separated_parallel_left (G : TwoTerminal) (C : Call G) (z : G)
    {lo hi p : ℝ}
    (hsupp : FiniteGame.Supported {x | lo ≤ G.depth x ∧ G.depth x ≤ hi} C.game)
    (hsource : lo ≤ G.depth C.source ∧ G.depth C.source ≤ hi)
    (hlo : p ≤ lo + G.depth z) (hhi : p ≤ 2 * G.length - hi - G.depth z) :
    (C.map (Parallel.inl G)).Separated (Parallel.inr G z) p := by
  refine ⟨Parallel.inl G '' {x | lo ≤ G.depth x ∧ G.depth x ≤ hi},
    hsupp.map _, ⟨C.source, hsource, rfl⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact Parallel.le_dist_inl_inr G x z (by linarith [hx.1]) (by linarith [hx.2])

theorem separated_parallel_right (G : TwoTerminal) (C : Call G) (z : G)
    {lo hi p : ℝ}
    (hsupp : FiniteGame.Supported {x | lo ≤ G.depth x ∧ G.depth x ≤ hi} C.game)
    (hsource : lo ≤ G.depth C.source ∧ G.depth C.source ≤ hi)
    (hlo : p ≤ lo + G.depth z) (hhi : p ≤ 2 * G.length - hi - G.depth z) :
    (C.map (Parallel.inr G)).Separated (Parallel.inl G z) p := by
  refine ⟨Parallel.inr G '' {x | lo ≤ G.depth x ∧ G.depth x ≤ hi},
    hsupp.map _, ⟨C.source, hsource, rfl⟩, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [dist_comm]
  exact Parallel.le_dist_inl_inr G z x (by linarith [hx.1]) (by linarith [hx.2])

theorem alternatingSafe_parallel (G : TwoTerminal) (calls : List (Call G))
    (u endpoint : G) {length amount price : ℝ} (hlength : 0 ≤ length)
    (hsegments : Call.Segments G.depth length calls u endpoint)
    (hcall : ∀ C ∈ calls, C.EscapeBound amount price)
    (hlo : price ≤ 2 * G.depth u)
    (hhi : price ≤ 2 * G.length - 2 * G.depth endpoint) :
    Requests.AlternatingSafe amount price
      ((calls.map (Call.map (Parallel.inl G))).zip (calls.map (Call.map (Parallel.inr G))))
      (Parallel.inr G u) := by
  induction calls generalizing u with
  | nil => trivial
  | cons C calls ih =>
    rcases hsegments with ⟨rfl, htarget, hsupp, hrest⟩
    have htail := hrest.height_le hlength
    refine ⟨(hcall C (List.mem_cons_self ..)).map _ (Parallel.inl_isometry G),
      (hcall C (List.mem_cons_self ..)).map _ (Parallel.inr_isometry G), rfl, ?_, ?_,
      ih C.target hrest (fun D hD => hcall D (List.mem_cons_of_mem C hD)) (by linarith)⟩
    · exact separated_parallel_left G C C.source hsupp ⟨le_rfl, by linarith⟩
        (by linarith) (by linarith)
    · exact separated_parallel_right G C C.target hsupp ⟨le_rfl, by linarith⟩
        (by linarith) (by linarith)

theorem segment_source_depth (G : TwoTerminal) (calls : List (Call G)) (u : G)
    (h : Call.Segments G.depth 1 calls u G.target) :
    G.depth u = G.length - calls.length := by
  have ht := h.height_target
  change G.length = G.depth u + calls.length * 1 at ht
  linarith

theorem segment_source_bounds (G : TwoTerminal) (calls : List (Call G)) (u : G)
    (m rounds : ℕ) (h : Call.Segments G.depth 1 calls u G.target)
    (hmin : m + rounds ≤ calls.length) (hmax : calls.length ≤ 2 * m) :
    G.length - 2 * m ≤ G.depth u ∧ G.depth u + rounds ≤ G.length - m := by
  have hmin' : (m : ℝ) + rounds ≤ calls.length := by exact_mod_cast hmin
  have hmax' : (calls.length : ℝ) ≤ 2 * m := by exact_mod_cast hmax
  rw [segment_source_depth G calls u h]
  constructor <;> linarith

theorem randomSafe_parallel (G : TwoTerminal) (m rounds : ℕ)
    (left right : List (Call G)) (u v : G) (amount price : ℝ)
    (hleft : Call.Segments G.depth 1 left u G.target)
    (hright : Call.Segments G.depth 1 right v G.target)
    (hleftMin : m + rounds ≤ left.length) (hrightMin : m + rounds ≤ right.length)
    (hleftMax : left.length ≤ 2 * m) (hrightMax : right.length ≤ 2 * m)
    (hlo : price ≤ 2 * (G.length - 2 * m)) (hhi : price ≤ 2 * m) :
    Requests.RandomSafe amount price rounds
      (left.map (Call.map (Parallel.inl G))) (right.map (Call.map (Parallel.inr G)))
      (Parallel.inl G u) (Parallel.inr G v) := by
  induction rounds generalizing left right u v with
  | zero => trivial
  | succ rounds ih =>
    have hLu := segment_source_bounds G left u m (rounds + 1) hleft hleftMin hleftMax
    have hRv := segment_source_bounds G right v m (rounds + 1) hright hrightMin hrightMax
    simp only [Nat.cast_add, Nat.cast_one] at hLu hRv
    cases left with
    | nil => simp only [List.length_nil] at hleftMin; omega
    | cons L left =>
      cases right with
      | nil => simp only [List.length_nil] at hrightMin; omega
      | cons R right =>
        rcases hleft with ⟨rfl, hLt, hLs, hLrest⟩
        rcases hright with ⟨rfl, hRt, hRs, hRrest⟩
        refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
        · exact separated_parallel_left G L R.source hLs ⟨le_rfl, by linarith⟩
            (by linarith [hLu.1, hRv.1]) (by linarith [hLu.2, hRv.2, Nat.cast_nonneg (α := ℝ) rounds])
        · exact separated_parallel_right G R L.source hRs ⟨le_rfl, by linarith⟩
            (by linarith [hLu.1, hRv.1]) (by linarith [hLu.2, hRv.2, Nat.cast_nonneg (α := ℝ) rounds])
        · exact ih left (R :: right) L.target R.source hLrest ⟨rfl, hRt, hRs, hRrest⟩
            (by simp only [List.length_cons] at hleftMin; omega) (by omega)
            (by simp only [List.length_cons] at hleftMax; omega) hrightMax
        · exact ih (L :: left) right L.source R.target ⟨rfl, hLt, hLs, hLrest⟩ hRrest
            (by omega) (by simp only [List.length_cons] at hrightMin; omega)
            hleftMax (by simp only [List.length_cons] at hrightMax; omega)

end ConvexBodyChasing.TwoTerminal

end
end BundledModule035

/- Component source: ConvexBodyChasing.ParallelPhaseTests -/
section BundledModule036
/-! # The coordinate-test invariant through the three phases -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing.TwoTerminal
local instance parallelPhaseTestsDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem parallel_sequence_tests {I : Type*} [Fintype I] (G : TwoTerminal)
    (coords : I → AnchoredFunction G) (side : Bool) (calls : List (Call G))
    {u endpoint : G} {length : ℝ} (hseg : Call.Segments G.depth length calls u endpoint)
    (hc : ∀ C ∈ calls, FiniteGame.TransitionChain
      (HasCoordinateTests G.depth (fun x i => coords i x)) C.game {C.source} {C.target}) :
    FiniteGame.TransitionChain
      (HasCoordinateTests G.parallel.depth (fun x j => parallelCoordinate coords j x))
      (Requests.sequence (calls.map (Call.map (Parallel.embed G side))))
      {Parallel.embed G side u} {Parallel.embed G side endpoint} := by
  apply Requests.sequence_transition
    (hseg.map (Parallel.embed G side) G.parallel.depth 0 (fun x => by simp))
  rintro _ hD
  obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hD
  simpa only [Finset.image_singleton, Call.map] using!
    (parallel_lower_tests coords (hc C hC) side).mono
      (fun _ _ h => h.extend (coords := fun x j => parallelCoordinate coords j x))

theorem parallel_finish_tests {I : Type*} [Fintype I] (G : TwoTerminal)
    (coords : I → AnchoredFunction G) (left right : List (Call G)) (u v : G)
    (hleft : Call.Segments G.depth 1 left u G.target)
    (hright : Call.Segments G.depth 1 right v G.target)
    (hcl : ∀ C ∈ left, FiniteGame.TransitionChain
      (HasCoordinateTests G.depth (fun x i => coords i x)) C.game {C.source} {C.target})
    (hcr : ∀ C ∈ right, FiniteGame.TransitionChain
      (HasCoordinateTests G.depth (fun x i => coords i x)) C.game {C.source} {C.target})
    (hqu : 0 < G.tent u) (hqv : 0 < G.tent v)
    (hdu : dist (Parallel.embed G true u) (Parallel.embed G false v) ≤ 4 * G.tent u)
    (hdv : dist (Parallel.embed G false v) (Parallel.embed G true u) ≤ 4 * G.tent v) :
    FiniteGame.TransitionChain
      (HasCoordinateTests G.parallel.depth (fun x j => parallelCoordinate coords j x))
      (Requests.finish (left.map (Call.map (Parallel.embed G true)))
        (right.map (Call.map (Parallel.embed G false)))
        (Parallel.embed G true u) (Parallel.embed G false v))
      {Parallel.embed G true u, Parallel.embed G false v} {G.parallel.target} := by
  apply Requests.finish_transition
  · simpa only [Parallel.embed_target] using! parallel_sequence_tests G coords true left hleft hcl
  · simpa only [Parallel.embed_target] using! parallel_sequence_tests G coords false right hright hcr
  · simpa only [Bool.not_true, Finset.pair_comm] using!
      parallel_removal_tests G coords true u v hqv hdv
  · exact parallel_removal_tests G coords false v u hqu hdu

theorem segment_stage2_bounds (G : TwoTerminal) (m : ℕ) {b : ℝ}
    (hG : G.length = 3 * m + b) (calls : List (Call G)) (u : G)
    (hseg : Call.Segments G.depth 1 calls u G.target)
    (hmin : m ≤ calls.length) (hmax : calls.length ≤ 2 * m) :
    b + m ≤ G.depth u ∧ G.depth u ≤ b + 2 * m := by
  have h := segment_source_bounds G calls u m 0 hseg (by omega) hmax
  constructor <;> linarith [h.1, h.2]

theorem tent_pos_of_depth (G : TwoTerminal) (x : G)
    (h₀ : 0 < G.depth x) (h₁ : G.depth x < G.length) : 0 < G.tent x := by
  simpa only [tent_eq] using! lt_min h₀ (sub_pos.mpr h₁)

theorem parallel_random_tests {I : Type*} [Fintype I] (G : TwoTerminal)
    (coords : I → AnchoredFunction G) (m rounds : ℕ) (b : ℝ)
    (hb₀ : 0 < b) (hb₁ : b ≤ m) (hG : G.length = 3 * m + b)
    (left right : List (Call G)) (u v : G)
    (hleft : Call.Segments G.depth 1 left u G.target)
    (hright : Call.Segments G.depth 1 right v G.target)
    (hleftMin : m + rounds ≤ left.length) (hrightMin : m + rounds ≤ right.length)
    (hleftMax : left.length ≤ 2 * m) (hrightMax : right.length ≤ 2 * m)
    (hcl : ∀ C ∈ left, FiniteGame.TransitionChain
      (HasCoordinateTests G.depth (fun x i => coords i x)) C.game {C.source} {C.target})
    (hcr : ∀ C ∈ right, FiniteGame.TransitionChain
      (HasCoordinateTests G.depth (fun x i => coords i x)) C.game {C.source} {C.target})
    (hzl : ∀ C ∈ left, ∀ i, coords i C.target = 0)
    (hzr : ∀ C ∈ right, ∀ i, coords i C.target = 0)
    (hzu : ∀ i, coords i u = 0) (hzv : ∀ i, coords i v = 0) :
    FiniteGame.TransitionChain
      (HasCoordinateTests G.parallel.depth (fun x j => parallelCoordinate coords j x))
      (Requests.randomStage rounds (left.map (Call.map (Parallel.embed G true)))
        (right.map (Call.map (Parallel.embed G false)))
        (Parallel.embed G true u) (Parallel.embed G false v))
      {Parallel.embed G true u, Parallel.embed G false v} {G.parallel.target} := by
  induction rounds generalizing left right u v
  all_goals have hLu := segment_stage2_bounds G m hG left u hleft (by omega) hleftMax
  all_goals have hRv := segment_stage2_bounds G m hG right v hright (by omega) hrightMax
  all_goals
    have hqu := tent_pos_of_depth G u (by linarith [hLu.1, Nat.cast_nonneg (α := ℝ) m])
      (by linarith [hLu.2])
  all_goals
    have hqv := tent_pos_of_depth G v (by linarith [hRv.1, Nat.cast_nonneg (α := ℝ) m])
      (by linarith [hRv.2])
  case succ rounds ih =>
    cases left with
    | nil => simp only [List.length_nil] at hleftMin; omega
    | cons L left =>
      cases right with
      | nil => simp only [List.length_nil] at hrightMin; omega
      | cons R right =>
        rcases hleft with ⟨rfl, hLt, hLs, hLrest⟩
        rcases hright with ⟨rfl, hRt, hRs, hRrest⟩
        have hwaitL : FiniteGame.TransitionChain
            (HasCoordinateTests G.parallel.depth (fun x j => parallelCoordinate coords j x))
            ((L.game.map (Parallel.embed G true)).withWaiting (Parallel.embed G false R.source))
            {Parallel.embed G true L.source, Parallel.embed G false R.source}
            {Parallel.embed G true L.target, Parallel.embed G false R.source} := by
          simpa only [Finset.image_singleton, Bool.not_true, Finset.pair_comm] using!
            parallel_waiting_tests coords (hcl L (List.mem_cons_self ..)) hLs (by simp)
              true R.source hqv hzv (fun x _ =>
                stage2_parallel_close G true false R.source x hG hb₀.le hb₁ hRv.1 hRv.2)
        have hwaitR : FiniteGame.TransitionChain
            (HasCoordinateTests G.parallel.depth (fun x j => parallelCoordinate coords j x))
            ((R.game.map (Parallel.embed G false)).withWaiting (Parallel.embed G true L.source))
            {Parallel.embed G true L.source, Parallel.embed G false R.source}
            {Parallel.embed G true L.source, Parallel.embed G false R.target} := by
          simpa only [Finset.image_singleton, Bool.not_false] using!
            parallel_waiting_tests coords (hcr R (List.mem_cons_self ..)) hRs (by simp)
              false L.source hqu hzu (fun x _ =>
                stage2_parallel_close G false true L.source x hG hb₀.le hb₁ hLu.1 hLu.2)
        have hnextL := ih left (R :: right) L.target R.source hLrest ⟨rfl, hRt, hRs, hRrest⟩
          (by simp only [List.length_cons] at hleftMin; omega) (by omega)
          (by simp only [List.length_cons] at hleftMax; omega) hrightMax
          (fun C hC => hcl C (List.mem_cons_of_mem L hC)) hcr
          (fun C hC => hzl C (List.mem_cons_of_mem L hC)) hzr
          (hzl L (List.mem_cons_self ..)) hzv
        have hnextR := ih (L :: left) right L.source R.target ⟨rfl, hLt, hLs, hLrest⟩ hRrest
          (by omega) (by simp only [List.length_cons] at hrightMin; omega)
          hleftMax (by simp only [List.length_cons] at hrightMax; omega)
          hcl (fun C hC => hcr C (List.mem_cons_of_mem R hC))
          hzl (fun C hC => hzr C (List.mem_cons_of_mem R hC))
          hzu (hzr R (List.mem_cons_self ..))
        exact ⟨hwaitL.append hnextL, hwaitR.append hnextR⟩
  case zero =>
    exact parallel_finish_tests G coords left right u v hleft hright hcl hcr hqu hqv
      (stage2_parallel_close G false true u v hG hb₀.le hb₁ hLu.1 hLu.2)
      (stage2_parallel_close G true false v u hG hb₀.le hb₁ hRv.1 hRv.2)

theorem parallel_alternating_tests {I : Type*} [Fintype I] (G : TwoTerminal)
    (coords : I → AnchoredFunction G) {m b δ : ℝ} (hm : 0 < m)
    (hb₀ : 0 < b) (hb₁ : b ≤ m) (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ b)
    (hG : G.length = 3 * m + b) (calls : List (Call G)) (u endpoint : G)
    (hseg : Call.Segments G.depth δ calls u endpoint)
    (hu : b ≤ G.depth u) (hend : G.depth endpoint ≤ b + m)
    (hc : ∀ C ∈ calls, FiniteGame.TransitionChain
      (HasCoordinateTests G.depth (fun x i => coords i x)) C.game {C.source} {C.target})
    (hz : ∀ C ∈ calls, ∀ i, coords i C.target = 0) (hzu : ∀ i, coords i u = 0)
    (next : FiniteGame G.parallel) (T : Finset G.parallel)
    (hnext : FiniteGame.TransitionChain
      (HasCoordinateTests G.parallel.depth (fun x j => parallelCoordinate coords j x)) next
      {Parallel.embed G true endpoint, Parallel.embed G false endpoint} T) :
    FiniteGame.TransitionChain
      (HasCoordinateTests G.parallel.depth (fun x j => parallelCoordinate coords j x))
      (Requests.alternating
        ((calls.map (Call.map (Parallel.embed G true))).zip
          (calls.map (Call.map (Parallel.embed G false)))) (Parallel.embed G false u) next)
      {Parallel.embed G true u, Parallel.embed G false u} T := by
  induction calls generalizing u with
  | nil => simpa only [Call.Segments] using! hseg ▸ hnext
  | cons C calls ih =>
    rcases hseg with ⟨rfl, ht, hs, hrest⟩
    have htail := hrest.height_le hδ₀
    have hqs := tent_pos_of_depth G C.source (by linarith) (by linarith)
    have hqt := tent_pos_of_depth G C.target (by linarith) (by linarith)
    have hwaitL : FiniteGame.TransitionChain
        (HasCoordinateTests G.parallel.depth (fun x j => parallelCoordinate coords j x))
        ((C.game.map (Parallel.embed G true)).withWaiting (Parallel.embed G false C.source))
        {Parallel.embed G true C.source, Parallel.embed G false C.source}
        {Parallel.embed G true C.target, Parallel.embed G false C.source} := by
      simpa only [Finset.image_singleton, Bool.not_true, Finset.pair_comm] using!
        parallel_waiting_tests coords (hc C (List.mem_cons_self ..)) hs (by simpa using! hδ₀)
          true C.source hqs hzu (fun x hx =>
            stage1_parallel_close G true false C.source x hG hb₁ hδ₁ hu (by linarith) hx.2)
    have hwaitR : FiniteGame.TransitionChain
        (HasCoordinateTests G.parallel.depth (fun x j => parallelCoordinate coords j x))
        ((C.game.map (Parallel.embed G false)).withWaiting (Parallel.embed G true C.target))
        {Parallel.embed G true C.target, Parallel.embed G false C.source}
        {Parallel.embed G true C.target, Parallel.embed G false C.target} := by
      simpa only [Finset.image_singleton, Bool.not_false] using!
        parallel_waiting_tests coords (hc C (List.mem_cons_self ..)) hs (by simpa using! hδ₀)
          false C.target hqt (hz C (List.mem_cons_self ..)) (fun x hx =>
            stage1_parallel_close G false true C.target x hG hb₁ hδ₁
              (by linarith) (by linarith) (by linarith [hx.2]))
    exact hwaitL.append (hwaitR.append (ih C.target hrest (by linarith)
      (fun D hD => hc D (List.mem_cons_of_mem C hD))
      (fun D hD => hz D (List.mem_cons_of_mem C hD)) (hz C (List.mem_cons_self ..))))

end ConvexBodyChasing.TwoTerminal

end
end BundledModule036

/- Component source: ConvexBodyChasing.ThreeStageTests -/
section BundledModule037
/-! # Coordinate tests through an entire three-stage block -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing.TwoTerminal
local instance threeStageTestsDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem parallel_threeStage_tests {I : Type*} [Fintype I] (G : TwoTerminal)
    (coords : I → AnchoredFunction G) (m : ℕ) (hm : 0 < m) (b : ℝ)
    (hb₀ : 0 < b) (hb₁ : b ≤ m) (hδ : 1 / (m : ℝ) ≤ b)
    (small large : List (Call G)) (u middle : G)
    (hsmall : Call.Segments G.depth (1 / m) small u middle)
    (hlarge : Call.Segments G.depth 1 large middle G.target)
    (hsmallLen : small.length = m ^ 2) (hlargeLen : large.length = 2 * m)
    (hu : G.depth u = b) (hG : G.length = 3 * m + b)
    (hsmallTest : ∀ C ∈ small, FiniteGame.TransitionChain
      (HasCoordinateTests G.depth (fun x i => coords i x)) C.game {C.source} {C.target})
    (hlargeTest : ∀ C ∈ large, FiniteGame.TransitionChain
      (HasCoordinateTests G.depth (fun x i => coords i x)) C.game {C.source} {C.target})
    (hsmallZero : ∀ C ∈ small, ∀ i, coords i C.target = 0)
    (hlargeZero : ∀ C ∈ large, ∀ i, coords i C.target = 0)
    (huZero : ∀ i, coords i u = 0) (hmiddleZero : ∀ i, coords i middle = 0) :
    FiniteGame.TransitionChain
      (HasCoordinateTests G.parallel.depth (fun x j => parallelCoordinate coords j x))
      (Requests.threeStage G.parallel.source (Parallel.embed G true u) (Parallel.embed G false u)
        (small.map (Call.map (Parallel.embed G true))) (small.map (Call.map (Parallel.embed G false)))
        (large.map (Call.map (Parallel.embed G true))) (large.map (Call.map (Parallel.embed G false))) m)
      {G.parallel.source} {G.parallel.target} := by
  have hm₀ : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmiddle : G.depth middle = b + m := by
    rw [hsmall.height_target, hu, hsmallLen, Nat.cast_pow]
    field_simp
  have hrandom := parallel_random_tests G coords m m b hb₀ hb₁ hG large large middle middle
    hlarge hlarge (by omega) (by omega) (by omega) (by omega)
    hlargeTest hlargeTest hlargeZero hlargeZero hmiddleZero hmiddleZero
  have halt := parallel_alternating_tests G coords hm₀ hb₀ hb₁ (one_div_nonneg.mpr hm₀.le)
    hδ hG small u middle hsmall hu.ge hmiddle.le hsmallTest hsmallZero huZero _ _ hrandom
  unfold Requests.threeStage
  rw [(hsmall.map (Parallel.embed G true) G.parallel.depth 0 (fun x => by simp)).lastTarget,
    (hsmall.map (Parallel.embed G false) G.parallel.depth 0 (fun x => by simp)).lastTarget]
  refine ⟨HasCoordinateTests.singleton _ _ _,
    ⟨parallel_entrance_tests G coords u (by linarith) ?_, halt⟩⟩
  simpa only [tent_eq] using!
    (min_eq_left (show G.depth u ≤ G.length - G.depth u by linarith))

end ConvexBodyChasing.TwoTerminal

end
end BundledModule037

/- Component source: ConvexBodyChasing.CopyTests -/
section BundledModule038
/-! # Coordinate-test chains on the concrete recursive copies -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing.TwoTerminal
local instance copyTestsDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem copyCalls_tests {I : Type*} [Fintype I] (initial G : TwoTerminal)
    (initialCoords : I → AnchoredFunction initial) (coords : I → AnchoredFunction G)
    (g : FiniteGame G)
    (hg : FiniteGame.TransitionChain (HasCoordinateTests G.depth (fun x i => coords i x))
      g {G.source} {G.target}) (n : ℕ)
    (C : Call (appendCopies initial G n)) (hC : C ∈ copyCalls initial G g n) :
    FiniteGame.TransitionChain
      (HasCoordinateTests (appendCopies initial G n).depth
        (fun x i => (initialCoords i).appendCopies (coords i) n x)) C.game {C.source} {C.target} := by
  obtain ⟨ι, hι, rfl, hdepth, hcoords⟩ := copyCalls_restriction initial G g n C hC
  simpa only [Finset.image_singleton, Call.map] using!
    hg.map_tests ι (scale := 1) zero_lt_one (fun x y => by simp only [hι.dist_eq, one_mul])
      (appendCopies initial G n).depth
      (fun x i => (initialCoords i).appendCopies (coords i) n x)
      ((appendCopies initial G n).depth (ι G.source))
      (fun x => by simpa only [one_mul] using! hdepth x)
      (fun x i => by simpa only [one_mul] using! hcoords (initialCoords i) (coords i) x)

theorem normalizeGame_tests {I : Type*} [Fintype I] (G : TwoTerminal)
    (coords : I → AnchoredFunction G) (g : FiniteGame G)
    (hg : FiniteGame.TransitionChain (HasCoordinateTests G.depth (fun x i => coords i x))
      g {G.source} {G.target}) (L : ℝ) (hL : 0 < L) :
    FiniteGame.TransitionChain
      (HasCoordinateTests (G.normalize L hL).depth (fun x i => (coords i).normalize L hL x))
      (G.normalizeGame g L hL) {(G.normalize L hL).source} {(G.normalize L hL).target} := by
  simpa only [Finset.image_singleton] using!
    hg.map_tests (W := G.normalize L hL) (fun x => ⟨x⟩)
      (div_pos hL G.length_pos) (fun _ _ => rfl)
      (G.normalize L hL).depth (fun x i => (coords i).normalize L hL x) 0
      (fun x => (zero_add _).symm) (fun _ _ => rfl)

theorem initialEmbedding_tests {I : Type*} [Fintype I] (initial G : TwoTerminal)
    (initialCoords : I → AnchoredFunction initial) (coords : I → AnchoredFunction G)
    {g : FiniteGame initial} {S T : Finset initial}
    (hg : FiniteGame.TransitionChain
      (HasCoordinateTests initial.depth (fun x i => initialCoords i x)) g S T) (n : ℕ) :
    FiniteGame.TransitionChain
      (HasCoordinateTests (appendCopies initial G n).depth
        (fun x i => (initialCoords i).appendCopies (coords i) n x))
      (g.map (initialEmbedding initial G n))
      (S.image (initialEmbedding initial G n)) (T.image (initialEmbedding initial G n)) := by
  exact hg.map_tests (initialEmbedding initial G n) (scale := 1) zero_lt_one
    (fun x y => by simp only [(initialEmbedding_isometry initial G n).dist_eq, one_mul])
    _ _ 0 (fun x => by simp only [depth_initialEmbedding, one_mul, zero_add])
    (fun x i => by simp only [AnchoredFunction.appendCopies_initial, one_mul])

end ConvexBodyChasing.TwoTerminal

end
end BundledModule038

/- Component source: ConvexBodyChasing.StepTests -/
section BundledModule039
/-! # Coordinate tests for the actual recursive graph and request game -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing.TwoTerminal
local instance stepTestsDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem stepGame_tests {I : Type*} [Fintype I] (G : TwoTerminal)
    (coords : I → AnchoredFunction G) (g : FiniteGame G)
    (hg : FiniteGame.TransitionChain (HasCoordinateTests G.depth (fun x i => coords i x))
      g {G.source} {G.target})
    (m : ℕ) (hm : 0 < m) (b : ℝ) (hb : 0 < b)
    (hbm : b ≤ m) (hδ : 1 / (m : ℝ) ≤ b) :
    FiniteGame.TransitionChain
      (HasCoordinateTests (G.step m hm b hb).depth
        (fun x j => parallelCoordinate (fun i => (coords i).branch m hm b hb) j x))
      (G.stepGame g m hm b hb) {(G.step m hm b hb).source} {(G.step m hm b hb).target} := by
  let hm₀ : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  let entrance := edge.scale b hb
  let small := G.normalize (1 / m) (one_div_pos.mpr hm₀)
  let large := G.normalize 1 zero_lt_one
  let first := appendCopies entrance small (m ^ 2)
  let whole := appendCopies first large (2 * m)
  let lift := initialEmbedding first large (2 * m)
  let sg := G.normalizeGame g (1 / m) (one_div_pos.mpr hm₀)
  let lg := G.normalizeGame g 1 zero_lt_one
  let smallCoords := fun i => (coords i).normalize (1 / m) (one_div_pos.mpr hm₀)
  let largeCoords := fun i => (coords i).normalize 1 zero_lt_one
  let firstCoords := fun i => (AnchoredFunction.zero entrance).appendCopies (smallCoords i) (m ^ 2)
  let wholeCoords := fun i => (firstCoords i).appendCopies (largeCoords i) (2 * m)
  let smallCalls := (copyCalls entrance small sg (m ^ 2)).map (Call.map lift)
  let largeCalls := copyCalls first large lg (2 * m)
  let u := lift (initialEmbedding entrance small (m ^ 2) entrance.target)
  change FiniteGame.TransitionChain
    (HasCoordinateTests whole.parallel.depth (fun x j => parallelCoordinate wholeCoords j x))
    (Requests.threeStage whole.parallel.source (Parallel.embed whole true u) (Parallel.embed whole false u)
      (smallCalls.map (Call.map (Parallel.embed whole true)))
      (smallCalls.map (Call.map (Parallel.embed whole false)))
      (largeCalls.map (Call.map (Parallel.embed whole true)))
      (largeCalls.map (Call.map (Parallel.embed whole false))) m)
    {whole.parallel.source} {whole.parallel.target}
  apply parallel_threeStage_tests whole wholeCoords m hm b hb hbm hδ
    smallCalls largeCalls u (lift first.target)
  case hsmallTest =>
    intro D hD
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hD
    have hcopy := copyCalls_tests entrance small (fun _ => AnchoredFunction.zero entrance)
      smallCoords sg (normalizeGame_tests G coords g hg (1 / m) (one_div_pos.mpr hm₀))
      (m ^ 2) E hE
    simpa only [Finset.image_singleton, Call.map] using!
      initialEmbedding_tests first large firstCoords largeCoords hcopy (2 * m)
  case hlargeTest =>
    exact copyCalls_tests first large firstCoords largeCoords lg
      (normalizeGame_tests G coords g hg 1 zero_lt_one) (2 * m)
  case hsmallZero =>
    intro D hD i
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hD
    exact ((firstCoords i).appendCopies_initial (largeCoords i) (2 * m) E.target).trans
      (copyCalls_endpoints hE (AnchoredFunction.zero entrance) (smallCoords i)).2
  case hlargeZero =>
    exact fun D hD i => (copyCalls_endpoints hD (firstCoords i) (largeCoords i)).2
  case huZero =>
    exact fun i => ((firstCoords i).appendCopies_initial (largeCoords i) (2 * m) _).trans
      ((AnchoredFunction.zero entrance).appendCopies_initial (smallCoords i) (m ^ 2) entrance.target)
  case hmiddleZero =>
    exact fun i => ((firstCoords i).appendCopies_initial (largeCoords i) (2 * m) first.target).trans
      (firstCoords i).target_zero
  case hsmall =>
    simpa only [small, length_normalize] using!
      (copyCalls_segments entrance small sg (m ^ 2)).map lift whole.depth 0
        (fun z => by simp only [whole, lift, depth_initialEmbedding, zero_add, first])
  case hlarge =>
    simpa only [large, length_normalize] using! copyCalls_segments first large lg (2 * m)
  case hsmallLen =>
    simpa only [smallCalls, List.length_map] using! length_copyCalls entrance small sg (m ^ 2)
  case hlargeLen => exact length_copyCalls first large lg (2 * m)
  case hu =>
    exact (depth_initialEmbedding first large (2 * m) _).trans
      ((depth_initialEmbedding entrance small (m ^ 2) entrance.target).trans
        (show entrance.length = b by simp only [entrance, length_scale, length_edge, mul_one]))
  case hG => exact length_branch G m hm b hb

end ConvexBodyChasing.TwoTerminal

end
end BundledModule039

/- Component source: ConvexBodyChasing.FairWalk -/
section BundledModule040
/-! # A quantitative fair-coin imbalance estimate

All expectations here are finite binary averages. No measure-theoretic
assumptions or asymptotic limit estimates are needed.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing.FairWalk

/-- Average of `f` after `n` independent symmetric unit steps starting at `x`. -/
def average : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f, x => f x
  | n + 1, f, x => (average n f (x - 1) + average n f (x + 1)) / 2

theorem fourth_moment (n : ℕ) (x : ℝ) :
    average n (fun y => y ^ 4) x = x ^ 4 + 6 * n * x ^ 2 + 3 * (n : ℝ) ^ 2 - 2 * n := by
  induction n generalizing x with
  | zero => simp [average]
  | succ n ih =>
    simp only [average, ih, Nat.cast_add, Nat.cast_one]
    ring

theorem second_moment (n : ℕ) (x : ℝ) :
    average n (fun y => y ^ 2) x = x ^ 2 + n := by
  induction n generalizing x <;> simp [average, *, Nat.cast_add]
  ring

theorem average_linear (n : ℕ) (f g : ℝ → ℝ) (a b x : ℝ) :
    average n (fun y => a * f y + b * g y) x =
      a * average n f x + b * average n g x := by
  induction n generalizing x <;> simp only [average, *]
  ring

theorem average_mono (n : ℕ) {f g : ℝ → ℝ} (h : ∀ y, f y ≤ g y) (x : ℝ) :
    average n f x ≤ average n g x := by
  induction n generalizing x with
  | zero => exact h x
  | succ n ih => exact div_le_div_of_nonneg_right (add_le_add (ih _) (ih _)) (by norm_num)



theorem average_mul (n : ℕ) (f : ℝ → ℝ) (c x : ℝ) :
    average n (fun y => c * f y) x = c * average n f x := by
  simpa only [zero_mul, add_zero] using! average_linear n f f c 0 x

/-- A quartic polynomial minorizes absolute value after scaling. -/
theorem abs_polynomial_lower (x t : ℝ) (ht : 0 ≤ t) :
    3 * t ^ 2 * x ^ 2 - x ^ 4 ≤ 2 * t ^ 3 * |x| := by
  have h := mul_nonneg (mul_nonneg (abs_nonneg x)
    (show 0 ≤ |x| + 2 * t by positivity)) (sq_nonneg (|x| - t))
  nlinarith only [h, sq_abs x]

/-- Explicit fluctuation bound for a symmetric walk, including `n = 0`. -/
theorem abs_average_lower (n : ℕ) : Real.sqrt n / 2 ≤ average n abs 0 := by
  have h := average_mono n
    (f := fun y => (3 * (2 * Real.sqrt n) ^ 2) * y ^ 2 + (-1) * y ^ 4)
    (g := fun y => (2 * (2 * Real.sqrt n) ^ 3) * |y|)
    (fun y => by simpa only [neg_one_mul, sub_eq_add_neg] using!
      abs_polynomial_lower y (2 * Real.sqrt n) (by positivity)) 0
  rw [average_linear, average_mul, second_moment, fourth_moment] at h
  norm_num [mul_pow, show ∀ x : ℝ, x ^ 3 = x * x ^ 2 by intro x; ring,
    Real.sq_sqrt (Nat.cast_nonneg n)] at h
  by_cases hn : n = 0
  · simp [hn, average]
  · have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    apply (mul_le_mul_iff_right₀ (show 0 < 16 * Real.sqrt n * n by positivity)).mp
    nlinarith [congrArg (fun x : ℝ => x * n) (Real.sq_sqrt (Nat.cast_nonneg n))]

/-- The random-stage charge is the average terminal branch length. -/
theorem randomCharge_eq (n left right : ℕ) (hleft : n ≤ left) (hright : n ≤ right) :
    Requests.randomCharge n left right =
      ((left : ℝ) + right) / 2 + average n abs ((left : ℝ) - right) / 2 := by
  induction n generalizing left right with
  | zero =>
    rcases le_total (left : ℝ) right with h | h
    · simp only [Requests.randomCharge, average, Nat.cast_max, max_eq_right h,
        abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · simp only [Requests.randomCharge, average, Nat.cast_max, max_eq_left h,
        abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  | succ n ih =>
    rw [Requests.randomCharge, ih (left - 1) right (by omega) (by omega),
      ih left (right - 1) (by omega) (by omega)]
    simp only [average, Nat.cast_sub (show 1 ≤ left by omega), Nat.cast_sub (show 1 ≤ right by omega), Nat.cast_one]
    ring_nf

theorem balanced_charge_lower (m : ℕ) :
    2 * m + Real.sqrt m / 4 ≤ Requests.randomCharge m (2 * m) (2 * m) := by
  rw [randomCharge_eq m (2 * m) (2 * m) (by omega) (by omega)]
  simp only [Nat.cast_mul, Nat.cast_ofNat, sub_self]
  linarith [abs_average_lower m]

end ConvexBodyChasing.FairWalk

end
end BundledModule040

/- Component source: ConvexBodyChasing.ThreeStageLower -/
section BundledModule041
/-! # The combined discrete lower-bound step

The geometric certificates are explicit intermediate hypotheses. They still
have to be verified for the concrete graph construction before this theorem
can be used in the recursive lower bound.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing.Requests
variable {V : Type*} [MetricSpace V] [DecidableEq V]

theorem threeStage_cap_lower (source u v : V)
    (smallLeft smallRight largeLeft largeRight : List (Call V)) (rounds : ℕ)
    {aSmall pSmall aLarge pLarge c price : ℝ}
    (haSmall : 0 ≤ aSmall) (hapSmall : aSmall ≤ pSmall)
    (haLarge : 0 ≤ aLarge) (hapLarge : aLarge ≤ pLarge)
    (hbudgetLarge : pLarge + aLarge * ((max largeLeft.length largeRight.length : ℕ) + rounds) + c ≤ price)
    (hbudgetSmall : pSmall + aSmall * (smallLeft.zip smallRight).length +
      (aLarge * randomCharge rounds largeLeft.length largeRight.length + c) ≤ price)
    (hsmall : AlternatingSafe aSmall pSmall (smallLeft.zip smallRight) v)
    (hlarge : RandomSafe aLarge pLarge rounds largeLeft largeRight
      (lastTarget u smallLeft) (lastTarget v smallRight))
    (hleft : ∀ C ∈ largeLeft, C.EscapeBound aLarge pLarge)
    (hright : ∀ C ∈ largeRight, C.EscapeBound aLarge pLarge)
    (f : V → ℝ) (hf : ∀ x, c ≤ f x) :
    ∀ x, aSmall * (smallLeft.zip smallRight).length +
      (aLarge * randomCharge rounds largeLeft.length largeRight.length + c) ≤
        FiniteGame.capEval price f
          (threeStage source u v smallLeft smallRight largeLeft largeRight rounds) x := by
  have h2 := randomStage_cap_lower rounds largeLeft largeRight
    (lastTarget u smallLeft) (lastTarget v smallRight) haLarge hapLarge hbudgetLarge
    hlarge hleft hright f hf
  have h1 := alternating_cap_lower (smallLeft.zip smallRight) v haSmall hapSmall
    hbudgetSmall hsmall _ f h2
  have hp : aSmall * (smallLeft.zip smallRight).length +
      (aLarge * randomCharge rounds largeLeft.length largeRight.length + c) ≤ price := by
    linarith
  exact singleton_cap_ge _ source f hp
    (FiniteGame.capEval_ge_const (.request {u, v} (by simp) .stop) hp h1 source)

/-- The explicit gain from one three-stage construction, once its call and
separation certificates have been established. -/
theorem threeStage_escape_lower (source u v : V)
    (smallLeft smallRight largeLeft largeRight : List (Call V))
    (m : ℕ) (hm : 0 < m) (C : ℝ) (hC : 0 ≤ C)
    (hsmallLen : (smallLeft.zip smallRight).length = m ^ 2)
    (hleftLen : largeLeft.length = 2 * m) (hrightLen : largeRight.length = 2 * m)
    (hsmall : AlternatingSafe (C / m) (2 * C / m) (smallLeft.zip smallRight) v)
    (hlarge : RandomSafe C (2 * C) m largeLeft largeRight
      (lastTarget u smallLeft) (lastTarget v smallRight))
    (hleft : ∀ D ∈ largeLeft, D.EscapeBound C (2 * C))
    (hright : ∀ D ∈ largeRight, D.EscapeBound C (2 * C)) :
    ∀ x, (3 * m + Real.sqrt m / 4) * C ≤ FiniteGame.escapeEval (6 * m * C)
      (threeStage source u v smallLeft smallRight largeLeft largeRight m) x := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hshort : C / m * (smallLeft.zip smallRight).length = C * m := by
    rw [hsmallLen, Nat.cast_pow, pow_two, ← mul_assoc, div_mul_cancel₀ _ hm0.ne']
  have hdivision : 2 * C / m ≤ 2 * C := div_le_self (by positivity) hm1
  have hcharge : randomCharge m largeLeft.length largeRight.length ≤ 3 * m := by
    calc
      _ ≤ ((max largeLeft.length largeRight.length : ℕ) : ℝ) + m := randomCharge_le _ _ _
      _ = 3 * (m : ℝ) := by simp only [hleftLen, hrightLen, max_self, Nat.cast_mul, Nat.cast_ofNat]; ring
  have hbSmall : 2 * C / m + C / m * (smallLeft.zip smallRight).length +
      (C * randomCharge m largeLeft.length largeRight.length + 0) ≤ 6 * m * C := by
    nlinarith [mul_le_mul_of_nonneg_left hcharge hC]
  have hbLarge : 2 * C + C * ((max largeLeft.length largeRight.length : ℕ) + m) + 0 ≤ 6 * m * C := by
    simp only [hleftLen, hrightLen, max_self, Nat.cast_mul, Nat.cast_ofNat, add_zero]
    nlinarith
  have h := threeStage_cap_lower source u v smallLeft smallRight largeLeft largeRight m
    (div_nonneg hC hm0.le) (div_le_div_of_nonneg_right (by linarith) hm0.le)
    hC (by linarith) hbLarge hbSmall hsmall hlarge hleft hright (fun _ => 0) (fun _ => le_rfl)
  simp only [hshort, hleftLen, hrightLen, add_zero, FiniteGame.capEval_zero] at h
  intro x
  nlinarith [h x, mul_le_mul_of_nonneg_left (FairWalk.balanced_charge_lower m) hC]

end ConvexBodyChasing.Requests

end
end BundledModule041

/- Component source: ConvexBodyChasing.StepLower -/
section BundledModule042
/-! # The lower-bound step on the concrete recursive graph -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing.TwoTerminal
local instance stepLowerDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α

theorem parallel_threeStage_lower (G : TwoTerminal) (m : ℕ) (hm : 0 < m)
    (C : ℝ) (hC : 0 ≤ C) (hCm : C ≤ m)
    (small large : List (Call G)) (u middle : G)
    (hsmall : Call.Segments G.depth (1 / m) small u middle)
    (hlarge : Call.Segments G.depth 1 large middle G.target)
    (hsmallLen : small.length = m ^ 2) (hlargeLen : large.length = 2 * m)
    (hu : G.depth u = C / m) (hG : G.length = 3 * m + C / m)
    (hsmallCost : ∀ D ∈ small, D.EscapeBound (C / m) (2 * C / m))
    (hlargeCost : ∀ D ∈ large, D.EscapeBound C (2 * C)) :
    ∀ x, (3 * m + Real.sqrt m / 4) * C ≤ FiniteGame.escapeEval (6 * m * C)
      (Requests.threeStage G.parallel.source (Parallel.inl G u) (Parallel.inr G u)
        (small.map (Call.map (Parallel.inl G))) (small.map (Call.map (Parallel.inr G)))
        (large.map (Call.map (Parallel.inl G))) (large.map (Call.map (Parallel.inr G))) m) x := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hmiddle : G.depth middle = C / m + m := by
    rw [hsmall.height_target, hu, hsmallLen, Nat.cast_pow]
    field_simp
  apply Requests.threeStage_escape_lower _ _ _ _ _ _ _ m hm C hC
  · simp only [List.length_zip, List.length_map, min_self, hsmallLen]
  · simpa only [List.length_map] using! hlargeLen
  · simpa only [List.length_map] using! hlargeLen
  · apply alternatingSafe_parallel G small u middle (by positivity) hsmall hsmallCost
    · rw [hu, mul_div_assoc]
    · rw [hG, hmiddle]
      linarith [div_le_self (show 0 ≤ 2 * C by positivity) (show (1 : ℝ) ≤ m by exact_mod_cast hm)]
  · rw [(hsmall.map (Parallel.inl G) G.parallel.depth 0 (fun z => by simp)).lastTarget,
      (hsmall.map (Parallel.inr G) G.parallel.depth 0 (fun z => by simp)).lastTarget]
    apply randomSafe_parallel G m m large large middle middle C (2 * C) hlarge hlarge
      (by omega) (by omega) (by omega) (by omega)
    · rw [hG]
      linarith [div_nonneg hC hm0.le]
    · linarith
  · intro D hD
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hD
    exact (hlargeCost E hE).map _ (Parallel.inl_isometry G)
  · intro D hD
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hD
    exact (hlargeCost E hE).map _ (Parallel.inr_isometry G)

/-- One genuine recursive step: all copy-depth and branch-separation conditions
are discharged for `stepGame`. Only the smaller game's inductive bound remains. -/
theorem stepGame_escape_lower (G : TwoTerminal) (g : FiniteGame G)
    (m : ℕ) (hm : 0 < m) (C : ℝ) (hC : 0 < C) (hCm : C ≤ m)
    (hg : (⟨G.source, G.target, g⟩ : Call G).EscapeBound (C * G.length) (2 * C * G.length)) :
    ∀ x, (3 * m + Real.sqrt m / 4) * C ≤ FiniteGame.escapeEval (6 * m * C)
      (G.stepGame g m hm (C / m) (div_pos hC (Nat.cast_pos.mpr hm))) x := by
  let hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  let entrance := edge.scale (C / m) (div_pos hC hm0)
  let small := G.normalize (1 / m) (one_div_pos.mpr hm0)
  let large := G.normalize 1 zero_lt_one
  let first := appendCopies entrance small (m ^ 2)
  let whole := appendCopies first large (2 * m)
  let lift := initialEmbedding first large (2 * m)
  let sg := G.normalizeGame g (1 / m) (one_div_pos.mpr hm0)
  let lg := G.normalizeGame g 1 zero_lt_one
  let smallCalls := (copyCalls entrance small sg (m ^ 2)).map (Call.map lift)
  let largeCalls := copyCalls first large lg (2 * m)
  let u := lift (initialEmbedding entrance small (m ^ 2) entrance.target)
  change ∀ x, (3 * m + Real.sqrt m / 4) * C ≤ FiniteGame.escapeEval (6 * m * C)
    (Requests.threeStage whole.parallel.source (Parallel.inl whole u) (Parallel.inr whole u)
      (smallCalls.map (Call.map (Parallel.inl whole))) (smallCalls.map (Call.map (Parallel.inr whole)))
      (largeCalls.map (Call.map (Parallel.inl whole))) (largeCalls.map (Call.map (Parallel.inr whole))) m) x
  apply parallel_threeStage_lower whole m hm C hC.le hCm smallCalls largeCalls u (lift first.target)
  · simpa only [small, length_normalize] using!
      (copyCalls_segments entrance small sg (m ^ 2)).map lift whole.depth 0
        (fun z => by simp only [whole, lift, depth_initialEmbedding, zero_add, first])
  · simpa only [large, length_normalize] using! copyCalls_segments first large lg (2 * m)
  · simpa only [smallCalls, List.length_map] using! length_copyCalls entrance small sg (m ^ 2)
  · exact length_copyCalls first large lg (2 * m)
  · simp only [whole, u, lift, first, depth_initialEmbedding]
    change entrance.length = C / m
    simp only [entrance, length_scale, length_edge, mul_one]
  · exact length_branch G m hm (C / m) (div_pos hC hm0)
  · have hs : (⟨small.source, small.target, sg⟩ : Call small).EscapeBound (C / m) (2 * C / m) := by
      simpa only [mul_one_div] using! normalizeGame_escapeBound G g (1 / m) (one_div_pos.mpr hm0) hg
    intro D hD
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hD
    exact (copyCalls_escapeBound entrance small sg hs (m ^ 2) E hE).map lift
      (initialEmbedding_isometry first large (2 * m))
  · exact copyCalls_escapeBound first large lg
      (by simpa only [mul_one] using! normalizeGame_escapeBound G g 1 zero_lt_one hg) (2 * m)

end ConvexBodyChasing.TwoTerminal

end
end BundledModule042

/- Component source: ConvexBodyChasing.Parameters -/
section BundledModule043
/-! # Explicit parameters for quadratic discrete growth -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing

theorem recursive_gain (C m : ℝ) (hC : 1 ≤ C) (hmin : 16 * C ≤ m) (hmax : m ≤ 17 * C) :
    (C + Real.sqrt C / 100) * (3 * m + C / m) ≤ (3 * m + Real.sqrt m / 4) * C := by
  have hC0 : 0 ≤ C := by linarith
  have hm0 : 0 < m := by linarith
  have hs : 1 ≤ Real.sqrt C := Real.le_sqrt_of_sq_le (by simpa only [one_pow] using! hC)
  have hdiv : C / m ≤ 1 / 16 := (div_le_iff₀ hm0).mpr (by linarith)
  have hroot : 4 * Real.sqrt C ≤ Real.sqrt m :=
    Real.le_sqrt_of_sq_le (by nlinarith [Real.sq_sqrt hC0])
  nlinarith [mul_le_mul_of_nonneg_left hdiv hC0,
    mul_le_mul_of_nonneg_left hdiv (Real.sqrt_nonneg C),
    mul_le_mul_of_nonneg_left hmax (Real.sqrt_nonneg C),
    mul_le_mul_of_nonneg_left hroot hC0, mul_le_mul_of_nonneg_left hs hC0,
    mul_le_mul_of_nonneg_left hC (Real.sqrt_nonneg C)]

def discreteRate (r : ℕ) : ℝ := (1 + r / 1000) ^ 2

def discreteCopies (r : ℕ) : ℕ := ⌈16 * discreteRate r⌉₊

theorem discreteRate_one_le (r : ℕ) : 1 ≤ discreteRate r := by
  unfold discreteRate
  nlinarith [Nat.cast_nonneg (α := ℝ) r]

theorem discreteRate_pos (r : ℕ) : 0 < discreteRate r :=
  zero_lt_one.trans_le (discreteRate_one_le r)

theorem discreteCopies_lower (r : ℕ) : 16 * discreteRate r ≤ discreteCopies r :=
  Nat.le_ceil _

theorem discreteCopies_upper (r : ℕ) : (discreteCopies r : ℝ) ≤ 17 * discreteRate r := by
  have h := Nat.ceil_lt_add_one (mul_nonneg (show (0 : ℝ) ≤ 16 by norm_num) (discreteRate_pos r).le)
  change (discreteCopies r : ℝ) < 16 * discreteRate r + 1 at h
  linarith [discreteRate_one_le r]

theorem discreteCopies_pos (r : ℕ) : 0 < discreteCopies r := by
  exact_mod_cast (show (0 : ℝ) < discreteCopies r by linarith [discreteCopies_lower r, discreteRate_pos r])

theorem discreteRate_le_copies (r : ℕ) : discreteRate r ≤ discreteCopies r := by
  linarith [discreteCopies_lower r, discreteRate_pos r]

theorem sqrt_discreteRate (r : ℕ) : Real.sqrt (discreteRate r) = 1 + r / 1000 :=
  Real.sqrt_sq (by positivity)

theorem discreteRate_succ_le (r : ℕ) :
    discreteRate (r + 1) ≤ discreteRate r + Real.sqrt (discreteRate r) / 100 := by
  rw [sqrt_discreteRate]
  simp only [discreteRate, Nat.cast_add, Nat.cast_one]
  nlinarith [Nat.cast_nonneg (α := ℝ) r]

theorem discreteRate_le_succ (r : ℕ) : discreteRate r ≤ discreteRate (r + 1) := by
  simp only [discreteRate, Nat.cast_add, Nat.cast_one]
  nlinarith [Nat.cast_nonneg (α := ℝ) r]

def lowerBoundParameters : GraphParameters where
  copies := discreteCopies
  copies_pos := discreteCopies_pos
  entrance r := discreteRate r / discreteCopies r
  entrance_pos r := div_pos (discreteRate_pos r) (Nat.cast_pos.mpr (discreteCopies_pos r))

theorem discreteRate_step (r : ℕ) :
    discreteRate (r + 1) * (3 * discreteCopies r + discreteRate r / discreteCopies r) ≤
      (3 * discreteCopies r + Real.sqrt (discreteCopies r) / 4) * discreteRate r := by
  apply (mul_le_mul_of_nonneg_right (discreteRate_succ_le r) ?_).trans
    (recursive_gain _ _ (discreteRate_one_le r) (discreteCopies_lower r) (discreteCopies_upper r))
  exact add_nonneg (by positivity) (div_nonneg (discreteRate_pos r).le (Nat.cast_nonneg _))

theorem discreteRate_escapePrice (r : ℕ) :
    6 * discreteCopies r * discreteRate r ≤
      2 * discreteRate (r + 1) * (3 * discreteCopies r + discreteRate r / discreteCopies r) := by
  nlinarith [mul_le_mul_of_nonneg_left (discreteRate_le_succ r) (Nat.cast_nonneg (α := ℝ) (discreteCopies r)),
    mul_nonneg (discreteRate_pos (r + 1)).le
      (div_nonneg (discreteRate_pos r).le (Nat.cast_nonneg (α := ℝ) (discreteCopies r)))]

end ConvexBodyChasing

end
end BundledModule043

/- Component source: ConvexBodyChasing.RecursiveTests -/
section BundledModule044
/-! # Consecutive-request coordinate tests for the full recursive family -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
namespace ConvexBodyChasing
local instance recursiveTestsDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance recursiveTestsFintype (G : TwoTerminal) : Fintype G := Fintype.ofFinite G

theorem recursiveGame_coordinate_tests (P : GraphParameters)
    (hentrance : ∀ r, P.entrance r ≤ P.copies r)
    (hsmall : ∀ r, 1 / (P.copies r : ℝ) ≤ P.entrance r) (r : ℕ) :
    FiniteGame.TransitionChain
      (HasCoordinateTests (recursiveGraph P r).depth (fun x i => branchCoordinate P r i x))
      (recursiveGame P r) {(recursiveGraph P r).source} {(recursiveGraph P r).target} := by
  induction r with
  | zero =>
    exact ⟨HasCoordinateTests.singleton _ _ _,
      ⟨HasCoordinateTests.of_forward _ _ _ _ (by simp [recursiveGraph, TwoTerminal.depth]), rfl⟩⟩
  | succ r ih =>
    exact TwoTerminal.stepGame_tests (recursiveGraph P r) (branchCoordinate P r) (recursiveGame P r)
      ih (P.copies r) (P.copies_pos r) (P.entrance r) (P.entrance_pos r) (hentrance r) (hsmall r)

/-- No geometric premises remain for the explicit lower-bound family. -/
theorem lowerBoundGame_coordinate_tests (r : ℕ) :
    FiniteGame.TransitionChain
      (HasCoordinateTests (recursiveGraph lowerBoundParameters r).depth
        (fun x i => branchCoordinate lowerBoundParameters r i x))
      (recursiveGame lowerBoundParameters r)
      {(recursiveGraph lowerBoundParameters r).source} {(recursiveGraph lowerBoundParameters r).target} := by
  apply recursiveGame_coordinate_tests lowerBoundParameters ?_ ?_ r
  · exact fun n => (div_le_self (discreteRate_pos n).le
      (by exact_mod_cast discreteCopies_pos n)).trans (discreteRate_le_copies n)
  · exact fun n => div_le_div_of_nonneg_right (discreteRate_one_le n) (Nat.cast_nonneg _)

theorem Ψ_eq_fullCoords (P : GraphParameters) (r : ℕ) :
    Ψ P r = CoordinateTest.fullCoords (recursiveGraph P r).depth
      (fun x i => branchCoordinate P r i x) := by
  exact funext (fun x => funext (fun | none => rfl | some i => rfl))



end ConvexBodyChasing

end
end BundledModule044

/- Component source: ConvexBodyChasing.Offline -/
section BundledModule045
/-! # Offline paths through the request generator

The proofs quantify over every realized finite request sequence. In particular,
the offline branch choice may depend on all the coins, but the requests do not
depend on a player's choices.
-/

namespace ConvexBodyChasing

namespace FiniteGame

variable {V : Type*} [DecidableEq V] {R : V → V → Prop}

/-- Every realization has a feasible path with moves satisfying `R`. -/
def HasOfflinePath (G : FiniteGame V) (R : V → V → Prop) (x y : V) : Prop :=
  ∀ requests, G.Realizes requests → ServesAlong R x requests y

theorem HasOfflinePath.withWaiting {G : FiniteGame V} {x y : V}
    (h : G.HasOfflinePath R x y) (z : V) :
    (G.withWaiting z).HasOfflinePath R x y := by
  intro requests hrequests
  obtain ⟨original, horiginal, rfl⟩ := (realizes_withWaiting z G requests).mp hrequests
  exact (h original horiginal).enlarge (insert z) (fun S => Finset.subset_insert z S)

theorem withWaiting_hasOfflinePath (G : FiniteGame V) (z : V) (hzz : R z z) :
    (G.withWaiting z).HasOfflinePath R z z := by
  intro requests hrequests
  obtain ⟨original, _, rfl⟩ := (realizes_withWaiting z G requests).mp hrequests
  exact ServesAlong.wait z hzz _ (by simp)

omit [DecidableEq V] in
theorem HasOfflinePath.append {G H : FiniteGame V} {x y z : V}
    (hG : G.HasOfflinePath R x y) (hH : H.HasOfflinePath R y z) :
    (G.append H).HasOfflinePath R x z := by
  intro requests hrequests
  obtain ⟨first, rest, hfirst, hrest, rfl⟩ := (realizes_append G H requests).mp hrequests
  exact (hG first hfirst).append (hH rest hrest)

/-- The starting branch may be chosen after all coins have been revealed. -/
def HasOfflineChoice (G : FiniteGame V) (R : V → V → Prop) (x y target : V) : Prop :=
  ∀ requests, G.Realizes requests →
    ServesAlong R x requests target ∨ ServesAlong R y requests target

theorem HasOfflineChoice.advance {G H : FiniteGame V} {x next y target : V}
    (hH : H.HasOfflineChoice R next y target) (hG : G.HasOfflinePath R x next)
    (hyy : R y y) : ((G.withWaiting y).append H).HasOfflineChoice R x y target := by
  intro requests hrequests
  obtain ⟨first, rest, hfirst, hrest, rfl⟩ :=
    (realizes_append (G.withWaiting y) H requests).mp hrequests
  rcases hH rest hrest with h | h
  · exact Or.inl ((hG.withWaiting y first hfirst).append h)
  · exact Or.inr ((withWaiting_hasOfflinePath G y hyy first hfirst).append h)

omit [DecidableEq V] in
theorem HasOfflineChoice.symm {G : FiniteGame V} {x y target : V}
    (h : G.HasOfflineChoice R x y target) : G.HasOfflineChoice R y x target :=
  fun requests hrequests => (h requests hrequests).symm

omit [DecidableEq V] in
theorem HasOfflineChoice.coin {G H : FiniteGame V} {x y target : V}
    (hG : G.HasOfflineChoice R x y target) (hH : H.HasOfflineChoice R x y target) :
    (FiniteGame.coin G H).HasOfflineChoice R x y target := by
  intro requests hrequests
  exact Or.elim hrequests (hG requests) (hH requests)

omit [DecidableEq V] in
theorem HasOfflinePath.map {W : Type*} [DecidableEq W] {T : W → W → Prop}
    {G : FiniteGame V} {x y : V} (h : G.HasOfflinePath R x y)
    (f : V → W) (hf : ∀ {a b}, R a b → T (f a) (f b)) :
    (G.map f).HasOfflinePath T (f x) (f y) := by
  intro requests hrequests
  obtain ⟨original, horiginal, rfl⟩ := (realizes_map f G requests).mp hrequests
  exact (h original horiginal).map f hf

end FiniteGame

namespace Call

variable {V : Type*}

/-- Consecutive recursive calls, with a certified offline path in each. -/
def Chain (R : V → V → Prop) : List (Call V) → V → V → Prop
  | [], x, y => x = y
  | C :: Cs, x, y => x = C.source ∧
      C.game.HasOfflinePath R C.source C.target ∧ Chain R Cs C.target y

theorem Chain.map {W : Type*} [DecidableEq W] {R : V → V → Prop} {T : W → W → Prop}
    {calls : List (Call V)} {x y : V} (h : Chain R calls x y)
    (f : V → W) (hf : ∀ {a b}, R a b → T (f a) (f b)) :
    Chain T (calls.map (Call.map f)) (f x) (f y) := by
  induction calls generalizing x with
  | nil => exact congrArg f h
  | cons C Cs ih => exact ⟨congrArg f h.1, h.2.1.map f hf, ih h.2.2⟩

theorem Chain.append {R : V → V → Prop} {left right : List (Call V)} {x y z : V}
    (hl : Chain R left x y) (hr : Chain R right y z) : Chain R (left ++ right) x z := by
  induction left generalizing x with
  | nil => exact hl ▸ hr
  | cons C Cs ih => exact ⟨hl.1, hl.2.1, ih hl.2.2⟩

end Call

namespace Requests

variable {V : Type*} [DecidableEq V] {R : V → V → Prop}

omit [DecidableEq V] in
theorem sequence_hasOfflinePath {calls : List (Call V)} {x y : V}
    (h : Call.Chain R calls x y) : (sequence calls).HasOfflinePath R x y := by
  induction calls generalizing x with
  | nil =>
    rcases h with rfl
    rintro requests rfl
    exact .nil x
  | cons C Cs ih =>
    rcases h with ⟨rfl, hC, hCs⟩
    exact hC.append (ih hCs)

omit [DecidableEq V] in
theorem singleton_hasOfflinePath {G : FiniteGame V} {x y z : V}
    (hxy : R x y) (hG : G.HasOfflinePath R y z) :
    (singleton y G).HasOfflinePath R x z := by
  rintro requests ⟨rest, rfl, hrest⟩
  exact .cons (Finset.mem_singleton_self y) hxy (hG rest hrest)

omit [DecidableEq V] in
theorem finish_offline {left right : List (Call V)} {u v target : V}
    (hrefl : ∀ x, R x x) (hleft : Call.Chain R left u target)
    (hright : Call.Chain R right v target) (requests : List (Finset V))
    (hrequests : (finish left right u v).Realizes requests) :
    ServesAlong R u requests target ∨ ServesAlong R v requests target := by
  by_cases hlen : right.length ≤ left.length
  · exact Or.inl (singleton_hasOfflinePath (hrefl u) (sequence_hasOfflinePath hleft)
      requests (by simpa only [finish, if_pos hlen] using! hrequests))
  · exact Or.inr (singleton_hasOfflinePath (hrefl v) (sequence_hasOfflinePath hright)
      requests (by simpa only [finish, if_neg hlen] using! hrequests))

theorem randomStage_offline (rounds : ℕ) {left right : List (Call V)} {u v target : V}
    (hrefl : ∀ x, R x x) (hleft : Call.Chain R left u target)
    (hright : Call.Chain R right v target) :
    (randomStage rounds left right u v).HasOfflineChoice R u v target := by
  induction rounds generalizing left right u v with
  | zero => exact finish_offline hrefl hleft hright
  | succ rounds ih =>
    cases left with
    | nil => exact finish_offline hrefl hleft hright
    | cons L left =>
      cases right with
      | nil => exact finish_offline hrefl hleft hright
      | cons C right =>
        rcases hleft with ⟨rfl, hL, hleft⟩
        rcases hright with ⟨rfl, hC, hright⟩
        exact ((ih (right := C :: right) hleft ⟨rfl, hC, hright⟩).advance hL
          (hrefl _)).coin
          (((ih (left := L :: left) ⟨rfl, hL, hleft⟩ hright).symm.advance hC
            (hrefl _)).symm)

theorem alternating_offline {left right : List (Call V)} {u v u' v' target : V}
    {next : FiniteGame V} (hrefl : ∀ x, R x x)
    (hleft : Call.Chain R left u u') (hright : Call.Chain R right v v')
    (hlen : left.length = right.length) (hnext : next.HasOfflineChoice R u' v' target) :
    (alternating (left.zip right) v next).HasOfflineChoice R u v target := by
  induction left generalizing right u v with
  | nil =>
    have hr : right = [] := List.length_eq_zero_iff.mp hlen.symm
    simp only [hr, Call.Chain, List.zip_nil_left, alternating] at hleft hright ⊢
    simpa only [hleft, hright] using! hnext

  | cons L left ih =>
    cases right with
    | nil => simp at hlen
    | cons C right =>
      rcases hleft with ⟨rfl, hL, hleft⟩
      rcases hright with ⟨rfl, hC, hright⟩
      exact (((ih hleft hright (Nat.succ.inj hlen)).symm.advance hC
        (hrefl _)).symm.advance hL (hrefl _))

omit [DecidableEq V] in
theorem lastTarget_of_chain {calls : List (Call V)} {x y : V}
    (h : Call.Chain R calls x y) : lastTarget x calls = y := by
  induction calls generalizing x with
  | nil => exact h
  | cons C Cs ih => exact ih h.2.2

theorem pair_hasOfflinePath {next : FiniteGame V} {source u v target : V}
    (hu : R source u) (hv : R source v) (hnext : next.HasOfflineChoice R u v target) :
    (FiniteGame.request {u, v} (by simp) next).HasOfflinePath R source target := by
  rintro requests ⟨rest, rfl, hrest⟩
  rcases hnext rest hrest with h | h
  · exact .cons (by simp) hu h
  · exact .cons (by simp) hv h

theorem threeStage_offline (rounds : ℕ)
    {smallLeft smallRight largeLeft largeRight : List (Call V)}
    {source u v u' v' target : V} (hrefl : ∀ x, R x x)
    (hu : R source u) (hv : R source v)
    (hsmallLeft : Call.Chain R smallLeft u u')
    (hsmallRight : Call.Chain R smallRight v v')
    (hlargeLeft : Call.Chain R largeLeft u' target)
    (hlargeRight : Call.Chain R largeRight v' target)
    (hlen : smallLeft.length = smallRight.length) :
    (threeStage source u v smallLeft smallRight largeLeft largeRight rounds).HasOfflinePath
      R source target := by
  unfold threeStage
  rw [lastTarget_of_chain hsmallLeft, lastTarget_of_chain hsmallRight]
  exact singleton_hasOfflinePath (hrefl source) (pair_hasOfflinePath hu hv
    (alternating_offline hrefl hsmallLeft hsmallRight hlen
      (randomStage_offline rounds hrefl hlargeLeft hlargeRight)))

end Requests
end ConvexBodyChasing

end BundledModule045

/- Component source: ConvexBodyChasing.EmbeddedOffline -/
section BundledModule046
/-! # Offline paths in the concrete recursive construction -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing

local instance (α : Type*) : DecidableEq α := Classical.decEq α

namespace TwoTerminal

theorem copyCalls_chain (initial G : TwoTerminal) (g : FiniteGame G)
    (hg : g.HasOfflinePath (Forward G.depth) G.source G.target) (n : ℕ) :
    Call.Chain (Forward (appendCopies initial G n).depth) (copyCalls initial G g n)
      (initialEmbedding initial G n initial.target) (appendCopies initial G n).target := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Call.Chain.append (ih.map (Series.inl _ G) (forward_series_inl _ G))
    exact ⟨Series.joint _ G, hg.map (Series.inr _ G) (forward_series_inr _ G), rfl⟩

theorem normalizeGame_offline (G : TwoTerminal) (g : FiniteGame G) (L : ℝ) (hL : 0 < L)
    (hg : g.HasOfflinePath (Forward G.depth) G.source G.target) :
    (G.normalizeGame g L hL).HasOfflinePath (Forward (G.normalize L hL).depth)
      (G.normalize L hL).source (G.normalize L hL).target :=
  hg.map (fun x => (⟨x⟩ : ScaledPoint G (L / G.length)))
    (forward_scale G (L / G.length) (div_pos hL G.length_pos))

theorem parallel_threeStage_offline (G : TwoTerminal) (rounds : ℕ)
    {small large : List (Call G)} {u middle : G}
    (hsmall : Call.Chain (Forward G.depth) small u middle)
    (hlarge : Call.Chain (Forward G.depth) large middle G.target) :
    (Requests.threeStage G.parallel.source (Parallel.inl G u) (Parallel.inr G u)
      (small.map (Call.map (Parallel.inl G))) (small.map (Call.map (Parallel.inr G)))
      (large.map (Call.map (Parallel.inl G))) (large.map (Call.map (Parallel.inr G))) rounds
      ).HasOfflinePath (Forward G.parallel.depth) G.parallel.source G.parallel.target := by
  apply Requests.threeStage_offline rounds (forward_refl _)
    (G.parallel.forward_source _) (G.parallel.forward_source _)
    (hsmall.map (Parallel.inl G) (forward_parallel_inl G))
    (hsmall.map (Parallel.inr G) (forward_parallel_inr G))
    (hlarge.map (Parallel.inl G) (forward_parallel_inl G))
  · simpa only [Parallel.joint_target] using!
      hlarge.map (Parallel.inr G) (forward_parallel_inr G)
  · simp only [List.length_map]

theorem stepGame_offline (G : TwoTerminal) (g : FiniteGame G) (m : ℕ) (hm : 0 < m)
    (b : ℝ) (hb : 0 < b) (hg : g.HasOfflinePath (Forward G.depth) G.source G.target) :
    (G.stepGame g m hm b hb).HasOfflinePath (Forward (G.step m hm b hb).depth)
      (G.step m hm b hb).source (G.step m hm b hb).target := by
  unfold stepGame
  apply parallel_threeStage_offline
  · exact (copyCalls_chain _ _ _ (normalizeGame_offline G g _ _ hg) _).map _
      (forward_initialEmbedding _ _ _)
  · exact copyCalls_chain _ _ _ (normalizeGame_offline G g _ _ hg) _

end TwoTerminal

/-- Every realized request sequence admits a source-to-target forward path. -/
theorem recursiveGame_offline (P : GraphParameters) (r : ℕ) :
    (recursiveGame P r).HasOfflinePath (Forward (recursiveGraph P r).depth)
      (recursiveGraph P r).source (recursiveGraph P r).target := by
  induction r with
  | zero =>
    exact Requests.singleton_hasOfflinePath (forward_refl _ _)
      (Requests.singleton_hasOfflinePath (TwoTerminal.edge.forward_target _)
        (fun requests h => h ▸ ServesAlong.nil _))
  | succ r ih => exact TwoTerminal.stepGame_offline _ _ _ _ _ _ ih

/-- The offline upper bound in manuscript Lemma 2, with a concrete feasible
comparator for each realization of the explicitly constructed distribution. -/
theorem recursiveGame_comparator (P : GraphParameters) (r : ℕ)
    (requests : List (Finset (recursiveGraph P r)))
    (hrequests : (recursiveGame P r).Realizes requests) :
    ∃ path : List (recursiveGraph P r),
      List.Forall₂ (fun S z => z ∈ S) requests path ∧
        metricMovement (recursiveGraph P r).source path = (recursiveGraph P r).length := by
  obtain ⟨path, hfeas, hcost⟩ := (recursiveGame_offline P r requests hrequests).exists_path
  exact ⟨path, hfeas, by simpa only [TwoTerminal.depth, dist_self, sub_zero,
    TwoTerminal.length] using! hcost⟩

end ConvexBodyChasing

end
end BundledModule046

/- Component source: ConvexBodyChasing.Norms -/
section BundledModule047
/-! # The norm comparison constants in equation (17) -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped ENNReal BigOperators

namespace ConvexBodyChasing

variable {ι : Type*} [Fintype ι] {p : ℝ≥0∞} [Fact (1 ≤ p)]



/-- The two distortion factors multiply to the dimension, uniformly in the exponent. -/
theorem distortion_product {D : ℝ} (hD : 0 < D) (q : ℝ) :
    D ^ (1 - q) * D ^ q = D := by
  simpa only [sub_add_cancel, Real.rpow_one] using! (Real.rpow_add hD (1 - q) q).symm

/-- Hölder's inequality in exactly the form needed by the online comparison. -/
theorem sum_abs_le_card_mul_lp (hp : p ≠ ∞) (x : PiLp p (fun _ : ι => ℝ)) :
    ∑ i, |x i| ≤ (Fintype.card ι : ℝ) ^ (1 - 1 / p.toReal) * ‖x‖ := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow (Finset.univ : Finset ι) (fun i => x i)
    (show 1 ≤ p.toReal from by simpa using! ENNReal.toReal_mono hp (Fact.out : 1 ≤ p))
  have h' := Real.rpow_le_rpow (by positivity) h
    (le_of_lt (one_div_pos.mpr (p.toReal_pos_iff_ne_top.mpr hp)))
  rw [← Real.rpow_mul (by positivity), mul_one_div_cancel (p.toReal_pos_iff_ne_top.mpr hp).ne',
    Real.rpow_one, Real.mul_rpow (by positivity) (by positivity),
    ← Real.rpow_mul (by positivity)] at h'
  simpa only [sub_mul, mul_one_div_cancel (p.toReal_pos_iff_ne_top.mpr hp).ne', one_mul,
    Finset.card_univ, PiLp.norm_eq_sum (p.toReal_pos_iff_ne_top.mpr hp), Real.norm_eq_abs] using! h'

end ConvexBodyChasing

end
end BundledModule047

/- Component source: ConvexBodyChasing.MappedOffline -/
section BundledModule048
/-! # The mapped offline comparator in the actual ℓ_p space -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped ENNReal
namespace ConvexBodyChasing

def ΨLp (P : GraphParameters) (r : ℕ) (p : ℝ≥0∞) (x : recursiveGraph P r) :
    Space (2 * r + 1) p := WithLp.toLp p (ΨFin P r x)

theorem ΨLp_dist_le (P : GraphParameters) (r : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (x y : recursiveGraph P r) :
    dist (ΨLp P r p x) (ΨLp P r p y) ≤
      ((2 * r + 1 : ℕ) : ℝ) ^ (1 / p.toReal) * dist x y := by
  have h := ((PiLp.lipschitzWith_toLp p (fun _ : Fin (2 * r + 1) => ℝ)).comp
    (ΨFin_lipschitz P r)).dist_le_mul x y
  simpa only [ΨLp, Function.comp_apply, mul_one, Fintype.card_fin, ENNReal.toReal_div,
    ENNReal.toReal_one, NNReal.coe_rpow, NNReal.coe_natCast] using! h

@[simp] theorem ΨLp_source (P : GraphParameters) (r : ℕ) (p : ℝ≥0∞) :
    ΨLp P r p (recursiveGraph P r).source = 0 := by
  simp only [ΨLp, ΨFin_source, WithLp.toLp_zero]

theorem movement_map_le {V E : Type*} [PseudoMetricSpace V] [NormedAddCommGroup E]
    (f : V → E) {C : ℝ} (hf : ∀ x y, dist (f x) (f y) ≤ C * dist x y)
    (start : V) (path : List V) :
    movement (f start) (path.map f) ≤ C * metricMovement start path := by
  induction path generalizing start with
  | nil => simp only [List.map_nil, movement, metricMovement, mul_zero, le_refl]
  | cons x xs ih =>
    simpa only [List.map_cons, movement, metricMovement, mul_add, dist_eq_norm'] using!
      add_le_add (hf start x) (ih x)



theorem mapped_path_feasible {V E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : V → E) {requests : List (Finset V)} {path : List V}
    (h : List.Forall₂ (fun S z => z ∈ S) requests path) :
    List.Forall₂ (fun (S : Finset V) z => z ∈ convexHull ℝ (f '' (S : Set V)))
      requests (path.map f) := by
  induction h with
  | nil => exact .nil
  | cons hmem hrest ih =>
    exact .cons (subset_convexHull ℝ _ (Set.mem_image_of_mem f hmem)) ih



end ConvexBodyChasing

end
end BundledModule048

/- Component source: ConvexBodyChasing.DiscreteLower -/
section BundledModule049
/-! # A quadratic lower bound for the explicit finite games

This theorem concerns the discrete recursive game. `ConvexLower.lean` transfers
its bound to convex strategies, and `Main.lean` proves the randomized result.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing

theorem recursiveGame_escape_bound (r : ℕ) :
    (⟨(recursiveGraph lowerBoundParameters r).source,
      (recursiveGraph lowerBoundParameters r).target, recursiveGame lowerBoundParameters r⟩ :
        Call (recursiveGraph lowerBoundParameters r)).EscapeBound
      (discreteRate r * (recursiveGraph lowerBoundParameters r).length)
      (2 * discreteRate r * (recursiveGraph lowerBoundParameters r).length) := by
  induction r with
  | zero =>
    refine ⟨recursiveGame_starts lowerBoundParameters 0, ?_⟩
    have hedge : dist TwoTerminal.edge.source TwoTerminal.edge.target = 1 := TwoTerminal.length_edge
    norm_num [recursiveGame, recursiveGraph, discreteRate, Requests.singleton,
      FiniteGame.escapeEval, Finset.inf'_singleton, hedge]
  | succ r ih =>
    refine ⟨recursiveGame_starts lowerBoundParameters (r + 1), ?_⟩
    have hstep := TwoTerminal.stepGame_escape_lower (recursiveGraph lowerBoundParameters r)
      (recursiveGame lowerBoundParameters r) (discreteCopies r) (discreteCopies_pos r)
      (discreteRate r) (discreteRate_pos r) (discreteRate_le_copies r) ih
      (recursiveGraph lowerBoundParameters (r + 1)).source
    have hrate : discreteRate (r + 1) * (recursiveGraph lowerBoundParameters (r + 1)).length ≤
        (3 * discreteCopies r + Real.sqrt (discreteCopies r) / 4) * discreteRate r := by
      simpa only [recursiveGraph_length_succ, lowerBoundParameters] using! discreteRate_step r
    have hprice : 6 * discreteCopies r * discreteRate r ≤
        2 * discreteRate (r + 1) * (recursiveGraph lowerBoundParameters (r + 1)).length := by
      simpa only [recursiveGraph_length_succ, lowerBoundParameters] using! discreteRate_escapePrice r
    exact hrate.trans (hstep.trans (FiniteGame.escapeEval_mono_price _ hprice _))

/-- Every strategy, even one observing all past coin flips, pays the stated
quadratic factor times the terminal distance in the explicit finite game. -/
theorem recursiveGame_strategy_lower (r : ℕ)
    (π : FiniteGame.Strategy (recursiveGame lowerBoundParameters r))
    (x : recursiveGraph lowerBoundParameters r) :
    discreteRate r * (recursiveGraph lowerBoundParameters r).length ≤
      FiniteGame.strategyCost (fun _ => 0) (recursiveGame lowerBoundParameters r) π x :=
  ((recursiveGame_escape_bound r).all_starts x).trans
    ((FiniteGame.escapeEval_le_eval _ _ x).trans (FiniteGame.eval_le_strategyCost _ _ π x))

theorem recursiveGame_quadratic_lower (r : ℕ)
    (π : FiniteGame.Strategy (recursiveGame lowerBoundParameters r))
    (x : recursiveGraph lowerBoundParameters r) :
    ((r : ℝ) ^ 2 / 1000000) * (recursiveGraph lowerBoundParameters r).length ≤
      FiniteGame.strategyCost (fun _ => 0) (recursiveGame lowerBoundParameters r) π x := by
  apply le_trans (mul_le_mul_of_nonneg_right ?_ (recursiveGraph lowerBoundParameters r).length_pos.le)
    (recursiveGame_strategy_lower r π x)
  unfold discreteRate
  nlinarith [Nat.cast_nonneg (α := ℝ) r]



end ConvexBodyChasing

end
end BundledModule049

/- Component source: ConvexBodyChasing.Outcomes -/
section BundledModule050
/-! # The finite probability space of oblivious request sequences

An outcome fixes every coin on the branch that it follows. Its weight is the
product of the fair-coin probabilities on that branch. The outcome space and
its law depend only on the request tree, never on an online algorithm.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators
namespace ConvexBodyChasing.FiniteGame
variable {V : Type*}

def Outcome : FiniteGame V → Type
  | .stop => Unit
  | .request _ _ next => Outcome next
  | .coin left right => Outcome left ⊕ Outcome right

instance outcomeFintype : (game : FiniteGame V) → Fintype game.Outcome
  | .stop => inferInstanceAs (Fintype Unit)
  | .request _ _ next => outcomeFintype next
  | .coin left right =>
    letI := outcomeFintype left
    letI := outcomeFintype right
    inferInstanceAs (Fintype (Outcome left ⊕ Outcome right))

def outcomeWeight : (game : FiniteGame V) → game.Outcome → ℝ
  | .stop, _ => 1
  | .request _ _ next, ω => outcomeWeight next ω
  | .coin left _, .inl ω => outcomeWeight left ω / 2
  | .coin _ right, .inr ω => outcomeWeight right ω / 2

theorem outcomeWeight_nonneg (game : FiniteGame V) (ω : game.Outcome) :
    0 ≤ game.outcomeWeight ω := by
  induction game with
  | stop => exact zero_le_one
  | request _ _ _ ih => exact ih ω
  | coin left right ihl ihr =>
    cases ω with
    | inl ω => exact div_nonneg (ihl ω) (by norm_num)
    | inr ω => exact div_nonneg (ihr ω) (by norm_num)

theorem outcomeWeight_total (game : FiniteGame V) :
    ∑ ω, game.outcomeWeight ω = 1 := by
  induction game with
  | stop => simp [Outcome, outcomeWeight]
  | request _ _ _ ih => exact ih
  | coin left right ihl ihr =>
    change (∑ ω : Outcome left ⊕ Outcome right, _) = 1
    norm_num [Fintype.sum_sum_type, outcomeWeight, ← Finset.sum_div, ihl, ihr]

def outcomeAverage (game : FiniteGame V) (f : game.Outcome → ℝ) : ℝ :=
  ∑ ω, game.outcomeWeight ω * f ω



@[simp] theorem outcomeAverage_request (S : Finset V) (hS : S.Nonempty) (game : FiniteGame V)
    (f : game.Outcome → ℝ) : outcomeAverage (.request S hS game) f = outcomeAverage game f := rfl

theorem outcomeAverage_coin (left right : FiniteGame V) (f : Outcome (.coin left right) → ℝ) :
    outcomeAverage (.coin left right) f =
      (left.outcomeAverage (fun ω => f (.inl ω)) +
        right.outcomeAverage (fun ω => f (.inr ω))) / 2 := by
  simp [outcomeAverage, Outcome, Fintype.sum_sum_type, outcomeWeight,
    div_mul_eq_mul_div, ← Finset.sum_div, add_div]



@[simp] theorem outcomeAverage_const (game : FiniteGame V) (c : ℝ) :
    game.outcomeAverage (fun _ => c) = c := by
  simp [outcomeAverage, ← Finset.sum_mul, outcomeWeight_total]

theorem outcomeAverage_add (game : FiniteGame V) (f g : game.Outcome → ℝ) :
    game.outcomeAverage (fun ω => f ω + g ω) = game.outcomeAverage f + game.outcomeAverage g := by
  simp [outcomeAverage, mul_add, Finset.sum_add_distrib]

theorem outcomeAverage_const_add (game : FiniteGame V) (c : ℝ) (f : game.Outcome → ℝ) :
    game.outcomeAverage (fun ω => c + f ω) = c + game.outcomeAverage f := by
  simpa only [outcomeAverage_const] using! game.outcomeAverage_add (fun _ => c) f



def outcomeRequests : (game : FiniteGame V) → game.Outcome → List (Finset V)
  | .stop, _ => []
  | .request S _ next, ω => S :: next.outcomeRequests ω
  | .coin left _, .inl ω => left.outcomeRequests ω
  | .coin _ right, .inr ω => right.outcomeRequests ω

theorem outcomeRequests_realizes (game : FiniteGame V) (ω : game.Outcome) :
    game.Realizes (game.outcomeRequests ω) := by
  induction game with
  | stop => rfl
  | request S hS game ih => exact ⟨_, rfl, ih ω⟩
  | coin left right ihl ihr =>
    cases ω with
    | inl ω => exact Or.inl (ihl ω)
    | inr ω => exact Or.inr (ihr ω)

end ConvexBodyChasing.FiniteGame

end
end BundledModule050

/- Component source: ConvexBodyChasing.OnlineTree -/
section BundledModule051
/-! # Running a history-based online algorithm on the oblivious tree -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing.FiniteGame
variable {V E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def outcomeBodies (φ : V → E) : (game : FiniteGame V) → game.Outcome → List (Body E)
  | .stop, _ => []
  | .request S hS next, ω => Body.ofFinset φ S hS :: next.outcomeBodies φ ω
  | .coin left _, .inl ω => left.outcomeBodies φ ω
  | .coin _ right, .inr ω => right.outcomeBodies φ ω



/-- This strategy uses only requests already revealed, as required by `OnlineAlgorithm`. -/
def algorithmStrategy (φ : V → E) (A : OnlineAlgorithm E) :
    (game : FiniteGame V) → List (Body E) → ConvexStrategy φ game
  | .stop, _ => PUnit.unit
  | .request S hS next, history =>
    let K := Body.ofFinset φ S hS
    (⟨(A history K).val, (A history K).property⟩,
      algorithmStrategy φ A next (history ++ [K]))
  | .coin left right, history =>
    (algorithmStrategy φ A left history, algorithmStrategy φ A right history)

theorem convexCost_algorithmStrategy (φ : V → E) (A : OnlineAlgorithm E)
    (game : FiniteGame V) (history : List (Body E)) (start : E) :
    convexCost φ game (algorithmStrategy φ A game history) start =
      game.outcomeAverage (fun ω => movement start (trajectory A history (game.outcomeBodies φ ω))) := by
  induction game generalizing history start with
  | stop => simp [convexCost, outcomeBodies, trajectory, movement]
  | request S hS game ih =>
    simp only [convexCost, algorithmStrategy, outcomeBodies, trajectory, movement, outcomeAverage_request]
    dsimp only [Outcome]
    simp only [outcomeAverage_const_add, ih, dist_eq_norm']
  | coin left right ihl ihr =>
    simp only [convexCost, algorithmStrategy, outcomeAverage_coin, outcomeBodies, ihl, ihr]

theorem outcomeBodies_serves (φ : V → E) (game : FiniteGame V) (ω : game.Outcome)
    {path : List E} (h : List.Forall₂ (fun (S : Finset V) x =>
      x ∈ convexHull ℝ (φ '' (↑S : Set V))) (game.outcomeRequests ω) path) :
    Serves (game.outcomeBodies φ ω) path := by
  induction game generalizing path with
  | stop => cases h; exact .nil
  | request S hS game ih =>
    cases h with
    | cons hx hxs => exact .cons hx (ih ω hxs)
  | coin left right ihl ihr =>
    cases ω with
    | inl ω => exact ihl ω h
    | inr ω => exact ihr ω h

end ConvexBodyChasing.FiniteGame

end
end BundledModule051

/- Component source: ConvexBodyChasing.ConvexLower -/
section BundledModule052
/-! # The lower bound for every strategy on the convexified finite tree

This module discharges the geometric premises of the Bellman comparison for
the explicit recursive construction in every finite ℓ_p norm.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators ENNReal
namespace ConvexBodyChasing
local instance convexLowerDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance convexLowerFintype (G : TwoTerminal) : Fintype G := Fintype.ofFinite G

theorem pairing_ΨLp (P : GraphParameters) (r : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (μ : recursiveGraph P r → ℝ) (i : Fin (2 * r + 1)) :
    (∑ v, μ v • ΨLp P r p v) i =
      SignedMass.pairing μ (fun v => Ψ P r v ((coordinateEquiv r).symm i)) := by
  simp [ΨLp, ΨFin, SignedMass.pairing]

theorem sum_abs_pairing_ΨLp (P : GraphParameters) (r : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (μ : recursiveGraph P r → ℝ) :
    ∑ i : Coordinate r, |SignedMass.pairing μ (fun v => Ψ P r v i)| =
      ∑ i : Fin (2 * r + 1), |(∑ v, μ v • ΨLp P r p v) i| := by
  simpa only [pairing_ΨLp] using!
    ((coordinateEquiv r).symm.sum_comp
      (fun i => |SignedMass.pairing μ (fun v => Ψ P r v i)|)).symm

theorem lowerBoundGame_dual_steps (r : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    FiniteGame.TransitionChain
      (DualStep (ΨLp lowerBoundParameters r p)
        (8 * ((2 * r + 1 : ℕ) : ℝ) ^ (1 - 1 / p.toReal)))
      (recursiveGame lowerBoundParameters r)
      {(recursiveGraph lowerBoundParameters r).source}
      {(recursiveGraph lowerBoundParameters r).target} := by
  apply (lowerBoundGame_coordinate_tests r).mono
  intro S T h μ f hμ hs hf
  obtain ⟨test⟩ := h f hf
  have htest := test.abs_pairing_le μ hμ hs
  rw [← Ψ_eq_fullCoords, sum_abs_pairing_ΨLp lowerBoundParameters r p] at htest
  exact htest.trans (by simpa only [Fintype.card_fin, mul_assoc] using!
    mul_le_mul_of_nonneg_left (sum_abs_le_card_mul_lp hp
      (∑ v, μ v • ΨLp lowerBoundParameters r p v)) (show (0 : ℝ) ≤ 8 by norm_num))

theorem recursiveGame_eval_quadratic_lower (r : ℕ) (x : recursiveGraph lowerBoundParameters r) :
    ((r : ℝ) ^ 2 / 1000000) * (recursiveGraph lowerBoundParameters r).length ≤
      FiniteGame.eval (fun _ => 0) (recursiveGame lowerBoundParameters r) x := by
  obtain ⟨optimal, hoptimal⟩ := FiniteGame.exists_optimal_strategy.{0, 0}
    (recursiveGame lowerBoundParameters r) (fun _ => 0) x
  exact (recursiveGame_quadratic_lower r optimal x).trans hoptimal.le







end ConvexBodyChasing

end
end BundledModule052

/- Component source: ConvexBodyChasing.RandomizedTree -/
section BundledModule053
/-! # Averaging the finite oblivious tree over an arbitrary random seed

All expectations use the extended nonnegative integral, including when a
randomized algorithm has infinite expected movement.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace ConvexBodyChasing
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]





namespace FiniteGame
variable {V : Type*}

def outcomeExpectation (game : FiniteGame V) (f : game.Outcome → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ ω, ENNReal.ofReal (game.outcomeWeight ω) * f ω

theorem ofReal_outcomeAverage (game : FiniteGame V) (f : game.Outcome → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) :
    ENNReal.ofReal (game.outcomeAverage f) = game.outcomeExpectation (fun ω => ENNReal.ofReal (f ω)) := by
  rw [outcomeAverage, ENNReal.ofReal_sum_of_nonneg
    (fun ω _ => mul_nonneg (game.outcomeWeight_nonneg ω) (hf ω))]
  simp only [outcomeExpectation, ENNReal.ofReal_mul (game.outcomeWeight_nonneg _)]

@[simp] theorem outcomeExpectation_const (game : FiniteGame V) (c : ℝ≥0∞) :
    game.outcomeExpectation (fun _ => c) = c := by
  rw [outcomeExpectation, ← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg
    (fun ω _ => game.outcomeWeight_nonneg ω), outcomeWeight_total]
  simp

theorem outcomeExpectation_mono (game : FiniteGame V) {f g : game.Outcome → ℝ≥0∞}
    (h : ∀ ω, f ω ≤ g ω) : game.outcomeExpectation f ≤ game.outcomeExpectation g := by
  exact Finset.sum_le_sum (fun ω _ => mul_le_mul_right (h ω) _)

theorem outcomeExpectation_le (game : FiniteGame V) {f : game.Outcome → ℝ≥0∞} {c : ℝ≥0∞}
    (h : ∀ ω, f ω ≤ c) : game.outcomeExpectation f ≤ c := by
  simpa only [outcomeExpectation_const] using! game.outcomeExpectation_mono h

theorem lintegral_outcomeAverage (game : FiniteGame V) (φ : V → E)
    (A : RandomizedOnlineAlgorithm E) (start : E) :
    (∫⁻ seed, ENNReal.ofReal (game.outcomeAverage (fun ω =>
      cost (A.algorithm seed) start (game.outcomeBodies φ ω))) ∂A.law) =
      game.outcomeExpectation (fun ω => expectedCost A start (game.outcomeBodies φ ω)) := by
  have heq (seed : A.Seed) : ENNReal.ofReal (game.outcomeAverage (fun ω =>
      cost (A.algorithm seed) start (game.outcomeBodies φ ω))) =
      game.outcomeExpectation (fun ω => ENNReal.ofReal
        (cost (A.algorithm seed) start (game.outcomeBodies φ ω))) :=
    game.ofReal_outcomeAverage _ (fun _ => movement_nonneg _ _)
  simp_rw [heq, outcomeExpectation]
  rw [lintegral_finsetSum (f := fun ω seed => ENNReal.ofReal (game.outcomeWeight ω) *
      ENNReal.ofReal (cost (A.algorithm seed) start (game.outcomeBodies φ ω))) _
    (fun ω _ => measurable_const.mul
    (A.measurable_cost start (game.outcomeBodies φ ω)).ennreal_ofReal)]
  simp only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, expectedCost]

/-- Pointwise deterministic lower bounds survive arbitrary independent seed randomization. -/
theorem randomized_lower_of_online (game : FiniteGame V) (φ : V → E)
    (start : E) {L C : ℝ} (hC : 0 ≤ C)
    (hlower : ∀ B : OnlineAlgorithm E, L ≤ C * game.outcomeAverage
      (fun ω => cost B start (game.outcomeBodies φ ω)))
    (A : RandomizedOnlineAlgorithm E) :
    ENNReal.ofReal L ≤ ENNReal.ofReal C *
      game.outcomeExpectation (fun ω => expectedCost A start (game.outcomeBodies φ ω)) := by
  have h := lintegral_mono (μ := A.law) (fun seed =>
    ENNReal.ofReal_le_ofReal (hlower (A.algorithm seed)))
  simpa only [ENNReal.ofReal_mul hC, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_outcomeAverage, lintegral_const, measure_univ, mul_one] using! h

/-- A finite oblivious distribution lower-bounds the competitive ratio. The
ratio is allowed to be any real number; nonnegativity is not assumed. -/
theorem randomized_comparison (game : FiniteGame V) (φ : V → E) (start : E)
    {L C B R : ℝ} (hL : 0 < L) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hlower : ∀ D : OnlineAlgorithm E, L ≤ C * game.outcomeAverage
      (fun ω => cost D start (game.outcomeBodies φ ω)))
    (hoffline : ∀ ω, ∃ path, Serves (game.outcomeBodies φ ω) path ∧ movement start path ≤ B)
    (A : RandomizedOnlineAlgorithm E) (hcomp : RandomizedCompetitive A start R) :
    L ≤ C * R * B := by
  have hupper : game.outcomeExpectation (fun ω => expectedCost A start (game.outcomeBodies φ ω)) ≤
      ENNReal.ofReal R * ENNReal.ofReal B := by
    apply game.outcomeExpectation_le
    intro ω
    obtain ⟨path, hpath, hcost⟩ := hoffline ω
    exact (hcomp _ path hpath).trans (by
      simpa only [ENNReal.ofReal_mul' (movement_nonneg start path)] using!
        mul_le_mul_right (ENNReal.ofReal_le_ofReal hcost) (ENNReal.ofReal R))
  have h := (game.randomized_lower_of_online φ start hC hlower A).trans
    (mul_le_mul_right hupper (ENNReal.ofReal C))
  rw [← ENNReal.ofReal_mul' hB, ← ENNReal.ofReal_mul hC, ENNReal.ofReal_le_ofReal_iff'] at h
  simpa only [mul_assoc] using! h.resolve_right (not_le.mpr hL)

end FiniteGame

end ConvexBodyChasing

end
end BundledModule053

/- Component source: ConvexBodyChasing.IsometricLower -/
section BundledModule055
/-! # Transporting the concrete lower bound along a linear isometry -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped ENNReal BigOperators
namespace ConvexBodyChasing

variable {V E F : Type*} [Fintype V] [MetricSpace V] [DecidableEq V]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem DualStep.linearIsometry {φ : V → E} {C : ℝ} {S T : Finset V}
    (h : DualStep φ C S T) (L : E →ₗᵢ[ℝ] F) : DualStep (fun v => L (φ v)) C S T := by
  intro μ f hμ hs hf
  simpa only [← L.map_smul, ← map_sum, L.norm_map] using! h μ f hμ hs hf

local instance isometricLowerDecidableEq (α : Type*) : DecidableEq α := Classical.decEq α
local instance isometricLowerFintype (G : TwoTerminal) : Fintype G := Fintype.ofFinite G

theorem isometric_game_online_bound (r : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (L : Space (2 * r + 1) p →ₗᵢ[ℝ] F) (A : OnlineAlgorithm F) :
    ((r : ℝ) ^ 2 / 1000000) * (recursiveGraph lowerBoundParameters r).length ≤
      (8 * ((2 * r + 1 : ℕ) : ℝ) ^ (1 - 1 / p.toReal)) *
        (recursiveGame lowerBoundParameters r).outcomeAverage (fun ω => cost A 0
          ((recursiveGame lowerBoundParameters r).outcomeBodies (fun v => L (ΨLp lowerBoundParameters r p v)) ω)) := by
  have hchain := (lowerBoundGame_dual_steps r p hp).mono (fun _ _ h => h.linearIsometry L)
  have hcompare := FiniteGame.eval_le_convexCost _ _ _ hchain
    (FiniteGame.algorithmStrategy.{0, _, 0} (fun v => L (ΨLp lowerBoundParameters r p v)) A
      (recursiveGame lowerBoundParameters r) [])
  have htotal := (recursiveGame_eval_quadratic_lower r _).trans hcompare
  simpa only [ΨLp_source, map_zero, FiniteGame.convexCost_algorithmStrategy, cost] using! htotal

theorem isometric_game_offline_bound (r : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (L : Space (2 * r + 1) p →ₗᵢ[ℝ] F) (ω : (recursiveGame lowerBoundParameters r).Outcome) :
    ∃ path : List F,
      Serves ((recursiveGame lowerBoundParameters r).outcomeBodies
        (fun v => L (ΨLp lowerBoundParameters r p v)) ω) path ∧
      movement 0 path ≤ ((2 * r + 1 : ℕ) : ℝ) ^ (1 / p.toReal) *
        (recursiveGraph lowerBoundParameters r).length := by
  obtain ⟨path, hpath, hcost⟩ := recursiveGame_comparator lowerBoundParameters r _
    ((recursiveGame lowerBoundParameters r).outcomeRequests_realizes ω)
  refine ⟨path.map (fun v => L (ΨLp lowerBoundParameters r p v)),
    FiniteGame.outcomeBodies_serves _ _ _ (mapped_path_feasible _ hpath), ?_⟩
  have hdist (x y : recursiveGraph lowerBoundParameters r) :
      dist (L (ΨLp lowerBoundParameters r p x)) (L (ΨLp lowerBoundParameters r p y)) ≤
        ((2 * r + 1 : ℕ) : ℝ) ^ (1 / p.toReal) * dist x y := by
    simpa only [L.dist_map] using! ΨLp_dist_le lowerBoundParameters r p x y
  simpa only [ΨLp_source, map_zero, hcost] using! movement_map_le
    (fun v => L (ΨLp lowerBoundParameters r p v)) hdist (recursiveGraph lowerBoundParameters r).source path

theorem isometric_randomized_comparison [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (r : ℕ) (hr : 1 ≤ r) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (L : Space (2 * r + 1) p →ₗᵢ[ℝ] F)
    (A : RandomizedOnlineAlgorithm F) (R : ℝ) (hcomp : RandomizedCompetitive A 0 R) :
    (r : ℝ) ^ 2 / 1000000 ≤ 8 * ((2 * r + 1 : ℕ) : ℝ) * R := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hlen := (recursiveGraph lowerBoundParameters r).length_pos
  have hbound := FiniteGame.randomized_comparison (recursiveGame lowerBoundParameters r)
    (fun v => L (ΨLp lowerBoundParameters r p v)) 0 (by positivity) (by positivity) (by positivity)
    (isometric_game_online_bound r p hp L) (isometric_game_offline_bound r p L) A hcomp
  have hprod := distortion_product (show (0 : ℝ) < ((2 * r + 1 : ℕ) : ℝ) by positivity)
    (1 / p.toReal)
  apply (mul_le_mul_iff_of_pos_right hlen).mp
  nlinarith only [hbound, congrArg (fun x => 8 * x * R * (recursiveGraph lowerBoundParameters r).length) hprod]

end ConvexBodyChasing

end
end BundledModule055

/- Component source: ConvexBodyChasing.Padding -/
section BundledModule056
/-! # Zero-padding in finite ℓ_p spaces -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped ENNReal BigOperators
namespace ConvexBodyChasing

def appendZeros (n m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Space n p →ₗᵢ[ℝ] Space (n + m) p where
  toFun x := WithLp.toLp p (Fin.append (fun i => x i) (fun _ : Fin m => (0 : ℝ)))
  map_add' x y := by
    ext i
    refine Fin.addCases ?_ ?_ i
    · simp
    · simp
  map_smul' c x := by
    ext i
    refine Fin.addCases ?_ ?_ i <;> simp
  norm_map' x := by
    change ‖WithLp.toLp p (Fin.append (fun i => x i) (fun _ : Fin m => (0 : ℝ)))‖ = ‖x‖
    simp only [PiLp.norm_eq_sum (p.toReal_pos_iff_ne_top.mpr hp), Fin.sum_univ_add,
      Fin.append_left, Fin.append_right, norm_zero,
      Real.zero_rpow (p.toReal_pos_iff_ne_top.mpr hp).ne', Finset.sum_const_zero, add_zero]

/-- A linear isometry into any larger finite ℓ_p space, obtained by zero-padding. -/
def dimensionEmbedding {n d : ℕ} (h : n ≤ d) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    Space n p →ₗᵢ[ℝ] Space d p :=
  (LinearIsometryEquiv.piLpCongrLeft p ℝ ℝ (finCongr (Nat.add_sub_of_le h))).toLinearIsometry.comp
    (appendZeros n (d - n) p hp)

end ConvexBodyChasing

end
end BundledModule056

/- Component source: ConvexBodyChasing.Dimension -/
section BundledModule057
/-! # Dimension bookkeeping for Theorem 1 -/

namespace ConvexBodyChasing

/-- The recursion level used to fit the construction in dimension `d`. -/
def level (d : ℕ) : ℕ := (d - 1) / 2

theorem level_bounds {d : ℕ} (hd : 3 ≤ d) :
    1 ≤ level d ∧ 2 * level d + 1 ≤ d ∧ d ≤ 4 * level d := by
  unfold level
  omega

/-- The last numerical step of Theorem 1, with the universal constant made explicit.
This lemma is only arithmetic; `Main.lean` discharges its premise using the
constructed distribution and the randomized online comparison. -/
theorem linear_bound_of_quadratic {d : ℕ} (hd : 3 ≤ d) {c R : ℝ} (hc : 0 < c)
    (h : c * (level d : ℝ) ^ 2 ≤ 8 * (2 * (level d : ℝ) + 1) * R) :
    c / 128 * d ≤ R := by
  obtain ⟨hr, hD, hdim⟩ := level_bounds hd
  have hr' : (1 : ℝ) ≤ level d := by exact_mod_cast hr
  have hD' : 2 * (level d : ℝ) + 1 ≤ d := by exact_mod_cast hD
  have hdim' : (d : ℝ) ≤ 4 * level d := by exact_mod_cast hdim
  apply (mul_le_mul_iff_of_pos_left (show 0 < 8 * (2 * (level d : ℝ) + 1) by positivity)).mp
  have hprod := mul_le_mul hdim'
    (show 2 * (level d : ℝ) + 1 ≤ 4 * level d by linarith) (by positivity) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hprod hc.le]

end ConvexBodyChasing

end BundledModule057

/- Component source: ConvexBodyChasing.Main -/
section BundledModule058
/-! # Linear lower bound for convex body chasing in every finite ℓ_p norm

The public theorem has only the dimension, exponent, and competitive-guarantee
assumptions. The recursive construction, both cost estimates, the probability
bridge, and dimension padding are all proved in its dependency chain.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped ENNReal
namespace ConvexBodyChasing

/-- Every randomized online algorithm in dimension `d ≥ 3`, for every
`1 ≤ p < ∞`, has competitive ratio at least `d / 128000000`. -/
theorem competitive_ratio_linear_lower_bound (d : ℕ) (hd : 3 ≤ d)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (A : RandomizedOnlineAlgorithm (Space d p)) (R : ℝ)
    (hcomp : RandomizedCompetitive A 0 R) : (d : ℝ) / 128000000 ≤ R := by
  have h := isometric_randomized_comparison (level d) (level_bounds hd).1 p hp
    (dimensionEmbedding (level_bounds hd).2.1 p hp) A R hcomp
  have hquad : (1 / 1000000 : ℝ) * (level d : ℝ) ^ 2 ≤
      8 * (2 * (level d : ℝ) + 1) * R := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      div_eq_mul_inv, one_mul, mul_comm] using! h
  convert! linear_bound_of_quadratic hd (show (0 : ℝ) < 1 / 1000000 by norm_num) hquad using 1
  ring



end ConvexBodyChasing

end
end BundledModule058

end CBCProve2MeProofs.FiniteLp

open scoped ENNReal
open ConvexBodyChasing

theorem solution (d : ℕ) (hd : 3 ≤ d)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (A : RandomizedOnlineAlgorithm (Space d p)) (R : ℝ)
    (hcomp : RandomizedCompetitive A 0 R) : (d : ℝ) / 128000000 ≤ R := by
  exact CBCProve2MeProofs.FiniteLp.ConvexBodyChasing.competitive_ratio_linear_lower_bound
    d hd p hp A R hcomp
