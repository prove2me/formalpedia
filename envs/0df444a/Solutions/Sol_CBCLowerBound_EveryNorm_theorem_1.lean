-- Prove2me | solution 1 for CBCLowerBound.EveryNorm.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @nhc
-- created : 2026-11-13T13:51:50.552146+00:00
-- url     : https://prove2.me/submissions/e6e65be5-3cd5-4099-b212-c4ea794fcf58

import Definitions.Def_CBCCompactChasingModel
import Definitions.Def_CBCLowerBound_EveryNorm_Chasing
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.List.Forall2
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.OrderClosed
import Theorems.Thm_CBCLowerBound_EveryNorm_lemma_10
import Theorems.Thm_ConvexBodyChasing_competitive_ratio_linear_lower_bound

set_option autoImplicit false

/- Component source: ConvexBodyChasing.QuotientGeometry -/
section BundledModule104
/-! # Geometry of the quotient lifting in the all-norms extension

These lemmas prove the elementary lifting step from the two unit-ball inclusions.
They do not assert the existence of a Milman quotient.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ConvexBodyChasing

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The first unit-ball inclusion gives a norm-controlled lift of every vector. -/
theorem exists_lift_norm_le (Q : E →L[ℝ] F)
    (hball : Metric.closedBall 0 1 ⊆ Q '' Metric.closedBall 0 1) (y : F) :
    ∃ x : E, Q x = y ∧ ‖x‖ ≤ ‖y‖ := by
  by_cases hy : y = 0
  · subst y
    exact ⟨0, Q.map_zero, by simp⟩
  · obtain ⟨x, hx, hQx⟩ := hball (show ‖y‖⁻¹ • y ∈ Metric.closedBall 0 1 by
      simp [Metric.mem_closedBall, norm_smul, hy])
    refine ⟨‖y‖ • x, by simp [hQx, smul_smul, hy], ?_⟩
    simpa only [norm_smul, Real.norm_of_nonneg (norm_nonneg y), mul_one] using!
      mul_le_mul_of_nonneg_left (show ‖x‖ ≤ 1 by simpa using! hx) (norm_nonneg y)

/-- Lift successive movements, not independently chosen positions. -/
theorem exists_lift_path (Q : E →L[ℝ] F)
    (hlift : ∀ y : F, ∃ x : E, Q x = y ∧ ‖x‖ ≤ ‖y‖)
    (start : E) (path : List F) :
    ∃ lifted : List E, lifted.map Q = path ∧
      movement start lifted ≤ movement (Q start) path := by
  induction path generalizing start with
  | nil => exact ⟨[], rfl, le_rfl⟩
  | cons y ys ih =>
    obtain ⟨v, hv, hnorm⟩ := hlift (y - Q start)
    obtain ⟨zs, hzs, hcost⟩ := ih (start + v)
    refine ⟨(start + v) :: zs, by simp [hzs, hv], ?_⟩
    simpa [movement, hv] using! add_le_add hnorm hcost

omit [NormedSpace ℝ E] in
/-- Every visited point is bounded by the starting norm plus the whole path cost. -/
theorem norm_le_norm_add_movement (start : E) (path : List E) {z : E} (hz : z ∈ path) :
    ‖z‖ ≤ ‖start‖ + movement start path := by
  induction path generalizing start with
  | nil => simp at hz
  | cons y ys ih =>
    have hy : ‖y‖ ≤ ‖start‖ + ‖y - start‖ := by
      simpa only [sub_add_cancel] using!
        (norm_add_le (y - start) start).trans_eq (add_comm ‖y - start‖ ‖start‖)
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hy.trans (add_le_add le_rfl
        (le_add_of_nonneg_right (movement_nonneg z ys)))
    · simpa only [movement, add_assoc] using!
        (ih y hz).trans (add_le_add hy (le_refl (movement y ys)))

/-- A path of cost at most `B` lifts inside the radius-`B` ball with no extra cost. -/
theorem exists_lift_path_in_ball (Q : E →L[ℝ] F)
    (hball : Metric.closedBall 0 1 ⊆ Q '' Metric.closedBall 0 1)
    (path : List F) {B : ℝ} (hcost : movement 0 path ≤ B) :
    ∃ lifted : List E, lifted.map Q = path ∧
      movement 0 lifted ≤ movement 0 path ∧
      ∀ z ∈ lifted, z ∈ Metric.closedBall 0 B := by
  obtain ⟨lifted, hmap, hlift⟩ := exists_lift_path Q (exists_lift_norm_le Q hball) 0 path
  refine ⟨lifted, hmap, by simpa using! hlift, fun z hz => ?_⟩
  simpa using! (norm_le_norm_add_movement 0 lifted hz).trans
    (show ‖(0 : E)‖ + movement 0 lifted ≤ B by
      simpa using! hlift.trans (by simpa using! hcost))

/-- The second unit-ball inclusion bounds the cost of projection. -/
theorem norm_map_le_of_ball_image_subset (Q : E →L[ℝ] F) {M : ℝ} (hM : 0 ≤ M)
    (hball : Q '' Metric.closedBall 0 1 ⊆ Metric.closedBall 0 M) (x : E) :
    ‖Q x‖ ≤ M * ‖x‖ := by
  exact Q.le_of_opNorm_le (ContinuousLinearMap.opNorm_le_of_unit_norm hM
    (fun z hz => by simpa using! hball ⟨z, by simp [hz], rfl⟩)) x

/-- Restricting a closed convex preimage to a ball gives a compact request. -/
def Body.boundedPreimage [ProperSpace E] (K : Body F) (Q : E →L[ℝ] F) (B : ℝ)
    (hne : (Metric.closedBall 0 B ∩ Q ⁻¹' (K : Set F)).Nonempty) : Body E where
  carrier := Metric.closedBall 0 B ∩ Q ⁻¹' (K : Set F)
  nonempty := hne
  compact := (isCompact_closedBall 0 B).inter_right (K.compact.isClosed.preimage Q.continuous)
  convex := (convex_closedBall (0 : E) B).inter (K.convex.linear_preimage Q.toLinearMap)

/-- The projected trajectory costs at most the operator's norm bound times the original. -/
theorem movement_map_le_of_norm_bound (Q : E →L[ℝ] F) {M : ℝ}
    (hQ : ∀ x, ‖Q x‖ ≤ M * ‖x‖) (start : E) (path : List E) :
    movement (Q start) (path.map Q) ≤ M * movement start path := by
  induction path generalizing start with
  | nil => simp [movement]
  | cons x xs ih =>
    simpa only [List.map_cons, movement, ← Q.map_sub, mul_add] using!
      add_le_add (hQ (x - start)) (ih x)

/-- The bounded preimages admit an offline path with the original cost bound. -/
theorem exists_lifted_serving_path (Q : E →L[ℝ] F)
    (hball : Metric.closedBall 0 1 ⊆ Q '' Metric.closedBall 0 1)
    {requests : List (Body F)} {path : List F} (hserves : Serves requests path)
    {B : ℝ} (hcost : movement 0 path ≤ B) :
    ∃ lifted : List E,
      List.Forall₂ (fun (K : Body F) x => x ∈ Metric.closedBall 0 B ∧ Q x ∈ K)
        requests lifted ∧ movement 0 lifted ≤ movement 0 path := by
  obtain ⟨lifted, hmap, hlift, hmem⟩ := exists_lift_path_in_ball Q hball path hcost
  refine ⟨lifted, ?_, hlift⟩
  apply List.Forall₂.flip
  refine (List.forall₂_and_left lifted requests).mpr ⟨hmem, ?_⟩
  exact (List.forall₂_map_right_iff (R := fun (K : Body F) y => y ∈ K) (f := Q) |>.mp
    (show List.Forall₂ (fun (K : Body F) y => y ∈ K) requests (lifted.map Q) from
      hmap.symm ▸ hserves)).flip

/-- Every request on a path of cost at most `B` has a nonempty bounded preimage. -/
theorem bounded_preimages_nonempty (Q : E →L[ℝ] F)
    (hball : Metric.closedBall 0 1 ⊆ Q '' Metric.closedBall 0 1)
    {requests : List (Body F)} {path : List F} (hserves : Serves requests path)
    {B : ℝ} (hcost : movement 0 path ≤ B) :
    ∀ K ∈ requests, (Metric.closedBall 0 B ∩ Q ⁻¹' (K : Set F)).Nonempty := by
  obtain ⟨lifted, hrel, _⟩ := exists_lifted_serving_path Q hball hserves hcost
  exact (List.forall₂_and_left (R := fun (K : Body F) x =>
    x ∈ Metric.closedBall 0 B ∧ Q x ∈ K) requests lifted).mp
      (hrel.imp (fun _ x hx => ⟨⟨x, hx⟩, hx⟩)) |>.1



end ConvexBodyChasing

end
end BundledModule104

/- Component source: ConvexBodyChasing.QuotientSimulation -/
section BundledModule121
/-! # Causal simulation through a bounded quotient preimage

The request transformation is a fixed function of the current request. Empty
preimages use a singleton fallback; on every instance admitting a comparator
of cost at most the chosen radius, the fallback is never used.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
attribute [local instance] Classical.propDecidable
namespace ConvexBodyChasing

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A single-point request. -/
def Body.singleton (x : E) : Body E where
  carrier := {x}
  nonempty := Set.singleton_nonempty x
  compact := isCompact_singleton
  convex := convex_singleton x

variable [ProperSpace E]

/-- A total request transformation, agreeing with the bounded preimage whenever nonempty. -/
def Body.quotientLift (K : Body F) (Q : E →L[ℝ] F) (B : ℝ) : Body E :=
  if h : (Metric.closedBall 0 B ∩ Q ⁻¹' (K : Set F)).Nonempty then
    K.boundedPreimage Q B h
  else Body.singleton 0

theorem Body.mem_quotientLift_iff (K : Body F) (Q : E →L[ℝ] F) (B : ℝ)
    (h : (Metric.closedBall 0 B ∩ Q ⁻¹' (K : Set F)).Nonempty) (x : E) :
    x ∈ K.quotientLift Q B ↔ x ∈ Metric.closedBall 0 B ∧ Q x ∈ K := by
  rw [Body.quotientLift, dif_pos h]
  rfl

/-- The fixed request map preserves an offline comparator within the chosen radius. -/
theorem quotientLift_offline (Q : E →L[ℝ] F)
    (hball : Metric.closedBall 0 1 ⊆ Q '' Metric.closedBall 0 1)
    {requests : List (Body F)} {path : List F} (hserves : Serves requests path)
    {B : ℝ} (hcost : movement 0 path ≤ B) :
    ∃ lifted : List E, Serves (requests.map (fun K => K.quotientLift Q B)) lifted ∧
      movement 0 lifted ≤ movement 0 path := by
  exact (exists_lifted_serving_path Q hball hserves hcost).elim (fun lifted h =>
    ⟨lifted, List.forall₂_map_left_iff.mpr (h.1.imp (fun K x hx =>
      (K.mem_quotientLift_iff Q B ⟨x, hx⟩ x).mpr hx)), h.2⟩)

/-- Simulate an algorithm on the transformed history and project its current decision. -/
def OnlineAlgorithm.projectQuotient (A : OnlineAlgorithm E) (Q : E →L[ℝ] F)
    (B : ℝ) : OnlineAlgorithm F := fun history K =>
  if h : (Metric.closedBall 0 B ∩ Q ⁻¹' (K : Set F)).Nonempty then
    ⟨Q (A (history.map (fun L => L.quotientLift Q B)) (K.quotientLift Q B)),
      ((K.mem_quotientLift_iff Q B h _).mp
        (A (history.map (fun L => L.quotientLift Q B)) (K.quotientLift Q B)).property).2⟩
  else ⟨K.nonempty.choose, K.nonempty.choose_spec⟩

theorem OnlineAlgorithm.projectQuotient_decision (A : OnlineAlgorithm E) (Q : E →L[ℝ] F)
    (B : ℝ) (history : List (Body F)) (K : Body F)
    (h : (Metric.closedBall 0 B ∩ Q ⁻¹' (K : Set F)).Nonempty) :
    (A.projectQuotient Q B history K).val =
      Q (A (history.map (fun L => L.quotientLift Q B)) (K.quotientLift Q B)) := by
  simp only [OnlineAlgorithm.projectQuotient, dif_pos h]

/-- On admissible requests, simulation commutes exactly with projecting the trajectory. -/
theorem trajectory_projectQuotient (A : OnlineAlgorithm E) (Q : E →L[ℝ] F) (B : ℝ)
    (history requests : List (Body F))
    (hne : ∀ K ∈ requests, (Metric.closedBall 0 B ∩ Q ⁻¹' (K : Set F)).Nonempty) :
    trajectory (A.projectQuotient Q B) history requests =
      (trajectory A (history.map (fun K => K.quotientLift Q B))
        (requests.map (fun K => K.quotientLift Q B))).map Q := by
  induction requests generalizing history with
  | nil => rfl
  | cons K Ks ih =>
    simp only [trajectory, List.map_cons,
      A.projectQuotient_decision Q B history K (hne K (List.mem_cons_self)),
      ih (history ++ [K]) (fun L hL => hne L (List.mem_cons_of_mem K hL)),
      List.map_append, List.map_nil]

/-- Projection controls online cost on every sequence with nonempty bounded preimages. -/
theorem cost_projectQuotient_le (A : OnlineAlgorithm E) (Q : E →L[ℝ] F) (B : ℝ)
    {M : ℝ} (hQ : ∀ x, ‖Q x‖ ≤ M * ‖x‖) (requests : List (Body F))
    (hne : ∀ K ∈ requests, (Metric.closedBall 0 B ∩ Q ⁻¹' (K : Set F)).Nonempty) :
    cost (A.projectQuotient Q B) 0 requests ≤
      M * cost A 0 (requests.map (fun K => K.quotientLift Q B)) := by
  simpa only [cost, trajectory_projectQuotient A Q B [] requests hne, List.map_nil,
    map_zero] using! movement_map_le_of_norm_bound Q hQ 0
      (trajectory A [] (requests.map (fun K => K.quotientLift Q B)))

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]





end ConvexBodyChasing

end
end BundledModule121

/- Component source: ConvexBodyChasing.OnlineAlgorithmLimits -/
section BundledModule122
/-! # Limits of online algorithms on compact requests

A fixed ultrafilter on the natural-number index gives a feasible limit decision
for every request history. Finite trajectory costs converge to the limit cost.
This lets bounds valid for all sufficiently large truncation radii pass to one
global online algorithm without knowing future requests or the horizon.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Filter
open scoped Topology
namespace ConvexBodyChasing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def OnlineAlgorithm.ultralimit (A : ℕ → OnlineAlgorithm E) : OnlineAlgorithm E := fun history K =>
  letI : Nonempty K := ⟨⟨K.nonempty.choose, K.nonempty.choose_spec⟩⟩
  letI : CompactSpace K := isCompact_iff_compactSpace.mp K.compact
  ((hyperfilter ℕ).map (fun n => A n history K)).lim

theorem OnlineAlgorithm.tendsto_ultralimit (A : ℕ → OnlineAlgorithm E)
    (history : List (Body E)) (K : Body E) :
    Tendsto (fun n => (A n history K).val) (hyperfilter ℕ)
      (𝓝 (OnlineAlgorithm.ultralimit A history K).val) := by
  letI : Nonempty K := ⟨⟨K.nonempty.choose, K.nonempty.choose_spec⟩⟩
  letI : CompactSpace K := isCompact_iff_compactSpace.mp K.compact
  have h : Tendsto (fun n => A n history K) (hyperfilter ℕ)
      (𝓝 (OnlineAlgorithm.ultralimit A history K)) :=
    ((hyperfilter ℕ).map (fun n => A n history K)).le_nhds_lim
  exact continuous_subtype_val.continuousAt.tendsto.comp h

theorem tendsto_movement_trajectory_of_decisions {ι : Type*} {l : Filter ι}
    (A : ι → OnlineAlgorithm E) (B : OnlineAlgorithm E)
    (hdec : ∀ history K, Tendsto (fun i => (A i history K).val) l (𝓝 (B history K).val))
    (history requests : List (Body E)) (s : ι → E) (x : E) (hs : Tendsto s l (𝓝 x)) :
    Tendsto (fun i => movement (s i) (trajectory (A i) history requests)) l
      (𝓝 (movement x (trajectory B history requests))) := by
  induction requests generalizing history s x with
  | nil => exact tendsto_const_nhds
  | cons K Ks ih =>
      exact ((hdec history K).sub hs).norm.add
        (ih (history ++ [K]) (fun i => (A i history K).val) (B history K).val (hdec history K))

theorem OnlineAlgorithm.tendsto_cost_ultralimit (A : ℕ → OnlineAlgorithm E)
    (start : E) (requests : List (Body E)) :
    Tendsto (fun n => cost (A n) start requests) (hyperfilter ℕ)
      (𝓝 (cost (OnlineAlgorithm.ultralimit A) start requests)) :=
  tendsto_movement_trajectory_of_decisions A (OnlineAlgorithm.ultralimit A)
    (OnlineAlgorithm.tendsto_ultralimit A) [] requests (fun _ => start) start tendsto_const_nhds

theorem competitive_ultralimit (A : ℕ → OnlineAlgorithm E) (start : E) (R : ℝ)
    (h : ∀ requests path, Serves requests path →
      ∀ᶠ n in atTop, cost (A n) start requests ≤ R * movement start path) :
    Competitive (OnlineAlgorithm.ultralimit A) start R := by
  intro requests path hp
  exact le_of_tendsto (OnlineAlgorithm.tendsto_cost_ultralimit A start requests)
    ((h requests path hp).filter_mono Nat.hyperfilter_le_atTop)

end ConvexBodyChasing

end
end BundledModule122

/- Component source: ConvexBodyChasing.GlobalQuotientTransfer -/
section BundledModule123
/-! # Global competitive transfer through a normed quotient

For a fixed comparator, every sufficiently large truncation radius admits its
lift. Taking the same ultrafilter limit at every decision gives one global
causal algorithm with the projected competitive guarantee.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open Filter
namespace ConvexBodyChasing

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem Competitive.projectQuotient_cost_le {A : OnlineAlgorithm E} {R : ℝ}
    (hA : Competitive A 0 R) (hR : 0 ≤ R) (Q : E →L[ℝ] F)
    (hcover : Metric.closedBall 0 1 ⊆ Q '' Metric.closedBall 0 1)
    {M : ℝ} (hM : 0 ≤ M) (hQ : ∀ x, ‖Q x‖ ≤ M * ‖x‖)
    {requests : List (Body F)} {path : List F} (hp : Serves requests path)
    {B : ℝ} (hB : movement 0 path ≤ B) :
    cost (A.projectQuotient Q B) 0 requests ≤ (M * R) * movement 0 path := by
  obtain ⟨lifted, hlift, hcost⟩ := quotientLift_offline Q hcover hp hB
  have h := cost_projectQuotient_le A Q B hQ requests (bounded_preimages_nonempty Q hcover hp hB)
  exact h.trans ((mul_le_mul_of_nonneg_left
    ((hA _ lifted hlift).trans (mul_le_mul_of_nonneg_left hcost hR)) hM).trans_eq (by ring))

theorem exists_competitive_quotient_algorithm {A : OnlineAlgorithm E} {R : ℝ}
    (hA : Competitive A 0 R) (hR : 0 ≤ R) (Q : E →L[ℝ] F)
    (hcover : Metric.closedBall 0 1 ⊆ Q '' Metric.closedBall 0 1)
    {M : ℝ} (hM : 0 ≤ M) (hQ : ∀ x, ‖Q x‖ ≤ M * ‖x‖) :
    ∃ B : OnlineAlgorithm F, Competitive B 0 (M * R) := by
  refine ⟨OnlineAlgorithm.ultralimit (fun n : ℕ => A.projectQuotient Q (n : ℝ)), ?_⟩
  apply competitive_ultralimit
  intro requests path hp
  obtain ⟨n, hn⟩ := exists_nat_ge (movement 0 path)
  exact Filter.eventually_atTop.mpr ⟨n, fun m hm =>
    hA.projectQuotient_cost_le hR Q hcover hM hQ hp (hn.trans (Nat.cast_le.mpr hm))⟩

end ConvexBodyChasing

end
end BundledModule123

/- Component source: ConvexBodyChasing.MeanAlgorithm -/
section BundledModule124
/-! # Averaging a randomized online algorithm

Compact requests bound each decision, so its Bochner expectation is integrable.
Convexity keeps the mean decision feasible, and convexity of the norm bounds
the mean algorithm's movement by the randomized algorithm's expected movement.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
namespace ConvexBodyChasing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem RandomizedOnlineAlgorithm.integrable_decision (A : RandomizedOnlineAlgorithm E)
    (history : List (Body E)) (K : Body E) :
    Integrable (fun ω => (A.algorithm ω history K).val) A.law := by
  obtain ⟨C, hC⟩ := K.compact.isBounded.exists_norm_le
  exact Integrable.of_bound (A.measurable_decision history K).aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun ω => hC _ (A.algorithm ω history K).property))

def RandomizedOnlineAlgorithm.meanAlgorithm (A : RandomizedOnlineAlgorithm E) : OnlineAlgorithm E :=
  fun history K => ⟨∫ ω, (A.algorithm ω history K).val ∂A.law,
    K.convex.integral_mem K.compact.isClosed
      (Filter.Eventually.of_forall (fun ω => (A.algorithm ω history K).property))
      (A.integrable_decision history K)⟩

theorem RandomizedOnlineAlgorithm.integrable_movement_trajectory (A : RandomizedOnlineAlgorithm E)
    (history requests : List (Body E)) (s : A.Seed → E) (hs : Integrable s A.law) :
    Integrable (fun ω => movement (s ω) (trajectory (A.algorithm ω) history requests)) A.law := by
  induction requests generalizing history s with
  | nil => exact integrable_const 0
  | cons K Ks ih =>
      exact ((A.integrable_decision history K).sub hs).norm.add
        (ih (history ++ [K]) _ (A.integrable_decision history K))

theorem RandomizedOnlineAlgorithm.movement_mean_le_integral (A : RandomizedOnlineAlgorithm E)
    (history requests : List (Body E)) (s : A.Seed → E) (hs : Integrable s A.law) :
    movement (∫ ω, s ω ∂A.law) (trajectory A.meanAlgorithm history requests) ≤
      ∫ ω, movement (s ω) (trajectory (A.algorithm ω) history requests) ∂A.law := by
  induction requests generalizing history s with
  | nil => simp only [trajectory, movement, integral_zero, le_refl]
  | cons K Ks ih =>
      have hn : Integrable (fun ω => ‖(A.algorithm ω history K).val - s ω‖) A.law :=
        ((A.integrable_decision history K).sub hs).norm
      change ‖(∫ ω, (A.algorithm ω history K).val ∂A.law) - (∫ ω, s ω ∂A.law)‖ +
          movement (∫ ω, (A.algorithm ω history K).val ∂A.law)
            (trajectory A.meanAlgorithm (history ++ [K]) Ks) ≤ _
      rw [show (fun ω => movement (s ω) (trajectory (A.algorithm ω) history (K :: Ks))) =
        (fun ω => ‖(A.algorithm ω history K).val - s ω‖ +
          movement (A.algorithm ω history K).val (trajectory (A.algorithm ω) (history ++ [K]) Ks))
        from rfl,
        integral_add hn
          (A.integrable_movement_trajectory (history ++ [K]) Ks _ (A.integrable_decision history K))]
      refine add_le_add ?_ (ih (history ++ [K]) _ (A.integrable_decision history K))
      rw [← integral_sub (A.integrable_decision history K) hs]
      exact norm_integral_le_integral_norm _

theorem RandomizedOnlineAlgorithm.integrable_cost (A : RandomizedOnlineAlgorithm E)
    (start : E) (requests : List (Body E)) :
    Integrable (fun ω => cost (A.algorithm ω) start requests) A.law :=
  A.integrable_movement_trajectory [] requests (fun _ => start) (integrable_const start)

theorem RandomizedOnlineAlgorithm.cost_mean_le_integral (A : RandomizedOnlineAlgorithm E)
    (start : E) (requests : List (Body E)) :
    cost A.meanAlgorithm start requests ≤ ∫ ω, cost (A.algorithm ω) start requests ∂A.law := by
  simpa [cost] using! A.movement_mean_le_integral [] requests (fun _ => start) (integrable_const start)

theorem RandomizedOnlineAlgorithm.expectedCost_eq_ofReal_integral (A : RandomizedOnlineAlgorithm E)
    (start : E) (requests : List (Body E)) :
    expectedCost A start requests = ENNReal.ofReal (∫ ω, cost (A.algorithm ω) start requests ∂A.law) :=
  (ofReal_integral_eq_lintegral_ofReal (A.integrable_cost start requests)
    (Filter.Eventually.of_forall (fun _ => movement_nonneg start _))).symm

theorem RandomizedCompetitive.meanAlgorithm {A : RandomizedOnlineAlgorithm E} {start : E} {R : ℝ}
    (hA : RandomizedCompetitive A start R) (hR : 0 ≤ R) : Competitive A.meanAlgorithm start R := by
  intro requests path hp
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hR (movement_nonneg start path))).mp
  exact (ENNReal.ofReal_le_ofReal (A.cost_mean_le_integral start requests)).trans
    ((A.expectedCost_eq_ofReal_integral start requests).symm.le.trans (hA requests path hp))

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Regard a deterministic algorithm as a randomized one with a single seed. -/
def OnlineAlgorithm.toRandomized (A : OnlineAlgorithm E) : RandomizedOnlineAlgorithm E where
  Seed := Unit
  measurableSpace := inferInstance
  law := Measure.dirac ()
  probability := inferInstance
  algorithm := fun _ => A
  measurable_decision := fun _ _ => measurable_const

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem OnlineAlgorithm.expectedCost_toRandomized (A : OnlineAlgorithm E)
    (start : E) (requests : List (Body E)) :
    expectedCost A.toRandomized start requests = ENNReal.ofReal (cost A start requests) := by
  simp only [expectedCost, OnlineAlgorithm.toRandomized, lintegral_const, measure_univ, mul_one]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem Competitive.toRandomized {A : OnlineAlgorithm E} {start : E} {R : ℝ}
    (hA : Competitive A start R) : RandomizedCompetitive A.toRandomized start R := by
  intro requests path hp
  rw [A.expectedCost_toRandomized]
  exact ENNReal.ofReal_le_ofReal (hA requests path hp)

end ConvexBodyChasing

end
end BundledModule124

/- Component source: ConvexBodyChasing.SubspaceSimulation -/
section BundledModule125
/-! # Restricting an ambient online algorithm to a subspace

Requests contained in a subspace force every feasible ambient decision to stay
there. The inherited norm makes this restriction preserve costs exactly.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
namespace ConvexBodyChasing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- View a compact convex request in a subspace as a request in the ambient space. -/
def Body.inAmbient (S : Submodule ℝ E) (K : Body S) : Body E where
  carrier := Subtype.val '' (K : Set S)
  nonempty := K.nonempty.image Subtype.val
  compact := K.compact.image continuous_subtype_val
  convex := K.convex.linear_image S.subtype

theorem Body.mem_inAmbient_iff (S : Submodule ℝ E) (K : Body S) (x : S) :
    (x : E) ∈ K.inAmbient S ↔ x ∈ K := by
  exact ⟨fun ⟨y, hy, hxy⟩ => Subtype.ext hxy ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

theorem Body.mem_subspace_of_mem_inAmbient (S : Submodule ℝ E) (K : Body S)
    {x : E} (hx : x ∈ K.inAmbient S) : x ∈ S := by
  exact hx.elim (fun y hy => hy.2 ▸ y.property)

/-- Feed subspace requests to the ambient algorithm, retaining its exact decision. -/
def OnlineAlgorithm.restrictSubspace (A : OnlineAlgorithm E) (S : Submodule ℝ E) :
    OnlineAlgorithm S := fun history K =>
  let x := A (history.map (fun L => L.inAmbient S)) (K.inAmbient S)
  let y : S := ⟨x.val, K.mem_subspace_of_mem_inAmbient S x.property⟩
  ⟨y, (K.mem_inAmbient_iff S y).mp x.property⟩

theorem OnlineAlgorithm.restrictSubspace_decision (A : OnlineAlgorithm E) (S : Submodule ℝ E)
    (history : List (Body S)) (K : Body S) :
    ((A.restrictSubspace S history K).val : E) =
      (A (history.map (fun L => L.inAmbient S)) (K.inAmbient S)).val := rfl

theorem trajectory_restrictSubspace (A : OnlineAlgorithm E) (S : Submodule ℝ E)
    (history requests : List (Body S)) :
    (trajectory (A.restrictSubspace S) history requests).map Subtype.val =
      trajectory A (history.map (fun K => K.inAmbient S))
        (requests.map (fun K => K.inAmbient S)) := by
  induction requests generalizing history with
  | nil => rfl
  | cons K Ks ih =>
    simp only [trajectory, List.map_cons, A.restrictSubspace_decision, ih,
      List.map_append, List.map_nil]

theorem movement_subspace (S : Submodule ℝ E) (start : S) (path : List S) :
    movement (start : E) (path.map Subtype.val) = movement start path := by
  induction path generalizing start with
  | nil => rfl
  | cons x xs ih => exact congrArg (fun t => ‖x - start‖ + t) (ih x)

theorem cost_restrictSubspace (A : OnlineAlgorithm E) (S : Submodule ℝ E)
    (start : S) (requests : List (Body S)) :
    cost (A.restrictSubspace S) start requests =
      cost A (start : E) (requests.map (fun K => K.inAmbient S)) := by
  simpa only [cost, trajectory_restrictSubspace, List.map_nil] using!
    (movement_subspace S start (trajectory (A.restrictSubspace S) [] requests)).symm

theorem Serves.inAmbient (S : Submodule ℝ E) {requests : List (Body S)} {path : List S}
    (h : Serves requests path) :
    Serves (requests.map (fun K => K.inAmbient S)) (path.map Subtype.val) := by
  exact List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr
    (h.imp (fun _ x hx => ⟨x, hx, rfl⟩)))

variable [MeasurableSpace E]

/-- Restriction preserves the seed law and measurability of decisions. -/
def RandomizedOnlineAlgorithm.restrictSubspace (A : RandomizedOnlineAlgorithm E)
    (S : Submodule ℝ E) : RandomizedOnlineAlgorithm S where
  Seed := A.Seed
  measurableSpace := A.measurableSpace
  law := A.law
  probability := A.probability
  algorithm := fun seed => (A.algorithm seed).restrictSubspace S
  measurable_decision := fun history K => by
    exact (A.measurable_decision (history.map (fun L => L.inAmbient S))
      (K.inAmbient S)).subtype_mk

theorem expectedCost_restrictSubspace (A : RandomizedOnlineAlgorithm E) (S : Submodule ℝ E)
    (start : S) (requests : List (Body S)) :
    expectedCost (A.restrictSubspace S) start requests =
      expectedCost A (start : E) (requests.map (fun K => K.inAmbient S)) := by
  simp only [expectedCost, RandomizedOnlineAlgorithm.restrictSubspace, cost_restrictSubspace]

/-- Any competitive guarantee in the ambient space also holds on its subspaces. -/
theorem RandomizedCompetitive.restrictSubspace {A : RandomizedOnlineAlgorithm E}
    (S : Submodule ℝ E) (start : S) {R : ℝ}
    (hcomp : RandomizedCompetitive A (start : E) R) :
    RandomizedCompetitive (A.restrictSubspace S) start R := by
  intro requests path hpath
  simpa only [expectedCost_restrictSubspace, movement_subspace] using!
    hcomp _ _ (hpath.inAmbient S)

end ConvexBodyChasing

end
end BundledModule125

/- Component source: ConvexBodyChasing.BasicLower -/
section BundledModule126
/-! # The unit lower bound in every nonzero normed space -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory
namespace ConvexBodyChasing

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cost_singleton (A : OnlineAlgorithm E) (x : E) :
    cost A 0 [Body.singleton x] = ‖x‖ := by
  have hx : (A [] (Body.singleton x)).val = x := (A [] (Body.singleton x)).property
  simp only [cost, trajectory, movement, hx, sub_zero, add_zero]

variable [MeasurableSpace E]

theorem expectedCost_singleton (A : RandomizedOnlineAlgorithm E) (x : E) :
    expectedCost A 0 [Body.singleton x] = ENNReal.ofReal ‖x‖ := by
  simp only [expectedCost, cost_singleton, lintegral_const, measure_univ, mul_one]

/-- A nonzero singleton forces every competitive guarantee to be at least one. -/
theorem one_le_of_randomizedCompetitive [Nontrivial E]
    (A : RandomizedOnlineAlgorithm E) (R : ℝ) (hcomp : RandomizedCompetitive A 0 R) :
    1 ≤ R := by
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have h := hcomp [Body.singleton x] [x] (.cons rfl .nil)
  rw [expectedCost_singleton, movement, movement, sub_zero, add_zero,
    ENNReal.ofReal_le_ofReal_iff'] at h
  exact (mul_le_mul_iff_of_pos_right (norm_pos_iff.mpr hx)).mp
    (by simpa only [one_mul] using! h.resolve_right (not_le.mpr (norm_pos_iff.mpr hx)))

end ConvexBodyChasing

end
end BundledModule126

/- Component source: Solutions.ModelBridge -/
section BundledModule128
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace CBCProve2Me

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]

def translatedBody (x₀ : X) (K : ConvexBodyChasing.Body X) : Set X :=
  (fun x => x₀ + x) '' (K : Set X)

theorem translatedBody_isBody (x₀ : X) (K : ConvexBodyChasing.Body X) :
    CBCLowerBound.EveryNorm.IsBody (translatedBody x₀ K) := by
  refine ⟨K.nonempty.image _, ?_, ?_⟩
  · exact (K.compact.image (continuous_const.add continuous_id)).isClosed
  · exact K.convex.translate x₀

theorem mem_translatedBody (x₀ y : X) (K : ConvexBodyChasing.Body X) :
    y ∈ translatedBody x₀ K ↔ y - x₀ ∈ K := by
  simp [translatedBody, sub_eq_add_neg, add_comm]

def toLocalAlgorithm {x₀ : X} (A : CBCLowerBound.EveryNorm.Algorithm X x₀) :
    ConvexBodyChasing.OnlineAlgorithm X := fun history K =>
  ⟨A.pos (history.map (translatedBody x₀) ++ [translatedBody x₀ K]) - x₀, by
    apply (mem_translatedBody x₀ _ K).mp
    apply A.pos_mem _ _ _ (translatedBody_isBody x₀ K)
    simpa only [List.forall_mem_map] using
      (fun (L : ConvexBodyChasing.Body X) (_ : L ∈ history) => translatedBody_isBody x₀ L)⟩

local instance : MeasurableSpace X := borel X
local instance : BorelSpace X := ⟨rfl⟩

def toLocalRandomized {x₀ : X} (A : CBCLowerBound.EveryNorm.RandomizedAlgorithm X x₀) :
    ConvexBodyChasing.RandomizedOnlineAlgorithm X where
  Seed := A.Ω
  measurableSpace := A.mΩ
  law := A.P
  probability := A.isProb
  algorithm := fun ω => toLocalAlgorithm (A.alg ω)
  measurable_decision := fun history K => by
    exact (A.measurable_pos _).sub_const x₀

omit [NormedSpace ℝ X] in
theorem movement_range (f : ℕ → X) (n : ℕ) :
    ConvexBodyChasing.movement (f 0) ((List.range n).map (fun t => f (t + 1))) =
      ∑ t ∈ Finset.range n, ‖f (t + 1) - f t‖ := by
  induction n generalizing f with
  | zero => simp [ConvexBodyChasing.movement]
  | succ n ih =>
    simp only [List.range_succ_eq_map, List.map_cons, List.map_map,
      ConvexBodyChasing.movement, Finset.sum_range_succ']
    simpa only [Function.comp_def, Nat.succ_eq_add_one, add_comm] using!
      congrArg (fun z => ‖f (0 + 1) - f 0‖ + z) (ih (fun t => f (t + 1)))

theorem trajectory_toLocal {x₀ : X} (A : CBCLowerBound.EveryNorm.Algorithm X x₀)
    (history requests : List (ConvexBodyChasing.Body X)) :
    ConvexBodyChasing.trajectory (toLocalAlgorithm A) history requests =
      (List.range requests.length).map (fun t =>
        A.pos ((history ++ requests.take (t + 1)).map (translatedBody x₀)) - x₀) := by
  induction requests generalizing history with
  | nil => simp [ConvexBodyChasing.trajectory]
  | cons K Ks ih =>
    simp [ConvexBodyChasing.trajectory, toLocalAlgorithm, ih,
      List.range_succ_eq_map, List.map_map, Function.comp_def, List.append_assoc]

theorem cost_toLocal {x₀ : X} (A : CBCLowerBound.EveryNorm.Algorithm X x₀)
    (requests : List (ConvexBodyChasing.Body X)) :
    ConvexBodyChasing.cost (toLocalAlgorithm A) 0 requests =
      A.cost (requests.map (translatedBody x₀)) := by
  simpa [ConvexBodyChasing.cost, trajectory_toLocal,
    CBCLowerBound.EveryNorm.Algorithm.cost, List.map_take, A.pos_nil] using!
    movement_range (fun t => A.pos ((requests.take t).map (translatedBody x₀)) - x₀)
      requests.length

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
theorem map_range_getD (path : List X) (fallback : X) :
    (List.range path.length).map (fun t => path.getD t fallback) = path := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simpa only [List.getElem_map, List.getElem_range] using!
      (List.getElem_eq_getD (l := path) (i := i) (h := h₂) fallback).symm

def offlinePath (x₀ : X) (path : List X) (t : ℕ) : X :=
  x₀ + (0 :: path).getD t 0

omit [NormedSpace ℝ X] in
theorem offlinePath_cost (x₀ : X) (path : List X) :
    (∑ t ∈ Finset.range path.length, ‖offlinePath x₀ path (t + 1) - offlinePath x₀ path t‖) =
      ConvexBodyChasing.movement 0 path := by
  simpa only [offlinePath, List.getD_cons_zero, List.getD_cons_succ,
    add_sub_add_left_eq_sub, map_range_getD] using!
    (movement_range (fun t => (0 :: path).getD t 0) path.length).symm

theorem offlinePath_serves (x₀ : X) {requests : List (ConvexBodyChasing.Body X)}
    {path : List X} (h : ConvexBodyChasing.Serves requests path) :
    ∀ (t : ℕ) (ht : t < (requests.map (translatedBody x₀)).length),
      offlinePath x₀ path (t + 1) ∈ (requests.map (translatedBody x₀))[t] := by
  intro t ht
  have hp : t < path.length := by simpa only [List.length_map, h.length_eq] using ht
  simpa only [offlinePath, List.getD_cons_succ, List.getElem_map,
    mem_translatedBody, add_sub_cancel_left,
    ← List.getElem_eq_getD (l := path) (i := t) (h := hp) 0] using!
    h.get (by simpa only [List.length_map] using ht) hp

theorem offlineCost_mem (x₀ : X) {requests : List (ConvexBodyChasing.Body X)}
    {path : List X} (h : ConvexBodyChasing.Serves requests path) :
    ConvexBodyChasing.movement 0 path ∈
      {c : ℝ | ∃ y : ℕ → X, y 0 = x₀ ∧
        (∀ (t : ℕ) (ht : t < (requests.map (translatedBody x₀)).length),
          y (t + 1) ∈ (requests.map (translatedBody x₀))[t]) ∧
        c = ∑ t ∈ Finset.range (requests.map (translatedBody x₀)).length,
          ‖y (t + 1) - y t‖} := by
  refine ⟨offlinePath x₀ path, ?_, offlinePath_serves x₀ h, ?_⟩
  · simp [offlinePath]
  · simpa only [List.length_map, h.length_eq] using (offlinePath_cost x₀ path).symm

theorem opt_bounds (x₀ : X) {requests : List (ConvexBodyChasing.Body X)}
    {path : List X} (h : ConvexBodyChasing.Serves requests path) :
    0 ≤ CBCLowerBound.EveryNorm.opt x₀ (requests.map (translatedBody x₀)) ∧
    CBCLowerBound.EveryNorm.opt x₀ (requests.map (translatedBody x₀)) ≤
      ConvexBodyChasing.movement 0 path := by
  have hmem := offlineCost_mem x₀ h
  have hlower : ∀ c ∈ {c : ℝ | ∃ y : ℕ → X, y 0 = x₀ ∧
      (∀ (t : ℕ) (ht : t < (requests.map (translatedBody x₀)).length),
        y (t + 1) ∈ (requests.map (translatedBody x₀))[t]) ∧
      c = ∑ t ∈ Finset.range (requests.map (translatedBody x₀)).length,
        ‖y (t + 1) - y t‖}, 0 ≤ c := by
    rintro c ⟨y, _, _, rfl⟩
    exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  exact ⟨le_csInf ⟨_, hmem⟩ hlower, csInf_le ⟨0, hlower⟩ hmem⟩

theorem expectedCost_toLocal {x₀ : X}
    (A : CBCLowerBound.EveryNorm.RandomizedAlgorithm X x₀)
    (requests : List (ConvexBodyChasing.Body X)) :
    ConvexBodyChasing.expectedCost (toLocalRandomized A) 0 requests =
      A.expCost (requests.map (translatedBody x₀)) := by
  simp only [ConvexBodyChasing.expectedCost, toLocalRandomized,
    CBCLowerBound.EveryNorm.RandomizedAlgorithm.expCost, cost_toLocal]
  rfl

theorem competitive_toLocal {x₀ : X}
    (A : CBCLowerBound.EveryNorm.RandomizedAlgorithm X x₀) (R : ℝ)
    (hcomp : A.IsCompetitive R) :
    ConvexBodyChasing.RandomizedCompetitive (toLocalRandomized A) 0 R := by
  intro requests path hpath
  rw [expectedCost_toLocal]
  refine (hcomp _ ?_).trans ?_
  · simpa only [List.forall_mem_map] using
      (fun (K : ConvexBodyChasing.Body X) (_ : K ∈ requests) => translatedBody_isBody x₀ K)
  · simpa only [ENNReal.ofReal_mul' (opt_bounds x₀ hpath).1,
      ENNReal.ofReal_mul' (ConvexBodyChasing.movement_nonneg 0 path), mul_comm] using
      mul_le_mul_left (ENNReal.ofReal_le_ofReal (opt_bounds x₀ hpath).2) (ENNReal.ofReal R)

end CBCProve2Me

end
end BundledModule128

open CBCLowerBound.EveryNorm
open scoped ENNReal

theorem solution : ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 2 ≤ d →
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X],
      Module.finrank ℝ X = d →
      ∀ (x₀ : X) (A : RandomizedAlgorithm X x₀) (R : ℝ),
        A.IsCompetitive R → c * d ≤ R := by
  obtain ⟨M, hM, hqs⟩ := CBCLowerBound.EveryNorm.lemma_10
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  refine ⟨1 / (256000000 * M), div_pos zero_lt_one (mul_pos (by norm_num) hMpos), ?_⟩
  intro d hd X _ _ _ hdim x₀ A R hcomp
  let : Nontrivial X := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ X)
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  have hlocal := CBCProve2Me.competitive_toLocal A R hcomp
  have hR : 1 ≤ R := ConvexBodyChasing.one_le_of_randomizedCompetitive _ R hlocal
  have hden : 0 < 256000000 * M := mul_pos (by norm_num) hMpos
  suffices (d : ℝ) / (256000000 * M) ≤ R by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using this
  by_cases hlarge : 6 ≤ d
  · obtain ⟨S, k, Q, hk, hcover, hbound⟩ := hqs X
    rw [hdim] at hk
    have hk3 : 3 ≤ k := by exact_mod_cast (show (3 : ℝ) ≤ k by linarith [show (6 : ℝ) ≤ d by exact_mod_cast hlarge])
    let Qc : S →L[ℝ] EuclideanSpace ℝ (Fin k) := Q.toContinuousLinearMap
    have hcoverc : Metric.closedBall 0 1 ⊆ Qc '' Metric.closedBall 0 1 := by
      simpa only [Metric.closedBall, dist_zero_right] using! hcover
    have hboundc : Qc '' Metric.closedBall 0 1 ⊆ Metric.closedBall 0 M := by
      simpa only [Metric.closedBall, dist_zero_right] using! hbound
    have hsub := hlocal.restrictSubspace S 0
    obtain ⟨B, hB⟩ := ConvexBodyChasing.exists_competitive_quotient_algorithm
      (hsub.meanAlgorithm (zero_le_one.trans hR)) (zero_le_one.trans hR)
      Qc hcoverc hMpos.le
      (ConvexBodyChasing.norm_map_le_of_ball_image_subset Qc hMpos.le hboundc)
    have hlower := ConvexBodyChasing.competitive_ratio_linear_lower_bound
      k hk3 (2 : ℝ≥0∞) (by norm_num) B.toRandomized (M * R) hB.toRandomized
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hk, hlower]
  · have hsmall : (d : ℝ) ≤ 5 := by exact_mod_cast (show d ≤ 5 by omega)
    exact ((div_le_one hden).mpr (by linarith only [hsmall, hM])).trans hR
