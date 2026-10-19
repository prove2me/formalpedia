-- Prove2me | solution 1 for ClarkeGradients.MaxFunctions.max_function_generalized_gradient
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-17T02:43:15.552464+00:00
-- url     : https://prove2.me/submissions/232e04ba-1095-4a07-ab77-a4af9c0216e0

-- Licensed under Apache 2.0. Full exact theorem: Clarke max-function generalized gradient and directional derivative.
import Mathlib
import Definitions.Def_ClarkeGradients_Shared_LipschitzOnBounded
import Definitions.Def_ClarkeGradients_Shared_generalizedGradient
import Definitions.Def_ClarkeGradients_Shared_genDirDeriv
import Definitions.Def_ClarkeGradients_MaxFunctions_HasOneSidedDirDeriv
import Definitions.Def_ClarkeGradients_MaxFunctions_SeqUpperSemicontinuous
import Definitions.Def_ClarkeGradients_MaxFunctions_maxFunction


open Set Filter Topology
open scoped BigOperators

namespace ClarkeProof

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def tupleHull (s : Set E) (k : ℕ) : Set E :=
  (fun p : (Fin k → ℝ) × (Fin k → E) => ∑ i, p.1 i • p.2 i) ''
    ((stdSimplex ℝ (Fin k)) ×ˢ Set.pi Set.univ (fun _ => s))

private lemma tupleHull_compact {s : Set E} (hs : IsCompact s) (k : ℕ) :
    IsCompact (tupleHull s k) := by
  have hp : IsCompact (Set.pi Set.univ (fun _ : Fin k => s)) := by
    simpa only [Set.pi, Set.mem_univ, forall_true_left] using isCompact_pi_infinite (fun _ : Fin k => hs)
  unfold tupleHull
  apply ((isCompact_stdSimplex ℝ (Fin k)).prod hp).image
  fun_prop

private lemma tupleHull_subset (s : Set E) (k : ℕ) :
    tupleHull s k ⊆ convexHull ℝ s := by
  rintro _ ⟨⟨w,z⟩, ⟨hw,hz⟩, rfl⟩
  exact (convex_convexHull ℝ s).sum_mem (fun i _ => hw.1 i) (by simpa using hw.2)
    (fun i _ => subset_convexHull ℝ s (hz i (Set.mem_univ i)))

variable [FiniteDimensional ℝ E]

lemma compact_convexHull {s : Set E} (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  classical
  let N := Module.finrank ℝ E + 1
  have heq : convexHull ℝ s = ⋃ k : Fin (N + 1), tupleHull s k.val := by
    apply Set.Subset.antisymm
    · intro x hx
      let t := Caratheodory.minCardFinsetOfMemConvexHull hx
      have ht : (↑t : Set E) ⊆ s := Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
      have ha : AffineIndependent ℝ ((↑) : t → E) :=
        Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
      have hcard : Fintype.card t ≤ N :=
        ha.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
      have hm : x ∈ convexHull ℝ (↑t : Set E) :=
        Caratheodory.mem_minCardFinsetOfMemConvexHull hx
      rw [t.convexHull_eq] at hm
      obtain ⟨w,hw,hsum,hxw⟩ := hm
      let e := (Fintype.equivFin t).symm
      have hs' : ∑ i : t, w i = 1 := by simpa only [Finset.univ_eq_attach, Finset.sum_attach] using hsum
      have hx' : (∑ i : t, w i • (i : E)) = x := by
        calc
          _ = ∑ i ∈ t, w i • i := t.sum_attach (fun i => w i • i)
          _ = x := by simpa [Finset.centerMass, hsum] using hxw
      apply Set.mem_iUnion.mpr
      refine ⟨⟨Fintype.card t, Nat.lt_succ_of_le hcard⟩, ?_⟩
      refine ⟨(fun i => w (e i), fun i => (e i : E)), ?_, ?_⟩
      · constructor
        · constructor
          · intro i; exact hw _ (e i).property
          · exact (e.sum_comp (fun i : t => w i)).trans hs'
        · intro i _; exact ht (e i).property
      · exact (e.sum_comp (fun i : t => w i • (i : E))).trans hx'
    · exact Set.iUnion_subset fun k => tupleHull_subset s k.val
  rw [heq]
  exact isCompact_iUnion (fun k => tupleHull_compact hs k.val)

end ClarkeProof


open Set Filter Topology MeasureTheory
open ClarkeGradients

namespace ClarkeProof

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

private def derivativeGraph (f : E → ℝ) : Set (E × E) :=
  {p | DifferentiableAt ℝ f p.1 ∧ gradient f p.1 = p.2}

lemma gradientLimits_iff_closure_graph (f : E → ℝ) (x z : E) :
    z ∈ Shared.gradientLimits f x ↔ (x,z) ∈ closure (derivativeGraph f) := by
  constructor
  · rintro ⟨h,hh,hd,hg⟩
    apply mem_closure_iff_seq_limit.mpr
    refine ⟨fun j => (x + h j, gradient f (x + h j)), fun j => ⟨hd j,rfl⟩, ?_⟩
    simpa using (tendsto_const_nhds.add hh).prodMk_nhds hg
  · intro hz
    obtain ⟨p,hp,ht⟩ := mem_closure_iff_seq_limit.mp hz
    refine ⟨fun j => (p j).1 - x, ?_, ?_, ?_⟩
    · simpa using (continuous_fst.tendsto _ |>.comp ht).sub_const x
    · intro j; simpa using (hp j).1
    · have hq := continuous_snd.tendsto (x,z) |>.comp ht
      exact hq.congr' (Filter.Eventually.of_forall fun j => by simp [(hp j).2])

lemma gradientLimits_isClosed (f : E → ℝ) (x : E) :
    IsClosed (Shared.gradientLimits f x) := by
  have heq : Shared.gradientLimits f x =
      (fun z => (x,z)) ⁻¹' closure (derivativeGraph f) := by
    ext z; exact gradientLimits_iff_closure_graph f x z
  rw [heq]
  exact isClosed_closure.preimage (continuous_const.prodMk continuous_id)

lemma norm_gradient_le_lipschitzOn {f : E → ℝ} {s : Set E} {K : NNReal} {x : E}
    (hs : s ∈ 𝓝 x) (hf : LipschitzOnWith K f s) : ‖gradient f x‖ ≤ K := by
  simpa only [gradient, LinearIsometryEquiv.norm_map] using
    norm_fderiv_le_of_lipschitzOn ℝ hs hf

lemma gradientLimits_norm_le {f : E → ℝ} {x z : E} {s : Set E} {K : NNReal}
    (hs : IsOpen s) (hx : x ∈ s) (hf : LipschitzOnWith K f s)
    (hz : z ∈ Shared.gradientLimits f x) : ‖z‖ ≤ K := by
  obtain ⟨h,hh,_,hg⟩ := hz
  have ht : Tendsto (fun j => x + h j) atTop (𝓝 x) := by
    simpa using tendsto_const_nhds.add hh
  apply le_of_tendsto hg.norm
  filter_upwards [ht.eventually (hs.mem_nhds hx)] with j hj
  exact norm_gradient_le_lipschitzOn (hs.mem_nhds hj) hf

lemma gradientLimits_nonempty {f : E → ℝ} (hf : Shared.LipschitzOnBounded f) (x : E) :
    (Shared.gradientLimits f x).Nonempty := by
  obtain ⟨K,hK⟩ := hf (Metric.ball x 1) Metric.isBounded_ball
  obtain ⟨g,hg,heq⟩ := hK.extend_real
  have hdense : Dense {y : E | DifferentiableAt ℝ g y} :=
    Measure.dense_of_ae (μ := volume) hg.ae_differentiableAt
  obtain ⟨y,hy,hyt⟩ := mem_closure_iff_seq_limit.mp (hdense x)
  have hbound : ∀ j, gradient g (y j) ∈ Metric.closedBall (0 : E) K := by
    intro j
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      norm_gradient_le_lipschitzOn (s := Set.univ) Filter.univ_mem hg.lipschitzOnWith
  obtain ⟨z,_,φ,hφ,hzt⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hbound
  refine ⟨z,(gradientLimits_iff_closure_graph f x z).mpr ?_⟩
  have hys := hyt.comp hφ.tendsto_atTop
  apply isClosed_closure.mem_of_tendsto (hys.prodMk_nhds hzt)
  filter_upwards [hys.eventually (Metric.ball_mem_nhds x (by norm_num : (0:ℝ)<1))] with j hj
  apply subset_closure
  have he : f =ᶠ[𝓝 (y (φ j))] g :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨Metric.ball x 1, Metric.isOpen_ball.mem_nhds hj, heq⟩
  exact ⟨(hy (φ j)).congr_of_eventuallyEq he, he.gradient_eq⟩

lemma gradientLimits_isCompact {f : E → ℝ} (hf : Shared.LipschitzOnBounded f) (x : E) :
    IsCompact (Shared.gradientLimits f x) := by
  obtain ⟨K,hK⟩ := hf (Metric.ball x 1) Metric.isBounded_ball
  apply (isCompact_closedBall (0 : E) (K : ℝ)).of_isClosed_subset
    (gradientLimits_isClosed f x)
  intro z hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    gradientLimits_norm_le Metric.isOpen_ball (Metric.mem_ball_self (by norm_num)) hK hz

lemma generalizedGradient_nonempty {f : E → ℝ} (hf : Shared.LipschitzOnBounded f) (x : E) :
    (Shared.generalizedGradient f x).Nonempty :=
  (gradientLimits_nonempty hf x).mono (subset_convexHull ℝ _)

lemma generalizedGradient_isCompact {f : E → ℝ} (hf : Shared.LipschitzOnBounded f) (x : E) :
    IsCompact (Shared.generalizedGradient f x) :=
  compact_convexHull (gradientLimits_isCompact hf x)

lemma generalizedGradient_norm_le {f : E → ℝ} {x z : E} {s : Set E} {K : NNReal}
    (hs : IsOpen s) (hx : x ∈ s) (hf : LipschitzOnWith K f s)
    (hz : z ∈ Shared.generalizedGradient f x) : ‖z‖ ≤ K := by
  have hsub : Shared.generalizedGradient f x ⊆ Metric.closedBall (0 : E) K :=
    convexHull_min (fun z hz => by
      simpa only [Metric.mem_closedBall, dist_zero_right] using gradientLimits_norm_le hs hx hf hz)
      (convex_closedBall (0 : E) (K : ℝ))
  simpa only [Metric.mem_closedBall, dist_zero_right] using hsub hz

end ClarkeProof


open Set Filter Topology

namespace ClarkeProof

lemma usc_limit_le {U : Type*} [TopologicalSpace U] {g : U → ℝ}
    {u : U} {a : ℝ} {s : ℕ → U} (hg : UpperSemicontinuousAt g u)
    (hs : Tendsto s atTop (𝓝 u)) (hv : Tendsto (g ∘ s) atTop (𝓝 a)) : a ≤ g u := by
  by_contra! h
  have h₁ := hs.eventually (hg ((g u + a)/2) (by linarith))
  have h₂ := hv.eventually (lt_mem_nhds (show (g u+a)/2 < a by linarith))
  obtain ⟨j,hj₁,hj₂⟩ := (h₁.and h₂).exists
  change (g u+a)/2 < g (s j) at hj₂
  linarith

lemma usc_bddAbove_range {U : Type*} [TopologicalSpace U] [SeqCompactSpace U]
    {g : U → ℝ} (hg : UpperSemicontinuous g) : BddAbove (Set.range g) := by
  classical
  by_contra hn
  have he : ∀ j : ℕ, ∃ u : U, (j : ℝ) < g u := by
    intro j
    obtain ⟨b,⟨u,rfl⟩,hb⟩ := not_bddAbove_iff.mp hn (j : ℝ)
    exact ⟨u,hb⟩
  choose s hs using he
  obtain ⟨u,φ,hφ,ht⟩ := SeqCompactSpace.tendsto_subseq s
  have h₁ := ht.eventually (hg u (g u+1) (by linarith))
  have h₂ : ∀ᶠ j : ℕ in atTop, g u+1 ≤ (φ j : ℝ) :=
    (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop).eventually
      (eventually_ge_atTop (g u+1))
  obtain ⟨j,hj₁,hj₂⟩ := (h₁.and h₂).exists
  have hj₃ := hs (φ j)
  change g (s (φ j)) < g u+1 at hj₁
  linarith

lemma usc_exists_max {U : Type*} [TopologicalSpace U] [SeqCompactSpace U] [Nonempty U]
    {g : U → ℝ} (hg : UpperSemicontinuous g) : ∃ u, ∀ v, g v ≤ g u := by
  classical
  have hb := usc_bddAbove_range hg
  obtain ⟨a,_,hat,ha⟩ := exists_seq_tendsto_sSup (Set.range_nonempty g) hb
  choose s hs using ha
  obtain ⟨u,φ,hφ,ht⟩ := SeqCompactSpace.tendsto_subseq s
  have hv : Tendsto (g ∘ (s ∘ φ)) atTop (𝓝 (sSup (Set.range g))) := by
    simpa only [Function.comp_def,hs] using hat.comp hφ.tendsto_atTop
  have hle := usc_limit_le (hg u) ht hv
  exact ⟨u,fun v => (le_csSup hb (Set.mem_range_self v)).trans hle⟩

end ClarkeProof


open Set Filter Topology
open ClarkeGradients ClarkeGradients.MaxFunctions

namespace ClarkeProof

variable {n : ℕ} {U : Type*} [TopologicalSpace U] [SeqCompactSpace U] [Nonempty U]
local notation "E" => EuclideanSpace ℝ (Fin n)
variable {g : EuclideanSpace ℝ (Fin n) → U → ℝ}

omit [SeqCompactSpace U] [Nonempty U] in
lemma piece_usc (ha : UpperSemicontinuous (fun p : E × U => g p.1 p.2)) (x : E) :
    UpperSemicontinuous (g x) := by
  intro u
  exact (ha (x,u)).comp (continuous_const.prodMk continuous_id).continuousAt

omit [Nonempty U] in
lemma piece_le_max (ha : UpperSemicontinuous (fun p : E × U => g p.1 p.2))
    (x : E) (u : U) : g x u ≤ maxFunction g x :=
  le_ciSup (usc_bddAbove_range (piece_usc ha x)) u

lemma maximizers_nonempty (ha : UpperSemicontinuous (fun p : E × U => g p.1 p.2))
    (x : E) : (maximizers g x).Nonempty := by
  obtain ⟨u,hu⟩ := usc_exists_max (piece_usc ha x)
  refine ⟨u,le_antisymm (piece_le_max ha x u) ?_⟩
  exact ciSup_le hu

lemma max_lipschitzOn (ha : UpperSemicontinuous (fun p : E × U => g p.1 p.2))
    {B : Set E} {K : NNReal} (hb : ∀ u, LipschitzOnWith K (fun y => g y u) B) :
    LipschitzOnWith K (maxFunction g) B := by
  apply LipschitzOnWith.of_le_add_mul K
  intro x hx y hy
  obtain ⟨u,hu⟩ := maximizers_nonempty ha x
  have h₁ := (hb u).dist_le_mul x hx y hy
  have h₂ := piece_le_max ha y u
  change g x u = maxFunction g x at hu
  rw [Real.dist_eq] at h₁
  have h₃ := (abs_le.mp h₁).2
  linarith

lemma max_lipschitzOnBounded (ha : UpperSemicontinuous (fun p : E × U => g p.1 p.2))
    (hb : ∀ B : Set E, Bornology.IsBounded B →
      ∃ K : NNReal, ∀ u, LipschitzOnWith K (fun y => g y u) B) :
    Shared.LipschitzOnBounded (maxFunction g) := by
  intro B hB
  obtain ⟨K,hK⟩ := hb B hB
  exact ⟨K,max_lipschitzOn ha hK⟩

lemma continuous_of_lipschitzOnBounded {f : E → ℝ} (hf : Shared.LipschitzOnBounded f) :
    Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨K,hK⟩ := hf (Metric.ball x 1) Metric.isBounded_ball
  exact hK.continuousOn.continuousAt (Metric.ball_mem_nhds x (by norm_num))

omit [Nonempty U] in
lemma active_limit (ha : UpperSemicontinuous (fun p : E × U => g p.1 p.2))
    (hf : Continuous (maxFunction g)) {xs : ℕ → E} {us : ℕ → U} {x : E} {u : U}
    (hx : Tendsto xs atTop (𝓝 x)) (hu : Tendsto us atTop (𝓝 u))
    (hm : ∀ j, us j ∈ maximizers g (xs j)) : u ∈ maximizers g x := by
  apply le_antisymm (piece_le_max ha x u)
  apply usc_limit_le (ha (x,u)) (hx.prodMk_nhds hu)
  have ht := (hf.tendsto x).comp hx
  exact ht.congr' (Filter.Eventually.of_forall fun j => (hm j).symm)

noncomputable def activeGradients (g : E → U → ℝ) (x : E) : Set E :=
  ⋃ u ∈ maximizers g x, Shared.generalizedGradient (fun y => g y u) x

lemma activeGradients_nonempty (ha : UpperSemicontinuous (fun p : E × U => g p.1 p.2))
    (hb : ∀ B : Set E, Bornology.IsBounded B →
      ∃ K : NNReal, ∀ u, LipschitzOnWith K (fun y => g y u) B) (x : E) :
    (activeGradients g x).Nonempty := by
  obtain ⟨u,hu⟩ := maximizers_nonempty ha x
  have hpiece : Shared.LipschitzOnBounded (fun y => g y u) := by
    intro B hB; obtain ⟨K,hK⟩ := hb B hB; exact ⟨K,hK u⟩
  obtain ⟨z,hz⟩ := generalizedGradient_nonempty hpiece x
  exact ⟨z,Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨hu,hz⟩⟩⟩

lemma activeGradients_isCompact (ha : UpperSemicontinuous (fun p : E × U => g p.1 p.2))
    (hb : ∀ B : Set E, Bornology.IsBounded B →
      ∃ K : NNReal, ∀ u, LipschitzOnWith K (fun y => g y u) B)
    (hd : SeqUpperSemicontinuous
      (fun p : E × U => Shared.generalizedGradient (fun y => g y p.2) p.1)) (x : E) :
    IsCompact (activeGradients g x) := by
  classical
  have hf := continuous_of_lipschitzOnBounded (max_lipschitzOnBounded ha hb)
  have hc : IsClosed (activeGradients g x) := by
    apply IsSeqClosed.isClosed
    intro z z₀ hz hzt
    have he : ∀ j, ∃ u, u ∈ maximizers g x ∧
        z j ∈ Shared.generalizedGradient (fun y => g y u) x := by
      intro j
      simpa only [activeGradients, Set.mem_iUnion, exists_prop] using hz j
    choose us hum hzg using he
    obtain ⟨u,φ,hφ,hut⟩ := SeqCompactSpace.tendsto_subseq us
    have hu := active_limit ha hf (x := x) (xs := fun _ => x) tendsto_const_nhds hut (fun j => hum (φ j))
    have hmem := hd (fun j => (x,us (φ j))) (x,u) (z ∘ φ) z₀
      (tendsto_const_nhds.prodMk_nhds hut) (hzt.comp hφ.tendsto_atTop)
      (fun j => hzg (φ j))
    exact Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨hu,hmem⟩⟩
  obtain ⟨K,hK⟩ := hb (Metric.ball x 1) Metric.isBounded_ball
  apply (isCompact_closedBall (0 : E) (K : ℝ)).of_isClosed_subset hc
  intro z hz
  obtain ⟨u,_,hu⟩ : ∃ u, u ∈ maximizers g x ∧
      z ∈ Shared.generalizedGradient (fun y => g y u) x := by
    simpa only [activeGradients, Set.mem_iUnion, exists_prop] using hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    generalizedGradient_norm_le Metric.isOpen_ball (Metric.mem_ball_self (by norm_num)) (hK u) hu

end ClarkeProof


open Set Filter MeasureTheory Topology
open scoped Topology

namespace ClarkeProof

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma ae_line_differentiable {f : E → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (v : E) :
    ∀ᵐ y : E, ∀ᵐ t : ℝ, DifferentiableAt ℝ f (y + t • v) := by
  have hm : MeasurableSet {p : E × ℝ | DifferentiableAt ℝ f (p.1 + p.2 • v)} :=
    (measurableSet_of_differentiableAt ℝ f).preimage (by fun_prop)
  apply (Measure.ae_ae_comm hm).mpr
  apply ae_of_all
  intro t
  exact (measurePreserving_add_right (volume : Measure E) (t • v)).quasiMeasurePreserving.ae
    hf.ae_differentiableAt

lemma lipschitz_line {f : E → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    (y v : E) : LipschitzWith (K * ‖v‖₊) (fun t : ℝ => f (y + t • v)) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  calc
    dist (f (y + s • v)) (f (y + t • v)) ≤ K * dist (y + s • v) (y + t • v) :=
      hf.dist_le_mul _ _
    _ = (K * ‖v‖₊ : NNReal) * dist s t := by
      simp only [dist_eq_norm, add_sub_add_left_eq_sub, ← sub_smul,
        norm_smul, Real.norm_eq_abs, NNReal.coe_mul, coe_nnnorm]
      ring

lemma line_increment_le_of_ae {f : E → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    (y v : E) {t c : ℝ} (ht : 0 ≤ t)
    (hd : ∀ᵐ s : ℝ, DifferentiableAt ℝ f (y + s • v))
    (hb : ∀ s ∈ Icc 0 t, DifferentiableAt ℝ f (y + s • v) →
      fderiv ℝ f (y + s • v) v ≤ c) :
    f (y + t • v) - f y ≤ c * t := by
  let F : ℝ → ℝ := fun s => f (y + s • v)
  have hAC : AbsolutelyContinuousOnInterval F 0 t :=
    (lipschitz_line hf y v).lipschitzOnWith.absolutelyContinuousOnInterval
  have hder : ∀ᵐ s : ℝ, s ∈ Icc 0 t → deriv F s ≤ c := by
    filter_upwards [hd] with s hs hst
    have hl : HasDerivAt (fun r : ℝ => y + r • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add y
    have he := hs.hasFDerivAt.comp_hasDerivAt s hl
    change HasDerivAt F (fderiv ℝ f (y + s • v) v) s at he
    rw [he.deriv]
    exact hb s hst hs
  have hi := intervalIntegral.integral_mono_ae_restrict ht hAC.intervalIntegrable_deriv
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => c) volume 0 t)
    ((ae_restrict_iff' measurableSet_Icc).mpr hder)
  rw [hAC.integral_deriv_eq_sub] at hi
  simpa [F, mul_comm] using hi

end ClarkeProof


open Set Filter MeasureTheory Topology

namespace ClarkeProof

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma line_increment_le_of_gradient_bound {f : E → ℝ} {K : NNReal}
    (hf : LipschitzWith K f) (x v : E) {r t c : ℝ} (ht : 0 ≤ t)
    (htv : t * ‖v‖ < r / 2)
    (hb : ∀ z ∈ Metric.ball x r, DifferentiableAt ℝ f z → fderiv ℝ f z v ≤ c)
    {y : E} (hy : y ∈ Metric.ball x (r / 2)) :
    f (y + t • v) - f y ≤ c * t := by
  have hdense := Measure.dense_of_ae (μ := volume) (ae_line_differentiable hf v)
  obtain ⟨z,hz,hzt⟩ := mem_closure_iff_seq_limit.mp (hdense y)
  have he : ∀ᶠ j in atTop, z j ∈ Metric.ball x (r / 2) :=
    hzt.eventually (Metric.isOpen_ball.mem_nhds hy)
  apply le_of_tendsto ((hf.continuous.tendsto _ |>.comp
    (hzt.add_const (t • v))).sub (hf.continuous.tendsto _ |>.comp hzt))
  filter_upwards [he] with j hj
  apply line_increment_le_of_ae hf (z j) v ht (hz j)
  intro s hs hds
  apply hb _ ?_ hds
  rw [Metric.mem_ball] at hj ⊢
  have hnorm : ‖s • v‖ ≤ t * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    exact mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)
  calc
    dist (z j + s • v) x ≤ dist (z j + s • v) (z j) + dist (z j) x := dist_triangle _ _ _
    _ = ‖s • v‖ + dist (z j) x := by rw [dist_eq_norm]; simp
    _ ≤ t * ‖v‖ + dist (z j) x := add_le_add hnorm (le_refl _)
    _ < r := by linarith

end ClarkeProof


open Set Filter Topology
open ClarkeGradients

noncomputable section

namespace ClarkeProof

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma differentiable_oneSided {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (v : E) :
    MaxFunctions.HasOneSidedDirDeriv f x v (inner ℝ (gradient f x) v) := by
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hf' : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by simpa using hf.hasFDerivAt
  have hd := hf'.comp_hasDerivAt 0 hl
  simpa [MaxFunctions.HasOneSidedDirDeriv, Function.comp_def, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right

abbrev quotientFilter : Filter (E × ℝ) := 𝓝 (0 : E) ×ˢ 𝓝[>] (0 : ℝ)

instance quotientFilter_neBot : NeBot (quotientFilter (n := n)) := by
  unfold quotientFilter
  infer_instance

def dirQuotient (f : E → ℝ) (x v : E) (p : E × ℝ) : ℝ :=
  (f (x + p.1 + p.2 • v) - f (x + p.1)) / p.2

lemma quotient_base_tendsto (x : E) :
    Tendsto (fun p : E × ℝ => x + p.1) quotientFilter (𝓝 x) := by
  simpa using tendsto_const_nhds.add (tendsto_fst :
    Tendsto (Prod.fst : E × ℝ → E) quotientFilter (𝓝 0))

lemma quotient_tip_tendsto (x v : E) :
    Tendsto (fun p : E × ℝ => x + p.1 + p.2 • v) quotientFilter (𝓝 x) := by
  have ht : Tendsto (Prod.snd : E × ℝ → ℝ) quotientFilter (𝓝 0) :=
    tendsto_snd.mono_right nhdsWithin_le_nhds
  simpa using (quotient_base_tendsto x).add (ht.smul_const v)

lemma quotient_positive : ∀ᶠ p : E × ℝ in quotientFilter, 0 < p.2 :=
  tendsto_snd.eventually self_mem_nhdsWithin

lemma quotient_eventually_abs_le {f : E → ℝ} (hf : Shared.LipschitzOnBounded f)
    (x v : E) : ∃ C : ℝ, ∀ᶠ p in quotientFilter, |dirQuotient f x v p| ≤ C := by
  obtain ⟨K,hK⟩ := hf (Metric.ball x 1) Metric.isBounded_ball
  refine ⟨K * ‖v‖, ?_⟩
  have hx : Metric.ball x 1 ∈ 𝓝 x := Metric.ball_mem_nhds x zero_lt_one
  filter_upwards [(quotient_base_tendsto x).eventually hx,
    (quotient_tip_tendsto x v).eventually hx, quotient_positive (n := n)] with p hp hq ht
  have h := hK.dist_le_mul _ hq _ hp
  have hb : |f (x + p.1 + p.2 • v) - f (x + p.1)| ≤ (K : ℝ) * (p.2 * ‖v‖) := by
    simpa [Real.dist_eq, dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_pos ht] using h
  rw [dirQuotient, abs_div, abs_of_pos ht]
  exact (div_le_iff₀ ht).mpr (by nlinarith [hb])

lemma quotient_bddAbove {f : E → ℝ} (hf : Shared.LipschitzOnBounded f) (x v : E) :
    quotientFilter.IsBoundedUnder (· ≤ ·) (dirQuotient f x v) := by
  obtain ⟨C,hC⟩ := quotient_eventually_abs_le hf x v
  exact isBoundedUnder_of_eventually_le (hC.mono fun p hp => (le_abs_self _).trans hp)

lemma quotient_bddBelow {f : E → ℝ} (hf : Shared.LipschitzOnBounded f) (x v : E) :
    quotientFilter.IsBoundedUnder (· ≥ ·) (dirQuotient f x v) := by
  obtain ⟨C,hC⟩ := quotient_eventually_abs_le hf x v
  exact isBoundedUnder_of_eventually_ge (hC.mono fun p hp => (abs_le.mp hp).1)

lemma eventually_slice_lt {f : E → ℝ} (hf : Shared.LipschitzOnBounded f)
    (x v : E) {c : ℝ} (hc : Shared.genDirDeriv f x v < c) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), (f (x + t • v) - f x) / t < c := by
  have he : ∀ᶠ p in quotientFilter, dirQuotient f x v p < c :=
    eventually_lt_of_limsup_lt hc (quotient_bddAbove hf x v)
  have ht : Tendsto (fun t : ℝ => ((0 : E), t)) (𝓝[>] 0) quotientFilter :=
    tendsto_const_nhds.prodMk tendsto_id
  simpa [dirQuotient] using ht.eventually he

end ClarkeProof


open Set Filter Topology
open ClarkeGradients

namespace ClarkeProof

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma gradientLimit_pairing_le {f : E → ℝ} (hf : Shared.LipschitzOnBounded f)
    (x v : E) {z : E} (hz : z ∈ Shared.gradientLimits f x) :
    inner ℝ z v ≤ Shared.genDirDeriv f x v := by
  obtain ⟨h,hh,hd,hg⟩ := hz
  apply le_limsup_of_le (quotient_bddAbove hf x v)
  intro b hb
  obtain ⟨pa,hpa,pb,hpb,hrect⟩ := eventually_prod_iff.mp hb
  apply le_of_tendsto (hg.inner (tendsto_const_nhds (x := v)))
  filter_upwards [hh.eventually hpa] with j hj
  apply le_of_tendsto (differentiable_oneSided (hd j) v)
  filter_upwards [hpb] with t ht
  exact hrect hj ht

lemma generalized_pairing_le {f : E → ℝ} (hf : Shared.LipschitzOnBounded f)
    (x v : E) {z : E} (hz : z ∈ Shared.generalizedGradient f x) :
    inner ℝ z v ≤ Shared.genDirDeriv f x v := by
  apply convexHull_min (fun w hw => gradientLimit_pairing_le hf x v hw) ?_ hz
  intro a ha b hb s t hs ht hst
  change inner ℝ (s • a + t • b) v ≤ Shared.genDirDeriv f x v
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have h₁ := mul_le_mul_of_nonneg_left ha hs
  have h₂ := mul_le_mul_of_nonneg_left hb ht
  calc
    _ ≤ s * Shared.genDirDeriv f x v + t * Shared.genDirDeriv f x v := add_le_add h₁ h₂
    _ = Shared.genDirDeriv f x v := by rw [← add_mul, hst, one_mul]

end ClarkeProof


open Set Filter Topology
open ClarkeGradients

namespace ClarkeProof

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma local_gradient_pairing_lt {f : E → ℝ} (hf : Shared.LipschitzOnBounded f)
    (x v : E) {c : ℝ}
    (hc : ∀ z ∈ Shared.gradientLimits f x, inner ℝ z v < c) :
    ∃ r > 0, ∀ y ∈ Metric.ball x r, DifferentiableAt ℝ f y →
      inner ℝ (gradient f y) v < c := by
  classical
  by_contra hn
  push Not at hn
  have hex : ∀ j : ℕ, ∃ y ∈ Metric.ball x (1 / ((j : ℝ) + 1)),
      DifferentiableAt ℝ f y ∧ c ≤ inner ℝ (gradient f y) v := by
    intro j
    exact hn _ (by positivity)
  choose y hy hd hp using hex
  have hyt : Tendsto y atTop (𝓝 x) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun j => dist_nonneg) (fun j => (hy j).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨K,hK⟩ := hf (Metric.ball x 1) Metric.isBounded_ball
  have hbound : ∀ j, gradient f (y j) ∈ Metric.closedBall (0 : E) K := by
    intro j
    have hj : y j ∈ Metric.ball x 1 := by
      apply Metric.ball_subset_ball _ (hy j)
      exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) j])
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      norm_gradient_le_lipschitzOn (Metric.isOpen_ball.mem_nhds hj) hK
  obtain ⟨z,_,φ,hφ,hzt⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hbound
  have hz : z ∈ Shared.gradientLimits f x := by
    refine ⟨fun j => y (φ j) - x, ?_, ?_, ?_⟩
    · simpa using (hyt.comp hφ.tendsto_atTop).sub_const x
    · intro j; simpa using hd (φ j)
    · simpa [Function.comp_def] using hzt
  have hle : c ≤ inner ℝ z v :=
    ge_of_tendsto (hzt.inner (tendsto_const_nhds (x := v))) (Eventually.of_forall fun j => hp (φ j))
  exact (hc z hz).not_ge hle

end ClarkeProof


open Set Filter Topology
open ClarkeGradients

namespace ClarkeProof

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma local_line_increment {f : E → ℝ} {K : NNReal} {x v y : E} {r t c : ℝ}
    (hf : LipschitzOnWith K f (Metric.ball x r)) (ht : 0 ≤ t)
    (htv : t * ‖v‖ < r / 2) (hy : y ∈ Metric.ball x (r / 2))
    (hb : ∀ z ∈ Metric.ball x r, DifferentiableAt ℝ f z →
      inner ℝ (gradient f z) v ≤ c) :
    f (y + t • v) - f y ≤ c * t := by
  obtain ⟨g,hg,heq⟩ := hf.extend_real
  have hr : 0 < r := by
    have := Metric.nonempty_ball.mp ⟨y,hy⟩
    linarith
  have hy' : y ∈ Metric.ball x r := (Metric.ball_subset_ball (by linarith)) hy
  have htip : y + t • v ∈ Metric.ball x r := by
    rw [Metric.mem_ball] at hy ⊢
    have hnorm : ‖t • v‖ = t * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    calc
      dist (y + t • v) x ≤ dist (y + t • v) y + dist y x := dist_triangle _ _ _
      _ = t * ‖v‖ + dist y x := by rw [dist_eq_norm]; simp [hnorm]
      _ < r := by linarith
  rw [heq htip, heq hy']
  apply line_increment_le_of_gradient_bound hg x v ht htv _ hy
  intro z hz hdz
  have he : f =ᶠ[𝓝 z] g :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨Metric.ball x r, Metric.isOpen_ball.mem_nhds hz, heq⟩
  have hdf : DifferentiableAt ℝ f z := hdz.congr_of_eventuallyEq he
  rw [← he.fderiv_eq]
  simpa only [inner_gradient_left] using hb z hz hdf

lemma genDirDeriv_le_of_local_gradient {f : E → ℝ} (hf : Shared.LipschitzOnBounded f)
    (x v : E) {r c : ℝ} (hr : 0 < r)
    (hb : ∀ z ∈ Metric.ball x r, DifferentiableAt ℝ f z →
      inner ℝ (gradient f z) v ≤ c) : Shared.genDirDeriv f x v ≤ c := by
  obtain ⟨K,hK⟩ := hf (Metric.ball x r) Metric.isBounded_ball
  apply limsup_le_of_le (quotient_bddBelow hf x v).isCoboundedUnder_le
  have htime : Tendsto (fun p : E × ℝ => p.2 * ‖v‖) quotientFilter (𝓝 0) := by
    have ht : Tendsto (Prod.snd : E × ℝ → ℝ) quotientFilter (𝓝 0) :=
      tendsto_snd.mono_right nhdsWithin_le_nhds
    simpa using ht.mul_const ‖v‖
  filter_upwards [(quotient_base_tendsto x).eventually
    (Metric.ball_mem_nhds x (half_pos hr)),
    htime.eventually (gt_mem_nhds (half_pos hr)), quotient_positive (n := n)] with p hy ht hp
  exact (div_le_iff₀ hp).mpr (local_line_increment hK hp.le ht hy hb)

end ClarkeProof


open Set Filter Topology
open ClarkeGradients

namespace ClarkeProof

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma support_isGreatest {f : E → ℝ} (hf : Shared.LipschitzOnBounded f) (x v : E) :
    IsGreatest ((fun z => inner ℝ z v) '' Shared.generalizedGradient f x)
      (Shared.genDirDeriv f x v) := by
  obtain ⟨z,hz,hm⟩ := (gradientLimits_isCompact hf x).exists_isMaxOn
    (gradientLimits_nonempty hf x) (show ContinuousOn (fun z : E => inner ℝ z v)
      (Shared.gradientLimits f x) by fun_prop)
  have hle : Shared.genDirDeriv f x v ≤ inner ℝ z v := by
    apply le_of_forall_gt
    intro c hc
    let b := (inner ℝ z v + c) / 2
    have hzb : inner ℝ z v < b := by dsimp [b]; linarith
    have hbc : b < c := by dsimp [b]; linarith
    obtain ⟨r,hr,hb⟩ := local_gradient_pairing_lt hf x v
      (fun w hw => (hm hw).trans_lt hzb)
    exact (genDirDeriv_le_of_local_gradient hf x v hr
      (fun y hy hd => (hb y hy hd).le)).trans_lt hbc
  have he : inner ℝ z v = Shared.genDirDeriv f x v :=
    le_antisymm (gradientLimit_pairing_le hf x v hz) hle
  constructor
  · exact ⟨z,subset_convexHull ℝ _ hz,he⟩
  · rintro _ ⟨w,hw,rfl⟩
    exact generalized_pairing_le hf x v hw

lemma mem_generalizedGradient_iff {f : E → ℝ} (hf : Shared.LipschitzOnBounded f)
    (x z : E) : z ∈ Shared.generalizedGradient f x ↔
      ∀ v, inner ℝ z v ≤ Shared.genDirDeriv f x v := by
  constructor
  · intro hz v; exact generalized_pairing_le hf x v hz
  · intro hz
    by_contra hn
    obtain ⟨l,c,hc,hcz⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ (Shared.gradientLimits f x))
      (generalizedGradient_isCompact hf x).isClosed hn
    let v := (InnerProductSpace.toDual ℝ E).symm l
    have hi : ∀ w : E, inner ℝ w v = l w := by
      intro w
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    obtain ⟨w,hw,he⟩ := (support_isGreatest hf x v).1
    change inner ℝ w v = Shared.genDirDeriv f x v at he
    have hzw := hz v
    rw [← he, hi, hi] at hzw
    exact (hzw.trans_lt (hc w hw)).not_gt hcz

end ClarkeProof


open Set Filter Topology
open ClarkeGradients ClarkeGradients.MaxFunctions

namespace ClarkeProof

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma oneSided_le_of_le {f k : E → ℝ} {x v : E} {a b : ℝ}
    (hk : HasOneSidedDirDeriv k x v a) (hf : HasOneSidedDirDeriv f x v b)
    (he : k x = f x) (hle : ∀ y, k y ≤ f y) : a ≤ b := by
  apply le_of_tendsto_of_tendsto hk hf
  filter_upwards [self_mem_nhdsWithin] with t ht
  apply div_le_div_of_nonneg_right _ (le_of_lt ht)
  rw [he]
  exact sub_le_sub_right (hle _) _

lemma oneSided_le_genDir_of_le {f k : E → ℝ} {x v : E} {a : ℝ}
    (hf : Shared.LipschitzOnBounded f) (hk : HasOneSidedDirDeriv k x v a)
    (he : k x = f x) (hle : ∀ y, k y ≤ f y) : a ≤ Shared.genDirDeriv f x v := by
  by_contra! h
  let c := (Shared.genDirDeriv f x v + a)/2
  have hc₁ : Shared.genDirDeriv f x v < c := by dsimp [c]; linarith
  have hc₂ : c < a := by dsimp [c]; linarith
  have h₁ := eventually_slice_lt hf x v hc₁
  have h₂ := hk.eventually (lt_mem_nhds hc₂)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t,ht,h₁,h₂⟩ := (hpos.and (h₁.and h₂)).exists
  have h₃ : (k (x+t•v)-k x)/t ≤ (f (x+t•v)-f x)/t := by
    apply div_le_div_of_nonneg_right _ (le_of_lt ht)
    rw [he]; exact sub_le_sub_right (hle _) _
  linarith

variable {U : Type*} [TopologicalSpace U] [SeqCompactSpace U] [Nonempty U]
variable {g : EuclideanSpace ℝ (Fin n) → U → ℝ}

omit [TopologicalSpace U] [SeqCompactSpace U] [Nonempty U] in
lemma piece_lipschitzOnBounded
    (hb : ∀ B : Set E, Bornology.IsBounded B →
      ∃ K : NNReal, ∀ u, LipschitzOnWith K (fun y => g y u) B) (u : U) :
    Shared.LipschitzOnBounded (fun y => g y u) := by
  intro B hB; obtain ⟨K,hK⟩ := hb B hB; exact ⟨K,hK u⟩

omit [Nonempty U] in
lemma active_piece_gradient_eq
    (ha : UpperSemicontinuous (fun p : E × U => g p.1 p.2))
    (hb : ∀ B : Set E, Bornology.IsBounded B →
      ∃ K : NNReal, ∀ u, LipschitzOnWith K (fun y => g y u) B)
    (hc : ∀ x u v, HasOneSidedDirDeriv (fun y => g y u) x v
      (Shared.genDirDeriv (fun y => g y u) x v))
    {x : E} (hx : DifferentiableAt ℝ (maxFunction g) x) {u : U}
    (hu : u ∈ maximizers g x) {z : E}
    (hz : z ∈ Shared.generalizedGradient (fun y => g y u) x) :
    z = gradient (maxFunction g) x := by
  have hle : ∀ v, inner ℝ z v ≤ inner ℝ (gradient (maxFunction g) x) v := by
    intro v
    have h₁ := (support_isGreatest (piece_lipschitzOnBounded hb u) x v).2 ⟨z,hz,rfl⟩
    exact h₁.trans (oneSided_le_of_le (hc x u v) (differentiable_oneSided hx v)
      hu (fun y => piece_le_max ha y u))
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  apply le_antisymm
  · simpa only [inner_sub_left, sub_nonpos] using hle (z-gradient (maxFunction g) x)
  · exact real_inner_self_nonneg

lemma max_gradient_hull
    (ha : UpperSemicontinuous (fun p : E × U => g p.1 p.2))
    (hb : ∀ B : Set E, Bornology.IsBounded B →
      ∃ K : NNReal, ∀ u, LipschitzOnWith K (fun y => g y u) B)
    (hc : ∀ x u v, HasOneSidedDirDeriv (fun y => g y u) x v
      (Shared.genDirDeriv (fun y => g y u) x v))
    (hd : SeqUpperSemicontinuous
      (fun p : E × U => Shared.generalizedGradient (fun y => g y p.2) p.1)) (x : E) :
    Shared.generalizedGradient (maxFunction g) x = convexHull ℝ (activeGradients g x) := by
  classical
  have hf := max_lipschitzOnBounded ha hb
  apply Set.Subset.antisymm
  · apply convexHull_min _ (convex_convexHull ℝ _)
    intro z hz
    obtain ⟨h,hh,hdf,hgt⟩ := hz
    choose us hum using fun j => maximizers_nonempty ha (x+h j)
    obtain ⟨u,φ,hφ,hut⟩ := SeqCompactSpace.tendsto_subseq us
    have hxt : Tendsto (fun j => x+h (φ j)) atTop (𝓝 x) := by
      simpa using tendsto_const_nhds.add (hh.comp hφ.tendsto_atTop)
    have hu := active_limit ha (continuous_of_lipschitzOnBounded hf) hxt hut
      (fun j => hum (φ j))
    have hseq : ∀ j, gradient (maxFunction g) (x+h (φ j)) ∈
        Shared.generalizedGradient (fun y => g y (us (φ j))) (x+h (φ j)) := by
      intro j
      obtain ⟨w,hw⟩ := generalizedGradient_nonempty
        (piece_lipschitzOnBounded hb (us (φ j))) (x+h (φ j))
      rwa [active_piece_gradient_eq ha hb hc (hdf (φ j)) (hum (φ j)) hw] at hw
    have hzmem := hd (fun j => (x+h (φ j),us (φ j))) (x,u)
      (fun j => gradient (maxFunction g) (x+h (φ j))) z (hxt.prodMk_nhds hut)
      (hgt.comp hφ.tendsto_atTop) hseq
    exact subset_convexHull ℝ _ (Set.mem_iUnion.mpr ⟨u,Set.mem_iUnion.mpr ⟨hu,hzmem⟩⟩)
  · apply convexHull_min _ (convex_convexHull ℝ _)
    intro z hz
    obtain ⟨u,hu,hz⟩ : ∃ u, u ∈ maximizers g x ∧
        z ∈ Shared.generalizedGradient (fun y => g y u) x := by
      simpa only [activeGradients, Set.mem_iUnion, exists_prop] using hz
    apply (mem_generalizedGradient_iff hf x z).mpr
    intro v
    have h₁ := (support_isGreatest (piece_lipschitzOnBounded hb u) x v).2 ⟨z,hz,rfl⟩
    exact h₁.trans (oneSided_le_genDir_of_le hf (hc x u v) hu (fun y => piece_le_max ha y u))

lemma inner_le_on_convexHull {A : Set E} {v : E} {m : ℝ}
    (h : ∀ z ∈ A, inner ℝ z v ≤ m) : ∀ z ∈ convexHull ℝ A, inner ℝ z v ≤ m := by
  apply convexHull_min h
  intro x hx y hy a b ha hb hab
  change inner ℝ (a • x + b • y) v ≤ m
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have h₁ := mul_le_mul_of_nonneg_left hx ha
  have h₂ := mul_le_mul_of_nonneg_left hy hb
  calc
    a * inner ℝ x v + b * inner ℝ y v ≤ a * m + b * m := add_le_add h₁ h₂
    _ = m := by rw [← add_mul, hab, one_mul]

lemma max_directional
    (ha : UpperSemicontinuous (fun p : E × U => g p.1 p.2))
    (hb : ∀ B : Set E, Bornology.IsBounded B →
      ∃ K : NNReal, ∀ u, LipschitzOnWith K (fun y => g y u) B)
    (hc : ∀ x u v, HasOneSidedDirDeriv (fun y => g y u) x v
      (Shared.genDirDeriv (fun y => g y u) x v))
    (hd : SeqUpperSemicontinuous
      (fun p : E × U => Shared.generalizedGradient (fun y => g y p.2) p.1)) (x v : E) :
    HasOneSidedDirDeriv (maxFunction g) x v (Shared.genDirDeriv (maxFunction g) x v) ∧
    IsGreatest {r : ℝ | ∃ u ∈ maximizers g x,
      ∃ z ∈ Shared.generalizedGradient (fun y => g y u) x, r = inner ℝ z v}
      (Shared.genDirDeriv (maxFunction g) x v) := by
  classical
  have hf := max_lipschitzOnBounded ha hb
  obtain ⟨z,hz,hm⟩ := (activeGradients_isCompact ha hb hd x).exists_isMaxOn
    (activeGradients_nonempty ha hb x) (show ContinuousOn (fun z : E => inner ℝ z v)
      (activeGradients g x) by fun_prop)
  have hhull := max_gradient_hull ha hb hc hd x
  have hzmax : inner ℝ z v = Shared.genDirDeriv (maxFunction g) x v := by
    apply le_antisymm
    · apply (support_isGreatest hf x v).2
      refine ⟨z,?_,rfl⟩
      rw [hhull]; exact subset_convexHull ℝ _ hz
    · obtain ⟨w,hw,he⟩ := (support_isGreatest hf x v).1
      rw [hhull] at hw
      rw [← he]
      exact inner_le_on_convexHull (fun y hy => hm hy) w hw
  obtain ⟨u,hu,hzu⟩ : ∃ u, u ∈ maximizers g x ∧
      z ∈ Shared.generalizedGradient (fun y => g y u) x := by
    simpa only [activeGradients, Set.mem_iUnion, exists_prop] using hz
  have hpiece : Shared.genDirDeriv (fun y => g y u) x v =
      Shared.genDirDeriv (maxFunction g) x v := by
    apply le_antisymm (oneSided_le_genDir_of_le hf (hc x u v) hu
      (fun y => piece_le_max ha y u))
    rw [← hzmax]
    exact (support_isGreatest (piece_lipschitzOnBounded hb u) x v).2 ⟨z,hzu,rfl⟩
  constructor
  · apply tendsto_order.mpr
    constructor
    · intro a ha'
      have ht := (hc x u v).eventually (lt_mem_nhds (hpiece.symm ▸ ha'))
      filter_upwards [ht,self_mem_nhdsWithin] with t ht hpos
      apply ht.trans_le
      apply div_le_div_of_nonneg_right _ (le_of_lt hpos)
      change g x u = maxFunction g x at hu
      rw [hu]
      exact sub_le_sub_right (piece_le_max ha (x+t•v) u) _
    · intro b hb'; exact eventually_slice_lt hf x v hb'
  · constructor
    · exact ⟨u,hu,z,hzu,hzmax.symm⟩
    · rintro r ⟨u',hu',z',hz',rfl⟩
      rw [← hzmax]
      exact hm (Set.mem_iUnion.mpr ⟨u',Set.mem_iUnion.mpr ⟨hu',hz'⟩⟩)

end ClarkeProof


open ClarkeGradients ClarkeGradients.MaxFunctions

namespace ClarkeProof

/-- Clarke (1975), Theorem (2.1). Let `U` be a (nonempty) sequentially compact space and
`g : ℝⁿ × U → ℝ` satisfy
(a) `g` is upper semicontinuous in `(x, u)`;
(b) `g` is locally Lipschitz in `x`, uniformly for `u ∈ U`;
(c) `g°ₓ(x, u; ·) = g'ₓ(x, u; ·)` (the one-sided derivative in `x` exists and equals the
    generalized directional derivative in `x`), for all `x, u`;
(d) `(x, u) ↦ ∂ₓg(x, u)` is upper semicontinuous (sequential closed graph).
Then, with `f(x) = max_u g(x, u)` and `M(x) = {u : g(x, u) = f(x)}`:
(1) `f` is locally Lipschitz; (2) `f'(x; v)` exists; (3)
`f'(x; v) = f°(x; v) = max {ζ · v : ζ ∈ ∂ₓg(x, u), u ∈ M(x)}`; (4) `∂f(x)` is the convex
hull of `{∂ₓg(x, u) : u ∈ M(x)}`. -/
theorem native_max_recovery
    {n : ℕ} {U : Type*} [TopologicalSpace U] [SeqCompactSpace U] [Nonempty U]
    (g : EuclideanSpace ℝ (Fin n) → U → ℝ)
    (ha : UpperSemicontinuous (fun p : EuclideanSpace ℝ (Fin n) × U => g p.1 p.2))
    (hb : ∀ B : Set (EuclideanSpace ℝ (Fin n)), Bornology.IsBounded B →
      ∃ K : NNReal, ∀ u : U, LipschitzOnWith K (fun y => g y u) B)
    (hc : ∀ (x : EuclideanSpace ℝ (Fin n)) (u : U) (v : EuclideanSpace ℝ (Fin n)),
      HasOneSidedDirDeriv (fun y => g y u) x v (Shared.genDirDeriv (fun y => g y u) x v))
    (hd : SeqUpperSemicontinuous
      (fun p : EuclideanSpace ℝ (Fin n) × U => Shared.generalizedGradient (fun y => g y p.2) p.1)) :
    Shared.LipschitzOnBounded (maxFunction g) ∧
    (∀ x v : EuclideanSpace ℝ (Fin n),
      HasOneSidedDirDeriv (maxFunction g) x v (Shared.genDirDeriv (maxFunction g) x v) ∧
      IsGreatest {r : ℝ | ∃ u ∈ maximizers g x, ∃ ζ ∈ Shared.generalizedGradient (fun y => g y u) x,
          r = inner ℝ ζ v}
        (Shared.genDirDeriv (maxFunction g) x v)) ∧
    (∀ x : EuclideanSpace ℝ (Fin n),
      Shared.generalizedGradient (maxFunction g) x =
        convexHull ℝ (⋃ u ∈ maximizers g x, Shared.generalizedGradient (fun y => g y u) x)) := by
  exact ⟨max_lipschitzOnBounded ha hb, max_directional ha hb hc hd,
    max_gradient_hull ha hb hc hd⟩

end ClarkeProof



namespace ClarkeGradients.MaxFunctions

/-- Clarke (1975), Theorem (2.1). Let `U` be a (nonempty) sequentially compact space and
`g : ℝⁿ × U → ℝ` satisfy
(a) `g` is upper semicontinuous in `(x, u)`;
(b) `g` is locally Lipschitz in `x`, uniformly for `u ∈ U`;
(c) `g°ₓ(x, u; ·) = g'ₓ(x, u; ·)` (the one-sided derivative in `x` exists and equals the
    generalized directional derivative in `x`), for all `x, u`;
(d) `(x, u) ↦ ∂ₓg(x, u)` is upper semicontinuous (sequential closed graph).
Then, with `f(x) = max_u g(x, u)` and `M(x) = {u : g(x, u) = f(x)}`:
(1) `f` is locally Lipschitz; (2) `f'(x; v)` exists; (3)
`f'(x; v) = f°(x; v) = max {ζ · v : ζ ∈ ∂ₓg(x, u), u ∈ M(x)}`; (4) `∂f(x)` is the convex
hull of `{∂ₓg(x, u) : u ∈ M(x)}`. -/
theorem max_function_generalized_gradient
    {n : ℕ} {U : Type*} [TopologicalSpace U] [SeqCompactSpace U] [Nonempty U]
    (g : EuclideanSpace ℝ (Fin n) → U → ℝ)
    (ha : UpperSemicontinuous (fun p : EuclideanSpace ℝ (Fin n) × U => g p.1 p.2))
    (hb : ∀ B : Set (EuclideanSpace ℝ (Fin n)), Bornology.IsBounded B →
      ∃ K : NNReal, ∀ u : U, LipschitzOnWith K (fun y => g y u) B)
    (hc : ∀ (x : EuclideanSpace ℝ (Fin n)) (u : U) (v : EuclideanSpace ℝ (Fin n)),
      HasOneSidedDirDeriv (fun y => g y u) x v (Shared.genDirDeriv (fun y => g y u) x v))
    (hd : SeqUpperSemicontinuous
      (fun p : EuclideanSpace ℝ (Fin n) × U => Shared.generalizedGradient (fun y => g y p.2) p.1)) :
    Shared.LipschitzOnBounded (maxFunction g) ∧
    (∀ x v : EuclideanSpace ℝ (Fin n),
      HasOneSidedDirDeriv (maxFunction g) x v (Shared.genDirDeriv (maxFunction g) x v) ∧
      IsGreatest {r : ℝ | ∃ u ∈ maximizers g x, ∃ ζ ∈ Shared.generalizedGradient (fun y => g y u) x,
          r = inner ℝ ζ v}
        (Shared.genDirDeriv (maxFunction g) x v)) ∧
    (∀ x : EuclideanSpace ℝ (Fin n),
      Shared.generalizedGradient (maxFunction g) x =
        convexHull ℝ (⋃ u ∈ maximizers g x, Shared.generalizedGradient (fun y => g y u) x)) := by
  exact ClarkeProof.native_max_recovery g ha hb hc hd

end ClarkeGradients.MaxFunctions

open ClarkeGradients ClarkeGradients.MaxFunctions

theorem solution
    {n : ℕ} {U : Type*} [TopologicalSpace U] [SeqCompactSpace U] [Nonempty U]
    (g : EuclideanSpace ℝ (Fin n) → U → ℝ)
    (ha : UpperSemicontinuous (fun p : EuclideanSpace ℝ (Fin n) × U => g p.1 p.2))
    (hb : ∀ B : Set (EuclideanSpace ℝ (Fin n)), Bornology.IsBounded B →
      ∃ K : NNReal, ∀ u : U, LipschitzOnWith K (fun y => g y u) B)
    (hc : ∀ (x : EuclideanSpace ℝ (Fin n)) (u : U) (v : EuclideanSpace ℝ (Fin n)),
      HasOneSidedDirDeriv (fun y => g y u) x v (Shared.genDirDeriv (fun y => g y u) x v))
    (hd : SeqUpperSemicontinuous
      (fun p : EuclideanSpace ℝ (Fin n) × U => Shared.generalizedGradient (fun y => g y p.2) p.1)) :
    Shared.LipschitzOnBounded (maxFunction g) ∧
    (∀ x v : EuclideanSpace ℝ (Fin n),
      HasOneSidedDirDeriv (maxFunction g) x v (Shared.genDirDeriv (maxFunction g) x v) ∧
      IsGreatest {r : ℝ | ∃ u ∈ maximizers g x, ∃ ζ ∈ Shared.generalizedGradient (fun y => g y u) x,
          r = inner ℝ ζ v}
        (Shared.genDirDeriv (maxFunction g) x v)) ∧
    (∀ x : EuclideanSpace ℝ (Fin n),
      Shared.generalizedGradient (maxFunction g) x =
        convexHull ℝ (⋃ u ∈ maximizers g x, Shared.generalizedGradient (fun y => g y u) x)) := ClarkeGradients.MaxFunctions.max_function_generalized_gradient g ha hb hc hd
