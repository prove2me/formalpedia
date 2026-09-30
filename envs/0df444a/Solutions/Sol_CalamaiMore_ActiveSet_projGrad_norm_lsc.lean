-- Prove2me | solution 1 for CalamaiMore.ActiveSet.projGrad_norm_lsc
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:49:45.69459+00:00
-- url     : https://prove2.me/submissions/4fe50d79-2d53-402f-9159-1ecbf9ab2766

import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Topology.Semicontinuity.Defs
import Definitions.Def_CalamaiMore_Convergence_projGrad
import Definitions.Def_CalamaiMore_ActiveSet_projGrad
import Definitions.Def_CalamaiMore_Shared_IsStationaryPoint
open scoped InnerProductSpace Topology
open Filter CalamaiMore.Shared
noncomputable section

open CalamaiMore.Convergence

private lemma feasible_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Ω : Set E) (x : E) (hx : x ∈ Ω) : (0 : E) ∈ feasibleDirections Ω x := by
  change ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • (0 : E) ∈ Ω
  filter_upwards [] with t
  simpa using hx

private lemma feasible_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Ω : Set E) (x : E) (hx : x ∈ Ω) (v : E) (hv : v ∈ feasibleDirections Ω x)
    (a : ℝ) (ha : 0 ≤ a) : a • v ∈ feasibleDirections Ω x := by
  rcases ha.eq_or_lt with rfl | ha
  · simpa using feasible_zero Ω x hx
  change ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • v ∈ Ω at hv
  change ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • (a • v) ∈ Ω
  have hn : Tendsto (fun t : ℝ => t * a) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => t * a) := by fun_prop
    have hh := hc.tendsto 0
    rw [zero_mul] at hh
    exact hh.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun t : ℝ => t * a) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hn, ?_⟩
    filter_upwards [eventually_mem_nhdsWithin] with t ht
    exact mul_pos ht ha
  have hh := ht.eventually hv
  simpa only [mul_smul] using hh

private lemma feasible_convex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Ω : Set E) (hcv : Convex ℝ Ω) (x : E) : Convex ℝ (feasibleDirections Ω x) := by
  intro u hu v hv a b ha hb hab
  change ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • u ∈ Ω at hu
  change ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • v ∈ Ω at hv
  change ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • (a • u + b • v) ∈ Ω
  filter_upwards [hu, hv] with t htu htv
  have hh := hcv htu htv ha hb hab
  convert hh using 1
  calc
    x + t • (a • u + b • v) = (a + b) • x + t • (a • u + b • v) := by rw [hab, one_smul]
    _ = a • (x + t • u) + b • (x + t • v) := by module

private lemma tangent_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Ω : Set E) (x : E) (hx : x ∈ Ω) (v : E) (hv : v ∈ tangentCone Ω x)
    (a : ℝ) (ha : 0 ≤ a) : a • v ∈ tangentCone Ω x := by
  have hh : Set.MapsTo (fun w : E => a • w) (feasibleDirections Ω x) (feasibleDirections Ω x) :=
    fun w hw => feasible_smul Ω x hx w hw a ha
  exact hh.closure (continuous_const_smul a) hv

private lemma feasible_diff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Ω : Set E) (hcv : Convex ℝ Ω) (x z : E) (hx : x ∈ Ω) (hz : z ∈ Ω) :
    z - x ∈ feasibleDirections Ω x := by
  change ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • (z - x) ∈ Ω
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [eventually_mem_nhdsWithin, hsmall] with t ht ht1
  have hh := hcv hx hz (show 0 ≤ 1 - t by linarith) (le_of_lt ht) (by ring : 1 - t + t = 1)
  convert hh using 1 <;> module

private lemma normal_tangent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (Ω : Set E) (hcv : Convex ℝ Ω) (x g : E) (hx : x ∈ Ω) :
    (∀ z ∈ Ω, 0 ≤ ⟪g, z - x⟫_ℝ) ↔ (∀ v ∈ tangentCone Ω x, 0 ≤ ⟪g, v⟫_ℝ) := by
  constructor
  · intro h
    have hclosed : IsClosed {v : E | 0 ≤ ⟪g, v⟫_ℝ} := isClosed_le continuous_const (by fun_prop)
    have hsub : feasibleDirections Ω x ⊆ {v : E | 0 ≤ ⟪g, v⟫_ℝ} := by
      intro v hv
      change ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • v ∈ Ω at hv
      have hboth := hv.and (eventually_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Set.Ioi 0)
      obtain ⟨t, htΩ, ht⟩ := hboth.exists
      have hh := h (x + t • v) htΩ
      change 0 < t at ht
      simp only [add_sub_cancel_left, inner_smul_right] at hh
      exact (mul_nonneg_iff_of_pos_left ht).mp hh
    exact fun v hv => closure_minimal hsub hclosed hv
  · intro h z hz
    exact h _ (subset_closure (feasible_diff Ω hcv x z hx hz))

private theorem projection_spec {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (C : Set E)
    (hne : C.Nonempty) (hc : IsClosed C) (hcv : Convex ℝ C) (x : E) :
    proj C x ∈ C ∧ ∀ y ∈ C, ⟪x - proj C x, y - proj C x⟫_ℝ ≤ 0 := by
  letI : Nonempty C := hne.to_subtype
  have hb : BddBelow (Set.range (fun y : C => ‖x - y‖)) := ⟨0, by
    rintro _ ⟨y, rfl⟩
    exact norm_nonneg _⟩
  have he : ∃ p ∈ C, ∀ y ∈ C, ‖p - x‖ ≤ ‖y - x‖ := by
    obtain ⟨p, hp, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hc.isComplete hcv x
    refine ⟨p, hp, ?_⟩
    intro y hy
    rw [norm_sub_rev p x, norm_sub_rev y x, hmin]
    exact ciInf_le hb ⟨y, hy⟩
  have hraw : proj C x ∈ C ∧ ∀ y ∈ C, ‖proj C x - x‖ ≤ ‖y - x‖ := by
    simpa only [proj, nearestPoint, dif_pos he] using Classical.choose_spec he
  have hp : ∀ y ∈ C, ‖x - proj C x‖ ≤ ‖x - y‖ := by
    intro y hy
    rw [norm_sub_rev x _, norm_sub_rev x y]
    exact hraw.2 y hy
  refine ⟨hraw.1, (norm_eq_iInf_iff_real_inner_le_zero hcv hraw.1).mp ?_⟩
  exact le_antisymm (le_ciInf (fun y => hp y y.2))
    (ciInf_le hb ⟨_, hraw.1⟩)

private theorem projection_descent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (C : Set E) (hne : C.Nonempty) (hc : IsClosed C) (hcv : Convex ℝ C)
    (x g : E) (hx : x ∈ C) (a : ℝ) (ha : 0 < a) :
    ‖proj C (x - a • g) - x‖ ^ 2 / a ≤ ⟪g, x - proj C (x - a • g)⟫_ℝ := by
  have hp := (projection_spec C hne hc hcv (x - a • g)).2 x hx
  rw [div_le_iff₀ ha]
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_comm (proj C (x - a • g)) x] at *
  nlinarith

private theorem cone_projection_properties {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (C : Set E) (h0 : (0 : E) ∈ C)
    (hc : IsClosed C) (hcv : Convex ℝ C)
    (hsmul : ∀ v ∈ C, ∀ a : ℝ, 0 ≤ a → a • v ∈ C) (g : E) :
    -⟪g, proj C (-g)⟫_ℝ = ‖proj C (-g)‖ ^ 2 ∧
    IsLeast {r : ℝ | ∃ v ∈ C, ‖v‖ ≤ 1 ∧ r = ⟪g, v⟫_ℝ} (-‖proj C (-g)‖) ∧
    ((∀ v ∈ C, 0 ≤ ⟪g, v⟫_ℝ) ↔ proj C (-g) = 0) := by
  let p := proj C (-g)
  have hp := projection_spec C ⟨0, h0⟩ hc hcv (-g)
  change p ∈ C ∧ ∀ y ∈ C, ⟪-g - p, y - p⟫_ℝ ≤ 0 at hp
  have heq : -⟪g, p⟫_ℝ = ‖p‖ ^ 2 := by
    have h1 := hp.2 0 h0
    have h2 := hp.2 (2 • p) (hsmul p hp.1 2 (by norm_num))
    simp only [inner_sub_left, inner_sub_right, inner_neg_left, inner_zero_right,
      inner_smul_right, real_inner_self_eq_norm_sq] at h1 h2
    nlinarith
  have hbound (v : E) (hv : v ∈ C) (hn : ‖v‖ ≤ 1) : -‖p‖ ≤ ⟪g, v⟫_ℝ := by
    have hvar := hp.2 v hv
    simp only [inner_sub_left, inner_sub_right, inner_neg_left,
      real_inner_self_eq_norm_sq] at hvar
    have hcs := real_inner_le_norm p v
    have hmul := mul_le_mul_of_nonneg_left hn (norm_nonneg p)
    nlinarith
  refine ⟨heq, ⟨?_, ?_⟩, ?_⟩
  · by_cases hz : p = 0
    · refine ⟨0, h0, by simp, ?_⟩
      change -‖p‖ = ⟪g, (0 : E)⟫_ℝ
      simp [hz]
    · have hn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      refine ⟨‖p‖⁻¹ • p, hsmul p hp.1 _ (inv_nonneg.mpr (norm_nonneg p)), ?_, ?_⟩
      · simp [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg p), hn]
      · change -‖p‖ = ⟪g, ‖p‖⁻¹ • p⟫_ℝ
        rw [inner_smul_right]
        have hh : ⟪g, p⟫_ℝ = -‖p‖ ^ 2 := by linarith
        rw [hh]
        field_simp
        <;> ring
  · rintro r ⟨v, hv, hn, rfl⟩
    exact hbound v hv hn
  · constructor
    · intro h
      have hh := h p hp.1
      have hn : ‖p‖ = 0 := by nlinarith [norm_nonneg p]
      exact norm_eq_zero.mp hn
    · intro hz v hv
      have hh := hp.2 v hv
      change p = 0 at hz
      simpa [hz] using hh


namespace CalamaiMore.ActiveSet

/-- Calamai–Moré, Lemma 3.3 (p. 104): for `Ω` nonempty closed convex and `f` continuously
differentiable on `Ω`, the map `x ↦ ‖∇_Ω f(x)‖` is lower semicontinuous on `Ω`. -/
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (Ω : Set E) (hΩne : Ω.Nonempty) (hΩc : IsClosed Ω) (hΩcv : Convex ℝ Ω)
    (f : E → ℝ) (hfd : ∀ x ∈ Ω, DifferentiableAt ℝ f x) (hfc : ContinuousOn (gradient f) Ω) :
    LowerSemicontinuousOn (fun y => ‖projGrad f Ω y‖) Ω := by
  have h0 (y : E) (hy : y ∈ Ω) : (0 : E) ∈ CalamaiMore.Shared.tangentCone Ω y :=
    subset_closure (feasible_zero Ω y hy)
  have hcv (y : E) : Convex ℝ (CalamaiMore.Shared.tangentCone Ω y) :=
    (feasible_convex Ω hΩcv y).closure
  have hprops (y : E) (hy : y ∈ Ω) :
      -⟪gradient f y, CalamaiMore.Convergence.projGrad f Ω y⟫_ℝ =
        ‖CalamaiMore.Convergence.projGrad f Ω y‖ ^ 2 ∧
      IsLeast {r : ℝ | ∃ v ∈ CalamaiMore.Shared.tangentCone Ω y,
        ‖v‖ ≤ 1 ∧ r = ⟪gradient f y, v⟫_ℝ} (-‖CalamaiMore.Convergence.projGrad f Ω y‖) := by
    have hh := cone_projection_properties (CalamaiMore.Shared.tangentCone Ω y) (h0 y hy)
      isClosed_closure (hcv y) (fun v hv a ha => tangent_smul Ω y hy v hv a ha) (gradient f y)
    exact ⟨hh.1, hh.2.1⟩
  have hbound (y z : E) (hy : y ∈ Ω) (hz : z ∈ Ω) :
      -⟪gradient f y, z - y⟫_ℝ / ‖z - y‖ ≤ ‖CalamaiMore.Convergence.projGrad f Ω y‖ := by
    by_cases hn : ‖z - y‖ = 0
    · simp [hn]
    have hd : z - y ∈ CalamaiMore.Shared.tangentCone Ω y := subset_closure (feasible_diff Ω hΩcv y z hy hz)
    have hunit := tangent_smul Ω y hy (z - y) hd (‖z - y‖⁻¹)
      (inv_nonneg.mpr (norm_nonneg _))
    have hnorm : ‖‖z - y‖⁻¹ • (z - y)‖ ≤ 1 := by simp [norm_smul, hn]
    have hh := (hprops y hy).2.2 ⟨_, hunit, hnorm, rfl⟩
    simp only [inner_smul_right] at hh
    rw [div_eq_mul_inv]
    nlinarith
  intro x hx b hb
  change b < ‖CalamaiMore.Convergence.projGrad f Ω x‖ at hb
  change ∀ᶠ y in 𝓝[Ω] x, b < ‖CalamaiMore.Convergence.projGrad f Ω y‖
  by_cases hb0 : b < 0
  · exact .of_forall fun y => hb0.trans_le (norm_nonneg _)
  have hb0' : 0 ≤ b := le_of_not_gt hb0
  let p := CalamaiMore.Convergence.projGrad f Ω x
  have hpNorm : 0 < ‖p‖ := lt_of_le_of_lt hb0' hb
  have hpne : ‖p‖ ≠ 0 := ne_of_gt hpNorm
  let R : E → ℝ := fun v => -⟪gradient f x, v⟫_ℝ / ‖v‖
  have hRp : R p = ‖p‖ := by
    have heq := (hprops x hx).1
    change -⟪gradient f x, p⟫_ℝ = ‖p‖ ^ 2 at heq
    dsimp [R]
    rw [heq]
    field_simp
  have hRc : ContinuousAt R p := by
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · exact hpne
  have hRe : ∀ᶠ v in 𝓝 p, b < R v := hRc.eventually (eventually_gt_nhds (by simpa [hRp] using hb))
  have hpT : p ∈ CalamaiMore.Shared.tangentCone Ω x :=
    (projection_spec _ ⟨0, h0 x hx⟩ isClosed_closure (hcv x) (-gradient f x)).1
  have hfreq := mem_closure_iff_frequently.mp hpT
  obtain ⟨w, hw, hwR⟩ := (hfreq.and_eventually hRe).exists
  have hwne : w ≠ 0 := by
    intro hw0
    simp [R, hw0] at hwR
    linarith
  have hwnorm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hwne
  change ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • w ∈ Ω at hw
  obtain ⟨t, htΩ, ht⟩ := (hw.and (eventually_mem_nhdsWithin : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Set.Ioi 0)).exists
  change 0 < t at ht
  let z := x + t • w
  have hz : z ∈ Ω := htΩ
  have hzNorm : ‖z - x‖ ≠ 0 := by
    dsimp [z]
    rw [add_sub_cancel_left]
    exact norm_ne_zero_iff.mpr (smul_ne_zero (ne_of_gt ht) hwne)
  let q : E → ℝ := fun y => -⟪gradient f y, z - y⟫_ℝ / ‖z - y‖
  have hqx : q x = R w := by
    dsimp [q, R, z]
    simp only [add_sub_cancel_left, inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht]
    field_simp
  have hqc : ContinuousWithinAt q Ω x := by
    apply ContinuousWithinAt.div
    · exact ((hfc x hx).inner (continuous_const.sub continuous_id).continuousWithinAt).neg
    · fun_prop
    · exact hzNorm
  have hqe : ∀ᶠ y in 𝓝[Ω] x, b < q y := hqc.eventually (eventually_gt_nhds (by simpa [hqx] using hwR))
  filter_upwards [hqe, eventually_mem_nhdsWithin] with y hyq hy
  exact hyq.trans_le (hbound y z hy hz)


end CalamaiMore.ActiveSet
