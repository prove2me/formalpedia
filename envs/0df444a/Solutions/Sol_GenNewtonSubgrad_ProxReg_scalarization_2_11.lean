-- Prove2me | solution 1 for GenNewtonSubgrad.ProxReg.scalarization_2_11
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T16:49:14.631339+00:00
-- url     : https://prove2.me/submissions/bba154f8-42bd-4864-a987-e9aa27ec88bc

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis

open Filter Topology
open scoped InnerProductSpace

namespace GNCScal
open GenNewtonSubgrad.ProxReg NonconvexSplitting.Shared

variable {E G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

lemma regSub_real_iff (h : E → ℝ) (y a : E) :
    IsRegularSubgrad (fun z => ((h z : ℝ) : EReal)) y a ↔
      ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝 y, h y + (⟪a, z - y⟫_ℝ - ε * ‖z - y‖) ≤ h z := by
  unfold IsRegularSubgrad
  simp only [← EReal.coe_add, EReal.coe_le_coe_iff, ne_eq, EReal.coe_ne_top, not_false_eq_true,
    true_and]

lemma exactify [ProperSpace E] {h : E → ℝ} {y a : E} {ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 ≤ δ)
    (hc : ContinuousOn h (Metric.closedBall y ρ))
    (hineq : ∀ z ∈ Metric.closedBall y ρ, h y + ⟪a, z - y⟫_ℝ - δ * ‖z - y‖ ≤ h z) :
    ∃ y' b : E, ‖y' - y‖ ≤ ρ ∧ ‖b - a‖ ≤ 2 * δ ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝 y', h y' + (⟪b, z - y'⟫_ℝ - ε * ‖z - y'‖) ≤ h z := by
  set μ := ρ / (δ + 1) with hμ
  have hμpos : 0 < μ := div_pos hρ (by linarith)
  set ψ : E → ℝ := fun z => h z - ⟪a, z - y⟫_ℝ + ‖z - y‖ ^ 2 / μ with hψ
  have hψc : ContinuousOn ψ (Metric.closedBall y ρ) := by
    refine (hc.sub ?_).add ?_
    · exact (continuous_const.inner (continuous_id.sub continuous_const)).continuousOn
    · exact (((continuous_id.sub continuous_const).norm.pow 2).div_const _).continuousOn
  obtain ⟨y', hy'mem, hmin⟩ := (isCompact_closedBall y ρ).exists_isMinOn
    ⟨y, Metric.mem_closedBall_self hρ.le⟩ hψc
  have hdist : ‖y' - y‖ ≤ δ * μ := by
    have h1 : ψ y' ≤ ψ y := hmin (Metric.mem_closedBall_self hρ.le)
    have h2 := hineq y' hy'mem
    have h1' : h y' - ⟪a, y' - y⟫_ℝ + ‖y' - y‖ ^ 2 / μ ≤ h y := by
      have e : ψ y = h y := by simp [hψ]
      rw [e] at h1; exact h1
    have ht := norm_nonneg (y' - y)
    have h3 : ‖y' - y‖ ^ 2 / μ ≤ δ * ‖y' - y‖ := by linarith
    rw [div_le_iff₀ hμpos] at h3
    by_contra hcon
    push_neg at hcon
    have : δ * μ * ‖y' - y‖ < ‖y' - y‖ * ‖y' - y‖ := by
      apply mul_lt_mul_of_pos_right hcon
      nlinarith [mul_nonneg hδ hμpos.le]
    nlinarith
  have hlt : ‖y' - y‖ < ρ := by
    have : δ * μ < ρ := by
      rw [hμ, mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  refine ⟨y', a - (2 / μ) • (y' - y), hlt.le, ?_, fun ε hε => ?_⟩
  · rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < 2 / μ)]
    calc 2 / μ * ‖y' - y‖ ≤ 2 / μ * (δ * μ) := by gcongr
      _ = 2 * δ := by field_simp
  · have hball : Metric.ball y ρ ∈ 𝓝 y' := Metric.isOpen_ball.mem_nhds (by
      rw [Metric.mem_ball, dist_eq_norm]; exact hlt)
    filter_upwards [hball, Metric.ball_mem_nhds y' (by positivity : (0:ℝ) < ε * μ)] with z hz hz'
    have hmz : ψ y' ≤ ψ z := hmin (Metric.ball_subset_closedBall hz)
    rw [Metric.mem_ball, dist_eq_norm] at hz'
    simp only [hψ] at hmz
    have hexp : ‖z - y‖ ^ 2 = ‖z - y'‖ ^ 2 + 2 * ⟪z - y', y' - y⟫_ℝ + ‖y' - y‖ ^ 2 := by
      have : z - y = (z - y') + (y' - y) := by abel
      rw [this, norm_add_sq_real]
    rw [hexp] at hmz
    have hin1 : ⟪a, z - y⟫_ℝ = ⟪a, z - y'⟫_ℝ + ⟪a, y' - y⟫_ℝ := by
      rw [← inner_add_right]; congr 1; abel
    have hin2 : ⟪a - (2 / μ) • (y' - y), z - y'⟫_ℝ = ⟪a, z - y'⟫_ℝ - 2 / μ * ⟪z - y', y' - y⟫_ℝ := by
      rw [inner_sub_left, real_inner_smul_left, real_inner_comm (y' - y)]
    rw [hin1] at hmz
    rw [hin2]
    have hq : ‖z - y'‖ ^ 2 / μ ≤ ε * ‖z - y'‖ := by
      rw [div_le_iff₀ hμpos]
      have := norm_nonneg (z - y')
      nlinarith
    have e1 : (‖z - y'‖ ^ 2 + 2 * ⟪z - y', y' - y⟫_ℝ + ‖y' - y‖ ^ 2) / μ
        = ‖z - y'‖ ^ 2 / μ + 2 / μ * ⟪z - y', y' - y⟫_ℝ + ‖y' - y‖ ^ 2 / μ := by ring
    rw [e1] at hmz
    linarith


lemma regSub_to_regNormal (F : E → G) (y a : E) (v : G)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝 y, ⟪v, F y⟫_ℝ + (⟪a, z - y⟫_ℝ - ε * ‖z - y‖) ≤ ⟪v, F z⟫_ℝ) :
    ((a, -v) : E × G) ∈ regNormal (gph (sv F)) (y, F y) := by
  refine ⟨Set.mem_singleton _, fun ε hε => ?_⟩
  have h1 := (continuous_fst.tendsto ((y, F y) : E × G)).eventually (h ε hε)
  filter_upwards [h1] with w hw hwS
  have hw2 : w.2 = F w.1 := hwS
  simp only [pairInner, Prod.fst_sub, Prod.snd_sub, hw2, inner_neg_left]
  have hn : ‖w.1 - y‖ ≤ ‖w - (y, F y)‖ := by
    have := norm_fst_le (w - ((y, F y) : E × G)); simpa using this
  simp only [inner_sub_right] at hw ⊢
  nlinarith [mul_le_mul_of_nonneg_left hn hε.le]

lemma regNormal_to_eps (F : E → G) (y : E) {U : Set E} (hU : U ∈ 𝓝 y) {L : NNReal}
    (hL : LipschitzOnWith L F U) (a : E) (w : G)
    (h : ((a, w) : E × G) ∈ regNormal (gph (sv F)) (y, F y)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝 y, ⟪a, z - y⟫_ℝ + ⟪w, F z - F y⟫_ℝ ≤ ε * ‖z - y‖ := by
  intro ε hε
  have hK : (0:ℝ) < L + 1 := by positivity
  have h1 := h.2 (ε / (L + 1)) (div_pos hε hK)
  have hFc : ContinuousAt F y := (hL.continuousOn).continuousAt hU
  have hmap : Tendsto (fun z => ((z, F z) : E × G)) (𝓝 y) (𝓝 (y, F y)) :=
    (continuousAt_id.prodMk hFc).tendsto
  filter_upwards [hmap.eventually h1, hU] with z hz hzU
  have hz' := hz (show F z ∈ ({F z} : Set G) from Set.mem_singleton _)
  simp only [pairInner, Prod.mk_sub_mk] at hz'
  have hyU : y ∈ U := mem_of_mem_nhds hU
  have hlip : ‖F z - F y‖ ≤ L * ‖z - y‖ := by
    have := hL.dist_le_mul z hzU y hyU
    rwa [dist_eq_norm, dist_eq_norm] at this
  have hnorm : ‖((z - y, F z - F y) : E × G)‖ ≤ (L + 1) * ‖z - y‖ := by
    rw [Prod.norm_mk]
    apply max_le
    · nlinarith [norm_nonneg (z - y)]
    · nlinarith [norm_nonneg (z - y)]
  calc ⟪a, z - y⟫_ℝ + ⟪w, F z - F y⟫_ℝ ≤ ε / (L + 1) * ‖((z - y, F z - F y) : E × G)‖ := hz'
    _ ≤ ε / (L + 1) * ((L + 1) * ‖z - y‖) := by gcongr
    _ = ε * ‖z - y‖ := by field_simp


theorem scal_main [ProperSpace E] (F : E → G) (xbar : E)
    (hF : ∃ U ∈ 𝓝 xbar, ∃ L, LipschitzOnWith L F U) (v : G) :
    coderiv (sv F) xbar (F xbar) v =
      LimitingSubdiff (fun z => ((⟪v, F z⟫_ℝ : ℝ) : EReal)) xbar := by
  obtain ⟨U, hU, L, hL⟩ := hF
  have hFc : ContinuousAt F xbar := (hL.continuousOn).continuousAt hU
  have hhc : ContinuousAt (fun z => ⟪v, F z⟫_ℝ) xbar := continuousAt_const.inner hFc
  ext u
  constructor
  · rintro ⟨-, zs, as, hzs, hzl, hal, hreg⟩
    obtain ⟨r1, hr1, hball⟩ := Metric.mem_nhds_iff.1 hU
    set xk : ℕ → E := fun k => (zs k).1 with hxkdef
    set ak : ℕ → E := fun k => (as k).1 with hakdef
    set wk : ℕ → G := fun k => (as k).2 with hwkdef
    have hzk : ∀ k, zs k = (xk k, F (xk k)) := fun k => Prod.ext rfl (hzs k)
    have hxk : Tendsto xk atTop (𝓝 xbar) := by
      exact (continuous_fst.tendsto _).comp hzl
    have hak : Tendsto ak atTop (𝓝 u) := by
      exact (continuous_fst.tendsto _).comp hal
    have hwk : Tendsto wk atTop (𝓝 (-v)) := by
      exact (continuous_snd.tendsto _).comp hal
    obtain ⟨K, hK⟩ := eventually_atTop.1 (hxk.eventually (Metric.ball_mem_nhds xbar (half_pos hr1)))
    have hLip1 : LipschitzOnWith L F (Metric.ball xbar r1) := hL.mono hball
    have hex : ∀ k : ℕ, ∃ y b : E, ‖y - xk (k + K)‖ ≤ 1 / ((k:ℝ) + 1) ∧
        ‖b - ak (k + K)‖ ≤ 2 * (1 / ((k:ℝ) + 1) + L * ‖v + wk (k + K)‖) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ z in 𝓝 y, ⟪v, F y⟫_ℝ + (⟪b, z - y⟫_ℝ - ε * ‖z - y‖) ≤ ⟪v, F z⟫_ℝ := by
      intro k
      set j := k + K
      have hxj : xk j ∈ Metric.ball xbar (r1 / 2) := hK j (Nat.le_add_left K k)
      have hxj' : xk j ∈ Metric.ball xbar r1 :=
        Metric.ball_subset_ball (half_le_self hr1.le) hxj
      have hUj : Metric.ball xbar r1 ∈ 𝓝 (xk j) := Metric.isOpen_ball.mem_nhds hxj'
      have hrn : ((ak j, wk j) : E × G) ∈ regNormal (gph (sv F)) (xk j, F (xk j)) := by
        rw [← hzk j]; exact hreg j
      have hk1 : (0:ℝ) < 1 / ((k:ℝ) + 1) := by positivity
      have heps := regNormal_to_eps F (xk j) hUj hLip1 (ak j) (wk j) hrn _ hk1
      obtain ⟨ρ0, hρ0, hρ0P⟩ := Metric.eventually_nhds_iff.1 heps
      set ρ := min (ρ0 / 2) (min (r1 / 2) (1 / ((k:ℝ) + 1))) with hρdef
      have hρ : 0 < ρ := lt_min (half_pos hρ0) (lt_min (half_pos hr1) hk1)
      have hcb : ∀ z ∈ Metric.closedBall (xk j) ρ, dist z (xk j) < ρ0 ∧ z ∈ Metric.ball xbar r1 := by
        intro z hz
        rw [Metric.mem_closedBall] at hz
        refine ⟨lt_of_le_of_lt hz (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hρ0)), ?_⟩
        rw [Metric.mem_ball] at hxj ⊢
        have : ρ ≤ r1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
        calc dist z xbar ≤ dist z (xk j) + dist (xk j) xbar := dist_triangle _ _ _
          _ < r1 / 2 + r1 / 2 := by linarith
          _ = r1 := by ring
      have hδ : 0 ≤ 1 / ((k:ℝ) + 1) + L * ‖v + wk j‖ := by positivity
      have hcont : ContinuousOn (fun z => ⟪v, F z⟫_ℝ) (Metric.closedBall (xk j) ρ) := by
        apply ContinuousOn.inner continuousOn_const
        exact (hLip1.continuousOn).mono (fun z hz => (hcb z hz).2)
      obtain ⟨y, b, hy, hb, hyreg⟩ := exactify (h := fun z => ⟪v, F z⟫_ℝ) (a := ak j) hρ hδ hcont
        (by
          intro z hz
          obtain ⟨hz1, hz2⟩ := hcb z hz
          have hP := hρ0P hz1
          have hlip : ‖F z - F (xk j)‖ ≤ L * ‖z - xk j‖ := by
            have := hLip1.dist_le_mul z hz2 (xk j) hxj'
            rwa [dist_eq_norm, dist_eq_norm] at this
          have hcs : |⟪v + wk j, F z - F (xk j)⟫_ℝ| ≤ ‖v + wk j‖ * ‖F z - F (xk j)‖ :=
            abs_real_inner_le_norm _ _
          have hsplit : ⟪v, F z⟫_ℝ - ⟪v, F (xk j)⟫_ℝ =
              ⟪v + wk j, F z - F (xk j)⟫_ℝ - ⟪wk j, F z - F (xk j)⟫_ℝ := by
            rw [inner_add_left, inner_sub_right]; ring
          have h3 : ‖v + wk j‖ * ‖F z - F (xk j)‖ ≤ L * ‖v + wk j‖ * ‖z - xk j‖ := by
            have := mul_le_mul_of_nonneg_left hlip (norm_nonneg (v + wk j))
            linarith
          have := (abs_le.1 hcs).1
          nlinarith)
      refine ⟨y, b, hy.trans ((min_le_right _ _).trans (min_le_right _ _)), hb, ?_⟩
      simpa using hyreg
    choose ys bs hys using hex
    have hshift : Tendsto (fun t : ℕ => t + K) atTop atTop := tendsto_add_atTop_nat K
    have hinv : Tendsto (fun t : ℕ => 1 / ((t:ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hys_t : Tendsto ys atTop (𝓝 xbar) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h2 : Tendsto (fun t => ‖xk (t + K) - xbar‖) atTop (𝓝 0) :=
        (tendsto_iff_norm_sub_tendsto_zero.1 (hxk.comp hshift))
      refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) (by have := hinv.add h2; rwa [zero_add] at this)
      calc ‖ys t - xbar‖ ≤ ‖ys t - xk (t + K)‖ + ‖xk (t + K) - xbar‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 1 / ((t:ℝ) + 1) + ‖xk (t + K) - xbar‖ := by gcongr; exact (hys t).1
    refine ⟨EReal.coe_ne_top _, ys, bs, hys_t, ?_, ?_, fun t => (regSub_real_iff _ _ _).2 ?_⟩
    · exact (continuous_coe_real_ereal.tendsto _).comp (hhc.tendsto.comp hys_t)
    · rw [tendsto_iff_norm_sub_tendsto_zero]
      have h2 : Tendsto (fun t => ‖ak (t + K) - u‖) atTop (𝓝 0) :=
        tendsto_iff_norm_sub_tendsto_zero.1 (hak.comp hshift)
      have h3 : Tendsto (fun t => ‖v + wk (t + K)‖) atTop (𝓝 0) := by
        have := ((hwk.comp hshift).const_add v).norm
        simpa using this
      have h4 : Tendsto (fun t : ℕ => 2 * (1 / ((t:ℝ) + 1) + L * ‖v + wk (t + K)‖) + ‖ak (t + K) - u‖)
          atTop (𝓝 0) := by
        have := ((hinv.add (h3.const_mul (L:ℝ))).const_mul 2).add h2
        simpa using this
      refine squeeze_zero (fun t => norm_nonneg _) (fun t => ?_) h4
      calc ‖bs t - u‖ ≤ ‖bs t - ak (t + K)‖ + ‖ak (t + K) - u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ _ := by gcongr; exact (hys t).2.1
    · exact (hys t).2.2
  · rintro ⟨-, xs, vs, hx, -, hv, hreg⟩
    refine ⟨Set.mem_singleton _, fun t => (xs t, F (xs t)), fun t => (vs t, -v),
      fun t => Set.mem_singleton _, ?_, ?_, fun t => ?_⟩
    · exact hx.prodMk_nhds (hFc.tendsto.comp hx)
    · exact hv.prodMk_nhds tendsto_const_nhds
    · exact regSub_to_regNormal F (xs t) (vs t) v ((regSub_real_iff _ _ _).1 (hreg t))

end GNCScal

open GenNewtonSubgrad.ProxReg in
theorem solution {n m : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (xbar : EuclideanSpace ℝ (Fin n))
    (hF : ∃ U ∈ 𝓝 xbar, ∃ L, LipschitzOnWith L F U) (v : EuclideanSpace ℝ (Fin m)) :
    coderiv (sv F) xbar (F xbar) v =
      NonconvexSplitting.Shared.LimitingSubdiff (fun z => ((⟪v, F z⟫_ℝ : ℝ) : EReal)) xbar :=
  GNCScal.scal_main F xbar hF v
