-- Prove2me | solution 1 for FiniteEnergyPlane.exists_reebOrbit_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T16:17:16.599221+00:00
-- url     : https://prove2.me/submissions/bc541996-a717-4a7e-b13a-7ac01584a3db

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_isCompact_energySurface
import Theorems.Thm_FiniteEnergyPlane_exists_lipschitzOnWith_reeb

open FiniteEnergyPlane
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal Real

/-! Limits of periodic Reeb orbits. -/


namespace ROFLimit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two-sided Gronwall on an invariant set for a Lipschitz field. -/
lemma dist_le_two_sided {R : E → E} {S : Set E} {K : NNReal} (hL : LipschitzOnWith K R S)
    {a b : ℝ → E} (ha : ∀ t, HasDerivAt a (R (a t)) t) (hb : ∀ t, HasDerivAt b (R (b t)) t)
    (haS : ∀ t, a t ∈ S) (hbS : ∀ t, b t ∈ S) (t : ℝ) :
    dist (a t) (b t) ≤ dist (a 0) (b 0) * Real.exp (K * |t|) := by
  have hac : Continuous a := continuous_iff_continuousAt.2 fun t => (ha t).continuousAt
  have hbc : Continuous b := continuous_iff_continuousAt.2 fun t => (hb t).continuousAt
  rcases le_total 0 t with h | h
  · have := dist_le_of_trajectories_ODE_of_mem (v := fun _ => R) (s := fun _ => S) (K := K)
      (f := a) (g := b) (a := 0) (b := t) (δ := dist (a 0) (b 0))
      (fun _ _ => hL) hac.continuousOn (fun s _ => (ha s).hasDerivWithinAt)
      (fun s _ => haS s) hbc.continuousOn (fun s _ => (hb s).hasDerivWithinAt)
      (fun s _ => hbS s) le_rfl t ⟨h, le_rfl⟩
    rw [sub_zero] at this; rw [abs_of_nonneg h]; exact this
  · -- reverse time
    have hneg : LipschitzOnWith K (fun y => - R y) S := by
      intro x hx y hy
      simpa [edist_neg_neg] using hL hx hy
    have hrev : ∀ c : ℝ → E, (∀ t, HasDerivAt c (R (c t)) t) →
        ∀ s, HasDerivAt (fun s => c (-s)) (- R (c (-s))) s := by
      intro c hc s
      have h1 : HasDerivAt (fun s : ℝ => -s) (-1) s := (hasDerivAt_id s).neg
      have := (hc (-s)).scomp s h1
      simp only [neg_smul, one_smul] at this
      exact this
    have := dist_le_of_trajectories_ODE_of_mem (v := fun _ y => - R y) (s := fun _ => S) (K := K)
      (f := fun s => a (-s)) (g := fun s => b (-s)) (a := 0) (b := -t) (δ := dist (a 0) (b 0))
      (fun _ _ => hneg) (hac.comp continuous_neg).continuousOn
      (fun s _ => (hrev a ha s).hasDerivWithinAt)
      (fun s _ => haS _) (hbc.comp continuous_neg).continuousOn
      (fun s _ => (hrev b hb s).hasDerivWithinAt)
      (fun s _ => hbS _) (by simp) (-t) ⟨by linarith, le_rfl⟩
    simp only [neg_neg, sub_zero] at this
    rw [abs_of_nonpos h]; exact this

/-- The limit curve of integral curves whose initial values converge. -/
lemma exists_limit_curve [CompleteSpace E] {R : E → E} {S : Set E} {K : NNReal}
    (hL : LipschitzOnWith K R S) (hS : IsClosed S)
    (Q : ℕ → ℝ → E) (hQ : ∀ k t, HasDerivAt (Q k) (R (Q k t)) t) (hQS : ∀ k t, Q k t ∈ S)
    (p : E) (h0 : Tendsto (fun k => Q k 0) atTop (𝓝 p)) :
    ∃ x : ℝ → E, (∀ t, HasDerivAt x (R (x t)) t) ∧ (∀ t, x t ∈ S) ∧ x 0 = p ∧
      ∀ t, Tendsto (fun k => Q k t) atTop (𝓝 (x t)) := by
  have hcau : ∀ t, CauchySeq (fun k => Q k t) := by
    intro t
    have hc0 : CauchySeq (fun k => Q k 0) := h0.cauchySeq
    rw [Metric.cauchySeq_iff] at hc0 ⊢
    intro ε hε
    set C := Real.exp (K * |t|) with hC
    have hCpos : 0 < C := Real.exp_pos _
    obtain ⟨N, hN⟩ := hc0 (ε / C) (div_pos hε hCpos)
    refine ⟨N, fun k hk l hl => ?_⟩
    have h1 := dist_le_two_sided hL (hQ k) (hQ l) (hQS k) (hQS l) t
    have h2 := hN k hk l hl
    calc dist (Q k t) (Q l t) ≤ dist (Q k 0) (Q l 0) * C := h1
      _ < ε / C * C := mul_lt_mul_of_pos_right h2 hCpos
      _ = ε := div_mul_cancel₀ _ hCpos.ne'
  choose x hx using fun t => cauchySeq_tendsto_of_complete (hcau t)
  have hxS : ∀ t, x t ∈ S := fun t => hS.mem_of_tendsto (hx t) (Eventually.of_forall fun k => hQS k t)
  have hx0 : x 0 = p := tendsto_nhds_unique (hx 0) h0
  have hbd : ∀ k t, dist (Q k t) (x t) ≤ dist (Q k 0) p * Real.exp (K * |t|) := by
    intro k t
    exact le_of_tendsto_of_tendsto' (tendsto_const_nhds.dist (hx t))
      ((tendsto_const_nhds.dist h0).mul_const _)
      (fun l => dist_le_two_sided hL (hQ k) (hQ l) (hQS k) (hQS l) t)
  refine ⟨x, ?_, hxS, hx0, hx⟩
  intro t
  have hd0 : Tendsto (fun k => dist (Q k 0) p) atTop (𝓝 0) := by
    simpa using h0.dist (tendsto_const_nhds (x := p))
  have hunif : TendstoLocallyUniformlyOn (fun k s => R (Q k s)) (fun s => R (x s)) atTop univ := by
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε t0 _
    refine ⟨ball t0 1, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ one_pos), ?_⟩
    set C := Real.exp (K * (|t0| + 1)) with hC
    have hCpos : 0 < C := Real.exp_pos _
    have hA : 0 < ((K : ℝ) + 1) * C := by positivity
    have hev := hd0.eventually (gt_mem_nhds (div_pos hε hA))
    filter_upwards [hev] with k hk s hs
    have hs' : |s| ≤ |t0| + 1 := by
      have h1 : |s - t0| < 1 := by simpa [Real.dist_eq] using hs
      have h2 : |s| ≤ |s - t0| + |t0| := by
        simpa using abs_add_le (s - t0) t0
      linarith
    have h1 := hL.dist_le_mul _ (hxS s) _ (hQS k s)
    have h2 := hbd k s
    have h3 : Real.exp (K * |s|) ≤ C := by
      rw [hC]; gcongr
    have h4 : dist (Q k 0) p * ((K : ℝ) + 1) * C < ε := by
      have := (lt_div_iff₀ hA).1 hk
      linarith
    have hK0 : (0 : ℝ) ≤ K := K.2
    have hd : 0 ≤ dist (Q k 0) p := dist_nonneg
    calc dist (R (x s)) (R (Q k s)) ≤ K * dist (x s) (Q k s) := h1
      _ = K * dist (Q k s) (x s) := by rw [dist_comm]
      _ ≤ K * (dist (Q k 0) p * C) := by
          gcongr
          exact h2.trans (mul_le_mul_of_nonneg_left h3 hd)
      _ ≤ dist (Q k 0) p * ((K : ℝ) + 1) * C := by nlinarith [mul_nonneg hd hCpos.le]
      _ < ε := h4
  exact hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ hunif
    (Eventually.of_forall fun k s _ => hQ k s) (fun s _ => hx s) (mem_univ t)

end ROFLimit

namespace FiniteEnergyPlane

theorem exists_reebOrbit_of_tendsto_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (Q : ℕ → ReebOrbit H) (p : V n) (T' : ℝ) (hT' : 0 < T')
    (hp : Tendsto (fun k => (Q k).x 0) atTop (𝓝 p))
    (hT : Tendsto (fun k => (Q k).T) atTop (𝓝 T')) :
    ∃ P : ReebOrbit H, P.T = T' ∧ P.x 0 = p := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_reeb H hH
  have hcpt := isCompact_energySurface H hH
  obtain ⟨x, hxd, hxS, hx0, hx⟩ := ROFLimit.exists_limit_curve hK hcpt.isClosed
    (fun k => (Q k).x) (fun k t => (Q k).hasDerivAt t) (fun k t => (Q k).mem t) p hp
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hK.continuousOn
  have hper : ∀ τ, x (τ + T') = x τ := by
    intro τ
    have hlim : Tendsto (fun k => dist ((Q k).x (τ + T')) ((Q k).x τ)) atTop
        (𝓝 (dist (x (τ + T')) (x τ))) := (hx _).dist (hx _)
    have hb : Tendsto (fun k => C * ‖(τ + T') - (τ + (Q k).T)‖) atTop (𝓝 (C * ‖(τ + T') - (τ + T')‖)) :=
      ((tendsto_const_nhds.sub (tendsto_const_nhds.add hT)).norm).const_mul C
    have hle : ∀ k, dist ((Q k).x (τ + T')) ((Q k).x τ) ≤ C * ‖(τ + T') - (τ + (Q k).T)‖ := by
      intro k
      have h1 := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (f := (Q k).x)
        (f' := fun t => reeb H ((Q k).x t)) (C := C) (s := univ) (x := τ + (Q k).T) (y := τ + T')
        (fun t _ => ((Q k).hasDerivAt t).hasDerivWithinAt) (fun t _ => hC _ ((Q k).mem t))
        convex_univ (mem_univ _) (mem_univ _)
      rwa [(Q k).periodic τ, ← dist_eq_norm] at h1
    have := le_of_tendsto_of_tendsto' hlim hb hle
    simp only [sub_self, norm_zero, mul_zero] at this
    exact dist_le_zero.1 this
  exact ⟨⟨x, T', hT', hxS, hxd, hper⟩, rfl, hx0⟩

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (Q : ℕ → ReebOrbit H) (p : V n) (T' : ℝ) (hT' : 0 < T')
    (hp : Tendsto (fun k => (Q k).x 0) atTop (𝓝 p))
    (hT : Tendsto (fun k => (Q k).T) atTop (𝓝 T')) :
    ∃ P : ReebOrbit H, P.T = T' ∧ P.x 0 = p :=
  exists_reebOrbit_of_tendsto_aux H hH Q p T' hT' hp hT
