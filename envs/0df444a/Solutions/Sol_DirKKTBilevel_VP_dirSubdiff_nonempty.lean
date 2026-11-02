-- Prove2me | solution 1 for DirKKTBilevel.VP.dirSubdiff_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T00:59:23.343+00:00
-- url     : https://prove2.me/submissions/f813ad8f-47b1-4a64-850a-9e4e9af9283d

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional
open DirKKTBilevel.VP

/-- The basic cone estimate: `‖‖u‖w − ‖w‖u‖ ≤ 2‖u‖‖w − u‖`. -/
lemma dk_cone_est {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] (u w : X) :
    ‖‖u‖ • w - ‖w‖ • u‖ ≤ 2 * ‖u‖ * ‖w - u‖ := by
  have h : ‖u‖ • w - ‖w‖ • u = ‖u‖ • (w - u) + (‖u‖ - ‖w‖) • u := by
    rw [smul_sub, sub_smul]; abel
  rw [h]
  calc ‖‖u‖ • (w - u) + (‖u‖ - ‖w‖) • u‖ ≤ ‖‖u‖ • (w - u)‖ + ‖(‖u‖ - ‖w‖) • u‖ := norm_add_le _ _
    _ = ‖u‖ * ‖w - u‖ + |‖u‖ - ‖w‖| * ‖u‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_norm]
    _ ≤ ‖u‖ * ‖w - u‖ + ‖w - u‖ * ‖u‖ := by
        gcongr
        rw [abs_sub_comm]
        exact abs_norm_sub_norm_le w u
    _ = 2 * ‖u‖ * ‖w - u‖ := by ring

/-- Small dilates of a small ball around the direction lie in the directional neighbourhood. -/
lemma dk_cone_ball {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (u : X) (η : ℝ) (hη : 0 < η) :
    ∃ s r : ℝ, 0 < s ∧ s ≤ η ∧ 0 < r ∧ r ≤ η ∧
      ∀ w : X, ‖w - u‖ < r → s • w ∈ dirNbhd ε δ u := by
  classical
  set c : ℝ := if u = 0 then 1 else δ / (2 + δ) * ‖u‖ with hc
  have hcpos : 0 < c := by
    rw [hc]; split_ifs with hu
    · norm_num
    · have : 0 < ‖u‖ := norm_pos_iff.mpr hu
      positivity
  set r : ℝ := min η c with hr
  have hrpos : 0 < r := lt_min hη hcpos
  set s : ℝ := min η (ε / (‖u‖ + r + 1)) with hs
  have hspos : 0 < s := lt_min hη (by positivity)
  refine ⟨s, r, hspos, min_le_left _ _, hrpos, min_le_left _ _, fun w hw => ?_⟩
  have hwn : ‖w‖ ≤ ‖u‖ + r := by
    have := norm_le_insert' w u
    have h2 : ‖w‖ ≤ ‖u‖ + ‖w - u‖ := by
      calc ‖w‖ = ‖u + (w - u)‖ := by rw [add_sub_cancel]
        _ ≤ ‖u‖ + ‖w - u‖ := norm_add_le _ _
    linarith
  refine ⟨?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
    have h1 : s ≤ ε / (‖u‖ + r + 1) := min_le_right _ _
    have h2 : s * (‖u‖ + r + 1) ≤ ε := by
      rwa [le_div_iff₀ (by positivity)] at h1
    nlinarith [norm_nonneg w]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos, smul_smul,
      show (‖u‖ * s) • w - (s * ‖w‖) • u = s • (‖u‖ • w - ‖w‖ • u) by
        rw [smul_sub, smul_smul, smul_smul, mul_comm ‖u‖ s],
      norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
    by_cases hu : u = 0
    · subst hu; simp
    · have hc' : c = δ / (2 + δ) * ‖u‖ := by rw [hc, if_neg hu]
      have hrc : r ≤ δ / (2 + δ) * ‖u‖ := hc' ▸ min_le_right _ _
      have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
      have hwu : ‖w - u‖ ≤ δ / (2 + δ) * ‖u‖ := hw.le.trans hrc
      have hwlow : ‖u‖ - ‖w - u‖ ≤ ‖w‖ := by
        have : ‖u‖ ≤ ‖w‖ + ‖u - w‖ := by
          calc ‖u‖ = ‖w + (u - w)‖ := by rw [add_sub_cancel]
            _ ≤ ‖w‖ + ‖u - w‖ := norm_add_le _ _
        rw [norm_sub_rev] at this; linarith
      have key : 2 * ‖u‖ * ‖w - u‖ ≤ δ * ‖w‖ * ‖u‖ := by
        have e1 : (2 + δ) * ‖w - u‖ ≤ δ * ‖u‖ := by
          have := mul_le_mul_of_nonneg_left hwu (by positivity : (0:ℝ) ≤ 2 + δ)
          rw [show (2 + δ) * (δ / (2 + δ) * ‖u‖) = δ * ‖u‖ by field_simp] at this
          exact this
        have e2 : 2 * ‖w - u‖ ≤ δ * ‖w‖ := by nlinarith
        nlinarith
      calc s * ‖‖u‖ • w - ‖w‖ • u‖ ≤ s * (2 * ‖u‖ * ‖w - u‖) :=
            mul_le_mul_of_nonneg_left (dk_cone_est u w) hspos.le
        _ ≤ s * (δ * ‖w‖ * ‖u‖) := mul_le_mul_of_nonneg_left key hspos.le
        _ = δ * (s * ‖w‖) * ‖u‖ := by ring

/-- A differentiable real function gives regular subgradients of its `EReal` coercion. -/
lemma dk_regular_of_hasFDeriv {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (φ : X → EReal) (f : X → ℝ) (z : X) (hfeq : ∀ᶠ y in 𝓝 z, φ y = (f y : EReal))
    (hd : DifferentiableAt ℝ f z) : IsRegularSubgrad φ z (gradient f z) := by
  refine ⟨by rw [hfeq.self_of_nhds]; exact EReal.coe_ne_top _, fun ε hε => ?_⟩
  have ho := hd.hasFDerivAt.isLittleO
  have hb := ho.def hε
  filter_upwards [hb, hfeq] with y hy hφy
  rw [hφy, hfeq.self_of_nhds, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have hg : inner ℝ (gradient f z) (y - z) = fderiv ℝ f z (y - z) := by
    simp [gradient]
  rw [hg]
  rw [Real.norm_eq_abs] at hy
  have := (abs_le.mp hy).1
  linarith

theorem solution {n : ℕ} (φ : E n → EReal) (x u : E n)
    (h : DirLipschitzAtEReal φ x u) : (dirSubdiff φ x u).Nonempty := by
  obtain ⟨L, ε, δ, hL, hε, hδ, hfin, hlip⟩ := h
  set f : E n → ℝ := fun z => (φ z).toReal with hf
  set S : Set (E n) := {z | z - x ∈ DirKKTBilevel.VP.dirNbhd ε δ u} with hS
  have hφS : ∀ z ∈ S, φ z = (f z : EReal) := fun z hz => by
    rw [hf]; exact (EReal.coe_toReal (hfin z hz).2 (hfin z hz).1).symm
  have hLS : LipschitzOnWith (Real.toNNReal L) f S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    rw [Real.coe_toNNReal _ hL.le, Real.dist_eq, dist_eq_norm]
    exact hlip a b ha hb
  have hrad := hLS.ae_differentiableWithinAt_of_mem (μ := MeasureTheory.volume)
  -- one approximating point for each tolerance
  have step : ∀ k : ℕ, ∃ s : ℝ, ∃ w g : E n, 0 < s ∧ s ≤ 1 / ((k:ℝ) + 1) ∧
      ‖w - u‖ ≤ 1 / ((k:ℝ) + 1) ∧ ‖g‖ ≤ L ∧ x + s • w ∈ S ∧
      IsRegularSubgrad φ (x + s • w) g := by
    intro k
    obtain ⟨s, r, hs, hsη, hr, hrη, hcone⟩ :=
      dk_cone_ball ε δ hε hδ u (1 / ((k:ℝ) + 1)) (by positivity)
    set B := Metric.ball (x + s • u) (s * r) with hB
    have hBS : B ⊆ S := by
      intro p hp
      have hp' : p = x + s • (s⁻¹ • (p - x)) := by
        rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul, add_sub_cancel]
      have hw : ‖s⁻¹ • (p - x) - u‖ < r := by
        have : s⁻¹ • (p - x) - u = s⁻¹ • (p - (x + s • u)) := by
          rw [smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]; abel
        rw [this, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, ← dist_eq_norm,
          inv_mul_lt_iff₀ hs]
        exact hp
      show p - x ∈ DirKKTBilevel.VP.dirNbhd ε δ u
      rw [hp', add_sub_cancel_left]
      exact hcone _ hw
    have hBpos : MeasureTheory.volume B ≠ 0 :=
      (Metric.measure_ball_pos _ _ (by positivity)).ne'
    obtain ⟨p, hpB, hpd⟩ := MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae hBpos
      (MeasureTheory.ae_restrict_of_ae hrad)
    have hBn : S ∈ 𝓝 p := Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hpB) hBS
    have hdiff : DifferentiableAt ℝ f p := (hpd (hBS hpB)).differentiableAt hBn
    refine ⟨s, s⁻¹ • (p - x), gradient f p, hs, hsη, ?_, ?_, ?_, ?_⟩
    · have : s⁻¹ • (p - x) - u = s⁻¹ • (p - (x + s • u)) := by
        rw [smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]; abel
      rw [this, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hs, ← dist_eq_norm]
      have : dist p (x + s • u) < s * r := hpB
      have h2 : s⁻¹ * dist p (x + s • u) < r := by rwa [inv_mul_lt_iff₀ hs]
      linarith
    · have := norm_fderiv_le_of_lipschitzOn ℝ hBn hLS
      rw [Real.coe_toNNReal _ hL.le] at this
      simpa [gradient] using this
    · rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul, add_sub_cancel]
      exact hBS hpB
    · rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul, add_sub_cancel]
      apply dk_regular_of_hasFDeriv φ f p _ hdiff
      filter_upwards [hBn] with y hy using hφS y hy
  choose s w g hs hsk hwk hgk hS' hreg using step
  -- compactness of the gradients
  obtain ⟨ξ, -, ψ, hψ, hlim⟩ := (isCompact_closedBall (0 : E n) L).tendsto_subseq
    (x := g) (fun k => by simpa using hgk k)
  have hx0 : x ∈ S := by
    show x - x ∈ DirKKTBilevel.VP.dirNbhd ε δ u
    rw [sub_self]; refine ⟨by simpa using hε, by simp⟩
  have hk0 : Tendsto (fun k : ℕ => 1 / ((ψ k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hψ.tendsto_atTop
  have hsT : Tendsto (fun k => s (ψ k)) atTop (𝓝 0) :=
    squeeze_zero (fun k => (hs (ψ k)).le) (fun k => hsk (ψ k)) hk0
  have hwT : Tendsto (fun k => w (ψ k)) atTop (𝓝 u) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun k => norm_nonneg _) (fun k => hwk (ψ k)) hk0
  refine ⟨ξ, (hfin x hx0).2, (hfin x hx0).1, fun k => s (ψ k), fun k => w (ψ k),
    fun k => g (ψ k), fun k => hs (ψ k), hsT, hwT, hlim, ?_, fun k => hreg (ψ k)⟩
  -- continuity of the values
  have hfT : Tendsto (fun k => f (x + s (ψ k) • w (ψ k))) atTop (𝓝 (f x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hnT : Tendsto (fun k => L * ‖s (ψ k) • w (ψ k)‖) atTop (𝓝 (L * ‖(0:ℝ) • u‖)) :=
      (continuous_norm.tendsto _).comp (hsT.smul hwT) |>.const_mul L
    rw [zero_smul, norm_zero, mul_zero] at hnT
    apply squeeze_zero (fun k => norm_nonneg _) _ hnT
    intro k
    have := hlip _ _ (hS' (ψ k)) hx0
    rw [Real.norm_eq_abs]
    simpa [hf] using this
  have := (continuous_coe_real_ereal.tendsto _).comp hfT
  rw [hφS x hx0]
  apply this.congr
  intro k
  exact (hφS _ (hS' (ψ k))).symm
