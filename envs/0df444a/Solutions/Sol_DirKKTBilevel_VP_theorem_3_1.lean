-- Prove2me | solution 1 for DirKKTBilevel.VP.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T01:13:38.743168+00:00
-- url     : https://prove2.me/submissions/3d01b621-6e8e-4562-9e7c-5a999fb7048a

import Mathlib
import Definitions.Def_DirKKTBilevel_VP_Model

open Filter Topology
open NonconvexSplitting.Shared SetConstrSOC.Directional
open DirKKTBilevel.VP

/-! ### Geometry of directional neighbourhoods -/

lemma t31_cone_est {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] (u w : X) :
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

/-- Uniform version: small dilates of a closed ball around the direction lie in the directional
neighbourhood. -/
lemma t31_cone_uniform {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (u : X) :
    ∃ r s0 : ℝ, 0 < r ∧ 0 < s0 ∧
      ∀ s : ℝ, 0 < s → s ≤ s0 → ∀ w : X, ‖w - u‖ ≤ r → s • w ∈ DirKKTBilevel.VP.dirNbhd ε δ u := by
  classical
  set c : ℝ := if u = 0 then 1 else δ / (2 + δ) * ‖u‖ with hc
  have hcpos : 0 < c := by
    rw [hc]; split_ifs with hu
    · norm_num
    · have : 0 < ‖u‖ := norm_pos_iff.mpr hu
      positivity
  set r : ℝ := c / 2 with hr
  have hrpos : 0 < r := by positivity
  set s0 : ℝ := ε / (‖u‖ + r + 1) with hs0
  have hs0pos : 0 < s0 := by positivity
  refine ⟨r, s0, hrpos, hs0pos, fun s hs hss0 w hw => ?_⟩
  have hwn : ‖w‖ ≤ ‖u‖ + r := by
    have h2 : ‖w‖ ≤ ‖u‖ + ‖w - u‖ := by
      calc ‖w‖ = ‖u + (w - u)‖ := by rw [add_sub_cancel]
        _ ≤ ‖u‖ + ‖w - u‖ := norm_add_le _ _
    linarith
  refine ⟨?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    have h2 : s * (‖u‖ + r + 1) ≤ ε := by
      rwa [hs0, le_div_iff₀ (by positivity)] at hss0
    nlinarith [norm_nonneg w]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, smul_smul,
      show (‖u‖ * s) • w - (s * ‖w‖) • u = s • (‖u‖ • w - ‖w‖ • u) by
        rw [smul_sub, smul_smul, smul_smul, mul_comm ‖u‖ s],
      norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    by_cases hu : u = 0
    · subst hu; simp
    · have hc' : c = δ / (2 + δ) * ‖u‖ := by rw [hc, if_neg hu]
      have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu
      have hwu : ‖w - u‖ ≤ δ / (2 + δ) * ‖u‖ := by
        have : r ≤ c := by rw [hr]; linarith
        linarith [hc' ▸ this]
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
            mul_le_mul_of_nonneg_left (t31_cone_est u w) hs.le
        _ ≤ s * (δ * ‖w‖ * ‖u‖) := mul_le_mul_of_nonneg_left key hs.le
        _ = δ * (s * ‖w‖) * ‖u‖ := by ring

lemma t31_dirNbhd_mono {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {ε ε' δ δ' : ℝ} (u : X) (hε : ε ≤ ε') (hδ : δ ≤ δ') :
    DirKKTBilevel.VP.dirNbhd ε δ u ⊆ DirKKTBilevel.VP.dirNbhd ε' δ' u := by
  intro w ⟨h1, h2⟩
  refine ⟨lt_of_lt_of_le h1 hε, h2.trans ?_⟩
  have : 0 ≤ ‖w‖ * ‖u‖ := by positivity
  nlinarith

/-! ### Euclidean-space bookkeeping -/

lemma t31_inner_eq {q : ℕ} (x y : E q) : inner ℝ x y = ∑ j, x j * y j := by
  simp [PiLp.inner_apply, mul_comm]

lemma t31_norm_sq {q : ℕ} (x : E q) : ‖x‖ ^ 2 = ∑ j, (x j) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

lemma t31_norm_posPart {q : ℕ} (a : E q) :
    ‖DirKKTBilevel.VP.posPart a‖ = Real.sqrt (∑ j, (max (a j) 0) ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  simp [DirKKTBilevel.VP.posPart, Real.norm_eq_abs, sq_abs]

/-- `‖a₊‖ ≤ ‖a − b‖` whenever `b ≤ 0`. -/
lemma t31_posPart_le {q : ℕ} (a b : E q) (hb : ∀ j, b j ≤ 0) :
    ‖DirKKTBilevel.VP.posPart a‖ ≤ ‖a - b‖ := by
  rw [t31_norm_posPart, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro j _
  simp only [PiLp.sub_apply, Real.norm_eq_abs, sq_abs]
  have := hb j
  rcases le_total (a j) 0 with h | h
  · rw [max_eq_right h]; nlinarith [sq_nonneg (a j - b j)]
  · rw [max_eq_left h]; nlinarith

lemma t31_abs_sum_le {q : ℕ} (l a : E q) : |∑ j, l j * a j| ≤ ‖l‖ * ‖a‖ := by
  rw [← t31_inner_eq]; exact abs_real_inner_le_norm l a

/-! ### The smoothing of `ρ‖·₊‖` -/

lemma t31_sq_pos_le (x y : ℝ) :
    (max y 0) ^ 2 ≤ (max x 0) ^ 2 + 2 * max x 0 * (y - x) + (y - x) ^ 2 := by
  have : (max x 0) ^ 2 + 2 * max x 0 * (y - x) + (y - x) ^ 2 = (max x 0 + (y - x)) ^ 2 := by ring
  rw [this]
  rcases le_total y 0 with hy | hy
  · rw [max_eq_right hy]; nlinarith [sq_nonneg (max x 0 + (y - x))]
  · rw [max_eq_left hy]
    rcases le_total x 0 with hx | hx
    · rw [max_eq_right hx]; nlinarith
    · rw [max_eq_left hx]; nlinarith

/-- Concavity of the square root as a tangent bound. -/
lemma t31_sqrt_tangent (S y : ℝ) (hS : 0 < S) (hy : 0 ≤ y) :
    Real.sqrt y ≤ S + (y - S ^ 2) / (2 * S) := by
  have h := sq_nonneg (Real.sqrt y - S)
  have hsy := Real.sq_sqrt hy
  rw [show S + (y - S ^ 2) / (2 * S) = (S ^ 2 + y) / (2 * S) by field_simp; ring]
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- The smoothing `H(a) = ρ √(Σ (a_j)₊² + μ²)`. -/
noncomputable def t31_H {q : ℕ} (ρ μ : ℝ) (a : E q) : ℝ :=
  ρ * Real.sqrt (∑ j, (max (a j) 0) ^ 2 + μ ^ 2)

/-- Its "gradient" `ζ(a) = ρ a₊ / √(Σ (a_j)₊² + μ²)`. -/
noncomputable def t31_ζ {q : ℕ} (ρ μ : ℝ) (a : E q) : E q :=
  WithLp.toLp 2 (fun j => ρ * max (a j) 0 / Real.sqrt (∑ i, (max (a i) 0) ^ 2 + μ ^ 2))

lemma t31_H_upper {q : ℕ} (ρ μ : ℝ) (hρ : 0 < ρ) (hμ : 0 < μ) (a b : E q) :
    t31_H ρ μ b ≤ t31_H ρ μ a + ∑ j, t31_ζ ρ μ a j * (b j - a j) + ρ / (2 * μ) * ‖b - a‖ ^ 2 := by
  set Qa := ∑ j, (max (a j) 0) ^ 2 with hQa
  set Qb := ∑ j, (max (b j) 0) ^ 2 with hQb
  set S := Real.sqrt (Qa + μ ^ 2) with hS
  have hQa0 : 0 ≤ Qa := by positivity
  have hQb0 : 0 ≤ Qb := by positivity
  have hSμ : μ ≤ S := by
    rw [hS]; apply Real.le_sqrt_of_sq_le; linarith
  have hSpos : 0 < S := lt_of_lt_of_le hμ hSμ
  have hS2 : S ^ 2 = Qa + μ ^ 2 := Real.sq_sqrt (by positivity)
  have htan := t31_sqrt_tangent S (Qb + μ ^ 2) hSpos (by positivity)
  have hQdiff : Qb - Qa ≤ 2 * ∑ j, max (a j) 0 * (b j - a j) + ‖b - a‖ ^ 2 := by
    rw [t31_norm_sq, hQb, hQa, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    have := t31_sq_pos_le (a j) (b j)
    simp only [PiLp.sub_apply]
    nlinarith
  have hζ : ∑ j, t31_ζ ρ μ a j * (b j - a j) = ρ / S * ∑ j, max (a j) 0 * (b j - a j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [t31_ζ]
    rw [← hQa, ← hS]
    ring
  rw [hζ]
  unfold t31_H
  rw [← hQa, ← hQb, ← hS]
  have hnn : 0 ≤ ‖b - a‖ ^ 2 := by positivity
  have h1 : Real.sqrt (Qb + μ ^ 2) ≤ S + (Qb - Qa) / (2 * S) := by
    have : (Qb + μ ^ 2 - S ^ 2) = Qb - Qa := by rw [hS2]; ring
    rw [← this]; exact htan
  have h2 : ρ * Real.sqrt (Qb + μ ^ 2) ≤ ρ * S + ρ / S * ∑ j, max (a j) 0 * (b j - a j)
      + ρ / (2 * S) * ‖b - a‖ ^ 2 := by
    calc ρ * Real.sqrt (Qb + μ ^ 2) ≤ ρ * (S + (Qb - Qa) / (2 * S)) :=
          mul_le_mul_of_nonneg_left h1 hρ.le
      _ ≤ ρ * (S + (2 * ∑ j, max (a j) 0 * (b j - a j) + ‖b - a‖ ^ 2) / (2 * S)) := by
          gcongr
      _ = ρ * S + ρ / S * ∑ j, max (a j) 0 * (b j - a j) + ρ / (2 * S) * ‖b - a‖ ^ 2 := by
          field_simp; ring
  have h3 : ρ / (2 * S) * ‖b - a‖ ^ 2 ≤ ρ / (2 * μ) * ‖b - a‖ ^ 2 := by
    gcongr
  linarith

lemma t31_H_bounds {q : ℕ} (ρ μ : ℝ) (hρ : 0 < ρ) (hμ : 0 < μ) (a : E q) :
    ρ * ‖DirKKTBilevel.VP.posPart a‖ ≤ t31_H ρ μ a ∧
      t31_H ρ μ a ≤ ρ * ‖DirKKTBilevel.VP.posPart a‖ + ρ * μ := by
  rw [t31_norm_posPart]
  unfold t31_H
  set Q := ∑ j, (max (a j) 0) ^ 2
  have hQ : 0 ≤ Q := by positivity
  constructor
  · gcongr; linarith [sq_nonneg μ]
  · rw [← mul_add]
    gcongr
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hQ, Real.sqrt_nonneg Q]

lemma t31_ζ_props {q : ℕ} (ρ μ : ℝ) (hρ : 0 < ρ) (hμ : 0 < μ) (a : E q) :
    (∀ j, 0 ≤ t31_ζ ρ μ a j) ∧ (∀ j, a j ≤ 0 → t31_ζ ρ μ a j = 0) ∧ ‖t31_ζ ρ μ a‖ ≤ ρ := by
  set S := Real.sqrt (∑ i, (max (a i) 0) ^ 2 + μ ^ 2) with hS
  have hSpos : 0 < S := Real.sqrt_pos.mpr (by positivity)
  refine ⟨fun j => ?_, fun j hj => ?_, ?_⟩
  · simp only [t31_ζ]; positivity
  · simp only [t31_ζ, max_eq_right hj, mul_zero, zero_div]
  · have : t31_ζ ρ μ a = (ρ / S) • DirKKTBilevel.VP.posPart a := by
      ext j; simp only [t31_ζ, DirKKTBilevel.VP.posPart, PiLp.smul_apply, smul_eq_mul]
      rw [← hS]; ring
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), t31_norm_posPart]
    rw [div_mul_eq_mul_div, div_le_iff₀ hSpos]
    gcongr
    rw [hS]; apply Real.sqrt_le_sqrt; linarith [sq_nonneg μ]

/-! ### The perturbation lemma -/

lemma t31_perturb {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] (A : X → ℝ) (p η : X) (R κ : ℝ) (hR : 0 < R) (hκ : 0 < κ)
    (hA : ContinuousOn A (Metric.closedBall p R))
    (hineq : ∀ w ∈ Metric.closedBall p R, A p - κ * ‖w - p‖ ≤ A w - inner ℝ η (w - p)) :
    ∃ p' η' : X, ‖p' - p‖ ≤ R / 2 ∧ ‖η' - η‖ ≤ 2 * κ ∧
      IsRegularSubgrad (fun w => ((A w : ℝ) : EReal)) p' η' := by
  set β := 2 * κ / R with hβ
  have hβpos : 0 < β := by positivity
  set Φ : X → ℝ := fun w => A w - inner ℝ η (w - p) + β * ‖w - p‖ ^ 2 with hΦ
  have hΦc : ContinuousOn Φ (Metric.closedBall p R) := by
    apply ContinuousOn.add (hA.sub (by fun_prop)) (by fun_prop)
  obtain ⟨p', hp'mem, hmin⟩ := (isCompact_closedBall p R).exists_isMinOn
    ⟨p, Metric.mem_closedBall_self hR.le⟩ hΦc
  have hΦp : Φ p = A p := by simp [hΦ]
  have hle := hmin (Metric.mem_closedBall_self hR.le)
  simp only at hle
  have hdist : ‖p' - p‖ ≤ R / 2 := by
    have h1 := hineq p' hp'mem
    have h2 : Φ p' ≤ A p := hΦp ▸ hle
    simp only [hΦ] at h2
    have h3 : β * ‖p' - p‖ ^ 2 ≤ κ * ‖p' - p‖ := by linarith
    rcases (norm_nonneg (p' - p)).lt_or_eq with hpos | hzero
    · have : β * ‖p' - p‖ ≤ κ := by
        have := h3; rw [sq] at this; nlinarith
      rw [hβ] at this
      rw [div_mul_eq_mul_div, div_le_iff₀ hR] at this
      nlinarith
    · rw [← hzero]; positivity
  refine ⟨p', η - (2 * β) • (p' - p), hdist, ?_, ?_⟩
  · rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc 2 * β * ‖p' - p‖ ≤ 2 * β * (R / 2) := by gcongr
      _ = 2 * κ := by rw [hβ]; field_simp
  · refine ⟨EReal.coe_ne_top _, fun ε hε => ?_⟩
    have hball : Metric.ball p' (min (R / 2) (ε / β)) ∈ 𝓝 p' :=
      Metric.ball_mem_nhds _ (lt_min (by positivity) (by positivity))
    filter_upwards [hball] with w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hw1 : ‖w - p'‖ < R / 2 := lt_of_lt_of_le hw (min_le_left _ _)
    have hw2 : ‖w - p'‖ < ε / β := lt_of_lt_of_le hw (min_le_right _ _)
    have hwmem : w ∈ Metric.closedBall p R := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      calc ‖w - p‖ = ‖(w - p') + (p' - p)‖ := by abel_nf
        _ ≤ ‖w - p'‖ + ‖p' - p‖ := norm_add_le _ _
        _ ≤ R := by linarith
    have hmw := hmin hwmem
    simp only [hΦ, Set.mem_setOf_eq] at hmw
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    -- expand the squares
    have hexp : ‖w - p‖ ^ 2 = ‖p' - p‖ ^ 2 + 2 * inner ℝ (p' - p) (w - p') + ‖w - p'‖ ^ 2 := by
      have : w - p = (p' - p) + (w - p') := by abel
      rw [this, norm_add_sq_real]
    have hlin : inner ℝ η (w - p) = inner ℝ η (p' - p) + inner ℝ η (w - p') := by
      rw [← inner_add_right]; congr 1; abel
    have hin : inner ℝ (η - (2 * β) • (p' - p)) (w - p') =
        inner ℝ η (w - p') - 2 * β * inner ℝ (p' - p) (w - p') := by
      rw [inner_sub_left, real_inner_smul_left]
    rw [hin]
    rw [hexp, hlin] at hmw
    have hdist2 : β * (‖p' - p‖ ^ 2 + 2 * inner ℝ (p' - p) (w - p') + ‖w - p'‖ ^ 2) =
        β * ‖p' - p‖ ^ 2 + 2 * β * inner ℝ (p' - p) (w - p') + β * ‖w - p'‖ ^ 2 := by ring
    have hq : β * ‖w - p'‖ ^ 2 ≤ ε * ‖w - p'‖ := by
      have := (lt_div_iff₀ hβpos).mp hw2
      rw [sq]; nlinarith [norm_nonneg (w - p')]
    linarith

lemma t31_H_cont {q : ℕ} (ρ μ : ℝ) : Continuous (t31_H (q := q) ρ μ) := by
  unfold t31_H
  have : Continuous (fun a : E q => ∑ j, (max (a j) 0) ^ 2 + μ ^ 2) := by
    apply Continuous.add _ continuous_const
    apply continuous_finset_sum
    intro j _
    have hj : Continuous (fun a : E q => a j) :=
      (PiLp.proj (p := 2) (𝕜 := ℝ) (fun _ : Fin q => ℝ) j).continuous
    exact (hj.max continuous_const).pow 2
  exact continuous_const.mul (Real.continuous_sqrt.comp this)

/-! ### One approximation step -/

lemma t31_step {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] {q : ℕ} (obj : X → ℝ) (con : X → E q) (z u : X)
    (L ε₂ δ₁ ρ : ℝ) (hL : 0 < L) (hε₂ : 0 < ε₂) (hδ₁ : 0 < δ₁) (hρ : 0 < ρ)
    (hlip : ∀ w w', w - z ∈ DirKKTBilevel.VP.dirNbhd ε₂ δ₁ u →
      w' - z ∈ DirKKTBilevel.VP.dirNbhd ε₂ δ₁ u → ‖con w - con w'‖ ≤ L * ‖w - w'‖)
    (hlow : ∀ w, w - z ∈ DirKKTBilevel.VP.dirNbhd ε₂ δ₁ u →
      obj z ≤ obj w + ρ * ‖DirKKTBilevel.VP.posPart (con w)‖)
    (heq7 : Tendsto (fun t : ℝ => (obj (z + t • u) +
      ρ * ‖DirKKTBilevel.VP.posPart (con (z + t • u))‖ - obj z) / t) (𝓝[>] 0) (𝓝 0))
    (hdiff : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ obj w)
    (hgc : ContinuousAt (gradient obj) z) (τ : ℝ) (hτ : 0 < τ) :
    ∃ (t : ℝ) (w : X) (ζ : E q) (η : X) (R0 : ℝ), 0 < t ∧ t ≤ τ ∧
      (z + t • u) - z ∈ DirKKTBilevel.VP.dirNbhd ε₂ δ₁ u ∧
      ‖w - (z + t • u)‖ ≤ t * τ ∧ ‖η + gradient obj z‖ ≤ τ ∧
      (∀ j, 0 ≤ ζ j) ∧ (∀ j, con w j ≤ 0 → ζ j = 0) ∧ ‖ζ‖ ≤ ρ ∧ 0 < R0 ∧
      (∀ w', ‖w' - w‖ ≤ R0 → w' - z ∈ DirKKTBilevel.VP.dirNbhd ε₂ δ₁ u) ∧
      (∀ ε' : ℝ, 0 < ε' → ∀ᶠ w' in 𝓝 w,
        (∑ j, ζ j * con w j) - ε' * ‖w' - w‖ ≤ (∑ j, ζ j * con w' j) - inner ℝ η (w' - w)) := by
  obtain ⟨r, s0, hr, hs0, hcone⟩ := t31_cone_uniform ε₂ δ₁ hε₂ hδ₁ u
  -- the closed ball around `z + t u` of radius `r t` lies in the cone
  have hball : ∀ t : ℝ, 0 < t → t ≤ s0 → ∀ w', ‖w' - (z + t • u)‖ ≤ r * t →
      w' - z ∈ DirKKTBilevel.VP.dirNbhd ε₂ δ₁ u := by
    intro t ht hts w' hw'
    have hrw : w' - z = t • (t⁻¹ • (w' - z)) := by
      rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    rw [hrw]
    apply hcone t ht hts
    have : t⁻¹ • (w' - z) - u = t⁻¹ • (w' - (z + t • u)) := by
      rw [smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]; abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht, inv_mul_le_iff₀ ht]
    linarith
  -- a neighbourhood of `z` where `obj` is differentiable with gradient close to `∇obj z`
  have hgc' : ∀ᶠ w in 𝓝 z, dist (gradient obj w) (gradient obj z) < τ / 2 :=
    hgc.eventually (Metric.ball_mem_nhds _ (by positivity))
  obtain ⟨R1, hR1, hR1prop⟩ := Metric.eventually_nhds_iff.mp (hdiff.and hgc')
  -- eventual conditions on `t`
  set m : ℝ := min (min τ (r / 2)) (τ / 4) with hm
  have hmpos : 0 < m := by positivity
  have hσ : Tendsto (fun t : ℝ => (obj (z + t • u) +
      ρ * ‖DirKKTBilevel.VP.posPart (con (z + t • u))‖ - obj z) / t + ρ * t) (𝓝[>] 0) (𝓝 0) := by
    have := heq7.add ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).const_mul ρ)
    simpa using this
  have hT1 : ∀ᶠ t in 𝓝[>] (0:ℝ), t * (‖u‖ + r) < R1 := by
    have : Tendsto (fun t : ℝ => t * (‖u‖ + r)) (𝓝[>] 0) (𝓝 (0 * (‖u‖ + r))) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).mul tendsto_const_nhds
    rw [zero_mul] at this
    exact this.eventually (gt_mem_nhds hR1)
  have hT2 : ∀ᶠ t in 𝓝[>] (0:ℝ), t < min s0 τ := by
    have : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    exact this.eventually (gt_mem_nhds (lt_min hs0 hτ))
  have hT3 := hσ.eventually (gt_mem_nhds (show (0:ℝ) < m ^ 2 by positivity))
  obtain ⟨t, ⟨⟨h1, h2⟩, h3⟩, ht0⟩ := ((hT1.and hT2).and hT3 |>.and self_mem_nhdsWithin).exists
  have ht : (0:ℝ) < t := ht0
  have hts0 : t ≤ s0 := (lt_of_lt_of_le h2 (min_le_left _ _)).le
  have htτ : t ≤ τ := (lt_of_lt_of_le h2 (min_le_right _ _)).le
  set zt : X := z + t • u with hzt
  set μ : ℝ := t ^ 2 with hμ
  have hμpos : 0 < μ := by positivity
  set B := Metric.closedBall zt (r * t) with hB
  have hBC : ∀ w' ∈ B, w' - z ∈ DirKKTBilevel.VP.dirNbhd ε₂ δ₁ u := fun w' hw' =>
    hball t ht hts0 w' (by rw [hB, Metric.mem_closedBall, dist_eq_norm] at hw'; exact hw')
  have hBR1 : ∀ w' ∈ B, dist w' z < R1 := by
    intro w' hw'
    rw [hB, Metric.mem_closedBall, dist_eq_norm] at hw'
    rw [dist_eq_norm]
    calc ‖w' - z‖ = ‖(w' - zt) + t • u‖ := by rw [hzt]; abel_nf
      _ ≤ ‖w' - zt‖ + ‖t • u‖ := norm_add_le _ _
      _ ≤ r * t + t * ‖u‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]; linarith
      _ = t * (‖u‖ + r) := by ring
      _ < R1 := h1
  -- the auxiliary objective
  set Θ : X → ℝ := fun w' => obj w' + t31_H ρ μ (con w') + ‖w' - zt‖ ^ 2 / t with hΘ
  have hobjc : ContinuousOn obj B := fun w' hw' =>
    ((hR1prop (hBR1 w' hw')).1).continuousAt.continuousWithinAt
  have hconc : ContinuousOn con B := by
    have : LipschitzOnWith (Real.toNNReal L) con B := by
      apply LipschitzOnWith.of_dist_le_mul
      intro a ha b hb
      rw [Real.coe_toNNReal _ hL.le, dist_eq_norm, dist_eq_norm]
      exact hlip a b (hBC a ha) (hBC b hb)
    exact this.continuousOn
  have hΘc : ContinuousOn Θ B := by
    apply ContinuousOn.add (hobjc.add ((t31_H_cont ρ μ).comp_continuousOn hconc))
    exact ContinuousOn.div_const (by fun_prop) t
  have hztB : zt ∈ B := Metric.mem_closedBall_self (by positivity)
  obtain ⟨w, hwB, hmin⟩ := (isCompact_closedBall zt (r * t)).exists_isMinOn ⟨zt, hztB⟩ hΘc
  have hwC := hBC w hwB
  -- localisation of the minimiser
  have hdist : ‖w - zt‖ ≤ t * m := by
    have hΘw : Θ w ≤ Θ zt := hmin hztB
    have hHzt := (t31_H_bounds ρ μ hρ hμpos (con zt)).2
    have hHw := (t31_H_bounds ρ μ hρ hμpos (con w)).1
    have hlw := hlow w hwC
    simp only [hΘ, sub_self, norm_zero] at hΘw
    have hq : ‖w - zt‖ ^ 2 / t ≤ (obj zt + ρ * ‖DirKKTBilevel.VP.posPart (con zt)‖ - obj z)
        + ρ * μ := by
      have : (0:ℝ) ^ 2 / t = 0 := by simp
      linarith
    have h3' : (obj zt + ρ * ‖DirKKTBilevel.VP.posPart (con zt)‖ - obj z) / t + ρ * t < m ^ 2 := h3
    have hsq : ‖w - zt‖ ^ 2 ≤ (t * m) ^ 2 := by
      have e1 : ‖w - zt‖ ^ 2 ≤ t * ((obj zt + ρ * ‖DirKKTBilevel.VP.posPart (con zt)‖ - obj z)
          + ρ * μ) := by
        rwa [div_le_iff₀ ht, mul_comm] at hq
      have e2 : t * ((obj zt + ρ * ‖DirKKTBilevel.VP.posPart (con zt)‖ - obj z) + ρ * μ) =
          t ^ 2 * ((obj zt + ρ * ‖DirKKTBilevel.VP.posPart (con zt)‖ - obj z) / t + ρ * t) := by
        rw [hμ]; field_simp
      rw [e2] at e1
      calc ‖w - zt‖ ^ 2 ≤ t ^ 2 * ((obj zt + ρ * ‖DirKKTBilevel.VP.posPart (con zt)‖ - obj z) / t
            + ρ * t) := e1
        _ ≤ t ^ 2 * m ^ 2 := by gcongr
        _ = (t * m) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).mp hsq
  have hmτ : m ≤ τ := (min_le_left _ _).trans (min_le_left _ _)
  have hmr : m ≤ r / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hm4 : m ≤ τ / 4 := min_le_right _ _
  set R0 : ℝ := r * t / 2 with hR0
  have hR0B : ∀ w', ‖w' - w‖ ≤ R0 → w' ∈ B := by
    intro w' hw'
    rw [hB, Metric.mem_closedBall, dist_eq_norm]
    calc ‖w' - zt‖ = ‖(w' - w) + (w - zt)‖ := by abel_nf
      _ ≤ ‖w' - w‖ + ‖w - zt‖ := norm_add_le _ _
      _ ≤ r * t / 2 + t * m := by linarith
      _ ≤ r * t := by nlinarith
  have hwR1 := hR1prop (hBR1 w hwB)
  set ζ := t31_ζ ρ μ (con w) with hζ
  set η : X := -gradient obj w - (2 / t) • (w - zt) with hη
  obtain ⟨hζ1, hζ2, hζ3⟩ := t31_ζ_props ρ μ hρ hμpos (con w)
  refine ⟨t, w, ζ, η, R0, ht, htτ, ?_, ?_, ?_, hζ1, hζ2, hζ3, by positivity,
    fun w' hw' => hBC w' (hR0B w' hw'), ?_⟩
  · exact hBC zt hztB
  · exact hdist.trans (by gcongr)
  · -- the multiplier estimate
    have e1 : η + gradient obj z = (gradient obj z - gradient obj w) - (2 / t) • (w - zt) := by
      rw [hη]; abel
    rw [e1]
    have e2 : ‖gradient obj z - gradient obj w‖ < τ / 2 := by
      rw [← dist_eq_norm, dist_comm]; exact hwR1.2
    have e3 : ‖(2 / t) • (w - zt)‖ ≤ 2 * m := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      calc 2 / t * ‖w - zt‖ ≤ 2 / t * (t * m) := by gcongr
        _ = 2 * m := by field_simp
    calc ‖gradient obj z - gradient obj w - (2 / t) • (w - zt)‖
        ≤ ‖gradient obj z - gradient obj w‖ + ‖(2 / t) • (w - zt)‖ := norm_sub_le _ _
      _ ≤ τ := by linarith
  · -- the Fréchet inequality
    intro ε' hε'
    set C : ℝ := 1 / t + ρ / (2 * μ) * L ^ 2 with hC
    have hCpos : 0 < C := by positivity
    have hd := hwR1.1.hasFDerivAt.isLittleO.def (half_pos hε')
    have hnear : ∀ᶠ w' in 𝓝 w, ‖w' - w‖ < min R0 (ε' / (2 * C)) := by
      have := Metric.ball_mem_nhds w (lt_min (by positivity : (0:ℝ) < R0)
        (by positivity : (0:ℝ) < ε' / (2 * C)))
      filter_upwards [this] with w' hw'
      rwa [Metric.mem_ball, dist_eq_norm] at hw'
    filter_upwards [hd, hnear] with w' hw'd hw'n
    have hw'1 : ‖w' - w‖ ≤ R0 := (lt_of_lt_of_le hw'n (min_le_left _ _)).le
    have hw'2 : ‖w' - w‖ ≤ ε' / (2 * C) := (lt_of_lt_of_le hw'n (min_le_right _ _)).le
    have hw'B := hR0B w' hw'1
    have hΘ' : Θ w ≤ Θ w' := hmin hw'B
    simp only [hΘ] at hΘ'
    have hHup := t31_H_upper ρ μ hρ hμpos (con w) (con w')
    have hLc : ‖con w' - con w‖ ≤ L * ‖w' - w‖ := hlip w' w (hBC w' hw'B) hwC
    have hLc2 : ‖con w' - con w‖ ^ 2 ≤ L ^ 2 * ‖w' - w‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hLc 2
      rwa [mul_pow] at this
    have hexp : ‖w' - zt‖ ^ 2 = ‖w - zt‖ ^ 2 + 2 * inner ℝ (w - zt) (w' - w) + ‖w' - w‖ ^ 2 := by
      have : w' - zt = (w - zt) + (w' - w) := by abel
      rw [this, norm_add_sq_real]
    rw [Real.norm_eq_abs] at hw'd
    have hobj := (abs_le.mp hw'd).2
    have hg : inner ℝ (gradient obj w) (w' - w) = fderiv ℝ obj w (w' - w) := by
      simp [gradient]
    have hηin : inner ℝ η (w' - w) = -(fderiv ℝ obj w (w' - w)) -
        2 / t * inner ℝ (w - zt) (w' - w) := by
      rw [hη, inner_sub_left, inner_neg_left, real_inner_smul_left, hg]
    have hsum : ∑ j, ζ j * (con w' j - con w j) = (∑ j, ζ j * con w' j) - ∑ j, ζ j * con w j := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro j _; ring
    rw [hsum] at hHup
    rw [hηin]
    -- collect the quadratic terms
    have hquad : ‖w' - w‖ ^ 2 / t + ρ / (2 * μ) * ‖con w' - con w‖ ^ 2 ≤ C * ‖w' - w‖ ^ 2 := by
      rw [hC, add_mul]
      have : ρ / (2 * μ) * ‖con w' - con w‖ ^ 2 ≤ ρ / (2 * μ) * (L ^ 2 * ‖w' - w‖ ^ 2) := by
        gcongr
      have e : ‖w' - w‖ ^ 2 / t = 1 / t * ‖w' - w‖ ^ 2 := by ring
      have e2 : ρ / (2 * μ) * (L ^ 2 * ‖w' - w‖ ^ 2) = ρ / (2 * μ) * L ^ 2 * ‖w' - w‖ ^ 2 := by
        ring
      rw [e]
      linarith
    have hCq : C * ‖w' - w‖ ^ 2 ≤ ε' / 2 * ‖w' - w‖ := by
      have := (le_div_iff₀ (by positivity : (0:ℝ) < 2 * C)).mp hw'2
      have h1 : C * ‖w' - w‖ ≤ ε' / 2 := by linarith
      calc C * ‖w' - w‖ ^ 2 = (C * ‖w' - w‖) * ‖w' - w‖ := by ring
        _ ≤ ε' / 2 * ‖w' - w‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    have hexp' : ‖w' - zt‖ ^ 2 / t = ‖w - zt‖ ^ 2 / t + 2 / t * inner ℝ (w - zt) (w' - w) +
        ‖w' - w‖ ^ 2 / t := by
      rw [hexp]; ring
    rw [hexp'] at hΘ'
    clear hexp hexp' hd hnear hLc hLc2 hmin
    linarith

/-! ### Eq. (7) -/

theorem t31_posPart_ratio {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {q : ℕ} (obj : X → ℝ) (con : X → E q) (z u : X) (d : E q)
    (hfeas : ∀ j, con z j ≤ 0) (hdir : HasDirDerivAt con z u d)
    (hcrit : criticalCone obj con z u d) :
    Tendsto (fun t : ℝ => ‖posPart (con (z + t • u))‖ / t) (𝓝[>] 0) (𝓝 0) := by
  -- componentwise convergence of the difference quotients
  have hcomp : ∀ j, Tendsto (fun t : ℝ => t⁻¹ * (con (z + t • u) j - con z j)) (𝓝[>] 0)
      (𝓝 (d j)) := by
    intro j
    have := ((PiLp.proj (p := 2) (𝕜 := ℝ) (fun _ : Fin q => ℝ) j).continuous.tendsto d).comp hdir
    simpa [Function.comp_def] using this
  -- each component of `t⁻¹ • posPart (con (z + t u))` tends to `0`
  have hj : ∀ j, Tendsto (fun t : ℝ => t⁻¹ * max (con (z + t • u) j) 0) (𝓝[>] 0) (𝓝 0) := by
    intro j
    rcases (hfeas j).lt_or_eq with hlt | heq
    · -- inactive constraint: eventually negative
      have hcont : Tendsto (fun t : ℝ => con (z + t • u) j) (𝓝[>] 0) (𝓝 (con z j)) := by
        have h1 : Tendsto (fun t : ℝ => t * (t⁻¹ * (con (z + t • u) j - con z j)))
            (𝓝[>] 0) (𝓝 (0 * d j)) :=
          (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).mul (hcomp j)
        have h2 : ∀ᶠ t in 𝓝[>] (0:ℝ), t * (t⁻¹ * (con (z + t • u) j - con z j)) + con z j
            = con (z + t • u) j := by
          filter_upwards [self_mem_nhdsWithin] with t ht
          have : t ≠ 0 := ne_of_gt ht
          field_simp
          ring
        have := h1.add_const (con z j)
        rw [zero_mul, zero_add] at this
        exact this.congr' h2
      have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), con (z + t • u) j < 0 :=
        hcont.eventually (gt_mem_nhds hlt)
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with t ht
      rw [max_eq_right ht.le, mul_zero]
    · -- active constraint
      have hd : d j ≤ 0 := hcrit.1 j heq
      have hlim : Tendsto (fun t : ℝ => max (t⁻¹ * (con (z + t • u) j - con z j)) 0)
          (𝓝[>] 0) (𝓝 (max (d j) 0)) :=
        (hcomp j).max tendsto_const_nhds
      rw [max_eq_right hd] at hlim
      apply hlim.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (0:ℝ) < t := ht
      rw [heq, sub_zero]
      rw [mul_max_of_nonneg _ _ (inv_nonneg.mpr ht'.le), mul_zero]
  -- assemble
  have hvec : Tendsto (fun t : ℝ => t⁻¹ • posPart (con (z + t • u))) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun t : ℝ => WithLp.toLp 2 (fun j => t⁻¹ * max (con (z + t • u) j) 0))
        (𝓝[>] 0) (𝓝 (WithLp.toLp 2 (fun _ : Fin q => (0:ℝ)))) := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin q => ℝ)).continuousAt.tendsto.comp
      exact tendsto_pi_nhds.mpr hj
    convert this using 1
    · funext t
      ext j
      simp only [PiLp.smul_apply, smul_eq_mul]
      rfl
    · congr 1
  have hn := (continuous_norm.tendsto (0 : E q)).comp hvec
  rw [norm_zero] at hn
  apply hn.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0:ℝ) < t := ht
  simp only [Function.comp_apply, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht']
  rw [div_eq_inv_mul]



theorem t31_eq7 {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    {q : ℕ} (obj : X → ℝ) (con : X → E q) (z u : X) (d : E q) (ε δ ρ : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hρ : 0 < ρ)
    (hobj : ContDiffAt ℝ 1 obj z) (hfeas : ∀ j, con z j ≤ 0) (hdir : HasDirDerivAt con z u d)
    (hcrit : criticalCone obj con z u d) (hcalm : IsCalmDirWith obj con z u ε δ ρ) :
    Tendsto (fun t : ℝ => (obj (z + t • u) + ρ * ‖posPart (con (z + t • u))‖ - obj z) / t)
      (𝓝[>] 0) (𝓝 0) := by
  have hpos := t31_posPart_ratio obj con z u d hfeas hdir hcrit
  -- derivative of `obj` along the ray
  have hD : HasFDerivAt obj (fderiv ℝ obj z) z :=
    (hobj.differentiableAt (by norm_num)).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => z + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const u).const_add z
  have hcomp : HasDerivAt (fun t : ℝ => obj (z + t • u)) (fderiv ℝ obj z u) 0 := by
    have hD' : HasFDerivAt obj (fderiv ℝ obj z) (z + (0:ℝ) • u) := by simpa using hD
    have := hD'.comp_hasDerivAt (0:ℝ) hline
    simpa [Function.comp_def] using this
  have hslope : Tendsto (fun t : ℝ => (obj (z + t • u) - obj z) / t) (𝓝[>] 0)
      (𝓝 (fderiv ℝ obj z u)) := by
    have := (hasDerivAt_iff_tendsto_slope.mp hcomp).mono_left
      (nhdsGT_le_nhdsNE (0:ℝ))
    apply this.congr'
    filter_upwards with t
    simp [slope_def_field]
  have hsum : Tendsto (fun t : ℝ => (obj (z + t • u) + ρ * ‖posPart (con (z + t • u))‖ - obj z) / t)
      (𝓝[>] 0) (𝓝 (fderiv ℝ obj z u)) := by
    have := hslope.add (hpos.const_mul ρ)
    rw [mul_zero, add_zero] at this
    apply this.congr'
    filter_upwards with t
    ring
  -- lower bound from calmness
  have hnorm0 : Tendsto (fun t : ℝ => ‖posPart (con (z + t • u))‖) (𝓝[>] 0) (𝓝 0) := by
    have h1 := (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x := 𝓝 (0:ℝ)))).mul hpos
    rw [mul_zero] at h1
    apply h1.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have : t ≠ 0 := ne_of_gt ht
    simp only [id]
    field_simp
  have hsmall : ∀ᶠ t in 𝓝[>] (0:ℝ), ‖posPart (con (z + t • u))‖ < ε :=
    hnorm0.eventually (gt_mem_nhds hε)
  have hsmall2 : ∀ᶠ t in 𝓝[>] (0:ℝ), t * ‖u‖ < ε := by
    have : Tendsto (fun t : ℝ => t * ‖u‖) (𝓝[>] 0) (𝓝 (0 * ‖u‖)) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).mul tendsto_const_nhds
    rw [zero_mul] at this
    exact this.eventually (gt_mem_nhds hε)
  have hge : ∀ᶠ t in 𝓝[>] (0:ℝ),
      0 ≤ (obj (z + t • u) + ρ * ‖posPart (con (z + t • u))‖ - obj z) / t := by
    filter_upwards [hsmall, hsmall2, self_mem_nhdsWithin] with t h1 h2 ht
    have ht' : (0:ℝ) < t := ht
    apply div_nonneg _ ht'.le
    have hmem : (z + t • u) - z ∈ dirNbhd ε δ u := by
      rw [add_sub_cancel_left]
      refine ⟨?_, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht']; exact h2
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht', smul_smul, mul_comm, sub_self,
          norm_zero]
        positivity
    have := hcalm (-posPart (con (z + t • u))) (by rwa [norm_neg]) (z + t • u) hmem (by
      intro j
      show con (z + t • u) j + (-(posPart (con (z + t • u)))) j ≤ 0
      simp only [PiLp.neg_apply]
      show con (z + t • u) j + -(max (con (z + t • u) j) 0) ≤ 0
      have := le_max_left (con (z + t • u) j) 0
      linarith)
    rw [norm_neg] at this
    linarith
  have hle : 0 ≤ fderiv ℝ obj z u := ge_of_tendsto hsum hge
  have hzero : fderiv ℝ obj z u = 0 := le_antisymm hcrit.2 hle
  rw [hzero] at hsum
  exact hsum

/-! ### Theorem 3.1 -/

theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X] {q : ℕ} (obj : X → ℝ) (con : X → E q) (z u : X) (d : E q)
    (hfeas : ∀ j, con z j ≤ 0) (hmin : IsLocalMinOn obj {w | ∀ j, con w j ≤ 0} z)
    (hobj : ContDiffAt ℝ 1 obj z) (hLip : DirLipschitzAt con z u)
    (hdir : HasDirDerivAt con z u d) (hcrit : criticalCone obj con z u d)
    (hcalm : IsCalmDir obj con z u) :
    ∃ l : E q, (∀ j, 0 ≤ l j) ∧ ∑ j, l j * con z j = 0 ∧ ∑ j, l j * d j = 0 ∧
      ∃ ξ ∈ dirSubdiff (fun w => ((∑ j, l j * con w j : ℝ) : EReal)) z u,
        gradient obj z + ξ = 0 := by
  obtain ⟨L, ε₀, δ₀, hL, hε₀, hδ₀, hlip0⟩ := hLip
  obtain ⟨ε, δ, ρ, hε, hδ, hρ, hcw⟩ := hcalm
  have heq7 := t31_eq7 obj con z u d ε δ ρ hε hδ hρ hobj hfeas hdir hcrit hcw
  set δ₁ := min δ δ₀ with hδ₁
  set ε₂ := min (min ε ε₀) (ε / L) with hε₂
  have hδ₁pos : 0 < δ₁ := lt_min hδ hδ₀
  have hε₂pos : 0 < ε₂ := lt_min (lt_min hε hε₀) (by positivity)
  set C := DirKKTBilevel.VP.dirNbhd ε₂ δ₁ u with hCdef
  have hC0 : C ⊆ DirKKTBilevel.VP.dirNbhd ε₀ δ₀ u :=
    t31_dirNbhd_mono u ((min_le_left _ _).trans (min_le_right _ _)) (min_le_right _ _)
  have hCc : C ⊆ DirKKTBilevel.VP.dirNbhd ε δ u :=
    t31_dirNbhd_mono u ((min_le_left _ _).trans (min_le_left _ _)) (min_le_left _ _)
  have hlip : ∀ w w', w - z ∈ C → w' - z ∈ C → ‖con w - con w'‖ ≤ L * ‖w - w'‖ :=
    fun w w' hw hw' => hlip0 w w' (hC0 hw) (hC0 hw')
  have hz0 : z - z ∈ C := by
    rw [sub_self]; exact ⟨by simpa using hε₂pos, by simp⟩
  have hlow : ∀ w, w - z ∈ C → obj z ≤ obj w + ρ * ‖DirKKTBilevel.VP.posPart (con w)‖ := by
    intro w hw
    have hpp : ‖DirKKTBilevel.VP.posPart (con w)‖ < ε := by
      calc ‖DirKKTBilevel.VP.posPart (con w)‖ ≤ ‖con w - con z‖ := t31_posPart_le _ _ hfeas
        _ ≤ L * ‖w - z‖ := hlip w z hw hz0
        _ < L * ε₂ := by gcongr; exact hw.1
        _ ≤ L * (ε / L) := by gcongr; exact min_le_right _ _
        _ = ε := by field_simp
    have := hcw (-DirKKTBilevel.VP.posPart (con w)) (by rwa [norm_neg]) w (hCc hw) (by
      intro j
      simp only [PiLp.neg_apply]
      show con w j + -(max (con w j) 0) ≤ 0
      have := le_max_left (con w j) 0
      linarith)
    rw [norm_neg] at this
    linarith
  have hdiff : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ obj w := by
    filter_upwards [hobj.eventually (by simp)] with w hw
    exact hw.differentiableAt (by norm_num)
  have hgc : ContinuousAt (gradient obj) z := by
    have h1 : ContinuousAt (fderiv ℝ obj) z :=
      (hobj.fderiv_right (m := 0) (by norm_num)).continuousAt
    exact (InnerProductSpace.toDual ℝ X).symm.continuous.continuousAt.comp h1
  -- the approximation steps
  have step := fun k : ℕ => t31_step obj con z u L ε₂ δ₁ ρ hL hε₂pos hδ₁pos hρ hlip hlow heq7
    hdiff hgc (1 / ((k:ℝ) + 1)) (by positivity)
  choose t w ζ η R0 ht htτ hzt hwt hη hζ0 hζc hζρ hR0 hR0C hfr using step
  -- a convergent subsequence of multipliers
  obtain ⟨l, -, ψ, hψ, hlim⟩ := (isCompact_closedBall (0 : E q) ρ).tendsto_subseq
    (x := ζ) (fun k => by simpa using hζρ k)
  have hτψ : Tendsto (fun k : ℕ => 1 / ((ψ k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hψ.tendsto_atTop
  have htψ : Tendsto (fun k => t (ψ k)) atTop (𝓝 0) :=
    squeeze_zero (fun k => (ht (ψ k)).le) (fun k => htτ (ψ k)) hτψ
  have hwC : ∀ k, w k - z ∈ C := fun k => hR0C k (w k) (by simp [(hR0 k).le])
  -- distance of `w` to `z`
  have hwz : ∀ k, ‖w k - z‖ ≤ t k * (1 / ((k:ℝ) + 1)) + t k * ‖u‖ := by
    intro k
    calc ‖w k - z‖ = ‖(w k - (z + t k • u)) + t k • u‖ := by abel_nf
      _ ≤ ‖w k - (z + t k • u)‖ + ‖t k • u‖ := norm_add_le _ _
      _ ≤ t k * (1 / ((k:ℝ) + 1)) + t k * ‖u‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (ht k)]; linarith [hwt k]
  have hwzT : Tendsto (fun k => ‖w (ψ k) - z‖) atTop (𝓝 0) := by
    have : Tendsto (fun k => t (ψ k) * (1 / ((ψ k : ℝ) + 1)) + t (ψ k) * ‖u‖) atTop
        (𝓝 (0 * 0 + 0 * ‖u‖)) := (htψ.mul hτψ).add (htψ.mul tendsto_const_nhds)
    simp only [mul_zero, zero_mul, add_zero] at this
    exact squeeze_zero (fun k => norm_nonneg _) (fun k => hwz (ψ k)) this
  -- components of the multipliers
  have hcomp : ∀ j, Tendsto (fun k => ζ (ψ k) j) atTop (𝓝 (l j)) := fun j =>
    ((PiLp.proj (p := 2) (𝕜 := ℝ) (fun _ : Fin q => ℝ) j).continuous.tendsto l).comp hlim
  have hl0 : ∀ j, 0 ≤ l j := fun j =>
    ge_of_tendsto (hcomp j) (Eventually.of_forall fun k => hζ0 (ψ k) j)
  have hlzero : ∀ j, (∀ᶠ k in atTop, con (w (ψ k)) j < 0) → l j = 0 := by
    intro j hev
    have : ∀ᶠ k in atTop, ζ (ψ k) j = 0 := by
      filter_upwards [hev] with k hk
      exact hζc (ψ k) j hk.le
    exact tendsto_nhds_unique (hcomp j) (tendsto_const_nhds.congr' (this.mono fun k hk => hk.symm))
  have hconw : ∀ j, Tendsto (fun k => con (w (ψ k)) j) atTop (𝓝 (con z j)) := by
    intro j
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ k, ‖con (w (ψ k)) j - con z j‖ ≤ L * ‖w (ψ k) - z‖ := by
      intro k
      calc ‖con (w (ψ k)) j - con z j‖ = ‖(con (w (ψ k)) - con z) j‖ := by simp
        _ ≤ ‖con (w (ψ k)) - con z‖ := PiLp.norm_apply_le _ _
        _ ≤ L * ‖w (ψ k) - z‖ := hlip _ _ (hwC _) hz0
    have := hwzT.const_mul L
    rw [mul_zero] at this
    exact squeeze_zero (fun k => norm_nonneg _) hb this
  -- the slopes along the approximating points
  have hslope : ∀ j, con z j = 0 → Tendsto (fun k => con (w (ψ k)) j / t (ψ k)) atTop
      (𝓝 (d j)) := by
    intro j hj
    have htT : Tendsto (fun k => t (ψ k)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨htψ, Eventually.of_forall fun k => ht (ψ k)⟩
    have h1 : Tendsto (fun k => (t (ψ k))⁻¹ • (con (z + t (ψ k) • u) - con z)) atTop (𝓝 d) :=
      hdir.comp htT
    have h1j : Tendsto (fun k => (con (z + t (ψ k) • u) j - con z j) / t (ψ k)) atTop
        (𝓝 (d j)) := by
      have := ((PiLp.proj (p := 2) (𝕜 := ℝ) (fun _ : Fin q => ℝ) j).continuous.tendsto d).comp h1
      refine this.congr fun k => ?_
      simp [div_eq_inv_mul]
    have h2 : Tendsto (fun k => (con (w (ψ k)) j - con (z + t (ψ k) • u) j) / t (ψ k)) atTop
        (𝓝 0) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simp only [sub_zero]
      have hb : ∀ k, ‖(con (w (ψ k)) j - con (z + t (ψ k) • u) j) / t (ψ k)‖ ≤
          L * (1 / ((ψ k : ℝ) + 1)) := by
        intro k
        rw [norm_div, Real.norm_eq_abs (t (ψ k)), abs_of_pos (ht (ψ k)),
          div_le_iff₀ (ht (ψ k))]
        calc ‖con (w (ψ k)) j - con (z + t (ψ k) • u) j‖
            = ‖(con (w (ψ k)) - con (z + t (ψ k) • u)) j‖ := by simp
          _ ≤ ‖con (w (ψ k)) - con (z + t (ψ k) • u)‖ := PiLp.norm_apply_le _ _
          _ ≤ L * ‖w (ψ k) - (z + t (ψ k) • u)‖ := hlip _ _ (hwC _) (hzt _)
          _ ≤ L * (t (ψ k) * (1 / ((ψ k : ℝ) + 1))) := by gcongr; exact hwt _
          _ = L * (1 / ((ψ k : ℝ) + 1)) * t (ψ k) := by ring
      have := hτψ.const_mul L
      rw [mul_zero] at this
      exact squeeze_zero (fun k => norm_nonneg _) hb this
    have := h1j.add h2
    rw [add_zero] at this
    refine this.congr fun k => ?_
    rw [hj]
    field_simp
    ring
  have hlvanish : ∀ j, (con z j < 0 ∨ (con z j = 0 ∧ d j < 0)) → l j = 0 := by
    intro j hj
    apply hlzero j
    rcases hj with hlt | ⟨heq, hd⟩
    · exact (hconw j).eventually (gt_mem_nhds hlt)
    · filter_upwards [(hslope j heq).eventually (gt_mem_nhds hd)] with k hk
      have := ht (ψ k)
      by_contra hc
      push_neg at hc
      have : 0 ≤ con (w (ψ k)) j / t (ψ k) := div_nonneg hc this.le
      linarith
  have hterm : ∀ j, l j * con z j = 0 ∧ l j * d j = 0 := by
    intro j
    rcases (hfeas j).lt_or_eq with hlt | heq
    · have := hlvanish j (Or.inl hlt); simp [this]
    · refine ⟨by rw [heq, mul_zero], ?_⟩
      rcases (hcrit.1 j heq).lt_or_eq with hd | hd
      · have := hlvanish j (Or.inr ⟨heq, hd⟩); simp [this]
      · rw [hd, mul_zero]
  refine ⟨l, hl0, Finset.sum_eq_zero fun j _ => (hterm j).1,
    Finset.sum_eq_zero fun j _ => (hterm j).2, -gradient obj z, ?_, by abel⟩
  -- the limiting multiplier function
  set A : X → ℝ := fun w' => ∑ j, l j * con w' j with hA
  have hAlip : ∀ a b, a - z ∈ C → b - z ∈ C → |A a - A b| ≤ ‖l‖ * L * ‖a - b‖ := by
    intro a b ha hb
    have : A a - A b = ∑ j, l j * (con a - con b) j := by
      rw [hA]; simp only; rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j _; simp; ring
    rw [this, mul_assoc]
    exact (t31_abs_sum_le l (con a - con b)).trans
      (mul_le_mul_of_nonneg_left (hlip a b ha hb) (norm_nonneg _))
  -- perturbed points with exact regular subgradients of `A`
  have pert : ∀ k : ℕ, ∃ (p : X) (η' : X), ‖p - w (ψ k)‖ ≤ t (ψ k) * (1 / ((ψ k : ℝ) + 1)) ∧
      ‖η' - η (ψ k)‖ ≤ 2 * (1 / ((k:ℝ) + 1) + ‖l - ζ (ψ k)‖ * L) ∧ p - z ∈ C ∧
      IsRegularSubgrad (fun w' => ((A w' : ℝ) : EReal)) p η' := by
    intro k
    set K := ψ k
    obtain ⟨r1, hr1, hr1p⟩ := Metric.eventually_nhds_iff.mp
      (hfr K (1 / ((k:ℝ) + 1)) (by positivity))
    set R : ℝ := min (r1 / 2) (min (R0 K) (2 * (t K * (1 / ((K:ℝ) + 1))))) with hR
    have hRpos : 0 < R := lt_min (by positivity) (lt_min (hR0 K) (by
      have := ht K; positivity))
    have hRC : ∀ w' ∈ Metric.closedBall (w K) R, w' - z ∈ C := by
      intro w' hw'
      rw [Metric.mem_closedBall, dist_eq_norm] at hw'
      exact hR0C K w' (hw'.trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hAc : ContinuousOn A (Metric.closedBall (w K) R) := by
      have : LipschitzOnWith (Real.toNNReal (‖l‖ * L)) A (Metric.closedBall (w K) R) := by
        apply LipschitzOnWith.of_dist_le_mul
        intro a ha b hb
        rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, dist_eq_norm]
        exact hAlip a b (hRC a ha) (hRC b hb)
      exact this.continuousOn
    have hineq : ∀ w' ∈ Metric.closedBall (w K) R,
        A (w K) - (1 / ((k:ℝ) + 1) + ‖l - ζ K‖ * L) * ‖w' - w K‖ ≤
          A w' - inner ℝ (η K) (w' - w K) := by
      intro w' hw'
      have hw'C := hRC w' hw'
      rw [Metric.mem_closedBall, dist_eq_norm] at hw'
      have hlt : dist w' (w K) < r1 := by
        rw [dist_eq_norm]
        calc ‖w' - w K‖ ≤ R := hw'
          _ ≤ r1 / 2 := min_le_left _ _
          _ < r1 := by linarith
      have h1 := hr1p hlt
      have hdec : A w' - A (w K) = (∑ j, ζ K j * con w' j - ∑ j, ζ K j * con (w K) j) +
          ∑ j, (l - ζ K) j * (con w' - con (w K)) j := by
        rw [hA]; simp only
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j _; simp; ring
      have h2 := t31_abs_sum_le (l - ζ K) (con w' - con (w K))
      have h3 : ‖con w' - con (w K)‖ ≤ L * ‖w' - w K‖ := hlip w' (w K) hw'C (hwC K)
      have h4 : ‖l - ζ K‖ * ‖con w' - con (w K)‖ ≤ ‖l - ζ K‖ * L * ‖w' - w K‖ := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      have h5 := (abs_le.mp (h2.trans h4)).1
      nlinarith
    obtain ⟨p, η', hp, hη', hreg⟩ := t31_perturb A (w K) (η K) R
      (1 / ((k:ℝ) + 1) + ‖l - ζ K‖ * L) hRpos (by positivity) hAc hineq
    refine ⟨p, η', ?_, hη', hRC p ?_, hreg⟩
    · calc ‖p - w K‖ ≤ R / 2 := hp
        _ ≤ (2 * (t K * (1 / ((K:ℝ) + 1)))) / 2 := by
            gcongr; exact (min_le_right _ _).trans (min_le_right _ _)
        _ = t K * (1 / ((K:ℝ) + 1)) := by ring
    · rw [Metric.mem_closedBall, dist_eq_norm]; linarith
  choose p η' hp hη' hpC hreg using pert
  -- assemble the directional limiting subgradient
  have htk : ∀ k, 0 < t (ψ k) := fun k => ht (ψ k)
  refine ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _, fun k => t (ψ k),
    fun k => (t (ψ k))⁻¹ • (p k - z), η', htk, htψ, ?_, ?_, ?_, fun k => ?_⟩
  · -- directions converge
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ k, ‖(t (ψ k))⁻¹ • (p k - z) - u‖ ≤ 2 * (1 / ((ψ k : ℝ) + 1)) := by
      intro k
      have e : (t (ψ k))⁻¹ • (p k - z) - u =
          (t (ψ k))⁻¹ • ((p k - w (ψ k)) + (w (ψ k) - (z + t (ψ k) • u))) := by
        rw [smul_add, smul_sub, smul_sub, smul_sub, smul_add, smul_smul,
          inv_mul_cancel₀ (htk k).ne', one_smul]; abel
      rw [e, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (htk k), inv_mul_le_iff₀ (htk k)]
      calc ‖(p k - w (ψ k)) + (w (ψ k) - (z + t (ψ k) • u))‖
          ≤ ‖p k - w (ψ k)‖ + ‖w (ψ k) - (z + t (ψ k) • u)‖ := norm_add_le _ _
        _ ≤ t (ψ k) * (1 / ((ψ k : ℝ) + 1)) + t (ψ k) * (1 / ((ψ k : ℝ) + 1)) :=
            add_le_add (hp k) (hwt _)
        _ = t (ψ k) * (2 * (1 / ((ψ k : ℝ) + 1))) := by ring
    have := hτψ.const_mul 2
    rw [mul_zero] at this
    exact squeeze_zero (fun k => norm_nonneg _) hb this
  · -- subgradients converge
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ k, ‖η' k - -gradient obj z‖ ≤
        2 * (1 / ((k:ℝ) + 1) + ‖l - ζ (ψ k)‖ * L) + 1 / ((ψ k : ℝ) + 1) := by
      intro k
      have e : η' k - -gradient obj z = (η' k - η (ψ k)) + (η (ψ k) + gradient obj z) := by abel
      rw [e]
      exact (norm_add_le _ _).trans (add_le_add (hη' k) (hη _))
    have hlz : Tendsto (fun k => ‖l - ζ (ψ k)‖) atTop (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.mp hlim)
      refine this.congr fun k => ?_
      rw [norm_sub_rev]; rfl
    have : Tendsto (fun k : ℕ => 2 * (1 / ((k:ℝ) + 1) + ‖l - ζ (ψ k)‖ * L) +
        1 / ((ψ k : ℝ) + 1)) atTop (𝓝 (2 * (0 + 0 * L) + 0)) :=
      ((tendsto_one_div_add_atTop_nhds_zero_nat.add (hlz.mul_const L)).const_mul 2).add hτψ
    simp only [zero_mul, add_zero, mul_zero] at this
    exact squeeze_zero (fun k => norm_nonneg _) hb this
  · -- values converge
    have hpz : ∀ k, z + t (ψ k) • ((t (ψ k))⁻¹ • (p k - z)) = p k := by
      intro k; rw [smul_smul, mul_inv_cancel₀ (htk k).ne', one_smul, add_sub_cancel]
    have hAT : Tendsto (fun k => A (p k)) atTop (𝓝 (A z)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hb : ∀ k, ‖A (p k) - A z‖ ≤ ‖l‖ * L * (2 * (t (ψ k) * (1 / ((ψ k : ℝ) + 1))) +
          t (ψ k) * ‖u‖) := by
        intro k
        rw [Real.norm_eq_abs]
        refine (hAlip _ _ (hpC k) hz0).trans ?_
        gcongr
        calc ‖p k - z‖ = ‖(p k - w (ψ k)) + (w (ψ k) - z)‖ := by abel_nf
          _ ≤ ‖p k - w (ψ k)‖ + ‖w (ψ k) - z‖ := norm_add_le _ _
          _ ≤ _ := by linarith [hp k, hwz (ψ k)]
      have : Tendsto (fun k => ‖l‖ * L * (2 * (t (ψ k) * (1 / ((ψ k : ℝ) + 1))) +
          t (ψ k) * ‖u‖)) atTop (𝓝 (‖l‖ * L * (2 * (0 * 0) + 0 * ‖u‖))) :=
        (((htψ.mul hτψ).const_mul 2).add (htψ.mul_const ‖u‖)).const_mul _
      simp only [mul_zero, zero_mul, add_zero] at this
      exact squeeze_zero (fun k => norm_nonneg _) hb this
    have := (continuous_coe_real_ereal.tendsto _).comp hAT
    refine this.congr fun k => ?_
    simp only [Function.comp_apply]
    rw [hpz k]
  · have hpz : z + t (ψ k) • ((t (ψ k))⁻¹ • (p k - z)) = p k := by
      rw [smul_smul, mul_inv_cancel₀ (htk k).ne', one_smul, add_sub_cancel]
    rw [hpz]
    exact hreg k
