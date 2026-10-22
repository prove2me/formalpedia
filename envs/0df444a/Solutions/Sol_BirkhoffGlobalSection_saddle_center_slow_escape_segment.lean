-- Prove2me | solution 1 for BirkhoffGlobalSection.saddle_center_slow_escape_segment
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-04T22:22:51.32853+00:00
-- url     : https://prove2.me/submissions/3a0b716e-3a99-4657-a0a2-8da22e3ba0fe

import Mathlib
import Definitions.Def_BirkhoffGlobalSection
import Definitions.Def_BirkhoffGlobalSection_DynamicalConvexity
import Definitions.Def_BirkhoffGlobalSection_TangentialHessian
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_leviCivita_explicit_derivatives
import Theorems.Thm_BirkhoffGlobalSection_first_critical_value_near_half

/-! Slow escape near the saddle-centers `s± = (±1/2, 0, 0, 0)`.

At `(μ, c) = (1/2, 2)` both points are equilibria of the Levi-Civita field. The field is
differentiable in `(μ, c, y)` there, so its speed is at most `C (‖y - s‖ + |μ - 1/2| + |c - 2|)`.
A Gronwall fence then keeps a trajectory starting within `r` of `s` inside the ball of radius
`r e^{2CL} < R` for time `L`, provided `|μ - 1/2| + |c - 2| < r`. The lower bound on `c` comes from
the first critical value near `-2`. -/

namespace BirkhoffGlobalSection.SlowEscape

open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian Filter Topology

/-- The Levi-Civita vector field, written with the explicit gradient. -/
noncomputable def vfield (q : ℝ × ℝ × Phase) : Phase :=
  ![kGradR q.1 q.2.1 (rD q.2.2) q.2.2 2, kGradR q.1 q.2.1 (rD q.2.2) q.2.2 3,
    -kGradR q.1 q.2.1 (rD q.2.2) q.2.2 0, -kGradR q.1 q.2.1 (rD q.2.2) q.2.2 1]

theorem hvf_eq (μ c : ℝ) {y : Phase} (hy : y ∈ U) :
    hamiltonianVectorField (leviCivitaHamiltonian μ c) y = vfield (μ, c, y) := by
  have h := (leviCivita_explicit_derivatives μ c).1 y hy
  simp only [hamiltonianVectorField, vfield, h, kGrad]

theorem isOpen_U' : IsOpen U :=
  isOpen_lt continuous_const (by unfold secondCollisionDistanceSq; fun_prop)

theorem differentiableAt_rD {y : Phase} (hy : y ∈ U) : DifferentiableAt ℝ rD y := by
  unfold rD
  refine DifferentiableAt.sqrt ?_ (show (0 : ℝ) < secondCollisionDistanceSq y from hy).ne'
  unfold secondCollisionDistanceSq; fun_prop

theorem differentiableAt_kGradR' (i : Fin 4) {p : ℝ × ℝ × ℝ × Phase} (hp : p.2.2.1 ≠ 0) :
    DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ × Phase => kGradR p.1 p.2.1 p.2.2.1 p.2.2.2 i) p := by
  have h3 : p.2.2.1 ^ 3 ≠ 0 := pow_ne_zero 3 hp
  fin_cases i <;>
    simp only [kGradR, dP, dZ, dD, zNormSq, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons] <;>
    fun_prop (disch := first | assumption | exact mul_ne_zero two_ne_zero h3)

theorem differentiableAt_vfield {q : ℝ × ℝ × Phase} (hq : q.2.2 ∈ U) :
    DifferentiableAt ℝ vfield q := by
  have hr : DifferentiableAt ℝ (fun q : ℝ × ℝ × Phase => (q.1, q.2.1, rD q.2.2, q.2.2)) q :=
    by
      have := (differentiableAt_rD hq).comp q
        (differentiableAt_snd.comp q differentiableAt_snd :
          DifferentiableAt ℝ (fun q : ℝ × ℝ × Phase => q.2.2) q)
      fun_prop
  have hr0 : rD q.2.2 ≠ 0 := (Real.sqrt_pos.mpr hq).ne'
  have hK : ∀ i : Fin 4, DifferentiableAt ℝ
      (fun q : ℝ × ℝ × Phase => kGradR q.1 q.2.1 (rD q.2.2) q.2.2 i) q := fun i => by
    have := DifferentiableAt.comp
      (g := fun p : ℝ × ℝ × ℝ × Phase => kGradR p.1 p.2.1 p.2.2.1 p.2.2.2 i) q
      (differentiableAt_kGradR' i (p := (q.1, q.2.1, rD q.2.2, q.2.2)) hr0) hr
    exact this
  rw [differentiableAt_pi]
  intro i
  fin_cases i
  · exact hK 2
  · exact hK 3
  · exact (hK 0).neg
  · exact (hK 1).neg

theorem rD_half {s : Phase} (h : secondCollisionDistanceSq s = 1 / 4) : rD s = 1 / 2 := by
  rw [rD, h, show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem D_sP : secondCollisionDistanceSq (![1 / 2, 0, 0, 0] : Phase) = 1 / 4 := by
  simp [secondCollisionDistanceSq]; norm_num

theorem D_sM : secondCollisionDistanceSq (![-(1 / 2), 0, 0, 0] : Phase) = 1 / 4 := by
  simp [secondCollisionDistanceSq]; norm_num

theorem sP_mem : (![1 / 2, 0, 0, 0] : Phase) ∈ U := by
  show (0 : ℝ) < _; rw [D_sP]; norm_num

theorem sM_mem : (![-(1 / 2), 0, 0, 0] : Phase) ∈ U := by
  show (0 : ℝ) < _; rw [D_sM]; norm_num

theorem vfield_sP : vfield (1 / 2, 2, ![1 / 2, 0, 0, 0]) = 0 := by
  funext i
  fin_cases i <;> simp [vfield, kGradR, dP, dZ, dD, zNormSq] <;>
    (try rw [rD_half (by simp [secondCollisionDistanceSq]; norm_num)]) <;> norm_num

theorem vfield_sM : vfield (1 / 2, 2, ![-(1 / 2), 0, 0, 0]) = 0 := by
  funext i
  fin_cases i <;> simp [vfield, kGradR, dP, dZ, dD, zNormSq] <;>
    (try rw [rD_half (by simp [secondCollisionDistanceSq]; norm_num)]) <;> norm_num

/-- Linear speed bound near an equilibrium of the `(1/2, 2)` field. -/
theorem lin_bound (s : Phase) (hs : s ∈ U) (h0 : vfield (1 / 2, 2, s) = 0) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ (μ c : ℝ) (y : Phase),
      |μ - 1 / 2| < δ → |c - 2| < δ → ‖y - s‖ < δ →
        y ∈ U ∧ ‖vfield (μ, c, y)‖ ≤ C * (‖y - s‖ + |μ - 1 / 2| + |c - 2|) := by
  have hd := differentiableAt_vfield (q := ((1 / 2 : ℝ), (2 : ℝ), s)) hs
  obtain ⟨C0, hC0⟩ := hd.isBigO_sub.bound
  have hU : ∀ᶠ q in 𝓝 ((1 / 2 : ℝ), (2 : ℝ), s), q.2.2 ∈ U :=
    (continuous_snd.comp continuous_snd).continuousAt.preimage_mem_nhds (isOpen_U'.mem_nhds hs)
  obtain ⟨δ, hδ, hall⟩ := Metric.eventually_nhds_iff.mp (hC0.and hU)
  refine ⟨max C0 1, δ, lt_of_lt_of_le one_pos (le_max_right _ _), hδ,
    fun μ c y hμ hc hy => ?_⟩
  have hdist : dist (μ, c, y) ((1 / 2 : ℝ), (2 : ℝ), s) < δ := by
    rw [Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq, dist_eq_norm]
    exact max_lt hμ (max_lt hc hy)
  obtain ⟨hb, hyU⟩ := hall hdist
  refine ⟨hyU, ?_⟩
  rw [h0, sub_zero] at hb
  have hn : ‖(μ, c, y) - ((1 / 2 : ℝ), (2 : ℝ), s)‖ ≤ ‖y - s‖ + |μ - 1 / 2| + |c - 2| := by
    rw [Prod.norm_def, Prod.norm_def]
    simp only [Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs]
    have h1 := norm_nonneg (y - s)
    have h2 := abs_nonneg (μ - 1 / 2)
    have h3 := abs_nonneg (c - 2)
    exact max_le (by linarith) (max_le (by linarith) (by linarith))
  have hn0 := norm_nonneg ((μ, c, y) - ((1 / 2 : ℝ), (2 : ℝ), s))
  calc ‖vfield (μ, c, y)‖ ≤ C0 * ‖(μ, c, y) - ((1 / 2 : ℝ), (2 : ℝ), s)‖ := hb
    _ ≤ max C0 1 * ‖(μ, c, y) - ((1 / 2 : ℝ), (2 : ℝ), s)‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hn0
    _ ≤ max C0 1 * (‖y - s‖ + |μ - 1 / 2| + |c - 2|) :=
        mul_le_mul_of_nonneg_left hn (le_trans zero_le_one (le_max_right _ _))

/-- Gronwall fence: a trajectory with speed `≤ C (‖x - s‖ + p)` inside the ball of radius `R`,
starting within `r > p` of `s`, stays in that ball for time `L` when `r e^{2CL} < R`. -/
theorem stay_in_ball {x v : ℝ → Phase} (hx : ∀ t, HasDerivAt x (v t) t) (s : Phase)
    {C R r p : ℝ} (hC : 0 < C) (hp0 : 0 ≤ p) (hp : p < r)
    (hv : ∀ t, ‖x t - s‖ < R → ‖v t‖ ≤ C * (‖x t - s‖ + p))
    {t0 L : ℝ} (hrR : r * Real.exp (2 * C * L) < R) (h0 : ‖x t0 - s‖ < r) :
    ∀ t ∈ Set.Icc t0 (t0 + L), ‖x t - s‖ < R := by
  have hr0 : 0 < r := lt_of_le_of_lt hp0 hp
  have key : ∀ t ∈ Set.Icc t0 (t0 + L), ‖x t - s‖ ≤ r * Real.exp (2 * C * (t - t0)) := by
    refine image_norm_le_of_norm_deriv_right_lt_deriv_boundary (f := fun t => x t - s) (f' := v)
      (B := fun t => r * Real.exp (2 * C * (t - t0)))
      (B' := fun t => 2 * C * (r * Real.exp (2 * C * (t - t0)))) ?_ ?_ ?_ ?_ ?_
    · exact fun t _ => ((hx t).sub_const s).continuousAt.continuousWithinAt
    · exact fun t _ => ((hx t).sub_const s).hasDerivWithinAt
    · show ‖x t0 - s‖ ≤ r * Real.exp (2 * C * (t0 - t0))
      rw [sub_self, mul_zero, Real.exp_zero, mul_one]; exact h0.le
    · intro t
      exact ((((hasDerivAt_id t).sub_const t0).const_mul (2 * C)).exp.const_mul r).congr_deriv
        (by simp only [id, mul_one]; ring)
    · intro t ht heq
      have hle : 2 * C * (t - t0) ≤ 2 * C * L := by
        have := ht.2; have := ht.1; nlinarith
      have hB : r * Real.exp (2 * C * (t - t0)) < R :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hle) hr0.le) hrR
      have hb := hv t (heq ▸ hB)
      rw [heq] at hb
      have hr1 : r ≤ r * Real.exp (2 * C * (t - t0)) :=
        le_mul_of_one_le_right hr0.le (Real.one_le_exp (by have := ht.1; nlinarith))
      have hpB : C * p < C * (r * Real.exp (2 * C * (t - t0))) :=
        mul_lt_mul_of_pos_left (lt_of_lt_of_le hp hr1) hC
      linarith
  intro t ht
  have hle : 2 * C * (t - t0) ≤ 2 * C * L := by
    have := ht.2; nlinarith
  calc ‖x t - s‖ ≤ r * Real.exp (2 * C * (t - t0)) := key t ht
    _ ≤ r * Real.exp (2 * C * L) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hle) hr0.le
    _ < R := hrR

end BirkhoffGlobalSection.SlowEscape

open BirkhoffGlobalSection BirkhoffGlobalSection.SlowEscape in
theorem solution (U : Set Phase) (hU : IsOpen U)
    (hplus : (![1 / 2, 0, 0, 0] : Phase) ∈ U)
    (hminus : (![-(1 / 2), 0, 0, 0] : Phase) ∈ U)
    (L : ℝ) (hL : 0 < L) :
    ∃ V : Set Phase, IsOpen V ∧ V ⊆ U ∧
      (![1 / 2, 0, 0, 0] : Phase) ∈ V ∧ (![-(1 / 2), 0, 0, 0] : Phase) ∈ V ∧
      ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
        ∀ μ c : ℝ, 0 < μ → μ < 1 →
          |μ - 1 / 2| < ε → c < 2 + η → belowFirstCriticalValue μ c →
          ∀ (x : ℝ → Phase) (T : ℝ),
            IsPeriodicHamiltonianSolutionIn (leviCivitaHamiltonian μ c)
              (leftEnergyComponent μ c) x T →
            (∃ t : ℝ, x t ∈ V) →
            ∃ a : ℝ, ∀ t ∈ Set.Icc a (a + L), x t ∈ U := by
  obtain ⟨C1, δ1, hC1, hδ1, hb1⟩ := lin_bound _ sP_mem vfield_sP
  obtain ⟨C2, δ2, hC2, hδ2, hb2⟩ := lin_bound _ sM_mem vfield_sM
  obtain ⟨R1, hR1, hball1⟩ := Metric.isOpen_iff.mp hU _ hplus
  obtain ⟨R2, hR2, hball2⟩ := Metric.isOpen_iff.mp hU _ hminus
  set C := max C1 C2 with hCdef
  have hC : 0 < C := lt_of_lt_of_le hC1 (le_max_left _ _)
  set R := min (min R1 R2) (min δ1 δ2) with hRdef
  have hR : 0 < R := lt_min (lt_min hR1 hR2) (lt_min hδ1 hδ2)
  have hRR1 : R ≤ R1 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hRR2 : R ≤ R2 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hRδ1 : R ≤ δ1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hRδ2 : R ≤ δ2 := le_trans (min_le_right _ _) (min_le_right _ _)
  set r := R / 2 * Real.exp (-(2 * C * L)) with hrdef
  have hr : 0 < r := by positivity
  have hrR : r * Real.exp (2 * C * L) < R := by
    rw [hrdef, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero]; linarith
  have hrhalf : r ≤ R / 2 := by
    rw [hrdef]
    exact mul_le_of_le_one_right (by positivity)
      (Real.exp_le_one_iff.2 (by have := mul_pos (mul_pos two_pos hC) hL; linarith))
  obtain ⟨ε0, hε0, hcrit⟩ := first_critical_value_near_half (r / 4) (by positivity)
  have hrsub1 : Metric.ball (![1 / 2, 0, 0, 0] : Phase) r ⊆ U :=
    (Metric.ball_subset_ball (by linarith)).trans hball1
  have hrsub2 : Metric.ball (![-(1 / 2), 0, 0, 0] : Phase) r ⊆ U :=
    (Metric.ball_subset_ball (by linarith)).trans hball2
  refine ⟨Metric.ball (![1 / 2, 0, 0, 0] : Phase) r ∪ Metric.ball (![-(1 / 2), 0, 0, 0] : Phase) r,
    Metric.isOpen_ball.union Metric.isOpen_ball, Set.union_subset hrsub1 hrsub2,
    Or.inl (Metric.mem_ball_self hr), Or.inr (Metric.mem_ball_self hr),
    min ε0 (r / 4), r / 4, lt_min hε0 (by positivity), by positivity, ?_⟩
  intro μ c h0 h1 hμ hc hsub x T hper ⟨t0, ht0⟩
  have hfc := hcrit μ h0 h1 (lt_of_lt_of_le hμ (min_le_left _ _))
  have hsub' : -c < firstCriticalValue μ := hsub
  have hcl : |c - 2| < r / 4 := abs_lt.2 ⟨by linarith, by linarith⟩
  have hμl : |μ - 1 / 2| < r / 4 := lt_of_lt_of_le hμ (min_le_right _ _)
  have hp0 : 0 ≤ |μ - 1 / 2| + |c - 2| := by positivity
  have hp : |μ - 1 / 2| + |c - 2| < r := by linarith
  have hder := hper.2.2.1
  refine ⟨t0, ?_⟩
  rcases ht0 with h | h
  · have hstay := stay_in_ball hder _ hC hp0 hp (R := R) (L := L)
      (fun t ht => by
        obtain ⟨hyU, hbd⟩ := hb1 μ c (x t) (by linarith) (by linarith) (by linarith)
        rw [hvf_eq μ c hyU]
        calc ‖vfield (μ, c, x t)‖ ≤ C1 * (‖x t - ![1 / 2, 0, 0, 0]‖ + |μ - 1 / 2| + |c - 2|) := hbd
          _ ≤ C * (‖x t - ![1 / 2, 0, 0, 0]‖ + (|μ - 1 / 2| + |c - 2|)) := by
            rw [← add_assoc]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      hrR (by rwa [Metric.mem_ball, dist_eq_norm] at h)
    intro t ht
    apply hball1
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_lt_of_le (hstay t ht) hRR1
  · have hstay := stay_in_ball hder _ hC hp0 hp (R := R) (L := L)
      (fun t ht => by
        obtain ⟨hyU, hbd⟩ := hb2 μ c (x t) (by linarith) (by linarith) (by linarith)
        rw [hvf_eq μ c hyU]
        calc ‖vfield (μ, c, x t)‖ ≤ C2 * (‖x t - ![-(1 / 2), 0, 0, 0]‖ + |μ - 1 / 2| + |c - 2|) := hbd
          _ ≤ C * (‖x t - ![-(1 / 2), 0, 0, 0]‖ + (|μ - 1 / 2| + |c - 2|)) := by
            rw [← add_assoc]
            exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
      hrR (by rwa [Metric.mem_ball, dist_eq_norm] at h)
    intro t ht
    apply hball2
    rw [Metric.mem_ball, dist_eq_norm]
    exact lt_of_lt_of_le (hstay t ht) hRR2
