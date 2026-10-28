-- Prove2me | solution 1 for DynMomentum.ShortHorizon.proposition_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-26T08:34:48.796918+00:00
-- url     : https://prove2.me/submissions/a1a63db5-b3a8-4bf1-ad54-cfe4dfd94f63

import Mathlib
import Definitions.Def_DynMomentum_ShortHorizon_Model

set_option autoImplicit false

namespace DM33

open DynMomentum.ShortHorizon Set

noncomputable def hh (P : Params) : ℝ := P.α / (Real.sqrt P.γ * P.τ)
noncomputable def Pe (P : Params) (w : ℝ) : ℝ := Real.exp (hh P * w)
noncomputable def Qe (P : Params) (T w : ℝ) : ℝ := Real.exp (hh P * (T - w))

/-- closed form of `A₁`. -/
noncomputable def yA (P : Params) (T : ℝ) (u : ℝ) : ℝ :=
  P.α * (P.γ - 1) * (1 - Qe P T u ^ 2) /
    (P.γ * P.σ ^ 2 * P.τ * ((Real.sqrt P.γ - 1) * Qe P T u ^ 2 + (Real.sqrt P.γ + 1)))

lemma expo_eq (P : Params) (T u : ℝ) : P.expo T u = Qe P T u ^ 2 := by
  unfold Params.expo Qe hh
  rw [sq, ← Real.exp_add]; congr 1; ring

lemma D_eq (P : Params) (T u : ℝ) :
    P.D T u = (Real.sqrt P.γ - 1) * Qe P T u ^ 2 + (Real.sqrt P.γ + 1) := by
  unfold Params.D; rw [expo_eq]

lemma PQ (P : Params) (T w : ℝ) : Pe P w * Qe P T w = Pe P T := by
  unfold Pe Qe; rw [← Real.exp_add]; congr 1; ring

lemma hasDerivAt_Pe (P : Params) (w : ℝ) : HasDerivAt (Pe P) (hh P * Pe P w) w := by
  have h1 : HasDerivAt (fun x => hh P * x) (hh P) w := by
    simpa using (hasDerivAt_id w).const_mul (hh P)
  have := h1.exp
  unfold Pe; convert this using 1; ring

lemma hasDerivAt_Qe (P : Params) (T w : ℝ) :
    HasDerivAt (Qe P T) (-(hh P) * Qe P T w) w := by
  have h1 : HasDerivAt (fun x => hh P * (T - x)) (-(hh P)) w := by
    simpa using ((hasDerivAt_id w).const_sub T).const_mul (hh P)
  have := h1.exp
  unfold Qe; convert this using 1; ring

lemma sqrt_facts (P : Params) (hP : P.Standing) :
    0 < Real.sqrt P.γ ∧ P.γ = Real.sqrt P.γ ^ 2 := by
  obtain ⟨_, _, _, _, hγ⟩ := hP
  exact ⟨Real.sqrt_pos.2 hγ, (Real.sq_sqrt hγ.le).symm⟩

lemma D_pos (P : Params) (hP : P.Standing) (T : ℝ) (hD : 0 < P.D T 0) :
    ∀ u ∈ Icc (0 : ℝ) T, 0 < P.D T u := by
  intro u hu
  obtain ⟨hα, _, _, hτ, _⟩ := hP
  have hq := (sqrt_facts P ⟨hα, ‹_›, ‹_›, hτ, ‹_›⟩).1
  have hle : P.expo T u ≤ P.expo T 0 := by
    unfold Params.expo
    apply Real.exp_le_exp.2
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith [hu.1]
  have hpos : 0 ≤ P.expo T u := (Real.exp_pos _).le
  unfold Params.D at hD ⊢
  by_cases h1 : 1 ≤ Real.sqrt P.γ
  · nlinarith
  · nlinarith

lemma yA_deriv (P : Params) (hP : P.Standing) (T u : ℝ) (hDu : P.D T u ≠ 0) :
    HasDerivAt (yA P T) (rhs1 P (yA P T u)) u := by
  obtain ⟨hα, hα1, hσ, hτ, hγ0⟩ := hP
  obtain ⟨hq, hγ⟩ := sqrt_facts P ⟨hα, hα1, hσ, hτ, hγ0⟩
  have hQ := hasDerivAt_Qe P T u
  rw [D_eq] at hDu
  have hden : P.γ * P.σ ^ 2 * P.τ * ((Real.sqrt P.γ - 1) * Qe P T u ^ 2 + (Real.sqrt P.γ + 1)) ≠ 0 := by
    have : P.γ * P.σ ^ 2 * P.τ ≠ 0 := by positivity
    exact mul_ne_zero this hDu
  have := (((hQ.pow 2).const_sub 1).const_mul (P.α * (P.γ - 1))).div
    ((((hQ.pow 2).const_mul (Real.sqrt P.γ - 1)).add_const (Real.sqrt P.γ + 1)).const_mul
      (P.γ * P.σ ^ 2 * P.τ)) hden
  refine this.congr_deriv ?_
  unfold rhs1 yA hh
  simp only [Pi.pow_apply]
  generalize Qe P T u = Qv at hden hDu ⊢
  generalize Real.sqrt P.γ = q at hq hγ hden hDu ⊢
  rw [hγ]
  have hq0 : q ≠ 0 := hq.ne'
  have hσ0 : P.σ ≠ 0 := hσ.ne'
  have hτ0 : P.τ ≠ 0 := hτ.ne'
  generalize hDv : (q - 1) * Qv ^ 2 + (q + 1) = Dv at hDu ⊢
  field_simp
  subst hDv
  ring

lemma A1_eq (P : Params) (hP : P.Standing) (T : ℝ) (hD : 0 < P.D T 0)
    (s : ℝ → ℝ) (A1 A2 : ℝ → ℝ) (hA : SolvesA9 P T s A1 A2) :
    ∀ u ∈ Icc (0 : ℝ) T, A1 u = yA P T u := by
  have hDp := D_pos P hP T hD
  have hy' : ∀ u ∈ Icc (0 : ℝ) T, HasDerivAt (yA P T) (rhs1 P (yA P T u)) u :=
    fun u hu => yA_deriv P hP T u (hDp u hu).ne'
  have hcA : ContinuousOn A1 (Icc 0 T) := fun u hu => (hA.1 u hu).continuousWithinAt
  have hcy : ContinuousOn (yA P T) (Icc 0 T) :=
    fun u hu => (hy' u hu).continuousAt.continuousWithinAt
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn hcA
  obtain ⟨C2, hC2⟩ := isCompact_Icc.exists_bound_of_continuousOn hcy
  set R := max C1 C2 with hR
  have hmem : ∀ t ∈ Ioc (0 : ℝ) T, Icc (0 : ℝ) T ∈ nhdsWithin t (Iic t) := fun t ht =>
    Filter.mem_of_superset (Icc_mem_nhdsLE ht.1) (Icc_subset_Icc_right ht.2)
  have key := ODE_solution_unique_of_mem_Icc_left (v := fun _ x => rhs1 P x)
    (s := fun _ => Metric.closedBall (0 : ℝ) R)
    (K := Real.toNNReal (P.σ ^ 2 * (2 * R) + |2 * P.α / (P.γ * P.τ)|))
    (f := A1) (g := yA P T) (a := 0) (b := T)
    (fun _ _ => by
      apply LipschitzOnWith.of_dist_le'
      intro x hx y hy
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hx hy
      have e : rhs1 P x - rhs1 P y = -(x - y) * (P.σ ^ 2 * (x + y) + 2 * P.α / (P.γ * P.τ)) := by
        unfold rhs1; ring
      rw [Real.dist_eq, Real.dist_eq, e, abs_mul, abs_neg, mul_comm]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      calc |P.σ ^ 2 * (x + y) + 2 * P.α / (P.γ * P.τ)|
          ≤ |P.σ ^ 2 * (x + y)| + |2 * P.α / (P.γ * P.τ)| := abs_add_le _ _
        _ ≤ P.σ ^ 2 * (2 * R) + |2 * P.α / (P.γ * P.τ)| := by
          gcongr
          rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
          gcongr
          calc |x + y| ≤ |x| + |y| := abs_add_le _ _
            _ ≤ 2 * R := by linarith)
    hcA
    (fun t ht => (hA.1 t (Ioc_subset_Icc_self ht)).mono_of_mem_nhdsWithin (hmem t ht))
    (fun t ht => by
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      have := hC1 t (Ioc_subset_Icc_self ht)
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _))
    hcy
    (fun t ht => (hy' t (Ioc_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => by
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      have := hC2 t (Ioc_subset_Icc_self ht)
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_right _ _))
    (by
      rw [hA.2.2.1]; unfold yA Qe; simp)
  exact fun u hu => key hu

end DM33

namespace DM33

open DynMomentum.ShortHorizon Set

noncomputable def aF (P : Params) (T w : ℝ) : ℝ :=
  P.γ * (1 - P.γ) * P.σ ^ 2 * P.τ / P.α * C0 P T w + P.α / P.τ

noncomputable def Phic (P : Params) (T u : ℝ) : ℝ := Pe P u * P.D T u / P.D T 0

noncomputable def Wf (P : Params) (T v : ℝ) : ℝ :=
  (Pe P (v + P.τ) - Pe P T * Qe P T (v + P.τ)) / (P.τ * P.D T 0)

lemma hasDerivAt_D (P : Params) (T w : ℝ) :
    HasDerivAt (fun x => P.D T x)
      ((Real.sqrt P.γ - 1) * (↑(2:ℕ) * Qe P T w ^ (2 - 1) * (-(hh P) * Qe P T w))) w := by
  have hfun : (fun x => P.D T x) = fun x => (Real.sqrt P.γ - 1) * Qe P T x ^ 2 + (Real.sqrt P.γ + 1) :=
    funext (D_eq P T)
  rw [hfun]
  exact (((hasDerivAt_Qe P T w).pow 2).const_mul (Real.sqrt P.γ - 1)).add_const _

lemma cont_D (P : Params) (T : ℝ) : Continuous (fun x => P.D T x) := by
  unfold Params.D Params.expo; fun_prop

lemma cont_Pe (P : Params) : Continuous (Pe P) := by unfold Pe; fun_prop

lemma cont_Qe (P : Params) (T : ℝ) : Continuous (Qe P T) := by unfold Qe; fun_prop

lemma cont_Phic (P : Params) (T : ℝ) : Continuous (Phic P T) := by
  unfold Phic; exact ((cont_Pe P).mul (cont_D P T)).div_const _

lemma contOn_C0 (P : Params) (hP : P.Standing) (T : ℝ)
    (hD : ∀ u ∈ Icc (0 : ℝ) T, 0 < P.D T u) : ContinuousOn (C0 P T) (Icc 0 T) := by
  obtain ⟨hα, hα1, hσ, hτ, hγ0⟩ := hP
  have hq : 0 < Real.sqrt P.γ := Real.sqrt_pos.2 hγ0
  have h1 : Continuous (fun w => P.α ^ 2 * (P.expo T w + 1)) := by unfold Params.expo; fun_prop
  have h2 : Continuous (fun w => P.γ * Real.sqrt P.γ * P.σ ^ 2 * P.τ ^ 2 * P.D T w) :=
    continuous_const.mul (cont_D P T)
  unfold C0
  exact ContinuousOn.div h1.continuousOn h2.continuousOn
    (fun w hw => by have := hD w hw; positivity)

lemma aF_eq_log (P : Params) (hP : P.Standing) (T w : ℝ) (hDw : P.D T w ≠ 0) :
    hh P + (Real.sqrt P.γ - 1) * (↑(2:ℕ) * Qe P T w ^ (2 - 1) * (-(hh P) * Qe P T w)) / P.D T w
      = aF P T w := by
  obtain ⟨hα, hα1, hσ, hτ, hγ0⟩ := hP
  obtain ⟨hq, hγ⟩ := sqrt_facts P ⟨hα, hα1, hσ, hτ, hγ0⟩
  unfold aF C0 hh
  rw [expo_eq, D_eq] at *
  generalize Qe P T w = Qv at hDw ⊢
  generalize Real.sqrt P.γ = q at hq hγ hDw ⊢
  rw [hγ]
  have hq0 : q ≠ 0 := hq.ne'
  have hσ0 : P.σ ≠ 0 := hσ.ne'
  have hτ0 : P.τ ≠ 0 := hτ.ne'
  have hα0 : P.α ≠ 0 := hα.ne'
  generalize hDv : (q - 1) * Qv ^ 2 + (q + 1) = Dv at hDw ⊢
  field_simp
  subst hDv
  ring

lemma aF_eq_y (P : Params) (hP : P.Standing) (T w : ℝ) (hDw : P.D T w ≠ 0) :
    aF P T w = P.σ ^ 2 * yA P T w + P.α / (P.γ * P.τ) := by
  obtain ⟨hα, hα1, hσ, hτ, hγ0⟩ := hP
  obtain ⟨hq, hγ⟩ := sqrt_facts P ⟨hα, hα1, hσ, hτ, hγ0⟩
  unfold aF C0 yA
  rw [expo_eq, D_eq] at *
  generalize Qe P T w = Qv at hDw ⊢
  generalize Real.sqrt P.γ = q at hq hγ hDw ⊢
  rw [hγ]
  have hq0 : q ≠ 0 := hq.ne'
  have hσ0 : P.σ ≠ 0 := hσ.ne'
  have hτ0 : P.τ ≠ 0 := hτ.ne'
  have hα0 : P.α ≠ 0 := hα.ne'
  generalize hDv : (q - 1) * Qv ^ 2 + (q + 1) = Dv at hDw ⊢
  field_simp
  subst hDv
  ring

lemma Phic_deriv (P : Params) (hP : P.Standing) (T u : ℝ) (hDu : P.D T u ≠ 0)
    (hD0 : P.D T 0 ≠ 0) : HasDerivAt (Phic P T) (aF P T u * Phic P T u) u := by
  have := ((hasDerivAt_Pe P u).mul (hasDerivAt_D P T u)).div_const (P.D T 0)
  refine this.congr_deriv ?_
  rw [← aF_eq_log P hP T u hDu]
  unfold Phic
  field_simp

lemma int_a (P : Params) (hP : P.Standing) (T : ℝ)
    (hD : ∀ u ∈ Icc (0 : ℝ) T, 0 < P.D T u) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) :
    Real.exp (∫ w in (0 : ℝ)..u,
        (P.γ * (1 - P.γ) * P.σ ^ 2 * P.τ / P.α * C0 P T w + P.α / P.τ)) = Phic P T u := by
  have hsub : uIcc 0 u ⊆ Icc 0 T := by
    rw [uIcc_of_le hu.1]; exact Icc_subset_Icc_right hu.2
  have hderiv : ∀ x ∈ uIcc 0 u,
      HasDerivAt (fun w => hh P * w + Real.log (P.D T w)) (aF P T x) x := by
    intro x hx
    have hDx := hD x (hsub hx)
    have h1 : HasDerivAt (fun w => hh P * w) (hh P) x := by
      simpa using (hasDerivAt_id x).const_mul (hh P)
    have := h1.add ((hasDerivAt_D P T x).log hDx.ne')
    refine this.congr_deriv ?_
    exact aF_eq_log P hP T x hDx.ne'
  have hint : IntervalIntegrable (aF P T) MeasureTheory.volume 0 u := by
    apply ContinuousOn.intervalIntegrable
    unfold aF
    exact ((continuousOn_const.mul (contOn_C0 P hP T hD)).add continuousOn_const).mono hsub
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  unfold aF at this
  rw [this]
  have hD0 := hD 0 ⟨le_rfl, hu.1.trans hu.2⟩
  have hDu := hD u hu
  unfold Phic Pe
  rw [Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_log hDu, Real.exp_log hD0]
  simp

lemma omegaHat_eq (P : Params) (hP : P.Standing) (T : ℝ)
    (hD : ∀ u ∈ Icc (0 : ℝ) T, 0 < P.D T u) (u : ℝ) (hu : u ∈ Icc (-P.τ) (T - P.τ)) :
    omegaHat P T u = P.γ * P.σ ^ 2 / P.α * C0 P T (u + P.τ) * Phic P T (u + P.τ) := by
  unfold omegaHat
  rw [int_a P hP T hD (u + P.τ) ⟨by linarith [hu.1], by linarith [hu.2]⟩]

lemma Wf_deriv (P : Params) (hP : P.Standing) (T v : ℝ) (hDw : P.D T (v + P.τ) ≠ 0)
    (hD0 : P.D T 0 ≠ 0) :
    HasDerivAt (Wf P T)
      (P.γ * P.σ ^ 2 / P.α * C0 P T (v + P.τ) * Phic P T (v + P.τ)) v := by
  have hP1 : HasDerivAt (fun x => Pe P (x + P.τ)) (hh P * Pe P (v + P.τ)) v :=
    (hasDerivAt_Pe P (v + P.τ)).comp_add_const v P.τ
  have hQ1 : HasDerivAt (fun x => Qe P T (x + P.τ)) (-(hh P) * Qe P T (v + P.τ)) v :=
    (hasDerivAt_Qe P T (v + P.τ)).comp_add_const v P.τ
  have := (hP1.sub (hQ1.const_mul (Pe P T))).div_const (P.τ * P.D T 0)
  refine this.congr_deriv ?_
  obtain ⟨hα, hα1, hσ, hτ, hγ0⟩ := hP
  obtain ⟨hq, hγ⟩ := sqrt_facts P ⟨hα, hα1, hσ, hτ, hγ0⟩
  unfold C0 Phic hh
  rw [← PQ P T (v + P.τ), expo_eq, D_eq P T (v + P.τ)]
  rw [D_eq P T (v + P.τ)] at hDw
  generalize Qe P T (v + P.τ) = Qv at hDw ⊢
  generalize Pe P (v + P.τ) = Pv
  generalize P.D T 0 = D0 at hD0 ⊢
  generalize Real.sqrt P.γ = q at hq hγ hDw ⊢
  rw [hγ]
  have hq0 : q ≠ 0 := hq.ne'
  have hσ0 : P.σ ≠ 0 := hσ.ne'
  have hτ0 : P.τ ≠ 0 := hτ.ne'
  have hα0 : P.α ≠ 0 := hα.ne'
  generalize hDv : (q - 1) * Qv ^ 2 + (q + 1) = Dv at hDw ⊢
  field_simp
  subst hDv
  ring

lemma omega_eq (P : Params) (hP : P.Standing) (T : ℝ) (hT0 : 0 ≤ T)
    (hD : ∀ u ∈ Icc (0 : ℝ) T, 0 < P.D T u) (v : ℝ) (hv : v ∈ Icc (-P.τ) 0) :
    omega P T v = Wf P T (min v (T - P.τ)) - Wf P T (-P.τ) := by
  have hm1 : -P.τ ≤ min v (T - P.τ) := le_min hv.1 (by linarith)
  have hm2 : min v (T - P.τ) ≤ T - P.τ := min_le_right _ _
  have hsub : uIcc (-P.τ) (min v (T - P.τ)) ⊆ Icc (-P.τ) (T - P.τ) := by
    rw [uIcc_of_le hm1]; exact Icc_subset_Icc_right hm2
  have hD0 := hD 0 ⟨le_rfl, hT0⟩
  unfold omega
  rw [intervalIntegral.integral_congr (g := fun u => P.γ * P.σ ^ 2 / P.α * C0 P T (u + P.τ)
      * Phic P T (u + P.τ)) (fun u hu => omegaHat_eq P hP T hD u (hsub hu))]
  have hmaps : MapsTo (fun x => x + P.τ) (Icc (-P.τ) (T - P.τ)) (Icc 0 T) :=
    fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    exact Wf_deriv P hP T x (hD _ (hmaps (hsub hx))).ne' hD0.ne'
  · apply ContinuousOn.intervalIntegrable
    have hC : ContinuousOn (fun x => C0 P T (x + P.τ)) (Icc (-P.τ) (T - P.τ)) :=
      (contOn_C0 P hP T hD).comp (continuous_add_const P.τ).continuousOn hmaps
    have hPh : Continuous (fun x => Phic P T (x + P.τ)) :=
      (cont_Phic P T).comp (continuous_add_const P.τ)
    exact ((continuousOn_const.mul hC).mul hPh.continuousOn).mono hsub


noncomputable def fF (P : Params) (T : ℝ) (s : ℝ → ℝ) (u : ℝ) : ℝ :=
  ((1 - P.α) * P.μ / P.γ + (P.r - P.σ ^ 2 / 2) * (1 - P.α / P.γ)
      - P.α / (P.γ * P.τ) * s (u - P.τ)) * yA P T u
    + (1 - P.γ) / P.γ ^ 2 * (P.α / (P.σ ^ 2 * P.τ))
        * ((1 - P.α) * P.μ + P.α * (P.σ ^ 2 / 2 - P.r) - P.α / P.τ * s (u - P.τ))

lemma Phic_zero (P : Params) (T : ℝ) (hD0 : P.D T 0 ≠ 0) : Phic P T 0 = 1 := by
  unfold Phic Pe; simp [hD0]

lemma A2_eq (P : Params) (hP : P.Standing) (T : ℝ) (hT0 : 0 ≤ T) (hTτ : T ≤ P.τ)
    (hD : 0 < P.D T 0) (s : ℝ → ℝ) (hs : ContinuousOn s (Icc (-P.τ) 0))
    (A1 A2 : ℝ → ℝ) (hA : SolvesA9 P T s A1 A2) :
    A2 0 = ∫ u in (0 : ℝ)..T, Phic P T u * fF P T s u := by
  have hDp := D_pos P hP T hD
  have hA1 := A1_eq P hP T hD s A1 A2 hA
  have hcA2 : ContinuousOn A2 (Icc 0 T) := fun u hu => (hA.2.1 u hu).continuousWithinAt
  have hcG : ContinuousOn (fun u => Phic P T u * A2 u) (Icc 0 T) :=
    (cont_Phic P T).continuousOn.mul hcA2
  have hsc : ContinuousOn (fun u => s (u - P.τ)) (Icc 0 T) :=
    hs.comp (continuous_sub_right P.τ).continuousOn
      (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hyc : ContinuousOn (yA P T) (Icc 0 T) := fun u hu =>
    (yA_deriv P hP T u (hDp u hu).ne').continuousAt.continuousWithinAt
  have hfc : ContinuousOn (fun u => Phic P T u * fF P T s u) (Icc 0 T) := by
    unfold fF
    refine (cont_Phic P T).continuousOn.mul (ContinuousOn.add ?_ ?_)
    · exact (continuousOn_const.sub (continuousOn_const.mul hsc)).mul hyc
    · exact continuousOn_const.mul (continuousOn_const.sub (continuousOn_const.mul hsc))
  have key := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT0 hcG
    (f' := fun u => -(Phic P T u * fF P T s u))
    (fun x hx => by
      have hx' := Ioo_subset_Icc_self hx
      have hA2x : HasDerivAt A2 (rhs2 P s x (A1 x) (A2 x)) x :=
        (hA.2.1 x hx').hasDerivAt (Icc_mem_nhds hx.1 hx.2)
      refine HasDerivAt.hasDerivWithinAt ?_
      refine ((Phic_deriv P hP T x (hDp x hx').ne' hD.ne').mul hA2x).congr_deriv ?_
      rw [hA1 x hx', aF_eq_y P hP T x (hDp x hx').ne']
      unfold rhs2 fF; ring)
    ((hfc.intervalIntegrable_of_Icc hT0).neg)
  rw [intervalIntegral.integral_neg, hA.2.2.2, Phic_zero P T hD.ne'] at key
  linarith

lemma int_PQ (P : Params) (hP : P.Standing) (T A B : ℝ) :
    ∫ w in (0 : ℝ)..T, (A * Pe P w + B * Qe P T w) = (A + B) * (Pe P T - 1) / hh P := by
  obtain ⟨hα, _, _, hτ, hγ0⟩ := hP
  have hq : 0 < Real.sqrt P.γ := Real.sqrt_pos.2 hγ0
  have hh0 : hh P ≠ 0 := by unfold hh; positivity
  have hd : ∀ x ∈ uIcc (0 : ℝ) T, HasDerivAt (fun w => (A * Pe P w - B * Qe P T w) / hh P)
      (A * Pe P x + B * Qe P T x) x := fun x _ => by
    have := (((hasDerivAt_Pe P x).const_mul A).sub ((hasDerivAt_Qe P T x).const_mul B)).div_const
      (hh P)
    refine this.congr_deriv ?_
    field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (((continuous_const.mul (cont_Pe P)).add (continuous_const.mul (cont_Qe P T))).intervalIntegrable _ _)]
  have e1 : Pe P 0 = 1 := by simp [Pe]
  have e2 : Qe P T T = 1 := by simp [Qe]
  have e3 : Qe P T 0 = Pe P T := by simp [Qe, Pe]
  rw [e1, e2, e3]; field_simp; ring

lemma ind_int (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) (f : ℝ → ℝ) :
    ∫ v in a..c, (Icc a b).indicator f v = ∫ v in a..b, f v := by
  rw [intervalIntegral.integral_of_le (hab.trans hbc), intervalIntegral.integral_of_le hab,
    MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.Measure.restrict_restrict measurableSet_Icc]
  have : Icc a b ∩ Ioc a c = Ioc a b := by
    ext x; simp only [mem_inter_iff, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨⟨_, h2⟩, h3, _⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1.le, h2⟩, h1, h2.trans hbc⟩
  rw [this]

/-- pointwise form of `Φ · f` (I1). -/
lemma I1 (P : Params) (hP : P.Standing) (T : ℝ) (s : ℝ → ℝ) (u : ℝ) (hDu : P.D T u ≠ 0)
    (hD0 : P.D T 0 ≠ 0) :
    Phic P T u * fF P T s u =
      (((1 - P.α) * P.μ / P.γ + (P.r - P.σ ^ 2 / 2) * (1 - P.α / P.γ))
            * (P.α * (P.γ - 1) / (P.γ * P.σ ^ 2 * P.τ * P.D T 0))
          + (1 - P.γ) / P.γ ^ 2 * (P.α / (P.σ ^ 2 * P.τ))
            * ((1 - P.α) * P.μ + P.α * (P.σ ^ 2 / 2 - P.r)) * ((Real.sqrt P.γ + 1) / P.D T 0))
          * Pe P u
        + (-(((1 - P.α) * P.μ / P.γ + (P.r - P.σ ^ 2 / 2) * (1 - P.α / P.γ))
              * (P.α * (P.γ - 1) * Pe P T / (P.γ * P.σ ^ 2 * P.τ * P.D T 0)))
          + (1 - P.γ) / P.γ ^ 2 * (P.α / (P.σ ^ 2 * P.τ))
            * ((1 - P.α) * P.μ + P.α * (P.σ ^ 2 / 2 - P.r))
            * ((Real.sqrt P.γ - 1) * Pe P T / P.D T 0)) * Qe P T u
        - (1 - P.γ) * (C0 P T u * Phic P T u * s (u - P.τ)) := by
  obtain ⟨hα, hα1, hσ, hτ, hγ0⟩ := hP
  obtain ⟨hq, hγ⟩ := sqrt_facts P ⟨hα, hα1, hσ, hτ, hγ0⟩
  unfold fF Phic C0 yA
  rw [← PQ P T u, expo_eq, D_eq P T u]
  rw [D_eq P T u] at hDu
  generalize s (u - P.τ) = sv
  generalize Qe P T u = Qv at hDu ⊢
  generalize Pe P u = Pv
  generalize P.D T 0 = D0 at hD0 ⊢
  generalize Real.sqrt P.γ = q at hq hγ hDu ⊢
  rw [hγ]
  have hq0 : q ≠ 0 := hq.ne'
  have hσ0 : P.σ ≠ 0 := hσ.ne'
  have hτ0 : P.τ ≠ 0 := hτ.ne'
  have hα0 : P.α ≠ 0 := hα.ne'
  generalize hDv : (q - 1) * Qv ^ 2 + (q + 1) = Dv at hDu ⊢
  field_simp
  subst hDv
  ring

/-- pointwise form of `Φ · bracket` (I2). -/
lemma I2 (P : Params) (hP : P.Standing) (T u : ℝ) (hDu : P.D T u ≠ 0) (hD0 : P.D T 0 ≠ 0) :
    Phic P T u * ((((1 - P.α) * P.μ - P.α * P.r) / P.γ + P.r)
              * (P.γ * (1 - P.γ) * P.τ / P.α) * C0 P T u
            + P.r * ((P.γ - 1) * P.α / (P.γ * P.σ ^ 2 * P.τ))) =
      ((((1 - P.α) * P.μ - P.α * P.r) / P.γ + P.r) * (P.γ * (1 - P.γ) * P.τ / P.α)
            * (P.α ^ 2 / (P.γ * Real.sqrt P.γ * P.σ ^ 2 * P.τ ^ 2 * P.D T 0))
          + P.r * ((P.γ - 1) * P.α / (P.γ * P.σ ^ 2 * P.τ)) * ((Real.sqrt P.γ + 1) / P.D T 0))
          * Pe P u
        + ((((1 - P.α) * P.μ - P.α * P.r) / P.γ + P.r) * (P.γ * (1 - P.γ) * P.τ / P.α)
            * (P.α ^ 2 * Pe P T / (P.γ * Real.sqrt P.γ * P.σ ^ 2 * P.τ ^ 2 * P.D T 0))
          + P.r * ((P.γ - 1) * P.α / (P.γ * P.σ ^ 2 * P.τ))
            * ((Real.sqrt P.γ - 1) * Pe P T / P.D T 0)) * Qe P T u := by
  obtain ⟨hα, hα1, hσ, hτ, hγ0⟩ := hP
  obtain ⟨hq, hγ⟩ := sqrt_facts P ⟨hα, hα1, hσ, hτ, hγ0⟩
  unfold Phic C0
  rw [← PQ P T u, expo_eq, D_eq P T u]
  rw [D_eq P T u] at hDu
  generalize Qe P T u = Qv at hDu ⊢
  generalize Pe P u = Pv
  generalize P.D T 0 = D0 at hD0 ⊢
  generalize Real.sqrt P.γ = q at hq hγ hDu ⊢
  rw [hγ]
  have hq0 : q ≠ 0 := hq.ne'
  have hσ0 : P.σ ≠ 0 := hσ.ne'
  have hτ0 : P.τ ≠ 0 := hτ.ne'
  have hα0 : P.α ≠ 0 := hα.ne'
  generalize hDv : (q - 1) * Qv ^ 2 + (q + 1) = Dv at hDu ⊢
  field_simp
  subst hDv
  ring


noncomputable def A1c (P : Params) (T : ℝ) : ℝ :=
  ((1 - P.α) * P.μ / P.γ + (P.r - P.σ ^ 2 / 2) * (1 - P.α / P.γ))
      * (P.α * (P.γ - 1) / (P.γ * P.σ ^ 2 * P.τ * P.D T 0))
    + (1 - P.γ) / P.γ ^ 2 * (P.α / (P.σ ^ 2 * P.τ))
      * ((1 - P.α) * P.μ + P.α * (P.σ ^ 2 / 2 - P.r)) * ((Real.sqrt P.γ + 1) / P.D T 0)

noncomputable def B1c (P : Params) (T : ℝ) : ℝ :=
  -(((1 - P.α) * P.μ / P.γ + (P.r - P.σ ^ 2 / 2) * (1 - P.α / P.γ))
        * (P.α * (P.γ - 1) * Pe P T / (P.γ * P.σ ^ 2 * P.τ * P.D T 0)))
    + (1 - P.γ) / P.γ ^ 2 * (P.α / (P.σ ^ 2 * P.τ))
      * ((1 - P.α) * P.μ + P.α * (P.σ ^ 2 / 2 - P.r))
      * ((Real.sqrt P.γ - 1) * Pe P T / P.D T 0)

noncomputable def A2c (P : Params) (T : ℝ) : ℝ :=
  (((1 - P.α) * P.μ - P.α * P.r) / P.γ + P.r) * (P.γ * (1 - P.γ) * P.τ / P.α)
      * (P.α ^ 2 / (P.γ * Real.sqrt P.γ * P.σ ^ 2 * P.τ ^ 2 * P.D T 0))
    + P.r * ((P.γ - 1) * P.α / (P.γ * P.σ ^ 2 * P.τ)) * ((Real.sqrt P.γ + 1) / P.D T 0)

noncomputable def B2c (P : Params) (T : ℝ) : ℝ :=
  (((1 - P.α) * P.μ - P.α * P.r) / P.γ + P.r) * (P.γ * (1 - P.γ) * P.τ / P.α)
      * (P.α ^ 2 * Pe P T / (P.γ * Real.sqrt P.γ * P.σ ^ 2 * P.τ ^ 2 * P.D T 0))
    + P.r * ((P.γ - 1) * P.α / (P.γ * P.σ ^ 2 * P.τ))
      * ((Real.sqrt P.γ - 1) * Pe P T / P.D T 0)

noncomputable def Om (P : Params) (T : ℝ) : ℝ :=
  (1 / (P.τ * P.D T 0) + -Pe P T / (P.τ * P.D T 0)) * (Pe P T - 1) / hh P
    - T * Wf P T (-P.τ) + (P.τ - T) * (Wf P T (T - P.τ) - Wf P T (-P.τ))

lemma cont_Wf (P : Params) (T : ℝ) : Continuous (Wf P T) := by
  unfold Wf Pe Qe; fun_prop

lemma int_lin (P : Params) (hP : P.Standing) (T A B c : ℝ) (hT0 : 0 ≤ T) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc 0 T)) :
    ∫ u in (0 : ℝ)..T, (A * Pe P u + B * Qe P T u - c * g u)
      = (A + B) * (Pe P T - 1) / hh P - c * ∫ u in (0 : ℝ)..T, g u := by
  rw [intervalIntegral.integral_sub, int_PQ P hP T, intervalIntegral.integral_const_mul]
  · exact ((continuous_const.mul (cont_Pe P)).add
      (continuous_const.mul (cont_Qe P T))).intervalIntegrable _ _
  · exact (continuousOn_const.mul hg).intervalIntegrable_of_Icc hT0

lemma omega_int (P : Params) (hP : P.Standing) (T : ℝ) (hT0 : 0 ≤ T) (hTτ : T ≤ P.τ)
    (hD : ∀ u ∈ Icc (0 : ℝ) T, 0 < P.D T u) :
    ∫ v in (-P.τ)..0, omega P T v = Om P T := by
  have hτ : 0 < P.τ := hP.2.2.2.1
  set g : ℝ → ℝ := fun v => Wf P T (min v (T - P.τ)) - Wf P T (-P.τ) with hg
  have gc : Continuous g :=
    ((cont_Wf P T).comp (continuous_id.min continuous_const)).sub continuous_const
  have e0 : ∫ v in (-P.τ)..0, omega P T v = ∫ v in (-P.τ)..0, g v := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (by linarith)] at hv
    exact omega_eq P hP T hT0 hD v hv
  rw [e0, ← intervalIntegral.integral_add_adjacent_intervals (b := T - P.τ)
    (gc.intervalIntegrable _ _) (gc.intervalIntegrable _ _)]
  have e1 : ∫ v in (-P.τ)..(T - P.τ), g v
      = ∫ v in (-P.τ)..(T - P.τ), (Wf P T v - Wf P T (-P.τ)) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (by linarith)] at hv
    simp only [hg, min_eq_left hv.2]
  have e2 : ∫ v in (T - P.τ)..0, g v = ∫ v in (T - P.τ)..0, (Wf P T (T - P.τ) - Wf P T (-P.τ)) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (by linarith)] at hv
    simp only [hg, min_eq_right hv.1]
  have h := intervalIntegral.integral_comp_add_right
    (fun w => (1 / (P.τ * P.D T 0)) * Pe P w + (-Pe P T / (P.τ * P.D T 0)) * Qe P T w) P.τ
    (a := -P.τ) (b := T - P.τ)
  simp only [neg_add_cancel, sub_add_cancel] at h
  have e3 : ∫ v in (-P.τ)..(T - P.τ), Wf P T v
      = ∫ x in (-P.τ)..(T - P.τ), (1 / (P.τ * P.D T 0) * Pe P (x + P.τ)
          + -Pe P T / (P.τ * P.D T 0) * Qe P T (x + P.τ)) := by
    apply intervalIntegral.integral_congr
    intro v _
    unfold Wf; ring
  rw [e1, e2, intervalIntegral.integral_sub ((cont_Wf P T).intervalIntegrable _ _)
    intervalIntegrable_const, e3, h, int_PQ P hP T, intervalIntegral.integral_const,
    intervalIntegral.integral_const]
  unfold Om
  simp only [smul_eq_mul]
  ring

lemma ind_s_int (P : Params) (hP : P.Standing) (T : ℝ) (hT0 : 0 ≤ T) (hTτ : T ≤ P.τ)
    (hD : ∀ u ∈ Icc (0 : ℝ) T, 0 < P.D T u) (s : ℝ → ℝ) :
    ∫ v in (-P.τ)..0, Set.indicator (Set.Icc (-P.τ) (T - P.τ)) (omegaHat P T) v * s v
      = P.γ * P.σ ^ 2 / P.α * ∫ u in (0 : ℝ)..T, C0 P T u * Phic P T u * s (u - P.τ) := by
  have e1 : ∀ v, Set.indicator (Set.Icc (-P.τ) (T - P.τ)) (omegaHat P T) v * s v
      = Set.indicator (Set.Icc (-P.τ) (T - P.τ)) (fun v => omegaHat P T v * s v) v :=
    fun v => (Set.indicator_mul_left _ _ _).symm
  simp_rw [e1]
  rw [ind_int _ _ _ (by linarith) (by linarith)]
  have h := intervalIntegral.integral_comp_add_right
    (fun w => P.γ * P.σ ^ 2 / P.α * (C0 P T w * Phic P T w * s (w - P.τ))) P.τ
    (a := -P.τ) (b := T - P.τ)
  simp only [neg_add_cancel, sub_add_cancel, add_sub_cancel_right] at h
  rw [← intervalIntegral.integral_const_mul, ← h]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le (by linarith)] at hv
  simp only
  rw [omegaHat_eq P hP T hD v hv]
  ring

lemma C1_eq (P : Params) (hP : P.Standing) (T : ℝ) (hT0 : 0 ≤ T) (hTτ : T ≤ P.τ)
    (hD : ∀ u ∈ Icc (0 : ℝ) T, 0 < P.D T u) :
    C1 P T = (A2c P T + B2c P T) * (Pe P T - 1) / hh P
      + (1 - P.γ) * P.r * (P.α / (P.γ * P.σ ^ 2)) * Om P T := by
  have hD0 := (hD 0 ⟨le_rfl, hT0⟩).ne'
  have hc : (∫ u in (0 : ℝ)..T,
      Real.exp (∫ w in (0 : ℝ)..u,
          (P.γ * (1 - P.γ) * P.σ ^ 2 * P.τ / P.α * C0 P T w + P.α / P.τ))
        * ((((1 - P.α) * P.μ - P.α * P.r) / P.γ + P.r)
              * (P.γ * (1 - P.γ) * P.τ / P.α) * C0 P T u
            + P.r * ((P.γ - 1) * P.α / (P.γ * P.σ ^ 2 * P.τ))))
      = ∫ u in (0 : ℝ)..T, (A2c P T * Pe P u + B2c P T * Qe P T u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hT0] at hu
    simp only
    rw [int_a P hP T hD u hu]
    exact I2 P hP T u (hD u hu).ne' hD0
  unfold C1
  rw [hc, int_PQ P hP T, omega_int P hP T hT0 hTτ hD]

lemma A2_val (P : Params) (hP : P.Standing) (T : ℝ) (hT0 : 0 ≤ T) (hTτ : T ≤ P.τ)
    (hD : 0 < P.D T 0) (s : ℝ → ℝ) (hs : ContinuousOn s (Icc (-P.τ) 0))
    (A1 A2 : ℝ → ℝ) (hA : SolvesA9 P T s A1 A2) :
    A2 0 = (A1c P T + B1c P T) * (Pe P T - 1) / hh P
      - (1 - P.γ) * ∫ u in (0 : ℝ)..T, C0 P T u * Phic P T u * s (u - P.τ) := by
  have hDp := D_pos P hP T hD
  have hsc : ContinuousOn (fun u => s (u - P.τ)) (Icc 0 T) :=
    hs.comp (continuous_sub_right P.τ).continuousOn
      (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hgc : ContinuousOn (fun u => C0 P T u * Phic P T u * s (u - P.τ)) (Icc 0 T) :=
    ((contOn_C0 P hP T hDp).mul (cont_Phic P T).continuousOn).mul hsc
  rw [A2_eq P hP T hT0 hTτ hD s hs A1 A2 hA]
  have hc : ∫ u in (0 : ℝ)..T, Phic P T u * fF P T s u
      = ∫ u in (0 : ℝ)..T, (A1c P T * Pe P u + B1c P T * Qe P T u
          - (1 - P.γ) * (C0 P T u * Phic P T u * s (u - P.τ))) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hT0] at hu
    exact I1 P hP T s u (hDp u hu).ne' hD.ne'
  rw [hc, int_lin P hP T _ _ _ hT0 _ hgc]


lemma Wf_strictMono (P : Params) (hP : P.Standing) (T : ℝ) (hD0 : 0 < P.D T 0) :
    StrictMono (Wf P T) := by
  intro a b hab
  obtain ⟨hα, _, _, hτ, hγ0⟩ := hP
  have hq : 0 < Real.sqrt P.γ := Real.sqrt_pos.2 hγ0
  have hh0 : 0 < hh P := by unfold hh; positivity
  unfold Wf
  apply (div_lt_div_iff_of_pos_right (by positivity)).2
  have h1 : Pe P (a + P.τ) < Pe P (b + P.τ) :=
    Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left (by linarith) hh0)
  have h2 : Qe P T (b + P.τ) < Qe P T (a + P.τ) :=
    Real.exp_lt_exp.2 (mul_lt_mul_of_pos_left (by linarith) hh0)
  have hX : 0 < Pe P T := Real.exp_pos _
  nlinarith

lemma main_eq (P : Params) (hP : P.Standing) (T : ℝ) (hT0 : 0 ≤ T) (hTτ : T ≤ P.τ)
    (hD : 0 < P.D T 0) (s : ℝ → ℝ) (hs : ContinuousOn s (Set.Icc (-P.τ) 0))
    (A1 A2 : ℝ → ℝ) (hA : SolvesA9 P T s A1 A2) :
    phiStar P s A1 A2 = phiM P s + phiH P T s := by
  have hDp := D_pos P hP T hD
  have hA10 : A1 0 = yA P T 0 := A1_eq P hP T hD s A1 A2 hA 0 ⟨le_rfl, hT0⟩
  have hτ : 0 < P.τ := hP.2.2.2.1
  have hw0 : omega P T 0 = Wf P T (T - P.τ) - Wf P T (-P.τ) := by
    rw [omega_eq P hP T hT0 hDp 0 ⟨by linarith, le_rfl⟩, min_eq_right (by linarith)]
  have hwm : omega P T (-P.τ) = 0 := by
    rw [omega_eq P hP T hT0 hDp (-P.τ) ⟨le_rfl, by linarith⟩, min_eq_left (by linarith)]
    ring
  unfold phiStar phiM phiH pathReturn
  rw [hA10, A2_val P hP T hT0 hTτ hD s hs A1 A2 hA, hw0, hwm,
    ind_s_int P hP T hT0 hTτ hDp s, C1_eq P hP T hT0 hTτ hDp, omega_int P hP T hT0 hTτ hDp]
  simp only [zero_mul, intervalIntegral.integral_zero, intervalIntegral.integral_const,
    smul_eq_mul]
  generalize ∫ u in (0 : ℝ)..T, C0 P T u * Phic P T u * s (u - P.τ) = S
  unfold theta0 yA A1c B1c A2c B2c Om Wf hh
  simp only [neg_add_cancel, sub_add_cancel]
  have e1 : Pe P 0 = 1 := by simp [Pe]
  have e2 : Qe P T T = 1 := by simp [Qe]
  have e3 : Qe P T 0 = Pe P T := by simp [Qe, Pe]
  rw [e1, e2, e3, D_eq P T 0, e3]
  have hD0' := hD
  rw [D_eq P T 0, e3] at hD0'
  obtain ⟨hα, hα1, hσ, hτ', hγ0⟩ := hP
  obtain ⟨hq, hγ⟩ := sqrt_facts P ⟨hα, hα1, hσ, hτ', hγ0⟩
  generalize Pe P T = X at hD0' ⊢
  generalize Real.sqrt P.γ = q at hq hγ hD0' ⊢
  rw [hγ]
  have hq0 : q ≠ 0 := hq.ne'
  have hσ0 : P.σ ≠ 0 := hσ.ne'
  have hτ0 : P.τ ≠ 0 := hτ.ne'
  have hα0 : P.α ≠ 0 := hα.ne'
  generalize hDv : (q - 1) * X ^ 2 + (q + 1) = Dv at hD0' ⊢
  have hDv0 : Dv ≠ 0 := hD0'.ne'
  field_simp
  subst hDv
  ring

lemma omega_props (P : Params) (hP : P.Standing) (T : ℝ) (hT0 : 0 ≤ T) (hTτ : T ≤ P.τ)
    (hD : 0 < P.D T 0) :
    (0 < T → ∀ v ∈ Set.Ioc (-P.τ) 0, 0 < omega P T v) ∧
    StrictMonoOn (omega P T) (Set.Icc (-P.τ) (T - P.τ)) ∧
    ∀ v ∈ Set.Icc (T - P.τ) 0, omega P T v = omega P T (T - P.τ) := by
  have hDp := D_pos P hP T hD
  have hτ : 0 < P.τ := hP.2.2.2.1
  have hW := Wf_strictMono P hP T hD
  refine ⟨fun hT v hv => ?_, fun a ha b hb hab => ?_, fun v hv => ?_⟩
  · rw [omega_eq P hP T hT0 hDp v ⟨hv.1.le, hv.2⟩, sub_pos]
    exact hW (lt_min hv.1 (by linarith))
  · rw [omega_eq P hP T hT0 hDp a ⟨ha.1, by linarith [ha.2]⟩,
      omega_eq P hP T hT0 hDp b ⟨hb.1, by linarith [hb.2]⟩,
      min_eq_left ha.2, min_eq_left hb.2]
    linarith [hW hab]
  · rw [omega_eq P hP T hT0 hDp v ⟨by linarith [hv.1], hv.2⟩,
      omega_eq P hP T hT0 hDp (T - P.τ) ⟨by linarith, by linarith⟩,
      min_eq_right hv.1, min_self]

end DM33

open DynMomentum.ShortHorizon in
theorem solution (P : Params) (hP : P.Standing) (T : ℝ) (hT0 : 0 ≤ T) (hTτ : T ≤ P.τ)
    (hD : 0 < P.D T 0) (s : ℝ → ℝ) (hs : ContinuousOn s (Set.Icc (-P.τ) 0))
    (A1 A2 : ℝ → ℝ) (hA : SolvesA9 P T s A1 A2) :
    phiStar P s A1 A2 = phiM P s + phiH P T s ∧
    (0 < T → ∀ v ∈ Set.Ioc (-P.τ) 0, 0 < omega P T v) ∧
    StrictMonoOn (omega P T) (Set.Icc (-P.τ) (T - P.τ)) ∧
    ∀ v ∈ Set.Icc (T - P.τ) 0, omega P T v = omega P T (T - P.τ) := by
  exact ⟨DM33.main_eq P hP T hT0 hTτ hD s hs A1 A2 hA, DM33.omega_props P hP T hT0 hTτ hD⟩
