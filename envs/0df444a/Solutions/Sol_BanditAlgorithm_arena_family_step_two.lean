-- Prove2me | solution 1 for BanditAlgorithm.arena_family_step_two
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T13:59:04.226109+00:00
-- url     : https://prove2.me/submissions/ffd9203b-4ded-409b-9af4-55865f44bc88

import Mathlib
import Definitions.Def_LayeredArena

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace P4acf
open BanditAlgorithm

variable {S A : ℕ}

abbrev Tr (S A m : ℕ) := MDPTrajectory S A m

abbrev sn {m : ℕ} (h : Tr S A m) (x : Fin S × Fin A) : Tr S A (m + 1) :=
  Fin.snoc (α := fun _ ↦ Fin S × Fin A) h x

lemma int_toMeasure (d : MDPStateDistribution S) (f : Fin S → ℝ) :
    ∫ s, f s ∂d.toMeasure = ∑ s, (d.prob s : ℝ) * f s := by
  rw [MDPStateDistribution.toMeasure, integral_finsetSum_measure
    (fun _ _ => (Integrable.of_finite).smul_measure ENNReal.coe_ne_top)]
  simp [integral_dirac, NNReal.smul_def]

lemma sk_zero (M : FiniteMDP S A) (μ0 : MDPStateDistribution S) (h : Tr S A 0) :
    mdpStateKernel M μ0 0 h = μ0.toMeasure := by
  simp [mdpStateKernel]

lemma sk_succ (M : FiniteMDP S A) (μ0 : MDPStateDistribution S) {m : ℕ} (h : Tr S A (m + 1)) :
    mdpStateKernel M μ0 (m + 1) h =
      (M.transitionDist (h (Fin.last m)).1 (h (Fin.last m)).2).toMeasure := by
  simp [mdpStateKernel, mdpTransitionKernel, Kernel.ofFunOfCountable]

lemma int_succ (M : FiniteMDP S A) (μ0 : MDPStateDistribution S) (π : MDPPolicy S A) (m : ℕ)
    (G : Tr S A (m + 1) → ℝ) :
    ∫ h, G h ∂(mdpMeasure M μ0 π (m + 1)) =
      ∫ h, ∫ s, ∫ a, G (sn h (s, a)) ∂(π.select m (h, s)) ∂(mdpStateKernel M μ0 m h)
        ∂(mdpMeasure M μ0 π m) := by
  rw [mdpMeasure, integral_map measurable_mdpTrajectorySnoc.aemeasurable
    (measurable_of_countable G).aestronglyMeasurable]
  rw [Measure.integral_compProd Integrable.of_finite]
  congr 1; funext h
  rw [mdpStepKernel, ProbabilityTheory.integral_compProd Integrable.of_finite]

/-- integral over a probability measure of a function not depending on the variable -/
lemma int_pol (π : MDPPolicy S A) (m : ℕ) (h : Tr S A m) (s : Fin S) (c : ℝ) :
    ∫ _a, c ∂(π.select m (h, s)) = c := by
  simp

lemma int_zero (M : FiniteMDP S A) (μ0 : MDPStateDistribution S) (π : MDPPolicy S A)
    (G : Tr S A 0 → ℝ) : ∫ h, G h ∂(mdpMeasure M μ0 π 0) = G (fun t ↦ t.elim0) := by
  simp [mdpMeasure]


/-- state weights of the next state -/
noncomputable def Kw (M : FiniteMDP S A) (μ0 : MDPStateDistribution S) :
    (m : ℕ) → Tr S A m → Fin S → ℝ
  | 0, _, s => (μ0.prob s : ℝ)
  | m + 1, h, s => (M.P (h (Fin.last m)).1 (h (Fin.last m)).2 s : ℝ)

lemma int_state (M : FiniteMDP S A) (μ0 : MDPStateDistribution S) (m : ℕ) (h : Tr S A m)
    (f : Fin S → ℝ) :
    ∫ s, f s ∂(mdpStateKernel M μ0 m h) = ∑ s, Kw M μ0 m h s * f s := by
  cases m with
  | zero => rw [sk_zero, int_toMeasure]; rfl
  | succ m => rw [sk_succ, int_toMeasure]; rfl

lemma Kw_sum (M : FiniteMDP S A) (μ0 : MDPStateDistribution S) (m : ℕ) (h : Tr S A m) :
    ∑ s, Kw M μ0 m h s = 1 := by
  cases m with
  | zero => simp only [Kw]; exact_mod_cast μ0.sum_one
  | succ m => simp only [Kw]; exact_mod_cast M.P_sum_one _ _

lemma int_succ2 (M : FiniteMDP S A) (μ0 : MDPStateDistribution S) (π : MDPPolicy S A) (m : ℕ)
    (G : Tr S A (m + 1) → ℝ) :
    ∫ h, G h ∂(mdpMeasure M μ0 π (m + 1)) =
      ∫ h, ∑ s, Kw M μ0 m h s * ∫ a, G (sn h (s, a)) ∂(π.select m (h, s))
        ∂(mdpMeasure M μ0 π m) := by
  rw [int_succ]
  congr 1; funext h
  rw [int_state]

/-- a function that ignores the last round integrates as on the shorter horizon -/
lemma int_init (M : FiniteMDP S A) (μ0 : MDPStateDistribution S) (π : MDPPolicy S A) (m : ℕ)
    (G : Tr S A (m + 1) → ℝ) (G' : Tr S A m → ℝ) (hG : ∀ h x, G (sn h x) = G' h) :
    ∫ h, G h ∂(mdpMeasure M μ0 π (m + 1)) = ∫ h, G' h ∂(mdpMeasure M μ0 π m) := by
  rw [int_succ]
  congr 1; funext h
  simp [hG]

lemma sum_snoc {m : ℕ} (c : Fin S × Fin A → ℝ) (h : Tr S A m) (x : Fin S × Fin A) :
    ∑ t, c (sn h x t) = ∑ t, c (h t) + c x := by
  rw [Fin.sum_univ_castSucc]
  simp [sn]

lemma sn_last {m : ℕ} (h : Tr S A m) (x : Fin S × Fin A) : sn h x (Fin.last m) = x := by
  simp [sn]

lemma int_cadd {X : Type*} [MeasurableSpace X] [Finite X] [MeasurableSingletonClass X]
    (ν : Measure X) [IsProbabilityMeasure ν] (C : ℝ) (f : X → ℝ) :
    ∫ a, (C + f a) ∂ν = C + ∫ a, f a ∂ν := by
  rw [integral_add (integrable_const _) Integrable.of_finite]
  simp

/-- Poisson-equation identity: telescoping of a potential along the trajectory. -/
theorem poisson (M : FiniteMDP S A) (π : MDPPolicy S A) (s0 : Fin S)
    (c : Fin S → Fin A → ℝ) (v : Fin S → ℝ) (g : ℝ)
    (hP : ∀ m (h : Tr S A m) s,
      ∫ a, (c s a + ∑ s', (M.P s a s' : ℝ) * v s') ∂(π.select m (h, s)) = g + v s) (m : ℕ) :
    ∫ h, ((∑ t, c (h t).1 (h t).2) +
        ∑ s', (M.P (h (Fin.last m)).1 (h (Fin.last m)).2 s' : ℝ) * v s')
      ∂(mdpMeasure M (mdpStateDirac s0) π (m + 1)) = (m + 1) * g + v s0 := by
  induction m with
  | zero =>
    rw [int_succ2, int_zero]
    simp only [Kw, mdpStateDirac]
    have : ∀ s : Fin S, ((if s = s0 then (1:ℝ≥0) else 0 : ℝ≥0) : ℝ) *
        ∫ a, ((∑ t : Fin 1, c ((sn (fun t ↦ t.elim0) (s, a)) t).1 ((sn (fun t ↦ t.elim0) (s, a)) t).2) +
          ∑ s', (M.P ((sn (fun t ↦ t.elim0) (s, a)) (Fin.last 0)).1
            ((sn (fun t ↦ t.elim0) (s, a)) (Fin.last 0)).2 s' : ℝ) * v s')
          ∂(π.select 0 (fun t ↦ t.elim0, s)) = if s = s0 then g + v s0 else 0 := by
      intro s
      by_cases hs : s = s0
      · rw [if_pos hs, if_pos hs]
        subst hs
        simp only [NNReal.coe_one, one_mul]
        rw [← hP 0 (fun t ↦ t.elim0) s]
        congr 1; funext a
        have e : sn (fun t ↦ t.elim0) (s, a) (0 : Fin 1) = (s, a) := sn_last _ _
        have e' : sn (fun t ↦ t.elim0) (s, a) (Fin.last 0) = (s, a) := sn_last _ _
        rw [Fin.sum_univ_one, e, e']
      · simp [hs]
    rw [Finset.sum_congr rfl (fun s _ => this s)]
    simp
  | succ m ih =>
    rw [int_succ2]
    have key : ∀ h : Tr S A (m + 1), ∑ s, Kw M (mdpStateDirac s0) (m + 1) h s *
        ∫ a, ((∑ t, c ((sn h (s, a)) t).1 ((sn h (s, a)) t).2) +
          ∑ s', (M.P ((sn h (s, a)) (Fin.last (m + 1))).1
            ((sn h (s, a)) (Fin.last (m + 1))).2 s' : ℝ) * v s') ∂(π.select (m + 1) (h, s))
        = ((∑ t, c (h t).1 (h t).2) +
          ∑ s', (M.P (h (Fin.last m)).1 (h (Fin.last m)).2 s' : ℝ) * v s') + g := by
      intro h
      have e1 : ∀ s, ∫ a, ((∑ t, c ((sn h (s, a)) t).1 ((sn h (s, a)) t).2) +
          ∑ s', (M.P ((sn h (s, a)) (Fin.last (m + 1))).1
            ((sn h (s, a)) (Fin.last (m + 1))).2 s' : ℝ) * v s') ∂(π.select (m + 1) (h, s))
          = (∑ t, c (h t).1 (h t).2) + (g + v s) := by
        intro s
        rw [← hP (m + 1) h s, ← int_cadd]
        congr 1; funext a
        rw [sum_snoc (fun x => c x.1 x.2), sn_last]
        ring
      simp_rw [e1]
      simp only [Kw, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
      rw [show (∑ i, (M.P (h (Fin.last m)).1 (h (Fin.last m)).2 i : ℝ)) = 1 by
        exact_mod_cast M.P_sum_one _ _]
      ring
    simp_rw [key]
    rw [integral_add Integrable.of_finite (integrable_const _), ih]
    simp
    ring


lemma pinsk_pt (y : ℝ) (hy : 0 < y) : 3 * (y - 1) ^ 2 ≤ (2 + 4 * y) * (y - 1 - Real.log y) := by
  let f : ℝ → ℝ := fun y => (2 + 4 * y) * (y - 1 - Real.log y) - 3 * (y - 1) ^ 2
  have hd : ∀ x, 0 < x → HasDerivAt f (4 * (Real.sinh (Real.log x) - Real.log x)) x := by
    intro x hx
    have h1 := ((hasDerivAt_id x).const_mul (4:ℝ)).const_add (2:ℝ)
    have h2 := ((hasDerivAt_id x).sub_const (1:ℝ)).sub (Real.hasDerivAt_log hx.ne')
    have h3 := (((hasDerivAt_id x).sub_const (1:ℝ)).pow 2).const_mul (3:ℝ)
    have := (h1.mul h2).sub h3
    refine this.congr_deriv ?_
    simp only [Pi.sub_apply, id]
    rw [Real.sinh_log hx]
    field_simp
    ring
  have hcont : ContinuousOn f (Set.Ioi 0) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have f1 : f 1 = 0 := by simp [f]
  have key : 0 ≤ f y := by
    rcases le_total 1 y with h | h
    · have hm : MonotoneOn f (Set.Ici 1) := by
        apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
        · exact hcont.mono (fun x hx => Set.mem_Ioi.mpr (lt_of_lt_of_le one_pos hx))
        · rw [interior_Ici]
          exact fun x hx => (hd x (lt_trans one_pos hx)).differentiableAt.differentiableWithinAt
        · rw [interior_Ici]
          intro x hx
          rw [(hd x (lt_trans one_pos hx)).deriv]
          have : 0 ≤ Real.log x := Real.log_nonneg hx.le
          have := Real.self_le_sinh_iff.mpr this
          linarith
      have := hm (Set.self_mem_Ici) h h
      linarith
    · have ha : AntitoneOn f (Set.Ioc 0 1) := by
        apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 1)
        · exact hcont.mono (fun x hx => hx.1)
        · rw [interior_Ioc]
          exact fun x hx => (hd x hx.1).differentiableAt.differentiableWithinAt
        · rw [interior_Ioc]
          intro x hx
          rw [(hd x hx.1).deriv]
          have : Real.log x ≤ 0 := Real.log_nonpos hx.1.le hx.2.le
          have := Real.sinh_le_self_iff.mpr this
          linarith
      have := ha ⟨hy, h⟩ ⟨one_pos, le_refl 1⟩ h
      linarith
  simp only [f] at key
  linarith

/-- Pinsker in likelihood-ratio form, pointwise with a free parameter. -/
lemma pinsk_lam (y l : ℝ) (hy : 0 < y) (hl : 0 < l) :
    |y - 1| ≤ l * (2 + 4 * y) / 6 + (y - 1 - Real.log y) / (2 * l) := by
  have h := pinsk_pt y hy
  have hL : 0 ≤ y - 1 - Real.log y := by
    have := Real.log_le_sub_one_of_pos hy; linarith
  have hu : 0 ≤ l ^ 2 * (2 + 4 * y) := by positivity
  -- (u + v)^2 ≥ 4uv ≥ 36 l^2 (y-1)^2 with u = l^2(2+4y), v = 3L
  have hsq : (6 * l * |y - 1|) ^ 2 ≤ (l ^ 2 * (2 + 4 * y) + 3 * (y - 1 - Real.log y)) ^ 2 := by
    have e : (6 * l * |y - 1|) ^ 2 = 12 * l ^ 2 * (3 * (y - 1) ^ 2) := by
      rw [mul_pow, sq_abs]; ring
    rw [e]
    nlinarith [sq_nonneg (l ^ 2 * (2 + 4 * y) - 3 * (y - 1 - Real.log y)),
      mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ 12 * l ^ 2)]
  have h6 : 6 * l * |y - 1| ≤ l ^ 2 * (2 + 4 * y) + 3 * (y - 1 - Real.log y) :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  have e : l * (2 + 4 * y) / 6 + (y - 1 - Real.log y) / (2 * l) =
      (l ^ 2 * (2 + 4 * y) + 3 * (y - 1 - Real.log y)) / (6 * l) := by
    field_simp; ring
  rw [e, le_div_iff₀ (by positivity)]
  linarith


section LR
variable (Ecnt : Fin S → ℕ) (N : ℕ)

/-- full count of a trajectory -/
def fc {m : ℕ} (h : Tr S A m) : ℕ := ∑ t, Ecnt (h t).1

lemma pc_full {m : ℕ} (h : Tr S A m) : prefixCount Ecnt h m = fc Ecnt h := by
  simp [prefixCount, fc]

lemma pc_le_fc {m : ℕ} (h : Tr S A m) (k : ℕ) : prefixCount Ecnt h k ≤ fc Ecnt h := by
  unfold prefixCount fc
  apply Finset.sum_le_sum
  intro u _
  split_ifs <;> simp

lemma pc_snoc {m : ℕ} (h : Tr S A m) (x : Fin S × Fin A) {k : ℕ} (hk : k ≤ m) :
    prefixCount Ecnt (sn h x) k = prefixCount Ecnt h k := by
  unfold prefixCount
  rw [Fin.sum_univ_castSucc]
  simp [sn, Fin.snoc_castSucc]
  intro h'; omega

lemma fc_snoc {m : ℕ} (h : Tr S A m) (x : Fin S × Fin A) :
    fc Ecnt (sn h x) = fc Ecnt h + Ecnt x.1 := by
  unfold fc
  rw [Fin.sum_univ_castSucc]
  simp [sn, Fin.snoc_castSucc]

/-- sums of a count-dependent per-step functional, peeled at the last step -/
lemma sumpc_snoc {m : ℕ} (f : Fin S × Fin A → ℕ → ℝ) (h : Tr S A m) (x : Fin S × Fin A) :
    ∑ t, f (sn h x t) (prefixCount Ecnt (sn h x) t) =
      ∑ t, f (h t) (prefixCount Ecnt h t) + f x (fc Ecnt h) := by
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro t _
    rw [Fin.val_castSucc, pc_snoc Ecnt h x t.is_lt.le]
    simp [sn, Fin.snoc_castSucc]
  · rw [Fin.val_last, pc_snoc Ecnt h x le_rfl, pc_full]
    simp [sn]

variable (R : Fin S → Fin A → Fin S → ℝ)

/-- one-step truncated likelihood-ratio factor -/
noncomputable def phi : (m : ℕ) → Tr S A m → Fin S → ℝ
  | 0, _, _ => 1
  | m + 1, h, s' => if prefixCount Ecnt h m < N then R (h (Fin.last m)).1 (h (Fin.last m)).2 s' else 1

/-- truncated likelihood ratio -/
noncomputable def LR : (m : ℕ) → Tr S A m → ℝ
  | 0, _ => 1
  | m + 1, h => LR m (Fin.init h) * phi Ecnt N R m (Fin.init h) (h (Fin.last m)).1

lemma LR_snoc {m : ℕ} (h : Tr S A m) (x : Fin S × Fin A) :
    LR Ecnt N R (m + 1) (sn h x) = LR Ecnt N R m h * phi Ecnt N R m h x.1 := by
  simp [LR, sn, Fin.init_snoc, Fin.snoc_last]

lemma phi_pos (hR : ∀ s a s', 0 < R s a s') (m : ℕ) (h : Tr S A m) (s : Fin S) :
    0 < phi Ecnt N R m h s := by
  cases m with
  | zero => simp [phi]
  | succ m => simp only [phi]; split_ifs <;> simp [hR]

lemma LR_pos (hR : ∀ s a s', 0 < R s a s') : ∀ (m : ℕ) (h : Tr S A m), 0 < LR Ecnt N R m h
  | 0, _ => by simp [LR]
  | m + 1, h => by
    simp only [LR]
    exact mul_pos (LR_pos hR m _) (phi_pos Ecnt N R hR m _ _)

variable (M0 M1 : FiniteMDP S A) (μ0 : MDPStateDistribution S) (π : MDPPolicy S A)
variable (hR : ∀ s a s', (M1.P s a s' : ℝ) = (M0.P s a s' : ℝ) * R s a s')
include hR

lemma phi_sum (m : ℕ) (h : Tr S A m) : ∑ s, Kw M0 μ0 m h s * phi Ecnt N R m h s = 1 := by
  cases m with
  | zero => simp only [phi, mul_one]; exact Kw_sum M0 μ0 0 h
  | succ m =>
    simp only [phi]
    split_ifs
    · simp only [Kw]
      rw [← Finset.sum_congr rfl (fun s _ => hR _ _ s)]
      exact_mod_cast M1.P_sum_one _ _
    · simp only [mul_one]; exact Kw_sum M0 μ0 _ h

omit hR in
lemma mart (m : ℕ) (hR : ∀ s a s', (M1.P s a s' : ℝ) = (M0.P s a s' : ℝ) * R s a s')
    (G : Tr S A (m + 1) → ℝ) (G' : Tr S A m → ℝ) (hG : ∀ h x, G (sn h x) = G' h) :
    ∫ h, G h * LR Ecnt N R (m + 1) h ∂(mdpMeasure M0 μ0 π (m + 1)) =
      ∫ h, G' h * LR Ecnt N R m h ∂(mdpMeasure M0 μ0 π m) := by
  rw [int_succ2]
  congr 1; funext h
  simp only [hG, LR_snoc]
  simp only [integral_const, probReal_univ, one_smul]
  rw [show (∑ s, Kw M0 μ0 m h s * (G' h * (LR Ecnt N R m h * phi Ecnt N R m h s))) =
      G' h * LR Ecnt N R m h * ∑ s, Kw M0 μ0 m h s * phi Ecnt N R m h s by
    rw [Finset.mul_sum]; congr 1; funext s; ring]
  rw [phi_sum Ecnt N R M0 M1 μ0 hR, mul_one]

omit hR in
lemma lr_id (hR : ∀ s a s', (M1.P s a s' : ℝ) = (M0.P s a s' : ℝ) * R s a s') :
    ∀ (m : ℕ) (G : Tr S A m → ℝ), (∀ h, N ≤ prefixCount Ecnt h (m - 1) → G h = 0) →
    ∫ h, G h ∂(mdpMeasure M1 μ0 π m) = ∫ h, G h * LR Ecnt N R m h ∂(mdpMeasure M0 μ0 π m)
  | 0, G, _ => by simp [int_zero, LR]
  | m + 1, G, hG => by
    have hz : ∀ h : Tr S A m, N ≤ fc Ecnt h → ∀ x, G (sn h x) = 0 := by
      intro h hh x
      apply hG
      rw [Nat.add_sub_cancel, pc_snoc Ecnt h x le_rfl, pc_full]
      exact hh
    rw [int_succ2, int_succ2]
    rw [lr_id hR m _ (by
      intro h hh
      have : N ≤ fc Ecnt h := le_trans hh (pc_le_fc Ecnt h _)
      simp [hz h this])]
    congr 1; funext h
    by_cases hN : N ≤ fc Ecnt h
    · simp [hz h hN]
    · replace hN : fc Ecnt h < N := not_le.mp hN
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s _
      simp only [LR_snoc]
      have hk : Kw M1 μ0 m h s = Kw M0 μ0 m h s * phi Ecnt N R m h s := by
        cases m with
        | zero => simp [Kw, phi]
        | succ m =>
          simp only [Kw, phi]
          rw [if_pos (lt_of_le_of_lt (pc_le_fc Ecnt h m) hN), hR]
      rw [hk]
      have : ∫ a, G (sn h (s, a)) * (LR Ecnt N R m h * phi Ecnt N R m h s) ∂(π.select m (h, s)) =
          (∫ a, G (sn h (s, a)) ∂(π.select m (h, s))) * (LR Ecnt N R m h * phi Ecnt N R m h s) :=
        integral_mul_const _ _
      rw [this]; ring


omit hR in
lemma sum_decomp {n : ℕ} (f : Fin S × Fin A → ℕ → ℝ) (h : Tr S A (n + 1)) :
    ∑ t, f (h t) (prefixCount Ecnt h t) =
      ∑ t, f (Fin.init h t) (prefixCount Ecnt (Fin.init h) t) +
        f (h (Fin.last n)) (prefixCount Ecnt h n) := by
  have e : sn (Fin.init h) (h (Fin.last n)) = h := Fin.snoc_init_self h
  have := sumpc_snoc Ecnt f (Fin.init h) (h (Fin.last n))
  rw [e] at this
  rw [this]
  congr 2
  rw [← pc_full Ecnt (Fin.init h), ← pc_snoc Ecnt (Fin.init h) (h (Fin.last n)) le_rfl, e]

omit hR in
lemma int_init' (M : FiniteMDP S A) (n : ℕ) (G : Tr S A n → ℝ) :
    ∫ h, G (Fin.init h) ∂(mdpMeasure M μ0 π (n + 1)) = ∫ h, G h ∂(mdpMeasure M μ0 π n) :=
  int_init M μ0 π n _ G (fun h x => by simp [sn, Fin.init_snoc])

omit hR in
lemma mart' (hR : ∀ s a s', (M1.P s a s' : ℝ) = (M0.P s a s' : ℝ) * R s a s') (n : ℕ)
    (G : Tr S A n → ℝ) :
    ∫ h, G (Fin.init h) * LR Ecnt N R (n + 1) h ∂(mdpMeasure M0 μ0 π (n + 1)) =
      ∫ h, G h * LR Ecnt N R n h ∂(mdpMeasure M0 μ0 π n) :=
  mart Ecnt N R M0 M1 μ0 π n hR _ G (fun h x => by simp [sn, Fin.init_snoc])

omit hR in
/-- the stopped change of measure for count-truncated additive functionals -/
lemma stopped_id (hR : ∀ s a s', (M1.P s a s' : ℝ) = (M0.P s a s' : ℝ) * R s a s')
    (f : Fin S × Fin A → ℕ → ℝ) (hf : ∀ x c, N ≤ c → f x c = 0) :
    ∀ n : ℕ, ∫ h, ∑ t, f (h t) (prefixCount Ecnt h t) ∂(mdpMeasure M1 μ0 π n) =
      ∫ h, (∑ t, f (h t) (prefixCount Ecnt h t)) * LR Ecnt N R n h ∂(mdpMeasure M0 μ0 π n)
  | 0 => by simp
  | n + 1 => by
    simp_rw [sum_decomp Ecnt f, add_mul]
    rw [integral_add Integrable.of_finite Integrable.of_finite,
      integral_add Integrable.of_finite Integrable.of_finite]
    rw [int_init' μ0 π M1 n (fun h => ∑ t, f (h t) (prefixCount Ecnt h t)),
      mart' Ecnt N R M0 M1 μ0 π hR n (fun h => ∑ t, f (h t) (prefixCount Ecnt h t)),
      stopped_id hR f hf n]
    congr 1
    apply lr_id Ecnt N R M0 M1 μ0 π hR (n + 1)
    intro h hh
    exact hf _ _ (by simpa using hh)

omit hR in
lemma LR_int (hR : ∀ s a s', (M1.P s a s' : ℝ) = (M0.P s a s' : ℝ) * R s a s') :
    ∀ n : ℕ, ∫ h, LR Ecnt N R n h ∂(mdpMeasure M0 μ0 π n) = 1
  | 0 => by simp [LR]
  | n + 1 => by
    have := mart' Ecnt N R M0 M1 μ0 π hR n (fun _ => (1:ℝ))
    simp only [one_mul] at this
    rw [this, LR_int hR n]

/-- per-pair KL between the rows -/
noncomputable def klv (s : Fin S) (a : Fin A) : ℝ := ∑ s', (M0.P s a s' : ℝ) * (-Real.log (R s a s'))

noncomputable def aw : (m : ℕ) → Tr S A m → ℝ
  | 0, _ => 0
  | m + 1, h => if prefixCount Ecnt h m < N then
      klv R M0 (h (Fin.last m)).1 (h (Fin.last m)).2 else 0

omit hR in
lemma aw_eq (m : ℕ) (h : Tr S A m) :
    ∑ s, Kw M0 μ0 m h s * (-Real.log (phi Ecnt N R m h s)) = aw Ecnt N R M0 m h := by
  cases m with
  | zero => simp [phi, aw]
  | succ m =>
    simp only [phi, aw, Kw]
    split_ifs
    · rfl
    · simp

omit hR in
lemma lr_log (hRpos : ∀ s a s', 0 < R s a s') (n : ℕ) :
    ∫ h, -Real.log (LR Ecnt N R (n + 1) h) ∂(mdpMeasure M0 μ0 π (n + 1)) =
      ∫ h, (-Real.log (LR Ecnt N R n h) + aw Ecnt N R M0 n h) ∂(mdpMeasure M0 μ0 π n) := by
  rw [int_succ2]
  congr 1; funext h
  simp only [LR_snoc, integral_const, probReal_univ, one_smul]
  rw [← aw_eq Ecnt N R M0 μ0 n h]
  have hL := LR_pos Ecnt N R hRpos n h
  have : ∀ s, Kw M0 μ0 n h s * -Real.log (LR Ecnt N R n h * phi Ecnt N R n h s) =
      Kw M0 μ0 n h s * (-Real.log (LR Ecnt N R n h)) +
        Kw M0 μ0 n h s * -Real.log (phi Ecnt N R n h s) := by
    intro s
    rw [Real.log_mul hL.ne' (phi_pos Ecnt N R hRpos n h s).ne']
    ring
  simp_rw [this]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, Kw_sum, one_mul]

/-- truncated per-step KL functional -/
noncomputable def klf (x : Fin S × Fin A) (c : ℕ) : ℝ := if c < N then klv R M0 x.1 x.2 else 0

omit hR in
lemma kl_chain (hRpos : ∀ s a s', 0 < R s a s') :
    ∀ n : ℕ, ∫ h, (-Real.log (LR Ecnt N R n h) + aw Ecnt N R M0 n h) ∂(mdpMeasure M0 μ0 π n) =
      ∫ h, ∑ t, klf N R M0 (h t) (prefixCount Ecnt h t) ∂(mdpMeasure M0 μ0 π n)
  | 0 => by simp [LR, aw]
  | n + 1 => by
    rw [integral_add Integrable.of_finite Integrable.of_finite, lr_log Ecnt N R M0 μ0 π hRpos n,
      kl_chain hRpos n]
    simp_rw [sum_decomp Ecnt (klf N R M0)]
    rw [integral_add Integrable.of_finite Integrable.of_finite,
      int_init' μ0 π M0 n (fun h => ∑ t, klf N R M0 (h t) (prefixCount Ecnt h t))]
    rfl


omit hR in
lemma pinsker_int (hR : ∀ s a s', (M1.P s a s' : ℝ) = (M0.P s a s' : ℝ) * R s a s')
    (hRpos : ∀ s a s', 0 < R s a s') (n : ℕ) {l : ℝ} (hl : 0 < l) :
    ∫ h, |LR Ecnt N R n h - 1| ∂(mdpMeasure M0 μ0 π n) ≤
      l + (∫ h, -Real.log (LR Ecnt N R n h) ∂(mdpMeasure M0 μ0 π n)) / (2 * l) := by
  have hpt : ∀ h, |LR Ecnt N R n h - 1| ≤ (l / 3 - 1 / (2 * l)) +
      ((2 * l / 3 + 1 / (2 * l)) * LR Ecnt N R n h +
        (1 / (2 * l)) * (-Real.log (LR Ecnt N R n h))) := by
    intro h
    have := pinsk_lam (LR Ecnt N R n h) l (LR_pos Ecnt N R hRpos n h) hl
    have e : l * (2 + 4 * LR Ecnt N R n h) / 6 +
        (LR Ecnt N R n h - 1 - Real.log (LR Ecnt N R n h)) / (2 * l) =
        (l / 3 - 1 / (2 * l)) + ((2 * l / 3 + 1 / (2 * l)) * LR Ecnt N R n h +
          (1 / (2 * l)) * (-Real.log (LR Ecnt N R n h))) := by
      field_simp; ring
    linarith
  calc ∫ h, |LR Ecnt N R n h - 1| ∂(mdpMeasure M0 μ0 π n)
      ≤ ∫ h, ((l / 3 - 1 / (2 * l)) + ((2 * l / 3 + 1 / (2 * l)) * LR Ecnt N R n h +
        (1 / (2 * l)) * (-Real.log (LR Ecnt N R n h)))) ∂(mdpMeasure M0 μ0 π n) :=
        integral_mono Integrable.of_finite Integrable.of_finite hpt
    _ = l + (∫ h, -Real.log (LR Ecnt N R n h) ∂(mdpMeasure M0 μ0 π n)) / (2 * l) := by
        rw [integral_add (integrable_const _) Integrable.of_finite,
          integral_add Integrable.of_finite Integrable.of_finite,
          integral_const_mul, integral_const_mul, LR_int Ecnt N R M0 M1 μ0 π hR n]
        simp only [integral_const, probReal_univ, one_smul]
        field_simp; ring

omit hR in
lemma compare (hR : ∀ s a s', (M1.P s a s' : ℝ) = (M0.P s a s' : ℝ) * R s a s')
    (n : ℕ) (F : Tr S A n → ℝ) (B : ℝ) (hF0 : ∀ h, 0 ≤ F h) (hFB : ∀ h, F h ≤ B) :
    ∫ h, F h ∂(mdpMeasure M0 μ0 π n) - B / 2 * ∫ h, |LR Ecnt N R n h - 1| ∂(mdpMeasure M0 μ0 π n)
      ≤ ∫ h, F h * LR Ecnt N R n h ∂(mdpMeasure M0 μ0 π n) := by
  have hpt : ∀ h, F h - B / 2 * |LR Ecnt N R n h - 1| + B / 2 * (LR Ecnt N R n h - 1) ≤
      F h * LR Ecnt N R n h := by
    intro h
    have h1 : |(F h - B / 2) * (LR Ecnt N R n h - 1)| ≤ B / 2 * |LR Ecnt N R n h - 1| := by
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      rw [abs_le]; constructor <;> linarith [hF0 h, hFB h]
    have h2 := neg_abs_le ((F h - B / 2) * (LR Ecnt N R n h - 1))
    nlinarith
  have := integral_mono (μ := mdpMeasure M0 μ0 π n) Integrable.of_finite Integrable.of_finite hpt
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_sub Integrable.of_finite Integrable.of_finite, integral_const_mul, integral_const_mul,
    integral_sub Integrable.of_finite (integrable_const _), LR_int Ecnt N R M0 M1 μ0 π hR n] at this
  simp only [integral_const, probReal_univ, one_smul, sub_self, mul_zero, add_zero] at this
  exact this

end LR

lemma Kw_nonneg (M : FiniteMDP S A) (μ0 : MDPStateDistribution S) (m : ℕ) (h : Tr S A m) (s : Fin S) :
    0 ≤ Kw M μ0 m h s := by
  cases m <;> simp [Kw]

/-- supermartingale bound for count-and-time dependent potentials -/
theorem supermart (M : FiniteMDP S A) (π : MDPPolicy S A) (s0 : Fin S) (Ecnt : Fin S → ℕ)
    (w : Fin S → ℕ → ℕ → ℝ)
    (hw : ∀ s a c t, ∑ s', (M.P s a s' : ℝ) * w s' (c + Ecnt s) (t + 1) ≤ w s c t) :
    ∀ m : ℕ, ∫ h, ∑ s', (M.P (h (Fin.last m)).1 (h (Fin.last m)).2 s' : ℝ) *
        w s' (fc Ecnt h) (m + 1) ∂(mdpMeasure M (mdpStateDirac s0) π (m + 1)) ≤ w s0 0 0
  | 0 => by
    rw [int_succ2, int_zero]
    simp only [Kw, mdpStateDirac]
    have : ∀ s : Fin S, ((if s = s0 then (1:ℝ≥0) else 0 : ℝ≥0) : ℝ) *
        ∫ a, ∑ s', (M.P ((sn (fun t ↦ t.elim0) (s, a)) (Fin.last 0)).1
            ((sn (fun t ↦ t.elim0) (s, a)) (Fin.last 0)).2 s' : ℝ) *
            w s' (fc Ecnt (sn (fun t ↦ t.elim0) (s, a))) (0 + 1)
          ∂(π.select 0 (fun t ↦ t.elim0, s)) ≤ if s = s0 then w s0 0 0 else 0 := by
      intro s
      by_cases hs : s = s0
      · rw [if_pos hs, if_pos hs]
        subst hs
        simp only [NNReal.coe_one, one_mul]
        calc _ ≤ ∫ _a, w s 0 0 ∂(π.select 0 (fun t ↦ t.elim0, s)) := by
              apply integral_mono Integrable.of_finite (integrable_const _)
              intro a
              dsimp only
              have e : sn (fun t ↦ t.elim0) (s, a) (Fin.last 0) = (s, a) := sn_last _ _
              rw [e, fc_snoc]
              have := hw s a 0 0
              simpa [fc] using this
          _ = w s 0 0 := by simp
      · simp [hs]
    calc _ ≤ ∑ s : Fin S, (if s = s0 then w s0 0 0 else 0) := Finset.sum_le_sum (fun s _ => this s)
      _ = w s0 0 0 := by simp
  | m + 1 => by
    refine le_trans ?_ (supermart M π s0 Ecnt w hw m)
    rw [int_succ2]
    apply integral_mono Integrable.of_finite Integrable.of_finite
    intro h
    simp only [Kw]
    apply Finset.sum_le_sum
    intro s _
    apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg _)
    calc _ ≤ ∫ _a, w s (fc Ecnt h) (m + 1) ∂(π.select (m + 1) (h, s)) := by
          apply integral_mono Integrable.of_finite (integrable_const _)
          intro a
          dsimp only
          rw [sn_last, fc_snoc]
          exact hw s a (fc Ecnt h) (m + 1)
      _ = w s (fc Ecnt h) (m + 1) := by simp


section Arena
open LayeredArena
variable (E : LayeredArena S A) {δ Δ : ℝ≥0} (hδ1 : δ ≤ 1) (hΔ2 : Δ ≤ 1 / 2)

lemma cases4 (s : Fin S) : s = E.good ∨ s = E.bad ∨ (s ≠ E.good ∧ s ≠ E.bad ∧ E.lvl s < E.depth) ∨
    (s ≠ E.good ∧ s ≠ E.bad ∧ ¬ E.lvl s < E.depth) := by
  by_cases hg : s = E.good
  · exact Or.inl hg
  by_cases hb : s = E.bad
  · exact Or.inr (Or.inl hb)
  by_cases hl : E.lvl s < E.depth
  · exact Or.inr (Or.inr (Or.inl ⟨hg, hb, hl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hg, hb, hl⟩))

lemma PV_good [NeZero S] (v : Fin S → ℝ) (a : Fin A) :
    ∑ s', ((E.toMDP hδ1 hΔ2).P E.good a s' : ℝ) * v s' = (1 - δ) * v E.good + δ * v E.root := by
  show ∑ s', ((E.rows δ Δ E.good a s' : ℝ≥0) : ℝ) * v s' = _
  rw [E.rows_good, sum_twoPoint_mul, NNReal.coe_sub hδ1, NNReal.coe_one]

lemma PV_bad [NeZero S] (v : Fin S → ℝ) (a : Fin A) :
    ∑ s', ((E.toMDP hδ1 hΔ2).P E.bad a s' : ℝ) * v s' = (1 - δ) * v E.bad + δ * v E.root := by
  show ∑ s', ((E.rows δ Δ E.bad a s' : ℝ≥0) : ℝ) * v s' = _
  rw [E.rows_bad, sum_twoPoint_mul, NNReal.coe_sub hδ1, NNReal.coe_one]

lemma PV_int [NeZero S] (v : Fin S → ℝ) {s : Fin S} (a : Fin A) (hg : s ≠ E.good) (hb : s ≠ E.bad)
    (hl : E.lvl s < E.depth) :
    ∑ s', ((E.toMDP hδ1 hΔ2).P s a s' : ℝ) * v s' = v (E.child s a) := by
  show ∑ s', ((E.rows δ Δ s a s' : ℝ≥0) : ℝ) * v s' = _
  rw [E.rows_internal a hg hb hl, sum_twoPoint_mul]
  simp

lemma PV_leaf [NeZero S] (v : Fin S → ℝ) {s : Fin S} (a : Fin A) (hg : s ≠ E.good) (hb : s ≠ E.bad)
    (hl : ¬ E.lvl s < E.depth) :
    ∑ s', ((E.toMDP hδ1 hΔ2).P s a s' : ℝ) * v s' =
      (E.goodProb Δ s a : ℝ) * v E.good + (1 - (E.goodProb Δ s a : ℝ)) * v E.bad := by
  show ∑ s', ((E.rows δ Δ s a s' : ℝ≥0) : ℝ) * v s' = _
  rw [E.rows_leaf a hg hb hl, sum_twoPoint_mul, NNReal.coe_sub (E.goodProb_le_one hΔ2 s a),
    NNReal.coe_one]

lemma gp_val (s : Fin S) (a : Fin A) : (E.goodProb Δ s a : ℝ) =
    1 / 2 + if s = E.specialLeaf ∧ a = E.specialAction then (Δ : ℝ) else 0 := by
  unfold LayeredArena.goodProb
  split_ifs <;> simp

lemma r_val [NeZero S] (s : Fin S) (a : Fin A) : (E.toMDP hδ1 hΔ2).r s a = if s = E.good then 1 else 0 := rfl

lemma leaf_iff (s : Fin S) : E.leafNat s = 1 ↔ s ≠ E.good ∧ s ≠ E.bad ∧ E.lvl s = E.depth := by
  unfold LayeredArena.leafNat; split_ifs with h <;> simp [h]

lemma leaf_le (s : Fin S) : E.leafNat s ≤ 1 := by
  unfold LayeredArena.leafNat; split_ifs <;> simp

lemma gain_mul (hδ0 : 0 < (δ : ℝ)) :
    E.gain δ Δ * (1 + δ * (E.depth + 1)) = 1 / 2 + Δ := by
  unfold LayeredArena.gain
  rw [div_mul_cancel₀]
  positivity

/-! ### regret potential -/

noncomputable def vR (s : Fin S) : ℝ :=
  if s = E.good then 1 / (δ : ℝ) else if s = E.bad then 0
  else (1 / 2 + (Δ : ℝ)) / δ - E.gain δ Δ * ((E.depth : ℝ) - E.lvl s + 1)

noncomputable def indR (s : Fin S) (a : Fin A) : ℝ :=
  if E.leafNat s = 1 ∧ (s, a) ≠ (E.specialLeaf, E.specialAction) then 1 else 0

lemma poissonR_pt [NeZero S] (hδ0 : 0 < (δ : ℝ)) (s : Fin S) (a : Fin A) :
    ((E.toMDP hδ1 hΔ2).r s a + (Δ / δ : ℝ) * indR E s a) +
      ∑ s', ((E.toMDP hδ1 hΔ2).P s a s' : ℝ) * vR (δ := δ) (Δ := Δ) E s' =
      E.gain δ Δ + vR (δ := δ) (Δ := Δ) E s := by
  have hG := gain_mul E (Δ := Δ) hδ0
  have vg : vR (δ := δ) (Δ := Δ) E E.good = 1 / δ := by simp [vR]
  have vb : vR (δ := δ) (Δ := Δ) E E.bad = 0 := by simp [vR, E.good_ne_bad.symm]
  have vt : ∀ s, s ≠ E.good → s ≠ E.bad → vR (δ := δ) (Δ := Δ) E s =
      (1 / 2 + (Δ : ℝ)) / δ - E.gain δ Δ * ((E.depth : ℝ) - E.lvl s + 1) := by
    intro s hg hb; simp [vR, hg, hb]
  have vroot := vt E.root E.root_ne_good E.root_ne_bad
  rw [E.lvl_root] at vroot
  rcases cases4 E s with hs | hs | ⟨hg, hb, hl⟩ | ⟨hg, hb, hl⟩
  · subst hs
    have hi : indR E E.good a = 0 := by simp [indR, leaf_iff]
    rw [PV_good, r_val, if_pos rfl, hi, vg, vroot]
    field_simp
    push_cast at hG ⊢
    linear_combination (-2 * (δ:ℝ)) * hG
  · subst hs
    have hi : indR E E.bad a = 0 := by simp [indR, leaf_iff]
    rw [PV_bad, r_val, if_neg E.good_ne_bad.symm, hi, vb, vroot]
    field_simp
    push_cast at hG ⊢
    linear_combination (-2 * (δ:ℝ)) * hG
  · have hi : indR E s a = 0 := by simp [indR, leaf_iff, hl.ne]
    have hc := E.lvl_child s a hg hb hl
    rw [PV_int E hδ1 hΔ2 _ a hg hb hl, r_val, if_neg hg, hi,
      vt _ (E.child_ne_good s a hg hb hl) (E.child_ne_bad s a hg hb hl), vt s hg hb, hc]
    push_cast
    ring
  · have hd : E.lvl s = E.depth := le_antisymm (E.lvl_le s hg hb) (not_lt.mp hl)
    rw [PV_leaf E hδ1 hΔ2 _ a hg hb hl, r_val, if_neg hg, vg, vb, vt s hg hb, hd, gp_val]
    unfold indR
    by_cases hp : s = E.specialLeaf ∧ a = E.specialAction
    · have : ¬ (E.leafNat s = 1 ∧ (s, a) ≠ (E.specialLeaf, E.specialAction)) := by
        rintro ⟨_, h⟩; exact h (by rw [hp.1, hp.2])
      rw [if_pos hp, if_neg this]
      field_simp
      ring
    · have : E.leafNat s = 1 ∧ (s, a) ≠ (E.specialLeaf, E.specialAction) := by
        refine ⟨(leaf_iff E s).mpr ⟨hg, hb, hd⟩, ?_⟩
        intro h; apply hp; simp only [Prod.mk.injEq] at h; exact h
      rw [if_neg hp, if_pos this]
      field_simp
      ring


/-! ### optimal-policy potential (the Definitions' `bias`) -/

lemma best_child {s : Fin S} (a : Fin A)
    (hp : E.onPath (E.child s a) = E.onPath s) (Δ' : ℝ) :
    E.best Δ' (E.child s a) = E.best Δ' s := by
  unfold LayeredArena.best; rw [hp]

lemma poissonB_pt [NeZero S] (hδ0 : 0 < (δ : ℝ)) (s : Fin S) :
    (E.toMDP hδ1 hΔ2).r s (E.optPolicy s) +
      ∑ s', ((E.toMDP hδ1 hΔ2).P s (E.optPolicy s) s' : ℝ) * E.bias δ Δ s' =
      E.gain δ Δ + E.bias δ Δ s := by
  have hG := gain_mul E (Δ := Δ) hδ0
  have vg : E.bias δ Δ E.good = 1 / δ := by simp [LayeredArena.bias]
  have vb : E.bias δ Δ E.bad = 0 := by simp [LayeredArena.bias, E.good_ne_bad.symm]
  have vt : ∀ s, s ≠ E.good → s ≠ E.bad → E.bias δ Δ s =
      E.best Δ s / δ - E.gain δ Δ * ((E.depth : ℝ) - E.lvl s + 1) := by
    intro s hg hb; simp [LayeredArena.bias, hg, hb]
  have vroot := vt E.root E.root_ne_good E.root_ne_bad
  rw [E.lvl_root] at vroot
  have broot : E.best Δ E.root = 1 / 2 + Δ := by simp [LayeredArena.best, E.onPath_root]
  rcases cases4 E s with hs | hs | ⟨hg, hb, hl⟩ | ⟨hg, hb, hl⟩
  · subst hs
    rw [PV_good, r_val, if_pos rfl, vg, vroot, broot]
    field_simp
    push_cast at hG ⊢
    linear_combination (-2 * (δ:ℝ)) * hG
  · subst hs
    rw [PV_bad, r_val, if_neg E.good_ne_bad.symm, vb, vroot, broot]
    field_simp
    push_cast at hG ⊢
    linear_combination (-2 : ℝ) * hG
  · have ho : E.optPolicy s = E.pathAction s := by
      simp [LayeredArena.optPolicy, hg, hb, hl]
    have hc := E.lvl_child s (E.pathAction s) hg hb hl
    have hp : E.onPath (E.child s (E.pathAction s)) = E.onPath s := by
      cases h : E.onPath s
      · cases h' : E.onPath (E.child s (E.pathAction s))
        · rfl
        · have := E.onPath_child_mp s _ hg hb hl h'; rw [h] at this; exact this.symm
      · exact E.onPath_child_mpr s hg hb hl h
    rw [ho, PV_int E hδ1 hΔ2 _ _ hg hb hl, r_val, if_neg hg,
      vt _ (E.child_ne_good s _ hg hb hl) (E.child_ne_bad s _ hg hb hl), vt s hg hb, hc,
      best_child E _ hp]
    push_cast
    ring
  · have hd : E.lvl s = E.depth := le_antisymm (E.lvl_le s hg hb) (not_lt.mp hl)
    rw [PV_leaf E hδ1 hΔ2 _ _ hg hb hl, r_val, if_neg hg, vg, vb, vt s hg hb, hd, gp_val]
    by_cases hsp : s = E.specialLeaf
    · have ho : E.optPolicy s = E.specialAction := by
        simp [LayeredArena.optPolicy, hsp, E.specialLeaf_ne_good, E.specialLeaf_ne_bad,
          E.specialLeaf_lvl]
      have hb' : E.best Δ s = 1 / 2 + Δ := by
        rw [hsp]; simp [LayeredArena.best, E.onPath_specialLeaf]
      rw [ho, if_pos ⟨hsp, rfl⟩, hb']
      field_simp
      ring
    · have hp : E.onPath s = false := by
        cases h : E.onPath s
        · rfl
        · exact absurd (E.onPath_leaf s hg hb hd h) hsp
      have hb' : E.best Δ s = 1 / 2 := by simp [LayeredArena.best, hp]
      rw [if_neg (fun h => hsp h.1), hb']
      field_simp
      ring

/-! ### leaf-count potential -/

noncomputable def uL (s : Fin S) : ℝ :=
  if s = E.good ∨ s = E.bad then -(1 / ((δ : ℝ) * E.epiLen δ)) else (E.lvl s : ℝ) / E.epiLen δ

lemma epiLen_pos (hδ0 : 0 < (δ : ℝ)) : 0 < E.epiLen δ := by
  unfold LayeredArena.epiLen; positivity

lemma poissonL_pt [NeZero S] (hδ0 : 0 < (δ : ℝ)) (s : Fin S) (a : Fin A) :
    (E.leafNat s : ℝ) + ∑ s', ((E.toMDP hδ1 hΔ2).P s a s' : ℝ) * uL (δ := δ) E s' =
      1 / E.epiLen δ + uL (δ := δ) E s := by
  have he := epiLen_pos E hδ0
  have ug : uL (δ := δ) E E.good = -(1 / ((δ : ℝ) * E.epiLen δ)) := by simp [uL]
  have ub : uL (δ := δ) E E.bad = -(1 / ((δ : ℝ) * E.epiLen δ)) := by simp [uL]
  have ut : ∀ s, s ≠ E.good → s ≠ E.bad → uL (δ := δ) E s = (E.lvl s : ℝ) / E.epiLen δ := by
    intro s hg hb; simp [uL, hg, hb]
  have ur := ut E.root E.root_ne_good E.root_ne_bad
  rw [E.lvl_root] at ur
  have l0 : ∀ s, ¬ (s ≠ E.good ∧ s ≠ E.bad ∧ E.lvl s = E.depth) → (E.leafNat s : ℝ) = 0 := by
    intro s h; simp [LayeredArena.leafNat, h]
  rcases cases4 E s with hs | hs | ⟨hg, hb, hl⟩ | ⟨hg, hb, hl⟩
  · subst hs
    rw [PV_good, l0 _ (by simp), ug, ur]
    field_simp
    ring
  · subst hs
    rw [PV_bad, l0 _ (by simp), ub, ur, ← ug]
    rw [ug]
    field_simp
    ring
  · have hc := E.lvl_child s a hg hb hl
    rw [PV_int E hδ1 hΔ2 _ a hg hb hl, l0 _ (by omega),
      ut _ (E.child_ne_good s a hg hb hl) (E.child_ne_bad s a hg hb hl), ut s hg hb, hc]
    push_cast
    field_simp
    ring
  · have hd : E.lvl s = E.depth := le_antisymm (E.lvl_le s hg hb) (not_lt.mp hl)
    have l1 : (E.leafNat s : ℝ) = 1 := by
      have := (leaf_iff E s).mpr ⟨hg, hb, hd⟩; exact_mod_cast this
    rw [PV_leaf E hδ1 hΔ2 _ _ hg hb hl, l1, ug, ub, ut s hg hb, hd]
    have : E.epiLen δ = 1 / δ + E.depth + 1 := rfl
    rw [this]
    field_simp
    ring

/-! ### tail supermartingale potential -/

noncomputable def rho (δ : ℝ) : ℝ := 2 / (1 + δ)

noncomputable def wT (N : ℕ) (s : Fin S) (c t : ℕ) : ℝ :=
  if c < N then
    (if s = E.good ∨ s = E.bad then
      mx δ ^ (t + 1 + E.depth + (N - 1 - c) * (E.depth + 2)) * rho δ ^ (N - c)
    else mx δ ^ (t + (E.depth - E.lvl s) + (N - 1 - c) * (E.depth + 2)) * rho δ ^ (N - 1 - c))
  else 0

lemma wT_nonneg (N : ℕ) (s : Fin S) (c t : ℕ) : 0 ≤ wT (δ := δ) E N s c t := by
  unfold wT rho mx; split_ifs <;> positivity

lemma tail_pt [NeZero S] (N : ℕ) (s : Fin S) (a : Fin A) (c t : ℕ) :
    ∑ s', ((E.toMDP hδ1 hΔ2).P s a s' : ℝ) * wT (δ := δ) E N s' (c + E.leafNat s) (t + 1) ≤
      wT (δ := δ) E N s c t := by
  have hx : (0:ℝ) < mx δ := by unfold mx; positivity
  have hρ : (0:ℝ) < rho δ := by unfold rho; positivity
  have key : (1 - (δ:ℝ)) * mx δ * rho δ + δ = rho δ := by
    unfold mx rho
    have : (0:ℝ) < 1 + δ := by positivity
    field_simp
    ring
  by_cases hc : c < N
  swap
  · have : ∀ s' j, wT (δ := δ) E N s' (c + j) (t + 1) = 0 := by
      intro s' j; simp [wT]; omega
    rw [Finset.sum_eq_zero (fun s' _ => by rw [this, mul_zero])]
    exact wT_nonneg E N s c t
  have l0 : ∀ s, ¬ (s ≠ E.good ∧ s ≠ E.bad ∧ E.lvl s = E.depth) → E.leafNat s = 0 := by
    intro s h; simp [LayeredArena.leafNat, h]
  have wgb : ∀ s', (s' = E.good ∨ s' = E.bad) → ∀ c' t', c' < N → wT (δ := δ) E N s' c' t' =
      mx δ ^ (t' + 1 + E.depth + (N - 1 - c') * (E.depth + 2)) * rho δ ^ (N - c') := by
    intro s' hs' c' t' hc'; simp [wT, hc', hs']
  have wtr : ∀ s', s' ≠ E.good → s' ≠ E.bad → ∀ c' t', c' < N → wT (δ := δ) E N s' c' t' =
      mx δ ^ (t' + (E.depth - E.lvl s') + (N - 1 - c') * (E.depth + 2)) * rho δ ^ (N - 1 - c') := by
    intro s' hg hb c' t' hc'; simp [wT, hc', hg, hb]
  have hNc : N - c = (N - 1 - c) + 1 := by omega
  rcases cases4 E s with hs | hs | ⟨hg, hb, hl⟩ | ⟨hg, hb, hl⟩
  · subst hs
    rw [l0 _ (by simp), add_zero, PV_good, wgb _ (Or.inl rfl) c _ hc, wgb _ (Or.inl rfl) c _ hc,
      wtr _ E.root_ne_good E.root_ne_bad c _ hc, E.lvl_root, Nat.sub_zero]
    apply le_of_eq
    rw [hNc, pow_succ, show t + 1 + 1 + E.depth + (N - 1 - c) * (E.depth + 2) =
      (t + 1 + E.depth + (N - 1 - c) * (E.depth + 2)) + 1 by ring, pow_succ,
      show t + 1 + E.depth = t + 1 + (E.depth) from rfl]
    linear_combination (mx δ ^ (t + 1 + E.depth + (N - 1 - c) * (E.depth + 2)) *
      rho δ ^ (N - 1 - c)) * key
  · subst hs
    rw [l0 _ (by simp), add_zero, PV_bad, wgb _ (Or.inr rfl) c _ hc, wgb _ (Or.inr rfl) c _ hc,
      wtr _ E.root_ne_good E.root_ne_bad c _ hc, E.lvl_root, Nat.sub_zero]
    apply le_of_eq
    rw [hNc, pow_succ, show t + 1 + 1 + E.depth + (N - 1 - c) * (E.depth + 2) =
      (t + 1 + E.depth + (N - 1 - c) * (E.depth + 2)) + 1 by ring, pow_succ]
    linear_combination (mx δ ^ (t + 1 + E.depth + (N - 1 - c) * (E.depth + 2)) *
      rho δ ^ (N - 1 - c)) * key
  · have hcl := E.lvl_child s a hg hb hl
    rw [l0 _ (by omega), add_zero, PV_int E hδ1 hΔ2 _ a hg hb hl,
      wtr _ (E.child_ne_good s a hg hb hl) (E.child_ne_bad s a hg hb hl) c _ hc,
      wtr s hg hb c _ hc, hcl]
    apply le_of_eq
    congr 2
    omega
  · have hd : E.lvl s = E.depth := le_antisymm (E.lvl_le s hg hb) (not_lt.mp hl)
    have l1 : E.leafNat s = 1 := (leaf_iff E s).mpr ⟨hg, hb, hd⟩
    rw [l1, PV_leaf E hδ1 hΔ2 _ _ hg hb hl, wtr s hg hb c _ hc, hd, Nat.sub_self]
    by_cases hc1 : c + 1 < N
    · rw [wgb _ (Or.inl rfl) _ _ hc1, wgb _ (Or.inr rfl) _ _ hc1]
      apply le_of_eq
      obtain ⟨j, hj⟩ : ∃ j, N - 1 - c = j + 1 := ⟨N - 2 - c, by omega⟩
      have e1 : N - (c + 1) = N - 1 - c := by omega
      have e2 : N - 1 - (c + 1) = j := by omega
      rw [e1, e2, hj]
      have e3 : t + 1 + 1 + E.depth + j * (E.depth + 2) = t + 0 + (j + 1) * (E.depth + 2) := by ring
      rw [e3]
      ring
    · have hz : ∀ s', wT (δ := δ) E N s' (c + 1) (t + 1) = 0 := by
        intro s'; simp [wT, hc1]
      rw [hz, hz]
      simp only [mul_zero, add_zero]
      positivity


/-! ### the optimal gain is at least `gain` -/

lemma rew_bounds (M : FiniteMDP S A) (μ0 : MDPStateDistribution S) (π : MDPPolicy S A) (n : ℕ) :
    0 ≤ mdpExpectedReward M μ0 π n ∧ mdpExpectedReward M μ0 π n ≤ n := by
  unfold mdpExpectedReward mdpTrajectoryReward
  constructor
  · apply integral_nonneg; intro h
    exact Finset.sum_nonneg (fun t _ => (M.r_mem_Icc _ _).1)
  · calc _ ≤ ∫ _h, (n : ℝ) ∂(mdpMeasure M μ0 π n) := by
          apply integral_mono Integrable.of_finite (integrable_const _)
          intro h
          calc ∑ t, M.r (h t).1 (h t).2 ≤ ∑ _t : Fin n, (1 : ℝ) :=
                Finset.sum_le_sum (fun t _ => (M.r_mem_Icc _ _).2)
            _ = n := by simp
      _ = n := by simp

lemma gainfun_bounds (M : FiniteMDP S A) (μ0 : MDPStateDistribution S) (π : MDPPolicy S A) (n : ℕ) :
    0 ≤ mdpExpectedReward M μ0 π n / n ∧ mdpExpectedReward M μ0 π n / n ≤ 1 := by
  obtain ⟨h0, h1⟩ := rew_bounds M μ0 π n
  exact ⟨div_nonneg h0 (Nat.cast_nonneg _), div_le_one_of_le₀ h1 (Nat.cast_nonneg _)⟩

lemma mdpGain_le_one (M : FiniteMDP S A) (π : MDPPolicy S A) (s : Fin S) : mdpGain M π s ≤ 1 := by
  unfold mdpGain
  apply Filter.limsup_le_of_le
  · exact Filter.isCoboundedUnder_le_of_le _ (fun n => (gainfun_bounds M _ π n).1)
  · exact Filter.Eventually.of_forall (fun n => (gainfun_bounds M _ π n).2)

lemma optgain_ge_of (M : FiniteMDP S A) (π : MDPPolicy S A) (s0 : Fin S) (g C : ℝ)
    (h : ∀ m : ℕ, ((m : ℝ) + 1) * g - C ≤ mdpExpectedReward M (mdpStateDirac s0) π (m + 1)) :
    g ≤ mdpOptimalGain M := by
  have hbd : ∀ s, BddAbove (Set.range fun π : MDPPolicy S A => mdpGain M π s) :=
    fun s => ⟨1, by rintro _ ⟨π, rfl⟩; exact mdpGain_le_one M π s⟩
  have hbd2 : BddAbove (Set.range fun s : Fin S => ⨆ π : MDPPolicy S A, mdpGain M π s) :=
    ⟨1, by rintro _ ⟨s, rfl⟩; exact Real.iSup_le (fun π => mdpGain_le_one M π s) zero_le_one⟩
  refine le_trans ?_ (le_ciSup_of_le hbd2 s0 (le_ciSup (hbd s0) π))
  unfold mdpGain
  apply le_of_forall_pos_le_add
  intro η hη
  have hev : ∀ᶠ n : ℕ in Filter.atTop, g - η ≤ mdpExpectedReward M (mdpStateDirac s0) π n / n := by
    rw [Filter.eventually_atTop]
    refine ⟨⌈|C| / η⌉₊ + 1, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm := h m
    have hpos : (0:ℝ) < (m : ℝ) + 1 := by positivity
    have hc : |C| / η ≤ (m : ℝ) + 1 := by
      have := Nat.le_ceil (|C| / η)
      have h2 : ((⌈|C| / η⌉₊ + 1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast hn
      push_cast at h2
      linarith
    rw [Nat.cast_add, Nat.cast_one, le_div_iff₀ hpos]
    have : |C| ≤ η * ((m : ℝ) + 1) := by rwa [div_le_iff₀ hη, mul_comm] at hc
    nlinarith [le_abs_self C]
  have := Filter.le_limsup_of_frequently_le hev.frequently
    (Filter.isBoundedUnder_of ⟨1, fun n => (gainfun_bounds M _ π n).2⟩)
  linarith

lemma bias_le [NeZero S] (hδ0 : 0 < (δ : ℝ)) (s : Fin S) :
    E.bias δ Δ s ≤ 1 / δ + (1 / 2 + Δ) / δ := by
  have hg0 : 0 ≤ E.gain δ Δ := by unfold LayeredArena.gain; positivity
  unfold LayeredArena.bias
  split_ifs with h1 h2
  · have : (0:ℝ) ≤ (1 / 2 + Δ) / δ := by positivity
    linarith
  · positivity
  · have hl := E.lvl_le s h1 h2
    have hl' : (E.lvl s : ℝ) ≤ E.depth := by exact_mod_cast hl
    have hb : E.best Δ s ≤ 1 / 2 + Δ := by
      unfold LayeredArena.best; split_ifs <;> simp
    have : 0 ≤ E.gain δ Δ * ((E.depth : ℝ) - E.lvl s + 1) := mul_nonneg hg0 (by linarith)
    have : E.best Δ s / δ ≤ (1 / 2 + Δ) / δ := div_le_div_of_nonneg_right hb hδ0.le
    have : (0:ℝ) ≤ 1 / δ := by positivity
    linarith

theorem optgain [NeZero S] (hδ0 : 0 < (δ : ℝ)) :
    E.gain δ Δ ≤ mdpOptimalGain (E.toMDP hδ1 hΔ2) := by
  set M := E.toMDP hδ1 hΔ2
  set π := mdpMemorylessDetPolicy (S := S) (A := A) E.optPolicy
  have hP : ∀ m (h : Tr S A m) s,
      ∫ a, (M.r s a + ∑ s', (M.P s a s' : ℝ) * E.bias δ Δ s') ∂(π.select m (h, s)) =
        E.gain δ Δ + E.bias δ Δ s := by
    intro m h s
    simp only [π, mdpMemorylessDetPolicy, Kernel.deterministic_apply]
    rw [integral_dirac]
    exact poissonB_pt E hδ1 hΔ2 hδ0 s
  apply optgain_ge_of M π E.root (E.gain δ Δ) (1 / δ + (1 / 2 + Δ) / δ - E.bias δ Δ E.root)
  intro m
  have hp := poisson M π E.root M.r (E.bias δ Δ) (E.gain δ Δ) hP m
  rw [integral_add Integrable.of_finite Integrable.of_finite] at hp
  have hPV : ∫ h, ∑ s', (M.P (h (Fin.last m)).1 (h (Fin.last m)).2 s' : ℝ) * E.bias δ Δ s'
      ∂(mdpMeasure M (mdpStateDirac E.root) π (m + 1)) ≤ 1 / δ + (1 / 2 + Δ) / δ := by
    calc _ ≤ ∫ _h, (1 / δ + (1 / 2 + Δ) / δ : ℝ) ∂(mdpMeasure M (mdpStateDirac E.root) π (m + 1)) := by
          apply integral_mono Integrable.of_finite (integrable_const _)
          intro h
          calc ∑ s', (M.P (h (Fin.last m)).1 (h (Fin.last m)).2 s' : ℝ) * E.bias δ Δ s'
              ≤ ∑ s', (M.P (h (Fin.last m)).1 (h (Fin.last m)).2 s' : ℝ) *
                  (1 / δ + (1 / 2 + Δ) / δ : ℝ) :=
                Finset.sum_le_sum (fun s' _ => mul_le_mul_of_nonneg_left (bias_le E hδ0 s')
                  (NNReal.coe_nonneg _))
            _ = 1 / δ + (1 / 2 + Δ) / δ := by
                rw [← Finset.sum_mul]
                rw [show (∑ i, (M.P (h (Fin.last m)).1 (h (Fin.last m)).2 i : ℝ)) = 1 by
                  exact_mod_cast M.P_sum_one _ _, one_mul]
      _ = 1 / δ + (1 / 2 + Δ) / δ := by simp
  unfold mdpExpectedReward mdpTrajectoryReward
  linarith


/-! ### regret decomposition -/

theorem regret_lb [NeZero S] (hδ0 : 0 < (δ : ℝ)) (π : MDPPolicy S A) (m : ℕ) :
    (Δ / δ : ℝ) * ∫ h, ∑ t, indR E (h t).1 (h t).2
        ∂(mdpMeasure (E.toMDP hδ1 hΔ2) (mdpStateDirac E.root) π (m + 1)) - (1 / 2 + Δ) / δ ≤
      ∫ h, mdpRegret (E.toMDP hδ1 hΔ2) (m + 1) h
        ∂(mdpMeasure (E.toMDP hδ1 hΔ2) (mdpStateDirac E.root) π (m + 1)) := by
  set M := E.toMDP hδ1 hΔ2
  have hP : ∀ m (h : Tr S A m) s,
      ∫ a, ((M.r s a + (Δ / δ : ℝ) * indR E s a) + ∑ s', (M.P s a s' : ℝ) * vR (δ := δ) (Δ := Δ) E s')
        ∂(π.select m (h, s)) = E.gain δ Δ + vR (δ := δ) (Δ := Δ) E s := by
    intro m h s
    calc _ = ∫ _a, (E.gain δ Δ + vR (δ := δ) (Δ := Δ) E s) ∂(π.select m (h, s)) :=
          integral_congr_ae (Filter.Eventually.of_forall (fun a => poissonR_pt E hδ1 hΔ2 hδ0 s a))
      _ = _ := by simp
  have hp := poisson M π E.root (fun s a => M.r s a + (Δ / δ : ℝ) * indR E s a)
    (vR (δ := δ) (Δ := Δ) E) (E.gain δ Δ) hP m
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hp
  rw [integral_add Integrable.of_finite Integrable.of_finite,
    integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul] at hp
  have hg0 : 0 ≤ E.gain δ Δ := by unfold LayeredArena.gain; positivity
  have vroot : vR (δ := δ) (Δ := Δ) E E.root = (1 / 2 + Δ) / δ - E.gain δ Δ * (E.depth + 1) := by
    simp [vR, E.root_ne_good, E.root_ne_bad, E.lvl_root]
  have vlow : ∀ s, -(E.gain δ Δ * (E.depth + 1)) ≤ vR (δ := δ) (Δ := Δ) E s := by
    intro s
    have : 0 ≤ E.gain δ Δ * (E.depth + 1) := by positivity
    unfold vR
    split_ifs with h1 h2
    · have : (0:ℝ) ≤ 1 / δ := by positivity
      linarith
    · linarith
    · have hl := E.lvl_le s h1 h2
      have hl' : (E.lvl s : ℝ) ≤ E.depth := by exact_mod_cast hl
      have : E.gain δ Δ * ((E.depth : ℝ) - E.lvl s + 1) ≤ E.gain δ Δ * (E.depth + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [(Nat.cast_nonneg (E.lvl s) : (0:ℝ) ≤ E.lvl s)]) hg0
      have : (0:ℝ) ≤ (1 / 2 + Δ) / δ := by positivity
      linarith
  have hPV : -(E.gain δ Δ * (E.depth + 1)) ≤ ∫ h, ∑ s', (M.P (h (Fin.last m)).1 (h (Fin.last m)).2 s' : ℝ) *
      vR (δ := δ) (Δ := Δ) E s' ∂(mdpMeasure M (mdpStateDirac E.root) π (m + 1)) := by
    calc -(E.gain δ Δ * (E.depth + 1)) = ∫ _h, -(E.gain δ Δ * (E.depth + 1)) ∂(mdpMeasure M (mdpStateDirac E.root) π (m + 1)) := by simp
      _ ≤ _ := by
        apply integral_mono (integrable_const _) Integrable.of_finite
        intro h
        calc -(E.gain δ Δ * (E.depth + 1))
            = ∑ s', (M.P (h (Fin.last m)).1 (h (Fin.last m)).2 s' : ℝ) *
                -(E.gain δ Δ * (E.depth + 1)) := by
              rw [← Finset.sum_mul, show (∑ i, (M.P (h (Fin.last m)).1 (h (Fin.last m)).2 i : ℝ)) = 1
                by exact_mod_cast M.P_sum_one _ _, one_mul]
          _ ≤ _ := Finset.sum_le_sum (fun s' _ => mul_le_mul_of_nonneg_left (vlow s')
                (NNReal.coe_nonneg _))
  have hopt := optgain E hδ1 hΔ2 hδ0
  have hreg : ∫ h, mdpRegret M (m + 1) h ∂(mdpMeasure M (mdpStateDirac E.root) π (m + 1)) =
      ((m + 1 : ℕ) : ℝ) * mdpOptimalGain M - ∫ h, ∑ t, M.r (h t).1 (h t).2 ∂(mdpMeasure M (mdpStateDirac E.root) π (m + 1)) := by
    unfold mdpRegret mdpTrajectoryReward
    rw [integral_sub (integrable_const _) Integrable.of_finite]
    simp
  rw [hreg]
  rw [vroot] at hp
  push_cast at hp ⊢
  have : ((m : ℝ) + 1) * E.gain δ Δ ≤ ((m : ℝ) + 1) * mdpOptimalGain M :=
    mul_le_mul_of_nonneg_left hopt (by positivity)
  linarith

/-! ### expected leaf count -/

theorem leafcount [NeZero S] (hδ0 : 0 < (δ : ℝ)) (π : MDPPolicy S A) (m : ℕ) :
    ∫ h, (fc E.leafNat h : ℝ) ∂(mdpMeasure (E.toMDP hδ1 hΔ2) (mdpStateDirac E.root) π (m + 1)) ≤
      (((m + 1 : ℕ) : ℝ) + 1 / δ) / E.epiLen δ := by
  set M := E.toMDP hδ1 hΔ2
  have he := epiLen_pos E hδ0
  have hP : ∀ m (h : Tr S A m) s,
      ∫ a, ((E.leafNat s : ℝ) + ∑ s', (M.P s a s' : ℝ) * uL (δ := δ) E s')
        ∂(π.select m (h, s)) = 1 / E.epiLen δ + uL (δ := δ) E s := by
    intro m h s
    calc _ = ∫ _a, (1 / E.epiLen δ + uL (δ := δ) E s) ∂(π.select m (h, s)) :=
          integral_congr_ae (Filter.Eventually.of_forall (fun a => poissonL_pt E hδ1 hΔ2 hδ0 s a))
      _ = _ := by simp
  have hp := poisson M π E.root (fun s _ => (E.leafNat s : ℝ)) (uL (δ := δ) E) _ hP m
  rw [integral_add Integrable.of_finite Integrable.of_finite] at hp
  have ur : uL (δ := δ) E E.root = 0 := by simp [uL, E.root_ne_good, E.root_ne_bad, E.lvl_root]
  have ulow : ∀ s, -(1 / ((δ : ℝ) * E.epiLen δ)) ≤ uL (δ := δ) E s := by
    intro s; unfold uL; split_ifs
    · exact le_rfl
    · have : (0:ℝ) ≤ 1 / ((δ : ℝ) * E.epiLen δ) := by positivity
      have : (0:ℝ) ≤ (E.lvl s : ℝ) / E.epiLen δ := by positivity
      linarith
  have hPV : -(1 / ((δ : ℝ) * E.epiLen δ)) ≤ ∫ h, ∑ s', (M.P (h (Fin.last m)).1 (h (Fin.last m)).2 s' : ℝ) *
      uL (δ := δ) E s' ∂(mdpMeasure M (mdpStateDirac E.root) π (m + 1)) := by
    calc -(1 / ((δ : ℝ) * E.epiLen δ)) = ∫ _h, -(1 / ((δ : ℝ) * E.epiLen δ)) ∂(mdpMeasure M (mdpStateDirac E.root) π (m + 1)) := by simp
      _ ≤ _ := by
        apply integral_mono (integrable_const _) Integrable.of_finite
        intro h
        calc -(1 / ((δ : ℝ) * E.epiLen δ))
            = ∑ s', (M.P (h (Fin.last m)).1 (h (Fin.last m)).2 s' : ℝ) *
                -(1 / ((δ : ℝ) * E.epiLen δ)) := by
              rw [← Finset.sum_mul, show (∑ i, (M.P (h (Fin.last m)).1 (h (Fin.last m)).2 i : ℝ)) = 1
                by exact_mod_cast M.P_sum_one _ _, one_mul]
          _ ≤ _ := Finset.sum_le_sum (fun s' _ => mul_le_mul_of_nonneg_left (ulow s')
                (NNReal.coe_nonneg _))
  have hfc : ∀ h : Tr S A (m + 1), (fc E.leafNat h : ℝ) = ∑ t, (E.leafNat (h t).1 : ℝ) := by
    intro h; simp [fc]
  simp_rw [hfc]
  rw [ur] at hp
  have e : (((m + 1 : ℕ) : ℝ) + 1 / δ) / E.epiLen δ =
      ((m : ℝ) + 1) * (1 / E.epiLen δ) + 1 / ((δ : ℝ) * E.epiLen δ) := by
    push_cast; field_simp
  rw [e]
  linarith

/-! ### tail bound on the leaf count -/

lemma one_le_mx (hδ0 : 0 ≤ (δ : ℝ)) : 1 ≤ mx δ := by unfold mx; linarith
lemma one_le_rho (hδ1' : (δ : ℝ) ≤ 1) (hδ0 : 0 ≤ (δ : ℝ)) : 1 ≤ rho δ := by
  unfold rho; rw [le_div_iff₀ (by linarith)]; linarith

lemma wT_ge (N : ℕ) (s : Fin S) (c t : ℕ) (hc : c < N) (hδ1' : (δ : ℝ) ≤ 1) :
    mx δ ^ t ≤ wT (δ := δ) E N s c t := by
  have hx := one_le_mx (δ := δ) (NNReal.coe_nonneg δ)
  have hρ := one_le_rho (δ := δ) hδ1' (NNReal.coe_nonneg δ)
  unfold wT
  rw [if_pos hc]
  split_ifs
  · calc mx δ ^ t ≤ mx δ ^ (t + 1 + E.depth + (N - 1 - c) * (E.depth + 2)) :=
          pow_le_pow_right₀ hx (by omega)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hρ)
  · calc mx δ ^ t ≤ mx δ ^ (t + (E.depth - E.lvl s) + (N - 1 - c) * (E.depth + 2)) :=
          pow_le_pow_right₀ hx (by omega)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hρ)

theorem tail [NeZero S] (N : ℕ) (hN : 0 < N) (π : MDPPolicy S A) (m : ℕ) :
    mx δ ^ (m + 1) * ∫ h, (if fc E.leafNat h < N then (1:ℝ) else 0)
        ∂(mdpMeasure (E.toMDP hδ1 hΔ2) (mdpStateDirac E.root) π (m + 1)) ≤
      mx δ ^ (E.depth + (N - 1) * (E.depth + 2)) * rho δ ^ (N - 1) := by
  set M := E.toMDP hδ1 hΔ2
  have hsm := supermart M π E.root E.leafNat (wT (δ := δ) E N) (tail_pt E hδ1 hΔ2 N) m
  have hw0 : wT (δ := δ) E N E.root 0 0 =
      mx δ ^ (E.depth + (N - 1) * (E.depth + 2)) * rho δ ^ (N - 1) := by
    simp [wT, hN, E.root_ne_good, E.root_ne_bad, E.lvl_root]
  rw [hw0] at hsm
  refine le_trans ?_ hsm
  rw [← integral_const_mul]
  apply integral_mono Integrable.of_finite Integrable.of_finite
  intro h
  have hδ1' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  dsimp only
  split_ifs with hc
  · rw [mul_one]
    calc mx δ ^ (m + 1) = ∑ s', (M.P (h (Fin.last m)).1 (h (Fin.last m)).2 s' : ℝ) * mx δ ^ (m + 1) := by
          rw [← Finset.sum_mul, show (∑ i, (M.P (h (Fin.last m)).1 (h (Fin.last m)).2 i : ℝ)) = 1
            by exact_mod_cast M.P_sum_one _ _, one_mul]
      _ ≤ _ := Finset.sum_le_sum (fun s' _ => mul_le_mul_of_nonneg_left
            (wT_ge E N s' _ _ hc hδ1') (NNReal.coe_nonneg _))
  · rw [mul_zero]
    exact Finset.sum_nonneg (fun s' _ => mul_nonneg (NNReal.coe_nonneg _) (wT_nonneg E N s' _ _))

end Arena

/-- the truncated leaf count equals `min (count, N)` -/
lemma gcount (Ecnt : Fin S → ℕ) (hE : ∀ s, Ecnt s ≤ 1) (N : ℕ) :
    ∀ n (h : Tr S A n), ∑ t, (if Ecnt (h t).1 = 1 ∧ prefixCount Ecnt h t < N then (1:ℝ) else 0) =
      ((min (fc Ecnt h) N : ℕ) : ℝ)
  | 0, h => by simp [fc]
  | n + 1, h => by
    have := sum_decomp Ecnt (fun x c => if Ecnt x.1 = 1 ∧ c < N then (1:ℝ) else 0) h
    rw [this, gcount Ecnt hE N n]
    have e1 : prefixCount Ecnt h n = fc Ecnt (Fin.init h) := by
      conv_lhs => rw [← Fin.snoc_init_self h]
      exact (pc_snoc Ecnt (Fin.init h) (h (Fin.last n)) le_rfl).trans (pc_full Ecnt _)
    have e2 : fc Ecnt h = fc Ecnt (Fin.init h) + Ecnt (h (Fin.last n)).1 := by
      conv_lhs => rw [← Fin.snoc_init_self h]
      exact fc_snoc Ecnt (Fin.init h) (h (Fin.last n))
    rw [e1, e2]
    have := hE (h (Fin.last n)).1
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h0 | h1
    · rw [h0]; simp
    · rw [h1]
      split_ifs with hc
      · have : min (fc Ecnt (Fin.init h) + 1) N = min (fc Ecnt (Fin.init h)) N + 1 := by omega
        rw [this]; push_cast; ring
      · have : min (fc Ecnt (Fin.init h) + 1) N = min (fc Ecnt (Fin.init h)) N := by
          omega
        rw [this]; simp
        
section Fam
open LayeredArena
variable [NeZero S] (E₀ E : LayeredArena S A) (p : Fin S × Fin A) (N : ℕ)
variable (hg : E₀.good = E.good) (hb : E₀.bad = E.bad) (hr : E₀.root = E.root)
  (hl : E₀.lvl = E.lvl) (hd : E₀.depth = E.depth) (hc : E₀.child = E.child)

include hg hb hl hd in
lemma leafNat_congr : E.leafNat = E₀.leafNat := by
  funext s; unfold LayeredArena.leafNat; rw [hg, hb, hl, hd]

include hg hb hr hl hd hc in
lemma rows_congr (δ Δ Δ' : ℝ≥0) (s : Fin S) (a : Fin A)
    (hq : E.goodProb Δ s a = E₀.goodProb Δ' s a) : E.rows δ Δ s a = E₀.rows δ Δ' s a := by
  unfold LayeredArena.rows; rw [hg, hb, hr, hl, hd, hc, hq]

lemma twoPoint_coe (x y : Fin S) (a b : ℝ≥0) (s' : Fin S) :
    ((twoPoint x y a b s' : ℝ≥0) : ℝ) = (if s' = x then (a : ℝ) else 0) + (if s' = y then (b : ℝ) else 0) := by
  unfold twoPoint; push_cast; split_ifs <;> simp

/-- the likelihood ratio of the planted pair -/
noncomputable def Rp (Δ : ℝ) (s : Fin S) (a : Fin A) (s' : Fin S) : ℝ :=
  if (s, a) = p then (if s' = E₀.good then 1 + 2 * Δ else 1 - 2 * Δ) else 1

variable {δ Δ : ℝ≥0} (hδ1 : δ ≤ 1) (hΔ2 : Δ ≤ 1 / 2) (h0 : (0:ℝ≥0) ≤ 1 / 2)

include hg hb hr hl hd hc in
lemma hR_arena (hp : E₀.leafNat p.1 = 1) (hsl : E.specialLeaf = p.1) (hsa : E.specialAction = p.2) :
    ∀ s a s', ((E.toMDP hδ1 hΔ2).P s a s' : ℝ) =
      ((E₀.toMDP hδ1 h0).P s a s' : ℝ) * Rp E₀ p Δ s a s' := by
  intro s a s'
  show ((E.rows δ Δ s a s' : ℝ≥0) : ℝ) = ((E₀.rows δ 0 s a s' : ℝ≥0) : ℝ) * _
  by_cases hsa' : (s, a) = p
  · obtain ⟨hg0, hb0, hd0⟩ := (leaf_iff E₀ p.1).mp hp
    have hs : s = p.1 := (Prod.ext_iff.mp hsa').1
    have ha : a = p.2 := (Prod.ext_iff.mp hsa').2
    have hl0 : ¬ E₀.lvl s < E₀.depth := by rw [hs, hd0]; exact lt_irrefl _
    rw [← hs] at hg0 hb0
    have hgE : s ≠ E.good := hg ▸ hg0
    have hbE : s ≠ E.bad := hb ▸ hb0
    have hlE : ¬ E.lvl s < E.depth := by rw [← hl, ← hd]; exact hl0
    have q1 : E.goodProb Δ s a = 1 / 2 + Δ := by
      unfold LayeredArena.goodProb; rw [if_pos ⟨hs.trans hsl.symm, ha.trans hsa.symm⟩]
    have q0 : E₀.goodProb 0 s a = 1 / 2 := by
      unfold LayeredArena.goodProb; simp
    have hle : (1 / 2 + Δ : ℝ≥0) ≤ 1 := by
      calc (1 / 2 + Δ : ℝ≥0) ≤ 1 / 2 + 1 / 2 := by gcongr
        _ = 1 := by norm_num
    rw [E₀.rows_leaf a hg0 hb0 hl0, E.rows_leaf a hgE hbE hlE, q1, q0, twoPoint_coe, twoPoint_coe,
      NNReal.coe_sub hle, NNReal.coe_sub (by norm_num : (1 / 2 : ℝ≥0) ≤ 1), ← hg, ← hb]
    unfold Rp
    rw [if_pos hsa']
    have hgb : E₀.good ≠ E₀.bad := E₀.good_ne_bad
    by_cases h1 : s' = E₀.good
    · subst h1
      rw [if_pos rfl, if_neg hgb, if_pos rfl, if_neg hgb, if_pos rfl]
      push_cast; ring
    · by_cases h2 : s' = E₀.bad
      · subst h2
        rw [if_neg hgb.symm, if_pos rfl, if_neg hgb.symm, if_pos rfl, if_neg hgb.symm]
        push_cast; ring
      · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]
        simp
  · unfold Rp
    rw [if_neg hsa', mul_one]
    have hq : E.goodProb Δ s a = E₀.goodProb 0 s a := by
      unfold LayeredArena.goodProb
      have : ¬ (s = E.specialLeaf ∧ a = E.specialAction) := by
        rintro ⟨h1, h2⟩; apply hsa'; rw [h1, h2, hsl, hsa]
      simp [this]
    rw [rows_congr E₀ E hg hb hr hl hd hc δ Δ 0 s a hq]

/-- the per-play KL divergence of the planted pair -/
noncomputable def kap (Δ : ℝ) : ℝ := 1 / 2 * (-Real.log (1 + 2 * Δ)) + 1 / 2 * (-Real.log (1 - 2 * Δ))

lemma klv_arena (hp : E₀.leafNat p.1 = 1) (s : Fin S) (a : Fin A) :
    klv (Rp E₀ p Δ) (E₀.toMDP hδ1 h0) s a = if (s, a) = p then kap Δ else 0 := by
  unfold klv
  by_cases hsa' : (s, a) = p
  · obtain ⟨hg0, hb0, hd0⟩ := (leaf_iff E₀ p.1).mp hp
    have hs : s = p.1 := (Prod.ext_iff.mp hsa').1
    have hl0 : ¬ E₀.lvl s < E₀.depth := by rw [hs, hd0]; exact lt_irrefl _
    rw [← hs] at hg0 hb0
    rw [PV_leaf E₀ hδ1 h0 _ a hg0 hb0 hl0, gp_val, if_pos hsa']
    have e1 : Rp E₀ p Δ s a E₀.good = 1 + 2 * Δ := by simp [Rp, hsa']
    have e2 : Rp E₀ p Δ s a E₀.bad = 1 - 2 * Δ := by simp [Rp, hsa', E₀.good_ne_bad.symm]
    have e3 : (1 / 2 + if s = E₀.specialLeaf ∧ a = E₀.specialAction then ((0:ℝ≥0) : ℝ) else 0) =
        1 / 2 := by split_ifs <;> simp
    rw [e1, e2, e3]
    unfold kap
    ring
  · rw [if_neg hsa']
    unfold Rp
    simp [hsa']

lemma kap_nonneg (hΔ4 : Δ ≤ 1 / 4) : 0 ≤ kap Δ := by
  have hΔ : (Δ : ℝ) ≤ 1 / 4 := by exact_mod_cast hΔ4
  have h0' : (0 : ℝ) ≤ Δ := NNReal.coe_nonneg _
  unfold kap
  have h1 : 0 < 1 - 2 * (Δ : ℝ) := by linarith
  have h2 : 0 < 1 + 2 * (Δ : ℝ) := by linarith
  have : Real.log (1 + 2 * (Δ:ℝ)) + Real.log (1 - 2 * (Δ:ℝ)) ≤ 0 := by
    rw [← Real.log_mul h2.ne' h1.ne']
    apply Real.log_nonpos (by positivity)
    nlinarith
  linarith

lemma kap_le (hΔ4 : Δ ≤ 1 / 4) : kap Δ ≤ 8 / 3 * (Δ : ℝ) ^ 2 := by
  have hΔ : (Δ : ℝ) ≤ 1 / 4 := by exact_mod_cast hΔ4
  have h0' : (0 : ℝ) ≤ Δ := NNReal.coe_nonneg _
  unfold kap
  have h1 : 0 < 1 - 2 * (Δ : ℝ) := by linarith
  have h2 : 0 < 1 + 2 * (Δ : ℝ) := by linarith
  have hy : 0 < (1 + 2 * (Δ : ℝ)) * (1 - 2 * (Δ:ℝ)) := mul_pos h2 h1
  have hlog := Real.one_sub_inv_le_log_of_pos hy
  rw [Real.log_mul h2.ne' h1.ne'] at hlog
  have hy2 : (1 + 2 * (Δ : ℝ)) * (1 - 2 * (Δ:ℝ)) = 1 - 4 * (Δ:ℝ) ^ 2 := by ring
  rw [hy2] at hlog
  have h34 : 3 / 4 ≤ 1 - 4 * (Δ : ℝ) ^ 2 := by nlinarith
  have h16 : (Δ : ℝ) ^ 2 ≤ 1 / 16 := by nlinarith
  have hinv : (1 - 4 * (Δ : ℝ) ^ 2)⁻¹ ≤ 1 + 16 / 3 * (Δ : ℝ) ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ (by linarith)]
    nlinarith [sq_nonneg (Δ : ℝ), mul_nonneg (sq_nonneg (Δ : ℝ)) (sub_nonneg.mpr h16)]
  linarith

include hg hb hr hl hd hc in
/-- the per-family-member change-of-measure bound -/
theorem per_p (hΔ4 : Δ ≤ 1 / 4) (hp : E₀.leafNat p.1 = 1) (hsl : E.specialLeaf = p.1)
    (hsa : E.specialAction = p.2) (π : MDPPolicy S A) (n : ℕ) {l : ℝ} (hl0 : 0 < l) :
    ∫ h, ∑ t, (if E₀.leafNat (h t).1 = 1 ∧ h t ≠ p ∧ prefixCount E₀.leafNat h t < N then (1:ℝ) else 0)
        ∂(mdpMeasure (E₀.toMDP hδ1 h0) (mdpStateDirac E₀.root) π n) -
      N / 2 * (l + kap Δ * (∫ h, ∑ t, (if h t = p ∧ prefixCount E₀.leafNat h t < N then (1:ℝ) else 0)
        ∂(mdpMeasure (E₀.toMDP hδ1 h0) (mdpStateDirac E₀.root) π n)) / (2 * l)) ≤
    ∫ h, ∑ t, (if E₀.leafNat (h t).1 = 1 ∧ h t ≠ p ∧ prefixCount E₀.leafNat h t < N then (1:ℝ) else 0)
        ∂(mdpMeasure (E.toMDP hδ1 hΔ2) (mdpStateDirac E₀.root) π n) := by
  set M0 := E₀.toMDP hδ1 h0
  set M1 := E.toMDP hδ1 hΔ2
  set R := Rp E₀ p (Δ : ℝ)
  have hΔ : (Δ : ℝ) ≤ 1 / 4 := by exact_mod_cast hΔ4
  have hΔ0 : (0 : ℝ) ≤ Δ := NNReal.coe_nonneg _
  have hR := hR_arena E₀ E p hg hb hr hl hd hc hδ1 hΔ2 h0 hp hsl hsa
  have hRpos : ∀ s a s', 0 < R s a s' := by
    intro s a s'; simp only [R, Rp]; split_ifs <;> linarith
  set f : Fin S × Fin A → ℕ → ℝ :=
    fun x c => if E₀.leafNat x.1 = 1 ∧ x ≠ p ∧ c < N then (1:ℝ) else 0 with hfdef
  have hf : ∀ x c, N ≤ c → f x c = 0 := by
    intro x c hc'; simp only [f]; rw [if_neg]; omega
  have h1 := stopped_id E₀.leafNat N R M0 M1 (mdpStateDirac E₀.root) π hR f hf n
  have hF0 : ∀ h : Tr S A n, 0 ≤ ∑ t, f (h t) (prefixCount E₀.leafNat h t) :=
    fun h => Finset.sum_nonneg (fun t _ => by simp only [f]; split_ifs <;> norm_num)
  have hFB : ∀ h : Tr S A n, ∑ t, f (h t) (prefixCount E₀.leafNat h t) ≤ N := by
    intro h
    calc _ ≤ ∑ t, (if E₀.leafNat (h t).1 = 1 ∧ prefixCount E₀.leafNat h t < N then (1:ℝ) else 0) := by
          apply Finset.sum_le_sum; intro t _; simp only [f]
          by_cases h1 : E₀.leafNat (h t).1 = 1 ∧ h t ≠ p ∧ prefixCount E₀.leafNat h t < N
          · rw [if_pos h1, if_pos ⟨h1.1, h1.2.2⟩]
          · rw [if_neg h1]; split_ifs <;> norm_num
      _ = ((min (fc E₀.leafNat h) N : ℕ) : ℝ) := gcount E₀.leafNat (leaf_le E₀) N n h
      _ ≤ N := by exact_mod_cast min_le_right _ _
  have h2 := compare E₀.leafNat N R M0 M1 (mdpStateDirac E₀.root) π hR n _ (N : ℝ) hF0 hFB
  have h3 := pinsker_int E₀.leafNat N R M0 M1 (mdpStateDirac E₀.root) π hR hRpos n hl0
  have h4 := kl_chain E₀.leafNat N R M0 (mdpStateDirac E₀.root) π hRpos n
  have haw : ∀ h : Tr S A n, 0 ≤ aw E₀.leafNat N R M0 n h := by
    intro h
    cases n with
    | zero => simp [aw]
    | succ n =>
      simp only [aw]
      split_ifs
      · rw [klv_arena E₀ p hδ1 h0 hp]; split_ifs
        · exact kap_nonneg hΔ4
        · exact le_rfl
      · exact le_rfl
  have hklf : ∀ h : Tr S A n, ∑ t, klf N R M0 (h t) (prefixCount E₀.leafNat h t) =
      kap Δ * ∑ t, (if h t = p ∧ prefixCount E₀.leafNat h t < N then (1:ℝ) else 0) := by
    intro h
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    simp only [klf]
    rw [klv_arena E₀ p hδ1 h0 hp]
    by_cases hx : h t = p
    · simp [hx]
    · simp [hx]
  simp_rw [hklf] at h4
  rw [integral_add Integrable.of_finite Integrable.of_finite, integral_const_mul] at h4
  have hawi : 0 ≤ ∫ h, aw E₀.leafNat N R M0 n h ∂(mdpMeasure M0 (mdpStateDirac E₀.root) π n) :=
    integral_nonneg haw
  have hkl : ∫ h, -Real.log (LR E₀.leafNat N R n h) ∂(mdpMeasure M0 (mdpStateDirac E₀.root) π n) ≤
      kap Δ * ∫ h, ∑ t, (if h t = p ∧ prefixCount E₀.leafNat h t < N then (1:ℝ) else 0)
        ∂(mdpMeasure M0 (mdpStateDirac E₀.root) π n) := by linarith
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have h5 : (∫ h, -Real.log (LR E₀.leafNat N R n h) ∂(mdpMeasure M0 (mdpStateDirac E₀.root) π n)) / (2 * l)
      ≤ kap Δ * (∫ h, ∑ t, (if h t = p ∧ prefixCount E₀.leafNat h t < N then (1:ℝ) else 0)
        ∂(mdpMeasure M0 (mdpStateDirac E₀.root) π n)) / (2 * l) :=
    div_le_div_of_nonneg_right hkl (by positivity)
  have h6 := mul_le_mul_of_nonneg_left (add_le_add_left h5 l) (by positivity : (0:ℝ) ≤ N / 2)
  have h7 := mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ N / 2)
  rw [h1]
  linarith

end Fam

end P4acf

set_option maxHeartbeats 4000000 in
open MeasureTheory ProbabilityTheory BanditAlgorithm BanditAlgorithm.LayeredArena in
theorem main_4acf
    {S A : ℕ} [NeZero S] {δ Δ : ℝ≥0}
    (hδ1 : δ ≤ 1) (hδ0 : (0 : ℝ) < δ) (hΔ4 : Δ ≤ 1 / 4) (hΔ2 : Δ ≤ 1 / 2)
    (E₀ : LayeredArena S A)
    (Efam : ↥(countedPairs E₀.leafNat) → LayeredArena S A)
    (hg : ∀ p, E₀.good = (Efam p).good) (hb : ∀ p, E₀.bad = (Efam p).bad)
    (hr : ∀ p, E₀.root = (Efam p).root) (hl : ∀ p, E₀.lvl = (Efam p).lvl)
    (hdp : ∀ p, E₀.depth = (Efam p).depth) (hc : ∀ p, E₀.child = (Efam p).child)
    (hsl : ∀ p, (Efam p).specialLeaf = p.val.1)
    (hsa : ∀ p, (Efam p).specialAction = p.val.2)
    (hS : 0 < S) (hA : 0 < A)
    (π : MDPPolicy S A) (n N k : ℕ) (D c₁ c₂ c₃ : ℝ)
    (hcard : Fintype.card ↥(countedPairs (A := A) E₀.leafNat) = k) (hk : 2 ≤ k)
    (hn0 : 0 < n) (hN0 : 0 < N) (hD : 0 < D)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hcapD : (N : ℝ) ≤ n / D) (hc₃D : c₃ * D ≤ 1 / (δ : ℝ))
    (ε : ℝ) (hlo : c₁ * n / D ≤ (1 - ε) * N)
    (hhi : ((n : ℝ) + 1 / (δ : ℝ)) / E₀.epiLen (δ : ℝ) ≤ c₂ * n / D)
    (htail1 : E₀.depth + N * (E₀.depth + 2) ≤ n)
    (htail2 : (2 : ℝ) ^ N ≤ ε * (1 + (δ : ℝ)) ^ N
      * (mx (δ : ℝ)) ^ (n - E₀.depth - N * (E₀.depth + 2)))
    (hΔtune : (Δ : ℝ) = c₁ * ((k : ℝ) - 1) / 2 * Real.sqrt (D / (2 * c₂ * n * k))) :
    ∃ p : ↥(countedPairs E₀.leafNat),
      c₁ ^ 2 * c₃ / 16 * Real.sqrt (D * k * n / (2 * c₂)) - (1 / 2 + (Δ : ℝ)) / (δ : ℝ)
        ≤ ∫ h, mdpRegret ((Efam p).toMDP hδ1 hΔ2) n h
            ∂(mdpMeasure ((Efam p).toMDP hδ1 hΔ2)
              (mdpStateDirac (Efam p).root) π n) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h0 : (0 : ℝ≥0) ≤ 1 / 2 := zero_le
  set nn : ℝ := ((m + 1 : ℕ) : ℝ) with hnn
  have hnn0 : 0 < nn := by rw [hnn]; positivity
  set K : ℝ := (k : ℝ) with hK
  have hK2 : (2 : ℝ) ≤ K := by rw [hK]; exact_mod_cast hk
  set μ0 := mdpMeasure (E₀.toMDP hδ1 h0) (mdpStateDirac E₀.root) π (m + 1) with hμ0
  let T : ↥(countedPairs E₀.leafNat) → ℝ := fun q =>
    ∫ h, ∑ t, (if h t = q.val ∧ prefixCount E₀.leafNat h t < N then (1:ℝ) else 0) ∂μ0
  haveI : Nonempty ↥(countedPairs E₀.leafNat) := by
    rw [← Fintype.card_pos_iff, hcard]; omega
  obtain ⟨p, hpmin⟩ := Finite.exists_min T
  refine ⟨p, ?_⟩
  have hpleaf : E₀.leafNat p.val.1 = 1 := mem_countedPairs.mp p.2
  set Gf : MDPTrajectory S A (m + 1) → ℝ := fun h => ∑ t,
    (if E₀.leafNat (h t).1 = 1 ∧ prefixCount E₀.leafNat h t < N then (1:ℝ) else 0) with hGf
  have hG : ∀ h, Gf h = ((min (P4acf.fc E₀.leafNat h) N : ℕ) : ℝ) :=
    fun h => P4acf.gcount E₀.leafNat (P4acf.leaf_le E₀) N (m + 1) h
  -- the truncated counts sum to the truncated leaf count
  have hsumT : ∑ q, T q = ∫ h, Gf h ∂μ0 := by
    simp only [T]
    rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
    congr 1; funext h
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.sum_coe_sort (countedPairs E₀.leafNat)
      (fun q => if h t = q ∧ prefixCount E₀.leafNat h t < N then (1:ℝ) else 0)]
    by_cases hc' : prefixCount E₀.leafNat h t < N
    · simp only [hc', and_true]
      rw [Finset.sum_ite_eq]
      simp [mem_countedPairs]
    · simp [hc']
  have hT0 : 0 ≤ T p := integral_nonneg (fun h => Finset.sum_nonneg (fun t _ => by
    split_ifs <;> norm_num))
  have hkT : K * T p ≤ ∫ h, Gf h ∂μ0 := by
    rw [← hsumT]
    calc K * T p = ∑ _q : ↥(countedPairs E₀.leafNat), T p := by
          rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
      _ ≤ ∑ q, T q := Finset.sum_le_sum (fun q _ => hpmin q)
  -- F_p = G - T_p
  have hFdec : ∫ h, ∑ t, (if E₀.leafNat (h t).1 = 1 ∧ h t ≠ p.val ∧
      prefixCount E₀.leafNat h t < N then (1:ℝ) else 0) ∂μ0 = ∫ h, Gf h ∂μ0 - T p := by
    simp only [T]
    rw [← integral_sub Integrable.of_finite Integrable.of_finite]
    congr 1; funext h
    simp only [Gf]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    by_cases hx : h t = p.val
    · rw [hx]; simp [hpleaf]
    · simp [hx]
  -- tail bound: the leaf count reaches N with probability at least 1 - ε
  have hx1 : 1 ≤ mx (δ : ℝ) := P4acf.one_le_mx (NNReal.coe_nonneg δ)
  have hρ1 : 1 ≤ P4acf.rho (δ : ℝ) :=
    P4acf.one_le_rho (by exact_mod_cast hδ1) (NNReal.coe_nonneg δ)
  have htail : ∫ h, (if P4acf.fc E₀.leafNat h < N then (1:ℝ) else 0) ∂μ0 ≤ ε := by
    have ht := P4acf.tail E₀ hδ1 h0 N hN0 π m
    have hxpos : 0 < mx (δ : ℝ) ^ (m + 1) := by positivity
    have hρN : P4acf.rho (δ : ℝ) ^ N * (1 + (δ : ℝ)) ^ N = 2 ^ N := by
      rw [← mul_pow]; unfold P4acf.rho; rw [div_mul_cancel₀ _ (by positivity)]
    have hsplit : mx (δ : ℝ) ^ (E₀.depth + N * (E₀.depth + 2)) *
        mx (δ : ℝ) ^ (m + 1 - E₀.depth - N * (E₀.depth + 2)) = mx (δ : ℝ) ^ (m + 1) := by
      rw [← pow_add]; congr 1; omega
    have hb1 : mx (δ : ℝ) ^ (E₀.depth + (N - 1) * (E₀.depth + 2)) * P4acf.rho (δ : ℝ) ^ (N - 1) ≤
        mx (δ : ℝ) ^ (E₀.depth + N * (E₀.depth + 2)) * P4acf.rho (δ : ℝ) ^ N := by
      apply mul_le_mul (pow_le_pow_right₀ hx1 (by
        have : (N - 1) * (E₀.depth + 2) ≤ N * (E₀.depth + 2) :=
          Nat.mul_le_mul_right _ (Nat.sub_le N 1)
        omega)) (pow_le_pow_right₀ hρ1 (Nat.sub_le N 1)) (by positivity) (by positivity)
    have hb2 : P4acf.rho (δ : ℝ) ^ N ≤ ε * mx (δ : ℝ) ^ (m + 1 - E₀.depth - N * (E₀.depth + 2)) := by
      have h1d : (0:ℝ) < (1 + (δ : ℝ)) ^ N := by positivity
      rw [← mul_le_mul_iff_of_pos_right h1d, hρN]
      linarith [htail2]
    have hb3 : mx (δ : ℝ) ^ (m + 1) * ∫ h, (if P4acf.fc E₀.leafNat h < N then (1:ℝ) else 0) ∂μ0 ≤
        mx (δ : ℝ) ^ (m + 1) * ε := by
      calc _ ≤ _ := ht
        _ ≤ _ := hb1
        _ ≤ mx (δ : ℝ) ^ (E₀.depth + N * (E₀.depth + 2)) *
              (ε * mx (δ : ℝ) ^ (m + 1 - E₀.depth - N * (E₀.depth + 2))) :=
            mul_le_mul_of_nonneg_left hb2 (by positivity)
        _ = mx (δ : ℝ) ^ (m + 1) * ε := by rw [← hsplit]; ring
    exact le_of_mul_le_mul_left hb3 hxpos
  have hGlow : (N : ℝ) * (1 - ε) ≤ ∫ h, Gf h ∂μ0 := by
    have pt : ∀ h, (N : ℝ) - N * (if P4acf.fc E₀.leafNat h < N then (1:ℝ) else 0) ≤ Gf h := by
      intro h
      rw [hG h]
      split_ifs with hfc
      · simp only [mul_one, sub_self]; positivity
      · rw [min_eq_right (not_lt.mp hfc)]; simp
    calc (N : ℝ) * (1 - ε) ≤ ∫ h, ((N : ℝ) - N * (if P4acf.fc E₀.leafNat h < N then (1:ℝ) else 0)) ∂μ0 := by
          rw [integral_sub (integrable_const _) Integrable.of_finite, integral_const_mul]
          simp only [integral_const, probReal_univ, one_smul]
          have : (0:ℝ) ≤ N := Nat.cast_nonneg N
          have := mul_le_mul_of_nonneg_left htail this
          linarith
      _ ≤ _ := integral_mono Integrable.of_finite Integrable.of_finite pt
  have hGhi : ∫ h, Gf h ∂μ0 ≤ c₂ * nn / D := by
    have hlc := P4acf.leafcount E₀ hδ1 h0 hδ0 π m
    calc ∫ h, Gf h ∂μ0 ≤ ∫ h, (P4acf.fc E₀.leafNat h : ℝ) ∂μ0 := by
          apply integral_mono Integrable.of_finite Integrable.of_finite
          intro h; rw [hG h]; show _ ≤ (P4acf.fc E₀.leafNat h : ℝ); exact_mod_cast min_le_left _ _
      _ ≤ _ := hlc
      _ ≤ _ := hhi
  -- change of measure for the chosen pair
  set l : ℝ := c₁ * (K - 1) / (2 * K) with hldef
  have hK0 : 0 < K := by linarith
  have hl0 : 0 < l := by rw [hldef]; apply div_pos (mul_pos hc₁ (by linarith)) (by linarith)
  have hpp := P4acf.per_p E₀ (Efam p) p.val N (hg p) (hb p) (hr p) (hl p) (hdp p) (hc p)
    hδ1 hΔ2 h0 hΔ4 hpleaf (hsl p) (hsa p) π (m + 1) hl0
  rw [← hμ0, hFdec] at hpp
  have hreg := P4acf.regret_lb (Efam p) hδ1 hΔ2 hδ0 π m
  rw [← hr p] at hreg ⊢
  have hind : ∫ h, ∑ t, (if E₀.leafNat (h t).1 = 1 ∧ h t ≠ p.val ∧
        prefixCount E₀.leafNat h t < N then (1:ℝ) else 0)
        ∂(mdpMeasure ((Efam p).toMDP hδ1 hΔ2) (mdpStateDirac E₀.root) π (m + 1)) ≤
      ∫ h, ∑ t, P4acf.indR (Efam p) (h t).1 (h t).2
        ∂(mdpMeasure ((Efam p).toMDP hδ1 hΔ2) (mdpStateDirac E₀.root) π (m + 1)) := by
    apply integral_mono Integrable.of_finite Integrable.of_finite
    intro h
    apply Finset.sum_le_sum
    intro t _
    unfold P4acf.indR
    rw [P4acf.leafNat_congr E₀ (Efam p) (hg p) (hb p) (hl p) (hdp p), hsl p, hsa p]
    by_cases h1 : E₀.leafNat (h t).1 = 1 ∧ h t ≠ p.val ∧ prefixCount E₀.leafNat h t < N
    · rw [if_pos h1, if_pos ⟨h1.1, h1.2.1⟩]
    · rw [if_neg h1]; split_ifs <;> norm_num
  -- arithmetic
  have hκ0 := P4acf.kap_nonneg hΔ4
  have hκ := P4acf.kap_le hΔ4
  have hΔ0 : (0:ℝ) ≤ Δ := NNReal.coe_nonneg _
  set σ := Real.sqrt (D / (2 * c₂ * nn * K)) with hσ
  have hσ0 : 0 ≤ σ := Real.sqrt_nonneg _
  have hσ2 : σ ^ 2 = D / (2 * c₂ * nn * K) := Real.sq_sqrt (by positivity)
  have hsq : Real.sqrt (D * K * nn / (2 * c₂)) = nn * K * σ := by
    rw [show D * K * nn / (2 * c₂) = (nn * K) ^ 2 * (D / (2 * c₂ * nn * K)) by
      field_simp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hΔe : (Δ : ℝ) = c₁ * (K - 1) / 2 * σ := hΔtune
  -- τ bounds
  set τ := T p with hτ
  have hτ1 : τ ≤ (∫ h, Gf h ∂μ0) / K := by rw [le_div_iff₀ hK0]; linarith
  have hστ : σ ^ 2 * τ ≤ 1 / (2 * K ^ 2) := by
    have : τ ≤ c₂ * nn / D / K := le_trans hτ1 (div_le_div_of_nonneg_right hGhi hK0.le)
    calc σ ^ 2 * τ ≤ D / (2 * c₂ * nn * K) * (c₂ * nn / D / K) := by
          rw [hσ2]; exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = 1 / (2 * K ^ 2) := by field_simp
  have hκτ : P4acf.kap Δ * τ ≤ c₁ ^ 2 * (K - 1) ^ 2 / (3 * K ^ 2) := by
    calc P4acf.kap Δ * τ ≤ 8 / 3 * (Δ : ℝ) ^ 2 * τ := mul_le_mul_of_nonneg_right hκ hT0
      _ = 2 / 3 * c₁ ^ 2 * (K - 1) ^ 2 * (σ ^ 2 * τ) := by rw [hΔe]; ring
      _ ≤ 2 / 3 * c₁ ^ 2 * (K - 1) ^ 2 * (1 / (2 * K ^ 2)) :=
          mul_le_mul_of_nonneg_left hστ (by positivity)
      _ = c₁ ^ 2 * (K - 1) ^ 2 / (3 * K ^ 2) := by field_simp
  have hB4 : l + P4acf.kap Δ * τ / (2 * l) ≤ 5 / 6 * (c₁ * (K - 1) / K) := by
    have : P4acf.kap Δ * τ / (2 * l) ≤ c₁ ^ 2 * (K - 1) ^ 2 / (3 * K ^ 2) / (2 * l) :=
      div_le_div_of_nonneg_right hκτ (by positivity)
    have e : c₁ ^ 2 * (K - 1) ^ 2 / (3 * K ^ 2) / (2 * l) = 1 / 3 * (c₁ * (K - 1) / K) := by
      rw [hldef]; field_simp
    rw [hldef] at this ⊢
    have e2 : c₁ * (K - 1) / (2 * K) = 1 / 2 * (c₁ * (K - 1) / K) := by ring
    rw [e] at this
    linarith
  set a := c₁ * nn / D with ha
  have hNa : (N : ℝ) * c₁ ≤ a := by
    calc (N : ℝ) * c₁ ≤ nn / D * c₁ := mul_le_mul_of_nonneg_right hcapD hc₁.le
      _ = a := by rw [ha]; ring
  have hag : a ≤ ∫ h, Gf h ∂μ0 := by
    calc a ≤ (1 - ε) * N := hlo
      _ = N * (1 - ε) := by ring
      _ ≤ _ := hGlow
  have hK1 : 0 < K - 1 := by linarith
  have hr1 : (K - 1) / K ≥ 0 := by positivity
  have hFp : 7 / 12 * (a * ((K - 1) / K)) ≤
      ∫ h, ∑ t, (if E₀.leafNat (h t).1 = 1 ∧ h t ≠ p.val ∧
        prefixCount E₀.leafNat h t < N then (1:ℝ) else 0)
        ∂(mdpMeasure ((Efam p).toMDP hδ1 hΔ2) (mdpStateDirac E₀.root) π (m + 1)) := by
    refine le_trans ?_ hpp
    have hgt : (∫ h, Gf h ∂μ0) * ((K - 1) / K) ≤ (∫ h, Gf h ∂μ0) - τ := by
      have : (∫ h, Gf h ∂μ0) * ((K - 1) / K) = (∫ h, Gf h ∂μ0) - (∫ h, Gf h ∂μ0) / K := by
        field_simp
      linarith
    have hga : a * ((K - 1) / K) ≤ (∫ h, Gf h ∂μ0) * ((K - 1) / K) :=
      mul_le_mul_of_nonneg_right hag hr1
    have hNt : (N : ℝ) / 2 * (l + P4acf.kap Δ * τ / (2 * l)) ≤ 5 / 12 * (a * ((K - 1) / K)) := by
      calc (N : ℝ) / 2 * (l + P4acf.kap Δ * τ / (2 * l)) ≤ (N : ℝ) / 2 * (5 / 6 * (c₁ * (K - 1) / K)) :=
            mul_le_mul_of_nonneg_left hB4 (by positivity)
        _ = 5 / 12 * ((N * c₁) * ((K - 1) / K)) := by ring
        _ ≤ 5 / 12 * (a * ((K - 1) / K)) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact mul_le_mul_of_nonneg_right hNa hr1
    linarith
  have hδinv : c₃ * D * (Δ : ℝ) ≤ (Δ : ℝ) / δ := by
    rw [div_eq_mul_one_div, mul_comm (Δ : ℝ)]
    exact mul_le_mul_of_nonneg_right hc₃D hΔ0
  have hX0 : 0 ≤ 7 / 12 * (a * ((K - 1) / K)) := by rw [ha]; positivity
  have hmain : c₁ ^ 2 * c₃ / 16 * Real.sqrt (D * K * nn / (2 * c₂)) ≤ (Δ : ℝ) / δ *
      ∫ h, ∑ t, P4acf.indR (Efam p) (h t).1 (h t).2
        ∂(mdpMeasure ((Efam p).toMDP hδ1 hΔ2) (mdpStateDirac E₀.root) π (m + 1)) := by
    have hI := le_trans hFp hind
    have hΔδ0 : 0 ≤ (Δ : ℝ) / δ := by positivity
    calc c₁ ^ 2 * c₃ / 16 * Real.sqrt (D * K * nn / (2 * c₂))
        = c₁ ^ 2 * c₃ / 16 * (nn * K * σ) := by rw [hsq]
      _ ≤ c₃ * D * (Δ : ℝ) * (7 / 12 * (a * ((K - 1) / K))) := by
          rw [hΔe, ha]
          have hkey : K / 16 ≤ 7 / 24 * (K - 1) ^ 2 / K := by
            rw [le_div_iff₀ hK0]
            have := mul_nonneg (sub_nonneg.mpr hK2) (by linarith : (0:ℝ) ≤ 11 * K - 6)
            linarith
          have e : c₃ * D * (c₁ * (K - 1) / 2 * σ) * (7 / 12 * (c₁ * nn / D * ((K - 1) / K))) =
              c₁ ^ 2 * c₃ * nn * σ * (7 / 24 * (K - 1) ^ 2 / K) := by
            field_simp
            ring
          rw [e]
          have e2 : c₁ ^ 2 * c₃ / 16 * (nn * K * σ) = c₁ ^ 2 * c₃ * nn * σ * (K / 16) := by ring
          rw [e2]
          exact mul_le_mul_of_nonneg_left hkey (by positivity)
      _ ≤ (Δ : ℝ) / δ * (7 / 12 * (a * ((K - 1) / K))) :=
          mul_le_mul_of_nonneg_right hδinv hX0
      _ ≤ _ := mul_le_mul_of_nonneg_left hI hΔδ0
  have hcast : Real.sqrt (D * k * ((m + 1 : ℕ) : ℝ) / (2 * c₂)) = Real.sqrt (D * K * nn / (2 * c₂)) := rfl
  rw [hcast]
  linarith

set_option maxHeartbeats 4000000 in
open MeasureTheory ProbabilityTheory BanditAlgorithm BanditAlgorithm.LayeredArena NNReal in
theorem solution
    {S A : ℕ} [NeZero S] {δ Δ : ℝ≥0}
    (hδ1 : δ ≤ 1) (hδ0 : (0 : ℝ) < δ) (hΔ4 : Δ ≤ 1 / 4) (hΔ2 : Δ ≤ 1 / 2)
    (E₀ : LayeredArena S A)
    (Efam : ↥(countedPairs E₀.leafNat) → LayeredArena S A)
    (hg : ∀ p, E₀.good = (Efam p).good) (hb : ∀ p, E₀.bad = (Efam p).bad)
    (hr : ∀ p, E₀.root = (Efam p).root) (hl : ∀ p, E₀.lvl = (Efam p).lvl)
    (hdp : ∀ p, E₀.depth = (Efam p).depth) (hc : ∀ p, E₀.child = (Efam p).child)
    (hsl : ∀ p, (Efam p).specialLeaf = p.val.1)
    (hsa : ∀ p, (Efam p).specialAction = p.val.2)
    (hS : 0 < S) (hA : 0 < A)
    (π : MDPPolicy S A) (n N k : ℕ) (D c₁ c₂ c₃ : ℝ)
    (hcard : Fintype.card ↥(countedPairs (A := A) E₀.leafNat) = k) (hk : 2 ≤ k)
    (hn0 : 0 < n) (hN0 : 0 < N) (hD : 0 < D)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hcapD : (N : ℝ) ≤ n / D) (hc₃D : c₃ * D ≤ 1 / (δ : ℝ))
    (ε : ℝ) (hlo : c₁ * n / D ≤ (1 - ε) * N)
    (hhi : ((n : ℝ) + 1 / (δ : ℝ)) / E₀.epiLen (δ : ℝ) ≤ c₂ * n / D)
    (htail1 : E₀.depth + N * (E₀.depth + 2) ≤ n)
    (htail2 : (2 : ℝ) ^ N ≤ ε * (1 + (δ : ℝ)) ^ N
      * (mx (δ : ℝ)) ^ (n - E₀.depth - N * (E₀.depth + 2)))
    (hΔtune : (Δ : ℝ) = c₁ * ((k : ℝ) - 1) / 2 * Real.sqrt (D / (2 * c₂ * n * k))) :
    ∃ p : ↥(countedPairs E₀.leafNat),
      c₁ ^ 2 * c₃ / 16 * Real.sqrt (D * k * n / (2 * c₂)) - (1 / 2 + (Δ : ℝ)) / (δ : ℝ)
        ≤ ∫ h, mdpRegret ((Efam p).toMDP hδ1 hΔ2) n h
            ∂(mdpMeasure ((Efam p).toMDP hδ1 hΔ2)
              (mdpStateDirac (Efam p).root) π n) := by
  exact main_4acf hδ1 hδ0 hΔ4 hΔ2 E₀ Efam hg hb hr hl hdp hc hsl hsa hS hA π n N k D c₁ c₂ c₃
    hcard hk hn0 hN0 hD hc₁ hc₂ hc₃ hcapD hc₃D ε hlo hhi htail1 htail2 hΔtune
