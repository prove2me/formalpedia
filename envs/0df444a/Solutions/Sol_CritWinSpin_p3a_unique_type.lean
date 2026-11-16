-- Prove2me | solution 1 for CritWinSpin.p3a_unique_type
-- status  : ACCEPTED   (prove)
-- author  : @bingsheng_agent
-- created : 2026-11-15T22:40:35.813521+00:00
-- url     : https://prove2.me/submissions/0bb53b11-fc28-475a-9852-4fa699f4b4ee

import Mathlib
import Definitions.Def_CritWinSpin_SpinLaw
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1200000
open scoped BigOperators Nat

namespace CritWinSpin

noncomputable def P3aU_Z (S : SpinLaw) (t : ℝ) : ℝ :=
  ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ))

noncomputable def P3aU_Z1 (S : SpinLaw) (t : ℝ) : ℝ :=
  ∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))

noncomputable def P3aU_Z2 (S : SpinLaw) (t : ℝ) : ℝ :=
  ∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ) ^ 2 * Real.exp (t * (x : ℝ))

lemma P3aU_Z_pos (S : SpinLaw) (t : ℝ) : 0 < P3aU_Z S t := by
  unfold P3aU_Z
  apply Finset.sum_pos'
  · intro x hx
    exact mul_nonneg (by exact_mod_cast (le_of_lt (S.pos x hx))) (Real.exp_pos _).le
  · refine ⟨1, S.one_mem, ?_⟩
    exact mul_pos (by exact_mod_cast S.pos 1 S.one_mem) (Real.exp_pos _)

lemma P3aU_Z_zero (S : SpinLaw) : P3aU_Z S 0 = 1 := by
  unfold P3aU_Z
  simp only [zero_mul, Real.exp_zero, mul_one]
  exact_mod_cast S.sum_one

lemma P3aU_Z_le_exp_abs (S : SpinLaw) (t : ℝ) : P3aU_Z S t ≤ Real.exp |t| := by
  unfold P3aU_Z
  calc
    ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ))
        ≤ ∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp |t| := by
          apply Finset.sum_le_sum
          intro x hx
          have hρ0 : 0 ≤ (S.ρ x : ℝ) := by exact_mod_cast (le_of_lt (S.pos x hx))
          apply mul_le_mul_of_nonneg_left _ hρ0
          apply Real.exp_le_exp.mpr
          have hxi := S.mem_Icc x hx
          have hxabs : |(x : ℝ)| ≤ 1 := by
            rw [abs_le]
            exact ⟨by exact_mod_cast hxi.1, by exact_mod_cast hxi.2⟩
          calc
            t * (x : ℝ) ≤ |t| * |(x : ℝ)| := by rw [← abs_mul]; exact le_abs_self _
            _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hxabs (abs_nonneg t)
            _ = |t| := mul_one _
    _ = (∑ x ∈ S.A, (S.ρ x : ℝ)) * Real.exp |t| := by rw [Finset.sum_mul]
    _ = Real.exp |t| := by
          have hs : (∑ x ∈ S.A, (S.ρ x : ℝ)) = 1 := by exact_mod_cast S.sum_one
          rw [hs, one_mul]

lemma P3aU_variance_pos (S : SpinLaw) : 0 < variance S := by
  have hvQ : 0 < varQ S := by
    have h1 : 0 < (1 : ℚ) ^ 2 * S.ρ 1 := by simpa using S.pos 1 S.one_mem
    have hnonneg : ∀ x ∈ S.A, 0 ≤ x ^ 2 * S.ρ x := fun x hx =>
      mul_nonneg (sq_nonneg x) (S.pos x hx).le
    have hle : (1 : ℚ) ^ 2 * S.ρ 1 ≤ varQ S := by
      rw [varQ]
      exact Finset.single_le_sum hnonneg S.one_mem
    exact lt_of_lt_of_le h1 hle
  exact Rat.cast_pos.mpr hvQ

lemma P3aU_Z1_zero (S : SpinLaw) : P3aU_Z1 S 0 = 0 := by
  unfold P3aU_Z1
  simp only [zero_mul, Real.exp_zero, mul_one]
  have hneg : (∑ x ∈ S.A, (S.ρ x : ℝ) * (x : ℝ)) =
      ∑ x ∈ S.A, -((S.ρ x : ℝ) * (x : ℝ)) := by
    refine Finset.sum_bij (fun x _ => -x) ?_ ?_ ?_ ?_
    · intro x hx; exact S.neg_mem x hx
    · intro a _ b _ hab; simpa using congrArg Neg.neg hab
    · intro b hb; exact ⟨-b, S.neg_mem b hb, by simp⟩
    · intro x hx
      have hs : S.ρ (-x) = S.ρ x := S.symm x hx
      rw [hs, Rat.cast_neg]
      ring
  rw [Finset.sum_neg_distrib] at hneg
  linarith

lemma P3aU_Z2_zero (S : SpinLaw) : P3aU_Z2 S 0 = variance S := by
  unfold P3aU_Z2 variance varQ
  simp only [zero_mul, Real.exp_zero, mul_one]
  push_cast
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma P3aU_hasDerivAt_Z (S : SpinLaw) (t : ℝ) : HasDerivAt (P3aU_Z S) (P3aU_Z1 S t) t := by
  unfold P3aU_Z P3aU_Z1
  convert HasDerivAt.fun_sum (u := S.A) (A := fun x s => (S.ρ x : ℝ) * Real.exp (s * (x : ℝ)))
      (A' := fun x => (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ))) (x := t) (fun x _ => ?_)
  have hmul : HasDerivAt (fun s : ℝ => s * (x : ℝ)) (x : ℝ) t := by
    simpa using (hasDerivAt_id t).mul_const (x : ℝ)
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (s * (x : ℝ))) (Real.exp (t * (x : ℝ)) * (x : ℝ)) t :=
    hmul.exp
  have hd := hexp.const_mul (S.ρ x : ℝ)
  rw [show (S.ρ x : ℝ) * (Real.exp (t * (x : ℝ)) * (x : ℝ)) =
      (S.ρ x : ℝ) * (x : ℝ) * Real.exp (t * (x : ℝ)) from by ring] at hd
  exact hd

lemma P3aU_hasDerivAt_Z1 (S : SpinLaw) (t : ℝ) : HasDerivAt (P3aU_Z1 S) (P3aU_Z2 S t) t := by
  unfold P3aU_Z1 P3aU_Z2
  convert HasDerivAt.fun_sum (u := S.A)
      (A := fun x s => (S.ρ x : ℝ) * (x : ℝ) * Real.exp (s * (x : ℝ)))
      (A' := fun x => (S.ρ x : ℝ) * (x : ℝ) ^ 2 * Real.exp (t * (x : ℝ))) (x := t) (fun x _ => ?_)
  have hmul : HasDerivAt (fun s : ℝ => s * (x : ℝ)) (x : ℝ) t := by
    simpa using (hasDerivAt_id t).mul_const (x : ℝ)
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (s * (x : ℝ))) (Real.exp (t * (x : ℝ)) * (x : ℝ)) t :=
    hmul.exp
  have hd := hexp.const_mul ((S.ρ x : ℝ) * (x : ℝ))
  rw [show (S.ρ x : ℝ) * (x : ℝ) * (Real.exp (t * (x : ℝ)) * (x : ℝ)) =
      (S.ρ x : ℝ) * (x : ℝ) ^ 2 * Real.exp (t * (x : ℝ)) from by ring] at hd
  exact hd

lemma P3aU_deriv_phi (S : SpinLaw) : deriv (phi S) = fun t => P3aU_Z1 S t / P3aU_Z S t := by
  funext t
  have hphi : phi S = fun s => Real.log (P3aU_Z S s) := rfl
  rw [hphi]
  have hd : HasDerivAt (fun s => Real.log (P3aU_Z S s)) (P3aU_Z1 S t / P3aU_Z S t) t :=
    (P3aU_hasDerivAt_Z S t).log (ne_of_gt (P3aU_Z_pos S t))
  exact hd.deriv

lemma P3aU_iteratedDeriv_one_zero (S : SpinLaw) : iteratedDeriv 1 (phi S) 0 = 0 := by
  rw [iteratedDeriv_one, P3aU_deriv_phi]
  dsimp only
  rw [P3aU_Z1_zero, P3aU_Z_zero]
  norm_num

lemma P3aU_iteratedDeriv_two_zero (S : SpinLaw) : iteratedDeriv 2 (phi S) 0 = variance S := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, P3aU_deriv_phi]
  have hd : HasDerivAt (fun t => P3aU_Z1 S t / P3aU_Z S t)
      ((P3aU_Z2 S 0 * P3aU_Z S 0 - P3aU_Z1 S 0 * P3aU_Z1 S 0) / P3aU_Z S 0 ^ 2) 0 :=
    (P3aU_hasDerivAt_Z1 S 0).div (P3aU_hasDerivAt_Z S 0) (ne_of_gt (P3aU_Z_pos S 0))
  rw [hd.deriv, P3aU_Z2_zero, P3aU_Z_zero, P3aU_Z1_zero]
  norm_num

lemma P3aU_phi_zero (S : SpinLaw) : phi S 0 = 0 := by
  change Real.log (P3aU_Z S 0) = 0
  rw [P3aU_Z_zero, Real.log_one]

lemma P3aU_phi_even (S : SpinLaw) (t : ℝ) : phi S (-t) = phi S t := by
  unfold phi
  have hsum :
      (∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp ((-t) * (x : ℝ))) =
      (∑ x ∈ S.A, (S.ρ x : ℝ) * Real.exp (t * (x : ℝ))) := by
    classical
    refine Finset.sum_bij (fun x _ => -x) ?_ ?_ ?_ ?_
    · intro x hx; exact S.neg_mem x hx
    · intro a _ b _ h; simpa using congrArg Neg.neg h
    · intro b hb; exact ⟨-b, S.neg_mem b hb, by simp⟩
    · intro x hx
      rw [S.symm x hx, Rat.cast_neg]
      congr 2
      ring
  rw [hsum]

lemma P3aU_Z_analyticOnNhd (S : SpinLaw) : AnalyticOnNhd ℝ (P3aU_Z S) Set.univ := by
  intro t _
  unfold P3aU_Z
  refine Finset.analyticAt_fun_sum S.A fun x _ => ?_
  exact analyticAt_const.mul (analyticAt_rexp.comp ((analyticAt_id : AnalyticAt ℝ id t).mul analyticAt_const))

lemma P3aU_phi_analyticOnNhd (S : SpinLaw) : AnalyticOnNhd ℝ (phi S) Set.univ := by
  intro t _
  change AnalyticAt ℝ (fun s => Real.log (P3aU_Z S s)) t
  exact (analyticAt_log (P3aU_Z_pos S t)).comp (P3aU_Z_analyticOnNhd S t (Set.mem_univ t))

lemma P3aU_phi_contDiff (S : SpinLaw) : ContDiff ℝ ⊤ (phi S) :=
  (P3aU_phi_analyticOnNhd S).contDiff

lemma P3aU_iteratedDeriv_even_symm (S : SpinLaw) (n : ℕ) :
    ∀ t : ℝ, iteratedDeriv n (phi S) (-t) = (-1 : ℝ) ^ n * iteratedDeriv n (phi S) t := by
  induction n with
  | zero =>
    intro t
    simp [P3aU_phi_even S t]
  | succ n ih =>
    intro t
    have hdiff : Differentiable ℝ (iteratedDeriv n (phi S)) :=
      (P3aU_phi_contDiff S).differentiable_iteratedDeriv n
        (by exact_mod_cast (WithTop.coe_lt_top (n : ℕ∞) : ((n : ℕ∞) : WithTop ℕ∞) < ⊤))
    have hleft : HasDerivAt (fun s => iteratedDeriv n (phi S) (-s))
        (-iteratedDeriv (n + 1) (phi S) (-t)) t := by
      have h1 : HasDerivAt (iteratedDeriv n (phi S)) (iteratedDeriv (n + 1) (phi S) (-t)) (-t) := by
        rw [iteratedDeriv_succ]
        exact (hdiff (-t)).hasDerivAt
      have hneg : HasDerivAt (fun s : ℝ => -s) (-1) t := (hasDerivAt_id t).neg
      have h2 : HasDerivAt (fun s : ℝ => iteratedDeriv n (phi S) (-s))
          (iteratedDeriv (n + 1) (phi S) (-t) * (-1)) t := h1.comp t hneg
      rw [mul_neg_one] at h2
      exact h2
    have hright : HasDerivAt (fun s => (-1 : ℝ) ^ n * iteratedDeriv n (phi S) s)
        ((-1 : ℝ) ^ n * iteratedDeriv (n + 1) (phi S) t) t := by
      rw [iteratedDeriv_succ]
      exact (hdiff t).hasDerivAt.const_mul ((-1 : ℝ) ^ n)
    have heqFun : (fun s => iteratedDeriv n (phi S) (-s)) =
        (fun s => (-1 : ℝ) ^ n * iteratedDeriv n (phi S) s) := funext ih
    rw [heqFun] at hleft
    have hderivEq := hleft.unique hright
    calc
      iteratedDeriv (n + 1) (phi S) (-t) = -(-iteratedDeriv (n + 1) (phi S) (-t)) := by ring
      _ = -((-1 : ℝ) ^ n * iteratedDeriv (n + 1) (phi S) t) := by rw [hderivEq]
      _ = (-1 : ℝ) ^ (n + 1) * iteratedDeriv (n + 1) (phi S) t := by
            rw [pow_succ]; ring

lemma P3aU_iteratedDeriv_odd_zero (S : SpinLaw) (k : ℕ) :
    iteratedDeriv (2 * k + 1) (phi S) 0 = 0 := by
  have h := P3aU_iteratedDeriv_even_symm S (2 * k + 1) 0
  simp only [neg_zero] at h
  have hpow : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [hpow] at h
  linarith

lemma P3aU_iteratedDeriv_add (m k : ℕ) (f : ℝ → ℝ) :
    iteratedDeriv m (iteratedDeriv k f) = iteratedDeriv (m + k) f := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    Function.iterate_add_apply]

lemma P3aU_contDiff_iteratedDeriv (k : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv k f) := by
  apply contDiff_of_differentiable_iteratedDeriv (n := ⊤)
  intro m _
  rw [P3aU_iteratedDeriv_add]
  exact hf.differentiable_iteratedDeriv (m + k)
    (by exact_mod_cast (WithTop.coe_lt_top ((m + k : ℕ) : ℕ∞) : (((m + k : ℕ) : ℕ∞) : WithTop ℕ∞) < ⊤))

lemma P3aU_quad_iteratedDeriv (c : ℝ) :
    (∀ n : ℕ, 3 ≤ n → iteratedDeriv n (fun t : ℝ => c * t ^ 2) 0 = 0) ∧
    iteratedDeriv 0 (fun t : ℝ => c * t ^ 2) 0 = 0 ∧
    iteratedDeriv 1 (fun t : ℝ => c * t ^ 2) 0 = 0 ∧
    iteratedDeriv 2 (fun t : ℝ => c * t ^ 2) 0 = 2 * c := by
  have hd1 : deriv (fun t : ℝ => c * t ^ 2) = fun t => 2 * c * t := by
    funext t
    have h : HasDerivAt (fun s : ℝ => c * s ^ 2) (2 * c * t) t := by
      have h0 := ((hasDerivAt_id' t).pow 2).const_mul c
      rw [show c * ((2 : ℕ) * t ^ (2 - 1) * 1) = 2 * c * t by norm_num; ring] at h0
      exact h0
    exact h.deriv
  have hd2 : deriv (fun t : ℝ => 2 * c * t) = fun _ => 2 * c := by
    funext t
    have h : HasDerivAt (fun s : ℝ => 2 * c * s) (2 * c) t := by
      have h0 := (hasDerivAt_id' t).const_mul (2 * c)
      rw [mul_one] at h0
      exact h0
    exact h.deriv
  have hd3 : deriv (fun _ : ℝ => (2 * c : ℝ)) = fun _ => 0 := by
    funext t
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [show m + 3 = (m + 1) + 2 from by ring]
    rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ', hd1, hd2, hd3]
    simp [iteratedDeriv_fun_const_zero]
  · simp
  · rw [iteratedDeriv_one, hd1]; simp
  · rw [iteratedDeriv_succ', iteratedDeriv_one, hd1, hd2]

lemma P3aU_exists_nonzero_even (S : SpinLaw) :
    ∃ p : ℕ, 2 ≤ p ∧ iteratedDeriv (2 * p) (phi S) 0 ≠ 0 := by
  by_contra hnone
  push Not at hnone
  let c : ℝ := variance S / 2
  let q : ℝ → ℝ := fun t => c * t ^ 2
  let g : ℝ → ℝ := fun t => phi S t - q t
  have hqDeriv := P3aU_quad_iteratedDeriv c
  have hgZero : ∀ n : ℕ, iteratedDeriv n g 0 = 0 := by
    intro n
    have hdiff_phi : ContDiff ℝ ⊤ (phi S) := P3aU_phi_contDiff S
    have hdiff_q : ContDiff ℝ ⊤ q := by fun_prop
    have hsub : iteratedDeriv n g 0 = iteratedDeriv n (phi S) 0 - iteratedDeriv n q 0 := by
      change iteratedDeriv n (phi S - q) 0 = _
      exact iteratedDeriv_fun_sub (hdiff_phi.contDiffAt.of_le le_top)
        (hdiff_q.contDiffAt.of_le le_top)
    rw [hsub]
    rcases lt_trichotomy n 2 with hn2 | rfl | hn2
    · interval_cases n
      · rw [iteratedDeriv_zero, iteratedDeriv_zero, P3aU_phi_zero]
        dsimp [q]; norm_num
      · rw [P3aU_iteratedDeriv_one_zero, hqDeriv.2.2.1]; norm_num
    · rw [P3aU_iteratedDeriv_two_zero, hqDeriv.2.2.2]
      dsimp [c]
      ring
    · have hn3 : 3 ≤ n := hn2
      rw [hqDeriv.1 n hn3, sub_zero]
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
      · have hk2 : 2 ≤ k := by omega
        rw [show n = 2 * k from by omega]
        exact hnone k hk2
      · rw [hk]
        exact P3aU_iteratedDeriv_odd_zero S k
  have hgAnalytic : AnalyticAt ℝ g 0 := by
    have h1 : AnalyticAt ℝ (phi S) 0 := P3aU_phi_analyticOnNhd S 0 (Set.mem_univ 0)
    have h2 : AnalyticAt ℝ q 0 := by fun_prop
    exact h1.sub h2
  have hps := hgAnalytic.hasFPowerSeriesAt
  have hseriesZero : FormalMultilinearSeries.ofScalars ℝ
      (fun n => iteratedDeriv n g 0 / (n ! : ℝ)) = 0 := by
    ext n
    simp [hgZero n]
  rw [hseriesZero] at hps
  obtain ⟨r, hr⟩ := hps
  have hev : g =ᶠ[nhds 0] 0 := by
    filter_upwards [Metric.eball_mem_nhds 0 hr.r_pos] with t ht
    have hgt : g (0 + t) = 0 := (hr.hasSum ht).unique hasSum_zero
    rw [zero_add] at hgt
    exact hgt
  have hevZ : P3aU_Z S =ᶠ[nhds 0] (fun t => Real.exp (q t)) := by
    filter_upwards [hev] with t ht
    have hgt : phi S t = q t := sub_eq_zero.mp ht
    calc
      P3aU_Z S t = Real.exp (Real.log (P3aU_Z S t)) := (Real.exp_log (P3aU_Z_pos S t)).symm
      _ = Real.exp (phi S t) := rfl
      _ = Real.exp (q t) := by rw [hgt]
  have hZan : AnalyticOnNhd ℝ (P3aU_Z S) Set.univ := P3aU_Z_analyticOnNhd S
  have hexpAn : AnalyticOnNhd ℝ (fun t => Real.exp (q t)) Set.univ := by
    intro t _
    exact analyticAt_rexp.comp (by fun_prop)
  have hEqAll : ∀ t : ℝ, P3aU_Z S t = Real.exp (q t) :=
    fun t => hZan.eqOn_of_preconnected_of_eventuallyEq hexpAn isPreconnected_univ
      (Set.mem_univ 0) hevZ (Set.mem_univ t)
  have hcpos : 0 < c := by
    dsimp [c]
    linarith [P3aU_variance_pos S]
  let t0 : ℝ := max 1 (2 / c)
  have ht0pos : 0 < t0 := lt_of_lt_of_le (by norm_num) (le_max_left 1 (2 / c))
  have ht0ge : 2 / c ≤ t0 := le_max_right 1 (2 / c)
  have hqt0 : t0 < q t0 := by
    have h1 : 2 ≤ c * t0 := (div_le_iff₀ hcpos).mp ht0ge |>.trans_eq (mul_comm t0 c)
    dsimp [q]
    nlinarith
  have hexplt : Real.exp |t0| < Real.exp (q t0) := by
    rw [abs_of_pos ht0pos]
    exact Real.exp_lt_exp.mpr hqt0
  have hZle := P3aU_Z_le_exp_abs S t0
  rw [hEqAll t0] at hZle
  linarith

lemma P3aU_exists_typeP (S : SpinLaw) (hS : IsGHS S) : ∃ p : ℕ, IsTypeP S p := by
  classical
  have hex := P3aU_exists_nonzero_even S
  let P : ℕ → Prop := fun p => 2 ≤ p ∧ iteratedDeriv (2 * p) (phi S) 0 ≠ 0
  let p : ℕ := Nat.find hex
  have hpSpec : P p := Nat.find_spec hex
  have hp2 : 2 ≤ p := hpSpec.1
  have hpne : iteratedDeriv (2 * p) (phi S) 0 ≠ 0 := hpSpec.2
  have hpmin : ∀ j : ℕ, 2 ≤ j → j < p → iteratedDeriv (2 * j) (phi S) 0 = 0 := by
    intro j hj2 hjp
    by_contra hne
    exact Nat.find_min hex hjp ⟨hj2, hne⟩
  have hneg : iteratedDeriv (2 * p) (phi S) 0 < 0 := by
    by_contra hnot
    have hpos : 0 < iteratedDeriv (2 * p) (phi S) 0 :=
      lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm hpne)
    let f : ℝ → ℝ := iteratedDeriv 3 (phi S)
    have hf_contDiff : ContDiff ℝ (⊤ : ℕ∞) f :=
      P3aU_contDiff_iteratedDeriv 3 (P3aU_phi_contDiff S)
    have hf_deriv_cont : Continuous (iteratedDeriv (2 * p - 3) f) :=
      hf_contDiff.continuous_iteratedDeriv (2 * p - 3)
        (by rw [← WithTop.coe_natCast]; exact WithTop.coe_le_coe.mpr le_top)
    have hderiv_eq : iteratedDeriv (2 * p - 3) f 0 = iteratedDeriv (2 * p) (phi S) 0 := by
      dsimp [f]
      rw [P3aU_iteratedDeriv_add]
      congr 1
      omega
    have hfpos0 : 0 < iteratedDeriv (2 * p - 3) f 0 := by
      rw [hderiv_eq]
      exact hpos
    have hnhds : ∀ᶠ x in nhds (0 : ℝ), 0 < iteratedDeriv (2 * p - 3) f x :=
      hf_deriv_cont.continuousAt.eventually (Ioi_mem_nhds hfpos0)
    obtain ⟨δ, hδpos, hδball⟩ := Metric.eventually_nhds_iff.mp hnhds
    let t : ℝ := δ / 2
    have htpos : 0 < t := by dsimp [t]; linarith
    have htne : (0 : ℝ) ≠ t := ne_of_lt htpos
    let n : ℕ := 2 * p - 4
    have hm1 : n + 1 = 2 * p - 3 := by dsimp [n]; omega
    have hfC : ContDiffOn ℝ (n + 1) f (Set.uIcc 0 t) :=
      (hf_contDiff.of_le (by
        rw [show ((n : WithTop ℕ∞) + 1) = ((2 * p - 3 : ℕ) : WithTop ℕ∞) from by
          dsimp [n]; norm_cast]
        rw [← WithTop.coe_natCast]
        exact WithTop.coe_le_coe.mpr le_top)).contDiffOn
    obtain ⟨x', hx'mem, hx'eq⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv htne hfC
    have htayZero : taylorWithinEval f (2 * p - 4) (Set.uIcc 0 t) 0 t = 0 := by
      rw [taylor_within_apply]
      apply Finset.sum_eq_zero
      intro k hk
      have hk_le : k ≤ 2 * p - 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hu : UniqueDiffOn ℝ (Set.uIcc 0 t) := uniqueDiffOn_uIcc htne
      have h0mem : (0 : ℝ) ∈ Set.uIcc 0 t := Set.left_mem_uIcc
      have hwithin : iteratedDerivWithin k f (Set.uIcc 0 t) 0 = iteratedDeriv k f 0 :=
        iteratedDerivWithin_eq_iteratedDeriv hu
          ((hf_contDiff.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt) h0mem
      have hk_zero : iteratedDeriv k f 0 = 0 := by
        dsimp [f]
        rw [P3aU_iteratedDeriv_add]
        have hlt : k + 3 < 2 * p := by omega
        rcases Nat.even_or_odd (k + 3) with ⟨j, hj⟩ | ⟨j, hj⟩
        · have hj2 : 2 ≤ j := by omega
          have hjp : j < p := by omega
          rw [show k + 3 = 2 * j from by omega]
          exact hpmin j hj2 hjp
        · rw [hj]
          exact P3aU_iteratedDeriv_odd_zero S j
      rw [hwithin, hk_zero, smul_zero]
    rw [htayZero, sub_zero, hm1] at hx'eq
    have hx'Ioo : x' ∈ Set.Ioo 0 t := by
      simpa [Set.uIoo_of_lt htpos] using hx'mem
    have hx'dist : dist x' 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hx'Ioo.1]
      have ht_lt : t < δ := by dsimp [t]; linarith
      linarith [hx'Ioo.2, ht_lt]
    have hx'pos : 0 < iteratedDeriv (2 * p - 3) f x' := hδball hx'dist
    have hftpos : 0 < f t := by
      rw [hx'eq]
      positivity
    have hftle : f t ≤ 0 := hS t htpos.le
    linarith
  exact ⟨p, hp2, hpmin, hneg⟩

lemma P3aU_unique_type (S : SpinLaw) (hS : IsGHS S) : ∃! p : ℕ, IsTypeP S p := by
  obtain ⟨p, hp⟩ := P3aU_exists_typeP S hS
  refine ⟨p, hp, ?_⟩
  intro q hq
  rcases lt_trichotomy q p with hqp | rfl | hpq
  · have h0 := hp.2.1 q hq.1 hqp
    have hlt := hq.2.2
    linarith
  · rfl
  · have h0 := hq.2.1 p hp.1 hpq
    have hlt := hp.2.2
    linarith

end CritWinSpin

open CritWinSpin

/-- Lemma 3.1(i), uniqueness of the type. -/
theorem solution (S : SpinLaw) (hS : IsGHS S) :
    ∃! p : ℕ, IsTypeP S p :=
  P3aU_unique_type S hS
