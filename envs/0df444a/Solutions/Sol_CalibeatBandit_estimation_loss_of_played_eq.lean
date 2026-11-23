-- Prove2me | solution 1 for CalibeatBandit.estimation_loss_of_played_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T18:57:18.291248+00:00
-- url     : https://prove2.me/submissions/c152d4d0-bf66-4f51-a5a2-97390fc88693

import Mathlib
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_IsProbVec
import Definitions.Def_CalibeatBandit_pseudoRewardLoss
import Definitions.Def_CalibeatBandit_rewardLoss
import Definitions.Def_CalibeatBandit_HSRof
import Definitions.Def_CalibeatBandit_HRecOf
import Definitions.Def_CalibeatBandit_algState
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_Supplement_PricingRegretBound
import Definitions.Def_CalibeatBandit_draw_run

section

set_option autoImplicit false
set_option maxHeartbeats 150000

open Matrix MeasureTheory
open scoped BigOperators

namespace CalibeatBandit

theorem explore_prob {K : ℕ} (hK : 0 < K) {μ : ℝ} (hμ₀ : 0 ≤ μ) (hμ₁ : μ ≤ 1)
    {x : Fin K → ℝ} (hx : IsProbVec x) : IsProbVec (explore μ x) := by
  have hk : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  constructor
  · intro i
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hμ₁) (hx.1 i)) (by positivity)
  · simp only [explore, Finset.sum_add_distrib, ← Finset.mul_sum, hx.2, mul_one,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
    ring

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}

theorem measurable_select {α : Type*} [Fintype α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {a : Ω → α} (ha : Measurable a)
    {f : α → Ω → ℝ} (hf : ∀ i, Measurable (f i)) :
    Measurable (fun ω => f (a ω) ω) := by
  classical
  have heq : (fun ω => f (a ω) ω) =
      fun ω => ∑ i, if a ω = i then f i ω else 0 := by
    funext ω
    simp
  rw [heq]
  exact Finset.measurable_sum _ fun i _ => Measurable.ite (ha (measurableSet_singleton i)) (hf i) measurable_const

end Measurability

theorem estimate_scaled_mem {K : ℕ} {η μ : ℝ} (hK : 0 < K)
    (hη : 0 < η) (hμ : μ ≤ 1 / 2) (hKη : 4 * K * η ≤ μ)
    (x : Fin K → ℝ) (hx : IsProbVec x) (I j : Fin K) (obs : ℝ)
    (hobs : obs ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ η * estimate η (explore μ x) I obs j ∧
      η * estimate η (explore μ x) I obs j ≤ 1 := by
  let p := explore μ x j
  let d := (Real.exp 1 - 2) * η
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  have hk₁ : 1 ≤ (K : ℝ) := by exact_mod_cast hK
  have hη₈ : η ≤ 1 / 8 := by nlinarith [mul_nonneg (sub_nonneg.mpr hk₁) hη.le]
  have hp : 4 * η ≤ p := by
    change 4 * η ≤ (1 - μ) * x j + μ / K
    have hle := (le_div_iff₀ hk).mpr (show 4 * η * K ≤ μ by linarith only [hKη])
    exact hle.trans (le_add_of_nonneg_left (mul_nonneg (by linarith) (hx.1 j)))
  have hp₀ : 0 < p := lt_of_lt_of_le (by positivity) hp
  have hd₀ : 0 ≤ d := mul_nonneg (sub_nonneg.mpr Real.exp_one_gt_two.le) hη.le
  have hd₁ : d ≤ η := by
    dsimp [d]
    nlinarith [mul_nonneg (show 0 ≤ 3 - Real.exp 1 by linarith [Real.exp_one_lt_three]) hη.le]
  let r := if I = j then obs else 0
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [r]
    split
    · exact hobs
    · exact ⟨le_rfl, zero_le_one⟩
  have hv : estimate η (explore μ x) I obs j = (r + d) / p := by
    change (if I = j then obs / p else 0) + d / p = _
    dsimp [r]
    split <;> simp [add_div]
  rw [hv]
  refine ⟨mul_nonneg hη.le (div_nonneg (add_nonneg hr.1 hd₀) hp₀.le), ?_⟩
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hp₀).mpr
  nlinarith [mul_nonneg hη.le (show 0 ≤ 4 - (r + d) by linarith [hr.2])]

end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

open MeasureTheory

namespace DrawRun

variable {K T : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem info_le_info (run : DrawRun K T P) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ T) :
    run.info a ≤ run.info b := by
  induction hab with
  | refl => exact le_rfl
  | step _ ih =>
    exact (ih (by omega)).trans ((run.info_le_preDraw _ (by omega)).trans (run.preDraw_le_succ _ (by omega)))

theorem preDraw_le_ambient (run : DrawRun K T P) {t : ℕ} (ht : t < T) :
    run.preDraw t ≤ mΩ :=
  (run.preDraw_le_succ t ht).trans (run.info_le _ (Nat.succ_le_of_lt ht))

end DrawRun

end CalibeatBandit

end

section

set_option autoImplicit false

open Matrix
open scoped BigOperators Nat

namespace CalibeatBandit

theorem exp_le_quadratic {z : ℝ} (hz₁ : z ≤ 1) :
    Real.exp z ≤ 1 + z + (Real.exp 1 - 2) * z ^ 2 := by
  by_cases hz : 0 ≤ z
  swap
  · have hz₀ : z ≤ 0 := le_of_not_ge hz
    have h : Real.exp z ≤ 1 + z + z ^ 2 / 2 := by
      let f (w : ℝ) := 1 + w + w ^ 2 / 2 - Real.exp w
      have hf' (w : ℝ) : HasDerivAt f (1 + w - Real.exp w) w := by
        have hd := (((hasDerivAt_id w).const_add 1).add ((hasDerivAt_pow 2 w).div_const 2)).sub
          (Real.hasDerivAt_exp w)
        convert hd using 1 <;> first | rfl | norm_num
      have hd : Differentiable ℝ f := fun w => (hf' w).differentiableAt
      have ha : AntitoneOn f (Set.Iic 0) :=
        antitoneOn_of_deriv_nonpos (convex_Iic _) hd.continuous.continuousOn hd.differentiableOn
          (fun w _ => by rw [(hf' w).deriv]; linarith [Real.add_one_le_exp w])
      have hcompare := ha (show z ∈ Set.Iic 0 from hz₀) (show 0 ∈ Set.Iic (0 : ℝ) by simp) hz₀
      have hzero : f 0 = 0 := by norm_num [f]
      rw [hzero] at hcompare
      exact sub_nonneg.mp hcompare
    have he : (1 / 2 : ℝ) ≤ Real.exp 1 - 2 := by
      linarith [Real.quadratic_le_exp_of_nonneg (x := 1) zero_le_one]
    nlinarith only [h, mul_nonneg (sub_nonneg.mpr he) (sq_nonneg z)]
  have series (a : ℝ) : HasSum (fun n : ℕ => a ^ n / (n ! : ℝ)) (Real.exp a) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp a
  have tail (a : ℝ) : (∑' n : ℕ, a ^ (n + 2) / ((n + 2)! : ℝ)) = Real.exp a - (1 + a) := by
    have h := (series a).summable.sum_add_tsum_nat_add 2
    rw [(series a).tsum_eq] at h
    norm_num [Finset.sum_range_succ] at h
    linarith
  have htail :
      (∑' n : ℕ, z ^ (n + 2) / ((n + 2)! : ℝ)) ≤
        ∑' n : ℕ, z ^ 2 * (1 ^ (n + 2) / ((n + 2)! : ℝ)) := by
    apply Summable.tsum_le_tsum
    · intro n
      simp only [one_pow, mul_one_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [pow_add, mul_comm (z ^ n)]
      exact mul_le_of_le_one_right (sq_nonneg z) (pow_le_one₀ hz hz₁)
    · exact (summable_nat_add_iff 2).2 (series z).summable
    · exact ((summable_nat_add_iff 2).2 (series 1).summable).mul_left _
  rw [tsum_mul_left, tail z, tail 1] at htail
  nlinarith only [htail]

end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit

/-- Conditional expectation of a bounded function evaluated at the played action. -/
theorem DrawRun.condExp_select_played {K T : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (run : DrawRun K T P) {t : ℕ} (ht : t < T)
    (g : Fin K → Ω → ℝ) (hg : ∀ j, Measurable[run.preDraw t] (g j))
    (B : ℝ) (hb : ∀ j ω, |g j ω| ≤ B) :
    Integrable (fun ω => g (run.I t ω) ω) P ∧
    condExp (run.preDraw t) P (fun ω => g (run.I t ω) ω) =ᵐ[P]
      fun ω => ∑ j, run.played t ω j * g j ω := by
  classical
  let ind (j : Fin K) : Ω → ℝ := (run.I t ⁻¹' {j}).indicator (fun _ => 1)
  have hm := run.preDraw_le_ambient ht
  have im (j : Fin K) : Measurable (ind j) :=
    measurable_const.indicator ((run.I_measurable t ht).mono
      (run.info_le _ (Nat.succ_le_of_lt ht)) le_rfl (measurableSet_singleton j))
  have ib (j : Fin K) (ω : Ω) : ind j ω ∈ Set.Icc (0 : ℝ) 1 := by
    by_cases h : run.I t ω = j <;> simp [ind, h]
  have ii (j : Fin K) : Integrable (ind j) P :=
    (integrable_const (1 : ℝ)).mono' (im j).aestronglyMeasurable (ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (ib j ω).1] using (ib j ω).2)
  have gi (j : Fin K) : Integrable (g j * ind j) P :=
    (integrable_const B).mono' (((hg j).mono hm le_rfl).mul (im j)).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        change ‖g j ω * ind j ω‖ ≤ B
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ib j ω).1]
        exact (mul_le_of_le_one_right (abs_nonneg _) (ib j ω).2).trans (hb j ω))
  have heq : (fun ω => g (run.I t ω) ω) = ∑ j, g j * ind j := by
    ext ω
    simp only [Finset.sum_apply, Pi.mul_apply, ind, Set.indicator_apply,
      Set.mem_preimage, Set.mem_singleton_iff, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  rw [heq]
  refine ⟨integrable_finsetSum' _ (fun j _ => gi j), (condExp_finsetSum (fun j _ => gi j) _).trans ?_⟩
  have hcoord (j : Fin K) :
      condExp (run.preDraw t) P (g j * ind j) =ᵐ[P] fun ω => g j ω * run.played t ω j := by
    refine (condExp_mul_of_stronglyMeasurable_left (hg j).stronglyMeasurable (gi j) (ii j)).trans ?_
    filter_upwards [run.I_law t ht j] with ω hω
    change condExp (run.preDraw t) P (ind j) ω = run.played t ω j at hω
    change g j ω * condExp (run.preDraw t) P (ind j) ω = _
    rw [hω]
  filter_upwards [ae_all_iff.mpr hcoord] with ω hω
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => (hω j).trans (mul_comm _ _)

end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory
open scoped BigOperators

namespace CalibeatBandit

theorem integrable_of_abs_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {f : Ω → ℝ} (hm : Measurable f) {B : ℝ}
    (hb : ∀ ω, |f ω| ≤ B) : Integrable f P :=
  (integrable_const B).mono' hm.aestronglyMeasurable
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hb ω)

theorem integral_exp_sum_le_one {T : ℕ} {Ω : Type*}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (info preDraw : ℕ → MeasurableSpace Ω)
    (hinfo : ∀ a b, a ≤ b → b ≤ T → info a ≤ info b)
    (hinfo_le : ∀ n ≤ T, info n ≤ mΩ)
    (hpre : ∀ n < T, preDraw n ≤ mΩ)
    (hprev : ∀ n < T, info n ≤ preDraw n)
    (d : ℕ → Ω → ℝ) {B : ℝ}
    (hm : ∀ t < T, Measurable[info (t + 1)] (d t))
    (hb : ∀ t < T, ∀ ω, |d t ω| ≤ B)
    (hc : ∀ t < T, condExp (preDraw t) P (fun ω => Real.exp (d t ω)) ≤ᵐ[P] fun _ => 1) :
    ∫ ω, Real.exp (∑ t ∈ Finset.range T, d t ω) ∂P ≤ 1 := by
  let F (n : ℕ) (ω : Ω) := Real.exp (∑ t ∈ Finset.range n, d t ω)
  have hF (n : ℕ) (hn : n ≤ T) : Measurable[info n] (F n) := by
    refine Real.continuous_exp.measurable.comp (Finset.measurable_sum _ fun t ht => ?_)
    have hs := Nat.succ_le_of_lt (Finset.mem_range.mp ht)
    exact (hm t (lt_of_lt_of_le (Finset.mem_range.mp ht) hn)).mono
      (hinfo _ _ hs hn) le_rfl
  have hi (n : ℕ) (hn : n ≤ T) : Integrable (F n) P := by
    apply integrable_of_abs_bound ((hF n hn).mono (hinfo_le n hn) le_rfl)
    intro ω
    rw [show F n ω = Real.exp (∑ t ∈ Finset.range n, d t ω) from rfl,
      abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ ∑ _ ∈ Finset.range n, B := Finset.sum_le_sum fun t ht =>
        (le_abs_self _).trans (hb t ((Finset.mem_range.mp ht).trans_le hn) ω)
      _ = (n : ℝ) * B := by simp
  have step (n : ℕ) (hn : n < T) : (∫ ω, F (n + 1) ω ∂P) ≤ ∫ ω, F n ω ∂P := by
    let G : Ω → ℝ := fun ω => Real.exp (d n ω)
    have hG : Integrable G P := by
      refine integrable_of_abs_bound (B := Real.exp B) (Real.continuous_exp.measurable.comp
        ((hm n hn).mono (hinfo_le _ (Nat.succ_le_of_lt hn)) le_rfl)) ?_
      intro ω
      change |Real.exp (d n ω)| ≤ Real.exp B
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hb n hn ω))
    have heq : F (n + 1) = F n * G := by
      funext ω
      simp [F, G, Finset.sum_range_succ, Real.exp_add]
    have hprod : Integrable (F n * G) P := heq ▸ hi (n + 1) (Nat.succ_le_of_lt hn)
    have hpull := condExp_mul_of_stronglyMeasurable_left
      ((hF n hn.le).mono (hprev n hn) le_rfl).stronglyMeasurable
      hprod hG
    rw [heq, ← integral_condExp (m := preDraw n) (hpre n hn)]
    apply integral_mono_ae integrable_condExp (hi n hn.le)
    filter_upwards [hpull, hc n hn] with ω hw hcω
    rw [hw]
    exact mul_le_of_le_one_right (Real.exp_nonneg _) hcω
  have hbound (n : ℕ) (hn : n ≤ T) : (∫ ω, F n ω ∂P) ≤ 1 := by
    induction n with
    | zero => simp [F]
    | succ n ih =>
      have hh : n < T := Nat.lt_of_succ_le hn
      exact (step n hh).trans (ih hh.le)
  exact hbound T le_rfl

theorem DrawRun.integral_exp_sum_le_one {K T : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : DrawRun K T P) (d : ℕ → Ω → ℝ) {B : ℝ}
    (hm : ∀ t < T, Measurable[run.info (t + 1)] (d t))
    (hb : ∀ t < T, ∀ ω, |d t ω| ≤ B)
    (hc : ∀ t < T, condExp (run.preDraw t) P (fun ω => Real.exp (d t ω)) ≤ᵐ[P] fun _ => 1) :
    ∫ ω, Real.exp (∑ t ∈ Finset.range T, d t ω) ∂P ≤ 1 :=
  CalibeatBandit.integral_exp_sum_le_one P run.info run.preDraw
    (fun _ _ h => run.info_le_info h) run.info_le
    (fun _ ht => run.preDraw_le_ambient ht) run.info_le_preDraw d hm hb hc

theorem integrable_finset_max {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsFiniteMeasure P] (hne : (Finset.univ : Finset ι).Nonempty)
    (F : ι → Ω → ℝ) {B : ℝ} (hm : ∀ i, Measurable (F i)) (hb : ∀ i ω, |F i ω| ≤ B) :
    Integrable (fun ω => Finset.univ.sup' hne (fun i => F i ω)) P := by
  let _ : Nonempty ι := hne.to_subtype.map Subtype.val
  apply integrable_of_abs_bound
  · simp_rw [Finset.sup'_univ_eq_ciSup]
    exact Measurable.iSup hm
  · intro ω
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hne (fun i => F i ω)
    exact hi.symm ▸ hb i ω

/-- A finite maximum is bounded in expectation by the logarithm of the number
of competitors whenever each competitor has an exponential moment at most one. -/
theorem integral_max_le_log_card {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (hne : (Finset.univ : Finset ι).Nonempty)
    (F : ι → Ω → ℝ) {η B : ℝ} (hη : 0 < η)
    (hm : ∀ i, Measurable (F i)) (hb : ∀ i ω, |F i ω| ≤ B)
    (he : ∀ i, ∫ ω, Real.exp (η * F i ω) ∂P ≤ 1) :
    ∫ ω, Finset.univ.sup' hne (fun i => F i ω) ∂P ≤ Real.log (Fintype.card ι) / η := by
  classical
  let M (ω : Ω) := Finset.univ.sup' hne (fun i => F i ω)
  let Z (ω : Ω) := ∑ i, Real.exp (η * F i ω)
  let N : ℝ := Fintype.card ι
  let H (ω : Ω) := Real.log N + (Z ω / N - 1)
  let _ : Nonempty ι := hne.to_subtype.map Subtype.val
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos (α := ι)
  have hM : Integrable M P := integrable_finset_max hne F hm hb
  have hei (i : ι) : Integrable (fun ω => Real.exp (η * F i ω)) P := by
    refine integrable_of_abs_bound (B := Real.exp (η * B))
      (Real.continuous_exp.measurable.comp ((hm i).const_mul η)) ?_
    intro ω
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hb i ω)) hη.le)
  have hZ : Integrable Z P := integrable_finsetSum _ fun i _ => hei i
  have hZi : (∫ ω, Z ω ∂P) ≤ N := by
    rw [show (∫ ω, Z ω ∂P) = ∑ i, ∫ ω, Real.exp (η * F i ω) ∂P from
      integral_finsetSum _ (fun i _ => hei i)]
    calc
      _ ≤ ∑ _ : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => he i
      _ = N := by simp [N]
  have hH : Integrable H P := (integrable_const _).add ((hZ.div_const N).sub (integrable_const _))
  have hpoint (ω : Ω) : η * M ω ≤ H ω := by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hne (fun i => F i ω)
    have hle : Real.exp (η * M ω) ≤ Z ω := by
      change Real.exp (η * Finset.univ.sup' hne (fun i => F i ω)) ≤ Z ω
      rw [hi]
      exact Finset.single_le_sum (fun j _ => Real.exp_nonneg (η * F j ω)) (Finset.mem_univ i)
    have hz : 0 < Z ω := (Real.exp_pos _).trans_le hle
    have hl := Real.log_le_log (Real.exp_pos _) hle
    rw [Real.log_exp] at hl
    have hh := Real.log_le_sub_one_of_pos (div_pos hz hN)
    rw [Real.log_div hz.ne' hN.ne'] at hh
    dsimp [H]
    linarith only [hl, hh]
  have hHi : (∫ ω, H ω ∂P) ≤ Real.log N := by
    let W : Ω → ℝ := fun ω => Z ω / N
    change (∫ ω, Real.log N + (W ω - 1) ∂P) ≤ _
    have hW : Integrable W P := hZ.div_const N
    have hdiff : Integrable (fun ω => W ω - 1) P := hW.sub (integrable_const _)
    rw [integral_add (integrable_const _) hdiff, integral_sub hW (integrable_const _)]
    dsimp only [W]
    rw [integral_div]
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    linarith only [(div_le_one hN).mpr hZi]
  have hi := (integral_mono (hM.const_mul η) hH hpoint).trans hHi
  have heq : (∫ ω, η * M ω ∂P) = η * ∫ ω, M ω ∂P := integral_const_mul η M
  rw [heq] at hi
  exact (le_div_iff₀ hη).mpr (by simpa only [mul_comm] using hi)

end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory
open scoped BigOperators

namespace CalibeatBandit

/-- A one-round exponential bound for the corrected estimate of a fixed action.
The two terms are the events that the learner plays or does not play that action. -/
theorem corrected_estimate_exp_le_one {η p y : ℝ} (hη : 0 ≤ η) (hη₁ : η ≤ 1)
    (hp : 0 < p) (hp₁ : p ≤ 1) (hy : 0 ≤ y) (hy₁ : y ≤ 1) :
    let d := (Real.exp 1 - 2) * η
    p * Real.exp (η * (y - (y + d) / p)) +
      (1 - p) * Real.exp (η * (y - d / p)) ≤ 1 := by
  intro d
  let c := Real.exp 1 - 2
  let a := η * (y - y / p)
  let b := η * y
  let k := c * η ^ 2 / p
  have hc : 0 ≤ c := sub_nonneg.mpr Real.exp_one_gt_two.le
  have hb : b ≤ 1 := (mul_le_of_le_one_right hη hy₁).trans hη₁
  have ha : a ≤ 1 := (mul_le_mul_of_nonneg_left (sub_le_self _ (div_nonneg hy hp.le)) hη).trans hb
  have hmean : p * a + (1 - p) * b = 0 := by
    dsimp [a, b]
    field_simp [hp.ne']
    ring
  have hsq : p * a ^ 2 + (1 - p) * b ^ 2 ≤ η ^ 2 / p := by
    have heq : p * a ^ 2 + (1 - p) * b ^ 2 = η ^ 2 * y ^ 2 * (1 - p) / p := by
      dsimp [a, b]
      field_simp [hp.ne']
      ring
    rw [heq]
    apply div_le_div_of_nonneg_right _ hp.le
    have hy2 : y ^ 2 ≤ 1 := by nlinarith [mul_nonneg hy (sub_nonneg.mpr hy₁)]
    have ht : y ^ 2 * (1 - p) ≤ 1 :=
      (mul_le_of_le_one_right (sq_nonneg y) (by linarith)).trans hy2
    simpa only [mul_assoc] using mul_le_of_le_one_right (sq_nonneg η) ht
  have htwo : p * Real.exp a + (1 - p) * Real.exp b ≤ 1 + k := by
    have hca := mul_le_mul_of_nonneg_left (exp_le_quadratic ha) hp.le
    have hcb := mul_le_mul_of_nonneg_left (exp_le_quadratic hb) (sub_nonneg.mpr hp₁)
    have hcs := mul_le_mul_of_nonneg_left hsq hc
    dsimp [k]
    rw [← mul_div_assoc] at hcs
    nlinarith only [hca, hcb, hmean, hcs]
  have ha_eq : η * (y - (y + d) / p) = -k + a := by
    dsimp [d, k, c, a]
    ring
  have hb_eq : η * (y - d / p) = -k + b := by
    dsimp [d, k, c, b]
    ring
  rw [ha_eq, hb_eq, Real.exp_add, Real.exp_add]
  calc
    _ = Real.exp (-k) * (p * Real.exp a + (1 - p) * Real.exp b) := by ring
    _ ≤ Real.exp (-k) * (1 + k) := mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg _)
    _ ≤ Real.exp (-k) * Real.exp k := by
      exact mul_le_mul_of_nonneg_left (by simpa only [add_comm] using Real.add_one_le_exp k)
        (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

set_option maxHeartbeats 650000 in
/-- The per-round conditional exponential bound for a weighted post-processing
rule. The weights may be selected using the information available before the draw. -/
theorem condExp_estimation_step_of_played_eq {K T : ℕ} {ι : Type*} [Fintype ι] {η μ : ℝ} (hK : 0 < K)
    (hη : 0 < η) (hμ₀ : 0 < μ) (hμ : μ ≤ 1 / 2) (hKη : 4 * K * η ≤ μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : DrawRun K T P) {t : ℕ} (ht : t < T)
    (x : Ω → Fin K → ℝ) (hx : ∀ ω, IsProbVec (x ω))
    (hxm : Measurable[run.preDraw t] x)
    (hplay : run.played t =ᵐ[P] fun ω => explore μ (x ω))
    (f : ι → Fin K) (w : Ω → ι → ℝ) (hw₀ : ∀ ω i, 0 ≤ w ω i)
    (hw : ∀ ω, ∑ i, w ω i = 1)
    (hwm : Measurable[run.preDraw t] w) :
    condExp (run.preDraw t) P (fun ω => Real.exp
      (η * ∑ i, w ω i * (run.y t ω (f i) - estimate η (explore μ (x ω)) (run.I t ω) (run.obs t ω) (f i)))) ≤ᵐ[P] fun _ => 1 := by
  classical
  let p (ω : Ω) := explore μ (x ω)
  let y (ω : Ω) := run.y t ω
  let d := (Real.exp 1 - 2) * η
  let g (j : Fin K) (ω : Ω) := Real.exp (η * ∑ i, w ω i *
    (y ω (f i) - (if j = f i then (y ω (f i) + d) / p ω (f i) else d / p ω (f i))))
  have hk : 0 < (K : ℝ) := by exact_mod_cast hK
  have hk₁ : 1 ≤ (K : ℝ) := by exact_mod_cast hK
  have hη₁ : η ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hk₁) hη.le]
  have hμ₁ : μ ≤ 1 := by linarith
  have hd : 0 ≤ d := mul_nonneg (sub_nonneg.mpr Real.exp_one_gt_two.le) hη.le
  have hp (ω : Ω) : IsProbVec (p ω) := explore_prob hK hμ₀.le hμ₁ (hx ω)
  have hp₀ (ω : Ω) (j : Fin K) : 0 < p ω j :=
    (div_pos hμ₀ hk).trans_le
      (le_add_of_nonneg_left (mul_nonneg (sub_nonneg.mpr hμ₁) ((hx ω).1 j)))
  have hp₁ (ω : Ω) (j : Fin K) : p ω j ≤ 1 :=
    (Finset.single_le_sum (fun i _ => (hp ω).1 i) (Finset.mem_univ j)).trans_eq (hp ω).2
  have hy (ω : Ω) (j : Fin K) : y ω j ∈ Set.Icc (0 : ℝ) 1 := run.y_mem t ht ω j
  have hmY (j : Fin K) : Measurable[run.preDraw t] (fun ω => y ω j) :=
    (measurable_pi_apply j).comp (run.y_measurable t ht)
  have hmP (j : Fin K) : Measurable[run.preDraw t] (fun ω => p ω j) :=
    (((measurable_pi_apply j).comp hxm).const_mul _).add measurable_const
  have hg (j : Fin K) : Measurable[run.preDraw t] (g j) := by
    apply Real.continuous_exp.measurable.comp
    apply Measurable.const_mul
    refine Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hwm).mul ?_
    by_cases e : j = f i
    · simp only [e, if_true]
      exact (hmY (f i)).sub (((hmY (f i)).add measurable_const).div (hmP (f i)))
    · simp only [if_neg e]
      exact (hmY (f i)).sub (measurable_const.div (hmP (f i)))
  have hgb (j : Fin K) (ω : Ω) : |g j ω| ≤ Real.exp η := by
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    refine mul_le_of_le_one_right hη.le ?_
    calc
      _ ≤ ∑ i, w ω i * 1 := Finset.sum_le_sum fun i _ => by
        apply mul_le_mul_of_nonneg_left _ (hw₀ ω i)
        refine (sub_le_self _ ?_).trans (hy ω (f i)).2
        split
        · exact div_nonneg (add_nonneg (hy ω (f i)).1 hd) (hp₀ ω (f i)).le
        · exact div_nonneg hd (hp₀ ω (f i)).le
      _ = _ := by simp only [mul_one, hw ω]
  obtain ⟨_, hce⟩ := run.condExp_select_played P ht g hg _ hgb
  have hselected : (fun ω => g (run.I t ω) ω) = fun ω => Real.exp
      (η * ∑ i, w ω i * (run.y t ω (f i) - estimate η (explore μ (x ω)) (run.I t ω) (run.obs t ω) (f i))) := by
    funext ω
    apply congrArg Real.exp
    refine congrArg (η * ·) (Finset.sum_congr rfl fun i _ => ?_)
    dsimp [y, p]
    change w ω i * (run.y t ω (f i) - _) = w ω i * (run.y t ω (f i) -
      ((if run.I t ω = f i then run.obs t ω / p ω (f i) else 0) +
        d / p ω (f i)))
    by_cases e : run.I t ω = f i
    · simp [e, p, DrawRun.obs, add_div]
    · simp [e, p]
  rw [← hselected]
  filter_upwards [hce, hplay] with ω he hpω
  rw [he, hpω]
  change ∑ j, p ω j * g j ω ≤ 1
  let a (j : Fin K) (i : ι) := η *
    (y ω (f i) - (if j = f i then (y ω (f i) + d) / p ω (f i) else d / p ω (f i)))
  have hjensen (j : Fin K) : g j ω ≤ ∑ i, w ω i * Real.exp (a j i) := by
    have h := convexOn_exp.map_sum_le (t := Finset.univ) (w := w ω) (p := a j)
      (fun i _ => hw₀ ω i) (hw ω) (fun i _ => Set.mem_univ (a j i))
    have heq : g j ω = Real.exp (∑ i, w ω i * a j i) := by
      unfold g a
      simp only [Finset.mul_sum]
      apply congrArg Real.exp
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [heq]
    simpa only [smul_eq_mul] using h
  calc
    _ ≤ ∑ j, p ω j * ∑ i, w ω i * Real.exp (a j i) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hjensen j) ((hp ω).1 j)
    _ = ∑ i, w ω i * ∑ j, p ω j * Real.exp (a j i) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ ∑ i, w ω i * 1 := by
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left ?_ (hw₀ ω i)
      let j := f i
      have hs : (∑ k ∈ Finset.univ.erase j, p ω k) = 1 - p ω j := by
        have h := Finset.sum_erase_add _ (fun k => p ω k) (Finset.mem_univ j)
        rw [(hp ω).2] at h
        linarith
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
      have hdiff : (∑ k ∈ Finset.univ.erase j, p ω k * Real.exp (a k i)) =
          (1 - p ω j) * Real.exp (η * (y ω j - d / p ω j)) := by
        rw [← hs, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k hk => ?_
        have hn := (Finset.mem_erase.mp hk).1
        simp [a, j, hn]
      rw [hdiff]
      have hsame : a j i = η * (y ω j - (y ω j + d) / p ω j) := by simp [a, j]
      rw [hsame, add_comm]
      exact corrected_estimate_exp_le_one hη.le hη₁ (hp₀ ω j) (hp₁ ω j) (hy ω j).1 (hy ω j).2
    _ = 1 := by simp only [mul_one, hw ω]

set_option maxHeartbeats 500000 in
/-- The estimation bound for an arbitrary finite reference set. -/
theorem estimation_loss_of_played_eq {K T : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hne : (Finset.univ : Finset (ι → Fin K)).Nonempty)
    {η μ : ℝ} (hK : 0 < K) (hη : 0 < η) (hμ₀ : 0 < μ)
    (hμ : μ ≤ 1 / 2) (hKη : 4 * K * η ≤ μ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (run : DrawRun K T P)
    (x : ℕ → Ω → Fin K → ℝ) (hx : ∀ t < T, ∀ ω, IsProbVec (x t ω))
    (hxm : ∀ t < T, Measurable[run.preDraw t] (x t))
    (hplay : ∀ t < T, run.played t =ᵐ[P] fun ω => explore μ (x t ω))
    (w : ℕ → Ω → ι → ℝ) (hw₀ : ∀ t < T, ∀ ω i, 0 ≤ w t ω i)
    (hw : ∀ t < T, ∀ ω, ∑ i, w t ω i = 1)
    (hwm : ∀ t < T, Measurable[run.preDraw t] (w t)) :
    let v := fun t ω => estimate η (explore μ (x t ω)) (run.I t ω) (run.obs t ω)
    ∫ ω, Finset.univ.sup' hne (fun f : ι → Fin K =>
      ∑ t ∈ Finset.range T, ∑ i, w t ω i * (run.y t ω (f i) - v t ω (f i))) ∂P
      ≤ Fintype.card ι * Real.log K / η := by
  intro v
  classical
  have hvb (t : ℕ) (ht : t < T) (ω : Ω) (j : Fin K) :
      0 ≤ η * v t ω j ∧ η * v t ω j ≤ 1 :=
    estimate_scaled_mem hK hη hμ hKη (x t ω) (hx t ht ω) (run.I t ω) j
      (run.obs t ω) (run.y_mem t ht ω (run.I t ω))
  have hvm (t : ℕ) (ht : t < T) (j : Fin K) :
      Measurable[run.info (t + 1)] (fun ω => v t ω j) := by
    have hxm' := ((measurable_pi_apply j).comp (hxm t ht)).mono (run.preDraw_le_succ t ht) le_rfl
    have hp : Measurable[run.info (t + 1)] (fun ω => explore μ (x t ω) j) :=
      (hxm'.const_mul (1 - μ)).add measurable_const
    have hy : Measurable[run.info (t + 1)] (run.obs t) := by
      unfold DrawRun.obs
      exact @measurable_select Ω (run.info (t + 1)) (Fin K) _ _ _ _ (run.I_measurable t ht)
        (fun j ω => run.y t ω j) (fun j => (measurable_pi_apply j).comp
          ((run.y_measurable t ht).mono (run.preDraw_le_succ t ht) le_rfl))
    exact (Measurable.ite (run.I_measurable t ht (measurableSet_singleton j))
      (hy.div hp) measurable_const).add (measurable_const.div hp)
  let D (t : ℕ) (f : ι → Fin K) (ω : Ω) :=
    ∑ i, w t ω i * (run.y t ω (f i) - v t ω (f i))
  have hm (t : ℕ) (ht : t < T) (f : ι → Fin K) :
      Measurable[run.info (t + 1)] (D t f) := by
    refine Finset.measurable_sum _ fun i _ => ?_
    have hwi := (measurable_pi_apply i).comp
      ((hwm t ht).mono (run.preDraw_le_succ t ht) le_rfl)
    have hyi := (measurable_pi_apply (f i)).comp
      ((run.y_measurable t ht).mono (run.preDraw_le_succ t ht) le_rfl)
    exact hwi.mul (hyi.sub (hvm t ht (f i)))
  have hb (t : ℕ) (ht : t < T) (f : ι → Fin K) (ω : Ω) :
      |D t f ω| ≤ 1 + 1 / η := by
    calc
      _ ≤ ∑ i, |w t ω i * (run.y t ω (f i) - v t ω (f i))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, w t ω i * (1 + 1 / η) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hw₀ := hw₀ t ht ω i
        rw [abs_mul, abs_of_nonneg hw₀]
        apply mul_le_mul_of_nonneg_left _ hw₀
        have hy := run.y_mem t ht ω (f i)
        have hv := hvb t ht ω (f i)
        have hv₀ := nonneg_of_mul_nonneg_right hv.1 hη
        have hv₁ := (le_div_iff₀ hη).mpr (by simpa only [mul_comm] using hv.2)
        exact abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2, div_nonneg zero_le_one hη.le]⟩
      _ = _ := by rw [← Finset.sum_mul, hw t ht ω, one_mul]
  let F (f : ι → Fin K) (ω : Ω) := ∑ t ∈ Finset.range T, D t f ω
  have hmF (f : ι → Fin K) : Measurable (F f) :=
    Finset.measurable_sum _ fun t ht =>
      (hm t (Finset.mem_range.mp ht) f).mono (run.info_le _ (Finset.mem_range.mp ht)) le_rfl
  have hbF (f : ι → Fin K) (ω : Ω) : |F f ω| ≤ T * (1 + 1 / η) := by
    calc
      _ ≤ ∑ t ∈ Finset.range T, |D t f ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ Finset.range T, (1 + 1 / η) := Finset.sum_le_sum fun t ht =>
        hb t (Finset.mem_range.mp ht) f ω
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hE (f : ι → Fin K) : (∫ ω, Real.exp (η * F f ω) ∂P) ≤ 1 := by
    have h := run.integral_exp_sum_le_one P (fun t ω => η * D t f ω)
      (fun t ht => (hm t ht f).const_mul η)
      (fun t ht ω => show |η * D t f ω| ≤ η * (1 + 1 / η) by
        rw [abs_mul, abs_of_pos hη]
        exact mul_le_mul_of_nonneg_left (hb t ht f ω) hη.le)
      (fun t ht => condExp_estimation_step_of_played_eq hK hη hμ₀ hμ hKη P run ht
        (x t) (hx t ht) (hxm t ht) (hplay t ht) f (w t) (hw₀ t ht) (hw t ht) (hwm t ht))
    simpa only [F, Finset.mul_sum] using h
  have h := integral_max_le_log_card P hne F hη hmF hbF hE
  simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Real.log_pow] using h

end CalibeatBandit

end

theorem solution : type_of% @CalibeatBandit.estimation_loss_of_played_eq := @CalibeatBandit.estimation_loss_of_played_eq
