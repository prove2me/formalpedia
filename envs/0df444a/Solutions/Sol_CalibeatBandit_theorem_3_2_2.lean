-- Prove2me | solution 2 for CalibeatBandit.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T17:32:26.067622+00:00
-- url     : https://prove2.me/submissions/4a29bd82-a4d9-4bbb-bfc9-9df7a7855d0c

import Mathlib
import Definitions.Def_CalibeatBandit_IsProbVec
import Definitions.Def_CalibeatBandit_IsColStochastic
import Definitions.Def_CalibeatBandit_fixedPointSol
import Definitions.Def_CalibeatBandit_calibeatPolicy
import Definitions.Def_CalibeatBandit_algState
import Definitions.Def_CalibeatBandit_HSRof
import Definitions.Def_CalibeatBandit_HRecOf
import Definitions.Def_CalibeatBandit_pseudoRewardLoss
import Definitions.Def_CalibeatBandit_rewardLoss
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_rT
import Definitions.Def_CalibeatBandit_swapRegret
import Definitions.Def_CalibeatBandit_etaStar
import Definitions.Def_CalibeatBandit_IsCalibeating
import Theorems.Thm_CalibeatBandit_pseudo_regret_bound
import Theorems.Thm_CalibeatBandit_rec_identity_C_1
import Theorems.Thm_CalibeatBandit_sampling_conversion_C_1

section

set_option autoImplicit false

open Matrix
open scoped BigOperators Nat

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false

open Matrix
open Filter
open scoped BigOperators Topology

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false
set_option maxHeartbeats 150000

open Matrix MeasureTheory
open scoped BigOperators

namespace CalibeatBandit


section Measurability

variable {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}


end Measurability

namespace ProtocolRun

variable {K T : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {policy : Policy K}


end ProtocolRun

end CalibeatBandit

end

section

set_option autoImplicit false

open MeasureTheory Matrix Filter
open scoped BigOperators

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false

open Matrix
open scoped BigOperators

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false

open MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false

open MeasureTheory Matrix Filter
open scoped BigOperators

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory
open scoped BigOperators

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory
open scoped BigOperators

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false

open Matrix CalibeatBandit
open scoped BigOperators


end

section

set_option autoImplicit false

open MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false

open Filter MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit


end CalibeatBandit

end

section

set_option autoImplicit false

namespace CalibeatBandit

/-- At the stated horizon the tuned parameters are admissible and the explicit
swap-regret bound is at most \(\varepsilon T\). -/
theorem etaStar_spec {K T : ℕ} {ε : ℝ} (hK : 2 ≤ K) (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hT : 1024 * (K : ℝ) ^ 2 * Real.log K / ε ^ 2 ≤ T) :
    0 < etaStar K T ∧ 0 < muStar K T ∧ muStar K T ≤ 1 / 2 ∧
    rT K T (etaStar K T) (muStar K T) + Real.sqrt (2 * T * K * Real.log K) ≤ ε * T := by
  let k : ℝ := K
  let t : ℝ := T
  let d : ℝ := k * Real.log k
  let b : ℝ := 2 * d + Real.log 2
  let a := Real.sqrt (b / (14 * k * t))
  let q := k * a
  have hk : 2 ≤ k := by dsimp [k]; exact_mod_cast hK
  have hk₀ : 0 < k := by linarith
  have hlog₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log k := Real.log_le_log (by norm_num) hk
  have hd : 0 < d := mul_pos hk₀ (hlog₂.trans_le hlog)
  have hb : 0 < b := by dsimp [b]; linarith
  have hb_le : b ≤ 3 * d := by
    have h := mul_nonneg (show 0 ≤ k - 1 by linarith) (hlog₂.trans_le hlog).le
    dsimp [b, d]
    linarith
  have hlog_pos : 0 < Real.log k := hlog₂.trans_le hlog
  have ht : 0 < t := lt_of_lt_of_le (by change 0 < 1024 * k ^ 2 * Real.log k / ε ^ 2; positivity) hT
  have htd : 1024 * k * d ≤ t * ε ^ 2 := by
    have h := (div_le_iff₀ (sq_pos_of_pos hε)).mp hT
    dsimp [d, k, t]
    nlinarith only [h]
  have ha : 0 < a := Real.sqrt_pos.mpr (by positivity)
  have haq : a ^ 2 * (14 * k * t) = b := by
    have h : a ^ 2 = b / (14 * k * t) := Real.sq_sqrt (by positivity)
    exact (eq_div_iff (by positivity)).mp h
  have hq : 0 < q := mul_pos hk₀ ha
  have hqt : 14 * q ^ 2 * t = k * b := by
    dsimp [q]
    linear_combination k * haq
  have hq_le : q ≤ ε / 32 := by
    have h₁ := mul_le_mul_of_nonneg_left hb_le hk₀.le
    have h₂ : 1024 * q ^ 2 * t ≤ ε ^ 2 * t := by
      nlinarith only [hqt, h₁, htd, mul_nonneg hk₀.le hd.le]
    have h₃ := le_of_mul_le_mul_right (show (32 * q) ^ 2 * t ≤ ε ^ 2 * t by
      nlinarith only [h₂]) ht
    by_contra! h
    have hprod := mul_pos (sub_pos.mpr (show ε < 32 * q by linarith))
      (show 0 < 32 * q + ε by positivity)
    nlinarith only [hprod, h₃]
  have hη : etaStar K T = a := by
    unfold etaStar
    have hsqrt : Real.sqrt ((2 * (K : ℝ) * Real.log K + Real.log 2) / (14 * K * T)) = a := by
      dsimp [a, b, d, k, t]
      congr 2
      ring
    rw [hsqrt]
    apply min_eq_right
    apply (le_div_iff₀ (by positivity)).mpr
    change a * (8 * k) ≤ 1
    dsimp [q] at hq_le
    nlinarith only [hq_le, hε₁]
  have hμ : muStar K T = 4 * q := by unfold muStar; rw [hη]; dsimp [q, k]; ring
  have hμ_le : 4 * q ≤ 1 / 2 := by linarith
  have hrec : rT K T (etaStar K T) (muStar K T) ≤ 28 * q * t := by
    rw [hη, hμ]
    have hba : b / a = 14 * q * t := by
      apply (div_eq_iff ha.ne').mpr
      dsimp [q]
      nlinarith only [haq]
    have hden : 0 < 1 - 4 * q := by linarith
    have hterm : 5 * q * t / (1 - 4 * q) ≤ 10 * q * t := by
      apply (div_le_iff₀ hden).mpr
      nlinarith only [mul_nonneg (show 0 ≤ q * t by positivity)
        (show 0 ≤ 1 / 2 - 4 * q by linarith)]
    unfold rT
    have hcoeff : 2 * (K : ℝ) * Real.log K + Real.log 2 = b := by dsimp [b, d, k]; ring
    rw [hcoeff]
    change 4 * q * t + b / a + (5 * a * k * t) / (1 - 4 * q) ≤ _
    rw [hba, show 5 * a * k * t = 5 * q * t by dsimp [q]; ring]
    linarith
  have hs : Real.sqrt (2 * t * k * Real.log k) ≤ ε * t / 8 := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    have h₁ : 128 * d ≤ t * ε ^ 2 := by
      have h₂ := mul_nonneg (show 0 ≤ 1024 * k - 128 by linarith) hd.le
      nlinarith only [h₂, htd]
    have h₂ := mul_le_mul_of_nonneg_right h₁ ht.le
    dsimp [d] at h₂
    nlinarith only [h₂]
  refine ⟨hη ▸ ha, hμ ▸ mul_pos (by norm_num) hq, hμ ▸ hμ_le, ?_⟩
  have h₁ := mul_le_mul_of_nonneg_right hq_le ht.le
  change _ + Real.sqrt (2 * t * k * Real.log k) ≤ ε * t
  nlinarith only [hrec, hs, h₁]

end CalibeatBandit

end

section

set_option autoImplicit false

open MeasureTheory Matrix
open scoped BigOperators

namespace CalibeatBandit

universe u

/-- The finite-horizon inequalities in the first conjunct of Theorem 3.2. -/
def HasFiniteHorizonBounds : Prop :=
  ∀ (K T : ℕ) (η μ : ℝ), 0 < K → 0 < η → 0 < μ → μ ≤ 1 / 2 → 4 * K * η ≤ μ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (run : ProtocolRun K T P (calibeatPolicy K η μ)),
      ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P
          ≤ rT K T η μ + Real.sqrt (2 * T * K * Real.log K) ∧
      ∫ ω, rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) ∂P
          ≤ rT K T η μ

private theorem benchmark_le_horizon {K T : ℕ} (y : ℕ → Fin K → ℝ) (I J : ℕ → Fin K)
    (hy : ∀ t < T, ∀ j, y t j ∈ Set.Icc (0 : ℝ) 1) :
    swapRegret T y I ≤ T ∧ rewardLoss T y J I ≤ T := by
  have h (a b : ℕ → Fin K) :
      ∑ t ∈ Finset.range T, (y t (a t) - y t (b t)) ≤ (T : ℝ) := by
    calc
      _ ≤ ∑ _ ∈ Finset.range T, (1 : ℝ) := Finset.sum_le_sum fun t ht => by
        have ha := hy t (Finset.mem_range.mp ht) (a t)
        have hb := hy t (Finset.mem_range.mp ht) (b t)
        exact sub_le_self _ hb.1 |>.trans ha.2
      _ = _ := by simp
  constructor
  · unfold swapRegret
    exact Finset.sup'_le _ _ fun f _ => h (fun t => f (I t)) I
  · unfold rewardLoss
    exact Finset.sup'_le _ _ fun f _ => h (fun t => f (J t)) I

private theorem integral_le_const {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (f : Ω → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hf : ∀ ω, f ω ≤ C) : ∫ ω, f ω ∂P ≤ C := by
  by_cases hi : Integrable f P
  · calc
      _ ≤ ∫ _ : Ω, C ∂P := integral_mono hi (integrable_const C) hf
      _ = C := by simp
  · rwa [integral_undef hi]

private theorem one_action_calibeating (T : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (policy : Policy 1) : IsCalibeating.{u} 1 T ε ε policy := by
  intro Ω m P pP run
  have h {a b : ℕ → Fin 1} (ω : Ω) (f : Fin 1 → Fin 1) :
      ∑ t ∈ Finset.range T, (run.y t ω (f (a t)) - run.y t ω (b t)) = 0 := by
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [Subsingleton.elim (f (a t)) (b t), sub_self]
  have hSR (ω : Ω) : swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) = 0 := by
    unfold swapRegret
    simp_rw [h]
    exact Finset.sup'_const _ _
  have hRec (ω : Ω) : rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) = 0 := by
    unfold rewardLoss
    simp_rw [h]
    exact Finset.sup'_const _ _
  simp only [hSR, hRec, integral_zero, and_self]
  positivity

/-- The normalized and sample-complexity conclusions of Theorem 3.2 follow
from the finite-horizon bounds. -/
theorem normalized_and_tuned (h : HasFiniteHorizonBounds.{u}) :
    (∀ (K T : ℕ) (η μ : ℝ), 0 < K → 0 < η → 0 < μ → μ ≤ 1 / 2 → 4 * K * η ≤ μ →
      IsCalibeating.{u} K T (rT K T η μ / T + Real.sqrt (2 * K * Real.log K / T))
        (rT K T η μ / T) (calibeatPolicy K η μ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (K T : ℕ) (ε : ℝ), 0 < K → 0 < ε →
      C * K ^ 2 * Real.log K / ε ^ 2 ≤ T →
      IsCalibeating.{u} K T ε ε (calibeatPolicy K (etaStar K T) (muStar K T))) := by
  constructor
  · intro K T η μ hK hη hμ₀ hμ₁ hKη Ω m P pP run
    by_cases hT : T = 0
    · subst T
      simp [swapRegret, rewardLoss]
      exact Finset.sup'_le _ _ fun _ _ => le_rfl
    have ht : 0 < (T : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hT
    have hn : 0 ≤ 2 * (K : ℝ) * Real.log K := by
      have hk : 1 ≤ (K : ℝ) := by exact_mod_cast hK
      exact mul_nonneg (by positivity) (Real.log_nonneg hk)
    have hsqrt : Real.sqrt (2 * K * Real.log K / T) * T =
        Real.sqrt (2 * T * K * Real.log K) := by
      rw [Real.sqrt_div hn]
      have hsq := Real.sq_sqrt ht.le
      have hpos := Real.sqrt_pos.mpr ht
      have ht' : (T : ℝ) = Real.sqrt T * Real.sqrt T := by nlinarith only [hsq]
      calc
        Real.sqrt (2 * K * Real.log K) / Real.sqrt T * T =
            Real.sqrt (2 * K * Real.log K) * Real.sqrt T := by
          apply (div_mul_eq_mul_div _ _ _).trans
          apply (div_eq_iff hpos.ne').mpr
          linear_combination Real.sqrt (2 * K * Real.log K) * ht'
        _ = _ := by rw [← Real.sqrt_mul hn]; congr 1; ring
    simpa only [add_mul, div_mul_cancel₀ _ ht.ne', hsqrt] using h K T η μ hK hη hμ₀ hμ₁ hKη P run
  · refine ⟨1024, by norm_num, ?_⟩
    intro K T ε hK hε hT
    by_cases hk : K = 1
    · subst K
      exact one_action_calibeating T hε.le _
    by_cases hε₁ : ε ≤ 1
    · have hp := etaStar_spec (K := K) (T := T) (ε := ε) (by omega) hε hε₁ hT
      intro P pP run
      have hb := h K T (etaStar K T) (muStar K T) hK hp.1 hp.2.1 hp.2.2.1
        (le_refl _) P run
      have hs : 0 ≤ Real.sqrt (2 * T * K * Real.log K) := Real.sqrt_nonneg _
      exact ⟨hb.1.trans hp.2.2.2, hb.2.trans (by linarith [hp.2.2.2])⟩
    · intro P pP run
      have hTε : (T : ℝ) ≤ ε * T := le_mul_of_one_le_left (by positivity) (le_of_not_ge hε₁)
      exact ⟨(integral_le_const P _ T (by positivity) fun ω =>
          (benchmark_le_horizon _ _ (fun t => run.J t ω) fun t ht j => run.y_mem t ht ω j).1).trans hTε,
        (integral_le_const P _ T (by positivity) fun ω =>
          (benchmark_le_horizon _ _ _ fun t ht j => run.y_mem t ht ω j).2).trans hTε⟩
theorem finite_horizon_bounds : HasFiniteHorizonBounds.{u} := by
  intro K T η μ hK hη hμ₀ hμ hKη Ω m P pP run
  obtain ⟨hs, hr⟩ := pseudo_regret_bound hK hη hμ₀ hμ hKη P run
  have hs' := sampling_conversion_C_1 P _ run hK
  obtain ⟨hr', hzero⟩ := rec_identity_C_1 P _ run
  have hsum : (∑ t ∈ Finset.range T, ∫ ω,
      (run.played t ω ⬝ᵥ run.y t ω - run.y t ω (run.I t ω)) ∂P) = 0 :=
    Finset.sum_eq_zero fun t ht => hzero t (Finset.mem_range.mp ht)
  rw [hsum, sub_zero] at hr'
  exact ⟨hs'.trans (add_le_add_left hs _), hr'.symm.le.trans hr⟩

/-- Theorem 3.2. The finite-horizon regret bounds, their normalized
calibeating guarantee, and the round complexity with the tuned parameters. -/
theorem theorem_3_2 :
    (∀ (K T : ℕ) (η μ : ℝ), 0 < K → 0 < η → 0 < μ → μ ≤ 1 / 2 → 4 * K * η ≤ μ →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (run : ProtocolRun K T P (calibeatPolicy K η μ)),
        ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P
            ≤ rT K T η μ + Real.sqrt (2 * T * K * Real.log K) ∧
        ∫ ω, rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) ∂P
            ≤ rT K T η μ) ∧
    (∀ (K T : ℕ) (η μ : ℝ), 0 < K → 0 < η → 0 < μ → μ ≤ 1 / 2 → 4 * K * η ≤ μ →
      IsCalibeating.{u} K T (rT K T η μ / T + Real.sqrt (2 * K * Real.log K / T))
        (rT K T η μ / T) (calibeatPolicy K η μ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (K T : ℕ) (ε : ℝ), 0 < K → 0 < ε →
      C * K ^ 2 * Real.log K / ε ^ 2 ≤ T →
      IsCalibeating.{u} K T ε ε (calibeatPolicy K (etaStar K T) (muStar K T))) :=
  ⟨finite_horizon_bounds, normalized_and_tuned finite_horizon_bounds⟩

end CalibeatBandit

end

open CalibeatBandit MeasureTheory Matrix

universe u

theorem solution :
    (∀ (K T : ℕ) (η μ : ℝ), 0 < K → 0 < η → 0 < μ → μ ≤ 1 / 2 → 4 * K * η ≤ μ →
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (run : ProtocolRun K T P (calibeatPolicy K η μ)),
        ∫ ω, swapRegret T (fun t => run.y t ω) (fun t => run.I t ω) ∂P
            ≤ rT K T η μ + Real.sqrt (2 * T * K * Real.log K) ∧
        ∫ ω, rewardLoss T (fun t => run.y t ω) (fun t => run.J t ω) (fun t => run.I t ω) ∂P
            ≤ rT K T η μ) ∧
    (∀ (K T : ℕ) (η μ : ℝ), 0 < K → 0 < η → 0 < μ → μ ≤ 1 / 2 → 4 * K * η ≤ μ →
      IsCalibeating.{u} K T (rT K T η μ / T + Real.sqrt (2 * K * Real.log K / T))
        (rT K T η μ / T) (calibeatPolicy K η μ)) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (K T : ℕ) (ε : ℝ), 0 < K → 0 < ε →
      C * K ^ 2 * Real.log K / ε ^ 2 ≤ T →
      IsCalibeating.{u} K T ε ε (calibeatPolicy K (etaStar K T) (muStar K T))) := CalibeatBandit.theorem_3_2
