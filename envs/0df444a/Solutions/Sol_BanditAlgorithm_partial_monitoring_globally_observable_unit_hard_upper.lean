-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_globally_observable_unit_hard_upper
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T20:23:47.740743+00:00
-- url     : https://prove2.me/submissions/cb846bf5-1932-422a-96b5-f3ac287431a0

import Theorems.Thm_BanditAlgorithm_partial_monitoring_globally_observable_bounded_vector_estimator
import Theorems.Thm_BanditAlgorithm_partial_monitoring_algorithm26_master_bound
import Theorems.Thm_BanditAlgorithm_pmPsi_le_quadratic
import Theorems.Thm_BanditAlgorithm_pmMinimaxRegret_le_policy_of_unit_losses
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BanditAlgorithm

noncomputable section

private lemma rpow_two_thirds_schedule (A B η₀ : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hη₀ : 0 < η₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ η : ℝ, 0 < η ∧ η ≤ η₀ ∧
        A / η + (n : ℝ) * η * (B / Real.sqrt η) ≤
          C * (n : ℝ) ^ ((2 : ℝ) / 3) := by
  let C := A + B + A / η₀ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n hn
  have hx : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  let t : ℝ := (n : ℝ) ^ ((1 : ℝ) / 3)
  have ht : 0 < t := Real.rpow_pos_of_pos hx _
  have ht2 : t ^ 2 = (n : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
  have ht3 : t ^ 3 = (n : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
  let η := η₀ / (η₀ * t ^ 2 + 1)
  have hden : 0 < η₀ * t ^ 2 + 1 := by positivity
  have hη : 0 < η := div_pos hη₀ hden
  have hηle : η ≤ η₀ := by
    rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg hη₀.le (sq_nonneg t)]
  have hetaInv : A / η = A * t ^ 2 + A / η₀ := by
    dsimp [η]
    field_simp [hη₀.ne']
  have hηt : η ≤ 1 / t ^ 2 := by
    dsimp [η]
    rw [div_le_div_iff₀ hden (sq_pos_of_pos ht)]
    nlinarith [sq_nonneg t]
  have hsqrtη : Real.sqrt η ≤ 1 / t := by
    have hs := Real.sqrt_le_sqrt hηt
    rw [Real.sqrt_div (by positivity : 0 ≤ (1 : ℝ)), Real.sqrt_one,
      Real.sqrt_sq_eq_abs, abs_of_pos ht] at hs
    exact hs
  have hsqrtpos : 0 < Real.sqrt η := Real.sqrt_pos.2 hη
  have heta_sqrt : η / Real.sqrt η = Real.sqrt η := by
    rw [div_eq_iff hsqrtpos.ne']
    simpa [pow_two] using (Real.sq_sqrt hη.le).symm
  refine ⟨η, hη, hηle, ?_⟩
  rw [hetaInv]
  have hsecond : (n : ℝ) * η * (B / Real.sqrt η) ≤ B * t ^ 2 := by
    calc
      (n : ℝ) * η * (B / Real.sqrt η) = (n : ℝ) * B * (η / Real.sqrt η) := by ring
      _ = (n : ℝ) * B * Real.sqrt η := by rw [heta_sqrt]
      _ ≤ (n : ℝ) * B * (1 / t) := by gcongr
      _ = B * t ^ 2 := by rw [← ht3]; field_simp [ht.ne']
  rw [← ht2]
  calc
    A * t ^ 2 + A / η₀ + (n : ℝ) * η * (B / Real.sqrt η) ≤
        A * t ^ 2 + A / η₀ + B * t ^ 2 := by linarith
    _ ≤ C * t ^ 2 := by
      have ht1 : 1 ≤ t := by
        dsimp [t]
        exact Real.one_le_rpow (by exact_mod_cast hn) (by norm_num)
      dsimp [C]
      nlinarith [sq_nonneg t, mul_le_mul_of_nonneg_left ht1 (div_nonneg hA hη₀.le)]

private lemma global_exploration_objective
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k)
    (hL : ∀ a i, G.L a i ∈ Set.Icc (0 : ℝ) 1)
    (S : Finset (Fin k)) (q : Fin k → ℝ) (hq : PMSupportedOn S q)
    (f : Fin k → 𝕊 → Fin k → ℝ) (hf : PMVectorEstimatorOn G S f)
    (V : ℝ) (hV : 0 ≤ V) (hfV : ∀ a σ b, |f a σ b| ≤ V)
    (η : ℝ) (hη : 0 < η)
    (hηsmall : η ≤ 1 / (((k : ℝ) * max 1 V) ^ 2 + 1)) :
    ∃ p : Fin k → ℝ,
      PMInteriorDistribution p ∧ PMVectorEstimatorOn G S f ∧
      ∀ i : Fin d,
        pmAlgorithm26Objective G η q p f i ≤
          ((1 : ℝ) + (k : ℝ) ^ 2 * (max 1 V) ^ 2) / Real.sqrt η := by
  classical
  have hkpos : 0 < k := by omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  let W : ℝ := max 1 V
  have hWpos : 0 < W := lt_of_lt_of_le zero_lt_one (le_max_left 1 V)
  have hVW : V ≤ W := le_max_right 1 V
  let γ : ℝ := Real.sqrt η
  have hγ : 0 < γ := Real.sqrt_pos.2 hη
  have hηone : η ≤ 1 := by
    calc
      η ≤ 1 / (((k : ℝ) * W) ^ 2 + 1) := by simpa [W] using hηsmall
      _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith [sq_nonneg ((k : ℝ) * W)]
  have hγone : γ ≤ 1 := by
    dsimp [γ]
    simpa using (Real.sqrt_le_one.mpr hηone)
  let u : Fin k → ℝ := fun _ => 1 / k
  have hu : u ∈ stdSimplex ℝ (Fin k) := by
    constructor
    · intro a
      dsimp [u]
      positivity
    · simp [u, hkpos.ne']
  let p : Fin k → ℝ := fun a => (1 - γ) * q a + γ * u a
  have hp : p ∈ stdSimplex ℝ (Fin k) := by
    constructor
    · intro a
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr hγone) (hq.1.1 a))
        (mul_nonneg hγ.le (hu.1 a))
    · dsimp [p]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hq.1.2, hu.2]
      ring
  have hpLower (a : Fin k) : γ / k ≤ p a := by
    dsimp [p, u]
    calc
      γ / (k : ℝ) = γ * (1 / (k : ℝ)) := by ring
      _ ≤ (1 - γ) * q a + γ * (1 / (k : ℝ)) :=
        le_add_of_nonneg_left (mul_nonneg (sub_nonneg.mpr hγone) (hq.1.1 a))
  have hpPos (a : Fin k) : 0 < p a :=
    (div_pos hγ hkR).trans_le (hpLower a)
  have hηeq : η = γ ^ 2 := by
    dsimp [γ]
    exact (Real.sq_sqrt hη.le).symm
  have hηkW : η * ((k : ℝ) * W) ≤ γ := by
    have hbound : γ * ((k : ℝ) * W) ≤ 1 := by
      have hs := Real.sqrt_le_sqrt hηsmall
      have hden : 0 < (((k : ℝ) * W) ^ 2 + 1) := by positivity
      have hs' : γ ≤ 1 / Real.sqrt ((((k : ℝ) * W) ^ 2 + 1)) := by
        simpa [γ, Real.sqrt_div (by positivity : 0 ≤ (1 : ℝ))] using hs
      have hsqrtLower : (k : ℝ) * W ≤
          Real.sqrt ((((k : ℝ) * W) ^ 2 + 1)) := by
        have hsqrt0 := Real.sqrt_nonneg ((((k : ℝ) * W) ^ 2 + 1))
        have hsqrtSq := Real.sq_sqrt (show 0 ≤ (((k : ℝ) * W) ^ 2 + 1) by positivity)
        nlinarith [sq_nonneg ((k : ℝ) * W)]
      have hkw0 : 0 ≤ (k : ℝ) * W := mul_nonneg hkR.le hWpos.le
      calc
        γ * ((k : ℝ) * W) ≤
            (1 / Real.sqrt ((((k : ℝ) * W) ^ 2 + 1))) * ((k : ℝ) * W) :=
              mul_le_mul_of_nonneg_right hs' hkw0
        _ ≤ 1 := by
          rw [div_mul_eq_mul_div, div_le_one (Real.sqrt_pos.2 hden)]
          simpa using hsqrtLower
    rw [hηeq, pow_two]
    nlinarith [hγ]
  have hstab : ∀ a σ b, -1 ≤ η * f a σ b / p a := by
    intro a σ b
    have hfneg : -W ≤ f a σ b :=
      (neg_le_neg hVW).trans (neg_le_of_abs_le (hfV a σ b))
    have hden : η * W ≤ p a := by
      calc
        η * W ≤ γ / k := by
          apply (le_div_iff₀ hkR).2
          simpa [mul_assoc, mul_left_comm, mul_comm] using hηkW
        _ ≤ p a := hpLower a
    apply (le_div_iff₀ (hpPos a)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hfneg hη.le]
  refine ⟨p, ⟨hp, hpPos⟩, hf, ?_⟩
  intro i
  have hloss : ∑ a : Fin k, (p a - q a) * G.L a i ≤ γ := by
    have hterm (a : Fin k) : (u a - q a) * G.L a i ≤ u a := by
      have hqa : 0 ≤ q a := hq.1.1 a
      have hLa := hL a i
      dsimp [u]
      nlinarith [mul_nonneg hqa hLa.1, mul_le_mul_of_nonneg_left hLa.2 (by positivity : 0 ≤ 1 / (k : ℝ))]
    have hsum : ∑ a : Fin k, (u a - q a) * G.L a i ≤ 1 := by
      calc
        _ ≤ ∑ a : Fin k, u a := Finset.sum_le_sum fun a _ => hterm a
        _ = 1 := hu.2
    dsimp [p]
    rw [show (∑ a : Fin k, (((1 - γ) * q a + γ * u a) - q a) * G.L a i) =
        γ * ∑ a : Fin k, (u a - q a) * G.L a i by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a ha
          ring]
    simpa using mul_le_mul_of_nonneg_left hsum hγ.le
  have hquad : ∑ a : Fin k, p a *
      (∑ b : Fin k, q b * (η * f a (G.Φ a i) b / p a) ^ 2) ≤
      η ^ 2 * ((k : ℝ) ^ 2 * W ^ 2 / γ) := by
    have hterm (a b : Fin k) :
        p a * (q b * (η * f a (G.Φ a i) b / p a) ^ 2) ≤
          η ^ 2 * (q b * ((k : ℝ) * W ^ 2 / γ)) := by
      have hf2 : (f a (G.Φ a i) b) ^ 2 ≤ W ^ 2 := by
        have habs : |f a (G.Φ a i) b| ≤ W := (hfV a _ b).trans hVW
        have hpw : 0 ≤ (W - |f a (G.Φ a i) b|) *
            (W + |f a (G.Φ a i) b|) :=
          mul_nonneg (sub_nonneg.mpr habs)
            (add_nonneg hWpos.le (abs_nonneg _))
        nlinarith [sq_abs (f a (G.Φ a i) b)]
      have hinv : 1 / p a ≤ (k : ℝ) / γ := by
        rw [div_le_div_iff₀ (hpPos a) hγ]
        have := hpLower a
        field_simp [hkR.ne'] at this ⊢
        nlinarith
      have hqb : 0 ≤ q b := hq.1.1 b
      calc
        p a * (q b * (η * f a (G.Φ a i) b / p a) ^ 2) =
            η ^ 2 * (q b * (f a (G.Φ a i) b) ^ 2) * (1 / p a) := by
              field_simp [ne_of_gt (hpPos a)]
        _ ≤ η ^ 2 * (q b * W ^ 2) * (1 / p a) := by
              apply mul_le_mul_of_nonneg_right
              · exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hf2 hqb) (sq_nonneg η)
              · exact (one_div_pos.mpr (hpPos a)).le
        _ ≤ η ^ 2 * (q b * W ^ 2) * ((k : ℝ) / γ) := by
              exact mul_le_mul_of_nonneg_left hinv
                (mul_nonneg (sq_nonneg η) (mul_nonneg hqb (sq_nonneg W)))
        _ = η ^ 2 * (q b * ((k : ℝ) * W ^ 2 / γ)) := by ring
    calc
      _ = ∑ a : Fin k, ∑ b : Fin k,
          p a * (q b * (η * f a (G.Φ a i) b / p a) ^ 2) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.mul_sum]
      _ ≤ ∑ a : Fin k, ∑ b : Fin k,
          η ^ 2 * (q b * ((k : ℝ) * W ^ 2 / γ)) := by
            exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b
      _ = ∑ a : Fin k, η ^ 2 * (((k : ℝ) * W ^ 2 / γ)) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [← Finset.mul_sum, ← Finset.sum_mul, hq.1.2, one_mul]
      _ = η ^ 2 * ((k : ℝ) ^ 2 * W ^ 2 / γ) := by
            simp
            field_simp [hγ.ne']
  have hpsi (a : Fin k) :
      pmPsi q (fun b => η * f a (G.Φ a i) b / p a) ≤
        ∑ b : Fin k, q b * (η * f a (G.Φ a i) b / p a) ^ 2 :=
    pmPsi_le_quadratic q _ hq.1 (fun b => hstab a (G.Φ a i) b)
  have hpsisum : ∑ a : Fin k, p a *
      pmPsi q (fun b => η * f a (G.Φ a i) b / p a) ≤
      η ^ 2 * ((k : ℝ) ^ 2 * W ^ 2 / γ) :=
    (Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hpsi a) (hp.1 a)).trans hquad
  unfold pmAlgorithm26Objective
  have hηne := hη.ne'
  have hγne := hγ.ne'
  calc
    _ ≤ (1 / η) * γ + (1 / η ^ 2) *
        (η ^ 2 * ((k : ℝ) ^ 2 * W ^ 2 / γ)) :=
      add_le_add (mul_le_mul_of_nonneg_left hloss (by positivity))
        (mul_le_mul_of_nonneg_left hpsisum (by positivity))
    _ = ((1 : ℝ) + (k : ℝ) ^ 2 * W ^ 2) / γ := by
      rw [hηeq]
      field_simp [hγne]
    _ = ((1 : ℝ) + (k : ℝ) ^ 2 * W ^ 2) / Real.sqrt η := rfl

theorem _root_.solution
    {k d : ℕ} {𝕊 : Type*}
    [Fintype 𝕊] [MeasurableSpace 𝕊] [MeasurableSingletonClass 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k) (hd : 0 < d)
    (hL : ∀ a i, G.L a i ∈ Set.Icc (0 : ℝ) 1)
    (hglo : GloballyObservable G) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      pmMinimaxRegret G n ≤ C * (n : ℝ) ^ ((2 : ℝ) / 3) := by
  classical
  obtain ⟨S, V, hS, hV, hbest, f, hf, hfV⟩ :=
    partial_monitoring_globally_observable_bounded_vector_estimator G hk hd hglo
  let W : ℝ := max 1 V
  let D : ℝ := 1 + (k : ℝ) ^ 2 * W ^ 2
  let η₀ : ℝ := 1 / (((k : ℝ) * W) ^ 2 + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hη₀ : 0 < η₀ := by dsimp [η₀]; positivity
  have hlog : 0 ≤ Real.log S.card :=
    Real.log_nonneg (by exact_mod_cast Finset.one_le_card.mpr hS)
  obtain ⟨C, hC, hschedule⟩ := rpow_two_thirds_schedule (Real.log S.card) D η₀ hlog hD hη₀
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨η, hη, hηle, hscalar⟩ := hschedule n hn
  have hsolve : ∀ q : Fin k → ℝ, PMSupportedOn S q →
      ∃ p : Fin k → ℝ, ∃ ff : Fin k → 𝕊 → Fin k → ℝ,
        PMInteriorDistribution p ∧ PMVectorEstimatorOn G S ff ∧
        ∀ i : Fin d, pmAlgorithm26Objective G η q p ff i ≤ D / Real.sqrt η := by
    intro q hq
    obtain ⟨p, hp, hf', hobj⟩ := global_exploration_objective
      G hk hL S q hq f hf V hV hfV η hη (by simpa [η₀, W] using hηle)
    exact ⟨p, f, hp, hf', by simpa [D, W] using hobj⟩
  obtain ⟨π, hπ⟩ := partial_monitoring_algorithm26_master_bound
    G S hS η (D / Real.sqrt η) hη hd hbest hsolve n
  exact (pmMinimaxRegret_le_policy_of_unit_losses G (by omega) hL π).trans
    (hπ.trans hscalar)

end
end BanditAlgorithm
