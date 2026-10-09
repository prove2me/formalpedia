-- Prove2me | solution 1 for CVPricing.Regret.cvp_regret_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-08T16:20:11.144172+00:00
-- url     : https://prove2.me/submissions/6d9c8856-2703-4fb3-b5a4-2b44e70e3f34
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares
import Definitions.Def_CVPricing_Regret_Model
import Definitions.Def_CVPricing_Regret_CVP
import Definitions.Def_CVPricing_Regret_Process
import Theorems.Thm_CVPricing_Regret_price_sq_error_rate
import Theorems.Thm_CVPricing_Regret_revenue_quadratic_gap

set_option autoImplicit false

open MeasureTheory

namespace Red0f2d3266

open MeasureTheory CVPricing.Regret

theorem prices_mem (M : Model) (α c : ℝ) (p d : ℕ → ℝ) (h : IsCVPPath M α c p d) :
    ∀ t : ℕ, 1 ≤ t → p t ∈ Set.Icc M.pl M.ph := by
  obtain ⟨h1, h2, -, -, -, -, hstep⟩ := h
  intro t ht
  induction t with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · exact h1
      · exact h2
    · rcases hstep n hn with ⟨-, hF⟩ | ⟨a, -, -, hF⟩ | ⟨a, -, -, hE⟩
      · rcases hF.1 with e | e <;> rw [e] <;> assumption
      · rcases hF.1 with e | e <;> rw [e] <;> assumption
      · rcases hE with ⟨-, hm, -⟩ | ⟨-, hm⟩
        · exact hm.1
        · exact hm.1.1

theorem rpow_gap (β x : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hx : 1 ≤ x) :
    β * x ^ (β - 1) ≤ x ^ β - (x - 1) ^ β := by
  have hx0 : 0 < x := by linarith
  have hs : -1 ≤ -(1 / x) := by
    rw [neg_le_neg_iff, div_le_one hx0]; exact hx
  have key := rpow_one_add_le_one_add_mul_self hs hβ0 hβ1
  have e1 : x - 1 = x * (1 + -(1 / x)) := by field_simp; ring
  have hnn : 0 ≤ 1 + -(1 / x) := by linarith
  rw [e1, Real.mul_rpow hx0.le hnn, Real.rpow_sub_one hx0.ne' β]
  have hxb : 0 ≤ x ^ β := Real.rpow_nonneg hx0.le β
  have h3 := mul_le_mul_of_nonneg_left key hxb
  have e3 : x ^ β * (1 + β * -(1 / x)) = x ^ β - β * (x ^ β / x) := by field_simp; ring
  linarith

theorem sum_rpow_le (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (T : ℕ) (hT : 1 ≤ T) :
    ∑ t ∈ Finset.Icc 2 T, (t : ℝ) ^ (β - 1) ≤ (T : ℝ) ^ β / β := by
  induction T, hT using Nat.le_induction with
  | base => simp; positivity
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hn' : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
    have hg := rpow_gap β ((n : ℝ) + 1) hβ0.le hβ1 hn'
    have e : ((n : ℝ) + 1 - 1) = n := by ring
    rw [e] at hg
    push_cast
    rw [le_div_iff₀ hβ0] at ih ⊢
    have e2 : (∑ t ∈ Finset.Icc 2 n, (t : ℝ) ^ (β - 1) + ((n : ℝ) + 1) ^ (β - 1)) * β
        = (∑ t ∈ Finset.Icc 2 n, (t : ℝ) ^ (β - 1)) * β + β * ((n : ℝ) + 1) ^ (β - 1) := by ring
    rw [e2]; linarith

theorem rate_sum (α : ℝ) (h0 : 0 < α) (h1 : α < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T →
      ∑ t ∈ Finset.Icc 2 T, ((t : ℝ) ^ (α - 1) + Real.log t / (t : ℝ) ^ α)
        ≤ K * ((T : ℝ) ^ α + (T : ℝ) ^ (1 - α) * Real.log T) := by
  refine ⟨1 / α + 1 / (1 - α), by have : 0 < 1 - α := by linarith
                                  positivity, ?_⟩
  intro T hT
  have hb : 0 < 1 - α := by linarith
  have hA := sum_rpow_le α h0 h1.le T hT
  have hB := sum_rpow_le (1 - α) hb (by linarith) T hT
  have hTpos : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hTpos
  have hsecond : ∑ t ∈ Finset.Icc 2 T, Real.log t / (t : ℝ) ^ α
      ≤ Real.log T * ∑ t ∈ Finset.Icc 2 T, (t : ℝ) ^ ((1 - α) - 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    simp only [Finset.mem_Icc] at ht
    have htpos : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
    have e : Real.log t / (t : ℝ) ^ α = Real.log t * (t : ℝ) ^ ((1 - α) - 1) := by
      rw [show (1 - α) - 1 = -α by ring, Real.rpow_neg htpos.le, div_eq_mul_inv]
    rw [e]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg htpos.le _)
    exact Real.log_le_log htpos (by exact_mod_cast ht.2)
  rw [Finset.sum_add_distrib]
  have hTa : 0 ≤ (T : ℝ) ^ α := Real.rpow_nonneg (by linarith) _
  have hTb : 0 ≤ (T : ℝ) ^ (1 - α) := Real.rpow_nonneg (by linarith) _
  have h3 : Real.log T * ∑ t ∈ Finset.Icc 2 T, (t : ℝ) ^ ((1 - α) - 1)
      ≤ Real.log T * ((T : ℝ) ^ (1 - α) / (1 - α)) := mul_le_mul_of_nonneg_left hB hlogT
  have e4 : (1 / α + 1 / (1 - α)) * ((T : ℝ) ^ α + (T : ℝ) ^ (1 - α) * Real.log T)
      = (T : ℝ) ^ α / α + Real.log T * ((T : ℝ) ^ (1 - α) / (1 - α))
        + ((T : ℝ) ^ (1 - α) * Real.log T) / α + (T : ℝ) ^ α / (1 - α) := by
    field_simp; ring
  have h5 : 0 ≤ ((T : ℝ) ^ (1 - α) * Real.log T) / α := by positivity
  have h6 : 0 ≤ (T : ℝ) ^ α / (1 - α) := by positivity
  rw [e4]; linarith

theorem assemble (M : Model) {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0) (p d : ℕ → Ω → ℝ)
    (hD : DemandModel M P ℱ p d) (α c p₁ : ℝ)
    (hp₁ : ∀ ω, p 1 ω = p₁)
    (hCVP : ∀ᵐ ω ∂P, IsCVPPath M α c (fun t => p t ω) (fun t => d t ω))
    (hrate : ∃ K : ℝ, 0 < K ∧ ∀ t : ℕ, 2 ≤ t →
      ∫ ω, (p t ω - pOpt M) ^ 2 ∂P
        ≤ K * ((t : ℝ) ^ (α - 1) + Real.log t / (t : ℝ) ^ α)) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T →
      regret M P p T ≤ K * ((T : ℝ) ^ α + (T : ℝ) ^ (1 - α) * Real.log T) := by
  obtain ⟨Kr, hKr0, hKr⟩ := hrate
  have : (ae P).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero P)
  obtain ⟨ω₀, hω₀⟩ := hCVP.exists
  have hαI : α ∈ Set.Ioo (0 : ℝ) 1 := hω₀.2.2.2.1
  obtain ⟨Ks, hKs0, hKs⟩ := rate_sum α hαI.1 hαI.2
  set po := pOpt M with hpo
  set K0 := sSup ((fun x => |deriv (deriv (revenue M.h M.a0)) x|) '' Set.Icc M.pl M.ph) with hK0
  have hK0n : 0 ≤ K0 := Real.sSup_nonneg (by rintro _ ⟨y, -, rfl⟩; exact abs_nonneg _)
  have hK0h : 0 ≤ K0 / 2 := by positivity
  refine ⟨K0 / 2 * ((p₁ - po) ^ 2 + Kr * Ks) + 1, by positivity, ?_⟩
  intro T hT
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTa : 1 ≤ (T : ℝ) ^ α := Real.one_le_rpow hT1 hαI.1.le
  have hTb : 0 ≤ (T : ℝ) ^ (1 - α) * Real.log T :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.log_nonneg hT1)
  set S := (T : ℝ) ^ α + (T : ℝ) ^ (1 - α) * Real.log T with hS
  have hS1 : 1 ≤ S := by linarith
  have hKpos : 0 < K0 / 2 * ((p₁ - po) ^ 2 + Kr * Ks) + 1 := by positivity
  unfold regret
  by_cases hI : Integrable (fun ω => ∑ t ∈ Finset.Icc 1 T,
      (revenue M.h M.a0 (pOpt M) - revenue M.h M.a0 (p t ω))) P
  swap
  · rw [integral_undef hI]; positivity
  -- the dominating function
  have hG : ∀ᵐ ω ∂P, ∀ t : ℕ, 1 ≤ t → p t ω ∈ Set.Icc M.pl M.ph :=
    hCVP.mono (fun ω h => prices_mem M α c _ _ h)
  set B := (|M.pl| + |M.ph| + |po|) ^ 2 with hB
  have hmeas : ∀ t : ℕ, 1 ≤ t → Measurable (p t) := fun t ht =>
    ((hD.price_meas t ht).mono (ℱ.le (t - 1))).measurable
  have hint : ∀ t ∈ Finset.Icc 1 T, Integrable (fun ω => K0 / 2 * (p t ω - po) ^ 2) P := by
    intro t ht
    simp only [Finset.mem_Icc] at ht
    have hm := hmeas t ht.1
    refine Integrable.of_bound (C := K0 / 2 * B)
      ((by fun_prop : Measurable fun ω => K0 / 2 * (p t ω - po) ^ 2).aestronglyMeasurable) ?_
    filter_upwards [hG] with ω hω
    have hpt := hω t ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ hK0h
    have hab : |p t ω - po| ≤ |M.pl| + |M.ph| + |po| := by
      have h1 : |p t ω| ≤ |M.pl| + |M.ph| := by
        rw [abs_le]; constructor
        · have := neg_abs_le M.pl; have := abs_nonneg M.ph; linarith [hpt.1]
        · have := le_abs_self M.ph; have := abs_nonneg M.pl; linarith [hpt.2]
      calc |p t ω - po| ≤ |p t ω| + |po| := abs_sub _ _
        _ ≤ _ := by linarith
    rw [hB, ← sq_abs (p t ω - po)]
    exact pow_le_pow_left₀ (abs_nonneg _) hab 2
  have hgI : Integrable (fun ω => ∑ t ∈ Finset.Icc 1 T, K0 / 2 * (p t ω - po) ^ 2) P :=
    integrable_finsetSum _ hint
  have hle : (fun ω => ∑ t ∈ Finset.Icc 1 T,
      (revenue M.h M.a0 (pOpt M) - revenue M.h M.a0 (p t ω)))
      ≤ᵐ[P] fun ω => ∑ t ∈ Finset.Icc 1 T, K0 / 2 * (p t ω - po) ^ 2 := by
    filter_upwards [hG] with ω hω
    apply Finset.sum_le_sum
    intro t ht
    simp only [Finset.mem_Icc] at ht
    have hq := revenue_quadratic_gap M (p t ω) (hω t ht.1)
    have := le_abs_self (revenue M.h M.a0 (pOpt M) - revenue M.h M.a0 (p t ω))
    rw [abs_sub_comm] at this
    linarith
  refine (integral_mono_ae hI hgI hle).trans ?_
  rw [integral_finsetSum _ hint]
  simp only [integral_const_mul]
  have hsplit : Finset.Icc 1 T = insert 1 (Finset.Icc 2 T) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : (1 : ℕ) ∉ Finset.Icc 2 T := by simp
  rw [hsplit, Finset.sum_insert hnot]
  have hI1 : ∫ ω, (p 1 ω - po) ^ 2 ∂P = (p₁ - po) ^ 2 := by simp [hp₁]
  rw [hI1]
  have hrest : ∑ t ∈ Finset.Icc 2 T, K0 / 2 * ∫ ω, (p t ω - po) ^ 2 ∂P
      ≤ K0 / 2 * (Kr * (Ks * S)) := by
    calc ∑ t ∈ Finset.Icc 2 T, K0 / 2 * ∫ ω, (p t ω - po) ^ 2 ∂P
        ≤ ∑ t ∈ Finset.Icc 2 T, K0 / 2 * (Kr * ((t : ℝ) ^ (α - 1) + Real.log t / (t : ℝ) ^ α)) := by
          apply Finset.sum_le_sum
          intro t ht
          simp only [Finset.mem_Icc] at ht
          exact mul_le_mul_of_nonneg_left (hKr t ht.1) hK0h
      _ = K0 / 2 * (Kr * ∑ t ∈ Finset.Icc 2 T, ((t : ℝ) ^ (α - 1) + Real.log t / (t : ℝ) ^ α)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ K0 / 2 * (Kr * (Ks * S)) := by
          apply mul_le_mul_of_nonneg_left _ hK0h
          exact mul_le_mul_of_nonneg_left (hKs T hT) hKr0.le
  have hfirst : K0 / 2 * (p₁ - po) ^ 2 ≤ K0 / 2 * (p₁ - po) ^ 2 * S := by
    have : 0 ≤ K0 / 2 * (p₁ - po) ^ 2 := by positivity
    nlinarith
  have hfin : K0 / 2 * (p₁ - po) ^ 2 * S + K0 / 2 * (Kr * (Ks * S))
      ≤ (K0 / 2 * ((p₁ - po) ^ 2 + Kr * Ks) + 1) * S := by
    have e : (K0 / 2 * ((p₁ - po) ^ 2 + Kr * Ks) + 1) * S
        = K0 / 2 * (p₁ - po) ^ 2 * S + K0 / 2 * (Kr * (Ks * S)) + S := by ring
    rw [e]; linarith
  linarith

end Red0f2d3266

open CVPricing.Regret in
/-- Reduction of `CVPricing.Regret.cvp_regret_bound` to the posted siblings
`CVPricing.Regret.price_sq_error_rate` and `CVPricing.Regret.revenue_quadratic_gap`. -/
theorem solution (M : Model) (hU : MQLEUnique M) {Ω : Type*} {m0 : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ m0) (p d : ℕ → Ω → ℝ)
    (hD : DemandModel M P ℱ p d) (α c p₁ p₂ : ℝ) (hα : 1 / 2 < α)
    (hp₁ : ∀ ω, p 1 ω = p₁) (hp₂ : ∀ ω, p 2 ω = p₂)
    (hCVP : ∀ᵐ ω ∂P, IsCVPPath M α c (fun t => p t ω) (fun t => d t ω)) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T →
      regret M P p T ≤ K * ((T : ℝ) ^ α + (T : ℝ) ^ (1 - α) * Real.log T) :=
  Red0f2d3266.assemble M P ℱ p d hD α c p₁ hp₁ hCVP
    (price_sq_error_rate M hU P ℱ p d hD α c p₁ p₂ hα hp₁ hp₂ hCVP)
