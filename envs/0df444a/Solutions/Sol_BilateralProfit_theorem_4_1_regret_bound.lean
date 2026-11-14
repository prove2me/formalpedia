-- Prove2me | solution 1 for BilateralProfit.theorem_4_1_regret_bound
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-13T16:50:43.864206+00:00
-- url     : https://prove2.me/submissions/c9619a75-355d-47a2-a2b0-5f122ac89dac

import Mathlib
import Definitions.Def_BilateralProfit_Algorithm1
import Theorems.Thm_BilateralProfit_theorem_4_2
import Theorems.Thm_BilateralProfit_telescoping_bound
import Theorems.Thm_BilateralProfit_grid_rounding
import Theorems.Thm_BilateralProfit_lemma_A_6
import Theorems.Thm_BilateralProfit_running_time


namespace BilateralProfit.MainSubmissionResolutionScalar

noncomputable def scale (t : ℝ) : ℝ := (t / Real.log t ^ 7) ^ ((1 : ℝ) / 3)

noncomputable def resolution (t : ℝ) : ℕ := max 2 ⌈scale t⌉₊

noncomputable def regretScale (t : ℝ) : ℝ :=
  t ^ ((2 : ℝ) / 3) * Real.log t ^ ((7 : ℝ) / 3)

lemma log_lower {t : ℝ} (ht : 2 ≤ t) : (1 / 2 : ℝ) ≤ Real.log t := by
  have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  exact h2.trans (Real.log_le_log (by norm_num) ht)

lemma scale_pos {t : ℝ} (ht : 2 ≤ t) : 0 < scale t := by
  have hlog : 0 < Real.log t := lt_of_lt_of_le (by norm_num) (log_lower ht)
  dsimp [scale]
  exact Real.rpow_pos_of_pos (div_pos (by linarith) (by positivity)) _

lemma scale_cube {t : ℝ} (ht : 2 ≤ t) : (scale t) ^ 3 = t / Real.log t ^ 7 := by
  have hlog : 0 < Real.log t := lt_of_lt_of_le (by norm_num) (log_lower ht)
  have hbase : 0 ≤ t / Real.log t ^ 7 := by positivity
  dsimp [scale]
  rw [← Real.rpow_mul_natCast hbase]
  norm_num

lemma log_seven_le {t : ℝ} (ht : 2 ≤ t) : Real.log t ^ 7 ≤ 1000000 * t := by
  have ht0 : 0 < t := by linarith
  have hl0 : 0 ≤ Real.log t := (log_lower ht).trans' (by norm_num)
  have hlog := Real.log_le_rpow_div ht0.le (by norm_num : (0 : ℝ) < 1 / 7)
  have hlog' : Real.log t ≤ 7 * t ^ ((1 : ℝ) / 7) := by convert hlog using 1 <;> ring
  have hpow := pow_le_pow_left₀ hl0 hlog' 7
  have hroot : (t ^ ((1 : ℝ) / 7)) ^ 7 = t := by
    rw [← Real.rpow_mul_natCast ht0.le]
    norm_num
  calc
    _ ≤ (7 * t ^ ((1 : ℝ) / 7)) ^ 7 := hpow
    _ = 7 ^ 7 * t := by rw [mul_pow, hroot]
    _ ≤ _ := by norm_num; linarith

lemma scale_lower {t : ℝ} (ht : 2 ≤ t) : (1 / 1000000 : ℝ) ≤ scale t := by
  have hz := scale_pos ht
  have hl := log_lower ht
  have hlog : 0 < Real.log t := by linarith
  have hpower : (1 / 1000000 : ℝ) ≤ (scale t) ^ 3 := by
    rw [scale_cube ht]
    apply (le_div_iff₀ (by positivity : 0 < Real.log t ^ 7)).mpr
    have h := log_seven_le ht
    linarith
  have hcube : (1 / 1000000 : ℝ) ^ 3 ≤ (scale t) ^ 3 :=
    (by norm_num : (1 / 1000000 : ℝ) ^ 3 ≤ 1 / 1000000).trans hpower
  nlinarith [sq_nonneg (scale t + 1 / 1000000),
    mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 1000000) hz.le]

lemma scale_le_resolution (t : ℝ) : scale t ≤ (resolution t : ℝ) := by
  exact (Nat.le_ceil (scale t)).trans (by exact_mod_cast (le_max_right 2 ⌈scale t⌉₊))

lemma resolution_le_add_two {t : ℝ} (ht : 2 ≤ t) : (resolution t : ℝ) ≤ scale t + 2 := by
  have hz := scale_pos ht
  have hc := (Nat.ceil_lt_add_one hz.le).le
  have hmax : (resolution t : ℝ) = max 2 (⌈scale t⌉₊ : ℝ) := by simp [resolution]
  rw [hmax]
  exact max_le (by linarith) (by linarith)

lemma resolution_le_scale {t : ℝ} (ht : 2 ≤ t) :
    (resolution t : ℝ) ≤ 2000001 * scale t := by
  have hz := scale_lower ht
  exact (resolution_le_add_two ht).trans (by linarith)

lemma two_le_resolution (t : ℝ) : 2 ≤ resolution t := le_max_left _ _

lemma scale_le_linear {t : ℝ} (ht : 2 ≤ t) : scale t ≤ 128 * t := by
  have ht0 : 0 < t := by linarith
  have hz := scale_pos ht
  have hlog := log_lower ht
  have hlogpos : 0 < Real.log t := by linarith
  have hlogpow : (1 / 128 : ℝ) ≤ Real.log t ^ 7 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hlog 7
    norm_num at h ⊢
    exact h
  have hcube : scale t ^ 3 ≤ 128 * t := by
    rw [scale_cube ht]
    apply (div_le_iff₀ (by positivity : 0 < Real.log t ^ 7)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlogpow (show 0 ≤ 128 * t by positivity)]
  have hone : 1 ≤ 128 * t := by linarith
  exact (pow_le_pow_iff_left₀ hz.le (by positivity : 0 ≤ 128 * t) (by decide : 3 ≠ 0)).mp
    (hcube.trans (le_self_pow₀ hone (by decide)))

lemma resolution_le_linear {t : ℝ} (ht : 2 ≤ t) : (resolution t : ℝ) ≤ 130 * t := by
  have h := resolution_le_add_two ht
  have hz := scale_le_linear ht
  linarith

lemma resolution_log_le {t : ℝ} (ht : 2 ≤ t) : Real.log (resolution t : ℝ) ≤ 261 * Real.log t := by
  have hr : (2 : ℝ) ≤ resolution t := by exact_mod_cast two_le_resolution t
  have ht0 : 0 < t := by linarith
  have h := Real.log_le_log (by linarith : (0 : ℝ) < resolution t) (resolution_le_linear ht)
  rw [Real.log_mul (by norm_num : (130 : ℝ) ≠ 0) ht0.ne'] at h
  have hc : Real.log 130 ≤ 130 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 130)
    linarith
  have hl := log_lower ht
  linarith

lemma scale_rpow_formula {t : ℝ} (ht : 2 ≤ t) :
    scale t = t ^ ((1 : ℝ) / 3) / Real.log t ^ ((7 : ℝ) / 3) := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := lt_of_lt_of_le (by norm_num) (log_lower ht)
  dsimp [scale]
  rw [Real.div_rpow ht0.le (by positivity : 0 ≤ Real.log t ^ 7),
    ← Real.rpow_natCast (Real.log t) 7, ← Real.rpow_mul hl.le]
  congr 2
  norm_num

lemma regretScale_mul_scale {t : ℝ} (ht : 2 ≤ t) : regretScale t * scale t = t := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := lt_of_lt_of_le (by norm_num) (log_lower ht)
  have hpow : Real.log t ^ ((7 : ℝ) / 3) ≠ 0 := (Real.rpow_pos_of_pos hl _).ne'
  rw [scale_rpow_formula ht]
  calc
    _ = t ^ ((2 : ℝ) / 3) * t ^ ((1 : ℝ) / 3) := by
      dsimp [regretScale]
      field_simp
    _ = t ^ ((2 : ℝ) / 3 + 1 / 3) := (Real.rpow_add ht0 _ _).symm
    _ = t := by norm_num

lemma horizon_div_resolution_le {t : ℝ} (ht : 2 ≤ t) : t / resolution t ≤ regretScale t := by
  have ht0 : 0 ≤ t := by linarith
  have hz := scale_pos ht
  calc
    _ ≤ t / scale t := div_le_div_of_nonneg_left ht0 hz (scale_le_resolution t)
    _ = _ := (eq_div_iff hz.ne').mpr (regretScale_mul_scale ht) |>.symm

lemma scale_sq_log_seven {t : ℝ} (ht : 2 ≤ t) :
    scale t ^ 2 * Real.log t ^ 7 = regretScale t := by
  have hz := scale_pos ht
  have hl : 0 < Real.log t := lt_of_lt_of_le (by norm_num) (log_lower ht)
  have hcube : scale t ^ 3 * Real.log t ^ 7 = t :=
    (eq_div_iff (by positivity : Real.log t ^ 7 ≠ 0)).mp (scale_cube ht)
  calc
    _ = (scale t ^ 3 * Real.log t ^ 7) / scale t := by field_simp
    _ = t / scale t := by rw [hcube]
    _ = _ := ((eq_div_iff hz.ne').mpr (regretScale_mul_scale ht)).symm

lemma resolution_sq_log_seven {t : ℝ} (ht : 2 ≤ t) :
    (resolution t : ℝ) ^ 2 * Real.log (resolution t : ℝ) ^ 7 ≤
      (2000001 : ℝ) ^ 2 * 261 ^ 7 * regretScale t := by
  have hz := scale_pos ht
  have hl : 0 ≤ Real.log t := (log_lower ht).trans' (by norm_num)
  have hr : (2 : ℝ) ≤ resolution t := by exact_mod_cast two_le_resolution t
  have hlr : 0 ≤ Real.log (resolution t : ℝ) := Real.log_nonneg (by linarith)
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ resolution t) (resolution_le_scale ht) 2
  have hp := pow_le_pow_left₀ hlr (resolution_log_le ht) 7
  calc
    _ ≤ (2000001 * scale t) ^ 2 * (261 * Real.log t) ^ 7 :=
      mul_le_mul hsq hp (by positivity) (by positivity)
    _ = (2000001 : ℝ) ^ 2 * 261 ^ 7 * (scale t ^ 2 * Real.log t ^ 7) := by ring
    _ = _ := by rw [scale_sq_log_seven ht]

end BilateralProfit.MainSubmissionResolutionScalar


set_option maxHeartbeats 1500000

namespace BilateralProfit.MainSubmissionRegret

theorem expect_sum (K T : ℕ) (f : (Fin T → Fin (Jpar K)) → Fin T → ℝ) :
    expectAlg K T (fun ω => ∑ t, f ω t) =
      ∑ t, expectAlg K T (fun ω => f ω t) := by
  unfold expectAlg
  rw [Finset.sum_comm, Finset.sum_div]

theorem grid_profit_nonneg (K : ℕ) (v : ℝ × ℝ) (a : Act K) :
    0 ≤ profit v (pt K a.1) := by
  have hi : (a.1.1 : ℝ) ≤ a.1.2 := by exact_mod_cast a.2
  apply mul_nonneg
  · exact sub_nonneg.mpr (div_le_div_of_nonneg_right hi (Nat.cast_nonneg K))
  · unfold tradeBit
    split_ifs <;> norm_num

theorem expProfit_nonneg (K T : ℕ) (S : Fin T → ℝ × ℝ) (t : Fin T) :
    0 ≤ expProfit K T S t := by
  unfold expProfit expectAlg
  exact div_nonneg (Finset.sum_nonneg fun ω _ => grid_profit_nonneg K (S t) _)
    (Nat.cast_nonneg _)

theorem regret_nonpos_of_reversed (K T : ℕ) (S : Fin T → ℝ × ℝ)
    (p q : ℝ) (hpq : q ≤ p) :
    ∑ t, (profit (S t) (p, q) - expProfit K T S t) ≤ 0 := by
  apply Finset.sum_nonpos
  intro t _
  have hp : profit (S t) (p, q) ≤ 0 := by
    unfold profit tradeBit
    split_ifs <;> simp only [mul_one, mul_zero] <;> linarith
  exact sub_nonpos.mpr (hp.trans (expProfit_nonneg K T S t))

theorem grid_regret (K : ℕ) (hK : 0 < K) (C₀ : ℝ)
    (hC₀ : ∀ ρ : Grid K × Act K → ℝ, IsDist ρ →
      ∃ a : Act K, gap ρ a - beta K * info ρ a ≤ C₀ / K)
    (T : ℕ) (S : Fin T → ℝ × ℝ)
    (hS : ∀ t, S t ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    (a : Act K) :
    ∑ t, (profit (S t) (pt K a.1) - expProfit K T S t) ≤
      (C₀ + 2) * T / K + beta K * Real.log (nA K) := by
  classical
  obtain ⟨hr, hprog⟩ := grid_rounding K hK
  have hex (t : Fin T) : ∃ x : Grid K, pt K x =
      ((⌈(K : ℝ) * (S t).1⌉₊ : ℝ) / K, (⌊(K : ℝ) * (S t).2⌋₊ : ℝ) / K) :=
    (hr (S t).1 (S t).2 (hS t).1 (hS t).2).1
  choose v hv using hex
  have hRun (ω : Fin T → Fin (Jpar K)) : runW (alg1 K T S ω) =
      runW (alg1 K T (fun t => pt K (v t)) ω) := by
    simpa only [← hv] using hprog T S hS ω
  have hact (ω : Fin T → Fin (Jpar K)) (t : Fin T) :
      alg1Act K T S ω t = alg1Act K T (fun s => pt K (v s)) ω t := by
    unfold alg1Act
    rw [hRun]
  have hp (t : Fin T) (b : Act K) :
      profit (S t) (pt K b.1) = profit (pt K (v t)) (pt K b.1) := by
    simpa only [← hv t] using (hr (S t).1 (S t).2 (hS t).1 (hS t).2).2 b |>.2
  have heq : (∑ t, (profit (S t) (pt K a.1) - expProfit K T S t)) =
      (∑ t, profit (pt K (v t)) (pt K a.1)) -
        expectAlg K T (fun ω => ∑ t, profit (pt K (v t))
          (pt K (alg1Act K T (fun s => pt K (v s)) ω t).1)) := by
    rw [Finset.sum_sub_distrib, expect_sum]
    apply congrArg₂ (fun x y : ℝ => x - y)
    · exact Finset.sum_congr rfl (fun t _ => hp t a)
    · apply Finset.sum_congr rfl
      intro t _
      unfold expProfit
      apply congrArg (expectAlg K T)
      funext ω
      rw [hp, hact]
  rw [heq]
  exact ((telescoping_bound K hK C₀ hC₀ T v).2 a).1.trans
    ((telescoping_bound K hK C₀ hC₀ T v).2 a).2

theorem regret_at_resolution (K : ℕ) (hK : 0 < K) (C₀ : ℝ)
    (hC₀ : ∀ ρ : Grid K × Act K → ℝ, IsDist ρ →
      ∃ a : Act K, gap ρ a - beta K * info ρ a ≤ C₀ / K)
    (T : ℕ) (S : Fin T → ℝ × ℝ)
    (hS : ∀ t, S t ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ 1) :
    ∑ t, (profit (S t) (p, q) - expProfit K T S t) ≤
      (C₀ + 4) * T / K + beta K * Real.log (nA K) := by
  obtain ⟨a, _, ha⟩ := lemma_A_6 K hK p q hp hpq hq
  have h := (ha T S (expProfit K T S)).trans
    (add_le_add (grid_regret K hK C₀ hC₀ T S hS a) (le_refl ((2 : ℝ) * T / K)))
  calc
    _ ≤ ((C₀ + 2) * T / K + beta K * Real.log (nA K)) + 2 * T / K := h
    _ = _ := by ring

theorem log_card_le (K : ℕ) (hK : 2 ≤ K) : Real.log (nA K) ≤ 4 * Real.log K := by
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hpos : 0 < nA K := by
    unfold nA
    exact_mod_cast Fintype.card_pos (α := Act K)
  have hcard : Fintype.card (Act K) ≤ (K + 1) ^ 2 := by
    simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using
      Fintype.card_subtype_le (fun x : Grid K => x.1 ≤ x.2)
  have hc : nA K ≤ ((K : ℝ) + 1) ^ 2 := by
    unfold nA
    exact_mod_cast hcard
  have hc' : nA K ≤ (2 * (K : ℝ)) ^ 2 :=
    hc.trans (pow_le_pow_left₀ (by positivity) (by linarith) 2)
  have hl := Real.log_le_log hpos hc'
  rw [Real.log_pow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (by linarith : (K : ℝ) ≠ 0)] at hl
  have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hKr
  norm_num at hl
  linarith

theorem beta_log_bound (K : ℕ) (hK : 2 ≤ K) :
    beta K * Real.log (nA K) ≤ 4 * (K : ℝ) ^ 2 * Real.log K ^ 7 := by
  have hb : 0 ≤ beta K := by unfold beta; positivity
  have h := mul_le_mul_of_nonneg_left (log_card_le K hK) hb
  calc
    _ ≤ beta K * (4 * Real.log K) := h
    _ = _ := by unfold beta; ring

theorem regret_bound : ∃ A : ℝ, 0 < A ∧
    ∀ T : ℕ, 2 ≤ T → ∀ S : Fin T → ℝ × ℝ,
      (∀ t, S t ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) →
      ∀ p q : ℝ, p ∈ Set.Icc (0 : ℝ) 1 → q ∈ Set.Icc (0 : ℝ) 1 →
        ∑ t, (profit (S t) (p, q) - expProfit (Kpin T) T S t) ≤
          A * MainSubmissionResolutionScalar.regretScale T := by
  obtain ⟨C₀, hC₀⟩ := theorem_4_2
  let D : ℝ := (2000001 : ℝ) ^ 2 * 261 ^ 7
  let A : ℝ := |C₀| + 4 + 4 * D
  have hD : 0 < D := by dsimp [D]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro T hT S hS p q hp hq
  have hTr : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hK2 : 2 ≤ Kpin T := le_max_left _ _
  have hK : 0 < Kpin T := by omega
  have hscale : 0 ≤ MainSubmissionResolutionScalar.regretScale T := by
    dsimp [MainSubmissionResolutionScalar.regretScale]
    positivity
  by_cases hpq : p ≤ q
  · have h := regret_at_resolution (Kpin T) hK C₀ (hC₀ _ hK) T S hS
      p q hp.1 hpq hq.2
    have ht : (T : ℝ) / Kpin T ≤ MainSubmissionResolutionScalar.regretScale T :=
      MainSubmissionResolutionScalar.horizon_div_resolution_le hTr
    have hk : (Kpin T : ℝ) ^ 2 * Real.log (Kpin T) ^ 7 ≤
        D * MainSubmissionResolutionScalar.regretScale T := MainSubmissionResolutionScalar.resolution_sq_log_seven hTr
    have hcoef : 0 ≤ |C₀| + 4 := by positivity
    have hnonneg : 0 ≤ (T : ℝ) / Kpin T := by positivity
    calc
      _ ≤ (C₀ + 4) * T / Kpin T + beta (Kpin T) * Real.log (nA (Kpin T)) := h
      _ ≤ (|C₀| + 4) * ((T : ℝ) / Kpin T) +
          4 * ((Kpin T : ℝ) ^ 2 * Real.log (Kpin T) ^ 7) := by
        apply add_le_add
        · simpa only [mul_div_assoc, add_comm] using
            mul_le_mul_of_nonneg_right (add_le_add_right (le_abs_self C₀) 4) hnonneg
        · simpa only [mul_assoc] using beta_log_bound (Kpin T) hK2
      _ ≤ (|C₀| + 4) * MainSubmissionResolutionScalar.regretScale T +
          4 * (D * MainSubmissionResolutionScalar.regretScale T) :=
        add_le_add (mul_le_mul_of_nonneg_left ht hcoef)
          (mul_le_mul_of_nonneg_left hk (by norm_num))
      _ = _ := by dsimp [A]; ring
  · exact (regret_nonpos_of_reversed (Kpin T) T S p q (le_of_not_ge hpq)).trans
      (mul_nonneg hA.le hscale)

end BilateralProfit.MainSubmissionRegret


namespace BilateralProfit.MainSubmissionRuntime

theorem polynomial_cost :
    ∃ D d : ℝ, 0 < D ∧ ∀ T : ℕ, 2 ≤ T →
      ∀ S : Fin T → ℝ × ℝ,
        (∀ t, S t ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) →
        ∀ ω : Fin T → Fin (Jpar (Kpin T)),
          (alg1Cost (Kpin T) T S ω : ℝ) ≤ D * (T : ℝ)^d := by
  obtain ⟨C, c, hcost⟩ := running_time
  let e : ℝ := 12 + max c 0
  refine ⟨max C 1 * (130 : ℝ)^e, e + 1, ?_, ?_⟩
  · have hC : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
    exact mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _)
  · intro T hT S hS ω
    have ht : (2 : ℝ) ≤ T := by exact_mod_cast hT
    have ht0 : (0 : ℝ) < T := by linarith
    have hK : 1 ≤ Kpin T := by
      have := MainSubmissionResolutionScalar.two_le_resolution (T : ℝ)
      change 2 ≤ Kpin T at this
      omega
    have hk : (1 : ℝ) ≤ Kpin T := by exact_mod_cast hK
    have hk0 : (0 : ℝ) < Kpin T := by linarith
    have hL : 1 ≤ 1 + Real.log (Kpin T) := by
      linarith [Real.log_natCast_nonneg (Kpin T)]
    have hLK : 1 + Real.log (Kpin T) ≤ Kpin T := by
      linarith [Real.log_le_sub_one_of_pos hk0]
    have he : 0 ≤ e := by dsimp [e]; have := le_max_right c 0; linarith
    have hC : 0 ≤ max C 1 := le_trans zero_le_one (le_max_right C 1)
    have hscale :
        (Kpin T : ℝ)^12 * (1 + Real.log (Kpin T))^c ≤ (Kpin T : ℝ)^e := by
      calc
        _ ≤ (Kpin T : ℝ)^12 * (1 + Real.log (Kpin T))^(max c 0) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hL (le_max_left c 0)) (by positivity)
        _ ≤ (Kpin T : ℝ)^12 * (Kpin T : ℝ)^(max c 0) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (by linarith : 0 ≤ 1 + Real.log (Kpin T)) hLK
              (le_max_right c 0)) (by positivity)
        _ = _ := by
          dsimp [e]
          rw [Real.rpow_add hk0]
          norm_num
    have hKlinear : (Kpin T : ℝ) ≤ 130 * T :=
      MainSubmissionResolutionScalar.resolution_le_linear ht
    have hbound := hcost T (Kpin T) (by omega) hK S hS ω
    calc
      (alg1Cost (Kpin T) T S ω : ℝ) ≤
          C * T * (Kpin T : ℝ)^12 * (1 + Real.log (Kpin T))^c := hbound
      _ ≤ max C 1 * T * ((Kpin T : ℝ)^12 * (1 + Real.log (Kpin T))^c) := by
        have hmul := mul_le_mul_of_nonneg_right (le_max_left C 1)
          (show 0 ≤ (T : ℝ) * (Kpin T : ℝ)^12 * (1 + Real.log (Kpin T))^c by positivity)
        calc
          C * T * (Kpin T : ℝ)^12 * (1 + Real.log (Kpin T))^c =
              C * ((T : ℝ) * (Kpin T : ℝ)^12 * (1 + Real.log (Kpin T))^c) := by ring
          _ ≤ _ := hmul
          _ = _ := by ring
      _ ≤ max C 1 * T * (Kpin T : ℝ)^e :=
        mul_le_mul_of_nonneg_left hscale (by positivity)
      _ ≤ max C 1 * T * (130 * (T : ℝ))^e :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hk0.le hKlinear he) (by positivity)
      _ = max C 1 * (130 : ℝ)^e * (T : ℝ)^(e+1) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 130) ht0.le,
          Real.rpow_add_one ht0.ne']
        ring

end BilateralProfit.MainSubmissionRuntime



namespace BilateralProfit

theorem cert_theorem_4_1_regret_bound_submission :
    ∃ C c : ℝ, 0 < C ∧ ∀ T : ℕ, 2 ≤ T →
      (∀ S : Fin T → ℝ × ℝ, (∀ t, S t ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) →
        ∀ p q : ℝ, p ∈ Set.Icc (0 : ℝ) 1 → q ∈ Set.Icc (0 : ℝ) 1 →
          ∑ t, (profit (S t) (p, q) - expProfit (Kpin T) T S t) ≤
            C * (T : ℝ) ^ ((2 : ℝ) / 3) * Real.log T ^ ((7 : ℝ) / 3)) ∧
      (∀ S : Fin T → ℝ × ℝ, (∀ t, S t ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) →
        ∀ ω : Fin T → Fin (Jpar (Kpin T)),
          (alg1Cost (Kpin T) T S ω : ℝ) ≤ C * (T : ℝ) ^ c) := by
  obtain ⟨A, hA, hreg⟩ := MainSubmissionRegret.regret_bound
  obtain ⟨D, d, hD, hcost⟩ := MainSubmissionRuntime.polynomial_cost
  refine ⟨A + D, d, add_pos hA hD, ?_⟩
  intro T hT
  constructor
  · intro S hS p q hp hq
    have hs : 0 ≤ MainSubmissionResolutionScalar.regretScale T := by
      dsimp [MainSubmissionResolutionScalar.regretScale]
      positivity
    calc
      _ ≤ A * MainSubmissionResolutionScalar.regretScale T := hreg T hT S hS p q hp hq
      _ ≤ (A + D) * MainSubmissionResolutionScalar.regretScale T :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD.le) hs
      _ = _ := by dsimp [MainSubmissionResolutionScalar.regretScale]; ring
  · intro S hS ω
    exact (hcost T hT S hS ω).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA.le)
        (Real.rpow_nonneg (Nat.cast_nonneg T) d))

end BilateralProfit

open BilateralProfit

theorem solution :
    ∃ C c : ℝ, 0 < C ∧ ∀ T : ℕ, 2 ≤ T →
      (∀ S : Fin T → ℝ × ℝ, (∀ t, S t ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) →
        ∀ p q : ℝ, p ∈ Set.Icc (0 : ℝ) 1 → q ∈ Set.Icc (0 : ℝ) 1 →
          ∑ t, (profit (S t) (p, q) - expProfit (Kpin T) T S t) ≤
            C * (T : ℝ) ^ ((2 : ℝ) / 3) * Real.log T ^ ((7 : ℝ) / 3)) ∧
      (∀ S : Fin T → ℝ × ℝ, (∀ t, S t ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) →
        ∀ ω : Fin T → Fin (Jpar (Kpin T)),
          (alg1Cost (Kpin T) T S ω : ℝ) ≤ C * (T : ℝ) ^ c) := by exact BilateralProfit.cert_theorem_4_1_regret_bound_submission

