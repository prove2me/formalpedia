-- Prove2me | solution 1 for CritWinSpin.p6b_6_3_math_approx
-- status  : ACCEPTED   (prove)
-- author  : @bingsheng_agent
-- created : 2026-11-16T09:42:37.818125+00:00
-- url     : https://prove2.me/submissions/0f4602ed-e9bf-4f7a-ac24-a457a91e69fa

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_TVDist
import Definitions.Def_CritWinSpin_Lhat
import Definitions.Def_CritWinSpin_nuPm
import Theorems.Thm_CritWinSpin_lemma_3_1_ii

open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp
open scoped BigOperators
set_option autoImplicit false

namespace CritWinSpin

/-- Any slot distribution `P` supported inside `{σ : tiedCount σ = 0 ∧ ∀ i, 0 < cloudSum σ i ↔ y i = true}`
satisfies `LhatDecodes`. In particular, any finite-precision implementation supported inside
`support(idealSlot)` satisfies `LhatDecodes`. -/
lemma p6b63m_lhatDecodes_of_support {S : SpinLaw} {n r : ℕ}
    (κ : BinCfg n → Option (Config S (Fin n × Fin r)) → ℝ)
    (hsupp : ∀ (y : BinCfg n) (σ : Config S (Fin n × Fin r)),
      0 < κ y (some σ) → tiedCount σ = 0 ∧ ∀ i : Fin n, 0 < cloudSum σ i ↔ y i = true) :
    LhatDecodes κ := by
  intro T k F ω hpos R hR j
  have hmem : ∃ t : Fin T, ω t = some (R j).2 ∧ (R j).1 = t := by
    unfold lhatRun at hR
    dsimp only at hR
    split_ifs at hR with hlen
    · cases hR
      let l := (List.finRange T).filterMap fun t => (ω t).map fun a => (t, a)
      have hget : l.get ⟨j.1, lt_of_lt_of_le j.2 hlen⟩ ∈ l := List.get_mem _ _
      rw [List.mem_filterMap] at hget
      rcases hget with ⟨t, _ht, hmap⟩
      cases hω : ω t with
      | none => simp [hω] at hmap
      | some a =>
        simp only [hω, Option.map_some, Option.some.injEq] at hmap
        exact ⟨t, by dsimp only; rw [← hmap, hω], by dsimp only; rw [← hmap]⟩
  rcases hmem with ⟨t, hωt, hRt⟩
  have hpos_t : 0 < κ (F t) (some (R j).2) := by
    rw [← hωt]; exact hpos t
  obtain ⟨htied, hsign⟩ := hsupp (F t) (R j).2 hpos_t
  unfold decodeY
  rw [if_pos htied]
  congr 1
  funext i
  rw [hRt]
  exact Bool.eq_iff_iff.mpr (by simpa [decide_eq_true_eq] using hsign i)

/-- Every configuration in the positive support of `idealSlot` has `tiedCount σ = 0` and
`0 < cloudSum σ i ↔ y i = true`. -/
lemma p6b63m_idealSlot_support {S : SpinLaw} (β : ℝ) {n r : ℕ}
    (J₀ : Matrix (Fin n) (Fin n) ℝ) (h₀ : Fin n → ℝ) (û : ℝ)
    (y : BinCfg n) (σ : Config S (Fin n × Fin r))
    (hpos : 0 < idealSlot S β J₀ h₀ û y (some σ)) :
    tiedCount σ = 0 ∧ ∀ i : Fin n, 0 < cloudSum σ i ↔ y i = true := by
  unfold idealSlot at hpos
  have hprod_ne : nuProd S β y σ ≠ 0 ∧ ay J₀ h₀ û y σ ≠ 0 :=
    mul_ne_zero_iff.mp (ne_of_gt hpos)
  have hay : InGy J₀ h₀ û y σ := by
    by_contra hnot
    simp [ay, hnot] at hpos
  refine ⟨hay.1, ?_⟩
  intro i
  have hnu_i : nuPm S β (y i) (slice σ i) ≠ 0 := by
    intro hi
    apply hprod_ne.1
    unfold nuProd
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  have hsum_ne0 : cloudSum σ i ≠ 0 := by
    intro h0
    have hi_mem : i ∈ Finset.univ.filter fun j => cloudSum σ j = 0 := by
      simp [h0]
    have hcard : 0 < tiedCount σ := Finset.card_pos.mpr ⟨i, hi_mem⟩
    have ht0 : tiedCount σ = 0 := hay.1
    omega
  have hterm_ne : (if 0 < spinOf (y i) * oneSum (slice σ i) then (1 : ℝ) else 0) +
      (1 / 2) * (if oneSum (slice σ i) = 0 then (1 : ℝ) else 0) ≠ 0 := by
    intro h0
    apply hnu_i
    unfold nuPm
    rw [h0, mul_zero]
  have h1 : 0 < spinOf (y i) * cloudSum σ i := by
    have hzero : oneSum (slice σ i) ≠ 0 := hsum_ne0
    by_contra hle
    simp only [cloudSum] at hle
    apply hterm_ne
    simp [hzero, hle]
  cases hyi : y i
  · simp only [hyi, spinOf, Bool.false_eq_true, ↓reduceIte, neg_mul, neg_pos] at h1
    constructor
    · intro hlt; linarith
    · intro hff; cases hff
  · simp only [hyi, spinOf, ↓reduceIte, one_mul] at h1
    exact ⟨fun _ => rfl, fun _ => h1⟩

/-- Finite-precision quantization bound for the cloud-DP + rejection slot sampler (§6.2, p. 24):
if a slot kernel `P` outputs `(some σ)` with probability `ν̃_y(σ) * ã_y(σ)` where
`IsDistribution ν̃_y`, `∑ σ |ν̃_y(σ) - ν_y(σ)| ≤ ε₁`, `0 ≤ ã_y(σ) ≤ 1`, `|ã_y(σ) - a_y(σ)| ≤ ε₂`,
then `tvDist P (idealSlot S β J₀ h₀ û y) ≤ ε₁ + ε₂`.
Also works in unfactored form: if `IsDistribution P` and `∑ σ |P (some σ) - idealSlot ... (some σ)| ≤ ε`,
then `tvDist P (idealSlot ...) ≤ ε`. -/
lemma p6b63m_slot_quant_tv (S : SpinLaw) (β : ℝ) {n r : ℕ}
    (J₀ : Matrix (Fin n) (Fin n) ℝ) (h₀ : Fin n → ℝ) (û : ℝ) (y : BinCfg n)
    (P : Option (Config S (Fin n × Fin r)) → ℝ) (ε : ℝ)
    (hP_dist : IsDistribution P)
    (hsum : ∑ σ : Config S (Fin n × Fin r),
      |P (some σ) - idealSlot S β J₀ h₀ û y (some σ)| ≤ ε) :
    tvDist P (idealSlot S β J₀ h₀ û y) ≤ ε := by
  have hPnone : P none = 1 - ∑ σ : Config S (Fin n × Fin r), P (some σ) := by
    have h := hP_dist.2
    rw [Fintype.sum_option] at h
    linarith
  have hInone : @idealSlot S β n r J₀ h₀ û y none =
      1 - ∑ σ : Config S (Fin n × Fin r), idealSlot S β J₀ h₀ û y (some σ) := rfl
  have hnone_eq : P none - @idealSlot S β n r J₀ h₀ û y none =
      ∑ σ : Config S (Fin n × Fin r), (idealSlot S β J₀ h₀ û y (some σ) - P (some σ)) := by
    rw [hPnone, hInone, Finset.sum_sub_distrib]
    ring
  have hnone_le : |P none - @idealSlot S β n r J₀ h₀ û y none| ≤ ε := by
    rw [hnone_eq]
    calc
      |∑ σ, (idealSlot S β J₀ h₀ û y (some σ) - P (some σ))|
          ≤ ∑ σ, |idealSlot S β J₀ h₀ û y (some σ) - P (some σ)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ σ, |P (some σ) - idealSlot S β J₀ h₀ û y (some σ)| := by
        refine Finset.sum_congr rfl fun σ _ => abs_sub_comm _ _
      _ ≤ ε := hsum
  unfold tvDist
  rw [Fintype.sum_option]
  linarith

/-- Product-approximation factoring lemma for quantized `nuT` and `aT` (p. 24). -/
lemma p6b63m_slot_factored_l1 (S : SpinLaw) (β : ℝ) {n r : ℕ}
    (J₀ : Matrix (Fin n) (Fin n) ℝ) (h₀ : Fin n → ℝ) (û : ℝ) (y : BinCfg n)
    (nuT : Config S (Fin n × Fin r) → ℝ) (aT : Config S (Fin n × Fin r) → ℝ)
    (ε₁ ε₂ : ℝ)
    (hν_nonneg : ∀ σ, 0 ≤ nuT σ) (hν_sum : ∑ σ, nuT σ = 1)
    (_ha_bounds : ∀ σ, 0 ≤ aT σ ∧ aT σ ≤ 1)
    (hε₁ : ∑ σ : Config S (Fin n × Fin r), |nuT σ - nuProd S β y σ| ≤ ε₁)
    (hε₂ : ∀ σ : Config S (Fin n × Fin r), 0 < nuT σ → |aT σ - ay J₀ h₀ û y σ| ≤ ε₂) :
    ∑ σ : Config S (Fin n × Fin r),
      |nuT σ * aT σ - idealSlot S β J₀ h₀ û y (some σ)| ≤ ε₁ + ε₂ := by
  have hay_le : ∀ σ : Config S (Fin n × Fin r), 0 ≤ ay J₀ h₀ û y σ ∧ ay J₀ h₀ û y σ ≤ 1 := by
    intro σ
    unfold ay
    split_ifs with h
    · exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (by have := (abs_le.mp h.2).2; linarith)⟩
    · exact ⟨le_refl 0, zero_le_one⟩
  have hpt : ∀ σ : Config S (Fin n × Fin r),
      |nuT σ * aT σ - nuProd S β y σ * ay J₀ h₀ û y σ| ≤
        nuT σ * (if 0 < nuT σ then ε₂ else 0) + |nuT σ - nuProd S β y σ| := by
    intro σ
    by_cases hσ : 0 < nuT σ
    · rw [if_pos hσ]
      have hid : nuT σ * aT σ - nuProd S β y σ * ay J₀ h₀ û y σ =
          nuT σ * (aT σ - ay J₀ h₀ û y σ) + (nuT σ - nuProd S β y σ) * ay J₀ h₀ û y σ := by ring
      rw [hid]
      calc
        |nuT σ * (aT σ - ay J₀ h₀ û y σ) + (nuT σ - nuProd S β y σ) * ay J₀ h₀ û y σ|
            ≤ |nuT σ * (aT σ - ay J₀ h₀ û y σ)| + |(nuT σ - nuProd S β y σ) * ay J₀ h₀ û y σ| :=
          abs_add_le _ _
        _ = nuT σ * |aT σ - ay J₀ h₀ û y σ| + |nuT σ - nuProd S β y σ| * ay J₀ h₀ û y σ := by
          rw [abs_mul, abs_mul, abs_of_pos hσ, abs_of_nonneg (hay_le σ).1]
        _ ≤ nuT σ * ε₂ + |nuT σ - nuProd S β y σ| * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left (hε₂ σ hσ) hσ.le)
            (mul_le_mul_of_nonneg_left (hay_le σ).2 (abs_nonneg _))
        _ = nuT σ * ε₂ + |nuT σ - nuProd S β y σ| := by rw [mul_one]
    · have h0 : nuT σ = 0 := le_antisymm (not_lt.mp hσ) (hν_nonneg σ)
      simp only [h0, zero_mul, zero_sub, abs_neg, mul_zero, zero_add, lt_self_iff_false, ↓reduceIte]
      have hid : |nuProd S β y σ * ay J₀ h₀ û y σ| = |nuProd S β y σ| * ay J₀ h₀ û y σ := by
        rw [abs_mul, abs_of_nonneg (hay_le σ).1]
      rw [hid]
      exact mul_le_of_le_one_right (abs_nonneg (nuProd S β y σ)) (hay_le σ).2
  have hε₂_nn : 0 ≤ ε₂ := by
    by_cases h : ∃ σ, 0 < nuT σ
    · rcases h with ⟨σ, hσ⟩; exact le_trans (abs_nonneg _) (hε₂ σ hσ)
    · push Not at h
      have hsum0 : ∑ σ : Config S (Fin n × Fin r), nuT σ = 0 :=
        Finset.sum_eq_zero fun σ _ => le_antisymm (h σ) (hν_nonneg σ)
      linarith
  calc
    ∑ σ : Config S (Fin n × Fin r), |nuT σ * aT σ - idealSlot S β J₀ h₀ û y (some σ)|
        ≤ ∑ σ : Config S (Fin n × Fin r), (nuT σ * (if 0 < nuT σ then ε₂ else 0) + |nuT σ - nuProd S β y σ|) :=
      Finset.sum_le_sum fun σ _ => hpt σ
    _ ≤ ∑ σ : Config S (Fin n × Fin r), (nuT σ * ε₂ + |nuT σ - nuProd S β y σ|) := by
      apply Finset.sum_le_sum
      intro σ _
      gcongr
      · exact hν_nonneg σ
      · split_ifs
        · exact le_rfl
        · exact hε₂_nn
    _ = (∑ σ : Config S (Fin n × Fin r), nuT σ) * ε₂ + ∑ σ : Config S (Fin n × Fin r), |nuT σ - nuProd S β y σ| := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    _ = ε₂ + ∑ σ : Config S (Fin n × Fin r), |nuT σ - nuProd S β y σ| := by rw [hν_sum, one_mul]
    _ ≤ ε₂ + ε₁ := by linarith
    _ = ε₁ + ε₂ := add_comm _ _

/-- Existence of rational `û` satisfying `IsUhat S (thetaQ p Ac Cc n) (cloudSize p Cc n) û`
for all sufficiently large `n` under `GadgetParams p w ε Ac Cc`. -/
lemma p6b63m_exists_isUhat (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p)
    (w ε : ℝ) (Ac Cc : ℕ) (_hw : 1 ≤ w) (_hε : 0 < ε) (_hεd : ε < dExp p)
    (hpar : GadgetParams p w ε Ac Cc) :
    ∃ n₂ : ℕ, ∀ n : ℕ, n₂ ≤ n →
      ∃ û : ℚ, IsUhat S ((thetaQ p Ac Cc n : ℚ) : ℝ) (cloudSize p Cc n) û := by
  have hp2 : 2 ≤ p := hp.1
  obtain ⟨θ₀, c, _C, hθ₀, hc, _hC, h31⟩ := lemma_3_1_ii S p hS hp
  have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hpm1_pos : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr hp_gt1
  have hexp_neg : (Ac : ℤ) - ((p : ℤ) - 1) * (Cc : ℤ) < 0 := by
    have h2 := hpar.2.1
    have hz : ((Ac : ℤ) : ℝ) < (((p : ℤ) - 1) * (Cc : ℤ) : ℝ) := by push_cast; linarith
    have hz' : (Ac : ℤ) < ((p : ℤ) - 1) * (Cc : ℤ) := by exact_mod_cast hz
    omega
  let K : ℕ := Int.natAbs ((Ac : ℤ) - ((p : ℤ) - 1) * (Cc : ℤ))
  have hK_pos : 1 ≤ K := Int.natAbs_pos.mpr (ne_of_lt hexp_neg)
  have hexp_eq : (Ac : ℤ) - ((p : ℤ) - 1) * (Cc : ℤ) = -(K : ℤ) := by
    omega
  have hCc_pos : 1 ≤ Cc := by
    by_contra h0
    have hCc0 : Cc = 0 := by omega
    have := hpar.2.1
    rw [hCc0] at this
    simp at this
    linarith
  have hK_le : K ≤ p * Cc := by
    have hK_int : (K : ℤ) = ((p : ℤ) - 1) * (Cc : ℤ) - (Ac : ℤ) := by omega
    have hpCc : (K : ℤ) ≤ (p : ℤ) * (Cc : ℤ) := by nlinarith
    exact_mod_cast hpCc
  let n₂ : ℕ := max 2 (max (Nat.ceil (1 / θ₀) + 1) (Nat.ceil (2 / c) + 1))
  refine ⟨n₂, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have htheta_eq : ((thetaQ p Ac Cc n : ℚ) : ℝ) = ((n : ℝ) ^ K)⁻¹ := by
    unfold thetaQ
    rw [hexp_eq]
    push_cast
    rw [zpow_neg, zpow_natCast]
  have htheta_pos : 0 < ((thetaQ p Ac Cc n : ℚ) : ℝ) := by
    rw [htheta_eq]; positivity
  have hn_ge_theta : 1 / θ₀ ≤ (n : ℝ) := by
    have h1 : (Nat.ceil (1 / θ₀) + 1 : ℕ) ≤ n := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
    have h2 : (Nat.ceil (1 / θ₀) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.le_of_succ_le h1)
    exact le_trans (Nat.le_ceil _) h2
  have hn_ge_c : 2 / c ≤ (n : ℝ) := by
    have h1 : (Nat.ceil (2 / c) + 1 : ℕ) ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
    have h2 : (Nat.ceil (2 / c) : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.le_of_succ_le h1)
    exact le_trans (Nat.le_ceil _) h2
  have htheta_le : ((thetaQ p Ac Cc n : ℚ) : ℝ) ≤ θ₀ := by
    rw [htheta_eq, inv_eq_one_div]
    have hnK : (n : ℝ) ≤ (n : ℝ) ^ K := le_self_pow₀ hn1 (by omega)
    rw [div_le_iff₀ (by positivity)]
    calc
      1 = θ₀ * (1 / θ₀) := by field_simp [hθ₀.ne']
      _ ≤ θ₀ * (n : ℝ) := mul_le_mul_of_nonneg_left hn_ge_theta hθ₀.le
      _ ≤ θ₀ * (n : ℝ) ^ K := mul_le_mul_of_nonneg_left hnK hθ₀.le
  obtain ⟨u, ⟨hu0, hu1, hufp⟩, _, hu_lb, _⟩ :=
    h31 ((thetaQ p Ac Cc n : ℚ) : ℝ) htheta_pos htheta_le
  have htheta_le1 : ((thetaQ p Ac Cc n : ℚ) : ℝ) ≤ 1 := by
    rw [htheta_eq]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hn1)
  have hpow_exp : 0 < 1 / (2 * (p : ℝ) - 2) ∧ 1 / (2 * (p : ℝ) - 2) ≤ 1 := by
    have hp_real : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have : (2 : ℝ) ≤ 2 * (p : ℝ) - 2 := by linarith
    exact ⟨one_div_pos.mpr (by linarith), div_le_one_of_le₀ (by linarith) (by linarith)⟩
  have htheta_le_rpow : ((thetaQ p Ac Cc n : ℚ) : ℝ) ≤
      ((thetaQ p Ac Cc n : ℚ) : ℝ) ^ (1 / (2 * (p : ℝ) - 2)) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge htheta_pos htheta_le1 hpow_exp.2
  have hu_ge_ctheta : c * ((thetaQ p Ac Cc n : ℚ) : ℝ) ≤ u :=
    le_trans (mul_le_mul_of_nonneg_left htheta_le_rpow hc.le) hu_lb
  have hr_ge : (n : ℝ) * (n : ℝ) ^ K ≤ ((cloudSize p Cc n : ℝ)) ^ 3 := by
    have h3p : K + 1 ≤ 3 * (p * Cc) := by omega
    calc
      (n : ℝ) * (n : ℝ) ^ K = (n : ℝ) ^ (K + 1) := by ring
      _ ≤ (n : ℝ) ^ (3 * (p * Cc)) := pow_le_pow_right₀ hn1 h3p
      _ = ((n : ℝ) ^ (p * Cc)) ^ 3 := by rw [← pow_mul]; ring_nf
      _ = ((cloudSize p Cc n : ℝ)) ^ 3 := by unfold cloudSize; push_cast; rfl
  have hr3_pos : (0 : ℝ) < ((cloudSize p Cc n : ℝ)) ^ 3 := by
    unfold cloudSize; positivity
  have hrad : 1 / ((cloudSize p Cc n : ℝ)) ^ 3 ≤ u / 2 := by
    have h1 : 2 / c ≤ (n : ℝ) := hn_ge_c
    have h2 : 1 ≤ (c / 2) * (n : ℝ) := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ c / 2)
      have : (c / 2) * (2 / c) = 1 := by field_simp [hc.ne']
      linarith
    calc
      1 / ((cloudSize p Cc n : ℝ)) ^ 3 ≤ 1 / ((n : ℝ) * (n : ℝ) ^ K) :=
        one_div_le_one_div_of_le (by positivity) hr_ge
      _ ≤ ((c / 2) * (n : ℝ)) / ((n : ℝ) * (n : ℝ) ^ K) :=
        div_le_div_of_nonneg_right h2 (by positivity)
      _ = (c * ((n : ℝ) ^ K)⁻¹) / 2 := by field_simp [hn_pos.ne']
      _ = (c * ((thetaQ p Ac Cc n : ℚ) : ℝ)) / 2 := by rw [htheta_eq]
      _ ≤ u / 2 := div_le_div_of_nonneg_right hu_ge_ctheta (by norm_num)
  have hdens : ∃ û : ℚ, u - 1 / ((cloudSize p Cc n : ℝ)) ^ 3 < (û : ℝ) ∧
      (û : ℝ) < u + 1 / ((cloudSize p Cc n : ℝ)) ^ 3 :=
    exists_rat_btwn (by linarith [one_div_pos.mpr hr3_pos])
  obtain ⟨û, hlo, hhi⟩ := hdens
  refine ⟨û, u, hu0, hu1, hufp, abs_le.mpr ⟨by linarith, by linarith⟩, by linarith, by linarith⟩

theorem p6b63_math_approx_core :
    (∀ (S : SpinLaw) {n r : ℕ} (κ : BinCfg n → Option (Config S (Fin n × Fin r)) → ℝ),
      (∀ (y : BinCfg n) (σ : Config S (Fin n × Fin r)),
        0 < κ y (some σ) → tiedCount σ = 0 ∧ ∀ i : Fin n, 0 < cloudSum σ i ↔ y i = true) →
      LhatDecodes κ) ∧
    (∀ (S : SpinLaw) (β : ℝ) {n r : ℕ} (J₀ : Matrix (Fin n) (Fin n) ℝ) (h₀ : Fin n → ℝ) (û : ℝ)
      (y : BinCfg n) (σ : Config S (Fin n × Fin r)),
      0 < idealSlot S β J₀ h₀ û y (some σ) →
      tiedCount σ = 0 ∧ ∀ i : Fin n, 0 < cloudSum σ i ↔ y i = true) ∧
    (∀ (S : SpinLaw) (β : ℝ) {n r : ℕ} (J₀ : Matrix (Fin n) (Fin n) ℝ) (h₀ : Fin n → ℝ) (û : ℝ)
      (y : BinCfg n) (P : Option (Config S (Fin n × Fin r)) → ℝ) (ε : ℝ),
      IsDistribution P →
      (∑ σ : Config S (Fin n × Fin r), |P (some σ) - idealSlot S β J₀ h₀ û y (some σ)| ≤ ε) →
      tvDist P (idealSlot S β J₀ h₀ û y) ≤ ε) ∧
    (∀ (S : SpinLaw) (β : ℝ) {n r : ℕ} (J₀ : Matrix (Fin n) (Fin n) ℝ) (h₀ : Fin n → ℝ) (û : ℝ)
      (y : BinCfg n) (nuT aT : Config S (Fin n × Fin r) → ℝ) (ε₁ ε₂ : ℝ),
      (∀ σ, 0 ≤ nuT σ) → ∑ σ, nuT σ = 1 → (∀ σ, 0 ≤ aT σ ∧ aT σ ≤ 1) →
      (∑ σ : Config S (Fin n × Fin r), |nuT σ - nuProd S β y σ| ≤ ε₁) →
      (∀ σ : Config S (Fin n × Fin r), 0 < nuT σ → |aT σ - ay J₀ h₀ û y σ| ≤ ε₂) →
      ∑ σ : Config S (Fin n × Fin r), |nuT σ * aT σ - idealSlot S β J₀ h₀ û y (some σ)| ≤ ε₁ + ε₂) ∧
    (∀ (S : SpinLaw) (p : ℕ), IsGHS S → IsTypeP S p →
      ∀ (w ε : ℝ) (Ac Cc : ℕ), 1 ≤ w → 0 < ε → ε < dExp p → GadgetParams p w ε Ac Cc →
      ∃ n₂ : ℕ, ∀ n : ℕ, n₂ ≤ n →
        ∃ û : ℚ, IsUhat S ((thetaQ p Ac Cc n : ℚ) : ℝ) (cloudSize p Cc n) û) := by
  refine ⟨@p6b63m_lhatDecodes_of_support, @p6b63m_idealSlot_support,
    p6b63m_slot_quant_tv, p6b63m_slot_factored_l1, @p6b63m_exists_isUhat⟩

end CritWinSpin

open QAlgorithms.Complexity QAlgorithms.LocalHamiltonian QuantumPRC OWFLocalDesc IsingLTL.BeliefProp CritWinSpin
open scoped BigOperators

theorem solution :
    (∀ (S : SpinLaw) {n r : ℕ} (κ : BinCfg n → Option (Config S (Fin n × Fin r)) → ℝ),
      (∀ (y : BinCfg n) (σ : Config S (Fin n × Fin r)),
        0 < κ y (some σ) → tiedCount σ = 0 ∧ ∀ i : Fin n, 0 < cloudSum σ i ↔ y i = true) →
      LhatDecodes κ) ∧
    (∀ (S : SpinLaw) (β : ℝ) {n r : ℕ} (J₀ : Matrix (Fin n) (Fin n) ℝ) (h₀ : Fin n → ℝ) (û : ℝ)
      (y : BinCfg n) (σ : Config S (Fin n × Fin r)),
      0 < idealSlot S β J₀ h₀ û y (some σ) →
      tiedCount σ = 0 ∧ ∀ i : Fin n, 0 < cloudSum σ i ↔ y i = true) ∧
    (∀ (S : SpinLaw) (β : ℝ) {n r : ℕ} (J₀ : Matrix (Fin n) (Fin n) ℝ) (h₀ : Fin n → ℝ) (û : ℝ)
      (y : BinCfg n) (P : Option (Config S (Fin n × Fin r)) → ℝ) (ε : ℝ),
      IsDistribution P →
      (∑ σ : Config S (Fin n × Fin r), |P (some σ) - idealSlot S β J₀ h₀ û y (some σ)| ≤ ε) →
      tvDist P (idealSlot S β J₀ h₀ û y) ≤ ε) ∧
    (∀ (S : SpinLaw) (β : ℝ) {n r : ℕ} (J₀ : Matrix (Fin n) (Fin n) ℝ) (h₀ : Fin n → ℝ) (û : ℝ)
      (y : BinCfg n) (nuT aT : Config S (Fin n × Fin r) → ℝ) (ε₁ ε₂ : ℝ),
      (∀ σ, 0 ≤ nuT σ) → ∑ σ, nuT σ = 1 → (∀ σ, 0 ≤ aT σ ∧ aT σ ≤ 1) →
      (∑ σ : Config S (Fin n × Fin r), |nuT σ - nuProd S β y σ| ≤ ε₁) →
      (∀ σ : Config S (Fin n × Fin r), 0 < nuT σ → |aT σ - ay J₀ h₀ û y σ| ≤ ε₂) →
      ∑ σ : Config S (Fin n × Fin r), |nuT σ * aT σ - idealSlot S β J₀ h₀ û y (some σ)| ≤ ε₁ + ε₂) ∧
    (∀ (S : SpinLaw) (p : ℕ), IsGHS S → IsTypeP S p →
      ∀ (w ε : ℝ) (Ac Cc : ℕ), 1 ≤ w → 0 < ε → ε < dExp p → GadgetParams p w ε Ac Cc →
      ∃ n₂ : ℕ, ∀ n : ℕ, n₂ ≤ n →
        ∃ û : ℚ, IsUhat S ((thetaQ p Ac Cc n : ℚ) : ℝ) (cloudSize p Cc n) û) :=
  p6b63_math_approx_core
