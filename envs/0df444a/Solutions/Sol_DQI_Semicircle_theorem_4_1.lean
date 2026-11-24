-- Prove2me | solution 1 for DQI.Semicircle.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-24T08:12:55.984317+00:00
-- url     : https://prove2.me/submissions/0b9e9790-41ce-4490-b7e6-25240b7d7270

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting
import Theorems.Thm_DQI_Semicircle_eq_129
import Theorems.Thm_DQI_Semicircle_eq_131
import Theorems.Thm_DQI_Semicircle_eq_132
import Theorems.Thm_DQI_Semicircle_eq_137
import Theorems.Thm_DQI_Semicircle_lemma_9_3

namespace DQI.Semicircle

open scoped BigOperators

/-- Since `Bᵀ : 𝔽_p^m → 𝔽_p^n` has `n < m`, its kernel contains a nonzero codeword `d`,
whose weight satisfies `2ℓ + 1 < wt d ≤ m`. -/
private lemma two_mul_add_one_lt_m {p m n ℓ : ℕ} [Fact p.Prime]
    (B : Matrix (Fin m) (Fin n) (ZMod p)) (hnm : n < m)
    (hdist : DistGt B (2 * ℓ + 1)) : 2 * ℓ + 1 < m := by
  let L : (Fin m → ZMod p) →ₗ[ZMod p] (Fin n → ZMod p) := Matrix.mulVecLin B.transpose
  have hker_ne : LinearMap.ker L ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective L := LinearMap.ker_eq_bot.mp hbot
    have hfr := LinearMap.finrank_le_finrank_of_injective hinj
    simp only [Module.finrank_fin_fun] at hfr
    omega
  obtain ⟨d, hd_mem, hd_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  have hd_ker : B.transpose.mulVec d = 0 := LinearMap.mem_ker.mp hd_mem
  have hlt : 2 * ℓ + 1 < wt d := hdist d hd_ne hd_ker
  have hwt_le : wt d ≤ m := by
    unfold wt
    exact (Finset.card_filter_le _ _).trans (by simp)
  omega

private def optSatSet {p m n : ℕ} [Fact p.Prime]
    (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (ℓ : ℕ) : Set ℝ :=
  {e : ℝ | ∃ P : Polynomial ℝ, P.natDegree ≤ ℓ ∧
    ∑ x, (P.eval (obj B F x)) ^ 2 = 1 ∧
    e = ∑ x, (P.eval (obj B F x)) ^ 2 * (sat B F x : ℝ)}

private lemma optSat_eq_sSup {p m n : ℕ} [Fact p.Prime]
    (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (ℓ : ℕ) :
    optSat B F ℓ = sSup (optSatSet B F ℓ) := rfl

private lemma optSatSet_nonempty {p m n : ℕ} [Fact p.Prime]
    (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (ℓ : ℕ) :
    (optSatSet B F ℓ).Nonempty := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hpn_pos : (0 : ℝ) < (p : ℝ) ^ n := pow_pos hp_pos n
  let c : ℝ := 1 / Real.sqrt ((p : ℝ) ^ n)
  refine ⟨∑ x, (Polynomial.C c).eval (obj B F x) ^ 2 * (sat B F x : ℝ),
    Polynomial.C c, ?_, ?_, rfl⟩
  · simp
  · have hcard : ((Finset.univ : Finset (Fin n → ZMod p)).card : ℝ) = (p : ℝ) ^ n := by
      rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow]
    have hc2 : c ^ 2 = 1 / ((p : ℝ) ^ n) := by
      dsimp [c]
      rw [div_pow, one_pow, Real.sq_sqrt hpn_pos.le]
    simp only [Polynomial.eval_C, Finset.sum_const, nsmul_eq_mul, hcard, hc2]
    exact mul_one_div_cancel hpn_pos.ne'

private lemma optSatSet_le_m {p m n : ℕ} [Fact p.Prime]
    (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (ℓ : ℕ) :
    ∀ e ∈ optSatSet B F ℓ, e ≤ m := by
  rintro e ⟨P, -, hnorm, rfl⟩
  calc ∑ x, (P.eval (obj B F x)) ^ 2 * (sat B F x : ℝ)
      ≤ ∑ x, (P.eval (obj B F x)) ^ 2 * (m : ℝ) := by
        refine Finset.sum_le_sum fun x _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
    _ = (∑ x, (P.eval (obj B F x)) ^ 2) * (m : ℝ) := (Finset.sum_mul _ _ _).symm
    _ = (m : ℝ) := by rw [hnorm, one_mul]

private lemma optSat_le_m {p m n : ℕ} [Fact p.Prime]
    (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p)) (ℓ : ℕ) :
    optSat B F ℓ ≤ m := by
  rw [optSat_eq_sSup]
  exact csSup_le (optSatSet_nonempty B F ℓ) (optSatSet_le_m B F ℓ)

private lemma optSat_mono {p m n : ℕ} [Fact p.Prime]
    (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p))
    {ℓ₁ ℓ₂ : ℕ} (hℓ : ℓ₁ ≤ ℓ₂) :
    optSat B F ℓ₁ ≤ optSat B F ℓ₂ := by
  rw [optSat_eq_sSup, optSat_eq_sSup]
  refine csSup_le_csSup ⟨m, optSatSet_le_m B F ℓ₂⟩ (optSatSet_nonempty B F ℓ₁) ?_
  rintro e ⟨P, hdeg, hnorm, he⟩
  exact ⟨P, hdeg.trans hℓ, hnorm, he⟩

private lemma distGt_mono {p m n : ℕ} [Fact p.Prime]
    {B : Matrix (Fin m) (Fin n) (ZMod p)} {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) (h : DistGt B t₂) :
    DistGt B t₁ :=
  fun d hd hker => lt_of_le_of_lt ht (h d hd hker)

private lemma atri_zero_eq_zero (m : ℕ) (dpar : ℝ) :
    Atri m 0 dpar = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [Atri]

private lemma lamMax_atri_zero (m : ℕ) (dpar : ℝ) :
    lamMax (Atri m 0 dpar) = 0 := by
  unfold lamMax
  rw [atri_zero_eq_zero, spectrum.zero_eq, csSup_singleton]

private lemma optSat_zero_div {p m n r : ℕ} [Fact p.Prime]
    (B : Matrix (Fin m) (Fin n) (ZMod p)) (F : Fin m → Finset (ZMod p))
    (hF : ∀ i, (F i).card = r) (hr : 1 ≤ r) (hrp : r < p) (hnm : n < m)
    (hdist : DistGt B 1) :
    optSat B F 0 / m = (r : ℝ) / p := by
  have h131 := eq_131 p m n B F r hF hr hrp hnm 0 hdist
  rw [lamMax_atri_zero] at h131
  simpa using h131

private lemma dparOf_eq_rho (p r : ℕ) (hp : 0 < p) (hr : 1 ≤ r) (hrp : r ≤ p) :
    dparOf p r =
      (1 - 2 * ((r : ℝ) / p)) / Real.sqrt (((r : ℝ) / p) * (1 - (r : ℝ) / p)) := by
  unfold dparOf
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hp_ne : (p : ℝ) ≠ 0 := hp_pos.ne'
  have hr_le_p : (r : ℝ) ≤ p := Nat.cast_le.mpr hrp
  have hnum : 1 - 2 * ((r : ℝ) / p) = ((p : ℝ) - 2 * r) / p := by
    field_simp
  have hrad : ((r : ℝ) / p) * (1 - (r : ℝ) / p) = ((r : ℝ) * ((p : ℝ) - r)) / ((p : ℝ) ^ 2) := by
    field_simp
  have hnonneg : 0 ≤ (r : ℝ) * ((p : ℝ) - r) :=
    mul_nonneg (Nat.cast_nonneg r) (sub_nonneg.mpr hr_le_p)
  have hden : Real.sqrt (((r : ℝ) / p) * (1 - (r : ℝ) / p)) =
      Real.sqrt ((r : ℝ) * ((p : ℝ) - r)) / p := by
    rw [hrad, Real.sqrt_div hnonneg, Real.sqrt_sq hp_pos.le]
  rw [hnum, hden, div_div_div_cancel_right₀ hp_ne]

/-- Core asymptotic evaluation when `μ' > 0` and `(r : ℝ) / p ≤ 1 - ℓ'_j / m_j` eventually. -/
private lemma tendsto_optSat_of_eventually_le (p : ℕ) [Fact p.Prime] (r : ℕ)
    (hr : 1 ≤ r) (hrp : r < p) (μ' : ℝ) (hμ'0 : 0 < μ') (hμ'1 : μ' ≤ 1)
    (m n ℓ' : ℕ → ℕ) (B : ∀ j, Matrix (Fin (m j)) (Fin (n j)) (ZMod p))
    (F : ∀ j, Fin (m j) → Finset (ZMod p)) (hF : ∀ j i, (F j i).card = r) (hnm : ∀ j, n j < m j)
    (hdist : ∀ j, DistGt (B j) (2 * ℓ' j + 1))
    (hratio : Filter.Tendsto (fun j => (ℓ' j : ℝ) / (m j : ℝ)) Filter.atTop (nhds μ'))
    (hm : Filter.Tendsto m Filter.atTop Filter.atTop)
    (hρ_ev : ∀ᶠ j in Filter.atTop, (r : ℝ) / p ≤ 1 - (ℓ' j : ℝ) / (m j : ℝ)) :
    Filter.Tendsto (fun j => optSat (B j) (F j) (ℓ' j) / m j) Filter.atTop
      (nhds ((Real.sqrt (μ' * (1 - (r : ℝ) / p)) + Real.sqrt ((r : ℝ) / p * (1 - μ'))) ^ 2)) := by
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp hρ_ev
  have hbound : ∀ j, 2 * ℓ' j + 1 < m j :=
    fun j => two_mul_add_one_lt_m (B j) (hnm j) (hdist j)
  have hratio_s : Filter.Tendsto (fun k => (ℓ' (k + J) : ℝ) / (m (k + J) : ℝ))
      Filter.atTop (nhds μ') :=
    (Filter.tendsto_add_atTop_iff_nat J).mpr hratio
  have hm_s : Filter.Tendsto (fun k => m (k + J)) Filter.atTop Filter.atTop :=
    (Filter.tendsto_add_atTop_iff_nat J).mpr hm
  have hℓm_s : ∀ k, 2 * ℓ' (k + J) ≤ m (k + J) := fun k => by have := hbound (k + J); omega
  have hd_s : ∀ k, 0 < ℓ' (k + J) →
      -((m (k + J) : ℝ) - 2 * ℓ' (k + J)) /
        Real.sqrt (ℓ' (k + J) * ((m (k + J) : ℝ) - ℓ' (k + J))) ≤ dparOf p r := by
    intro k hk
    have hlt := hbound (k + J)
    exact eq_132 p r (m (k + J)) (ℓ' (k + J)) hr hrp hk (by omega) (hJ (k + J) (by omega))
  have hlam_s := lemma_9_3 μ' (dparOf p r) hμ'0 (fun k => m (k + J)) (fun k => ℓ' (k + J))
    hratio_s hm_s hℓm_s hd_s
  have hlam : Filter.Tendsto (fun j => lamMax (Atri (m j) (ℓ' j) (dparOf p r)) / m j)
      Filter.atTop (nhds (μ' * dparOf p r + 2 * Real.sqrt (μ' * (1 - μ')))) :=
    (Filter.tendsto_add_atTop_iff_nat J).mp hlam_s
  set ρ : ℝ := (r : ℝ) / p
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  have hp_rpos : (0 : ℝ) < p := Nat.cast_pos.mpr hp_pos
  have hρ0 : 0 < ρ := div_pos (Nat.cast_pos.mpr (by omega)) hp_rpos
  have hρ1 : ρ < 1 := (div_lt_one hp_rpos).mpr (Nat.cast_lt.mpr hrp)
  have hcomb : Filter.Tendsto
      (fun j => ρ + Real.sqrt (ρ * (1 - ρ)) * (lamMax (Atri (m j) (ℓ' j) (dparOf p r)) / m j))
      Filter.atTop
      (nhds (ρ + Real.sqrt (ρ * (1 - ρ)) *
        (μ' * dparOf p r + 2 * Real.sqrt (μ' * (1 - μ'))))) :=
    tendsto_const_nhds.add (hlam.const_mul _)
  have heq_lim : ρ + Real.sqrt (ρ * (1 - ρ)) *
      (μ' * dparOf p r + 2 * Real.sqrt (μ' * (1 - μ'))) =
      (Real.sqrt (μ' * (1 - ρ)) + Real.sqrt (ρ * (1 - μ'))) ^ 2 := by
    rw [dparOf_eq_rho p r hp_pos hr hrp.le]
    exact eq_137 ρ μ' hρ0 hρ1 hμ'0.le hμ'1
  rw [heq_lim] at hcomb
  refine hcomb.congr fun j => ?_
  have h131 := eq_131 p (m j) (n j) (B j) (F j) r (hF j) hr hrp (hnm j) (ℓ' j) (hdist j)
  rw [h131, mul_div_assoc]

/-- Boundary case `μ = 0`: `optSat / m → r / p` via `eq_131`, `eq_132`, and Gershgorin `eq_129`. -/
private lemma tendsto_optSat_zero (p : ℕ) [Fact p.Prime] (r : ℕ)
    (hr : 1 ≤ r) (hrp : r < p)
    (m n ℓ : ℕ → ℕ) (B : ∀ j, Matrix (Fin (m j)) (Fin (n j)) (ZMod p))
    (F : ∀ j, Fin (m j) → Finset (ZMod p)) (hF : ∀ j i, (F j i).card = r) (hnm : ∀ j, n j < m j)
    (hdist : ∀ j, DistGt (B j) (2 * ℓ j + 1))
    (hratio : Filter.Tendsto (fun j => (ℓ j : ℝ) / (m j : ℝ)) Filter.atTop (nhds 0))
    (hm : Filter.Tendsto m Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun j => optSat (B j) (F j) (ℓ j) / m j) Filter.atTop
      (nhds ((r : ℝ) / p)) := by
  set ρ : ℝ := (r : ℝ) / p
  set d : ℝ := dparOf p r
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hρ0 : 0 < ρ := div_pos (Nat.cast_pos.mpr (by omega)) hp_pos
  have hρ1 : ρ < 1 := (div_lt_one hp_pos).mpr (Nat.cast_lt.mpr hrp)
  have hbound : ∀ j, 2 * ℓ j + 1 < m j :=
    fun j => two_mul_add_one_lt_m (B j) (hnm j) (hdist j)
  have hlow : ∀ j, ρ ≤ optSat (B j) (F j) (ℓ j) / m j := by
    intro j
    have hm_pos : (0 : ℝ) < m j := Nat.cast_pos.mpr (by have := hbound j; omega)
    have hdist0 : DistGt (B j) 1 := distGt_mono (by omega) (hdist j)
    have h0 : optSat (B j) (F j) 0 / m j = ρ :=
      optSat_zero_div (B j) (F j) (hF j) hr hrp (hnm j) hdist0
    rw [← h0]
    exact div_le_div_of_nonneg_right (optSat_mono (B j) (F j) (Nat.zero_le _)) hm_pos.le
  let u : ℕ → ℝ := fun j =>
    ρ + Real.sqrt (ρ * (1 - ρ)) *
      (2 / Real.sqrt (m j) + ((ℓ j : ℝ) / m j) * d +
        2 * Real.sqrt (((ℓ j : ℝ) / m j) * (1 - (ℓ j : ℝ) / m j)))
  have h1mρ : Filter.Tendsto (fun j => 1 - (ℓ j : ℝ) / (m j : ℝ)) Filter.atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hratio
  have hρ_lt : ρ < 1 - 0 := by linarith
  have hρ_ev : ∀ᶠ j in Filter.atTop, ρ ≤ 1 - (ℓ j : ℝ) / (m j : ℝ) :=
    (h1mρ.eventually (Ioi_mem_nhds hρ_lt)).mono fun _ hj => le_of_lt hj
  have hup : ∀ᶠ j in Filter.atTop, optSat (B j) (F j) (ℓ j) / m j ≤ u j := by
    refine hρ_ev.mono fun j hj_ρ => ?_
    have hlt := hbound j
    have hm_pos : (0 : ℝ) < m j := Nat.cast_pos.mpr (by omega)
    have hsqrt_coeff : 0 ≤ Real.sqrt (ρ * (1 - ρ)) := Real.sqrt_nonneg _
    rcases Nat.eq_zero_or_pos (ℓ j) with hℓ0 | hℓ_pos
    · have hdist0 : DistGt (B j) 1 := distGt_mono (by omega) (hdist j)
      have h0 : optSat (B j) (F j) 0 / m j = ρ :=
        optSat_zero_div (B j) (F j) (hF j) hr hrp (hnm j) hdist0
      dsimp [u]
      rw [hℓ0, h0]
      simp only [Nat.cast_zero, zero_div, zero_mul, sub_zero, mul_one, Real.sqrt_zero, add_zero]
      have : 0 ≤ Real.sqrt (ρ * (1 - ρ)) * (2 / Real.sqrt (m j)) := by positivity
      linarith
    · have hd : -((m j : ℝ) - 2 * ℓ j) / Real.sqrt (ℓ j * ((m j : ℝ) - ℓ j)) ≤ d :=
        eq_132 p r (m j) (ℓ j) hr hrp hℓ_pos (by omega) hj_ρ
      have h129 := eq_129 (m j) (ℓ j) d hℓ_pos (by omega) hd
      set Bval : ℝ := 2 * Real.sqrt (m j) + (ℓ j : ℝ) * d +
        2 * Real.sqrt ((ℓ j : ℝ) * ((m j : ℝ) - ℓ j))
      have hBval_nonneg : 0 ≤ Bval := by
        have hℓ_rpos : (0 : ℝ) < ℓ j := Nat.cast_pos.mpr hℓ_pos
        have hmℓ_pos : (0 : ℝ) < (m j : ℝ) - ℓ j := by
          have : (ℓ j : ℝ) < m j := Nat.cast_lt.mpr (by omega)
          linarith
        have hprod_pos : 0 < (ℓ j : ℝ) * ((m j : ℝ) - ℓ j) := mul_pos hℓ_rpos hmℓ_pos
        have hsq_pos : 0 < Real.sqrt ((ℓ j : ℝ) * ((m j : ℝ) - ℓ j)) := Real.sqrt_pos.mpr hprod_pos
        have hd' : -((m j : ℝ) - 2 * (ℓ j : ℝ)) ≤ d * Real.sqrt ((ℓ j : ℝ) * ((m j : ℝ) - ℓ j)) :=
          (div_le_iff₀ hsq_pos).mp hd
        have hkey : 0 ≤ ((ℓ j : ℝ) * d + 2 * Real.sqrt ((ℓ j : ℝ) * ((m j : ℝ) - ℓ j))) *
            Real.sqrt ((ℓ j : ℝ) * ((m j : ℝ) - ℓ j)) := by
          calc 0 ≤ (ℓ j : ℝ) * (m j : ℝ) := by positivity
            _ = (ℓ j : ℝ) * (-((m j : ℝ) - 2 * (ℓ j : ℝ))) +
                  2 * ((ℓ j : ℝ) * ((m j : ℝ) - ℓ j)) := by ring
            _ ≤ (ℓ j : ℝ) * (d * Real.sqrt ((ℓ j : ℝ) * ((m j : ℝ) - ℓ j))) +
                  2 * (Real.sqrt ((ℓ j : ℝ) * ((m j : ℝ) - ℓ j)) *
                    Real.sqrt ((ℓ j : ℝ) * ((m j : ℝ) - ℓ j))) := by
                  rw [Real.mul_self_sqrt hprod_pos.le]
                  nlinarith
            _ = ((ℓ j : ℝ) * d + 2 * Real.sqrt ((ℓ j : ℝ) * ((m j : ℝ) - ℓ j))) *
                  Real.sqrt ((ℓ j : ℝ) * ((m j : ℝ) - ℓ j)) := by ring
        have hsum_nonneg : 0 ≤ (ℓ j : ℝ) * d + 2 * Real.sqrt ((ℓ j : ℝ) * ((m j : ℝ) - ℓ j)) :=
          nonneg_of_mul_nonneg_left hkey hsq_pos
        have : 0 ≤ 2 * Real.sqrt (m j) := by positivity
        dsimp [Bval]
        linarith
      have hlam_le : lamMax (Atri (m j) (ℓ j) d) ≤ Bval :=
        Real.sSup_le h129 hBval_nonneg
      have hBdiv : Bval / (m j : ℝ) =
          2 / Real.sqrt (m j) + ((ℓ j : ℝ) / m j) * d +
            2 * Real.sqrt (((ℓ j : ℝ) / m j) * (1 - (ℓ j : ℝ) / m j)) := by
        have hm_ne : (m j : ℝ) ≠ 0 := hm_pos.ne'
        have h1 : 2 * Real.sqrt (m j) / (m j : ℝ) = 2 / Real.sqrt (m j) := by
          have hsq : Real.sqrt (m j) * Real.sqrt (m j) = (m j : ℝ) := Real.mul_self_sqrt hm_pos.le
          have hsq_ne : Real.sqrt (m j) ≠ 0 := (Real.sqrt_pos.mpr hm_pos).ne'
          rw [div_eq_div_iff hm_ne hsq_ne]
          nlinarith
        have h2 : (ℓ j : ℝ) * d / (m j : ℝ) = ((ℓ j : ℝ) / m j) * d := div_mul_eq_mul_div _ _ _ |>.symm
        have hrad_eq : ((ℓ j : ℝ) * ((m j : ℝ) - ℓ j)) / ((m j : ℝ) ^ 2) =
            ((ℓ j : ℝ) / m j) * (1 - (ℓ j : ℝ) / m j) := by
          field_simp
        have hnonneg_prod : 0 ≤ (ℓ j : ℝ) * ((m j : ℝ) - ℓ j) := by
          refine mul_nonneg (Nat.cast_nonneg _) ?_
          have : (ℓ j : ℝ) ≤ m j := Nat.cast_le.mpr (by omega)
          linarith
        have h3 : 2 * Real.sqrt ((ℓ j : ℝ) * ((m j : ℝ) - ℓ j)) / (m j : ℝ) =
            2 * Real.sqrt (((ℓ j : ℝ) / m j) * (1 - (ℓ j : ℝ) / m j)) := by
          rw [← hrad_eq, Real.sqrt_div hnonneg_prod, Real.sqrt_sq hm_pos.le, mul_div_assoc]
        dsimp [Bval]
        rw [add_div, add_div, h1, h2, h3]
      have h131 := eq_131 p (m j) (n j) (B j) (F j) r (hF j) hr hrp (hnm j) (ℓ j) (hdist j)
      rw [h131, mul_div_assoc]
      dsimp [u]
      rw [← hBdiv]
      gcongr
  have hu_tendsto : Filter.Tendsto u Filter.atTop (nhds ρ) := by
    have hm_real : Filter.Tendsto (fun j => (m j : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.comp hm
    have hsqrt_m : Filter.Tendsto (fun j => Real.sqrt (m j)) Filter.atTop Filter.atTop :=
      Real.tendsto_sqrt_atTop.comp hm_real
    have ht1 : Filter.Tendsto (fun j => 2 / Real.sqrt (m j)) Filter.atTop (nhds 0) := by
      simpa using tendsto_const_nhds.div_atTop hsqrt_m
    have ht2 : Filter.Tendsto (fun j => ((ℓ j : ℝ) / m j) * d) Filter.atTop (nhds 0) := by
      simpa using hratio.mul_const d
    have ht3 : Filter.Tendsto
        (fun j => 2 * Real.sqrt (((ℓ j : ℝ) / m j) * (1 - (ℓ j : ℝ) / m j)))
        Filter.atTop (nhds 0) := by
      have hprod : Filter.Tendsto
          (fun j => ((ℓ j : ℝ) / m j) * (1 - (ℓ j : ℝ) / m j))
          Filter.atTop (nhds (0 * (1 - 0))) :=
        hratio.mul (tendsto_const_nhds.sub hratio)
      have hsq : Filter.Tendsto
          (fun j => Real.sqrt (((ℓ j : ℝ) / m j) * (1 - (ℓ j : ℝ) / m j)))
          Filter.atTop (nhds (Real.sqrt (0 * (1 - 0)))) :=
        (Real.continuous_sqrt.tendsto _).comp hprod
      simpa using hsq.const_mul 2
    have hsum : Filter.Tendsto
        (fun j => 2 / Real.sqrt (m j) + ((ℓ j : ℝ) / m j) * d +
          2 * Real.sqrt (((ℓ j : ℝ) / m j) * (1 - (ℓ j : ℝ) / m j)))
        Filter.atTop (nhds 0) := by
      simpa using (ht1.add ht2).add ht3
    have hall : Filter.Tendsto u Filter.atTop (nhds (ρ + Real.sqrt (ρ * (1 - ρ)) * 0)) :=
      tendsto_const_nhds.add (hsum.const_mul _)
    simpa using hall
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu_tendsto
    (Filter.Eventually.of_forall hlow) hup

end DQI.Semicircle

open DQI.Semicircle

/-- Theorem 4.1, p. 11 (with (139), p. 34). Fixed prime `p` and `r ∈ {1, …, p−1}`; a sequence of
instances `j ↦ (B_j, F_j)` with `m_j → ∞`, `ℓ_j/m_j → μ` and `2ℓ_j + 1 < d^⊥`. -/
theorem solution (p : ℕ) [Fact p.Prime] (r : ℕ) (hr : 1 ≤ r) (hrp : r < p) (μ : ℝ) (hμ : 0 ≤ μ)
    (m n ℓ : ℕ → ℕ) (B : ∀ j, Matrix (Fin (m j)) (Fin (n j)) (ZMod p))
    (F : ∀ j, Fin (m j) → Finset (ZMod p)) (hF : ∀ j i, (F j i).card = r) (hnm : ∀ j, n j < m j)
    (hdist : ∀ j, DistGt (B j) (2 * ℓ j + 1))
    (hratio : Filter.Tendsto (fun j => (ℓ j : ℝ) / (m j : ℝ)) Filter.atTop (nhds μ))
    (hm : Filter.Tendsto m Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun j => optSat (B j) (F j) (ℓ j) / m j) Filter.atTop
      (nhds (semicircle ((r : ℝ) / p) μ)) := by
  set ρ : ℝ := (r : ℝ) / p
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hρ0 : 0 < ρ := div_pos (Nat.cast_pos.mpr (by omega)) hp_pos
  have hρ1 : ρ < 1 := (div_lt_one hp_pos).mpr (Nat.cast_lt.mpr hrp)
  have hbound : ∀ j, 2 * ℓ j + 1 < m j :=
    fun j => two_mul_add_one_lt_m (B j) (hnm j) (hdist j)
  have hμ_half : μ ≤ 1 / 2 := by
    refine le_of_tendsto_of_tendsto' hratio tendsto_const_nhds fun j => ?_
    have hlt := hbound j
    have hm_pos : (0 : ℝ) < m j := Nat.cast_pos.mpr (by omega)
    rw [div_le_iff₀ hm_pos]
    have h2 : (2 * ℓ j : ℝ) ≤ m j := by exact_mod_cast (show 2 * ℓ j ≤ m j by omega)
    push_cast at h2
    linarith
  have hμ1 : μ ≤ 1 := by linarith
  rcases lt_or_ge ρ (1 - μ) with hρ_lt | hρ_ge
  · have hsemi : semicircle ρ μ =
        (Real.sqrt (μ * (1 - ρ)) + Real.sqrt (ρ * (1 - μ))) ^ 2 := by
      unfold semicircle
      rw [if_pos hρ_lt.le]
    rw [hsemi]
    rcases eq_or_lt_of_le hμ with rfl | hμ_pos
    · have h0 := tendsto_optSat_zero p r hr hrp m n ℓ B F hF hnm hdist hratio hm
      have hval : (Real.sqrt (0 * (1 - ρ)) + Real.sqrt (ρ * (1 - 0))) ^ 2 = ρ := by
        simp [Real.sq_sqrt hρ0.le]
      rwa [hval]
    · have h1m : Filter.Tendsto (fun j => 1 - (ℓ j : ℝ) / (m j : ℝ))
          Filter.atTop (nhds (1 - μ)) :=
        tendsto_const_nhds.sub hratio
      have hρ_ev : ∀ᶠ j in Filter.atTop, ρ ≤ 1 - (ℓ j : ℝ) / (m j : ℝ) :=
        (h1m.eventually (Ioi_mem_nhds hρ_lt)).mono fun _ hj => le_of_lt hj
      exact tendsto_optSat_of_eventually_le p r hr hrp μ hμ_pos hμ1 m n ℓ B F hF hnm
        hdist hratio hm hρ_ev
  · have hsemi : semicircle ρ μ = 1 := by
      unfold semicircle
      split_ifs with hle
      · have hμ_eq : μ = 1 - ρ := by linarith
        subst hμ_eq
        have h1 : Real.sqrt ((1 - ρ) * (1 - ρ)) = 1 - ρ :=
          Real.sqrt_mul_self (by linarith)
        have h2 : Real.sqrt (ρ * (1 - (1 - ρ))) = ρ := by
          ring_nf
          exact Real.sqrt_sq hρ0.le
        rw [h1, h2]
        ring
      · rfl
    rw [hsemi]
    set μ' : ℝ := 1 - ρ
    have hμ'0 : 0 < μ' := by dsimp [μ']; linarith
    have hμ'1 : μ' ≤ 1 := by dsimp [μ']; linarith
    have hμ'_le_μ : μ' ≤ μ := by dsimp [μ']; linarith
    let ℓ' : ℕ → ℕ := fun j => min (ℓ j) (Nat.floor (μ' * (m j : ℝ)))
    have hdist' : ∀ j, DistGt (B j) (2 * ℓ' j + 1) := by
      intro j
      have : ℓ' j ≤ ℓ j := Nat.min_le_left _ _
      exact distGt_mono (by omega) (hdist j)
    have hfloor_ratio : Filter.Tendsto
        (fun j => (Nat.floor (μ' * (m j : ℝ)) : ℝ) / (m j : ℝ)) Filter.atTop (nhds μ') := by
      have hm_real : Filter.Tendsto (fun j => (m j : ℝ)) Filter.atTop Filter.atTop :=
        tendsto_natCast_atTop_atTop.comp hm
      have hlow_f : Filter.Tendsto (fun j => μ' - 1 / (m j : ℝ)) Filter.atTop (nhds μ') := by
        have hinv : Filter.Tendsto (fun j => 1 / (m j : ℝ)) Filter.atTop (nhds 0) :=
          tendsto_const_nhds.div_atTop hm_real
        simpa using tendsto_const_nhds.sub hinv
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow_f tendsto_const_nhds (fun j => ?_) (fun j => ?_)
      · have hm_pos : (0 : ℝ) < m j := Nat.cast_pos.mpr (by have := hbound j; omega)
        have hlt1 : μ' * (m j : ℝ) < (Nat.floor (μ' * (m j : ℝ)) : ℝ) + 1 :=
          Nat.lt_floor_add_one _
        rw [le_div_iff₀ hm_pos]
        have : (μ' - 1 / (m j : ℝ)) * (m j : ℝ) = μ' * (m j : ℝ) - 1 := by field_simp
        linarith
      · have hm_pos : (0 : ℝ) < m j := Nat.cast_pos.mpr (by have := hbound j; omega)
        rw [div_le_iff₀ hm_pos]
        exact Nat.floor_le (by positivity)
    have hratio' : Filter.Tendsto (fun j => (ℓ' j : ℝ) / (m j : ℝ)) Filter.atTop (nhds μ') := by
      have hmin : Filter.Tendsto
          (fun j => min ((ℓ j : ℝ) / (m j : ℝ)) ((Nat.floor (μ' * (m j : ℝ)) : ℝ) / (m j : ℝ)))
          Filter.atTop (nhds (min μ μ')) :=
        hratio.min hfloor_ratio
      rw [min_eq_right hμ'_le_μ] at hmin
      refine hmin.congr fun j => ?_
      have hm_nonneg : (0 : ℝ) ≤ m j := Nat.cast_nonneg _
      dsimp [ℓ']
      rw [Nat.cast_min, min_div_div_right hm_nonneg]
    have hρ_ev' : ∀ᶠ j in Filter.atTop, ρ ≤ 1 - (ℓ' j : ℝ) / (m j : ℝ) := by
      refine Filter.Eventually.of_forall fun j => ?_
      have hm_pos : (0 : ℝ) < m j := Nat.cast_pos.mpr (by have := hbound j; omega)
      have hle1 : (ℓ' j : ℝ) ≤ (Nat.floor (μ' * (m j : ℝ)) : ℝ) :=
        Nat.cast_le.mpr (Nat.min_le_right _ _)
      have hle2 : (Nat.floor (μ' * (m j : ℝ)) : ℝ) ≤ μ' * (m j : ℝ) :=
        Nat.floor_le (by positivity)
      have hdiv : (ℓ' j : ℝ) / (m j : ℝ) ≤ μ' := (div_le_iff₀ hm_pos).mpr (hle1.trans hle2)
      dsimp [μ'] at hdiv
      linarith
    have hlow_tendsto := tendsto_optSat_of_eventually_le p r hr hrp μ' hμ'0 hμ'1 m n ℓ' B F hF hnm
      hdist' hratio' hm hρ_ev'
    have hval1 : (Real.sqrt (μ' * (1 - ρ)) + Real.sqrt (ρ * (1 - μ'))) ^ 2 = 1 := by
      have h1 : Real.sqrt (μ' * (1 - ρ)) = 1 - ρ := by
        dsimp [μ']
        exact Real.sqrt_mul_self (by linarith)
      have h2 : Real.sqrt (ρ * (1 - μ')) = ρ := by
        dsimp [μ']
        ring_nf
        exact Real.sqrt_sq hρ0.le
      rw [h1, h2]
      ring
    rw [hval1] at hlow_tendsto
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow_tendsto tendsto_const_nhds
      (fun j => ?_) (fun j => ?_)
    · have hm_pos : (0 : ℝ) < m j := Nat.cast_pos.mpr (by have := hbound j; omega)
      exact div_le_div_of_nonneg_right (optSat_mono (B j) (F j) (Nat.min_le_left _ _)) hm_pos.le
    · have hm_pos : (0 : ℝ) < m j := Nat.cast_pos.mpr (by have := hbound j; omega)
      exact (div_le_one hm_pos).mpr (optSat_le_m (B j) (F j) (ℓ j))
