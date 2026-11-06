-- Prove2me | solution 1 for BotNguyenADMM.Rates.theorem_20
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T09:07:28.733639+00:00
-- url     : https://prove2.me/submissions/4c203bfe-f142-4296-bc18-0c3ad358b226
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BotNguyenADMM_Rates_Setting
import Definitions.Def_BotNguyenADMM_Rates_Lojasiewicz
import Theorems.Thm_BotNguyenADMM_Rates_theorem_18
import Theorems.Thm_BotNguyenADMM_Rates_lemma_19
import Theorems.Thm_BotNguyenADMM_Rates_theorem_20_prox_mu1_zero

open Filter Topology
open scoped InnerProductSpace RealInnerProductSpace
open NonconvexSplitting.Shared

namespace BotNguyenADMM.Rates.Thm20Aux

/-- From `‖a‖ ≤ c · M`, `0 ≤ M ≤ t`, deduce `‖a‖ ≤ max c 1 · t`. -/
theorem le_max_one_mul {a c M t : ℝ} (ha : a ≤ c * M) (hM : 0 ≤ M) (hMt : M ≤ t) :
    a ≤ max c 1 * t := by
  have h1 : c * M ≤ max c 1 * M := mul_le_mul_of_nonneg_right (le_max_left _ _) hM
  have h2 : max c 1 * M ≤ max c 1 * t :=
    mul_le_mul_of_nonneg_left hMt (le_trans zero_le_one (le_max_right _ _))
  linarith

theorem max_nonneg_sqrt_phi (CL θ s : ℝ) (hCL : 0 < CL) (hθ : θ < 1) (hs : 0 ≤ s) :
    0 ≤ max (Real.sqrt s) (phiLoj CL θ s) :=
  le_trans (Real.sqrt_nonneg s) (le_max_left _ _)

/-- The key estimate: if `0 ≤ s ≤ C u` with `C > 0`, `u ≥ 0`, and both `√u` and `u^{1−θ}` are
at most `w`, then `max{√s, φ(s)} ≤ B w` with `B = max{√C, C_L C^{1−θ}/(1−θ)}`. -/
theorem key (CL θ C s u w : ℝ) (hCL : 0 < CL) (hθ0 : 0 ≤ θ) (hθ : θ < 1) (hC : 0 < C)
    (hs : 0 ≤ s) (hsu : s ≤ C * u) (hu : 0 ≤ u) (h1 : Real.sqrt u ≤ w)
    (h2 : u ^ (1 - θ) ≤ w) :
    max (Real.sqrt s) (phiLoj CL θ s) ≤
      max (Real.sqrt C) (CL * C ^ (1 - θ) / (1 - θ)) * w := by
  have hw : 0 ≤ w := le_trans (Real.sqrt_nonneg u) h1
  have h1θ : 0 < 1 - θ := by linarith
  apply max_le
  · calc Real.sqrt s ≤ Real.sqrt (C * u) := Real.sqrt_le_sqrt hsu
      _ = Real.sqrt C * Real.sqrt u := Real.sqrt_mul hC.le u
      _ ≤ Real.sqrt C * w := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hw
  · unfold phiLoj
    have hp : s ^ (1 - θ) ≤ (C * u) ^ (1 - θ) := Real.rpow_le_rpow hs hsu h1θ.le
    rw [Real.mul_rpow hC.le hu] at hp
    have hCp : 0 ≤ C ^ (1 - θ) := Real.rpow_nonneg hC.le _
    calc CL * s ^ (1 - θ) / (1 - θ) ≤ CL * (C ^ (1 - θ) * u ^ (1 - θ)) / (1 - θ) := by
          apply div_le_div_of_nonneg_right _ h1θ.le
          exact mul_le_mul_of_nonneg_left hp hCL.le
      _ = (CL * C ^ (1 - θ) / (1 - θ)) * u ^ (1 - θ) := by ring
      _ ≤ (CL * C ^ (1 - θ) / (1 - θ)) * w := by
          apply mul_le_mul_of_nonneg_left h2
          exact div_nonneg (mul_nonneg hCL.le hCp) h1θ.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hw

theorem B_pos (CL θ C : ℝ) (hC : 0 < C) :
    0 < max (Real.sqrt C) (CL * C ^ (1 - θ) / (1 - θ)) :=
  lt_of_lt_of_le (Real.sqrt_pos.mpr hC) (le_max_left _ _)

/-- Linear-rate auxiliary bounds: for `0 < Q ≤ 1`, `1/2 ≤ 1 − θ`, `√(Qᵏ) ≤ (√Q)ᵏ` and
`(Qᵏ)^{1−θ} ≤ (√Q)ᵏ`. -/
theorem lin_aux (Q θ : ℝ) (k : ℕ) (hQ0 : 0 < Q) (hQ1 : Q ≤ 1) (hθ : θ ≤ 1 / 2) :
    Real.sqrt (Q ^ k) ≤ Real.sqrt Q ^ k ∧ (Q ^ k) ^ (1 - θ) ≤ Real.sqrt Q ^ k := by
  have hs : Real.sqrt (Q ^ k) = Real.sqrt Q ^ k := by
    have e : Q ^ k = (Real.sqrt Q ^ k) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hQ0.le]
    rw [e, Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) _)]
  refine ⟨hs.le, ?_⟩
  rw [← hs, Real.sqrt_eq_rpow]
  apply Real.rpow_le_rpow_of_exponent_ge (pow_pos hQ0 k) (pow_le_one₀ hQ0.le hQ1)
  linarith

/-- Sublinear auxiliary bounds: for `t ≥ 1` and `θ ∈ (1/2, 1)`, with `p = 1/(2θ−1)` and
`q = (1−θ)/(2θ−1)`: `√(t^{−p}) ≤ t^{−q}` and `(t^{−p})^{1−θ} ≤ t^{−q}`. -/
theorem sub_aux (t θ : ℝ) (ht : 1 ≤ t) (hθ1 : 1 / 2 < θ) (hθ2 : θ < 1) :
    Real.sqrt (t ^ (-(1 / (2 * θ - 1)))) ≤ t ^ (-((1 - θ) / (2 * θ - 1))) ∧
      (t ^ (-(1 / (2 * θ - 1)))) ^ (1 - θ) ≤ t ^ (-((1 - θ) / (2 * θ - 1))) := by
  have ht0 : 0 ≤ t := by linarith
  have hd : 0 < 2 * θ - 1 := by linarith
  constructor
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht0]
    apply Real.rpow_le_rpow_of_exponent_le ht
    rw [neg_mul, neg_le_neg_iff, div_mul_eq_mul_div, one_mul]
    apply div_le_div_of_nonneg_right _ hd.le
    linarith
  · rw [← Real.rpow_mul ht0]
    apply le_of_eq
    congr 1
    field_simp

end BotNguyenADMM.Rates.Thm20Aux

open BotNguyenADMM.Rates BotNguyenADMM.Rates.Thm20Aux in
theorem solution
    {n m : ℕ} (v : BotNguyenADMM.KL.Variant) (g : BotNguyenADMM.KL.E m → EReal) (h : BotNguyenADMM.KL.E n → ℝ) (A : BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E m)
    (L r ρ lam μ₁ μ₂ : ℝ) (M₁ : ℕ → BotNguyenADMM.KL.E n →L[ℝ] BotNguyenADMM.KL.E n) (M₂ : ℕ → BotNguyenADMM.KL.E m →L[ℝ] BotNguyenADMM.KL.E m)
    (hA2 : Assumption2 v g h A L r ρ lam μ₁ μ₂ M₁ M₂)
    (x : ℕ → BotNguyenADMM.KL.E n) (z y : ℕ → BotNguyenADMM.KL.E m) (hrun : IsRun v g h A r ρ M₁ M₂ x z y)
    (hbx : Bornology.IsBounded (Set.range x)) (hbz : Bornology.IsBounded (Set.range z))
    (hby : Bornology.IsBounded (Set.range y))
    (xh : BotNguyenADMM.KL.E n) (zh yh : BotNguyenADMM.KL.E m) (CL θ : ℝ)
    (hloj : LojAt v g h A L r ρ lam μ₁ x z y xh zh yh CL θ) :
    (θ = 0 → ∃ K : ℕ, ∀ k ≥ K, x k = xh ∧ z k = zh ∧ y k = yh) ∧
    (0 < θ ∧ θ ≤ 1 / 2 → ∃ k₀ : ℕ, 1 ≤ k₀ ∧
      ∃ C01 C02 C03 Qhat : ℝ, 0 < C01 ∧ 0 < C02 ∧ 0 < C03 ∧ 0 ≤ Qhat ∧ Qhat < 1 ∧
      ∀ k ≥ k₀, ‖x k - xh‖ ≤ C01 * Qhat ^ k ∧ ‖y k - yh‖ ≤ C02 * Qhat ^ k ∧
        ‖z k - zh‖ ≤ C03 * Qhat ^ k) ∧
    (1 / 2 < θ ∧ θ < 1 → ∃ k₀ : ℕ, 3 ≤ k₀ ∧
      ∃ C11 C12 C13 : ℝ, 0 < C11 ∧ 0 < C12 ∧ 0 < C13 ∧
      ∀ k ≥ k₀, ‖x k - xh‖ ≤ C11 * ((k : ℝ) - 1) ^ (-((1 - θ) / (2 * θ - 1))) ∧
        ‖y k - yh‖ ≤ C12 * ((k : ℝ) - 1) ^ (-((1 - θ) / (2 * θ - 1))) ∧
        ‖z k - zh‖ ≤ C13 * ((k : ℝ) - 2) ^ (-((1 - θ) / (2 * θ - 1)))) := by
  by_cases hC1 : 0 < C1 v L μ₁ lam ρ r
  swap
  · -- `C₁ ≤ 0` forces Algorithm 1 with `μ₁ = 0`.
    have hT0 : 0 < T0 lam ρ := by
      unfold T0
      have hl := hA2.lam_pos
      have hρ := hA2.ρ_pos
      have hρ2 := hA2.ρ_lt_two
      split_ifs
      · positivity
      · have : 0 < 2 - ρ := by linarith
        positivity
    have hr := hA2.r_pos
    have hL : 0 < L := by
      have := hA2.L_pos
      by_contra hn
      push Not at hn
      have : 4 * T0 lam ρ * L ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) hn
      linarith
    have hμ := hA2.μ₁_nonneg
    cases v with
    | linearized =>
      exfalso
      apply hC1
      simp only [C1]
      have : 0 < L + μ₁ := by linarith
      positivity
    | prox =>
      have hμ0 : μ₁ = 0 := by
        by_contra hne
        apply hC1
        simp only [C1]
        have : 0 < μ₁ := lt_of_le_of_ne hμ (Ne.symm hne)
        positivity
      exact theorem_20_prox_mu1_zero .prox g h A L r ρ lam μ₁ μ₂ M₁ M₂ rfl hμ0 hA2 x z y hrun
        hbx hbz hby xh zh yh CL θ hloj
  -- The case `C₁ > 0`: Theorem 18 combined with Lemma 19.
  have hCL : 0 < CL := hloj.1
  have hθ0 : 0 ≤ θ := hloj.2.1
  have hθ1 : θ < 1 := hloj.2.2.1
  have h18 := theorem_18 v g h A L r ρ lam μ₁ μ₂ M₁ M₂ hA2 x z y hrun hbx hbz hby xh zh yh CL θ hloj
  obtain ⟨k₁, hk₁, h19⟩ :=
    lemma_19 v g h A L r ρ lam μ₁ μ₂ M₁ M₂ hA2 x z y hrun hbx hbz hby xh zh yh CL θ hloj hC1
  set E := Ek v g h A L r ρ lam μ₁ x z y xh zh yh with hE
  set c20 := C20 v L μ₁ lam ρ r
  set c21 := C21 v L μ₁ lam ρ r
  set c22 := C22 v A L μ₁ lam ρ r
  refine ⟨?_, ?_, ?_⟩
  · -- (i) finite termination
    intro hθ
    obtain ⟨K, hK1, hK⟩ := h18.1 hθ
    have hE0 : ∀ k ≥ K, E k = 0 := by
      intro k hk
      simp only [hE, Ek, hK k hk, sub_self]
    have hM0 : ∀ k ≥ K, max (Real.sqrt (E k)) (phiLoj CL θ (E k)) = 0 := by
      intro k hk
      rw [hE0 k hk, hθ]
      simp [phiLoj]
    refine ⟨max K k₁ + 1, fun k hk => ?_⟩
    have hkK : k ≥ K := by omega
    have hkK' : k - 1 ≥ K := by omega
    obtain ⟨hx, hy, hz⟩ := h19 k (by omega)
    rw [hM0 k hkK, mul_zero] at hx hy
    rw [hM0 (k - 1) hkK', mul_zero] at hz
    refine ⟨?_, ?_, ?_⟩
    · exact sub_eq_zero.mp (norm_le_zero_iff.mp hx)
    · exact sub_eq_zero.mp (norm_le_zero_iff.mp hz)
    · exact sub_eq_zero.mp (norm_le_zero_iff.mp hy)
  · -- (ii) linear rate
    rintro ⟨hθp, hθh⟩
    obtain ⟨k₂, hk₂, C0, hC0, Q, hQ0, hQ1, hb⟩ := h18.2.1 ⟨hθp, hθh⟩
    set Q' := max Q (1 / 2) with hQ'
    have hQ'0 : 0 < Q' := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hQ'1 : Q' < 1 := max_lt hQ1 (by norm_num)
    have hb' : ∀ k ≥ k₂, 0 ≤ E k ∧ E k ≤ C0 * Q' ^ k := by
      intro k hk
      obtain ⟨h1, h2⟩ := hb k hk
      refine ⟨h1, le_trans h2 ?_⟩
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQ0 (le_max_left _ _) k) hC0.le
    set B := max (Real.sqrt C0) (CL * C0 ^ (1 - θ) / (1 - θ)) with hB
    have hBpos : 0 < B := B_pos CL θ C0 hC0
    set Qh := Real.sqrt Q' with hQh
    have hQhpos : 0 < Qh := Real.sqrt_pos.mpr hQ'0
    have hQh1 : Qh < 1 := by
      rw [hQh, Real.sqrt_lt' one_pos]; simpa using hQ'1
    have hM : ∀ k ≥ k₂, max (Real.sqrt (E k)) (phiLoj CL θ (E k)) ≤ B * Qh ^ k := by
      intro k hk
      obtain ⟨h1, h2⟩ := hb' k hk
      obtain ⟨a1, a2⟩ := lin_aux Q' θ k hQ'0 hQ'1.le hθh
      exact key CL θ C0 (E k) (Q' ^ k) (Qh ^ k) hCL hθ0 hθ1 hC0 h1 h2
        (pow_nonneg hQ'0.le k) a1 a2
    refine ⟨max k₁ k₂ + 1, by omega, max c20 1 * B, max c21 1 * B, max c22 1 * (B / Qh), Qh,
      by positivity, by positivity, by positivity, hQhpos.le, hQh1, fun k hk => ?_⟩
    obtain ⟨hx, hy, hz⟩ := h19 k (by omega)
    have hMk := hM k (by omega)
    have hMk1 := hM (k - 1) (by omega)
    have hpow : Qh ^ (k - 1) = Qh ^ k / Qh := by
      have : k = (k - 1) + 1 := by omega
      conv_rhs => rw [this, pow_succ]
      field_simp
    refine ⟨?_, ?_, ?_⟩
    · have := le_max_one_mul hx (max_nonneg_sqrt_phi CL θ _ hCL hθ1 (hb' k (by omega)).1) hMk
      calc _ ≤ _ := this
        _ = max c20 1 * B * Qh ^ k := by ring
    · have := le_max_one_mul hy (max_nonneg_sqrt_phi CL θ _ hCL hθ1 (hb' k (by omega)).1) hMk
      calc _ ≤ _ := this
        _ = max c21 1 * B * Qh ^ k := by ring
    · have := le_max_one_mul hz
        (max_nonneg_sqrt_phi CL θ _ hCL hθ1 (hb' (k - 1) (by omega)).1) hMk1
      calc _ ≤ _ := this
        _ = max c22 1 * (B / Qh) * Qh ^ k := by rw [hpow]; ring
  · -- (iii) sublinear rate
    rintro ⟨hθa, hθb⟩
    obtain ⟨k₂, hk₂, C1h, hC1h, hb⟩ := h18.2.2 ⟨hθa, hθb⟩
    set B := max (Real.sqrt C1h) (CL * C1h ^ (1 - θ) / (1 - θ)) with hB
    have hBpos : 0 < B := B_pos CL θ C1h hC1h
    have hM : ∀ k ≥ k₂, max (Real.sqrt (E k)) (phiLoj CL θ (E k)) ≤
        B * ((k : ℝ) - 1) ^ (-((1 - θ) / (2 * θ - 1))) := by
      intro k hk
      obtain ⟨h1, h2⟩ := hb k hk
      have ht : (1 : ℝ) ≤ (k : ℝ) - 1 := by
        have : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (le_trans hk₂ hk)
        linarith
      obtain ⟨a1, a2⟩ := sub_aux ((k : ℝ) - 1) θ ht hθa hθb
      exact key CL θ C1h (E k) _ _ hCL hθ0 hθ1 hC1h h1 h2
        (Real.rpow_nonneg (by linarith) _) a1 a2
    refine ⟨max k₁ k₂ + 1, by omega, max c20 1 * B, max c21 1 * B, max c22 1 * B,
      by positivity, by positivity, by positivity, fun k hk => ?_⟩
    obtain ⟨hx, hy, hz⟩ := h19 k (by omega)
    have hMk := hM k (by omega)
    have hMk1 := hM (k - 1) (by omega)
    have hcast : (((k - 1 : ℕ) : ℝ) - 1) = (k : ℝ) - 2 := by
      have : 1 ≤ k := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [hcast] at hMk1
    refine ⟨?_, ?_, ?_⟩
    · have := le_max_one_mul hx (max_nonneg_sqrt_phi CL θ _ hCL hθ1 (hb k (by omega)).1) hMk
      calc _ ≤ _ := this
        _ = _ := by ring
    · have := le_max_one_mul hy (max_nonneg_sqrt_phi CL θ _ hCL hθ1 (hb k (by omega)).1) hMk
      calc _ ≤ _ := this
        _ = _ := by ring
    · have := le_max_one_mul hz
        (max_nonneg_sqrt_phi CL θ _ hCL hθ1 (hb (k - 1) (by omega)).1) hMk1
      calc _ ≤ _ := this
        _ = _ := by ring
