-- Prove2me | solution 1 for CarbonPolicy.TaxVsCap.proposition_1a
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:13:36.150769+00:00
-- url     : https://prove2.me/submissions/c8c09b4d-955f-4128-b0d3-b99fb852a229

import Mathlib
import Definitions.Def_CarbonPolicy_TaxVsCap_Setting
set_option autoImplicit false
open ProbabilityTheory MeasureTheory
open CarbonPolicy.TaxVsCap

theorem kk_profit_q (b w γ a k : ℝ) (hb : 0 < b) :
    profit b w γ a k (qStar b γ a k) = (a - γ * k) ^ 2 / (4 * b) + w * k := by
  unfold profit qStar
  field_simp
  ring

theorem kk_int_sq {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a : Ω → ℝ) (ha : MemLp a 2 P) (c : ℝ) :
    ∫ ω, (a ω - c) ^ 2 ∂P = Var[a; P] + (∫ ω, a ω ∂P - c) ^ 2 := by
  have h1 : Integrable a P := ha.integrable (by norm_num)
  have h2 : Integrable (fun ω => a ω ^ 2) P := ha.integrable_sq
  have hv := variance_eq_sub ha
  have e : ∀ ω, (a ω - c) ^ 2 = a ω ^ 2 - 2 * c * a ω + c ^ 2 := fun ω => by ring
  simp_rw [e]
  have h3 : Integrable (fun ω => 2 * c * a ω) P := h1.const_mul _
  have h4 : Integrable (fun ω => a ω ^ 2 - 2 * c * a ω) P := h2.sub h3
  rw [integral_add h4 (integrable_const _), integral_sub h2 h3, integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hv' : Var[a; P] = ∫ ω, a ω ^ 2 ∂P - (∫ ω, a ω ∂P) ^ 2 := by
    rw [hv]; simp [Pi.pow_apply]
  rw [hv']
  ring

theorem kk_int_main {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a : Ω → ℝ) (ha : MemLp a 2 P) (c d b : ℝ) :
    ∫ ω, ((a ω - c) ^ 2 / (4 * b) + d) ∂P = (Var[a; P] + (∫ ω, a ω ∂P - c) ^ 2) / (4 * b) + d := by
  have hi : Integrable (fun ω => (a ω - c) ^ 2) P := (ha.sub (memLp_const c)).integrable_sq
  rw [integral_add (hi.div_const _) (integrable_const _), integral_div, kk_int_sq P a ha c]
  simp

theorem kk_moment_tax {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b β γp w : ℝ) (hb : 0 < b) (γ : ℝ) :
    PiT M b β γp w γ =
      ((abar M.P M.a) - γ * (kbar M.P M.k)) ^ 2 / (4 * b) +
        (sigmaD M.P M.a) ^ 2 / (4 * b) - β * (γp - γ) ^ 2 + w * (kbar M.P M.k) := by
  haveI := M.prob
  unfold PiT
  simp_rw [kk_profit_q b w γ _ _ hb]
  have hs : sigmaD M.P M.a ^ 2 = Var[M.a; M.P] := by
    unfold sigmaD
    rw [Real.sq_sqrt (variance_nonneg _ _)]
  rw [hs, kk_int_main M.P M.a M.a_L2 (γ * kbar M.P M.k) (w * kbar M.P M.k) b]
  unfold abar
  ring


theorem kk_lemma_1 {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b β γp w : ℝ) (hb : 0 < b) (hγp : 0 < γp)
    (hA : Assumption1 M b β γp) :
    OptimalTax M b β γp w (gammaT0 b β γp (abar M.P M.a) (kbar M.P M.k)) ∧
    ∀ γ : ℝ, OptimalTax M b β γp w γ → γ = gammaT0 b β γp (abar M.P M.a) (kbar M.P M.k) := by
  haveI := M.prob
  obtain ⟨h1, h2, h3⟩ := hA
  have hk : 0 < kbar M.P M.k := M.kbar_pos
  have hs2 : 0 ≤ sigma M.P M.k ^ 2 := sq_nonneg _
  set k := kbar M.P M.k with hkdef
  set ā := abar M.P M.a with hadef
  have hD : 0 < 4 * b * β - k ^ 2 := by nlinarith
  have hN : ā * k < 4 * b * β * γp := lt_of_le_of_lt (le_max_left _ _) h2
  have hag : γp * k ≤ ā := by
    have i1 : Integrable M.a M.P := M.a_L2.integrable (by norm_num)
    have i2 : Integrable M.k M.P := M.k_L2.integrable (by norm_num)
    have := integral_mono_ae (i2.const_mul γp) i1 (h3.mono (fun ω h => h.le))
    rw [integral_const_mul] at this
    exact this
  set g0 := gammaT0 b β γp ā k with hg0
  have hg0e : g0 = (4 * b * β * γp - ā * k) / (4 * b * β - k ^ 2) := rfl
  have hg0mem : g0 ∈ Set.Icc (0 : ℝ) γp := by
    refine ⟨?_, ?_⟩
    · rw [hg0e]; exact div_nonneg (by linarith) hD.le
    · rw [hg0e, div_le_iff₀ hD]
      nlinarith
  have hform := kk_moment_tax M b β γp w hb
  have key : ∀ γ, PiT M b β γp w γ = PiT M b β γp w g0 - (4 * b * β - k ^ 2) / (4 * b) * (γ - g0) ^ 2 := by
    intro γ
    rw [hform γ, hform g0, hg0e]
    field_simp
    ring
  have hpos : 0 < (4 * b * β - k ^ 2) / (4 * b) := div_pos hD (by linarith)
  refine ⟨⟨hg0mem, ?_⟩, ?_⟩
  · intro γ _
    show PiT M b β γp w γ ≤ PiT M b β γp w g0
    rw [key γ]
    nlinarith [mul_nonneg hpos.le (sq_nonneg (γ - g0))]
  · rintro γ ⟨hγ, hmax⟩
    have h := hmax hg0mem
    have h' : PiT M b β γp w g0 ≤ PiT M b β γp w γ := h
    rw [key γ] at h'
    have : (4 * b * β - k ^ 2) / (4 * b) * (γ - g0) ^ 2 ≤ 0 := by linarith
    have h0 : (γ - g0) ^ 2 ≤ 0 := by
      by_contra hc; push_neg at hc; nlinarith [mul_pos hpos hc]
    nlinarith [sq_nonneg (γ - g0)]

theorem kk_var_eq {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a : Ω → ℝ) (ha : MemLp a 2 P) :
    Var[a; P] = ∫ ω, a ω ^ 2 ∂P - (∫ ω, a ω ∂P) ^ 2 := by
  rw [variance_eq_sub ha]; simp [Pi.pow_apply]

theorem kk_moment_cap {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b β γp w : ℝ) (hb : 0 < b) (γ : ℝ) :
    PiC M b β γp w γ =
      ((abar M.P M.a) - γ * (kbar M.P M.k)) ^ 2 / (4 * b) +
        (sigmaD M.P M.a) ^ 2 / (4 * b) +
        (γ ^ 2 * (sigma M.P M.k) ^ 2 - 2 * γ * (rho M.P M.a M.k) *
          (sigmaD M.P M.a) * (sigma M.P M.k)) / (4 * b) -
        β * (γp - γ) ^ 2 + w * (kbar M.P M.k) := by
  haveI := M.prob
  have ha := M.a_L2
  have hk := M.k_L2
  unfold PiC
  simp_rw [kk_profit_q b w γ _ _ hb]
  have hs : sigmaD M.P M.a ^ 2 = Var[M.a; M.P] := by
    unfold sigmaD
    rw [Real.sq_sqrt (variance_nonneg _ _)]
  have hs2 : sigma M.P M.k ^ 2 = Var[M.k; M.P] := by
    unfold sigma
    rw [Real.sq_sqrt (variance_nonneg _ _)]
  have hpos : 0 < sigmaD M.P M.a * sigma M.P M.k := by
    apply mul_pos
    · unfold sigmaD; exact Real.sqrt_pos.2 M.var_a_pos
    · unfold sigma; exact Real.sqrt_pos.2 M.var_k_pos
  have hrho : rho M.P M.a M.k * sigmaD M.P M.a * sigma M.P M.k = cov[M.a, M.k; M.P] := by
    unfold rho
    rw [mul_assoc, div_mul_cancel₀ _ hpos.ne']
  have i1 : Integrable M.a M.P := ha.integrable (by norm_num)
  have i2 : Integrable M.k M.P := hk.integrable (by norm_num)
  have ia2 : Integrable (fun ω => M.a ω ^ 2) M.P := ha.integrable_sq
  have ik2 : Integrable (fun ω => M.k ω ^ 2) M.P := hk.integrable_sq
  have iak : Integrable (fun ω => M.a ω * M.k ω) M.P := ha.integrable_mul hk
  have e : ∀ ω, (M.a ω - γ * M.k ω) ^ 2 =
      M.a ω ^ 2 - 2 * γ * (M.a ω * M.k ω) + γ ^ 2 * M.k ω ^ 2 := fun ω => by ring
  have hint : ∫ ω, (M.a ω - γ * M.k ω) ^ 2 ∂M.P =
      ∫ ω, M.a ω ^ 2 ∂M.P - 2 * γ * ∫ ω, M.a ω * M.k ω ∂M.P + γ ^ 2 * ∫ ω, M.k ω ^ 2 ∂M.P := by
    simp_rw [e]
    have h3 : Integrable (fun ω => 2 * γ * (M.a ω * M.k ω)) M.P := iak.const_mul _
    have h4 : Integrable (fun ω => γ ^ 2 * M.k ω ^ 2) M.P := ik2.const_mul _
    have h34 : Integrable (fun ω => M.a ω ^ 2 - 2 * γ * (M.a ω * M.k ω)) M.P := ia2.sub h3
    rw [integral_add h34 h4, integral_sub ia2 h3, integral_const_mul, integral_const_mul]
  have hq : Integrable (fun ω => (M.a ω - γ * M.k ω) ^ 2) M.P :=
    (ha.sub (hk.const_mul γ)).integrable_sq
  have hcov : cov[M.a, M.k; M.P] = ∫ ω, M.a ω * M.k ω ∂M.P - abar M.P M.a * kbar M.P M.k := by
    rw [covariance_eq_sub ha hk]; rfl
  have hr2 : 2 * γ * rho M.P M.a M.k * sigmaD M.P M.a * sigma M.P M.k =
      2 * γ * cov[M.a, M.k; M.P] := by rw [← hrho]; ring
  rw [integral_add (hq.div_const _) (i2.const_mul w), integral_div, hint, integral_const_mul,
    hs, hs2, hr2, hcov, kk_var_eq M.P M.a ha, kk_var_eq M.P M.k hk]
  unfold abar kbar
  field_simp
  ring


theorem kk_lemma_2 {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b β γp w : ℝ) (hb : 0 < b) (hγp : 0 < γp)
    (hA : Assumption1 M b β γp) :
    OptimalCap M b β γp w (gammaC0 b β γp (abar M.P M.a) (kbar M.P M.k) (sigmaD M.P M.a) (sigma M.P M.k) (rho M.P M.a M.k)) ∧
    ∀ γ : ℝ, OptimalCap M b β γp w γ → γ = gammaC0 b β γp (abar M.P M.a) (kbar M.P M.k) (sigmaD M.P M.a) (sigma M.P M.k) (rho M.P M.a M.k) := by
  haveI := M.prob
  obtain ⟨h1, h2, h3⟩ := hA
  have hk : 0 < kbar M.P M.k := M.kbar_pos
  have hform := kk_moment_cap M b β γp w hb
  set k := kbar M.P M.k with hkdef
  set ā := abar M.P M.a with hadef
  set s := sigma M.P M.k with hsdef
  set sD := sigmaD M.P M.a with hsDdef
  set r := rho M.P M.a M.k with hrdef
  have hs2 : 0 ≤ k ^ 2 + s ^ 2 := by positivity
  have hD : 0 < 4 * b * β - k ^ 2 - s ^ 2 := by linarith
  have hN1 : ā * k < 4 * b * β * γp := lt_of_le_of_lt (le_max_left _ _) h2
  have hN2 : ā * k + r * sD * s < 4 * b * β * γp := lt_of_le_of_lt (le_max_right _ _) h2
  set D := 4 * b * β - k ^ 2 - s ^ 2 with hDdef
  set γs := (4 * b * β * γp - ā * k - r * sD * s) / D with hγs
  have hγs0 : 0 < γs := div_pos (by linarith) hD
  have hpos : 0 < D / (4 * b) := div_pos hD (by linarith)
  have key : ∀ γ, PiC M b β γp w γ = PiC M b β γp w γs - D / (4 * b) * (γ - γs) ^ 2 := by
    intro γ
    rw [hform γ, hform γs, hγs]
    field_simp
    ring
  have hcases : gammaC0 b β γp ā k sD s r =
      if ā * k + r * sD * s > (k ^ 2 + s ^ 2) * γp then γs else γp := by
    unfold gammaC0
    rfl
  rw [hcases]
  split_ifs with hc
  · -- interior case
    have hlt : γs < γp := by
      rw [hγs, div_lt_iff₀ hD]; nlinarith
    refine ⟨⟨⟨hγs0.le, hlt.le⟩, ?_⟩, ?_⟩
    · intro γ _
      show PiC M b β γp w γ ≤ PiC M b β γp w γs
      rw [key γ]
      nlinarith [mul_nonneg hpos.le (sq_nonneg (γ - γs))]
    · rintro γ ⟨hγ, hmax⟩
      have h' : PiC M b β γp w γs ≤ PiC M b β γp w γ := hmax ⟨hγs0.le, hlt.le⟩
      rw [key γ] at h'
      have h0 : (γ - γs) ^ 2 ≤ 0 := by
        by_contra hc'; push_neg at hc'; nlinarith [mul_pos hpos hc']
      nlinarith [sq_nonneg (γ - γs)]
  · -- boundary case
    push_neg at hc
    have hge : γp ≤ γs := by
      rw [hγs, le_div_iff₀ hD]; nlinarith
    refine ⟨⟨⟨hγp.le, le_refl _⟩, ?_⟩, ?_⟩
    · intro γ hγ
      show PiC M b β γp w γ ≤ PiC M b β γp w γp
      rw [key γ, key γp]
      have hγle : γ ≤ γp := hγ.2
      have : (γp - γs) ^ 2 ≤ (γ - γs) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this hpos.le]
    · rintro γ ⟨hγ, hmax⟩
      have h' : PiC M b β γp w γp ≤ PiC M b β γp w γ := hmax ⟨hγp.le, le_refl _⟩
      rw [key γ, key γp] at h'
      have hγle : γ ≤ γp := hγ.2
      have h4 : (γ - γs) ^ 2 ≤ (γp - γs) ^ 2 := by
        by_contra hc'; push_neg at hc'; nlinarith [mul_pos hpos (sub_pos.2 hc')]
      nlinarith


theorem solution {Ω : Type} [MeasurableSpace Ω] (M : Model Ω)
    (b β γp w : ℝ) (hb : 0 < b) (hγp : 0 < γp)
    (hA : Assumption1 M b β γp)
    (γT γC : ℝ) (hT : OptimalTax M b β γp w γT)
    (hC : OptimalCap M b β γp w γC) :
    γT < γC ↔ rho M.P M.a M.k < R0 b β γp (abar M.P M.a) (kbar M.P M.k) (sigmaD M.P M.a) (sigma M.P M.k) := by
  haveI := M.prob
  have eT := (kk_lemma_1 M b β γp w hb hγp hA).2 γT hT
  have eC := (kk_lemma_2 M b β γp w hb hγp hA).2 γC hC
  rw [eT, eC]
  obtain ⟨h1, h2, h3⟩ := hA
  have hk : 0 < kbar M.P M.k := M.kbar_pos
  have hsD : 0 < sigmaD M.P M.a := by unfold sigmaD; exact Real.sqrt_pos.2 M.var_a_pos
  have hs : 0 < sigma M.P M.k := by unfold sigma; exact Real.sqrt_pos.2 M.var_k_pos
  have hag : γp * kbar M.P M.k < abar M.P M.a := by
    have i1 : Integrable M.a M.P := M.a_L2.integrable (by norm_num)
    have i2 : Integrable M.k M.P := M.k_L2.integrable (by norm_num)
    have hpos : 0 < ∫ ω, (M.a ω - γp * M.k ω) ∂M.P := by
      rw [integral_pos_iff_support_of_nonneg_ae]
      · have : Function.support (fun ω => M.a ω - γp * M.k ω) =ᵐ[M.P] (Set.univ : Set Ω) := by
          refine Filter.eventuallyEq_set.2 ?_
          filter_upwards [h3] with ω hω
          simp only [Function.mem_support, Set.mem_univ, iff_true]
          intro h; linarith
        rw [measure_congr this]
        simp
      · filter_upwards [h3] with ω hω
        show 0 ≤ M.a ω - γp * M.k ω
        linarith
      · exact i1.sub (i2.const_mul γp)
    rw [integral_sub i1 (i2.const_mul γp), integral_const_mul] at hpos
    unfold abar kbar
    linarith
  have hk0 := hk
  have hs2 : 0 ≤ sigma M.P M.k ^ 2 := sq_nonneg _
  set k := kbar M.P M.k with hkdef
  set ā := abar M.P M.a with hadef
  set s := sigma M.P M.k with hsdef
  set sD := sigmaD M.P M.a with hsDdef
  set r := rho M.P M.a M.k with hrdef
  have hDT : 0 < 4 * b * β - k ^ 2 := by nlinarith
  have hD : 0 < 4 * b * β - k ^ 2 - s ^ 2 := by linarith
  have hN1 : ā * k < 4 * b * β * γp := lt_of_le_of_lt (le_max_left _ _) h2
  have hN2 : ā * k + r * sD * s < 4 * b * β * γp := lt_of_le_of_lt (le_max_right _ _) h2
  have hR0 : R0 b β γp ā k sD s = s / sD * ((4 * b * β * γp - ā * k) / (4 * b * β - k ^ 2)) := rfl
  have hR0' : r < R0 b β γp ā k sD s ↔ r * sD * (4 * b * β - k ^ 2) < s * (4 * b * β * γp - ā * k) := by
    rw [hR0, div_mul_div_comm, lt_div_iff₀ (by positivity)]
    constructor <;> intro h <;> nlinarith
  rw [hR0']
  have hT0 : gammaT0 b β γp ā k = (4 * b * β * γp - ā * k) / (4 * b * β - k ^ 2) := rfl
  rw [hT0]
  unfold gammaC0
  by_cases hc : ā * k + r * sD * s > (k ^ 2 + s ^ 2) * γp
  · rw [if_pos hc, div_lt_div_iff₀ hDT hD]
    constructor
    · intro h
      have : r * sD * s * (4 * b * β - k ^ 2) < s * (s * (4 * b * β * γp - ā * k)) := by nlinarith
      by_contra hcon
      push_neg at hcon
      nlinarith [mul_le_mul_of_nonneg_left hcon hs.le]
    · intro h
      nlinarith [mul_lt_mul_of_pos_left h hs]
  · rw [if_neg hc]
    push_neg at hc
    have hlt : (4 * b * β * γp - ā * k) / (4 * b * β - k ^ 2) < γp := by
      rw [div_lt_iff₀ hDT]; nlinarith
    constructor
    · intro _
      have h1 : r * sD * s * (4 * b * β - k ^ 2) ≤ ((k ^ 2 + s ^ 2) * γp - ā * k) * (4 * b * β - k ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) hDT.le
      have h2' : ((k ^ 2 + s ^ 2) * γp - ā * k) * (4 * b * β - k ^ 2) - s ^ 2 * (4 * b * β * γp - ā * k)
          = k * (4 * b * β - k ^ 2 - s ^ 2) * (k * γp - ā) := by ring
      have h3' : k * (4 * b * β - k ^ 2 - s ^ 2) * (k * γp - ā) < 0 :=
        mul_neg_of_pos_of_neg (mul_pos hk hD) (by linarith)
      by_contra hcon
      push_neg at hcon
      nlinarith [mul_le_mul_of_nonneg_left hcon hs.le]
    · intro _; exact hlt
