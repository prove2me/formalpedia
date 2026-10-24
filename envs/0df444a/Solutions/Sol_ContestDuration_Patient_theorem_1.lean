-- Prove2me | solution 1 for ContestDuration.Patient.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-24T01:24:45.110455+00:00
-- url     : https://prove2.me/submissions/ee9a06dd-a076-470b-a545-e26bcf4b1b96

import Mathlib
import Definitions.Def_ContestDuration_Patient_Model

set_option autoImplicit false

open MeasureTheory Filter Topology
open CrowdContest.Pooling (cdf)

namespace ContestDurationPatientAux
open ContestDuration.Patient

lemma cdf_scaled (h : ℝ → ℝ) {α : ℝ} (hα : 0 < α) (x : ℝ) :
    cdf (scaled h α) x = cdf h (x / α) := by
  unfold cdf
  rw [← integral_indicator measurableSet_Iic, ← integral_indicator measurableSet_Iic]
  have e : (Set.Iic x).indicator (scaled h α) =
      fun t => (fun u => (Set.Iic (x / α)).indicator h u / α) (t / α) := by
    funext t
    simp only [Set.indicator, Set.mem_Iic, scaled]
    by_cases ht : t ≤ x
    · have : t / α ≤ x / α := div_le_div_of_nonneg_right ht hα.le
      simp [ht, this]
    · have : ¬ t / α ≤ x / α := by
        intro h'; exact ht ((div_le_div_iff_of_pos_right hα).1 h')
      simp [ht, this]
  rw [e, Measure.integral_comp_div (fun u => (Set.Iic (x / α)).indicator h u / α) α,
    integral_div, abs_of_pos hα, smul_eq_mul]
  field_simp

/-- The integrand of `Irank`. -/
noncomputable def Gfun (N j : ℕ) (h : ℝ → ℝ) (s : ℝ) : ℝ :=
  ((((N - j : ℕ) : ℝ) * cdf h s ^ (N - j - 1) * (1 - cdf h s) ^ (j - 1)
      - ((j - 1 : ℕ) : ℝ) * cdf h s ^ (N - j) * (1 - cdf h s) ^ (j - 2)) * h s ^ 2)

lemma Irank_eq (N j : ℕ) (h : ℝ → ℝ) :
    Irank N j h = ((N - 1).choose (j - 1) : ℝ) * ∫ s, Gfun N j h s := rfl

lemma Gfun_scaled (N j : ℕ) (h : ℝ → ℝ) {α : ℝ} (hα : 0 < α) (s : ℝ) :
    Gfun N j (scaled h α) s = Gfun N j h (s / α) / α ^ 2 := by
  simp only [Gfun, cdf_scaled h hα, scaled]
  ring

lemma Irank_scaled (N j : ℕ) (h : ℝ → ℝ) {α : ℝ} (hα : 0 < α) :
    Irank N j (scaled h α) = Irank N j h / α := by
  rw [Irank_eq, Irank_eq]
  simp only [Gfun_scaled N j h hα]
  have := Measure.integral_comp_div (fun u => Gfun N j h u / α ^ 2) α
  rw [this, integral_div, abs_of_pos hα, smul_eq_mul]
  field_simp

lemma xOf_scaled (P : Params) (h : ℝ → ℝ) {α : ℝ} (hα : 0 < α) :
    xOf P (scaled h α) = xOf P h / α := by
  unfold xOf
  simp only [Irank_scaled _ _ h hα]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

lemma tau_cont (b : ℝ) (hb : 1 < b) (θ : ℝ → ℝ) (hθ : ProductivityOK θ) :
    Continuous (fun t => θ t ^ (b / (b - 1))) :=
  hθ.1.rpow_const (fun _ => Or.inr (div_nonneg (by linarith) (by linarith)))

lemma tau_strictMonoOn (b : ℝ) (hb : 1 < b) (θ : ℝ → ℝ) (hθ : ProductivityOK θ) :
    StrictMonoOn (tau b θ) (Set.Ici 0) := by
  have hc := tau_cont b hb θ hθ
  intro x hx y hy hxy
  have hx' : (0:ℝ) ≤ x := hx
  unfold tau
  have hadd := intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := x) (c := y)
    (hc.intervalIntegrable (μ := volume) _ _) (hc.intervalIntegrable (μ := volume) _ _)
  have : 0 < ∫ t in x..y, θ t ^ (b / (b - 1)) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _)
      (fun t ht => Real.rpow_pos_of_pos (hθ.2 t (le_trans hx' ht.1.le)) _) hxy
  linarith

lemma tau_zero (b : ℝ) (θ : ℝ → ℝ) : tau b θ 0 = 0 := by
  simp [tau]

lemma tau_pos (b : ℝ) (hb : 1 < b) (θ : ℝ → ℝ) (hθ : ProductivityOK θ) {T : ℝ} (hT : 0 < T) :
    0 < tau b θ T := by
  have := tau_strictMonoOn b hb θ hθ (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hT.le) hT
  rwa [tau_zero] at this

lemma core (P : Params) (hS : P.Standing) (θ : ℝ → ℝ) (hθ : ProductivityOK θ) (h : ℝ → ℝ)
    (hx : 0 < xOf P h) (hR : RegularProfit P θ h) (Tb : ℝ) (hTb : 0 < Tb)
    (hτ : tau P.b θ Tb = Kbar P h) (hδ : P.δ < delta1 P θ h Tb) (hE : IsEquilibrium P θ h Tb) :
    ∀ T, IsOptDuration P θ h T ↔ T = Tb := by
  obtain ⟨hN, hb, hc, hF, hA, hFA, hδ0, -, -, hγsum⟩ := hS
  have hb0 : 0 < P.b := by linarith
  have hb1 : 0 < P.b - 1 := by linarith
  have hb1' : P.b - 1 ≠ 0 := hb1.ne'
  have hNpos : (0:ℝ) < P.N := by exact_mod_cast (by omega : 0 < P.N)
  have hbase_pos : 0 < P.A * xOf P h / (P.c * P.b) := by positivity
  set base := P.A * xOf P h / (P.c * P.b) with hbase
  set K := base ^ (1 / (P.b - 1)) with hK
  have hKpos : 0 < K := Real.rpow_pos_of_pos hbase_pos _
  have heff : ∀ T, effort P θ h T = K * tau P.b θ T := fun T => rfl
  have hsumA : ∑ j ∈ Finset.Icc 1 P.N, P.γ j * P.A = P.A := by
    rw [← Finset.sum_mul, hγsum, one_mul]
  have hKb : K ^ P.b * base ^ (-(P.b / (P.b - 1))) = 1 := by
    rw [hK, ← Real.rpow_mul hbase_pos.le, ← Real.rpow_add hbase_pos]
    have : 1 / (P.b - 1) * P.b + -(P.b / (P.b - 1)) = 0 := by field_simp; ring
    rw [this, Real.rpow_zero]
  have hKbar : Kbar P h = (P.A - P.N * P.F) / (P.c * P.N) * base ^ (-(P.b / (P.b - 1))) := rfl
  have hMK : P.c * K ^ P.b * Kbar P h = P.A / P.N - P.F := by
    rw [hKbar]
    calc P.c * K ^ P.b * ((P.A - P.N * P.F) / (P.c * P.N) * base ^ (-(P.b / (P.b - 1))))
        = (P.A - P.N * P.F) / P.N * (K ^ P.b * base ^ (-(P.b / (P.b - 1)))) := by
          field_simp
      _ = _ := by rw [hKb]; field_simp
  have hMpos : 0 < P.c * K ^ P.b := mul_pos hc (Real.rpow_pos_of_pos hKpos _)
  have hpsi : ∀ T, 0 < T → psi P θ (effort P θ h T) T = P.c * K ^ P.b * tau P.b θ T := by
    intro T hT
    have ht := tau_pos P.b hb θ hθ hT
    unfold psi
    rw [heff, Real.mul_rpow hKpos.le ht.le]
    rw [show P.c * (K ^ P.b * tau P.b θ T ^ P.b) * tau P.b θ T ^ (1 - P.b)
        = P.c * K ^ P.b * (tau P.b θ T ^ P.b * tau P.b θ T ^ (1 - P.b)) by ring,
      ← Real.rpow_add ht, show P.b + (1 - P.b) = 1 by ring, Real.rpow_one]
  have hpart : ∀ T, 0 < T → (Participates P θ h T ↔ tau P.b θ T ≤ Kbar P h) := by
    intro T hT
    unfold Participates
    rw [hsumA, hpsi T hT]
    have e1 : 1 / (P.N : ℝ) * P.A = P.A / P.N := by ring
    rw [e1]
    constructor
    · intro h0
      exact le_of_mul_le_mul_left (by linarith) hMpos
    · intro h0
      nlinarith [mul_le_mul_of_nonneg_left h0 hMpos.le]
  -- delta1 and the derivative of profit at Tb
  have hKK : K * Kbar P h = P.b * (P.A - P.N * P.F) / (P.N * xOf P h * P.A) := by
    have e : K * base ^ (-(P.b / (P.b - 1))) = base⁻¹ := by
      rw [hK, ← Real.rpow_add hbase_pos,
        show 1 / (P.b - 1) + -(P.b / (P.b - 1)) = -1 by field_simp; ring, Real.rpow_neg_one]
    rw [hKbar]
    calc K * ((P.A - P.N * P.F) / (P.c * P.N) * base ^ (-(P.b / (P.b - 1))))
        = (P.A - P.N * P.F) / (P.c * P.N) * (K * base ^ (-(P.b / (P.b - 1)))) := by ring
      _ = _ := by
        rw [e, hbase]
        field_simp
  set E := CrowdContest.Pooling.expMax h P.N with hEdef
  set r := P.b / (P.b - 1) with hr
  have hrpos : 0 < r := div_pos hb0 hb1
  have hd1 : delta1 P θ h Tb = θ Tb ^ r * K / (K * Kbar P h + E) := by
    rw [hKK]; rfl
  have hnum : 0 < θ Tb ^ r * K := mul_pos (Real.rpow_pos_of_pos (hθ.2 Tb hTb.le) _) hKpos
  have hD : 0 < K * Kbar P h + E := by
    by_contra hneg
    push Not at hneg
    have : delta1 P θ h Tb ≤ 0 := by
      rw [hd1]; exact div_nonpos_of_nonneg_of_nonpos hnum.le hneg
    linarith
  have hlt : P.δ * (K * Kbar P h + E) < θ Tb ^ r * K := by
    rw [hd1] at hδ
    exact (lt_div_iff₀ hD).1 hδ
  have htau' : HasDerivAt (tau P.b θ) (θ Tb ^ r) Tb :=
    ((tau_cont P.b hb θ hθ).integral_hasStrictDerivAt 0 Tb).hasDerivAt
  have hp := ((((hasDerivAt_id' Tb).const_mul (-P.δ)).exp).mul
    ((htau'.const_mul K).add_const E)).sub_const (∑ j ∈ Finset.Icc 1 P.N, P.γ j * P.A)
  have hp' : HasDerivAt (profit P θ h) _ Tb := hp
  have hdpos : 0 < Real.exp (-P.δ * Tb) * (-P.δ * 1) * (K * tau P.b θ Tb + E) +
      Real.exp (-P.δ * Tb) * (K * θ Tb ^ r) := by
    rw [hτ]
    have key : Real.exp (-P.δ * Tb) * (-P.δ * 1) * (K * Kbar P h + E) +
        Real.exp (-P.δ * Tb) * (K * θ Tb ^ r) =
        Real.exp (-P.δ * Tb) * (θ Tb ^ r * K - P.δ * (K * Kbar P h + E)) := by ring
    rw [key]
    exact mul_pos (Real.exp_pos _) (sub_pos.2 hlt)
  have hmono : StrictMonoOn (profit P θ h) (Set.Icc 0 Tb) := by
    rcases hR.1 with hinc | ⟨m, -, hinc, hdec⟩
    · exact hinc.mono Set.Icc_subset_Ici_self
    · by_cases hTm : Tb ≤ m
      · exact hinc.mono (Set.Icc_subset_Icc_right hTm)
      · exfalso
        push Not at hTm
        have hlim := hp'.tendsto_slope_zero_right
        have hle : Real.exp (-P.δ * Tb) * (-P.δ * 1) * (K * tau P.b θ Tb + E) +
            Real.exp (-P.δ * Tb) * (K * θ Tb ^ r) ≤ 0 := by
          apply le_of_tendsto hlim
          filter_upwards [self_mem_nhdsWithin] with t ht
          have ht' : (0:ℝ) < t := ht
          have : profit P θ h (Tb + t) < profit P θ h Tb :=
            hdec (Set.mem_Ici.2 hTm.le) (Set.mem_Ici.2 (by linarith)) (by linarith)
          rw [smul_eq_mul]
          exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 ht'.le) (by linarith)
        linarith
  have hsm := tau_strictMonoOn P.b hb θ hθ
  have hPartTb : Participates P θ h Tb := (hpart Tb hTb).2 (le_of_eq hτ)
  have hle_Tb : ∀ T, 0 < T → Participates P θ h T → T ≤ Tb := by
    intro T hT hP
    have h1 := (hpart T hT).1 hP
    rw [← hτ] at h1
    exact (hsm.le_iff_le (Set.mem_Ici.2 hT.le) (Set.mem_Ici.2 hTb.le)).1 h1
  intro T
  constructor
  · rintro ⟨hT0, hEq, hP, hmax⟩
    have hTle := hle_Tb T hT0 hP
    have hge := hmax Tb hTb hE hPartTb
    rcases lt_or_eq_of_le hTle with hlt' | heq
    · exfalso
      have := hmono ⟨hT0.le, hTle⟩ ⟨hTb.le, le_rfl⟩ hlt'
      linarith
    · exact heq
  · rintro rfl
    refine ⟨hTb, hE, hPartTb, fun T' hT' _ hP' => ?_⟩
    exact hmono.monotoneOn ⟨hT'.le, hle_Tb T' hT' hP'⟩ ⟨hTb.le, le_rfl⟩ (hle_Tb T' hT' hP')

lemma exists_unique_opt (P : Params) (hS : P.Standing) (θ : ℝ → ℝ) (hθ : ProductivityOK θ)
    (h : ℝ → ℝ) (hx : 0 < xOf P h) (hR : RegularProfit P θ h) (hPat : IsPatient P θ h) :
    ∃! T, IsOptDuration P θ h T := by
  obtain ⟨Tb, hTb, hτ, hδ, hE⟩ := hPat
  have hc := core P hS θ hθ h hx hR Tb hTb hτ hδ hE
  exact ⟨Tb, (hc Tb).2 rfl, fun T hT => (hc T).1 hT⟩

lemma opt_tau (P : Params) (hS : P.Standing) (θ : ℝ → ℝ) (hθ : ProductivityOK θ)
    (h : ℝ → ℝ) (hx : 0 < xOf P h) (hR : RegularProfit P θ h) (hPat : IsPatient P θ h)
    (T : ℝ) (hT : IsOptDuration P θ h T) : tau P.b θ T = Kbar P h := by
  obtain ⟨Tb, hTb, hτ, hδ, hE⟩ := hPat
  rw [(core P hS θ hθ h hx hR Tb hTb hτ hδ hE T).1 hT]
  exact hτ

lemma exp_ok (ρ : ℝ) : ProductivityOK (fun t => Real.exp (ρ * t)) :=
  ⟨by fun_prop, fun _ _ => Real.exp_pos _⟩

end ContestDurationPatientAux

open ContestDurationPatientAux in
open ContestDuration.Patient in
theorem solution (P : Params) (hS : P.Standing) (h : ℝ → ℝ)
    (hh : ShockOK h) (hx : 0 < xOf P h) :
    (∀ θ : ℝ → ℝ, ProductivityOK θ →
      (∀ α, 0 < α → RegularProfit P θ (scaled h α) →
        IsPatient P θ (scaled h α) → ∃! T, IsOptDuration P θ (scaled h α) T) ∧
      (∀ α₁ α₂ T₁ T₂, 0 < α₁ → α₁ < α₂ →
        RegularProfit P θ (scaled h α₁) → IsPatient P θ (scaled h α₁) →
        RegularProfit P θ (scaled h α₂) → IsPatient P θ (scaled h α₂) →
        IsOptDuration P θ (scaled h α₁) T₁ →
        IsOptDuration P θ (scaled h α₂) T₂ → T₁ < T₂)) ∧
    ((∀ ρ, RegularProfit P (fun t => Real.exp (ρ * t)) h →
      IsPatient P (fun t => Real.exp (ρ * t)) h →
      ∃! T, IsOptDuration P (fun t => Real.exp (ρ * t)) h T) ∧
    (∀ ρ₁ ρ₂ T₁ T₂, ρ₁ < ρ₂ →
      RegularProfit P (fun t => Real.exp (ρ₁ * t)) h →
      IsPatient P (fun t => Real.exp (ρ₁ * t)) h →
      RegularProfit P (fun t => Real.exp (ρ₂ * t)) h →
      IsPatient P (fun t => Real.exp (ρ₂ * t)) h →
      IsOptDuration P (fun t => Real.exp (ρ₁ * t)) h T₁ →
      IsOptDuration P (fun t => Real.exp (ρ₂ * t)) h T₂ → T₂ < T₁)) := by
  have hb : 1 < P.b := hS.2.1
  have hxs : ∀ α, 0 < α → 0 < xOf P (scaled h α) := fun α hα => by
    rw [xOf_scaled P h hα]; exact div_pos hx hα
  refine ⟨fun θ hθ => ⟨fun α hα hR hP => exists_unique_opt P hS θ hθ _ (hxs α hα) hR hP, ?_⟩,
    fun ρ hR hP => exists_unique_opt P hS _ (exp_ok ρ) h hx hR hP, ?_⟩
  · intro α₁ α₂ T₁ T₂ hα₁ hlt hR₁ hP₁ hR₂ hP₂ hT₁ hT₂
    have hα₂ : 0 < α₂ := lt_trans hα₁ hlt
    have e₁ := opt_tau P hS θ hθ _ (hxs α₁ hα₁) hR₁ hP₁ T₁ hT₁
    have e₂ := opt_tau P hS θ hθ _ (hxs α₂ hα₂) hR₂ hP₂ T₂ hT₂
    obtain ⟨hN, -, hc, hF, hA, hFA, -⟩ := hS
    have hNpos : (0:ℝ) < P.N := by exact_mod_cast (by omega : 0 < P.N)
    have hb0 : 0 < P.b := by linarith
    have hK : Kbar P (scaled h α₁) < Kbar P (scaled h α₂) := by
      unfold Kbar
      rw [xOf_scaled P h hα₁, xOf_scaled P h hα₂]
      have hC : 0 < (P.A - P.N * P.F) / (P.c * P.N) := by
        apply div_pos _ (by positivity)
        have := (lt_div_iff₀ hNpos).1 hFA
        linarith
      apply mul_lt_mul_of_pos_left _ hC
      apply Real.rpow_lt_rpow_of_neg
      · have := div_pos hx hα₂; positivity
      · apply div_lt_div_of_pos_right _ (by positivity)
        exact mul_lt_mul_of_pos_left (div_lt_div_of_pos_left hx hα₁ hlt) hA
      · have : 0 < P.b / (P.b - 1) := div_pos hb0 (by linarith)
        linarith
    by_contra hcon
    push Not at hcon
    have hsm := tau_strictMonoOn P.b hb θ hθ
    have := hsm.monotoneOn (Set.mem_Ici.2 hT₂.1.le) (Set.mem_Ici.2 hT₁.1.le) hcon
    linarith
  · intro ρ₁ ρ₂ T₁ T₂ hlt hR₁ hP₁ hR₂ hP₂ hT₁ hT₂
    have e₁ := opt_tau P hS _ (exp_ok ρ₁) h hx hR₁ hP₁ T₁ hT₁
    have e₂ := opt_tau P hS _ (exp_ok ρ₂) h hx hR₂ hP₂ T₂ hT₂
    have hr : 0 < P.b / (P.b - 1) := div_pos (by linarith) (by linarith)
    have hT₁0 : 0 < T₁ := hT₁.1
    have hstrict : tau P.b (fun t => Real.exp (ρ₁ * t)) T₁ <
        tau P.b (fun t => Real.exp (ρ₂ * t)) T₁ := by
      have hc₁ := tau_cont P.b hb _ (exp_ok ρ₁)
      have hc₂ := tau_cont P.b hb _ (exp_ok ρ₂)
      have hpos : 0 < ∫ t in (0:ℝ)..T₁,
          (Real.exp (ρ₂ * t) ^ (P.b / (P.b - 1)) - Real.exp (ρ₁ * t) ^ (P.b / (P.b - 1))) := by
        apply intervalIntegral.intervalIntegral_pos_of_pos_on
          ((hc₂.sub hc₁).intervalIntegrable _ _) _ hT₁0
        intro t ht
        simp only [Pi.sub_apply]
        rw [← Real.exp_mul, ← Real.exp_mul]
        apply sub_pos.2 (Real.exp_lt_exp.2 _)
        have := mul_pos (mul_pos (sub_pos.2 hlt) ht.1) hr
        nlinarith
      rw [intervalIntegral.integral_sub (hc₂.intervalIntegrable _ _)
        (hc₁.intervalIntegrable _ _)] at hpos
      unfold tau
      linarith
    by_contra hcon
    push Not at hcon
    have hsm := tau_strictMonoOn P.b hb _ (exp_ok ρ₂)
    have := hsm.monotoneOn (Set.mem_Ici.2 hT₁0.le) (Set.mem_Ici.2 hT₂.1.le) hcon
    linarith
