-- Prove2me | solution 1 for BOPDistrib.Misalign.corollary_1_proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T08:44:37.563931+00:00
-- url     : https://prove2.me/submissions/285e2351-4948-4fc0-bca7-d0f7d755fc76

import Mathlib
import Definitions.Def_BOPDistrib_Misalign_Model

open BOPDistrib.Misalign

namespace BOPCor1Sol

/-- A property of the risk aversion that is upward closed on `(0,∞)` and closed from the right. -/
def Good (S : ℝ → Prop) : Prop :=
  (∀ a b : ℝ, 0 < a → a ≤ b → S a → S b) ∧ (∀ a : ℝ, 0 < a → (∀ b, a < b → S b) → S a)

lemma good_congr {S T : ℝ → Prop} (h : ∀ α, 0 < α → (S α ↔ T α)) (hS : Good S) : Good T := by
  refine ⟨fun a b ha hab hT => ?_, fun a ha hT => ?_⟩
  · have hb : 0 < b := lt_of_lt_of_le ha hab
    exact (h b hb).1 (hS.1 a b ha hab ((h a ha).2 hT))
  · exact (h a ha).1 (hS.2 a ha fun b hb => (h b (ha.trans hb)).2 (hT b hb))

lemma good_const (p : Prop) : Good (fun _ => p) :=
  ⟨fun _ _ _ _ h => h, fun a _ h => h (a + 1) (by linarith)⟩

lemma good_and {S T : ℝ → Prop} (hS : Good S) (hT : Good T) : Good (fun α => S α ∧ T α) :=
  ⟨fun a b ha hab h => ⟨hS.1 a b ha hab h.1, hT.1 a b ha hab h.2⟩,
   fun a ha h => ⟨hS.2 a ha fun b hb => (h b hb).1, hT.2 a ha fun b hb => (h b hb).2⟩⟩

lemma good_or {S T : ℝ → Prop} (hS : Good S) (hT : Good T) : Good (fun α => S α ∨ T α) := by
  refine ⟨fun a b ha hab h => h.imp (hS.1 a b ha hab) (hT.1 a b ha hab), fun a ha h => ?_⟩
  by_contra hn
  push Not at hn
  obtain ⟨hSa, hTa⟩ := hn
  have hex : ∃ b, a < b ∧ ¬ S b := by
    by_contra h'
    push Not at h'
    exact hSa (hS.2 a ha h')
  obtain ⟨b, hab, hSb⟩ := hex
  apply hTa
  apply hT.2 a ha
  intro c hc
  rcases le_total c b with hcb | hbc
  · rcases h c hc with h1 | h1
    · exact absurd (hS.1 c b (ha.trans hc) hcb h1) hSb
    · exact h1
  · rcases h b hab with h1 | h1
    · exact absurd h1 hSb
    · exact hT.1 b c (ha.trans hab) hbc h1

lemma threshold {S : ℝ → Prop} (hS : Good S) :
    ∃ t : ENNReal, ∀ α : ℝ, 0 < α → (S α ↔ t ≤ ENNReal.ofReal α) := by
  refine ⟨⨅ (a : ℝ) (_ : 0 < a ∧ S a), ENNReal.ofReal a,
    fun α hα => ⟨fun h => iInf₂_le α ⟨hα, h⟩, fun h => ?_⟩⟩
  apply hS.2 α hα
  intro b hb
  have hb0 : 0 < b := hα.trans hb
  have hlt : (⨅ (a : ℝ) (_ : 0 < a ∧ S a), ENNReal.ofReal a) < ENNReal.ofReal b :=
    lt_of_le_of_lt h ((ENNReal.ofReal_lt_ofReal_iff hb0).2 hb)
  rw [iInf_lt_iff] at hlt
  obtain ⟨a, ha⟩ := hlt
  rw [iInf_lt_iff] at ha
  obtain ⟨⟨ha0, hSa⟩, hab⟩ := ha
  have : a < b := (ENNReal.ofReal_lt_ofReal_iff hb0).1 hab
  exact hS.1 a b ha0 this.le hSa

lemma good_affine {f : ℝ → ℝ} (hanti : ∀ a b, 0 < a → a ≤ b → f b ≤ f a)
    (hcont : ∀ a, 0 < a → ContinuousAt f a) (A B c : ℝ) (hB : 0 ≤ B) :
    Good (fun α => A + B * f α ≤ c) := by
  refine ⟨fun a b ha hab h => ?_, fun a ha h => ?_⟩
  · have := hanti a b ha hab
    nlinarith [mul_le_mul_of_nonneg_left this hB]
  · have ht : Filter.Tendsto (fun α => A + B * f α) (nhdsWithin a (Set.Ioi a))
        (nhds (A + B * f a)) :=
      ((continuousAt_const.add (continuousAt_const.mul (hcont a ha))).tendsto).mono_left
        nhdsWithin_le_nhds
    exact le_of_tendsto ht (eventually_nhdsWithin_of_forall fun b hb => h b hb)

/-! ### The log term -/

section LogTerm

variable (P : Params) (m : ℝ)

lemma arg_pos (hβ0 : 0 < P.β) (hβ1 : P.β < 1) (hd : 0 < P.vh - m) {α : ℝ} (hα : 0 < α) :
    0 < 1 - P.β * Real.exp (-α * (P.vh - m)) := by
  have : Real.exp (-α * (P.vh - m)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  nlinarith

lemma logTerm_pos (hβ0 : 0 < P.β) (hβ1 : P.β < 1) (hd : 0 < P.vh - m) {α : ℝ} (hα : 0 < α) :
    0 < logTerm P m α := by
  unfold logTerm
  have he : Real.exp (-α * (P.vh - m)) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have h1 : 1 < (1 - P.β * Real.exp (-α * (P.vh - m))) / (1 - P.β) := by
    rw [one_lt_div (by linarith)]
    nlinarith
  exact mul_pos (by positivity) (Real.log_pos h1)

lemma logTerm_le (hβ0 : 0 < P.β) (hβ1 : P.β < 1) (hd : 0 < P.vh - m) {α : ℝ} (hα : 0 < α) :
    logTerm P m α * (1 - P.β) ≤ P.β * (P.vh - m) := by
  unfold logTerm
  have hZ := arg_pos P m hβ0 hβ1 hd hα
  have hx : 0 < (1 - P.β * Real.exp (-α * (P.vh - m))) / (1 - P.β) := div_pos hZ (by linarith)
  have hlog := Real.log_le_sub_one_of_pos hx
  have hexp := Real.add_one_le_exp (-α * (P.vh - m))
  have h1 : Real.log ((1 - P.β * Real.exp (-α * (P.vh - m))) / (1 - P.β)) * (1 - P.β) ≤
      P.β * α * (P.vh - m) := by
    have e : ((1 - P.β * Real.exp (-α * (P.vh - m))) / (1 - P.β) - 1) * (1 - P.β) =
        P.β * (1 - Real.exp (-α * (P.vh - m))) := by
      have hne : (1 - P.β) ≠ 0 := (by linarith : (0:ℝ) < 1 - P.β).ne'
      rw [div_sub_one hne, div_mul_cancel₀ _ hne]
      ring
    have := mul_le_mul_of_nonneg_right hlog (by linarith : (0:ℝ) ≤ 1 - P.β)
    rw [e] at this
    nlinarith
  rw [show 1 / α * Real.log ((1 - P.β * Real.exp (-α * (P.vh - m))) / (1 - P.β)) * (1 - P.β) =
      (Real.log ((1 - P.β * Real.exp (-α * (P.vh - m))) / (1 - P.β)) * (1 - P.β)) / α by ring,
    div_le_iff₀ hα]
  linarith

lemma logTerm_anti (hβ0 : 0 < P.β) (hβ1 : P.β < 1) (hd : 0 < P.vh - m) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) : logTerm P m b ≤ logTerm P m a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hX := arg_pos P m hβ0 hβ1 hd hb
  have hZ := arg_pos P m hβ0 hβ1 hd ha
  have hY : 0 < 1 - P.β := by linarith
  obtain ⟨lam, hlam⟩ : ∃ lam, lam = a / b := ⟨_, rfl⟩
  have hl0 : 0 < lam := by rw [hlam]; positivity
  have hl1 : lam ≤ 1 := by rw [hlam]; exact (div_le_one hb).2 hab
  have hexp : Real.exp (-a * (P.vh - m)) ≤ lam * Real.exp (-b * (P.vh - m)) + (1 - lam) := by
    have := convexOn_exp.2 (Set.mem_univ (-b * (P.vh - m))) (Set.mem_univ 0) hl0.le
      (by linarith : 0 ≤ 1 - lam) (by ring)
    have e : lam • (-b * (P.vh - m)) + (1 - lam) • (0:ℝ) = -a * (P.vh - m) := by
      rw [hlam, smul_eq_mul, smul_eq_mul]
      field_simp
      ring
    rw [e, smul_eq_mul, smul_eq_mul, Real.exp_zero, mul_one] at this
    exact this
  have hZge : lam * (1 - P.β * Real.exp (-b * (P.vh - m))) + (1 - lam) * (1 - P.β) ≤
      1 - P.β * Real.exp (-a * (P.vh - m)) := by nlinarith
  have hpos : 0 < lam * (1 - P.β * Real.exp (-b * (P.vh - m))) + (1 - lam) * (1 - P.β) := by
    have := mul_pos hl0 hX
    have := mul_nonneg (sub_nonneg.2 hl1) hY.le
    linarith
  have hconc := (strictConcaveOn_log_Ioi.concaveOn).2 (Set.mem_Ioi.2 hX) (Set.mem_Ioi.2 hY)
    hl0.le (by linarith : 0 ≤ 1 - lam) (by ring)
  simp only [smul_eq_mul] at hconc
  have hmono := Real.log_le_log hpos hZge
  unfold logTerm
  rw [Real.log_div hX.ne' hY.ne', Real.log_div hZ.ne' hY.ne']
  have key : lam * (Real.log (1 - P.β * Real.exp (-b * (P.vh - m))) - Real.log (1 - P.β)) ≤
      Real.log (1 - P.β * Real.exp (-a * (P.vh - m))) - Real.log (1 - P.β) := by linarith
  have e2 : 1 / b * (Real.log (1 - P.β * Real.exp (-b * (P.vh - m))) - Real.log (1 - P.β)) =
      1 / a * (lam * (Real.log (1 - P.β * Real.exp (-b * (P.vh - m))) - Real.log (1 - P.β))) := by
    rw [hlam]
    field_simp
  rw [e2]
  exact mul_le_mul_of_nonneg_left key (by positivity)

lemma logTerm_cont (hβ0 : 0 < P.β) (hβ1 : P.β < 1) (hd : 0 < P.vh - m) {α : ℝ} (hα : 0 < α) :
    ContinuousAt (fun t => logTerm P m t) α := by
  unfold logTerm
  apply ContinuousAt.mul
  · exact continuousAt_const.div continuousAt_id hα.ne'
  · apply ContinuousAt.log
    · fun_prop
    · exact (div_pos (arg_pos P m hβ0 hβ1 hd hα) (by linarith)).ne'

/-- `q(α) = m − r_α(m)`. -/
noncomputable def qf (α : ℝ) : ℝ := m - refund P m α

lemma qf_eq (α : ℝ) : qf P m α = min m (logTerm P m α) := by
  unfold qf refund
  rcases le_total 0 (m - logTerm P m α) with h | h
  · rw [max_eq_right h, min_eq_right (by linarith)]; ring
  · rw [max_eq_left h, min_eq_left (by linarith)]; ring

lemma qf_nonneg (hβ0 : 0 < P.β) (hβ1 : P.β < 1) (hd : 0 < P.vh - m) (hm : 0 ≤ m) {α : ℝ}
    (hα : 0 < α) : 0 ≤ qf P m α := by
  rw [qf_eq]
  exact le_min hm (logTerm_pos P m hβ0 hβ1 hd hα).le

lemma qf_le (hβ0 : 0 < P.β) (hβ1 : P.β < 1) (hd : 0 < P.vh - m) {α : ℝ}
    (hα : 0 < α) : qf P m α * (1 - P.β) ≤ P.β * (P.vh - m) := by
  have h1 : qf P m α ≤ logTerm P m α := by rw [qf_eq]; exact min_le_right _ _
  have := logTerm_le P m hβ0 hβ1 hd hα
  nlinarith

lemma qf_anti (hβ0 : 0 < P.β) (hβ1 : P.β < 1) (hd : 0 < P.vh - m) :
    ∀ a b, 0 < a → a ≤ b → qf P m b ≤ qf P m a := by
  intro a b ha hab
  rw [qf_eq, qf_eq]
  exact min_le_min le_rfl (logTerm_anti P m hβ0 hβ1 hd ha hab)

lemma qf_cont (hβ0 : 0 < P.β) (hβ1 : P.β < 1) (hd : 0 < P.vh - m) :
    ∀ a, 0 < a → ContinuousAt (qf P m) a := by
  intro a ha
  have : qf P m = fun t => min m (logTerm P m t) := funext (qf_eq P m)
  rw [this]
  exact continuousAt_const.min (logTerm_cont P m hβ0 hβ1 hd ha)

end LogTerm

/-! ### Allocations -/

section Alloc

variable (P : Params) (m : ℝ)

/-- The education level of FR when the indicator `1{y ≤ y_θ}` is on. -/
noncomputable def th1 : ℝ :=
  P.θ0 + max 0 (P.b - (P.vh - m) * (P.β + (1 - P.θ0) * (1 - P.β))) *
    invPP (P.cθ - (P.vh - m) * (1 - P.β))

lemma thetaFR_eq (α : ℝ) : thetaFR P m α = if P.y ≤ yθ P m α then th1 P m else P.θ0 := by
  unfold thetaFR th1; split_ifs <;> ring

lemma yθ_eq (α : ℝ) : yθ P m α = P.w - (1 - P.γ) * qf P m α - (P.vh - m) := rfl

lemma CSB_eq (α θ : ℝ) : CSB P m α θ = (P.vh - m) * P.β - qf P m α * (1 - θ) * (1 - P.β) := rfl

lemma PiA_eq (x θ : ℝ) :
    PiA P m x θ = ((1 - P.γ) * m + P.γ * P.vh - P.w) * P.β * θ + x * θ * P.β := by
  unfold PiA BOPDistrib.Misalign.CSA; ring

lemma PiB_lin (α x θ : ℝ) :
    PiB P m α x θ = (x * (P.β + (1 - θ) * (1 - P.β)) + ((1 - P.γ) * m + P.γ * P.vh - P.w) * P.β
      + (1 - P.β) * (1 - θ) * (P.y - P.w)) + ((1 - P.β) * (1 - θ) * (1 - P.γ)) * qf P m α := by
  unfold PiB CSB qf; ring

lemma thetaM_facts (hS : Standing P m) :
    P.θ0 < thetaM P ∧ thetaM P ≤ 1 ∧ P.cθ * (thetaM P - P.θ0) + xM P * thetaM P * P.β = P.b ∧
    xM P * (P.β + (1 - thetaM P) * (1 - P.β)) = xM P * thetaM P * P.β := by
  obtain ⟨hvh, hβ0, hβ1, hm0, hwm, hmv, hγ0, hγ1, hθ0, hθ1, hc, hb0, hA⟩ := hS
  unfold thetaM xM
  rcases le_or_gt P.b (P.cθ * (1 - P.θ0)) with h | h
  · have h1 : P.θ0 + P.b / P.cθ ≤ 1 := by
      have : P.b / P.cθ ≤ 1 - P.θ0 := by rw [div_le_iff₀ hc]; linarith
      linarith
    rw [min_eq_right h1, max_eq_left (by linarith)]
    refine ⟨by have := div_pos hb0 hc; linarith, h1, ?_, by simp⟩
    field_simp
    ring
  · have h1 : 1 ≤ P.θ0 + P.b / P.cθ := by
      have : 1 - P.θ0 ≤ P.b / P.cθ := by rw [le_div_iff₀ hc]; linarith
      linarith
    rw [min_eq_left h1, max_eq_right (by linarith)]
    refine ⟨by linarith, le_rfl, ?_, by ring⟩
    field_simp
    ring

lemma thetaF_facts (hS : Standing P m) :
    P.θ0 ≤ thetaF P m ∧ thetaF P m < thetaM P ∧
    P.cθ * (thetaF P m - P.θ0) + xF P m * thetaF P m * P.β = P.b := by
  have hM := thetaM_facts P m hS
  obtain ⟨hvh, hβ0, hβ1, hm0, hwm, hmv, hγ0, hγ1, hθ0, hθ1, hc, hb0, hA⟩ := hS
  have hd : 0 < P.vh - m := by linarith
  have hθβ : 0 < P.θ0 * P.β := mul_pos hθ0 hβ0
  unfold thetaF xF
  rcases le_or_gt P.b (P.θ0 * P.β * (P.vh - m)) with h | h
  · rw [max_eq_left (by linarith), min_eq_right ?_]
    · simp only [zero_div, add_zero, sub_self, mul_zero, zero_add]
      refine ⟨le_rfl, hM.1, ?_⟩
      field_simp
    · rw [div_le_iff₀ hθβ]; linarith
  · rw [max_eq_right (by linarith), min_eq_left ?_]
    · have hden : 0 < P.cθ + P.β * (P.vh - m) := by positivity
      have hnn := div_nonneg (by linarith : (0:ℝ) ≤ P.b - P.θ0 * P.β * (P.vh - m)) hden.le
      refine ⟨by linarith, ?_, ?_⟩
      · unfold thetaM
        apply lt_min
        · have : (P.b - P.θ0 * P.β * (P.vh - m)) / (P.cθ + P.β * (P.vh - m)) < 1 - P.θ0 := by
            rw [div_lt_iff₀ hden]; nlinarith
          linarith
        · have : (P.b - P.θ0 * P.β * (P.vh - m)) / (P.cθ + P.β * (P.vh - m)) < P.b / P.cθ := by
            rw [div_lt_div_iff₀ hden hc]; nlinarith [mul_pos hθβ hd, mul_pos hb0 (mul_pos hβ0 hd)]
          linarith
      · field_simp
        ring
    · rw [le_div_iff₀ hθβ]; linarith

lemma th1_facts (hS : Standing P m) :
    P.θ0 ≤ th1 P m ∧ th1 P m ≤ 1 ∧ th1 P m ≤ thetaM P ∧
    (th1 P m - P.θ0) * xFR P m = (th1 P m - P.θ0) * (P.vh - m) ∧
    P.cθ * (th1 P m - P.θ0) + xFR P m * (P.β + (1 - th1 P m) * (1 - P.β)) ≤ P.b ∧
    xFR P m * (P.β + (1 - P.θ0) * (1 - P.β)) ≤ P.b := by
  have hM := thetaM_facts P m hS
  obtain ⟨hvh, hβ0, hβ1, hm0, hwm, hmv, hγ0, hγ1, hθ0, hθ1, hc, hb0, hA⟩ := hS
  have hd : 0 < P.vh - m := by linarith
  have hD0 : 0 < P.β + (1 - P.θ0) * (1 - P.β) := by nlinarith
  have hxD : xFR P m * (P.β + (1 - P.θ0) * (1 - P.β)) ≤ P.b := by
    have : xFR P m ≤ P.b / (P.β + (1 - P.θ0) * (1 - P.β)) := min_le_right _ _
    rwa [le_div_iff₀ hD0] at this
  have hθM : P.θ0 ≤ thetaM P := hM.1.le
  have triv : th1 P m = P.θ0 → (P.θ0 ≤ th1 P m ∧ th1 P m ≤ 1 ∧ th1 P m ≤ thetaM P ∧
      (th1 P m - P.θ0) * xFR P m = (th1 P m - P.θ0) * (P.vh - m) ∧
      P.cθ * (th1 P m - P.θ0) + xFR P m * (P.β + (1 - th1 P m) * (1 - P.β)) ≤ P.b ∧
      xFR P m * (P.β + (1 - P.θ0) * (1 - P.β)) ≤ P.b) := by
    intro h
    rw [h]
    refine ⟨le_rfl, hθ1.le, hθM, by ring, by simpa using hxD, hxD⟩
  rcases le_or_gt (P.b - (P.vh - m) * (P.β + (1 - P.θ0) * (1 - P.β))) 0 with h1 | h1
  · apply triv; unfold th1; rw [max_eq_left h1]; ring
  rcases le_or_gt (P.cθ - (P.vh - m) * (1 - P.β)) 0 with h2 | h2
  · apply triv; unfold th1 invPP; rw [if_neg (by linarith)]; ring
  have hth : th1 P m = P.θ0 + (P.b - (P.vh - m) * (P.β + (1 - P.θ0) * (1 - P.β))) /
      (P.cθ - (P.vh - m) * (1 - P.β)) := by
    unfold th1 invPP; rw [if_pos h2, max_eq_right h1.le]; ring
  have hx : xFR P m = P.vh - m := by
    unfold xFR; apply min_eq_left; rw [le_div_iff₀ hD0]; linarith
  have hq0 : 0 ≤ (P.b - (P.vh - m) * (P.β + (1 - P.θ0) * (1 - P.β))) /
      (P.cθ - (P.vh - m) * (1 - P.β)) := div_nonneg h1.le h2.le
  have hle1 : (P.b - (P.vh - m) * (P.β + (1 - P.θ0) * (1 - P.β))) /
      (P.cθ - (P.vh - m) * (1 - P.β)) ≤ 1 - P.θ0 := by
    rw [div_le_iff₀ h2]; nlinarith
  have hle2 : (P.b - (P.vh - m) * (P.β + (1 - P.θ0) * (1 - P.β))) /
      (P.cθ - (P.vh - m) * (1 - P.β)) ≤ P.b / P.cθ := by
    rw [div_le_div_iff₀ h2 hc]
    have e1 := mul_lt_mul_of_pos_right hA (mul_pos hd (by linarith : (0:ℝ) < 1 - P.β))
    have e2 := mul_lt_mul_of_pos_left h2 (mul_pos hβ0 hd)
    nlinarith
  rw [hth, hx]
  refine ⟨by linarith, by linarith, ?_, rfl, ?_, by rw [← hx]; exact hxD⟩
  · unfold thetaM; exact le_min (by linarith) (by linarith)
  · apply le_of_eq
    field_simp
    ring

lemma PiFR_max (hS : Standing P m) (α : ℝ) :
    PiFR P m α = max (PiB P m α (xFR P m) P.θ0) (PiB P m α (xFR P m) (th1 P m)) := by
  have h1 := th1_facts P m hS
  obtain ⟨hvh, hβ0, hβ1, hm0, hwm, hmv, hγ0, hγ1, hθ0, hθ1, hc, hb0, hA⟩ := hS
  have hdiff : PiB P m α (xFR P m) (th1 P m) - PiB P m α (xFR P m) P.θ0 =
      (th1 P m - P.θ0) * (1 - P.β) * (yθ P m α - P.y) := by
    rw [PiB_lin, PiB_lin, yθ_eq]
    linear_combination (-(1 - P.β)) * h1.2.2.2.1
  unfold PiFR
  rw [thetaFR_eq]
  split_ifs with hy
  · rw [max_eq_right]
    have : 0 ≤ (th1 P m - P.θ0) * (1 - P.β) * (yθ P m α - P.y) :=
      mul_nonneg (mul_nonneg (by linarith [h1.1]) (by linarith)) (by linarith)
    linarith
  · rw [max_eq_left]
    have : (th1 P m - P.θ0) * (1 - P.β) * (yθ P m α - P.y) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith [h1.1]) (by linarith))
        (by push Not at hy; linarith)
    linarith

lemma mF_sub (hS : Standing P m) :
    ((1 - P.γ) * m + P.γ * P.vh - P.w) * P.β - P.cθ = (1 - P.γ) * P.β * (m - mF P) := by
  obtain ⟨hvh, hβ0, hβ1, hm0, hwm, hmv, hγ0, hγ1, hθ0, hθ1, hc, hb0, hA⟩ := hS
  have : (1 - P.γ) ≠ 0 := by linarith
  have : P.β ≠ 0 := hβ0.ne'
  unfold mF
  field_simp
  ring

lemma PiF_sub_PiM (hS : Standing P m) :
    PiF P m - PiM P m = (((1 - P.γ) * m + P.γ * P.vh - P.w) * P.β - P.cθ) *
      (thetaF P m - thetaM P) := by
  have hF := thetaF_facts P m hS
  have hM := thetaM_facts P m hS
  unfold PiF PiM
  rw [PiA_eq, PiA_eq]
  linear_combination hF.2.2 - hM.2.2.1


end Alloc

/-! ### Monotone atoms in α -/

section Atoms

variable (P : Params) (m : ℝ)

lemma good_PiB (hS : Standing P m) (x θ c : ℝ) (hθ : θ ≤ 1) :
    Good (fun α => PiB P m α x θ ≤ c) := by
  obtain ⟨hvh, hβ0, hβ1, hm0, hwm, hmv, hγ0, hγ1, hθ0, hθ1, hc, hb0, hA⟩ := hS
  have hd : 0 < P.vh - m := by linarith
  refine good_congr (fun α _ => by rw [PiB_lin]) (good_affine (qf_anti P m hβ0 hβ1 hd)
    (qf_cont P m hβ0 hβ1 hd) _ _ c ?_)
  exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)

lemma good_CSB (hS : Standing P m) (θ c : ℝ) (hθ : θ ≤ 1) :
    Good (fun α => c ≤ CSB P m α θ) := by
  obtain ⟨hvh, hβ0, hβ1, hm0, hwm, hmv, hγ0, hγ1, hθ0, hθ1, hc, hb0, hA⟩ := hS
  have hd : 0 < P.vh - m := by linarith
  refine good_congr (fun α _ => ?_) (good_affine (qf_anti P m hβ0 hβ1 hd)
    (qf_cont P m hβ0 hβ1 hd) (c - (P.vh - m) * P.β) ((1 - θ) * (1 - P.β)) 0 ?_)
  · rw [CSB_eq]; constructor <;> intro h <;> linarith
  · exact mul_nonneg (by linarith) (by linarith)

lemma good_yθ (hS : Standing P m) : Good (fun α => P.y ≤ yθ P m α) := by
  obtain ⟨hvh, hβ0, hβ1, hm0, hwm, hmv, hγ0, hγ1, hθ0, hθ1, hc, hb0, hA⟩ := hS
  have hd : 0 < P.vh - m := by linarith
  refine good_congr (fun α _ => ?_) (good_affine (qf_anti P m hβ0 hβ1 hd)
    (qf_cont P m hβ0 hβ1 hd) (P.y - P.w + (P.vh - m)) (1 - P.γ) 0 (by linarith))
  rw [yθ_eq]; constructor <;> intro h <;> linarith

end Atoms

section Main

variable (P : Params) (m : ℝ)

lemma CSB_mono (hS : Standing P m) {α : ℝ} (hα : 0 < α) {θ θ' : ℝ} (h : θ ≤ θ') :
    CSB P m α θ ≤ CSB P m α θ' := by
  obtain ⟨hvh, hβ0, hβ1, hm0, hwm, hmv, hγ0, hγ1, hθ0, hθ1, hc, hb0, hA⟩ := hS
  have hd : 0 < P.vh - m := by linarith
  have hq := qf_nonneg P m hβ0 hβ1 hd hm0 hα
  rw [CSB_eq, CSB_eq]
  nlinarith [mul_nonneg (mul_nonneg hq (sub_nonneg.2 h)) (by linarith : (0:ℝ) ≤ 1 - P.β)]

lemma thetaFR_le (hS : Standing P m) (α : ℝ) : thetaFR P m α ≤ thetaM P := by
  rw [thetaFR_eq]; split_ifs
  · exact (th1_facts P m hS).2.2.1
  · exact (thetaM_facts P m hS).1.le

lemma CSF_le_CSM (hS : Standing P m) : CSF P m ≤ CSM P m := by
  have hF := thetaF_facts P m hS
  obtain ⟨hvh, hβ0, hβ1, hm0, hwm, hmv, hγ0, hγ1, hθ0, hθ1, hc, hb0, hA⟩ := hS
  have hd : 0 < P.vh - m := by linarith
  unfold CSF CSM BOPDistrib.Misalign.CSA
  have : 0 < (P.vh - m) * P.β := by positivity
  nlinarith [hF.2.1]

lemma CSM_le_CSMR (hS : Standing P m) {α : ℝ} (hα : 0 < α) : CSM P m ≤ CSMR P m α := by
  have hM := thetaM_facts P m hS
  obtain ⟨hvh, hβ0, hβ1, hm0, hwm, hmv, hγ0, hγ1, hθ0, hθ1, hc, hb0, hA⟩ := hS
  have hd : 0 < P.vh - m := by linarith
  have hql := qf_le P m hβ0 hβ1 hd hα
  unfold CSM CSMR
  rw [CSB_eq, show thetaMR P = thetaM P from rfl]
  show (P.vh - m) * thetaM P * P.β ≤ _
  nlinarith [mul_le_mul_of_nonneg_right hql (by linarith [hM.2.1] : (0:ℝ) ≤ 1 - thetaM P)]

lemma CSFR_le_CSMR (hS : Standing P m) {α : ℝ} (hα : 0 < α) : CSFR P m α ≤ CSMR P m α :=
  CSB_mono P m hS hα (thetaFR_le P m hS α)

lemma part1 (hS : Standing P m) (α : ℝ) (hα : 0 < α) :
    MRMaxCS P m α ∧ CSF P m ≤ CSM P m ∧ CSM P m ≤ CSMR P m α := by
  refine ⟨?_, CSF_le_CSM P m hS, CSM_le_CSMR P m hS hα⟩
  unfold MRMaxCS
  exact max_le ((CSF_le_CSM P m hS).trans (CSM_le_CSMR P m hS hα))
    (max_le (CSM_le_CSMR P m hS hα) (CSFR_le_CSMR P m hS hα))

lemma good_FMinCS (hS : Standing P m) : Good (fun α => FMinCS P m α) := by
  have h1 := th1_facts P m hS
  have hθ1 : P.θ0 < 1 := hS.2.2.2.2.2.2.2.2.2.1
  refine good_congr (S := fun α => (P.y ≤ yθ P m α ∧ CSF P m ≤ CSB P m α (th1 P m)) ∨
      CSF P m ≤ CSB P m α P.θ0) (fun α hα => ?_)
    (good_or (good_and (good_yθ P m hS) (good_CSB P m hS _ _ h1.2.1))
      (good_CSB P m hS _ _ hθ1.le))
  have hmono := CSB_mono P m hS hα h1.1
  have eF : FMinCS P m α ↔ CSF P m ≤ CSFR P m α := by
    unfold FMinCS
    constructor
    · intro h; exact h.trans ((min_le_right _ _).trans (min_le_right _ _))
    · intro h
      exact le_min ((CSF_le_CSM P m hS).trans (CSM_le_CSMR P m hS hα))
        (le_min (CSF_le_CSM P m hS) h)
  rw [eF]
  unfold CSFR
  rw [thetaFR_eq]
  split_ifs with hy
  · constructor
    · rintro (h | h)
      · exact h.2
      · exact h.trans hmono
    · intro h; exact Or.inl ⟨hy, h⟩
  · constructor
    · rintro (h | h)
      · exact absurd h.1 hy
      · exact h
    · intro h; exact Or.inr h

lemma good_FOpt (hS : Standing P m) : Good (fun α => FOpt P m α) := by
  have h1 := th1_facts P m hS
  have hM := thetaM_facts P m hS
  have hθ1 : P.θ0 < 1 := hS.2.2.2.2.2.2.2.2.2.1
  refine good_congr (S := fun α => PiM P m ≤ PiF P m ∧
      ((PiB P m α (xFR P m) P.θ0 ≤ PiF P m ∧ PiB P m α (xFR P m) (th1 P m) ≤ PiF P m) ∧
        PiB P m α (xMR P) (thetaMR P) ≤ PiF P m)) (fun α _ => ?_)
    (good_and (good_const _) (good_and (good_and (good_PiB P m hS _ _ _ hθ1.le)
      (good_PiB P m hS _ _ _ h1.2.1)) (good_PiB P m hS _ _ _ hM.2.1)))
  unfold FOpt PiMR
  rw [PiFR_max P m hS α]
  simp only [max_le_iff]

lemma property1 (hS : Standing P m) : PiM P m ≤ PiF P m ↔ m ≤ mF P := by
  have hF := thetaF_facts P m hS
  have hFM := PiF_sub_PiM P m hS
  have hmF := mF_sub P m hS
  obtain ⟨hvh, hβ0, hβ1, hm0, hwm, hmv, hγ0, hγ1, hθ0, hθ1, hc, hb0, hA⟩ := hS
  have hg : 0 < (1 - P.γ) * P.β := mul_pos (by linarith) hβ0
  have hlt : thetaF P m - thetaM P < 0 := by linarith [hF.2.1]
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have : 0 < ((1 - P.γ) * m + P.γ * P.vh - P.w) * P.β - P.cθ := by
      rw [hmF]; exact mul_pos hg (by linarith)
    nlinarith [mul_neg_of_pos_of_neg this hlt]
  · intro h
    have : ((1 - P.γ) * m + P.γ * P.vh - P.w) * P.β - P.cθ ≤ 0 := by
      rw [hmF]; exact mul_nonpos_of_nonneg_of_nonpos hg.le (by linarith)
    nlinarith [mul_nonneg_of_nonpos_of_nonpos this hlt.le]

lemma part3a (hS : Standing P m) (hw : P.w ≤ wbar P) (hcθ : P.cθ ≤ cθbar P) :
    mF P ≤ mMR P ∧ mF P ≤ mMRbar P ∧ mMR P ≤ P.vh ∧ mMRbar P ≤ P.vh := by
  obtain ⟨hvh, hβ0, hβ1, hm0, hwm, hmv, hγ0, hγ1, hθ0, hθ1, hc, hb0, hA⟩ := hS
  have hg : 0 < (1 - P.γ) * P.β := mul_pos (by linarith) hβ0
  have hγne : (1 - P.γ) ≠ 0 := by intro h; linarith
  have hβne : P.β ≠ 0 := hβ0.ne'
  have eMR : mMR P - mF P = (wbar P - P.w) / ((1 - P.γ) * P.β) := by
    unfold mMR mF wbar
    field_simp
    ring
  have eMRbar : mMRbar P - mF P = (cθbar P - P.cθ) / ((1 - P.γ) * P.β) := by
    unfold mMRbar mF cθbar
    field_simp
    ring
  have eMR' : P.vh - mMR P = (cθbar P - P.cθ) / ((1 - P.γ) * P.β) := by
    unfold mMR cθbar; ring
  have eMRbar' : P.vh - mMRbar P = (wbar P - P.w) / ((1 - P.γ) * P.β) := by
    unfold mMRbar wbar; ring
  have hw' : 0 ≤ (wbar P - P.w) / ((1 - P.γ) * P.β) := div_nonneg (by linarith) hg.le
  have hc' : 0 ≤ (cθbar P - P.cθ) / ((1 - P.γ) * P.β) := div_nonneg (by linarith) hg.le
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma part3c (hS : Standing P m) (hw : P.w ≤ wbar P) (hcθ : P.cθ ≤ cθbar P)
    (hmax : max (mMR P) (mMRbar P) ≤ m) (α : ℝ) (hα : 0 < α) : MROpt P m α := by
  have hF := thetaF_facts P m hS
  have hM := thetaM_facts P m hS
  have h1 := th1_facts P m hS
  have hPiFR := PiFR_max P m hS α
  have hmF := mF_sub P m hS
  have h3a := part3a P m hS hw hcθ
  obtain ⟨hvh, hβ0, hβ1, hm0, hwm, hmv, hγ0, hγ1, hθ0, hθ1, hc, hb0, hA⟩ := hS
  have hd : 0 < P.vh - m := by linarith
  have hg : 0 < (1 - P.γ) * P.β := mul_pos (by linarith) hβ0
  have hm1 : mMR P ≤ m := (le_max_left _ _).trans hmax
  have hm2 : mMRbar P ≤ m := (le_max_right _ _).trans hmax
  have hm1' : (P.vh - m) * ((1 - P.γ) * P.β) ≤ (1 - P.β) * (P.w - P.y) - P.cθ := by
    have : P.vh - m ≤ ((1 - P.β) * (P.w - P.y) - P.cθ) / ((1 - P.γ) * P.β) := by
      unfold mMR at hm1; linarith
    rwa [le_div_iff₀ hg] at this
  have hm2' : (P.vh - m) * ((1 - P.γ) * P.β) ≤ P.β * P.vh + (1 - P.β) * P.y - P.w := by
    have : P.vh - m ≤ (P.β * P.vh + (1 - P.β) * P.y - P.w) / ((1 - P.γ) * P.β) := by
      unfold mMRbar at hm2; linarith
    rwa [le_div_iff₀ hg] at this
  have hq := qf_nonneg P m hβ0 hβ1 hd hm0 hα
  have hql := qf_le P m hβ0 hβ1 hd hα
  have hPiMR : PiMR P m α = P.b - P.cθ * (thetaM P - P.θ0) +
      ((1 - P.γ) * m + P.γ * P.vh - P.w) * P.β +
      (1 - P.β) * (1 - thetaM P) * ((1 - P.γ) * qf P m α + P.y - P.w) := by
    unfold PiMR
    rw [PiB_lin, show xMR P = xM P from rfl, show thetaMR P = thetaM P from rfl, hM.2.2.2]
    linear_combination hM.2.2.1
  have hPiM : PiM P m = ((1 - P.γ) * m + P.γ * P.vh - P.w) * P.β * thetaM P + P.b -
      P.cθ * (thetaM P - P.θ0) := by
    unfold PiM; rw [PiA_eq]; linear_combination hM.2.2.1
  have hMleMR : PiM P m ≤ PiMR P m α := by
    rw [hPiM, hPiMR]
    have hk2 : 0 ≤ ((1 - P.γ) * m + P.γ * P.vh - P.w) * P.β +
        (1 - P.β) * ((1 - P.γ) * qf P m α + P.y - P.w) := by
      linarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 - P.β)
        (by linarith : (0:ℝ) ≤ 1 - P.γ)) hq]
    linarith [mul_nonneg (by linarith [hM.2.1] : (0:ℝ) ≤ 1 - thetaM P) hk2]
  have hFleM : PiF P m ≤ PiM P m := by
    have : m - mF P ≥ 0 := by linarith [h3a.1]
    have hk : 0 ≤ ((1 - P.γ) * m + P.γ * P.vh - P.w) * P.β - P.cθ := by
      rw [hmF]; exact mul_nonneg hg.le this
    have hFM := PiF_sub_PiM P m ⟨hvh, hβ0, hβ1, hm0, hwm, hmv, hγ0, hγ1, hθ0, hθ1, hc, hb0, hA⟩
    linarith [mul_nonneg hk (by linarith [hF.2.1] : (0:ℝ) ≤ thetaM P - thetaF P m)]
  have hQ : P.cθ + (1 - P.β) * ((1 - P.γ) * qf P m α + P.y - P.w) ≤ 0 := by
    have := mul_le_mul_of_nonneg_right hql (by linarith : (0:ℝ) ≤ 1 - P.γ)
    linarith
  have hBle : ∀ x θ : ℝ, θ ≤ thetaM P →
      P.cθ * (θ - P.θ0) + x * (P.β + (1 - θ) * (1 - P.β)) ≤ P.b →
      PiB P m α x θ ≤ PiMR P m α := by
    intro x θ hθ hbud
    rw [hPiMR, PiB_lin]
    linarith [mul_nonneg_of_nonpos_of_nonpos (by linarith : θ - thetaM P ≤ 0) hQ]
  have hFRleMR : PiFR P m α ≤ PiMR P m α := by
    rw [hPiFR]
    refine max_le (hBle _ _ hM.1.le (by simpa using h1.2.2.2.2.2)) (hBle _ _ h1.2.2.1 h1.2.2.2.2.1)
  unfold MROpt
  exact max_le (hFleM.trans hMleMR) (max_le hMleMR hFRleMR)

end Main

end BOPCor1Sol

open BOPCor1Sol

theorem solution (P : Params) (m : ℝ) (hS : Standing P m) :
    ∃ acs : ENNReal,
      (∀ α : ℝ, 0 < α → MRMaxCS P m α ∧ CSF P m ≤ CSM P m ∧ CSM P m ≤ CSMR P m α) ∧
      (∀ α : ℝ, 0 < α → (FMinCS P m α ↔ acs ≤ ENNReal.ofReal α)) ∧
      (P.w ≤ wbar P → P.cθ ≤ cθbar P →
        (mF P ≤ mMR P ∧ mF P ≤ mMRbar P ∧ mMR P ≤ P.vh ∧ mMRbar P ≤ P.vh) ∧
        (∃ aF : ENNReal, ∀ α : ℝ, 0 < α →
          (FOpt P m α ↔ m ≤ mF P ∧ aF ≤ ENNReal.ofReal α) ∧
          (FOpt P m α ∧ FMinCS P m α ↔ m ≤ mF P ∧ max aF acs ≤ ENNReal.ofReal α)) ∧
        (max (mMR P) (mMRbar P) ≤ m → ∀ α : ℝ, 0 < α → MROpt P m α)) := by
  obtain ⟨acs, hacs⟩ := threshold (good_FMinCS P m hS)
  refine ⟨acs, part1 P m hS, hacs, fun hw hcθ => ⟨part3a P m hS hw hcθ, ?_, part3c P m hS hw hcθ⟩⟩
  obtain ⟨aF, haF⟩ := threshold (good_FOpt P m hS)
  have hFOpt : ∀ α : ℝ, 0 < α → (FOpt P m α ↔ m ≤ mF P ∧ aF ≤ ENNReal.ofReal α) := by
    intro α hα
    constructor
    · intro h
      exact ⟨(property1 P m hS).1 ((le_max_left _ _).trans h), (haF α hα).1 h⟩
    · intro h
      exact (haF α hα).2 h.2
  refine ⟨aF, fun α hα => ⟨hFOpt α hα, ?_⟩⟩
  rw [hFOpt α hα, hacs α hα, max_le_iff]
  tauto
