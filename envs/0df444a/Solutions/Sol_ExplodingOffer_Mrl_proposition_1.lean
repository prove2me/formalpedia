-- Prove2me | solution 1 for ExplodingOffer.Mrl.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T23:20:27.295117+00:00
-- url     : https://prove2.me/submissions/9d06134c-7dee-4bbb-b71f-b1b18f6f7975

import Mathlib
import Definitions.Def_ExplodingOffer_Mrl_Model
import Theorems.Thm_ExplodingOffer_Mrl_tval_bijection
import Theorems.Thm_ExplodingOffer_Mrl_eq_5_6

open MeasureTheory
open ExplodingOffer.Mrl

namespace Prop1Aux

variable {μ : Measure ℝ} {a : ℝ} {b : EReal}

lemma L_anti (hμ : OfferDist μ a b) : Antitone (Lfun μ) := by
  haveI := hμ.isProb
  intro v w hvw
  apply integral_mono ((hμ.integrable.sub (integrable_const w)).pos_part)
    ((hμ.integrable.sub (integrable_const v)).pos_part)
  intro x
  simp only [Pi.sub_apply]
  exact max_le_max (by linarith) le_rfl

lemma Tval_nonneg (hμ : OfferDist μ a b) (s : ℝ) (hs0 : 0 ≤ s) (hsb : (s : EReal) < b) :
    0 ≤ Tval μ s := by
  obtain ⟨_, hmono, _, _⟩ := tval_bijection hμ
  have h0b : ((0:ℝ) : EReal) < b := lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr hs0) hsb
  have := hmono.monotoneOn ⟨le_refl (0:ℝ), h0b⟩ ⟨hs0, hsb⟩ hs0
  rw [show Tval μ 0 = 0 by simp [Tval]] at this
  exact this

/-- `𝒯⁻¹` is monotone on `[0, ∞)`. -/
lemma Tinv_mono (hμ : OfferDist μ a b) {y y' : ℝ} (hy : 0 ≤ y) (hyy : y ≤ y') :
    Tinv μ b y ≤ Tinv μ b y' := by
  obtain ⟨_, hmono, hinv, _⟩ := tval_bijection hμ
  obtain ⟨h0, hb, hT⟩ := hinv y hy
  obtain ⟨h0', hb', hT'⟩ := hinv y' (le_trans hy hyy)
  by_contra h
  push Not at h
  have := hmono ⟨h0', hb'⟩ ⟨h0, hb⟩ h
  linarith

/-- If `𝒯(s) < y` (with `y ≥ 0`, `0 ≤ s < b`) then `s < 𝒯⁻¹(y)`. -/
lemma lt_Tinv (hμ : OfferDist μ a b) {s y : ℝ} (hs0 : 0 ≤ s) (hsb : (s : EReal) < b)
    (hy : 0 ≤ y) (h : Tval μ s < y) : s < Tinv μ b y := by
  obtain ⟨_, hmono, hinv, _⟩ := tval_bijection hμ
  obtain ⟨h0, hb, hT⟩ := hinv y hy
  by_contra hc
  push Not at hc
  have := hmono.monotoneOn ⟨h0, hb⟩ ⟨hs0, hsb⟩ hc
  linarith

lemma minAccept_nonneg (hμ : OfferDist μ a b) {lam T tD : ℝ} (hlam : 0 < lam) (htDT : tD ≤ T) :
    0 ≤ minAccept μ b lam T tD := by
  obtain ⟨_, _, hinv, _⟩ := tval_bijection hμ
  exact (hinv _ (mul_nonneg hlam.le (by linarith))).1

end Prop1Aux

open Prop1Aux in
theorem solution {μ : Measure ℝ} {a : ℝ} {b : EReal} (hμ : OfferDist μ a b)
    {lam T u : ℝ} (hlam : 0 < lam) (hT : 0 < T) (hu : 0 < u) :
    (∀ s : ℝ, 0 ≤ s → s ≤ u →
      Feasible μ b lam T u s (optDeadline μ b lam T s) ∧
      ∀ tD : ℝ, Feasible μ b lam T u s tD →
        surplus μ b lam T u s tD ≤ surplus μ b lam T u s (optDeadline μ b lam T s)) ∧
    AntitoneOn (optDeadline μ b lam T) (Set.Icc 0 u) := by
  haveI := hμ.isProb
  haveI := hμ.noAtoms
  obtain ⟨hLpos, hmono, hinv, hleft⟩ := tval_bijection hμ
  obtain ⟨hV0, hVb, hTV⟩ := hinv (lam * T) (by positivity)
  constructor
  · intro s hs0 hsu
    by_cases hsb : (s : EReal) < b
    · have hc0 := Tval_nonneg hμ s hs0 hsb
      have hopt : optDeadline μ b lam T s = max (T - Tval μ s / lam) 0 := by
        unfold optDeadline; rw [if_pos hsb]
      -- feasibility
      have hfeas : Feasible μ b lam T u s (optDeadline μ b lam T s) := by
        refine ⟨?_, hsu, by rw [hopt]; exact le_max_right _ _, ?_⟩
        · unfold minAccept
          rw [hopt]
          rcases le_total (T - Tval μ s / lam) 0 with h | h
          · rw [max_eq_right h, sub_zero]
            have : lam * T ≤ Tval μ s := by
              rw [sub_nonpos, le_div_iff₀ hlam] at h; linarith
            calc Tinv μ b (lam * T) ≤ Tinv μ b (Tval μ s) := Tinv_mono hμ (by positivity) this
              _ = s := hleft s hs0 hsb
          · rw [max_eq_left h]
            have : lam * (T - (T - Tval μ s / lam)) = Tval μ s := by field_simp; ring
            rw [this, hleft s hs0 hsb]
        · rw [hopt]
          apply max_le _ hT.le
          have : 0 ≤ Tval μ s / lam := div_nonneg hc0 hlam.le
          linarith
      refine ⟨hfeas, ?_⟩
      intro tD htD
      obtain ⟨hmin, _, htD0, htDT⟩ := htD
      obtain ⟨hmin', _, hopt0, hoptT⟩ := hfeas
      rw [(eq_5_6 hμ hlam hT htD0 htDT hmin hsb u).2,
        (eq_5_6 hμ hlam hT hopt0 hoptT hmin' hsb u).2]
      have hLs := hLpos s hs0 hsb
      -- the optimal deadline is the smallest feasible one
      have hle : optDeadline μ b lam T s ≤ tD := by
        rw [hopt]
        apply max_le _ htD0
        by_contra h
        push Not at h
        have hlt : Tval μ s < lam * (T - tD) := by
          rw [lt_sub_comm, div_lt_iff₀ hlam] at h; linarith
        have := lt_Tinv hμ hs0 hsb (by linarith) hlt
        unfold minAccept at hmin
        linarith
      have hvt : ∀ t, 0 ≤ t → valueToGo μ b lam T s t 0 = Tinv μ b (Tval μ s + lam * t) := by
        intro t ht; unfold valueToGo; rw [if_pos ht, if_pos hsb]; congr 1; ring
      rw [hvt tD htD0, hvt _ hopt0]
      have hmonoV : Tinv μ b (Tval μ s + lam * optDeadline μ b lam T s) ≤
          Tinv μ b (Tval μ s + lam * tD) :=
        Tinv_mono hμ (by positivity) (by nlinarith)
      have := L_anti hμ hmonoV
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact div_le_div_of_nonneg_right this hLs.le
    · -- `s ≥ b`: no alternative offer is ever accepted before `t_D`
      push Not at hsb
      have hopt : optDeadline μ b lam T s = 0 := by
        unfold optDeadline; rw [if_neg (not_lt.mpr hsb)]
      have hzero : ∀ tD : ℝ, 0 ≤ tD → surplus μ b lam T u s tD = u - s := by
        intro tD h
        have hint : ∫ t in (0:ℝ)..tD, (μ (Set.Ici (valueToGo μ b lam T s tD t))).toReal = 0 := by
          rw [intervalIntegral.integral_of_le h]
          apply setIntegral_eq_zero_of_forall_eq_zero
          intro t ht
          have : valueToGo μ b lam T s tD t = s := by
            unfold valueToGo; rw [if_pos ht.2, if_neg (not_lt.mpr hsb)]
          rw [this, measure_congr (Ioi_ae_eq_Ici (μ := μ) (a := s)).symm]
          have : Set.Ioi s ⊆ {x : ℝ | b < (x : EReal)} := fun x hx =>
            lt_of_le_of_lt hsb (EReal.coe_lt_coe_iff.mpr hx)
          rw [measure_mono_null this hμ.above]; rfl
        unfold surplus noAcceptProb
        rw [hint]; simp
      refine ⟨⟨?_, hsu, by rw [hopt], by rw [hopt]; exact hT.le⟩, fun tD htD => by
        rw [hzero tD htD.2.2.1, hzero _ (by rw [hopt])]⟩
      unfold minAccept; rw [hopt, sub_zero]
      have := lt_of_lt_of_le hVb hsb
      exact (EReal.coe_lt_coe_iff.mp this).le
  · intro s hs s' hs' hss'
    by_cases hsb' : (s' : EReal) < b
    · have hsb : (s : EReal) < b := lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr hss') hsb'
      unfold optDeadline
      rw [if_pos hsb, if_pos hsb']
      have := hmono.monotoneOn ⟨hs.1, hsb⟩ ⟨hs'.1, hsb'⟩ hss'
      apply max_le_max _ le_rfl
      have := div_le_div_of_nonneg_right this hlam.le
      linarith
    · have : optDeadline μ b lam T s' = 0 := by unfold optDeadline; rw [if_neg hsb']
      rw [this]
      unfold optDeadline
      split_ifs
      · exact le_max_right _ _
      · exact le_rfl
