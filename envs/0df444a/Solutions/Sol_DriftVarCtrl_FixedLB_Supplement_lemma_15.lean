-- Prove2me | solution 1 for DriftVarCtrl.FixedLB.Supplement.lemma_15
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:40:15.086355+00:00
-- url     : https://prove2.me/submissions/d98a7804-8fc9-4620-b691-3462806ca43b

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_Thresholds

open DriftVarCtrl
open DriftVarCtrl.FixedLB
open DriftVarCtrl.FixedLB.Supplement

open DriftVarCtrl.FixedLB

/-- Lemma 15 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. EC-23). For a control `c` and every value `h > 0` there is a unique
`Ũ > 0` with `h = h⁺(Ũ)`, where `h⁺(Ũ) = −Mμ/(Ũ(1 − (1 − e^{−vŨ})/(vŨ)))` is (17) with upper
boundary `Ũ`.

Formalization Note: `h` ranges over all positive reals, not only the model's cost of `c`. The
standing `v₁ < v₂` (p. 12) is `hv`. -/
theorem solution (p : Params) (hv : v p .one < v p .two) (c : Ctrl) (h : ℝ) (hh : 0 < h) :
    ∃! Ũ : ℝ, 0 < Ũ ∧ h = hplusU p c Ũ := by
      have hmu : 0 < p.mu c := by
        cases c
        · exact p.hμ₁
        · exact p.hμ₂
      have hsig : 0 < p.sig c := by
        cases c
        · exact p.hσ₁
        · exact p.hσ₂
      have hvc : 0 < v p c := by
        unfold v
        positivity
      have hM := p.hM
      obtain ⟨w, hw⟩ : ∃ w, w = v p c := ⟨_, rfl⟩
      obtain ⟨N, hN⟩ : ∃ N, N = -p.M * p.mu c := ⟨_, rfl⟩
      have hw0 : 0 < w := hw ▸ hvc
      have hN0 : 0 < N := by
        rw [hN]
        exact mul_pos (by linarith) hmu
      have hwne : w ≠ 0 := hw0.ne'
      obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun U => U - (1 - Real.exp (-w * U)) / w := ⟨_, rfl⟩
      have hgU : ∀ U, g U = U - (1 - Real.exp (-w * U)) / w := fun U => by rw [hg]
      have hg0 : g 0 = 0 := by simp [hgU]
      -- strict monotonicity on [0, ∞)
      have hmono : ∀ a b, 0 ≤ a → a < b → g a < g b := by
        intro a b ha hab
        have h1 : Real.exp (-w * a) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
        have h2 : 0 < Real.exp (-w * a) := Real.exp_pos _
        have hx : 0 < w * (b - a) := mul_pos hw0 (by linarith)
        have h3 : -(w * (b - a)) + 1 < Real.exp (-(w * (b - a))) :=
          Real.add_one_lt_exp (by linarith)
        have h4 : Real.exp (-w * b) = Real.exp (-w * a) * Real.exp (-(w * (b - a))) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have h5 : Real.exp (-w * a) - Real.exp (-w * b) < w * (b - a) := by
          rw [h4]
          nlinarith
        have h6 : g b - g a = (w * (b - a) - (Real.exp (-w * a) - Real.exp (-w * b))) / w := by
          rw [hgU, hgU]
          field_simp
          ring
        have h7 : 0 < g b - g a := by
          rw [h6]
          exact div_pos (by linarith) hw0
        linarith
      have hiff : ∀ U, 0 < U → (h = hplusU p c U ↔ g U = N / h) := by
        intro U hU
        have hgpos : 0 < g U := by
          have := hmono 0 U le_rfl hU
          linarith
        have hden : U * (1 - (1 - Real.exp (-w * U)) / (w * U)) = g U := by
          rw [hgU]
          field_simp
        unfold hplusU
        rw [← hw, ← hN, hden, eq_div_iff hgpos.ne', eq_div_iff hh.ne', mul_comm]
      have hK : 0 < N / h := div_pos hN0 hh
      have hcont : Continuous g := by
        rw [hg]
        fun_prop
      have hb : 0 ≤ N / h + 1 / w := by positivity
      have hlarge : N / h ≤ g (N / h + 1 / w) := by
        have h2 : 0 < Real.exp (-w * (N / h + 1 / w)) / w := div_pos (Real.exp_pos _) hw0
        rw [hgU, sub_div]
        linarith
      obtain ⟨U, hUmem, hUeq⟩ :=
        intermediate_value_Icc hb hcont.continuousOn ⟨hg0.le.trans hK.le, hlarge⟩
      have hUpos : 0 < U := by
        rcases hUmem.1.eq_or_lt with h0 | h0
        · rw [← h0, hg0] at hUeq
          linarith
        · exact h0
      refine ⟨U, ⟨hUpos, (hiff U hUpos).2 hUeq⟩, ?_⟩
      rintro y ⟨hy, hyeq⟩
      have hyg := (hiff y hy).1 hyeq
      rcases lt_trichotomy y U with hl | hl | hl
      · have := hmono y U hy.le hl
        linarith
      · exact hl
      · have := hmono U y hUpos.le hl
        linarith
