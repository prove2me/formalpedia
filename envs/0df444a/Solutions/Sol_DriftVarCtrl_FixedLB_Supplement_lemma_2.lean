-- Prove2me | solution 1 for DriftVarCtrl.FixedLB.Supplement.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:38:45.614863+00:00
-- url     : https://prove2.me/submissions/7f2c7b57-cefb-47bb-9f7d-f9015879c5a2

import Mathlib
import Definitions.Def_DriftVarCtrl_FixedLB_Model
import Definitions.Def_DriftVarCtrl_FixedLB_Supplement_Thresholds

open DriftVarCtrl
open DriftVarCtrl.FixedLB
open DriftVarCtrl.FixedLB.Supplement

open DriftVarCtrl.FixedLB

/-- Lemma 2 (Wang, Zenios, New Venture Creation: A Drift-Variance Diffusion Control Model, SSRN 3667132 (working paper, sha256 2d7a57ba…), p. 18; proof p. EC-20). Consider a control `c` with cost `h ≤ h⁺`. Then the
value function of the single control policy that always uses `c` (fixed lower boundary `0`) is
non-positive on `(0, U]`. If `h > h⁺`, it is positive on some interval in `(0, U]`.

Formalization Note: "the value function associated with the single control policy" is any
`W` with `IsValue p (static p c) W` (the analytic value of the base model: the ODE of `c` on
`(0, U)`, `W(0) = 0`, `W(U) = M`); the lemma's proof uses its closed form (54). The standing
`v₁ < v₂` (p. 12) is the hypothesis `hv`. -/
theorem solution (p : Params) (hv : v p .one < v p .two) (c : Ctrl) :
    (p.cost c ≤ hplus p c → ∀ W : ℝ → ℝ, IsValue p (static p c) W →
      ∀ x ∈ Set.Ioc 0 p.U, W x ≤ 0) ∧
    (hplus p c < p.cost c → ∀ W : ℝ → ℝ, IsValue p (static p c) W →
      ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ p.U ∧ ∀ x ∈ Set.Ioo a b, 0 < W x) := by
        have hmu : 0 < p.mu c := by cases c; exacts [p.hμ₁, p.hμ₂]
        have hsig : 0 < p.sig c := by cases c; exacts [p.hσ₁, p.hσ₂]
        have hh : 0 < p.cost c := by cases c; exacts [p.hh₁, p.hh₂]
        have hU := p.hU
        have hvdef : p.sig c ^ 2 * v p c = 2 * p.mu c := by
          unfold v
          field_simp
        have hv0 : 0 < v p c := by unfold v; positivity
        have hplusdef : hplus p c = -p.M * p.mu c / (p.U * (1 - (1 - Real.exp (-v p c * p.U)) / (v p c * p.U))) := rfl
        rw [hplusdef]
        clear hplusdef
        have key : ∀ W : ℝ → ℝ, IsValue p (static p c) W → ∃ D : ℝ,
            ∀ x ∈ Set.Icc 0 p.U, W x = -(p.cost c / p.mu c) * x + D * (1 - Real.exp (-v p c * x)) := by
          intro W hW
          obtain ⟨hC, hW0, hWU, hode⟩ := hW
          have hode' : ∀ x ∈ Set.Ioo 0 p.U, ContDiffAt ℝ 2 W x ∧
              p.cost c + p.mu c * deriv W x + p.sig c ^ 2 / 2 * deriv (deriv W) x = 0 := by
            intro x hx
            have := hode (⟨0, by simp⟩ : Fin 1) x (by
              simpa [static] using hx)
            simpa [static] using this
          have hd1 : ∀ x ∈ Set.Ioo 0 p.U, HasDerivAt W (deriv W x) x := fun x hx =>
            ((hode' x hx).1.differentiableAt (by norm_num)).hasDerivAt
          have hd2 : ∀ x ∈ Set.Ioo 0 p.U, HasDerivAt (deriv W)
              (-v p c * (deriv W x + p.cost c / p.mu c)) x := by
            intro x hx
            have h1 : ContDiffAt ℝ 1 (deriv W) x := by
              have h0 : ContDiffOn ℝ 2 W (Set.Ioo 0 p.U) :=
                fun y hy => (hode' y hy).1.contDiffWithinAt
              have h1 : ContDiffOn ℝ 1 (deriv W) (Set.Ioo 0 p.U) :=
                h0.deriv_of_isOpen isOpen_Ioo (by norm_num)
              exact h1.contDiffAt (isOpen_Ioo.mem_nhds hx)
            have h2 := (h1.differentiableAt (by norm_num)).hasDerivAt
            have h3 : deriv (deriv W) x = -v p c * (deriv W x + p.cost c / p.mu c) := by
              have h4 := (hode' x hx).2
              have h5 : p.sig c ^ 2 * deriv (deriv W) x
                  = p.sig c ^ 2 * (-v p c * (deriv W x + p.cost c / p.mu c)) := by
                have : p.sig c ^ 2 * (-v p c * (deriv W x + p.cost c / p.mu c))
                    = -(p.sig c ^ 2 * v p c) * (deriv W x + p.cost c / p.mu c) := by ring
                rw [this, hvdef]
                field_simp
                linarith
              exact mul_left_cancel₀ (by positivity) h5
            rwa [h3] at h2
          have hexp : ∀ (a x : ℝ), HasDerivAt (fun y => Real.exp (a * y)) (Real.exp (a * x) * a) x := by
            intro a x
            have := ((hasDerivAt_id x).const_mul a).exp
            simpa using this
          have hG : ∀ x ∈ Set.Ioo 0 p.U,
              HasDerivAt (fun y => (deriv W y + p.cost c / p.mu c) * Real.exp (v p c * y)) 0 x := by
            intro x hx
            have := ((hd2 x hx).add_const (p.cost c / p.mu c)).mul (hexp (v p c) x)
            have hz : -v p c * (deriv W x + p.cost c / p.mu c) * Real.exp (v p c * x)
                + (deriv W x + p.cost c / p.mu c) * (Real.exp (v p c * x) * v p c) = 0 := by ring
            rw [hz] at this
            exact this
          obtain ⟨C, hCc⟩ : ∃ C, ∀ x ∈ Set.Ioo 0 p.U,
              (deriv W x + p.cost c / p.mu c) * Real.exp (v p c * x) = C := by
            refine ⟨(deriv W (p.U/2) + p.cost c / p.mu c) * Real.exp (v p c * (p.U/2)), fun x hx => ?_⟩
            exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
              (f := fun y => (deriv W y + p.cost c / p.mu c) * Real.exp (v p c * y))
              (fun y hy => (hG y hy).differentiableAt.differentiableWithinAt)
              (fun y hy => (hG y hy).deriv) hx ⟨by linarith, by linarith⟩
          have hW' : ∀ x ∈ Set.Ioo 0 p.U, deriv W x + p.cost c / p.mu c = C * Real.exp (-v p c * x) := by
            intro x hx
            rw [← hCc x hx, mul_assoc, ← Real.exp_add]
            simp
          have hH : ∀ x ∈ Set.Ioo 0 p.U, HasDerivAt
              (fun y => W y + p.cost c / p.mu c * y + C / v p c * Real.exp (-v p c * y)) 0 x := by
            intro x hx
            have := ((hd1 x hx).add ((hasDerivAt_id x).const_mul (p.cost c / p.mu c))).add
              ((hexp (-v p c) x).const_mul (C / v p c))
            have hz : deriv W x + p.cost c / p.mu c * 1
                + C / v p c * (Real.exp (-v p c * x) * -v p c) = 0 := by
              rw [mul_one, hW' x hx]
              have hne := hv0.ne'
              have : C / v p c * (Real.exp (-v p c * x) * -v p c)
                  = -(C / v p c * v p c) * Real.exp (-v p c * x) := by ring
              rw [this, div_mul_cancel₀ _ hne]
              ring
            rw [hz] at this
            exact this
          have hHc : ContinuousOn
              (fun y => W y + p.cost c / p.mu c * y + C / v p c * Real.exp (-v p c * y))
              (Set.Icc 0 p.U) := by
            have := hC.continuousOn
            fun_prop
          have hm := monotoneOn_of_deriv_nonneg (convex_Icc 0 p.U) hHc
            (fun y hy => (hH y (by simpa using hy)).differentiableAt.differentiableWithinAt)
            (fun y hy => (hH y (by simpa using hy)).deriv.ge)
          have ha := antitoneOn_of_deriv_nonpos (convex_Icc 0 p.U) hHc
            (fun y hy => (hH y (by simpa using hy)).differentiableAt.differentiableWithinAt)
            (fun y hy => (hH y (by simpa using hy)).deriv.le)
          refine ⟨C / v p c, fun x hx => ?_⟩
          have h0 : (0:ℝ) ∈ Set.Icc 0 p.U := ⟨le_rfl, hU.le⟩
          have e := le_antisymm (ha h0 hx hx.1) (hm h0 hx hx.1)
          simp only [hW0, mul_zero, Real.exp_zero] at e
          linarith
        set a := v p c with hadef
        set h := p.cost c
        set m := p.mu c
        set U := p.U
        have hexpU : Real.exp (-a * U) < 1 := by
          rw [Real.exp_lt_one_iff]
          nlinarith [mul_pos hv0 hU]
        have haU : 0 < a * U := mul_pos hv0 hU
        have hden : 0 < U * (1 - (1 - Real.exp (-a * U)) / (a * U)) := by
          apply mul_pos hU
          rw [sub_pos, div_lt_one haU]
          have := Real.add_one_lt_exp (x := -a * U) (by nlinarith)
          linarith
        have hid : h * (U * (1 - (1 - Real.exp (-a * U)) / (a * U)))
            = h * U - h * (1 - Real.exp (-a * U)) / a := by
          field_simp
        have hMeq : ∀ W : ℝ → ℝ, IsValue p (static p c) W → ∀ D : ℝ,
            (∀ x ∈ Set.Icc 0 U, W x = -(h / m) * x + D * (1 - Real.exp (-a * x))) →
            -p.M * m = h * U - D * m * (1 - Real.exp (-a * U)) := by
          intro W hW D hD
          have h1 := hD U ⟨hU.le, le_rfl⟩
          rw [hW.2.2.1] at h1
          rw [h1]
          field_simp
          ring
        constructor
        · intro hle W hW x hx
          obtain ⟨D, hD⟩ := key W hW
          have hM := hMeq W hW D hD
          rw [le_div_iff₀ hden, hid, hM] at hle
          have hDle : D ≤ h / (m * a) := by
            have h1 : D * m * (1 - Real.exp (-a * U)) ≤ h / a * (1 - Real.exp (-a * U)) := by
              have : h * (1 - Real.exp (-a * U)) / a = h / a * (1 - Real.exp (-a * U)) := by ring
              linarith
            have h2 := le_of_mul_le_mul_right h1 (by linarith)
            rw [le_div_iff₀ hv0] at h2
            rw [le_div_iff₀ (by positivity)]
            linarith
          rw [hD x ⟨hx.1.le, hx.2⟩]
          have hax : 0 ≤ a * x := mul_nonneg hv0.le hx.1.le
          have h3 : 0 ≤ 1 - Real.exp (-a * x) := by
            have : Real.exp (-a * x) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
            linarith
          have h4 : 1 - Real.exp (-a * x) ≤ a * x := by
            have := Real.add_one_le_exp (-a * x)
            linarith
          have h5 : D * (1 - Real.exp (-a * x)) ≤ h / (m * a) * (a * x) :=
            (mul_le_mul_of_nonneg_right hDle h3).trans (mul_le_mul_of_nonneg_left h4 (by positivity))
          have h6 : h / (m * a) * (a * x) = h / m * x := by field_simp
          linarith
        · intro hlt W hW
          obtain ⟨D, hD⟩ := key W hW
          have hM := hMeq W hW D hD
          rw [div_lt_iff₀ hden, hid, hM] at hlt
          have hDgt : h < D * m * a := by
            have h1 : h / a * (1 - Real.exp (-a * U)) < D * m * (1 - Real.exp (-a * U)) := by
              have : h * (1 - Real.exp (-a * U)) / a = h / a * (1 - Real.exp (-a * U)) := by ring
              linarith
            have h2 := lt_of_mul_lt_mul_right h1 (by linarith)
            rwa [div_lt_iff₀ hv0] at h2
          have hD0 : 0 < D := by
            have : 0 < D * (m * a) := by linarith
            exact pos_of_mul_pos_left this (by positivity)
          refine ⟨0, min U ((D * m * a - h) / (h * a)), le_rfl, lt_min hU
            (div_pos (by linarith) (by positivity)), min_le_left _ _, fun x hx => ?_⟩
          have hx0 := hx.1
          have hxU : x < U := hx.2.trans_le (min_le_left _ _)
          have hxb : x < (D * m * a - h) / (h * a) := hx.2.trans_le (min_le_right _ _)
          rw [lt_div_iff₀ (by positivity)] at hxb
          rw [hD x ⟨hx0.le, hxU.le⟩]
          have hax : 0 < a * x := mul_pos hv0 hx0
          have h3 : Real.exp (-a * x) ≤ 1 / (1 + a * x) := by
            rw [show -a * x = -(a * x) by ring, Real.exp_neg, ← one_div]
            apply one_div_le_one_div_of_le (by linarith)
            linarith [Real.add_one_le_exp (a * x)]
          have h4 : D * (a * x / (1 + a * x)) ≤ D * (1 - Real.exp (-a * x)) := by
            apply mul_le_mul_of_nonneg_left _ hD0.le
            have : a * x / (1 + a * x) = 1 - 1 / (1 + a * x) := by field_simp; ring
            linarith
          have h5 : h / m * x < D * (a * x / (1 + a * x)) := by
            rw [div_mul_eq_mul_div, ← mul_div_assoc, div_lt_div_iff₀ hmu (by linarith)]
            nlinarith
          linarith
