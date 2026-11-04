-- Prove2me | solution 1 for DoubleMoralHazard.Baseline.hjb_bound
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T21:52:33.461236+00:00
-- url     : https://prove2.me/submissions/e2beb2b7-f338-4be1-bc93-3c3e0d602d30

import Mathlib
import Definitions.Def_DoubleMoralHazard_Baseline_Params
import Definitions.Def_DoubleMoralHazard_Baseline_HJB

open DoubleMoralHazard.Baseline Set Filter Topology

namespace DMHHjbAux

/-- Tangent-line inequality for a concave function differentiable on `[0, ∞)`. -/
lemma tangent {F : ℝ → ℝ} (hcc : ConcaveOn ℝ (Ici 0) F) (hd : DifferentiableOn ℝ F (Ici 0))
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    F y ≤ F x + derivWithin F (Ici 0) x * (y - x) := by
  rcases lt_trichotomy x y with h | rfl | h
  · have := hcc.slope_le_derivWithin (mem_Ici.2 hx) (mem_Ici.2 hy) h (hd x (mem_Ici.2 hx))
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 h)] at this
    linarith
  · simp
  · have := hcc.derivWithin_le_slope (mem_Ici.2 hy) (mem_Ici.2 hx) h (hd x (mem_Ici.2 hx))
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 h)] at this
    have e : derivWithin F (Ici 0) x * (y - x) = -(derivWithin F (Ici 0) x * (x - y)) := by ring
    linarith

lemma anti {F : ℝ → ℝ} (hcc : ConcaveOn ℝ (Ici 0) F) (hd : DifferentiableOn ℝ F (Ici 0))
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    derivWithin F (Ici 0) y ≤ derivWithin F (Ici 0) x :=
  hcc.antitoneOn_derivWithin hd (mem_Ici.2 hx) (mem_Ici.2 (hx.trans hxy)) hxy

/-- Beyond the threshold the derivative is `-1`. -/
lemma deriv_eq {F : ℝ → ℝ} (hcc : ConcaveOn ℝ (Ici 0) F) (hd : DifferentiableOn ℝ F (Ici 0))
    {wbar : ℝ} (hwbar : 0 ≤ wbar) (hext : ∀ w, wbar ≤ w → F w = F wbar - (w - wbar))
    (hge : ∀ w : ℝ, 0 ≤ w → -1 ≤ derivWithin F (Ici 0) w) {w : ℝ} (hw : wbar < w) :
    derivWithin F (Ici 0) w = -1 := by
  have hx0 : 0 ≤ (wbar + w) / 2 := by linarith
  have hxw : (wbar + w) / 2 < w := by linarith
  have := hcc.derivWithin_le_slope (mem_Ici.2 hx0) (mem_Ici.2 (by linarith)) hxw
    (hd w (mem_Ici.2 (by linarith)))
  have e1 := hext w hw.le
  have e2 := hext ((wbar + w) / 2) (by linarith)
  rw [slope_def_field, e1, e2] at this
  have e : (F wbar - (w - wbar) - (F wbar - ((wbar + w) / 2 - wbar))) / (w - (wbar + w) / 2) = -1 := by
    rw [div_eq_iff (by linarith)]; ring
  rw [e] at this
  exact le_antisymm this (hge w (by linarith))

/-- The value-function identity extends from `[0, w̄)` to all of `[0, ∞)`. -/
lemma ident {F J : ℝ → ℝ} {r A wbar : ℝ} (_hr : 0 < r) (hwbar : 0 < wbar)
    (hcc : ConcaveOn ℝ (Ici 0) F) (hd : DifferentiableOn ℝ F (Ici 0))
    (hge : ∀ w : ℝ, 0 ≤ w → -1 ≤ derivWithin F (Ici 0) w)
    (hext : ∀ w, wbar ≤ w → F w = F wbar - (w - wbar))
    (hJ : ∀ w, wbar ≤ w → J w = J wbar)
    (hcont : ContinuousWithinAt (fun w => r * F w - J w) (Ico 0 wbar) wbar)
    (heq : ∀ w ∈ Ico 0 wbar, r * F w = A + J w + r * (w - wbar) * derivWithin F (Ici 0) w) :
    ∀ w : ℝ, 0 ≤ w → r * F w = A + J w + r * (w - wbar) * derivWithin F (Ici 0) w := by
  set D := derivWithin F (Ici 0)
  -- boundary value
  have hbd : r * F wbar = A + J wbar := by
    have : (𝓝[Ico 0 wbar] wbar).NeBot := mem_closure_iff_nhdsWithin_neBot.mp
      (by rw [closure_Ico hwbar.ne]; exact ⟨hwbar.le, le_rfl⟩)
    have h0 : Tendsto (fun w => r * (w - wbar)) (𝓝[Ico 0 wbar] wbar) (𝓝 0) := by
      have : Tendsto (fun w : ℝ => r * (w - wbar)) (𝓝 wbar) (𝓝 (r * (wbar - wbar))) :=
        ((continuous_const.mul (continuous_id.sub continuous_const)).tendsto wbar)
      rw [sub_self, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hb : IsBoundedUnder (· ≤ ·) (𝓝[Ico 0 wbar] wbar) (norm ∘ D) := by
      refine isBoundedUnder_of_eventually_le (a := 1 + |D 0|) ?_
      refine eventually_nhdsWithin_of_forall (fun w hw => ?_)
      have h1 := hge w hw.1
      have h2 : D w ≤ D 0 := anti hcc hd le_rfl hw.1
      simp only [Function.comp, Real.norm_eq_abs]
      rw [abs_le]
      constructor
      · linarith [abs_nonneg (D 0)]
      · linarith [le_abs_self (D 0)]
    have hz := h0.zero_mul_isBoundedUnder_le hb
    have h2 : Tendsto (fun w => r * F w - J w) (𝓝[Ico 0 wbar] wbar) (𝓝 A) := by
      have := (tendsto_const_nhds (x := A)).add hz
      rw [add_zero] at this
      refine this.congr' (eventually_nhdsWithin_of_forall (fun w hw => ?_))
      show A + r * (w - wbar) * D w = r * F w - J w
      rw [heq w hw]; ring
    have := tendsto_nhds_unique hcont h2
    linarith
  intro w hw
  rcases lt_or_ge w wbar with h | h
  · exact heq w ⟨hw, h⟩
  · rcases eq_or_lt_of_le h with rfl | h'
    · simp only [sub_self, mul_zero, zero_mul, add_zero]; exact hbd
    · have hdw : D w = -1 := deriv_eq hcc hd hwbar.le hext hge h'
      rw [hdw, hext w h, hJ w h]
      linarith

lemma cont_shift {F : ℝ → ℝ} (hc : ContinuousOn F (Ici 0)) {wbar a : ℝ} (hw : 0 ≤ wbar)
    (ha : 0 ≤ a) : ContinuousWithinAt (fun w => F (w + a)) (Ico 0 wbar) wbar :=
  ContinuousWithinAt.comp (f := fun w : ℝ => w + a) (g := F) (t := Ici 0)
    (hc (wbar + a) (mem_Ici.2 (by linarith)))
    (continuous_add_const a).continuousWithinAt
    (fun x hx => mem_Ici.2 (by linarith [hx.1]))

lemma cont0 {F : ℝ → ℝ} (hc : ContinuousOn F (Ici 0)) {wbar : ℝ} (hw : 0 ≤ wbar) :
    ContinuousWithinAt F (Ico 0 wbar) wbar :=
  (hc wbar (mem_Ici.2 hw)).mono Ico_subset_Ici_self

lemma shift_ext {F : ℝ → ℝ} {wbar : ℝ} (hext : ∀ w, wbar ≤ w → F w = F wbar - (w - wbar))
    {w a : ℝ} (hw : wbar ≤ w) (ha : 0 ≤ a) : F (w + a) - F w = -a := by
  rw [hext _ (by linarith), hext w hw]; ring

end DMHHjbAux

open DMHHjbAux

theorem solution (P : Params) :
    (P.c ≤ P.mu * P.p * P.Ru → ∀ F : ℝ → ℝ, IsSol1 P F → ConcaveOn ℝ (Ici 0) F →
      DifferentiableOn ℝ F (Ici 0) → (∀ w : ℝ, 0 ≤ w → -1 ≤ derivWithin F (Ici 0) w) →
      ∀ w Hu Ho : ℝ, 0 ≤ w → P.Ru ≤ Hu → P.beta ≤ P.p * Hu + (1 - P.p) * Ho → 0 ≤ w + Ho →
        Phi P F w Hu Ho ≤ 0) ∧
    (P.mu * P.p * P.Ru < P.c ∧ P.c < P.mu * P.Ru → ∀ F : ℝ → ℝ, IsSol2 P F →
      ConcaveOn ℝ (Ici 0) F →
      DifferentiableOn ℝ F (Ici 0) → (∀ w : ℝ, 0 ≤ w → -1 ≤ derivWithin F (Ici 0) w) →
      ∀ w Hu Ho : ℝ, 0 ≤ w → P.Ru ≤ Hu → P.beta ≤ P.p * Hu + (1 - P.p) * Ho → 0 ≤ w + Ho →
        Phi P F w Hu Ho ≤ 0) ∧
    (P.mu * P.Ru ≤ P.c → ∀ F : ℝ → ℝ, IsSol3 P F → ConcaveOn ℝ (Ici 0) F →
      DifferentiableOn ℝ F (Ici 0) → (∀ w : ℝ, 0 ≤ w → -1 ≤ derivWithin F (Ici 0) w) →
      ∀ w Hu Ho : ℝ, 0 ≤ w → P.Ru ≤ Hu → P.beta ≤ P.p * Hu + (1 - P.p) * Ho → 0 ≤ w + Ho →
        Phi P F w Hu Ho ≤ 0) := by
  have hr := P.r_pos
  have hmu := P.mu_pos
  have hp := P.p_pos
  have hp1 := P.p_lt_one
  have hR := P.Ru_pos
  have hc := P.c_pos
  have hV : P.r * P.Vbar = P.mu * P.p * P.Ru + P.mu * (1 - P.p) * P.Ro - P.c := by
    unfold Params.Vbar; first | (field_simp; done) | (field_simp; ring)
  have hbeta : P.mu * P.beta = P.c := by unfold Params.beta; field_simp
  have hbeta0 : 0 < P.beta := by unfold Params.beta; positivity
  have hw1 : P.r * P.wbar1 = P.mu * P.p * P.Ru := by unfold Params.wbar1; field_simp
  have hw2 : P.r * P.wbar2 = P.c := by unfold Params.wbar2; field_simp
  have hw3 : P.r * P.wbar3 = P.c := by unfold Params.wbar3 Params.wbar2; field_simp
  have hw1p : 0 < P.wbar1 := by unfold Params.wbar1; positivity
  have hw2p : 0 < P.wbar2 := by unfold Params.wbar2; positivity
  have hw3p : 0 < P.wbar3 := by unfold Params.wbar3 Params.wbar2; positivity
  refine ⟨?_, ?_, ?_⟩
  · -- Scenario 1
    intro hcase F hF hcc hd hge w Hu Ho hw hHu hIC hHo
    obtain ⟨hcF, hext, hode, -⟩ := hF
    have hid := ident (J := fun w => P.mu * P.p * (F (w + P.Ru) - F w)) (A := P.r * P.Vbar)
      hr hw1p hcc hd hge hext
      (fun w hw => by rw [shift_ext hext hw hR.le, shift_ext hext le_rfl hR.le])
      (by
        refine ((continuousWithinAt_const.mul (cont0 hcF hw1p.le)).sub
          (continuousWithinAt_const.mul ((cont_shift hcF hw1p.le hR.le).sub
            (cont0 hcF hw1p.le)))))
      (fun w hw => by rw [(hode w hw).2])
      w hw
    set D := derivWithin F (Ici 0)
    have t1 := tangent hcc hd (x := w + P.Ru) (y := w + Hu) (by linarith) (by linarith)
    have t2 := tangent hcc hd (x := w) (y := w + Ho) hw hHo
    have a1 := anti hcc hd (x := w) (y := w + P.Ru) hw (by linarith)
    have k1 : 0 ≤ (D w - D (w + P.Ru)) * (Hu - P.Ru) :=
      mul_nonneg (by linarith) (by linarith)
    have hPhi : Phi P F w Hu Ho = P.mu * P.p * (F (w + Hu) - F (w + P.Ru) - D w * (Hu - P.Ru))
        + P.mu * (1 - P.p) * (F (w + Ho) - F w - D w * Ho) := by
      unfold Phi
      have e1 : P.mu * P.p * P.Ru = P.r * P.wbar1 := hw1.symm
      linear_combination (-1 : ℝ) * hid - hV + (D w) * hw1
    rw [hPhi]
    have q1 : F (w + Hu) - F (w + P.Ru) - D w * (Hu - P.Ru) ≤ 0 := by
      have : D (w + P.Ru) * (w + Hu - (w + P.Ru)) = D (w + P.Ru) * (Hu - P.Ru) := by ring
      nlinarith
    have q2 : F (w + Ho) - F w - D w * Ho ≤ 0 := by
      have : D w * (w + Ho - w) = D w * Ho := by ring
      linarith
    have m1 : 0 < P.mu * P.p := by positivity
    have m2 : 0 < P.mu * (1 - P.p) := mul_pos hmu (by linarith)
    nlinarith
  · -- Scenario 2
    intro ⟨hcase, hcase'⟩ F hF hcc hd hge w Hu Ho hw hHu hIC hHo
    obtain ⟨hcF, hext, hode, -⟩ := hF
    have hbO : P.p * P.Ru + (1 - P.p) * P.betaO = P.beta := by
      have h1p : (1 - P.p) ≠ 0 := by linarith
      unfold Params.betaO; field_simp; ring
    have hbO0 : 0 < P.betaO := by
      unfold Params.betaO
      apply div_pos _ (by linarith)
      have : P.mu * (P.p * P.Ru) < P.mu * P.beta := by rw [hbeta]; linarith
      have := lt_of_mul_lt_mul_left this hmu.le
      linarith
    have hbOR : P.betaO ≤ P.Ru := by
      have : P.mu * P.beta < P.mu * P.Ru := by rw [hbeta]; linarith
      have hb := lt_of_mul_lt_mul_left this hmu.le
      nlinarith
    have hid := ident (J := fun w => P.mu * P.p * (F (w + P.Ru) - F w)
        + P.mu * (1 - P.p) * (F (w + P.betaO) - F w)) (A := P.r * P.Vbar)
      hr hw2p hcc hd hge hext
      (fun w hw => by
        rw [shift_ext hext hw hR.le, shift_ext hext le_rfl hR.le,
          shift_ext hext hw hbO0.le, shift_ext hext le_rfl hbO0.le])
      (by
        refine ((continuousWithinAt_const.mul (cont0 hcF hw2p.le)).sub
          ((continuousWithinAt_const.mul ((cont_shift hcF hw2p.le hR.le).sub
            (cont0 hcF hw2p.le))).add
          (continuousWithinAt_const.mul ((cont_shift hcF hw2p.le hbO0.le).sub
            (cont0 hcF hw2p.le))))))
      (fun w hw => by rw [(hode w hw).2]; ring)
      w hw
    set D := derivWithin F (Ici 0)
    have t1 := tangent hcc hd (x := w + P.Ru) (y := w + Hu) (by linarith) (by linarith)
    have t2 := tangent hcc hd (x := w + P.betaO) (y := w + Ho) (by linarith) hHo
    have a1 := anti hcc hd (x := w + P.betaO) (y := w + P.Ru) (by linarith) (by linarith)
    have a2 := anti hcc hd (x := w) (y := w + P.betaO) hw (by linarith)
    have hPhi : Phi P F w Hu Ho = P.mu * P.p * (F (w + Hu) - F (w + P.Ru) - D w * (Hu - P.Ru))
        + P.mu * (1 - P.p) * (F (w + Ho) - F (w + P.betaO) - D w * (Ho - P.betaO)) := by
      unfold Phi
      have hc' : P.c = P.mu * P.p * P.Ru + P.mu * (1 - P.p) * P.betaO := by
        rw [← hbeta, ← hbO]; ring
      linear_combination (-1 : ℝ) * hid - hV + (D w) * hw2 + (D w) * hc'
    rw [hPhi]
    have hICo : 0 ≤ P.p * (Hu - P.Ru) + (1 - P.p) * (Ho - P.betaO) := by linarith
    have hICo : 0 ≤ P.p * (Hu - P.Ru) + (1 - P.p) * (Ho - P.betaO) := by linarith
    have e1 : D (w + P.Ru) * (w + Hu - (w + P.Ru)) = D (w + P.Ru) * (Hu - P.Ru) := by ring
    have e2 : D (w + P.betaO) * (w + Ho - (w + P.betaO)) = D (w + P.betaO) * (Ho - P.betaO) := by
      ring
    have k1 : 0 ≤ (D (w + P.betaO) - D (w + P.Ru)) * (Hu - P.Ru) :=
      mul_nonneg (by linarith) (by linarith)
    have k2 : 0 ≤ (D w - D (w + P.betaO)) * (P.p * (Hu - P.Ru) + (1 - P.p) * (Ho - P.betaO)) :=
      mul_nonneg (by linarith) hICo
    have m1 : 0 < P.mu * P.p := by positivity
    have m2 : 0 < P.mu * (1 - P.p) := mul_pos hmu (by linarith)
    set X := F (w + Hu) - F (w + P.Ru) - D w * (Hu - P.Ru) with hX
    set Y := F (w + Ho) - F (w + P.betaO) - D w * (Ho - P.betaO) with hY
    have q1 : X ≤ (D (w + P.Ru) - D w) * (Hu - P.Ru) := by
      have : (D (w + P.Ru) - D w) * (Hu - P.Ru) = D (w + P.Ru) * (Hu - P.Ru) - D w * (Hu - P.Ru) := by
        ring
      rw [this, hX]; linarith
    have q2 : Y ≤ (D (w + P.betaO) - D w) * (Ho - P.betaO) := by
      have : (D (w + P.betaO) - D w) * (Ho - P.betaO)
          = D (w + P.betaO) * (Ho - P.betaO) - D w * (Ho - P.betaO) := by ring
      rw [this, hY]; linarith
    have q1' := mul_le_mul_of_nonneg_left q1 m1.le
    have q2' := mul_le_mul_of_nonneg_left q2 m2.le
    have hsum : P.mu * P.p * ((D (w + P.Ru) - D w) * (Hu - P.Ru))
        + P.mu * (1 - P.p) * ((D (w + P.betaO) - D w) * (Ho - P.betaO))
        = -(P.mu * (P.p * ((D (w + P.betaO) - D (w + P.Ru)) * (Hu - P.Ru))
          + (D w - D (w + P.betaO)) * (P.p * (Hu - P.Ru) + (1 - P.p) * (Ho - P.betaO)))) := by ring
    have hfin : 0 ≤ P.mu * (P.p * ((D (w + P.betaO) - D (w + P.Ru)) * (Hu - P.Ru))
          + (D w - D (w + P.betaO)) * (P.p * (Hu - P.Ru) + (1 - P.p) * (Ho - P.betaO))) := by
      positivity
    linarith
  · -- Scenario 3
    intro hcase F hF hcc hd hge w Hu Ho hw hHu hIC hHo
    obtain ⟨hcF, hext, hode, -⟩ := hF
    have hid := ident (J := fun w => P.mu * (F (w + P.beta) - F w)) (A := P.r * P.Vbar)
      hr hw3p hcc hd hge hext
      (fun w hw => by rw [shift_ext hext hw hbeta0.le, shift_ext hext le_rfl hbeta0.le])
      (by
        refine ((continuousWithinAt_const.mul (cont0 hcF hw3p.le)).sub
          (continuousWithinAt_const.mul ((cont_shift hcF hw3p.le hbeta0.le).sub
            (cont0 hcF hw3p.le)))))
      (fun w hw => by linarith [(hode w hw).2])
      w hw
    set D := derivWithin F (Ici 0)
    have t1 := tangent hcc hd (x := w + P.beta) (y := w + Hu) (by linarith) (by linarith)
    have t2 := tangent hcc hd (x := w + P.beta) (y := w + Ho) (by linarith) hHo
    have a1 := anti hcc hd (x := w) (y := w + P.beta) hw (by linarith)
    have hPhi : Phi P F w Hu Ho = P.mu * P.p * (F (w + Hu) - F (w + P.beta) - D w * (Hu - P.beta))
        + P.mu * (1 - P.p) * (F (w + Ho) - F (w + P.beta) - D w * (Ho - P.beta)) := by
      unfold Phi
      linear_combination (-1 : ℝ) * hid - hV + (D w) * hw3 + (D w) * hbeta.symm
    rw [hPhi]
    have e1 : D (w + P.beta) * (w + Hu - (w + P.beta)) = D (w + P.beta) * (Hu - P.beta) := by ring
    have e2 : D (w + P.beta) * (w + Ho - (w + P.beta)) = D (w + P.beta) * (Ho - P.beta) := by ring
    have hICo : 0 ≤ P.p * (Hu - P.beta) + (1 - P.p) * (Ho - P.beta) := by linarith
    have m1 : 0 < P.mu * P.p := by positivity
    have m2 : 0 < P.mu * (1 - P.p) := mul_pos hmu (by linarith)
    set X := F (w + Hu) - F (w + P.beta) - D w * (Hu - P.beta) with hX
    set Y := F (w + Ho) - F (w + P.beta) - D w * (Ho - P.beta) with hY
    have q1 : X ≤ (D (w + P.beta) - D w) * (Hu - P.beta) := by
      have : (D (w + P.beta) - D w) * (Hu - P.beta)
          = D (w + P.beta) * (Hu - P.beta) - D w * (Hu - P.beta) := by ring
      rw [this, hX]; linarith
    have q2 : Y ≤ (D (w + P.beta) - D w) * (Ho - P.beta) := by
      have : (D (w + P.beta) - D w) * (Ho - P.beta)
          = D (w + P.beta) * (Ho - P.beta) - D w * (Ho - P.beta) := by ring
      rw [this, hY]; linarith
    have q1' := mul_le_mul_of_nonneg_left q1 m1.le
    have q2' := mul_le_mul_of_nonneg_left q2 m2.le
    have hsum : P.mu * P.p * ((D (w + P.beta) - D w) * (Hu - P.beta))
        + P.mu * (1 - P.p) * ((D (w + P.beta) - D w) * (Ho - P.beta))
        = -(P.mu * ((D w - D (w + P.beta)) * (P.p * (Hu - P.beta) + (1 - P.p) * (Ho - P.beta)))) := by
      ring
    have hfin : 0 ≤ P.mu * ((D w - D (w + P.beta)) * (P.p * (Hu - P.beta) + (1 - P.p) * (Ho - P.beta))) :=
      mul_nonneg hmu.le (mul_nonneg (by linarith) hICo)
    linarith
