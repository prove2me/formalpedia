-- Prove2me | solution 1 for ExtrapBias.Beliefs.extrapolation_bias
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T22:04:23.904073+00:00
-- url     : https://prove2.me/submissions/f44006cd-b3f6-402e-86a6-85a6850d8a7b

import Mathlib
import Definitions.Def_ExtrapBias_Beliefs_Model

set_option autoImplicit false

namespace ExtrapBiasCcc

open ExtrapBias.Beliefs

/-- Facts about a differentiable function concave on `[0, ∞)`. -/
lemma concave_facts (F : ℝ → ℝ) (hc : ConcaveOn ℝ (Set.Ici 0) F)
    (hd : Differentiable ℝ F) :
    AntitoneOn (deriv F) (Set.Ici 0) ∧
    (∀ m : ℝ, 0 ≤ m → F 0 ≤ F m - deriv F m * m) := by
  have hcv : ConvexOn ℝ (Set.Ici 0) (-F) := hc.neg
  have hdn : ∀ x, deriv (-F) x = - deriv F x := fun x => deriv.neg
  refine ⟨?_, ?_⟩
  · have hm := hcv.monotoneOn_deriv (fun x _ => (hd x).neg)
    intro x hx y hy hxy
    have := hm hx hy hxy
    rw [hdn, hdn] at this
    linarith
  · intro m hm
    rcases hm.eq_or_lt with h | h
    · subst h; simp
    · have := hcv.slope_le_deriv ((Set.mem_Ici.mpr le_rfl)) (Set.mem_Ici.mpr hm) h ((hd m).neg)
      rw [hdn, slope_def_field] at this
      simp only [Pi.neg_apply] at this
      rw [sub_zero] at this
      rw [div_le_iff₀ h] at this
      nlinarith

lemma deriv2_nonpos (F : ℝ → ℝ) (hA : AntitoneOn (deriv F) (Set.Ici 0))
    (hdd : Differentiable ℝ (deriv F)) (m : ℝ) (hm : 0 ≤ m) :
    deriv (deriv F) m ≤ 0 := by
  have h1 : AntitoneOn (deriv F) (Set.Ici m) :=
    hA.mono (Set.Ici_subset_Ici.mpr hm)
  have h2 := h1.derivWithin_nonpos (x := m)
  rwa [(hdd m).derivWithin (uniqueDiffOn_Ici m m (Set.mem_Ici.mpr le_rfl))] at h2

/-- Derivative of the worst-case angle. -/
lemma phi_hasDeriv (p : Params) (F : ℝ → ℝ) (hd : Differentiable ℝ F)
    (hdd : Differentiable ℝ (deriv F)) (m : ℝ)
    (hD : 0 < F m - deriv F m * m) (hFm : 0 < F m) :
    ∃ φ' : ℝ, HasDerivAt (phiOpt p F) φ' m ∧
      (deriv (deriv F) m ≤ 0 → φ' ≤ 0) ∧ (deriv (deriv F) m < 0 → φ' < 0) := by
  set c : ℝ := p.sigY * p.kapT / (p.sigD * p.kapP) with hcdef
  have hc : 0 < c := div_pos (mul_pos p.sigY_pos p.kapT_pos) (mul_pos p.sigD_pos p.kapP_pos)
  have h1 : HasDerivAt (deriv F) (deriv (deriv F) m) m := (hdd m).hasDerivAt
  have h0 : HasDerivAt F (deriv F m) m := (hd m).hasDerivAt
  have hDd : HasDerivAt (fun x => F x - deriv F x * x)
      (deriv F m - (deriv (deriv F) m * m + deriv F m * 1)) m :=
    h0.sub (h1.mul (hasDerivAt_id m))
  have hq := (h1.div hDd hD.ne').mul_const c
  have ha := hq.arctan
  refine ⟨_, ha, ?_, ?_⟩
  · intro hneg
    have hN : deriv (deriv F) m * (F m - deriv F m * m) -
        deriv F m * (deriv F m - (deriv (deriv F) m * m + deriv F m * 1)) =
        deriv (deriv F) m * F m := by ring
    rw [hN]
    apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
    apply mul_nonpos_of_nonpos_of_nonneg _ hc.le
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    exact mul_nonpos_of_nonpos_of_nonneg hneg hFm.le
  · intro hneg
    have hN : deriv (deriv F) m * (F m - deriv F m * m) -
        deriv F m * (deriv F m - (deriv (deriv F) m * m + deriv F m * 1)) =
        deriv (deriv F) m * F m := by ring
    rw [hN]
    apply mul_neg_of_pos_of_neg (by positivity)
    apply mul_neg_of_neg_of_pos _ hc
    apply div_neg_of_neg_of_pos _ (by positivity)
    exact mul_neg_of_neg_of_pos hneg hFm

/-- Uniqueness of the minimizing angle. -/
lemma bracket_min (p : Params) (F0 F1 F2 m i φ : ℝ) (hA : 0 < F0 - F1 * m) (hB : 0 < F1)
    (hφ : φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi)) :
    let φ0 := Real.arctan ((F1 / (F0 - F1 * m)) * (p.sigY * p.kapT / (p.sigD * p.kapP)))
    bracket25 p F0 F1 F2 m i φ0 ≤ bracket25 p F0 F1 F2 m i φ ∧
      (bracket25 p F0 F1 F2 m i φ = bracket25 p F0 F1 F2 m i φ0 → φ = φ0) := by
  intro φ0
  set a : ℝ := (F0 - F1 * m) * (p.sigD * p.kapP) with ha
  set b : ℝ := F1 * (p.sigY * p.kapT) with hb
  have hapos : 0 < a := mul_pos hA (mul_pos p.sigD_pos p.kapP_pos)
  have ht : F1 / (F0 - F1 * m) * (p.sigY * p.kapT / (p.sigD * p.kapP)) = b / a := by
    rw [ha, hb]
    have := p.sigD_pos.ne'
    have := p.kapP_pos.ne'
    field_simp
  have hφ0 : φ0 = Real.arctan (b / a) := by simp only [φ0, ht]
  have hc0 : 0 < Real.cos φ0 := by
    rw [hφ0]; exact Real.cos_arctan_pos _
  have htan : Real.tan φ0 = b / a := by rw [hφ0, Real.tan_arctan]
  have hbs : b = a * Real.sin φ0 / Real.cos φ0 := by
    rw [mul_div_assoc, ← Real.tan_eq_sin_div_cos, htan]
    field_simp
  have hdiff : bracket25 p F0 F1 F2 m i φ - bracket25 p F0 F1 F2 m i φ0 =
      a / Real.cos φ0 * (1 - Real.cos (φ - φ0)) := by
    have hsc := Real.sin_sq_add_cos_sq φ0
    rw [Real.cos_sub]
    simp only [bracket25]
    have e1 : a * Real.cos φ0 + b * Real.sin φ0 = a / Real.cos φ0 := by
      rw [hbs]; field_simp; nlinarith [hsc]
    have e2 : a / Real.cos φ0 * (1 - (Real.cos φ * Real.cos φ0 + Real.sin φ * Real.sin φ0))
        = a / Real.cos φ0 - a * Real.cos φ - b * Real.sin φ := by
      rw [hbs]; field_simp; ring
    rw [e2, ← e1, ha, hb]
    ring
  have hpos : 0 < a / Real.cos φ0 := div_pos hapos hc0
  refine ⟨?_, ?_⟩
  · have := Real.cos_le_one (φ - φ0)
    nlinarith [hdiff]
  · intro heq
    have h1 : Real.cos (φ - φ0) = 1 := by
      have : a / Real.cos φ0 * (1 - Real.cos (φ - φ0)) = 0 := by rw [← hdiff, heq]; ring
      rcases mul_eq_zero.mp this with h | h
      · linarith
      · linarith
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).mp h1
    have hlo : 0 < φ0 := by
      rw [hφ0]; apply Real.arctan_pos.mpr (div_pos ?_ hapos)
      exact mul_pos hB (mul_pos p.sigY_pos p.kapT_pos)
    have hhi : φ0 < Real.pi / 2 := by rw [hφ0]; exact Real.arctan_lt_pi_div_two _
    have hpi := Real.pi_pos
    have hn1 : (n : ℝ) < 1 := by
      by_contra hc
      push Not at hc
      nlinarith [hφ.2]
    have hn2 : (-1 : ℝ) < n := by
      by_contra hc
      push Not at hc
      nlinarith [hφ.1]
    have hn1' : n < 1 := by exact_mod_cast hn1
    have hn2' : -1 < n := by exact_mod_cast hn2
    have : n = 0 := by omega
    subst this
    simp at hn
    linarith

end ExtrapBiasCcc

open ExtrapBias.Beliefs in
theorem solution (p : Params) (qA iA φA mstar : ℝ) (F : ℝ → ℝ)
    (hA : IsAmbBenchmark p qA iA φA)
    (hF : IsScaledValue p qA mstar F) :
    ∀ m ∈ Set.Icc 0 mstar,
      phiOpt p F m ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) ∧
      (∀ i : ℝ, ∀ φ ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        bracket25 p (F m) (deriv F m) (deriv (deriv F) m) m i (phiOpt p F m) ≤
          bracket25 p (F m) (deriv F m) (deriv (deriv F) m) m i φ ∧
        (bracket25 p (F m) (deriv F m) (deriv (deriv F) m) m i φ =
          bracket25 p (F m) (deriv F m) (deriv (deriv F) m) m i (phiOpt p F m) →
          φ = phiOpt p F m)) ∧
      0 ≤ sensPP p F m ∧ sensPT p F m ≤ 0 ∧
      sensTP p F m ≤ 0 ∧ 0 ≤ sensTT p F m ∧
      (deriv (deriv F) m < 0 →
        sensPT p F m < 0 ∧ 0 < sensTT p F m ∧
        (0 < m → 0 < sensPP p F m ∧ sensTP p F m < 0)) := by
  intro m hm
  obtain ⟨hqA, -⟩ := hA
  obtain ⟨_, hC2, hmono, hconc, -, hd1, -, hF0, -⟩ := hF
  have hd : Differentiable ℝ F := hC2.differentiable (by norm_num)
  have hdd : Differentiable ℝ (deriv F) := by
    have h2 : ContDiff ℝ (1 + 1) F := by convert hC2 using 1; rfl
    have h := contDiff_succ_iff_deriv.mp h2
    exact h.2.2.differentiable (by norm_num)
  obtain ⟨hanti, htan⟩ := ExtrapBiasCcc.concave_facts F hconc hd
  have hm0 : 0 ≤ m := hm.1
  have hF1 : 1 ≤ deriv F m := by
    rw [← hd1]; exact hanti (Set.mem_Ici.mpr hm0) (Set.mem_Ici.mpr (hm0.trans hm.2)) hm.2
  have hF0pos : 0 < F 0 := lt_of_lt_of_le (mul_pos p.omega_pos hqA) hF0
  have hD : 0 < F m - deriv F m * m := lt_of_lt_of_le hF0pos (htan m hm0)
  have hFm : 0 < F m := lt_of_lt_of_le hF0pos
    (hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hm0) hm0)
  have hF2 : deriv (deriv F) m ≤ 0 := ExtrapBiasCcc.deriv2_nonpos F hanti hdd m hm0
  -- angle bounds
  have hx : 0 < deriv F m / (F m - deriv F m * m) * (p.sigY * p.kapT / (p.sigD * p.kapP)) :=
    mul_pos (div_pos (by linarith) hD)
      (div_pos (mul_pos p.sigY_pos p.kapT_pos) (mul_pos p.sigD_pos p.kapP_pos))
  have hφlo : 0 < phiOpt p F m := Real.arctan_pos.mpr hx
  have hφhi : phiOpt p F m < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hsin : 0 < Real.sin (phiOpt p F m) :=
    Real.sin_pos_of_pos_of_lt_pi hφlo (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos (phiOpt p F m) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hφhi⟩
  obtain ⟨φ', hφ', hφn, hφs⟩ := ExtrapBiasCcc.phi_hasDeriv p F hd hdd m hD hFm
  have hPd : deriv (hP p F) m = -p.kapP * (-Real.sin (phiOpt p F m) * φ') := by
    have : hP p F = fun x => -p.kapP * Real.cos (phiOpt p F x) := rfl
    rw [this]
    exact (hφ'.cos.const_mul (-p.kapP)).deriv
  have hTd : deriv (hT p F) m = -p.kapT * (Real.cos (phiOpt p F m) * φ') := by
    have : hT p F = fun x => -p.kapT * Real.sin (phiOpt p F x) := rfl
    rw [this]
    exact (hφ'.sin.const_mul (-p.kapT)).deriv
  have hφ'n := hφn hF2
  have kP := p.kapP_pos
  have kT := p.kapT_pos
  have sD := p.sigD_pos
  have sY := p.sigY_pos
  simp only [sensPP, sensPT, sensTP, sensTT, hPd, hTd]
  refine ⟨⟨hφlo, hφhi⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i φ hφ
    exact ExtrapBiasCcc.bracket_min p (F m) (deriv F m) (deriv (deriv F) m) m i φ
      (by simpa using hD) (by linarith) hφ
  · have : 0 ≤ p.kapP * Real.sin (phiOpt p F m) * (-φ') * m * p.sigD := by
      have := mul_pos kP hsin
      have : 0 ≤ -φ' := by linarith
      positivity
    nlinarith
  · have : 0 ≤ p.kapP * Real.sin (phiOpt p F m) * (-φ') * p.sigY := by
      have : 0 ≤ -φ' := by linarith
      positivity
    nlinarith
  · have : 0 ≤ p.kapT * Real.cos (phiOpt p F m) * (-φ') * m * p.sigD := by
      have : 0 ≤ -φ' := by linarith
      positivity
    nlinarith
  · have : 0 ≤ p.kapT * Real.cos (phiOpt p F m) * (-φ') * p.sigY := by
      have : 0 ≤ -φ' := by linarith
      positivity
    nlinarith
  · intro h2
    have hs := hφs h2
    have hnp : 0 < -φ' := by linarith
    refine ⟨?_, ?_, ?_⟩
    · have : 0 < p.kapP * Real.sin (phiOpt p F m) * (-φ') * p.sigY := by positivity
      nlinarith
    · have : 0 < p.kapT * Real.cos (phiOpt p F m) * (-φ') * p.sigY := by positivity
      nlinarith
    · intro hmpos
      refine ⟨?_, ?_⟩
      · have : 0 < p.kapP * Real.sin (phiOpt p F m) * (-φ') * m * p.sigD := by positivity
        nlinarith
      · have : 0 < p.kapT * Real.cos (phiOpt p F m) * (-φ') * m * p.sigD := by positivity
        nlinarith
