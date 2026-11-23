-- Prove2me | solution 1 for DelaunayStretch.lemma_4_2_range_of_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T01:05:20.560183+00:00
-- url     : https://prove2.me/submissions/4537bd20-ae90-4640-b9c6-f05a76a23016

import Mathlib
import Definitions.Def_DelaunayStretch_SigmaSet

open DelaunayStretch Complex

namespace DelaunayStretch
namespace L42

theorem arg_eq_of_re_im (z : ℂ) (r θ : ℝ) (hr : 0 < r) (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hre : z.re = r * Real.cos θ) (him : z.im = r * Real.sin θ) : Complex.arg z = θ := by
  have : z = (r : ℂ) * (Complex.cos θ + Complex.sin θ * Complex.I) := by
    apply Complex.ext
    · simp [hre, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    · simp [him, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [this, Complex.arg_mul_cos_add_sin_mul_I hr hθ]

theorem dist_sq_eq (z w : ℂ) : dist z w ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
  rw [Complex.dist_eq_re_im, Real.sq_sqrt (by positivity)]

theorem upperAngle_eq (O : Disk) (p : ℂ) (t : ℝ) (hr : 0 < O.radius)
    (ht1 : -(Real.pi / 2) < t) (ht2 : t ≤ 3 * Real.pi / 2)
    (hre : p.re = O.center.re + O.radius * Real.cos t)
    (him : p.im = O.center.im + O.radius * Real.sin t) : O.upperAngle p = t := by
  unfold Disk.upperAngle
  rw [arg_eq_of_re_im _ O.radius (t - Real.pi / 2) hr ⟨by linarith, by linarith⟩]
  · ring
  · simp [Real.cos_sub_pi_div_two, him]
  · simp [Real.sin_sub_pi_div_two, hre]

theorem lowerAngle_eq (O : Disk) (p : ℂ) (t : ℝ) (hr : 0 < O.radius)
    (ht1 : Real.pi / 2 < t) (ht2 : t ≤ 5 * Real.pi / 2)
    (hre : p.re = O.center.re + O.radius * Real.cos t)
    (him : p.im = O.center.im + O.radius * Real.sin t) : O.lowerAngle p = t := by
  unfold Disk.lowerAngle
  have hc : Real.cos (t - 3 * Real.pi / 2) = - Real.sin t := by
    rw [show t - 3 * Real.pi / 2 = (t - Real.pi / 2) - Real.pi by ring, Real.cos_sub_pi,
      Real.cos_sub_pi_div_two]
  have hs : Real.sin (t - 3 * Real.pi / 2) = Real.cos t := by
    rw [show t - 3 * Real.pi / 2 = (t - Real.pi / 2) - Real.pi by ring, Real.sin_sub_pi,
      Real.sin_sub_pi_div_two, neg_neg]
  rw [arg_eq_of_re_im _ O.radius (t - 3 * Real.pi / 2) hr ⟨by linarith, by linarith⟩]
  · ring
  · simp [hc, him]
  · simp [hs, hre]

/-- `sin a < sin x` for `a ∈ (-π/2, π/2)` and `x ∈ (-π/2, 3π/2)`. -/
theorem sin_lt_sin_iff' {a x : ℝ} (ha1 : -(Real.pi / 2) < a) (ha2 : a < Real.pi / 2)
    (hx1 : -(Real.pi / 2) < x) (hx2 : x < 3 * Real.pi / 2) :
    Real.sin a < Real.sin x ↔ a < x ∧ x < Real.pi - a := by
  have hm := Real.strictMonoOn_sin
  have haI : a ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨ha1.le, ha2.le⟩
  rcases le_total x (Real.pi / 2) with hx | hx
  · have hxI : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨hx1.le, hx⟩
    rw [hm.lt_iff_lt haI hxI]
    constructor
    · intro h; exact ⟨h, by linarith⟩
    · intro h; exact h.1
  · have hxI : Real.pi - x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨by linarith, by linarith⟩
    rw [← Real.sin_pi_sub x, hm.lt_iff_lt haI hxI]
    constructor
    · intro h; exact ⟨by linarith, by linarith⟩
    · intro h; linarith [h.2]


theorem circ_eq {O : Disk} {p : ℂ} (hp : p ∈ O.boundary) :
    (p.re - O.center.re) ^ 2 + (p.im - O.center.im) ^ 2 = O.radius ^ 2 := by
  have h : dist p O.center = O.radius := hp
  rw [← dist_sq_eq, h]

theorem gamma_facts (s : GateState) (hs : s.IsGateState) :
    -s.O.radius < s.O.center.im ∧ s.O.center.im < s.O.radius ∧
    -(Real.pi / 2) < s.gammaCoord ∧ s.gammaCoord < Real.pi / 2 ∧
    s.O.center.im = s.O.radius * Real.sin s.gammaCoord ∧
    s.O.axisHalfChord = s.O.radius * Real.cos s.gammaCoord := by
  obtain ⟨hr, ha, hb, ha0, hb0, -⟩ := hs
  have ha' := circ_eq ha
  have hb' := circ_eq hb
  set o := s.O.center
  set r := s.O.radius
  have h1 : -r < o.im := by nlinarith [sq_nonneg (s.aG.re - o.re)]
  have h2 : o.im < r := by nlinarith [sq_nonneg (s.bG.re - o.re)]
  have hx1 : -1 < o.im / r := by rw [lt_div_iff₀ hr]; linarith
  have hx2 : o.im / r < 1 := by rw [div_lt_iff₀ hr]; linarith
  have hg1 : -(Real.pi / 2) < s.gammaCoord := Real.neg_pi_div_two_lt_arcsin.mpr hx1
  have hg2 : s.gammaCoord < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hx2
  have hsin : Real.sin s.gammaCoord = o.im / r := Real.sin_arcsin hx1.le hx2.le
  have hcos : 0 < Real.cos s.gammaCoord := Real.cos_pos_of_mem_Ioo ⟨hg1, hg2⟩
  refine ⟨h1, h2, hg1, hg2, ?_, ?_⟩
  · rw [hsin]; field_simp
  · unfold Disk.axisHalfChord
    have hsq : r ^ 2 - o.im ^ 2 = (r * Real.cos s.gammaCoord) ^ 2 := by
      have := Real.sin_sq_add_cos_sq s.gammaCoord
      rw [hsin] at this
      field_simp at this
      nlinarith [this]
    rw [hsq, Real.sqrt_sq (by positivity)]

theorem phi_facts (s : GateState) (hs : s.IsGateState) :
    0 < dist s.aG s.bG ∧
    -(Real.pi / 2) < s.phiCoord ∧ s.phiCoord < Real.pi / 2 ∧
    s.aG.im - s.bG.im = dist s.aG s.bG * Real.cos s.phiCoord ∧
    s.aG.re - s.bG.re = -(dist s.aG s.bG * Real.sin s.phiCoord) := by
  obtain ⟨hr, ha, hb, ha0, hb0, -⟩ := hs
  set w := (-I) * (s.aG - s.bG) with hw
  have hwre : w.re = s.aG.im - s.bG.im := by simp [hw]
  have hwim : w.im = -(s.aG.re - s.bG.re) := by simp [hw]
  have hwn : ‖w‖ = dist s.aG s.bG := by simp [hw, Complex.dist_eq]
  have hpos : 0 < w.re := by rw [hwre]; linarith
  have habs : |Complex.arg w| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hpos)
  have hL : 0 < dist s.aG s.bG := by
    rw [← hwn]; apply norm_pos_iff.mpr; intro h; rw [h] at hpos; simp at hpos
  have e1 := Complex.norm_mul_cos_arg w
  have e2 := Complex.norm_mul_sin_arg w
  rw [hwn] at e1 e2
  refine ⟨hL, (abs_lt.mp habs).1, (abs_lt.mp habs).2, ?_, ?_⟩
  · show _ = _ * Real.cos (Complex.arg w); linarith
  · show _ = -(_ * Real.sin (Complex.arg w)); linarith

theorem offset_mul (s : GateState) (hL : 0 < dist s.aG s.bG) :
    s.offset * dist s.aG s.bG =
      (s.O.center.re - (s.aG.re + s.bG.re) / 2) * (s.aG.im - s.bG.im) -
      (s.O.center.im - (s.aG.im + s.bG.im) / 2) * (s.aG.re - s.bG.re) := by
  unfold GateState.offset GateState.normal GateState.mid
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.div_ofReal_re,
    Complex.div_ofReal_im, Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
    Complex.add_re, Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im]
  norm_num
  field_simp
  ring

theorem theta_facts (s : GateState) (hs : s.IsGateState) :
    0 < s.thetaCoord ∧ s.thetaCoord < Real.pi ∧
    s.aG.re = s.O.center.re - s.O.radius * Real.cos (s.thetaCoord - s.phiCoord) ∧
    s.aG.im = s.O.center.im + s.O.radius * Real.sin (s.thetaCoord - s.phiCoord) ∧
    s.bG.re = s.O.center.re - s.O.radius * Real.cos (s.thetaCoord + s.phiCoord) ∧
    s.bG.im = s.O.center.im - s.O.radius * Real.sin (s.thetaCoord + s.phiCoord) ∧
    dist s.aG s.bG = 2 * s.O.radius * Real.sin s.thetaCoord := by
  obtain ⟨hL, -, -, hd2, hd1⟩ := phi_facts s hs
  have hX := offset_mul s hL
  have hL2 := dist_sq_eq s.aG s.bG
  obtain ⟨hr, ha, hb, -, -, -⟩ := hs
  have ha' := circ_eq ha
  have hb' := circ_eq hb
  have hcs := Real.cos_sq_add_sin_sq s.phiCoord
  have hθdef : s.thetaCoord = Real.arccos (s.offset / s.O.radius) := rfl
  set L := dist s.aG s.bG
  set X := s.offset
  set c := Real.cos s.phiCoord
  set sn := Real.sin s.phiCoord
  set θ := s.thetaCoord
  set r := s.O.radius
  set a1 := s.aG.re
  set a2 := s.aG.im
  set b1 := s.bG.re
  set b2 := s.bG.im
  set o1 := s.O.center.re
  set o2 := s.O.center.im
  set P := o1 - (a1 + b1) / 2 with hP
  set Q := o2 - (a2 + b2) / 2 with hQ
  have hXdef : X = P * c + Q * sn := by
    have h : L * (X - (P * c + Q * sn)) = 0 := by
      rw [hd2, hd1] at hX; linear_combination hX
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hL.ne'
    · linarith
  have hY : 2 * sn * P - 2 * c * Q = 0 := by
    have h : L * (2 * sn * P - 2 * c * Q) = 0 := by
      have e : (a1 - b1) * (a1 + b1 - 2 * o1) + (a2 - b2) * (a2 + b2 - 2 * o2) = 0 := by
        linear_combination ha' - hb'
      rw [hd2, hd1] at e
      rw [hP, hQ]; linear_combination e
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hL.ne'
    · exact h
  have ha1 : a1 = o1 - X * c - L / 2 * sn := by
    linear_combination (1/2) * hd1 + c * hXdef + P * hcs - (sn/2) * hY
  have ha2 : a2 = o2 + L / 2 * c - X * sn := by
    linear_combination (1/2) * hd2 + sn * hXdef + Q * hcs + (c/2) * hY
  have hb1 : b1 = o1 + L / 2 * sn - X * c := by
    linear_combination (-1/2) * hd1 + c * hXdef + P * hcs - (sn/2) * hY
  have hb2 : b2 = o2 - L / 2 * c - X * sn := by
    linear_combination (-1/2) * hd2 + sn * hXdef + Q * hcs + (c/2) * hY
  have hrr : X ^ 2 + L ^ 2 / 4 = r ^ 2 := by
    rw [ha1, ha2] at ha'
    linear_combination ha' - (X ^ 2 + L ^ 2 / 4) * hcs
  have hXr : -r < X ∧ X < r := abs_lt_of_sq_lt_sq' (by nlinarith) hr.le
  have hx1 : -1 < X / r := by rw [lt_div_iff₀ hr]; linarith
  have hx2 : X / r < 1 := by rw [div_lt_iff₀ hr]; linarith
  have hcosθ : Real.cos θ = X / r := by rw [hθdef]; exact Real.cos_arccos hx1.le hx2.le
  have hsinθ : Real.sin θ = L / (2 * r) := by
    rw [hθdef, Real.sin_arccos]
    have : 1 - (X / r) ^ 2 = (L / (2 * r)) ^ 2 := by
      field_simp; linear_combination (-4) * hrr
    rw [this, Real.sqrt_sq (by positivity)]
  refine ⟨Real.arccos_pos.mpr hx2, Real.arccos_lt_pi.mpr hx1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Real.cos_sub, hcosθ, hsinθ, ha1]; field_simp; ring
  · rw [Real.sin_sub, hcosθ, hsinθ, ha2]; field_simp; ring
  · rw [Real.cos_add, hcosθ, hsinθ, hb1]; field_simp; ring
  · rw [Real.sin_add, hcosθ, hsinθ, hb2]; field_simp; ring
  · rw [hsinθ]; field_simp

theorem part4 (s : GateState) (hs : s.IsGateState) :
      s.O.upperArcLength s.O.wMinus s.O.wPlus = s.O.radius * (Real.pi + 2 * s.gammaCoord) ∧
      s.O.lowerArcLength s.O.wMinus s.O.wPlus = s.O.radius * (Real.pi - 2 * s.gammaCoord) ∧
      s.O.upperArcLength s.O.wMinus s.aG =
        s.O.radius * (s.thetaCoord + s.gammaCoord - s.phiCoord) ∧
      s.O.lowerArcLength s.O.wMinus s.bG =
        s.O.radius * (s.thetaCoord - s.gammaCoord + s.phiCoord) ∧
      s.O.upperArcLength s.O.wMinus s.aG + s.O.lowerArcLength s.O.wMinus s.bG =
        s.O.radius * (2 * s.thetaCoord) ∧
      s.O.wMinus.re = s.O.center.re - s.O.radius * Real.cos s.gammaCoord ∧
      s.O.wPlus.re = s.O.center.re + s.O.radius * Real.cos s.gammaCoord ∧
      s.crossing.re - s.O.center.re =
        s.O.radius * (Real.sin s.gammaCoord * Real.sin s.phiCoord - Real.cos s.thetaCoord) /
          Real.cos s.phiCoord := by
  obtain ⟨-, -, hg1, hg2, ho2, hhalf⟩ := gamma_facts s hs
  obtain ⟨-, hp1, hp2, -, -⟩ := phi_facts s hs
  obtain ⟨ht1, ht2, ha1, ha2, hb1, hb2, -⟩ := theta_facts s hs
  have hr : 0 < s.O.radius := hs.1
  have hcs := Real.cos_sq_add_sin_sq s.phiCoord
  have hcpos : 0 < Real.cos s.phiCoord := Real.cos_pos_of_mem_Ioo ⟨hp1, hp2⟩
  have hspos : 0 < Real.sin s.thetaCoord := Real.sin_pos_of_pos_of_lt_pi ht1 ht2
  set γ := s.gammaCoord
  set φ := s.phiCoord
  set θ := s.thetaCoord
  set r := s.O.radius
  set o := s.O.center
  have hwm_re : s.O.wMinus.re = o.re - r * Real.cos γ := by simp [Disk.wMinus, hhalf, o, r]
  have hwp_re : s.O.wPlus.re = o.re + r * Real.cos γ := by simp [Disk.wPlus, hhalf, o, r]
  have hwm_im : s.O.wMinus.im = 0 := by simp [Disk.wMinus]
  have hwp_im : s.O.wPlus.im = 0 := by simp [Disk.wPlus]
  have hUm : s.O.upperAngle s.O.wMinus = Real.pi + γ := by
    apply upperAngle_eq _ _ _ hr (by linarith) (by linarith)
    · rw [hwm_re, show Real.pi + γ = γ + Real.pi by ring, Real.cos_add_pi]; ring
    · rw [hwm_im, show Real.pi + γ = γ + Real.pi by ring, Real.sin_add_pi]; linarith
  have hUp : s.O.upperAngle s.O.wPlus = -γ := by
    apply upperAngle_eq _ _ _ hr (by linarith) (by linarith)
    · rw [hwp_re, Real.cos_neg]
    · rw [hwp_im, Real.sin_neg]; linarith
  have hLm : s.O.lowerAngle s.O.wMinus = Real.pi + γ := by
    apply lowerAngle_eq _ _ _ hr (by linarith) (by linarith)
    · rw [hwm_re, show Real.pi + γ = γ + Real.pi by ring, Real.cos_add_pi]; ring
    · rw [hwm_im, show Real.pi + γ = γ + Real.pi by ring, Real.sin_add_pi]; linarith
  have hLp : s.O.lowerAngle s.O.wPlus = 2 * Real.pi - γ := by
    apply lowerAngle_eq _ _ _ hr (by linarith) (by linarith)
    · rw [hwp_re, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi]; ring
    · rw [hwp_im, Real.sin_sub, Real.cos_two_pi, Real.sin_two_pi]; linarith
  have hUa : s.O.upperAngle s.aG = Real.pi - θ + φ := by
    apply upperAngle_eq _ _ _ hr (by linarith) (by linarith)
    · rw [ha1, show Real.pi - θ + φ = Real.pi - (θ - φ) by ring, Real.cos_pi_sub]; ring
    · rw [ha2, show Real.pi - θ + φ = Real.pi - (θ - φ) by ring, Real.sin_pi_sub]
  have hLb : s.O.lowerAngle s.bG = Real.pi + θ + φ := by
    apply lowerAngle_eq _ _ _ hr (by linarith) (by linarith)
    · rw [hb1, show Real.pi + θ + φ = (θ + φ) + Real.pi by ring, Real.cos_add_pi]; ring
    · rw [hb2, show Real.pi + θ + φ = (θ + φ) + Real.pi by ring, Real.sin_add_pi]; ring
  refine ⟨?_, ?_, ?_, ?_, ?_, hwm_re, hwp_re, ?_⟩
  · unfold Disk.upperArcLength; rw [hUm, hUp]; ring
  · unfold Disk.lowerArcLength; rw [hLm, hLp]; ring
  · unfold Disk.upperArcLength; rw [hUm, hUa]; ring
  · unfold Disk.lowerArcLength; rw [hLm, hLb]; ring
  · unfold Disk.upperArcLength Disk.lowerArcLength; rw [hUm, hUa, hLm, hLb]; ring
  · have hcross : s.crossing.re =
        s.aG.re + s.aG.im / (s.aG.im - s.bG.im) * (s.bG.re - s.aG.re) := by
      unfold GateState.crossing axisCrossing
      rw [Complex.add_re, Complex.re_ofReal_mul, Complex.sub_re]
    have hden : s.aG.im - s.bG.im = 2 * r * Real.sin θ * Real.cos φ := by
      rw [ha2, hb2, Real.sin_sub, Real.sin_add]; ring
    have hnum : s.bG.re - s.aG.re = 2 * r * Real.sin θ * Real.sin φ := by
      rw [ha1, hb1, Real.cos_sub, Real.cos_add]; ring
    rw [hcross, hden, hnum]
    have e : s.aG.im / (2 * r * Real.sin θ * Real.cos φ) * (2 * r * Real.sin θ * Real.sin φ) =
        s.aG.im * Real.sin φ / Real.cos φ := by
      field_simp
    rw [e, eq_div_iff hcpos.ne', ha1, ha2, ho2, Real.cos_sub, Real.sin_sub]
    field_simp
    linear_combination (-r * Real.cos θ) * hcs

theorem dist_eq_of_sq {z w : ℂ} {d : ℝ} (hd : 0 ≤ d)
    (h : (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 = d ^ 2) : dist z w = d := by
  rw [← Real.sqrt_sq hd, ← h, ← dist_sq_eq, Real.sqrt_sq dist_nonneg]

theorem psi_eq (s : GateState) (hr : 0 < s.O.radius) :
    s.δ = 2 * s.O.radius * (s.psiCoord - s.phiCoord) := by
  unfold GateState.psiCoord; field_simp; ring

theorem part1 (s : GateState) (hs : s.IsGateState) : s.angularCoords ∈ SigmaSet := by
  obtain ⟨-, -, hg1, hg2, ho2, -⟩ := gamma_facts s hs
  obtain ⟨-, hp1, hp2, -, -⟩ := phi_facts s hs
  obtain ⟨ht1, ht2, -, ha2, -, hb2, hL⟩ := theta_facts s hs
  obtain ⟨hr, -, -, ha0, hb0, hδ⟩ := hs
  have hδ' := psi_eq s hr
  simp only [SigmaSet, OmegaTimesR, OmegaSet, Set.mem_setOf_eq, GateState.angularCoords]
  set γ := s.gammaCoord
  set φ := s.phiCoord
  set θ := s.thetaCoord
  set r := s.O.radius
  have hA : Real.sin (-γ) < Real.sin (θ - φ) := by
    rw [Real.sin_neg]
    have : 0 < r * (Real.sin γ + Real.sin (θ - φ)) := by rw [ha2, ho2] at ha0; linarith
    have := (pos_iff_pos_of_mul_pos this).mp hr
    linarith
  have hB : Real.sin γ < Real.sin (θ + φ) := by
    have : 0 < r * (Real.sin (θ + φ) - Real.sin γ) := by rw [hb2, ho2] at hb0; linarith
    have := (pos_iff_pos_of_mul_pos this).mp hr
    linarith
  rw [sin_lt_sin_iff' (by linarith) (by linarith) (by linarith) (by linarith)] at hA hB
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [abs_sub_lt_iff]; constructor <;> linarith
  · have : |γ + φ| < Real.pi - θ := by rw [abs_lt]; constructor <;> linarith
    linarith
  · rw [hδ', hL] at hδ
    rw [abs_le] at hδ ⊢
    have h2r : 0 < 2 * r := by linarith
    constructor
    · nlinarith
    · nlinarith

theorem gs_ext {s t : GateState} (h1 : s.O.center = t.O.center) (h2 : s.O.radius = t.O.radius)
    (h3 : s.aG = t.aG) (h4 : s.bG = t.bG) (h5 : s.δ = t.δ) : s = t := by
  obtain ⟨⟨o, r⟩, a, b, d⟩ := s
  obtain ⟨⟨o', r'⟩, a', b', d'⟩ := t
  simp_all

theorem part3 (s s' : GateState) (hs : s.IsGateState) (hs' : s'.IsGateState)
    (h : s.angularCoords = s'.angularCoords) :
    ∃ k t : ℝ, 0 < k ∧ s' = s.scaleTranslate k t := by
  simp only [GateState.angularCoords, Prod.mk.injEq] at h
  obtain ⟨eg, ep, et, eps⟩ := h
  obtain ⟨-, -, -, -, ho2, -⟩ := gamma_facts s hs
  obtain ⟨-, -, ha1, ha2, hb1, hb2, -⟩ := theta_facts s hs
  obtain ⟨-, -, -, -, ho2', -⟩ := gamma_facts s' hs'
  obtain ⟨-, -, ha1', ha2', hb1', hb2', -⟩ := theta_facts s' hs'
  have hr : 0 < s.O.radius := hs.1
  have hr' : 0 < s'.O.radius := hs'.1
  have hd := psi_eq s hr
  have hd' := psi_eq s' hr'
  rw [← eg] at ho2'
  rw [← et, ← ep] at ha1' ha2' hb1' hb2'
  rw [← eps, ← ep] at hd'
  set k := s'.O.radius / s.O.radius with hk
  have hkr : k * s.O.radius = s'.O.radius := by rw [hk]; field_simp
  refine ⟨k, s'.O.center.re - k * s.O.center.re, div_pos hr' hr, ?_⟩
  apply gs_ext
  · show s'.O.center = (k : ℂ) * s.O.center + ((s'.O.center.re - k * s.O.center.re : ℝ) : ℂ)
    apply Complex.ext
    · simp
    · simp; rw [ho2', ho2, ← hkr]; ring
  · show s'.O.radius = k * s.O.radius
    exact hkr.symm
  · show s'.aG = (k : ℂ) * s.aG + ((s'.O.center.re - k * s.O.center.re : ℝ) : ℂ)
    apply Complex.ext
    · simp; rw [ha1', ha1, ← hkr]; ring
    · simp; rw [ha2', ha2, ho2', ho2, ← hkr]; ring
  · show s'.bG = (k : ℂ) * s.bG + ((s'.O.center.re - k * s.O.center.re : ℝ) : ℂ)
    apply Complex.ext
    · simp; rw [hb1', hb1, ← hkr]; ring
    · simp; rw [hb2', hb2, ho2', ho2, ← hkr]; ring
  · show s'.δ = k * s.δ
    rw [hd', hd, ← hkr]; ring

theorem part2 (z : R4) (hz : z ∈ SigmaSet) :
    ∃ s : GateState, s.IsGateState ∧ s.angularCoords = z := by
  obtain ⟨γ, φ, θ, ψ⟩ := z
  simp only [SigmaSet, OmegaTimesR, OmegaSet, Set.mem_setOf_eq] at hz
  obtain ⟨⟨h1, h2⟩, h3⟩ := hz
  obtain ⟨h1a, h1b⟩ := abs_sub_lt_iff.mp h1
  have h2' : |γ + φ| < Real.pi - θ := by linarith
  obtain ⟨h2a, h2b⟩ := abs_lt.mp h2'
  have hg1 : -(Real.pi / 2) < γ := by linarith
  have hg2 : γ < Real.pi / 2 := by linarith
  have hp1 : -(Real.pi / 2) < φ := by linarith
  have hp2 : φ < Real.pi / 2 := by linarith
  have ht1 : 0 < θ := by linarith
  have ht2 : θ < Real.pi := by linarith
  have hspos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi ht1 ht2
  have hcs := Real.cos_sq_add_sin_sq φ
  have hcs' := Real.cos_sq_add_sin_sq (θ - φ)
  have hcs'' := Real.cos_sq_add_sin_sq (θ + φ)
  have hcsθ := Real.cos_sq_add_sin_sq θ
  have hA : Real.sin (-γ) < Real.sin (θ - φ) := by
    rw [sin_lt_sin_iff' (by linarith) (by linarith) (by linarith) (by linarith)]
    constructor <;> linarith
  have hB : Real.sin γ < Real.sin (θ + φ) := by
    rw [sin_lt_sin_iff' (by linarith) (by linarith) (by linarith) (by linarith)]
    constructor <;> linarith
  rw [Real.sin_neg] at hA
  set s : GateState := ⟨⟨⟨0, Real.sin γ⟩, 1⟩, ⟨-Real.cos (θ - φ), Real.sin γ + Real.sin (θ - φ)⟩,
    ⟨-Real.cos (θ + φ), Real.sin γ - Real.sin (θ + φ)⟩, 2 * (ψ - φ)⟩ with hsdef
  have hL : dist s.aG s.bG = 2 * Real.sin θ := by
    apply dist_eq_of_sq (by positivity)
    simp only [hsdef]
    rw [Real.cos_sub, Real.cos_add, Real.sin_sub, Real.sin_add]
    linear_combination (4 * Real.sin θ ^ 2) * hcs
  have hgs : s.IsGateState := by
    refine ⟨by simp [hsdef], ?_, ?_, ?_, ?_, ?_⟩
    · show dist _ _ = _
      apply dist_eq_of_sq zero_le_one
      simp only [hsdef]
      linear_combination hcs'
    · show dist _ _ = _
      apply dist_eq_of_sq zero_le_one
      simp only [hsdef]
      linear_combination hcs''
    · simp only [hsdef]; linarith
    · simp only [hsdef]; linarith
    · rw [hL]; simp only [hsdef]
      rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
      linarith
  have hphi : s.phiCoord = φ := by
    unfold GateState.phiCoord
    apply arg_eq_of_re_im _ (2 * Real.sin θ) φ (by positivity) ⟨by linarith, by linarith⟩
    · simp only [hsdef, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.neg_re,
        Complex.neg_im, Complex.I_re, Complex.I_im]
      rw [Real.sin_sub, Real.sin_add]; ring
    · simp only [hsdef, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.neg_re,
        Complex.neg_im, Complex.I_re, Complex.I_im]
      rw [Real.cos_sub, Real.cos_add]; ring
  have hoff : s.offset = Real.cos θ := by
    have h := offset_mul s (by rw [hL]; positivity)
    obtain ⟨X, hXe⟩ : ∃ X, X = s.offset := ⟨_, rfl⟩
    rw [hL, ← hXe] at h
    rw [← hXe]
    simp only [hsdef] at h
    rw [Real.cos_sub, Real.cos_add, Real.sin_sub, Real.sin_add] at h
    have h' : 2 * Real.sin θ * (X - Real.cos θ) = 0 := by
      linear_combination h + (2 * Real.sin θ * Real.cos θ) * hcs
    rcases mul_eq_zero.mp h' with h'' | h''
    · exact absurd h'' (by positivity)
    · linarith
  refine ⟨s, hgs, ?_⟩
  simp only [GateState.angularCoords, Prod.mk.injEq]
  refine ⟨?_, hphi, ?_, ?_⟩
  · unfold GateState.gammaCoord
    simp only [hsdef, div_one]
    exact Real.arcsin_sin hg1.le hg2.le
  · unfold GateState.thetaCoord
    rw [hoff]
    simp only [hsdef, div_one]
    exact Real.arccos_cos ht1.le ht2.le
  · unfold GateState.psiCoord
    rw [hphi]
    simp only [hsdef]
    ring

end L42

end DelaunayStretch

open DelaunayStretch.L42 in
theorem solution :
    (∀ s : GateState, s.IsGateState → s.angularCoords ∈ SigmaSet) ∧
    (∀ z ∈ SigmaSet, ∃ s : GateState, s.IsGateState ∧ s.angularCoords = z) ∧
    (∀ s s' : GateState, s.IsGateState → s'.IsGateState → s.angularCoords = s'.angularCoords →
      ∃ k t : ℝ, 0 < k ∧ s' = s.scaleTranslate k t) ∧
    (∀ s : GateState, s.IsGateState →
      s.O.upperArcLength s.O.wMinus s.O.wPlus = s.O.radius * (Real.pi + 2 * s.gammaCoord) ∧
      s.O.lowerArcLength s.O.wMinus s.O.wPlus = s.O.radius * (Real.pi - 2 * s.gammaCoord) ∧
      s.O.upperArcLength s.O.wMinus s.aG =
        s.O.radius * (s.thetaCoord + s.gammaCoord - s.phiCoord) ∧
      s.O.lowerArcLength s.O.wMinus s.bG =
        s.O.radius * (s.thetaCoord - s.gammaCoord + s.phiCoord) ∧
      s.O.upperArcLength s.O.wMinus s.aG + s.O.lowerArcLength s.O.wMinus s.bG =
        s.O.radius * (2 * s.thetaCoord) ∧
      s.O.wMinus.re = s.O.center.re - s.O.radius * Real.cos s.gammaCoord ∧
      s.O.wPlus.re = s.O.center.re + s.O.radius * Real.cos s.gammaCoord ∧
      s.crossing.re - s.O.center.re =
        s.O.radius * (Real.sin s.gammaCoord * Real.sin s.phiCoord - Real.cos s.thetaCoord) /
          Real.cos s.phiCoord) :=
  ⟨part1, part2, part3, part4⟩
