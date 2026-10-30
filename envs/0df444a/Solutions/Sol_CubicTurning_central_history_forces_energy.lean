-- Prove2me | solution 1 for CubicTurning.central_history_forces_energy
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:30:55.569366+00:00
-- url     : https://prove2.me/submissions/a7f58cd8-9abf-4be3-a7e3-ef17659b95a9

import Mathlib
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate


open CubicTurning in
theorem solution (t : ℝ) (e : ℂ) (ht : 0<t) (ht1 : t≤1)
    (hf : IsForward e (1:ℂ) (-1+Complex.I*(t:ℂ))) :
    energy e (1:ℂ) (-1+Complex.I*(t:ℂ))=2+2*Real.sqrt (1+t^2) := by
  rcases hf with ⟨he,h₀,h₁⟩
  have hx : 0≤e.re := by simpa using h₀
  have hforward : 0≤-e.re-e.im*t := by
    simpa [Complex.mul_re,Complex.mul_im] using h₁
  have hnorm : e.re^2+e.im^2=1 := by
    have hh := Complex.normSq_eq_norm_sq (z:=e)
    rw [Complex.normSq_apply,he] at hh
    nlinarith
  have hy : e.im≤0 := by nlinarith
  have hxy : e.re≤-e.im := by nlinarith [mul_nonneg (sub_nonneg.mpr ht1) (neg_nonneg.mpr hy)]
  have hx1 : e.re≤1 := by simpa [he] using Complex.re_le_norm e
  have hyhalf : 1/2≤-e.im := by
    have hsq : e.re^2≤e.im^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (show 0≤-e.im+e.re by linarith)]
    nlinarith [sq_nonneg (e.im+1/2)]
  let d : ℂ := -1+Complex.I*(t:ℂ)
  have hd : d≠0 := by intro hz; have hh:=congrArg Complex.re hz; simp [d] at hh
  have hdre : (e*d).re = -e.re-e.im*t := by simp [d,Complex.mul_re,Complex.mul_im]
  have hdim : (e*d).im = -e.im+e.re*t := by simp [d,Complex.mul_re,Complex.mul_im]; ring
  have hn : ‖d‖^2=1+t^2 := by
    rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    simp [d,pow_two]
  have hnle : ‖d‖≤3/2 := by nlinarith [norm_nonneg d]
  have hproj : (e*d).re≤‖d‖ := by
    have hh:=Complex.re_le_norm (e*d)
    rwa [norm_mul,he,one_mul] at hh
  have hw : 0<‖d‖+(e*d).re := by
    have hpn:=norm_pos_iff.mpr hd
    have hfr : 0≤(e*d).re := by rw [hdre]; exact hforward
    linarith
  have hq₀ : halfSlope e (1:ℂ)≤-(1/7) := by
    unfold halfSlope
    simp only [mul_one,norm_one]
    apply (div_le_iff₀ (show 0<1+e.re by linarith)).mpr
    linarith
  have hq₁ : 1/7≤halfSlope e d := by
    unfold halfSlope
    apply (le_div_iff₀ hw).mpr
    rw [hdim]
    have hxt : 0≤e.re*t := mul_nonneg hx ht.le
    nlinarith
  have hpair : pairEnergy 1 d=2+2*Real.sqrt (1+t^2) := by
    have hdnorm : ‖d‖=Real.sqrt (1+t^2) := by
      exact (Real.sqrt_eq_iff_eq_sq (by positivity) (norm_nonneg _)).mpr hn.symm |>.symm
    simp [pairEnergy,d,Complex.mul_re,Complex.conj_re,hdnorm]
    ring
  change energy e 1 d=_
  rw [energy,if_pos (Or.inr ⟨hq₁,hq₀⟩)]
  exact hpair
