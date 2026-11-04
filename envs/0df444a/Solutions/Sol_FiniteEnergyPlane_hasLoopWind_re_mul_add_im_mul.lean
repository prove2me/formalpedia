-- Prove2me | solution 1 for FiniteEnergyPlane.hasLoopWind_re_mul_add_im_mul
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-03T11:11:11.312093+00:00
-- url     : https://prove2.me/submissions/0e45c517-c0ae-4203-904e-056cb1898121

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_mul
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_triangular_iff



namespace FiniteEnergyPlane

theorem hasLoopWind_re_mul_add_im_mul_aux {c p q : ℝ → ℂ} {k m : ℤ} (hc : HasLoopWind c k)
    (hp : HasLoopWind p m) (hq : Continuous q) (hqp : Function.Periodic q 1)
    (hpq : ∀ t, 0 < (starRingEnd ℂ (p t) * q t).im) :
    HasLoopWind (fun t => ((c t).re : ℂ) * p t + ((c t).im : ℂ) * q t) (k + m) := by
  obtain ⟨hcc, hcp, hc0, -⟩ := id hc
  obtain ⟨hpc, hpp, hp0, -⟩ := id hp
  set w : ℝ → ℂ := fun t => q t / p t with hw
  have hwc : Continuous w := hq.div hpc hp0
  have hwp : Function.Periodic w 1 := fun t => by simp only [hw, hqp t, hpp t]
  have hwim : ∀ t, 0 < (w t).im := by
    intro t
    have : w t = (starRingEnd ℂ (p t) * q t) / ((Complex.normSq (p t) : ℝ) : ℂ) := by
      simp only [hw]
      rw [Complex.normSq_eq_conj_mul_self]
      field_simp [hp0 t]
    rw [this, Complex.div_ofReal_im]
    exact div_pos (hpq t) (Complex.normSq_pos.2 (hp0 t))
  have hG := (hasLoopWind_triangular_iff (a := fun _ => (1 : ℝ)) (b := fun t => (w t).re)
    (d := fun t => (w t).im) continuous_const (Complex.continuous_re.comp hwc)
    (Complex.continuous_im.comp hwc) (fun _ => rfl) (fun t => by simp only [hwp t])
    (fun t => by simp only [hwp t]) (fun _ => one_pos) hwim hcc hcp hc0 k).2 hc
  have hprod := hasLoopWind_mul hp hG
  rw [add_comm m k] at hprod
  convert hprod using 2 with t
  have hpt := hp0 t
  have hre := Complex.re_add_im (w t)
  have hwt : w t * p t = q t := by simp only [hw]; field_simp [hpt]
  push_cast
  linear_combination (-(((c t).im : ℂ) * p t)) * hre - ((c t).im : ℂ) * hwt

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution {c p q : ℝ → ℂ} {k m : ℤ} (hc : HasLoopWind c k)
    (hp : HasLoopWind p m) (hq : Continuous q) (hqp : Function.Periodic q 1)
    (hpq : ∀ t, 0 < (starRingEnd ℂ (p t) * q t).im) :
    HasLoopWind (fun t => ((c t).re : ℂ) * p t + ((c t).im : ℂ) * q t) (k + m) :=
  hasLoopWind_re_mul_add_im_mul_aux hc hp hq hqp hpq
