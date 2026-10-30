-- Prove2me | solution 1 for CubicTurning.sharp_finite_balanced_law_exact
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:56:32.898379+00:00
-- url     : https://prove2.me/submissions/e7b8d0b2-40fb-4360-bd63-c0294431b067

import Mathlib
import Definitions.Def_CubicTurning_finite_balanced
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_CubicTurning_affine_cubic_uniform_law
import Theorems.Thm_CubicTurning_central_history_forces_energy
import Theorems.Thm_CubicTurning_central_history_forces_energy_negative
import Theorems.Thm_CubicTurning_chain_start_middle
import Theorems.Thm_CubicTurning_sharp_finite_balanced_law_lower
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate


set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate
namespace CubicTurning









theorem pairEnergy_nonneg (d₀ d₁ : ℂ) : 0 ≤ pairEnergy d₀ d₁ := by
  have h := Complex.re_le_norm (d₀ * conj d₁)
  rw [norm_mul, Complex.norm_conj] at h
  dsimp [pairEnergy]
  linarith



































theorem variance_decomposition (r : ℝ) (a b c : ℂ)
    (hsecond : a^2+b^2+c^2=6*(r:ℂ)^2) :
    variance a b c = 2*r^2+(2/3)*(a.im^2+b.im^2+c.im^2) := by
  have h := congrArg Complex.re hsecond
  simp [pow_two,Complex.mul_re] at h
  unfold variance
  rw [←Complex.normSq_eq_norm_sq,←Complex.normSq_eq_norm_sq,←Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply]
  nlinarith

theorem radial_bound_identity (r Y : ℝ) (hr : 0 ≤ r) (hY : 0 ≤ Y) :
    2*r*(Real.sqrt (r^2+Y)+r) =
      2*r^2+Real.sqrt ((2*r^2)*(2*(2*r^2+Y)-2*r^2)) := by
  have hh : 0 ≤ r^2+Y := by positivity
  have hs : (Real.sqrt (r^2+Y))^2 = r^2+Y := Real.sq_sqrt hh
  have hroot : Real.sqrt ((2*r^2)*(2*(2*r^2+Y)-2*r^2)) =
      2*r*Real.sqrt (r^2+Y) := by
    apply (Real.sqrt_eq_iff_eq_sq (mul_nonneg (by positivity) (by nlinarith [sq_nonneg r])) (by positivity)).mpr
    nlinarith
  rw [hroot]
  ring






























































end CubicTurning


set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate
namespace CubicTurning












theorem sharp_family_center (t : ℝ) :
    sharpCentral t+sharpOuterPlus t+sharpOuterMinus t=0 := by
  apply Complex.ext <;> simp [sharpCentral,sharpOuterPlus,sharpOuterMinus] <;> ring

theorem sharp_family_second (t : ℝ) :
    (sharpCentral t)^2+(sharpOuterPlus t)^2+(sharpOuterMinus t)^2=6 := by
  have hs : (Real.sqrt (3+3*t^2/4))^2=3+3*t^2/4 := Real.sq_sqrt (by positivity)
  simp only [pow_two] at hs
  apply Complex.ext <;> simp [sharpCentral,sharpOuterPlus,sharpOuterMinus,pow_two,
    Complex.mul_re,Complex.mul_im] <;> nlinarith [hs]

theorem sharp_family_variance (t : ℝ) :
    variance (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t)=2+t^2 := by
  have hv := variance_decomposition 1 (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t)
    (by simpa using sharp_family_second t)
  convert hv using 1 <;> simp [sharpCentral,sharpOuterPlus,sharpOuterMinus] <;> ring

theorem energy_nonneg (e d₀ d₁ : ℂ) : 0≤energy e d₀ d₁ := by
  unfold energy
  split_ifs
  · exact pairEnergy_nonneg _ _
  · rfl

theorem sharp_history_endpoint_energy (t : ℝ) (ht : 0<t) (ht1 : t≤1)
    (z : Fin 3 → ℂ) (e : ℂ)
    (hz : DerivativeChainPrivate.IsChain ![sharpCentral t,sharpOuterPlus t,sharpOuterMinus t] z)
    (hf : IsForward e (z 1-z 0) (z 2-z 1)) (hend : z 2=sharpCentral t) :
    energy e (z 1-z 0) (z 2-z 1)=2+2*Real.sqrt (1+t^2) := by
  obtain ⟨hz₀,hz₁⟩ := chain_start_middle _ _ _ (sharp_family_center t) (sharp_family_second t) z hz
  rcases hz₁ with hz₁|hz₁
  · rw [hz₀,hz₁,hend] at hf ⊢
    have hd : sharpCentral t-1=-1+Complex.I*(t:ℂ) := by unfold sharpCentral; ring
    rw [hd] at hf ⊢
    simpa using central_history_forces_energy t e ht ht1 (by simpa only [sub_zero] using hf)
  · rw [hz₀,hz₁,hend] at hf ⊢
    have hd : sharpCentral t-(-1)=1+Complex.I*(t:ℂ) := by unfold sharpCentral; ring
    rw [hd] at hf ⊢
    simpa using central_history_forces_energy_negative t e ht ht1 (by simpa only [sub_zero] using hf)

theorem sharp_uniform_law_lower (t : ℝ) (ht : 0<t) (ht1 : t≤1)
    (L : AffineUniformForwardLaw (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t) 0) :
    (2+2*Real.sqrt (1+t^2))/3≤L.meanEnergy := by
  have hend : L.paths 0 2=sharpCentral t := by simpa using L.endpoint 0
  have hc := sharp_history_endpoint_energy t ht ht1 (L.paths 0) (L.axes 0) (L.actual 0) (L.forward 0) hend
  unfold AffineUniformForwardLaw.meanEnergy
  rw [Fin.sum_univ_succ]
  have hb := energy_nonneg (L.axes 1) (L.paths 1 1-L.paths 1 0) (L.paths 1 2-L.paths 1 1)
  have hc' := energy_nonneg (L.axes 2) (L.paths 2 1-L.paths 2 0) (L.paths 2 2-L.paths 2 1)
  simp [Fin.sum_univ_succ] at *
  linarith

theorem sharp_uniform_law_exact (t : ℝ) (ht : 0<t) (ht1 : t≤1) :
    ∃ L : AffineUniformForwardLaw (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t) 0,
      L.meanEnergy=(2+2*Real.sqrt (1+t^2))/3 ∧
      ∀ M : AffineUniformForwardLaw (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t) 0,
        L.meanEnergy≤M.meanEnergy := by
  have he := affine_cubic_uniform_law 1 (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t)
    0 1 (by norm_num) (by norm_num) (sharp_family_center t) (by simpa using sharp_family_second t)
  obtain ⟨M,hL,hL'⟩ := he
  let L : AffineUniformForwardLaw (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t) 0 := {
    paths := M.paths
    axes := M.axes
    actual := by simpa only [zero_add,one_mul] using M.actual
    endpoint := by simpa only [zero_add,one_mul] using M.endpoint
    start := M.start
    forward := M.forward }
  change L.meanEnergy ≤ _ at hL
  have hlo := sharp_uniform_law_lower t ht ht1 L
  rw [sharp_family_variance] at hL
  have hrad := radial_bound_identity 1 (t^2) (by norm_num) (sq_nonneg t)
  norm_num at hrad hL
  have hcost : L.meanEnergy=(2+2*Real.sqrt (1+t^2))/3 := by linarith
  refine ⟨L,hcost,?_⟩
  intro M
  rw [hcost]
  exact sharp_uniform_law_lower t ht ht1 M








































end CubicTurning

open CubicTurning in
theorem solution (t : ℝ) (ht : 0<t) (ht1 : t≤1) :
    ∃ L : FiniteBalancedForwardLaw 3 (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t),
      L.meanEnergy=(2+2*Real.sqrt (1+t^2))/3 ∧
      ∀ (n : ℕ) (M : FiniteBalancedForwardLaw n (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t)),
        L.meanEnergy≤M.meanEnergy := by
  obtain ⟨U,hU,hmin⟩ := sharp_uniform_law_exact t ht ht1
  let L : FiniteBalancedForwardLaw 3 (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t) := {
    weights := fun _ => 1/3
    nonneg := by intro i; norm_num
    total := by norm_num
    paths := U.paths
    axes := U.axes
    actual := U.actual
    balanced := by
      simp only [U.endpoint]
      simp [Fin.sum_univ_succ]
      linear_combination (sharp_family_center t)/3
    forward := U.forward }
  have he : L.meanEnergy=U.meanEnergy := by
    change (∑ i,(1/3)*energy (U.axes i) (U.paths i 1-U.paths i 0) (U.paths i 2-U.paths i 1))=
      (∑ i,energy (U.axes i) (U.paths i 1-U.paths i 0) (U.paths i 2-U.paths i 1))/3
    rw [←Finset.mul_sum]
    ring
  refine ⟨L,he.trans hU,?_⟩
  intro n M
  rw [he,hU]
  exact sharp_finite_balanced_law_lower t ht ht1 M
