-- Prove2me | solution 1 for CubicTurning.affine_cubic_uniform_law
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:25:41.938631+00:00
-- url     : https://prove2.me/submissions/75e803c7-0a3d-435b-a440-4f318482eea5

import Mathlib
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_CubicTurning_actual_history_affine
import Theorems.Thm_CubicTurning_uniform_energy_bound
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate


set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate
namespace CubicTurning



















theorem anisotropic_bound (H V : ℝ) (hH : 0 ≤ H) (hHV : H ≤ V) :
    (H + Real.sqrt (H*(2*V-H)))/3 ≤ 2*V/3 := by
  have hV : 0 ≤ V := hH.trans hHV
  have hb : Real.sqrt (H*(2*V-H)) ≤ V := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact hV
    · nlinarith [sq_nonneg (V-H)]
  linarith





theorem middle_real (r : ℝ) (v : ℂ) : (middle r v).im = 0 := by
  unfold middle
  split_ifs <;> simp

theorem frame_forward (r : ℝ) (hr : 0 ≤ r) (v : ℂ) :
    IsForward (frame r v) (middle r v) (v-middle r v) := by
  unfold frame
  split_ifs with h₀ h₁ h₂
  · have hx : 0 ≤ v.re := hr.trans h₀
    simp [IsForward, middle, hx]
    exact ⟨hr,h₀⟩
  · by_cases hx : 0 ≤ v.re
    · have hz : r = 0 := by linarith
      have hv : v.re = 0 := by linarith
      simp [IsForward, middle, hx, hz, hv]
    · simp [IsForward, middle, hx]
      exact ⟨hr,h₁⟩
  · simp [IsForward, Complex.mul_re, middle_real]
    exact h₂
  · simp [IsForward, Complex.mul_re, middle_real]
    exact le_of_not_ge h₂

















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







theorem pairEnergy_unit_mul (u : ℂ) (hu : ‖u‖=1) (d₀ d₁ : ℂ) :
    pairEnergy (u*d₀) (u*d₁)=pairEnergy d₀ d₁ := by
  have huc : u*conj u=1 := by
    rw [Complex.mul_conj,Complex.normSq_eq_norm_sq,hu]
    norm_num
  unfold pairEnergy
  rw [norm_mul,norm_mul,hu,one_mul,one_mul]
  have he : u*d₀*conj (u*d₁)=(u*conj u)*(d₀*conj d₁) := by
    simp only [map_mul]
    ring
  rw [he,huc,one_mul]





theorem energy_unit_mul (u : ℂ) (hu : ‖u‖=1) (e d₀ d₁ : ℂ) :
    energy e (u*d₀) (u*d₁) = energy (e*u) d₀ d₁ := by
  have hp := pairEnergy_unit_mul u hu d₀ d₁
  simp only [energy,halfSlope,norm_mul,hu,one_mul,←mul_assoc,hp]
  rfl
















































end CubicTurning

open CubicTurning in
theorem solution (r : ℝ) (a b c u t : ℂ) (hr : 0 ≤ r)
    (ht : ‖t‖=1) (hcenter : a+b+c=0) (hsecond : a^2+b^2+c^2=6*(r:ℂ)^2) :
    ∃ L : AffineUniformForwardLaw (u+t*a) (u+t*b) (u+t*c) u,
      L.meanEnergy ≤ (2*r^2+Real.sqrt ((2*r^2)*(2*variance a b c-2*r^2)))/3 ∧
      L.meanEnergy ≤ (2/3)*variance a b c := by
  have hct : conj t*t=1 := by
    rw [mul_comm,Complex.mul_conj,Complex.normSq_eq_norm_sq,ht]
    norm_num
  let roots : Fin 3 → ℂ := ![a,b,c]
  let paths := fun i : Fin 3 => (![u,u+t*middle r (roots i),u+t*roots i] : Fin 3 → ℂ)
  let axes := fun i : Fin 3 => frame r (roots i)*conj t
  have hsteps₀ (i : Fin 3) : paths i 1-paths i 0 = t*middle r (roots i) := by
    dsimp [paths]
    ring
  have hsteps₁ (i : Fin 3) : paths i 2-paths i 1 = t*(roots i-middle r (roots i)) := by
    dsimp [paths]
    ring
  have haxes (i : Fin 3) : axes i*t=frame r (roots i) := by
    dsimp [axes]
    rw [mul_assoc,hct,mul_one]
  let L : AffineUniformForwardLaw (u+t*a) (u+t*b) (u+t*c) u := {
    paths := paths
    axes := axes
    actual := by
      intro i
      apply actual_history_affine r a b c (roots i) u t hcenter hsecond
      fin_cases i <;> simp [roots]
    endpoint := by intro i; fin_cases i <;> simp [paths,roots]
    start := by intro i; simp [paths]
    forward := by
      intro i
      rw [hsteps₀,hsteps₁]
      have hf := frame_forward r hr (roots i)
      rcases hf with ⟨he,h₀,h₁⟩
      refine ⟨?_,?_,?_⟩
      · dsimp [axes]; rw [norm_mul,Complex.norm_conj,he,ht]; norm_num
      · rwa [←mul_assoc,haxes]
      · rwa [←mul_assoc,haxes] }
  have he : L.meanEnergy = (endpointEnergy r a+endpointEnergy r b+endpointEnergy r c)/3 := by
    change (∑ i,energy (axes i) (paths i 1-paths i 0) (paths i 2-paths i 1))/3 = _
    simp only [hsteps₀,hsteps₁,energy_unit_mul t ht,haxes]
    simp [roots,endpointEnergy,Fin.sum_univ_succ]
    ring
  have hY : 0 ≤ (2/3)*(a.im^2+b.im^2+c.im^2) := by positivity
  have hv := variance_decomposition r a b c hsecond
  have hb := uniform_energy_bound r a b c hr hcenter hsecond
  dsimp only at hb
  rw [radial_bound_identity r _ hr hY,←hv] at hb
  refine ⟨L,?_,?_⟩
  · rwa [he]
  · have hV : 2*r^2 ≤ variance a b c := by rw [hv]; linarith
    have hA := anisotropic_bound (2*r^2) (variance a b c) (by positivity) hV
    rw [he]
    linarith
