-- Prove2me | solution 1 for CubicTurning.unit_disk_law_double
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:58:59.002885+00:00
-- url     : https://prove2.me/submissions/396d2d1c-6e48-436d-998b-52d49b8a9f8b

import Mathlib
import Definitions.Def_CubicTurning_finite_balanced
import Definitions.Def_CubicTurning_foundations
import Definitions.Def_CubicTurning_unit_disk
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate


set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate
namespace CubicTurning
































theorem chain_endpoint_membership (a b c : ℂ) (z : Fin 3 → ℂ)
    (hz : DerivativeChainPrivate.IsChain ![a,b,c] z) : z 2=a ∨ z 2=b ∨ z 2=c := by
  have h:=hz 2
  simp [DerivativeChainPrivate.row,DerivativeChainPrivate.fromRoots,Fin.prod_univ_succ] at h
  simpa only [mul_eq_zero,sub_eq_zero,or_assoc] using h
































end CubicTurning


set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
open ComplexConjugate
namespace CubicTurning

theorem chain_complex_scale (a b c s : ℂ) (z : Fin 3 → ℂ)
    (hz : DerivativeChainPrivate.IsChain ![a,b,c] z) :
    DerivativeChainPrivate.IsChain ![s*a,s*b,s*c] (fun i => s*z i) := by
  intro i
  have hi:=hz i
  fin_cases i
  · simp [DerivativeChainPrivate.row,DerivativeChainPrivate.fromRoots,Fin.prod_univ_succ,
      Function.iterate_succ_apply,Polynomial.derivative_mul] at hi ⊢
    linear_combination s*hi
  · simp [DerivativeChainPrivate.row,DerivativeChainPrivate.fromRoots,Fin.prod_univ_succ,
      Function.iterate_succ_apply,Polynomial.derivative_mul] at hi ⊢
    linear_combination s^2*hi
  · obtain ha|hb|hc:=chain_endpoint_membership a b c z hz
    · simp [DerivativeChainPrivate.row,DerivativeChainPrivate.fromRoots,Fin.prod_univ_succ,ha]
    · simp [DerivativeChainPrivate.row,DerivativeChainPrivate.fromRoots,Fin.prod_univ_succ,hb]
    · simp [DerivativeChainPrivate.row,DerivativeChainPrivate.fromRoots,Fin.prod_univ_succ,hc]

theorem halfSlope_positive_scale (s : ℝ) (hs : 0<s) (e d : ℂ) :
    halfSlope e ((s:ℂ)*d)=halfSlope e d := by
  unfold halfSlope
  have hm : e*((s:ℂ)*d)=(s:ℂ)*(e*d) := by ring
  rw [hm,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs]
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,mul_zero,sub_zero,add_zero]
  rw [←mul_add]
  exact mul_div_mul_left _ _ (ne_of_gt hs)

theorem pairEnergy_positive_scale (s : ℝ) (hs : 0<s) (d₀ d₁ : ℂ) :
    pairEnergy ((s:ℂ)*d₀) ((s:ℂ)*d₁)=s^2*pairEnergy d₀ d₁ := by
  unfold pairEnergy
  simp [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs,
    Complex.mul_re,Complex.mul_im]
  ring

theorem energy_positive_scale (s : ℝ) (hs : 0<s) (e d₀ d₁ : ℂ) :
    energy e ((s:ℂ)*d₀) ((s:ℂ)*d₁)=s^2*energy e d₀ d₁ := by
  simp only [energy,halfSlope_positive_scale s hs]
  split_ifs
  · exact pairEnergy_positive_scale s hs _ _
  · ring


























end CubicTurning

open CubicTurning in
theorem solution {n : ℕ} (t : ℝ)
    (L : FiniteBalancedForwardLaw n (unitDiskCentral t) (unitDiskOuterPlus t) (unitDiskOuterMinus t)) :
    ∃ M : FiniteBalancedForwardLaw n (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t),
      M.meanEnergy=4*L.meanEnergy := by
  let paths := fun i : Fin n => fun j : Fin 3 => (2:ℂ)*L.paths i j
  have hstep (i : Fin n) (j k : Fin 3) : paths i j-paths i k=(2:ℂ)*(L.paths i j-L.paths i k) := by
    dsimp [paths]
    ring
  let M : FiniteBalancedForwardLaw n (sharpCentral t) (sharpOuterPlus t) (sharpOuterMinus t) := {
    weights := L.weights
    nonneg := L.nonneg
    total := L.total
    paths := paths
    axes := L.axes
    actual := by
      intro i
      have h:=chain_complex_scale _ _ _ 2 (L.paths i) (L.actual i)
      norm_num [unitDiskCentral,unitDiskOuterPlus,unitDiskOuterMinus,←mul_assoc] at h
      exact h
    balanced := by
      change (∑ i,(L.weights i:ℂ)*((2:ℂ)*L.paths i 2))=0
      have he : (∑ i,(L.weights i:ℂ)*((2:ℂ)*L.paths i 2))=
          2*∑ i,(L.weights i:ℂ)*L.paths i 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [he,L.balanced,mul_zero]
    forward := by
      intro i
      rw [hstep,hstep]
      obtain ⟨he,h₀,h₁⟩:=L.forward i
      refine ⟨he,?_,?_⟩
      · have hh : L.axes i*((2:ℂ)*(L.paths i 1-L.paths i 0))=
          (2:ℂ)*(L.axes i*(L.paths i 1-L.paths i 0)) := by ring
        rw [hh]
        simpa [Complex.mul_re] using (mul_nonneg (show 0≤(2:ℝ) by norm_num) h₀)
      · have hh : L.axes i*((2:ℂ)*(L.paths i 2-L.paths i 1))=
          (2:ℂ)*(L.axes i*(L.paths i 2-L.paths i 1)) := by ring
        rw [hh]
        simpa [Complex.mul_re] using (mul_nonneg (show 0≤(2:ℝ) by norm_num) h₁) }
  refine ⟨M,?_⟩
  change (∑ i,L.weights i*energy (L.axes i) (paths i 1-paths i 0) (paths i 2-paths i 1))=
    4*∑ i,L.weights i*energy (L.axes i) (L.paths i 1-L.paths i 0) (L.paths i 2-L.paths i 1)
  have henergy (e d₀ d₁ : ℂ) : energy e ((2:ℂ)*d₀) ((2:ℂ)*d₁)=4*energy e d₀ d₁ := by
    convert energy_positive_scale 2 (by norm_num) e d₀ d₁ using 1 <;> norm_num
  simp only [hstep,henergy]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
