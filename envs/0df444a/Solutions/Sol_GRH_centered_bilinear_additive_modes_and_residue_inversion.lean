-- Prove2me | solution 1 for GRH.centered_bilinear_additive_modes_and_residue_inversion
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T05:21:23.637014+00:00
-- url     : https://prove2.me/submissions/fce99dad-3a58-411e-96c6-57fd5088a0df

import Theorems.Thm_GRH_centered_moebius_uniform_large_modulus_range
import Mathlib.Tactic.Ring

open Finset GRH.AdditiveMoebiusSpectrum

private theorem phaseAt {q : ℕ} [NeZero q] (h : ZMod q) (n : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * ((n : ℝ) * (angle h : ℝ))) =
      ZMod.stdAddChar ((n : ZMod q)*h) := by
  have e := ZMod.stdAddChar_coe (N:=q) ((n * h.val : ℕ) : ℤ)
  push_cast at e
  rw [ZMod.natCast_zmod_val] at e
  rw [e]
  unfold angle
  push_cast
  congr 1
  ring

private theorem orthogonal {q : ℕ} [NeZero q] (t : ZMod q) :
    ∑ k : ZMod q, ZMod.stdAddChar (t*k) = if t=0 then (q : ℂ) else 0 := by
  classical
  by_cases h : t=0
  · simp [h,ZMod.card]
  · rw [if_neg h]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q h)

private theorem groupByClass {q : ℕ} [NeZero q] (h : ZMod q) (N : ℕ) (s : Bool) :
    transform s N (angle h) =
      ∑ a : ZMod q, (fiber a N (weight s N) : ℂ) * ZMod.stdAddChar (a*h) := by
  classical
  simp only [transform,phaseAt,fiber,Complex.ofReal_sum,apply_ite Complex.ofReal,Complex.ofReal_zero,
    sum_mul,ite_mul,zero_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  simp


private noncomputable def fft {q : ℕ} [NeZero q] (f : ZMod q → ℝ) (h : ZMod q) : ℂ :=
  ∑ a : ZMod q, (f a : ℂ)*ZMod.stdAddChar (a*h)

private theorem invertTable {q : ℕ} [NeZero q] (f : ZMod q → ℝ) (a : ZMod q) :
    (q : ℂ)*(f a : ℂ) = ∑ h : ZMod q, ZMod.stdAddChar (-(a*h))*fft f h := by
  classical
  simp_rw [fft,mul_sum]
  rw [sum_comm]
  have prod (b h : ZMod q) :
      ZMod.stdAddChar (-(a*h))*((f b : ℂ)*ZMod.stdAddChar (b*h)) =
      (f b : ℂ)*ZMod.stdAddChar ((b-a)*h) := by
    rw [sub_mul,sub_eq_add_neg,AddChar.map_add_eq_mul]
    ring
  simp_rw [prod,← mul_sum,orthogonal,sub_eq_zero,mul_ite,mul_zero]
  simp [mul_comm]

open scoped ComplexConjugate

private theorem parseval {q : ℕ} [NeZero q] (f : ZMod q → ℝ) :
    ∑ h : ZMod q, ‖fft f h‖^2 = (q : ℝ)*∑ a : ZMod q, (f a)^2 := by
  classical
  have cj (t : ZMod q) : conj (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
    rw [ZMod.stdAddChar_apply,ZMod.stdAddChar_apply,AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj]
  have cs (h : ZMod q) : conj (fft f h) = ∑ a : ZMod q, (f a : ℂ)*ZMod.stdAddChar (-(a*h)) := by
    simp only [fft,map_sum,map_mul,Complex.conj_ofReal,cj]
  have HH : (∑ h : ZMod q, ((‖fft f h‖^2 : ℝ) : ℂ)) = (q : ℂ)*∑ a : ZMod q, (f a : ℂ)^2 := by
    calc
      _ = ∑ h : ZMod q, conj (fft f h)*fft f h := by
        apply sum_congr rfl
        intro h _
        simpa using (Complex.conj_mul' (fft f h)).symm
      _ = ∑ a : ZMod q, (f a : ℂ) * ∑ h : ZMod q, ZMod.stdAddChar (-(a*h))*fft f h := by
        simp_rw [cs,sum_mul,mul_assoc,mul_sum]
        rw [sum_comm]
      _ = _ := by
        simp_rw [← invertTable]
        rw [mul_sum]
        apply sum_congr rfl
        intro a _
        ring
  exact_mod_cast HH

private theorem modes (q : ℕ) [NeZero q] (N : ℕ) :
    (∀ h : ZMod q, h ≠ 0 → transform true N (angle h) =
      ∑ a : ZMod q, (GRH.centeredMoebiusBilinear q a N : ℂ) * ZMod.stdAddChar (a*h)) ∧
    (∀ (s : Bool) (a : ZMod q), (q : ℂ) * (fiber a N (weight s N) : ℂ) =
      ∑ h : ZMod q, ZMod.stdAddChar (-(a*h)) * transform s N (angle h)) := by
  classical
  constructor
  · intro h hh
    rw [groupByClass]
    simp_rw [← (GRH.centered_moebius_uniform_large_modulus_range q _ N).1,
      Complex.ofReal_add,add_mul,sum_add_distrib,← mul_sum]
    have hz : ∑ a : ZMod q, ZMod.stdAddChar (a*h) = 0 := by
      simpa only [mul_comm _ h,if_neg hh] using orthogonal h
    rw [hz,mul_zero,add_zero]
  · intro s a
    simp_rw [groupByClass]
    exact invertTable (fun b => fiber b N (weight s N)) a

theorem solution (q : ℕ) [NeZero q] (N : ℕ) :
    (∀ h : ZMod q, h ≠ 0 → transform true N (angle h) =
      ∑ a : ZMod q, (GRH.centeredMoebiusBilinear q a N : ℂ) * ZMod.stdAddChar (a*h)) ∧
    (∀ (s : Bool) (a : ZMod q), (q : ℂ) * (fiber a N (weight s N) : ℂ) =
      ∑ h : ZMod q, ZMod.stdAddChar (-(a*h)) * transform s N (angle h)) ∧
    (q : ℝ) * rowVariance q N =
      ∑ h ∈ (univ : Finset (ZMod q)).erase 0, ‖transform true N (angle h)‖^2 := by
  classical
  obtain ⟨hm,hi⟩ := modes q N
  refine ⟨hm,hi,?_⟩
  let B := fun a : ZMod q => GRH.centeredMoebiusBilinear q a N
  let m : ℝ := (∑ a : ZMod q, B a)/(q : ℝ)
  let f := fun a : ZMod q => B a - m
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hsum : ∑ a : ZMod q, f a = 0 := by
    simp [f,m,sum_sub_distrib,ZMod.card]
    field_simp
    ring
  have hz : fft f 0 = 0 := by simp [fft,← Complex.ofReal_sum,hsum]
  have hn (h : ZMod q) (hne : h ≠ 0) : fft f h = transform true N (angle h) := by
    rw [hm h hne]
    have hc : ∑ a : ZMod q, ZMod.stdAddChar (a*h) = 0 := by
      simpa only [mul_comm _ h,if_neg hne] using orthogonal h
    simp only [fft,f,Complex.ofReal_sub,sub_mul,sum_sub_distrib,← mul_sum,hc,mul_zero,sub_zero,B]
  calc
    _ = ∑ h : ZMod q, ‖fft f h‖^2 := (parseval f).symm
    _ = ∑ h ∈ (univ : Finset (ZMod q)).erase 0, ‖fft f h‖^2 := by
      have es := (sum_erase_add univ (fun h : ZMod q => ‖fft f h‖^2) (mem_univ 0)).symm
      have hz2 : ‖fft f 0‖^2 = 0 := by rw [hz,norm_zero]; norm_num
      rw [hz2,add_zero] at es
      exact es
    _ = _ := sum_congr rfl fun h hh => by rw [hn h (mem_erase.mp hh).1]
