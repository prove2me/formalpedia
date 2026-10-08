-- Prove2me | solution 1 for BoundedNV.Stakes.eq54_55_single_crossing
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T23:14:53.901853+00:00
-- url     : https://prove2.me/submissions/b1999aeb-892a-4ba4-a578-ba1c49db8271

import Mathlib
import Definitions.Def_BoundedNV_ExpFam_Logit
open MeasureTheory

theorem solution (S : Set ℝ) (hSpos : 0 < volume S)
    (π : ℝ → ℝ) (β lam₁ lam₂ : ℝ) (hβ : 0 < β) (hlam : lam₂ < lam₁)
    (hint₁ : IntegrableOn (fun x => Real.exp (lam₁ * π x / β)) S)
    (hint₂ : IntegrableOn (fun x => Real.exp (lam₂ * π x / β)) S)
    (x : ℝ) (hx : x ∈ S) :
    let K := (∫ v in S, Real.exp (lam₁ * π v / β)) / (∫ v in S, Real.exp (lam₂ * π v / β))
    (BoundedNV.Uniform.logitDensity S (fun y => lam₂ * π y) β x < BoundedNV.Uniform.logitDensity S (fun y => lam₁ * π y) β x ↔
        K < Real.exp ((lam₁ * π x - lam₂ * π x) / β)) ∧
      (K < Real.exp ((lam₁ * π x - lam₂ * π x) / β) ↔
        β * Real.log K / (lam₁ - lam₂) < π x) := by
  haveI : NeZero (volume.restrict S) := ⟨by
    intro h
    have := congrArg (fun μ : Measure ℝ => μ Set.univ) h
    apply hSpos.ne'
    simpa using this⟩
  have h₁ : 0 < ∫ v in S, Real.exp (lam₁ * π v / β) := integral_exp_pos hint₁
  have h₂ : 0 < ∫ v in S, Real.exp (lam₂ * π v / β) := integral_exp_pos hint₂
  dsimp only
  constructor
  · simp only [BoundedNV.Uniform.logitDensity, Set.indicator_of_mem hx]
    rw [sub_div, Real.exp_sub]
    rw [div_lt_div_iff₀ h₂ h₁, div_lt_div_iff₀ h₂ (Real.exp_pos _)]
    constructor <;> intro h <;> nlinarith
  · rw [← Real.log_lt_log_iff (div_pos h₁ h₂) (Real.exp_pos _), Real.log_exp]
    rw [lt_div_iff₀ hβ, div_lt_iff₀ (sub_pos.mpr hlam)]
    constructor <;> intro h <;> nlinarith
#print axioms solution
