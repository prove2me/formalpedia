-- Prove2me | solution 1 for DerivativeChainContinuation.appell_centroid_return_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:33:54.609147+00:00
-- url     : https://prove2.me/submissions/8e9e880b-46a8-4961-8194-b2166e4376a4

import Mathlib
import Definitions.Def_DerivativeChainContinuation_AppellTranslation
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
import Theorems.Thm_DerivativeChainContinuation_appell_centroid_return_parameter
open DerivativeChain DerivativeChainPrivate
open Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false



set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate




end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (M h s q : ℕ) (hq : 2 ≤ q) (hqM : q ≤ M)
    (hs : 0 < s) (c : ℕ → ℂ) (hc0 : c 0=1)
    (hpref : ∀ j ≤ M, j ≠ 0 → j ≠ q → c j=0)
    (hreturn : ∀ j, M+h < j → j ≤ M+h+s → c j=0)
    (u a : ℂ) (D : ℝ) (hD : 0 ≤ D)
    (hbound : ∀ z : ℂ, (translatedAppell (M+h+s) c u).eval z=0 → ‖z-a‖ ≤ D) :
    ∃ z : Fin (M+h+s) → ℂ,
      (∀ i, (derivative^[M+h+s-(i.val+1)] (translatedAppell (M+h+s) c u)).eval (z i)=0) ∧
      z ⟨0,by omega⟩=u ∧ (∀ i, M+h ≤ i.val → z i=u) ∧
      chainCost z ≤ (1+Real.sqrt (h+1 : ℕ))*Real.sqrt (D^2-‖u-a‖^2) ∧
      (c q=0 → chainCost z ≤ (1+Real.sqrt h)*Real.sqrt (D^2-‖u-a‖^2)) := by
  classical
  let d := if c q=0 then h else h+1
  have hd : d=h+1 ∨ (d=h ∧ c q=0) := by
    by_cases hz : c q=0
    · exact Or.inr ⟨by simp [d,hz],hz⟩
    · exact Or.inl (by simp [d,hz])
  have hdl : d ≤ h+1 := by dsimp [d]; split_ifs <;> omega
  obtain ⟨z,hzr,hz0,hzt,hzc⟩ := appell_centroid_return_parameter M h s q d hq hqM hs c hc0
    hpref hreturn hd u a D hD hbound
  refine ⟨z,hzr,hz0,hzt,hzc.trans ?_,?_⟩
  · apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    have hh : (d:ℝ) ≤ (h+1:ℕ) := by exact_mod_cast hdl
    exact add_le_add (le_refl (1:ℝ)) (Real.sqrt_le_sqrt hh)
  · intro hz
    simpa only [d,if_pos hz] using hzc
