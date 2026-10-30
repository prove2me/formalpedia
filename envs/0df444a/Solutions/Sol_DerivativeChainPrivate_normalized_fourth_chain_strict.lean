-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_fourth_chain_strict
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T04:27:49.25448+00:00
-- url     : https://prove2.me/submissions/7694d221-f824-485e-8740-f14999ec49de

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChainPrivate_higher_power_radicals
import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Theorems.Thm_DerivativeChainPrivate_normalized_fourth_octic_step
import Theorems.Thm_DerivativeChainPrivate_normalized_fourth_prefix_five
import Theorems.Thm_DerivativeChainPrivate_normalized_fourth_selected_sextic_step
import Theorems.Thm_DerivativeChainPrivate_normalized_fourth_septic_step
import Theorems.Thm_DerivativeChainPrivate_normalized_fourth_source_step
import Theorems.Thm_DerivativeChainPrivate_northeast_chain_cost
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


open Polynomial DerivativeChainPrivate
set_option autoImplicit false



set_option autoImplicit false

namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial









end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate













end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
open scoped BigOperators
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem power_root_inherited_derivative (q : Polynomial ℂ) (h k : ℕ)
    (z : ℂ) (hz : q.eval z = 0) (hk : k < h) :
    (Polynomial.derivative^[k] (q ^ h)).eval z = 0 := by
  obtain ⟨p, hp⟩ := Polynomial.pow_sub_dvd_iterate_derivative_pow q h k
  rw [hp, Polynomial.eval_mul, Polynomial.eval_pow, hz,
    zero_pow (show h - k ≠ 0 by omega), zero_mul]



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate











end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial







end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
open Filter Topology
namespace DerivativeChainPrivate
open Polynomial











end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate





set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem normalized_fourth_power_expansion (β : ℂ) :
    ((X^3 - C (11/2) * X - 55 * C β)^4 : Polynomial ℂ) =
      C (1) * X^12 +
      C (-22) * X^10 +
      C (-220*β) * X^9 +
      C (363/2) * X^8 +
      C (3630*β) * X^7 +
      C (18150*β^2 - 1331/2) * X^6 +
      C (-19965*β) * X^5 +
      C (14641/16 - 199650*β^2) * X^4 +
      C (-665500*β^3 + 73205*β/2) * X^3 +
      C (1098075*β^2/2) * X^2 +
      C (3660250*β^3) * X^1 +
      C (9150625*β^4) * X^0 := by
  apply Polynomial.funext
  intro z
  simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat]
  ring

theorem normalized_fourth_power_actual_rows (β z : ℂ) :
    let p : Polynomial ℂ := (X^3 - C (11/2) * X - 55 * C β)^4
    (derivative^[4] p).eval z = 11880 * (550*β^2*z^2 - 1210*β^2/3 - 56*β*z^5 + 770*β*z^3/3 - 605*β*z/3 + z^8 - 28*z^6/3 + 77*z^4/3 - 121*z^2/6 + 1331/720) ∧
    (derivative^[5] p).eval z = 95040 * (275*β^2*z/2 - 35*β*z^4 + 385*β*z^2/4 - 605*β/24 + z^7 - 7*z^5 + 77*z^3/6 - 121*z/24) ∧
    (derivative^[6] p).eval z = 665280 * (275*β^2/14 - 20*β*z^3 + 55*β*z/2 + z^6 - 5*z^4 + 11*z^2/2 - 121/168) ∧
    (derivative^[7] p).eval z = 3991680 * (-10*β*z^2 + 55*β/12 + z^5 - 10*z^3/3 + 11*z/6) ∧
    (derivative^[8] p).eval z = 19958400 * (-4*β*z + z^4 - 2*z^2 + 11/30) ∧
    (derivative^[9] p).eval z = 79833600 * (-β + z^3 - z) ∧
    (derivative^[10] p).eval z = 239500800 * (z^2 - 1/3) ∧
    (derivative^[11] p).eval z = 479001600 * (z) := by
  let p : Polynomial ℂ := (X^3 - C (11/2) * X - 55 * C β)^4
  have hexpand := normalized_fourth_power_expansion β
  change p = _ at hexpand
  dsimp only
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ⟩
  all_goals change (derivative^[_] p).eval z = _
  all_goals rw [hexpand]
  all_goals simp only [iterate_map_add, iterate_derivative_C_mul,
    iterate_derivative_X_pow_eq_C_mul, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  all_goals norm_num [Nat.descFactorial] <;> ring





end DerivativeChainPrivate

open DerivativeChainPrivate in
theorem solution (β : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im) :
    ∃ z : Fin 12 → ℂ,
      (∀ i, (derivative^[12-(i.val+1)] ((X^3-C (11/2)*X-55*C β)^4)).eval (z i)=0) ∧
      z 0=0 ∧ (∀ i : Fin 12, 8 ≤ i.val → z i=z 11) ∧
      (z 11)^3-(11/2)*z 11-55*β=0 ∧
      Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      chainCost z ≤ Real.sqrt 2*‖z 11‖ := by
  obtain ⟨f,hfroot,hf0,hfr,hfi,hfpos,hfX,hfinv⟩ := normalized_fourth_prefix_five β hR hI.le
  have hfim : 0 ≤ (f 4).im := by
    have hh := hfi (show (0:Fin 5) ≤ 4 by decide)
    simpa only [hf0,Complex.zero_im] using hh
  have hfQ : (f 4)^5-(10/3)*(f 4)^3-10*β*(f 4)^2+(11/6)*(f 4)+(55/12)*β=0 := by
    have hh := hfroot 4
    change (derivative^[7] ((X^3-C (11/2)*X-55*C β)^4)).eval (f 4)=0 at hh
    rw [(normalized_fourth_power_actual_rows β (f 4)).2.2.2.1] at hh
    linear_combination (1/3991680:ℂ)*hh
  obtain ⟨μ,hfinite,hsupp,hμ,w₆,hw₆,h₅₆r,h₅₆i,h₆i,h₆loc,h₆graph⟩ :=
    normalized_fourth_selected_sextic_step β (f 4) hR hI hfpos hfim hfX hfQ hfinv
  letI : IsFiniteMeasure μ := hfinite
  have h₆r : 0 < w₆.re := lt_of_lt_of_le hfpos h₅₆r
  obtain ⟨w₇,hw₇,h₆₇r,h₆₇i,h₇X,h₇graph⟩ := normalized_fourth_septic_step μ hsupp hμ β w₆ hR hI h₆r h₆i h₆loc.le hw₆ h₆graph
  have h₇r : 0 < w₇.re := lt_of_lt_of_le h₆r h₆₇r
  have h₇i : 0 < w₇.im := lt_of_lt_of_le h₆i h₆₇i
  obtain ⟨w₈,hw₈,h₇₈r,h₇₈i,h₈graph⟩ := normalized_fourth_octic_step β w₇ hR hI h₇r h₇i h₇X.le hw₇ h₇graph
  have h₈r : 0 < w₈.re := lt_of_lt_of_le h₇r h₇₈r
  have h₈i : 0 < w₈.im := lt_of_lt_of_le h₇i h₇₈i
  have h₈X : 4 ≤ w₈.re^2 := by nlinarith only [h₇X,h₇r,h₇₈r]
  obtain ⟨ρ,hρ,h₈ρr,h₈ρi⟩ := normalized_fourth_source_step β w₈ hR hI h₈r h₈i h₈X hw₈ h₈graph
  let g : ℕ → ℂ
    | 0 => f 0
    | 1 => f 1
    | 2 => f 2
    | 3 => f 3
    | 4 => f 4
    | 5 => w₆
    | 6 => w₇
    | 7 => w₈
    | _ => ρ
  have hre : ∀ i < 11, (g i).re ≤ (g (i+1)).re := by
    intro i hi
    interval_cases i <;> simp only [g]
    · exact hfr (by decide : (0:Fin 5) ≤ 1)
    · exact hfr (by decide : (1:Fin 5) ≤ 2)
    · exact hfr (by decide : (2:Fin 5) ≤ 3)
    · exact hfr (by decide : (3:Fin 5) ≤ 4)
    · exact h₅₆r
    · exact h₆₇r
    · exact h₇₈r
    · exact h₈ρr
    all_goals exact le_rfl
  have him : ∀ i < 11, (g i).im ≤ (g (i+1)).im := by
    intro i hi
    interval_cases i <;> simp only [g]
    · exact hfi (by decide : (0:Fin 5) ≤ 1)
    · exact hfi (by decide : (1:Fin 5) ≤ 2)
    · exact hfi (by decide : (2:Fin 5) ≤ 3)
    · exact hfi (by decide : (3:Fin 5) ≤ 4)
    · exact h₅₆i
    · exact h₆₇i
    · exact h₇₈i
    · exact h₈ρi
    all_goals exact le_rfl
  have hqρ : (X^3-C (11/2)*X-55*C β : Polynomial ℂ).eval ρ=0 := by
    simpa only [eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat] using hρ
  have hrows (i : ℕ) (hi : i < 12) :
      (derivative^[12-(i+1)] ((X^3-C (11/2)*X-55*C β)^4)).eval (g i)=0 := by
    interval_cases i
    · simpa [g] using hfroot 0
    · simpa [g] using hfroot 1
    · simpa [g] using hfroot 2
    · simpa [g] using hfroot 3
    · simpa [g] using hfroot 4
    · rw [(normalized_fourth_power_actual_rows β (g 5)).2.2.1]
      simp only [g]
      linear_combination 665280*hw₆
    · rw [(normalized_fourth_power_actual_rows β (g 6)).2.1]
      simp only [g]
      linear_combination 95040*hw₇
    · rw [(normalized_fourth_power_actual_rows β (g 7)).1]
      simp only [g]
      linear_combination 11880*hw₈
    · exact power_root_inherited_derivative _ 4 3 ρ hqρ (by norm_num)
    · exact power_root_inherited_derivative _ 4 2 ρ hqρ (by norm_num)
    · exact power_root_inherited_derivative _ 4 1 ρ hqρ (by norm_num)
    · exact power_root_inherited_derivative _ 4 0 ρ hqρ (by norm_num)
  refine ⟨fun i => g i.val,fun i => hrows i.val i.isLt,?_,?_,hρ,?_,?_,?_⟩
  · exact hf0
  · intro i hi
    fin_cases i <;> norm_num at hi <;> rfl
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact hre i.val i.isLt
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact him i.val i.isLt
  · simpa only [g,hf0,sub_zero,Nat.reduceSub] using northeast_chain_cost 12 g hre him
