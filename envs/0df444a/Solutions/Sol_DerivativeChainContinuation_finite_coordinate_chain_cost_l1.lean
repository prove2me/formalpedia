-- Prove2me | solution 1 for DerivativeChainContinuation.finite_coordinate_chain_cost_l1
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T02:13:23.445095+00:00
-- url     : https://prove2.me/submissions/4d2f4640-a4b5-4e46-9a4e-2a7f282994a2

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
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







theorem chainCost_eq_sum_range {n : ℕ} (f : ℕ → ℂ) :
    chainCost (fun i : Fin n => f i.val) =
      ∑ i ∈ Finset.range (n - 1), ‖f (i + 1) - f i‖ := by
  unfold chainCost
  exact Fin.sum_univ_eq_sum_range (fun i => ‖f (i + 1) - f i‖) (n - 1)





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



theorem solution (n : ℕ) [NeZero n] (z : Fin n → ℂ)
    (last : Fin n) (hlast : last.val=n-1) (hre : Monotone (fun i => (z i).re))
    (him : Monotone (fun i => (z i).im)) :
    chainCost z ≤ (z last).re-(z 0).re+(z last).im-(z 0).im := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  let g : ℕ → ℂ := fun i => if hi : i < n then z ⟨i,hi⟩ else 0
  have hfun : (fun i : Fin n => g i.val)=z := by funext i; simp [g,i.isLt]
  have hstep (i : ℕ) (hi : i < n-1) : ‖g (i+1)-g i‖ ≤
      (g (i+1)).re-(g i).re+((g (i+1)).im-(g i).im) := by
    have hi0 : i < n := by omega
    have hi1 : i+1 < n := by omega
    have hr := hre (show (⟨i,hi0⟩:Fin n) ≤ ⟨i+1,hi1⟩ from Nat.le_succ i)
    have hm := him (show (⟨i,hi0⟩:Fin n) ≤ ⟨i+1,hi1⟩ from Nat.le_succ i)
    simpa only [g,dif_pos hi0,dif_pos hi1,Complex.sub_re,Complex.sub_im,
      abs_of_nonneg (sub_nonneg.mpr hr),abs_of_nonneg (sub_nonneg.mpr hm)] using
      Complex.norm_le_abs_re_add_abs_im (g (i+1)-g i)
  have hh : chainCost (fun i : Fin n => g i.val) ≤
      (g (n-1)).re-(g 0).re+((g (n-1)).im-(g 0).im) := by
    rw [chainCost_eq_sum_range]
    calc
      _ ≤ ∑ i ∈ Finset.range (n-1),
          ((g (i+1)).re-(g i).re+((g (i+1)).im-(g i).im)) :=
        Finset.sum_le_sum fun i hi => hstep i (Finset.mem_range.mp hi)
      _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_range_sub (fun i => (g i).re),Finset.sum_range_sub (fun i => (g i).im)]
  rw [hfun] at hh
  have hl : n-1 < n := by omega
  have he : (⟨n-1,hl⟩:Fin n)=last := Fin.ext hlast.symm
  have hzero : (⟨0,hn⟩:Fin n)=0 := by apply Fin.ext; simp
  simp only [g,dif_pos hl,dif_pos hn,he,hzero] at hh
  linarith
