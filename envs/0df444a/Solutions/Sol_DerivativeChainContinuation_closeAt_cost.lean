-- Prove2me | solution 1 for DerivativeChainContinuation.closeAt_cost
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T19:56:15.477647+00:00
-- url     : https://prove2.me/submissions/7569bce6-ddf8-4a5e-9c49-450324694dca

import Mathlib
import Definitions.Def_DerivativeChainContinuation_JoinedPaths
import Definitions.Def_DerivativeChainContinuation_ReturnPath
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability
open DerivativeChain DerivativeChainPrivate
open Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


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





set_option autoImplicit false
namespace DerivativeChainContinuation
open DerivativeChainPrivate
open scoped BigOperators



theorem joinAt_tail (M : ℕ) (hM : 1 ≤ M) (f z : ℕ → ℂ)
    (he : f (M-1)=z 0) (j : ℕ) : joinAt M f z (M-1+j)=z j := by
  by_cases hj : j=0
  · subst j; simp [joinAt,show M-1 < M by omega,he]
  · simp [joinAt,show ¬M-1+j < M by omega]

theorem joinAt_cost (M h : ℕ) (hM : 1 ≤ M) (f z : ℕ → ℂ)
    (he : f (M-1)=z 0) :
    chainCost (fun i : Fin (M+h) => joinAt M f z i) =
      (∑ i ∈ Finset.range (M-1), ‖f (i+1)-f i‖) +
      (∑ j ∈ Finset.range h, ‖z (j+1)-z j‖) := by
  rw [chainCost_eq_sum_range,show M+h-1=(M-1)+h by omega,Finset.sum_range_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp [joinAt,show i < M by omega,show i+1 < M by omega]
  · apply Finset.sum_congr rfl
    intro j _
    rw [show M-1+j+1=M-1+(j+1) by omega,joinAt_tail M hM f z he,joinAt_tail M hM f z he]







end DerivativeChainContinuation



set_option autoImplicit false
namespace DerivativeChainContinuation
open DerivativeChainPrivate
open scoped BigOperators





end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (r s : ℕ) (hr : 1 ≤ r) (hs : 0 < s) (f : ℕ → ℂ) (u : ℂ) :
    chainCost (fun i : Fin (r+s) => closeAt r f u i) =
      chainCost (fun i : Fin r => f i)+‖u-f (r-1)‖ := by
  let t : ℕ → ℂ := fun j => if j=0 then f (r-1) else u
  have he : (fun i : Fin (r+s) => closeAt r f u i) =
      (fun i : Fin (r+s) => joinAt r f t i) := by
    funext i
    by_cases hi : i.val < r
    · simp [closeAt,joinAt,hi]
    · simp [closeAt,joinAt,hi,t,show i.val-(r-1) ≠ 0 by omega]
  rw [he,joinAt_cost r s hr f t (by simp [t]),chainCost_eq_sum_range]
  congr 1
  rw [Finset.sum_eq_single 0]
  · simp [t]
  · intro j _ hj
    simp [t,hj]
  · intro hn
    exact (hn (Finset.mem_range.mpr hs)).elim
