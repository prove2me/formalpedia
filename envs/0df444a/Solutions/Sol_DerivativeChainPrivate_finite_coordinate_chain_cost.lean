-- Prove2me | solution 1 for DerivativeChainPrivate.finite_coordinate_chain_cost
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T02:46:50.541139+00:00
-- url     : https://prove2.me/submissions/5c660cdc-13fd-4e4f-827b-23cba0cac2e8

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_northeast_chain_cost
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


open DerivativeChainPrivate in
theorem solution (n : ℕ) [NeZero n] (z : Fin n → ℂ) (last : Fin n)
    (hlast : last.val=n-1) (hre : Monotone (fun i => (z i).re))
    (him : Monotone (fun i => (z i).im)) :
    chainCost z ≤ Real.sqrt 2*‖z last-z 0‖ := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  let g : ℕ → ℂ := fun i => if hi : i < n then z ⟨i,hi⟩ else 0
  have hR : ∀ i < n-1, (g i).re ≤ (g (i+1)).re := by
    intro i hi
    have hi0 : i < n := by omega
    have hi1 : i+1 < n := by omega
    simp only [g,dif_pos hi0,dif_pos hi1]
    exact hre (show (⟨i,hi0⟩:Fin n) ≤ ⟨i+1,hi1⟩ from Nat.le_succ i)
  have hI : ∀ i < n-1, (g i).im ≤ (g (i+1)).im := by
    intro i hi
    have hi0 : i < n := by omega
    have hi1 : i+1 < n := by omega
    simp only [g,dif_pos hi0,dif_pos hi1]
    exact him (show (⟨i,hi0⟩:Fin n) ≤ ⟨i+1,hi1⟩ from Nat.le_succ i)
  have hh := northeast_chain_cost n g hR hI
  have hfun : (fun i : Fin n => g i.val)=z := by funext i; simp [g,i.isLt]
  rw [hfun] at hh
  have hl : n-1 < n := by omega
  have he : (⟨n-1,hl⟩:Fin n)=last := Fin.ext hlast.symm
  have hzero : (⟨0,hn⟩:Fin n)=0 := by apply Fin.ext; simp
  simpa only [g,dif_pos hl,dif_pos hn,he,hzero] using hh
