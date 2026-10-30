-- Prove2me | solution 1 for DerivativeChainExtremal.radial_gate_exactly_three_modes
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:32:20.653255+00:00
-- url     : https://prove2.me/submissions/2797488b-6ced-4b4a-aa5e-86f429db14aa

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ExtremalGateExample
import Definitions.Def_DerivativeChainContinuation_CenteredSource
import Definitions.Def_DerivativeChainContinuation_TwoModeChain
import Theorems.Thm_DerivativeChainExtremal_radial_gate_centroid
import Theorems.Thm_DerivativeChainExtremal_radial_gate_degree
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainExtremal
end DerivativeChainExtremal
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
namespace DerivativeChainExtremal
open Polynomial DerivativeChainPrivate DerivativeChainContinuation

















theorem radial_gate_beyond_two_modes : 3 ≤ (centeredModeSupport radialGateExample).card := by
  have hcent : centeredSource radialGateExample=radialGateExample := by simp [centeredSource,radial_gate_centroid]
  have hs : ({4,8,10}:Finset ℕ) ⊆ centeredModeSupport radialGateExample := by
    intro j hj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hj
    rcases hj with rfl|rfl|rfl
    all_goals
      simp only [centeredModeSupport,radial_gate_degree,hcent,Finset.mem_filter,Finset.mem_Icc]
      norm_num [radialGateExample]
  have hc := Finset.card_le_card hs
  norm_num at hc
  exact hc











end DerivativeChainExtremal


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
open DerivativeChainExtremal
open Polynomial DerivativeChainPrivate DerivativeChainContinuation



















theorem solution : (_root_.DerivativeChainContinuation.centeredModeSupport _root_.DerivativeChainExtremal.radialGateExample).card=3 := by
  have hcent : _root_.DerivativeChainContinuation.centeredSource _root_.DerivativeChainExtremal.radialGateExample=_root_.DerivativeChainExtremal.radialGateExample := by simp [_root_.DerivativeChainContinuation.centeredSource,_root_.DerivativeChainExtremal.radial_gate_centroid]
  have hs : _root_.DerivativeChainContinuation.centeredModeSupport _root_.DerivativeChainExtremal.radialGateExample ⊆ ({4,8,10}:Finset ℕ) := by
    intro j hj
    simp only [_root_.DerivativeChainContinuation.centeredModeSupport,_root_.DerivativeChainExtremal.radial_gate_degree,Finset.mem_filter,Finset.mem_Icc] at hj
    obtain ⟨⟨hj2,hj10⟩,hne⟩ := hj
    rw [hcent] at hne
    interval_cases j <;> norm_num [_root_.DerivativeChainExtremal.radialGateExample] at *
  have hc := Finset.card_le_card hs
  norm_num at hc
  exact le_antisymm hc _root_.DerivativeChainExtremal.radial_gate_beyond_two_modes
