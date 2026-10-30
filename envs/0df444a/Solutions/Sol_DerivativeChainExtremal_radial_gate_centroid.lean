-- Prove2me | solution 1 for DerivativeChainExtremal.radial_gate_centroid
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:22:23.931109+00:00
-- url     : https://prove2.me/submissions/7fe905ee-c434-41a6-a06e-ca55a72c9a5d

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ExtremalGateExample
import Definitions.Def_DerivativeChainContinuation_CenteredSource
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
open DerivativeChainExtremal
open Polynomial DerivativeChainPrivate DerivativeChainContinuation







theorem solution : _root_.DerivativeChainContinuation.rootCentroid _root_.DerivativeChainExtremal.radialGateExample=0 := by
  have hlead : _root_.DerivativeChainExtremal.radialGateExample.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr (by
    intro h
    have hd := _root_.DerivativeChainExtremal.radial_gate_degree
    rw [h,natDegree_zero] at hd
    norm_num at hd)
  have hn : _root_.DerivativeChainExtremal.radialGateExample.nextCoeff=0 := by
    rw [nextCoeff,_root_.DerivativeChainExtremal.radial_gate_degree]
    norm_num [_root_.DerivativeChainExtremal.radialGateExample]
  have hs := (IsAlgClosed.splits _root_.DerivativeChainExtremal.radialGateExample).nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
  have hz : -_root_.DerivativeChainExtremal.radialGateExample.leadingCoeff*_root_.DerivativeChainExtremal.radialGateExample.roots.sum=0 := by
    simpa only [hn] using hs.symm
  have hsum : _root_.DerivativeChainExtremal.radialGateExample.roots.sum=0 := (mul_eq_zero.mp hz).resolve_left (neg_ne_zero.mpr hlead)
  simp only [_root_.DerivativeChainContinuation.rootCentroid,hsum,zero_div]
