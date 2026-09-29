-- Prove2me | solution 1 for FamousTheorems.eigenvectorbasis_apply_self_apply
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T08:37:46.557227+00:00
-- url     : https://prove2.me/submissions/c1e4e1b2-372f-4fa7-bad7-cb67baaa0b65

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {E : Type u_2} 
    [inst_1 : NormedAddCommGroup E] [inst_2 : InnerProductSpace 𝕜 E] {T : E →ₗ[𝕜] E} [inst_3 : FiniteDimensional 𝕜 E] 
    {n : ℕ} (hT : T.IsSymmetric) (hn : Module.finrank 𝕜 E = n) (v : E) (i : Fin n), 
    ((hT.eigenvectorBasis hn).repr (T v)).ofLp i = ↑(hT.eigenvalues hn i) * ((hT.eigenvectorBasis hn).repr v).ofLp i :=
  @_root_.LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply
