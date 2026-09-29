-- Prove2me | solution 1 for FamousTheorems.to_localinverse
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T12:40:08.98572+00:00
-- url     : https://prove2.me/submissions/5dcb3801-2617-40d9-90d6-0b4026759f42

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] [inst_1 : CompleteSpace 𝕜] 
    {f : 𝕜 → 𝕜} {f' a : 𝕜} (hf : HasStrictDerivAt f f' a) (hf' : f' ≠ 0), 
    HasStrictDerivAt (HasStrictDerivAt.localInverse f f' a hf hf') f'⁻¹ (f a) :=
  @_root_.HasStrictDerivAt.to_localInverse
