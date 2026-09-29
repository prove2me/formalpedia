-- Prove2me | solution 1 for FamousTheorems.map_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:13:13.472999+00:00
-- url     : https://prove2.me/submissions/be434b60-f328-482d-8658-fe9f5559f01b

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {𝕜 : Type u_1} {E : Type u_2} {β : Type u_3} {ι : Type u_4} [inst : Field 𝕜] 
    [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [inst_3 : AddCommGroup E] [inst_4 : AddCommGroup β] 
    [inst_5 : PartialOrder β] [IsOrderedAddMonoid β] [inst_7 : Module 𝕜 E] [inst_8 : Module 𝕜 β] 
    [IsStrictOrderedModule 𝕜 β] {s : Set E} {f : E → β} {t : Finset ι} {w : ι → 𝕜} {p : ι → E}, 
    ConvexOn 𝕜 s f → 
    (∀ i ∈ t, 0 ≤ w i) → ∑ i ∈ t, w i = 1 → (∀ i ∈ t, p i ∈ s) → f (∑ i ∈ t, w i • p i) ≤ ∑ i ∈ t, w i • f (p i) :=
  @_root_.ConvexOn.map_sum_le
