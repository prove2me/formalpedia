-- Prove2me | solution 1 for FamousTheorems.tendstolocallyuniformly_of_forall_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:01:38.707171+00:00
-- url     : https://prove2.me/submissions/97afa6c4-bccc-47d2-ab7f-aee872fe9d8e

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {ι : Type u_1} {α : Type u_2} {G : Type u_3} [inst : Preorder ι] 
    [inst_1 : TopologicalSpace α] [inst_2 : NormedAddCommGroup G] [inst_3 : Lattice G] [HasSolidNorm G] 
    [IsOrderedAddMonoid G] {F : ι → α → G} {f : α → G}, 
    (∀ (i : ι), Continuous (F i)) → 
    Monotone F → 
    Continuous f → (∀ (x : α), Tendsto (fun x_1 => F x_1 x) atTop (𝓝 (f x))) → TendstoLocallyUniformly F f atTop :=
  @_root_.Monotone.tendstoLocallyUniformly_of_forall_tendsto
