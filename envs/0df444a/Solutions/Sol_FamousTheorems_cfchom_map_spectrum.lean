-- Prove2me | solution 1 for FamousTheorems.cfchom_map_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T16:55:22.162413+00:00
-- url     : https://prove2.me/submissions/2e606b49-9fe0-474a-89c0-0a45b07258be

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [inst : CommSemiring R] [inst_1 : StarRing R] 
    [inst_2 : MetricSpace R] [inst_3 : IsTopologicalSemiring R] [inst_4 : ContinuousStar R] [inst_5 : TopologicalSpace A] 
    [inst_6 : Ring A] [inst_7 : StarRing A] [inst_8 : Algebra R A] [instCFC : ContinuousFunctionalCalculus R A p] {a : A} 
    (ha : p a) (f : C(↑(spectrum R a), R)), spectrum R ((cfcHom ha) f) = range ⇑f :=
  @_root_.cfcHom_map_spectrum
