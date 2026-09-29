-- Prove2me | solution 1 for FamousTheorems.exists_eigenvalue
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:13:04.931326+00:00
-- url     : https://prove2.me/submissions/180d14b0-f6cc-4913-8c3b-8e5a18aafa7f

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {K : Type u_1} {V : Type u_2} [inst : Field K] [inst_1 : AddCommGroup V] 
    [inst_2 : Module K V] [IsAlgClosed K] [FiniteDimensional K V] [Nontrivial V] (f : Module.End K V), 
    ∃ c, f.HasEigenvalue c :=
  @_root_.Module.End.exists_eigenvalue
