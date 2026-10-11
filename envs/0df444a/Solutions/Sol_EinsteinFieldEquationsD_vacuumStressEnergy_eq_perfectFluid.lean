-- Prove2me | solution 1 for EinsteinFieldEquationsD.vacuumStressEnergy_eq_perfectFluid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-11T07:01:13.485562+00:00
-- url     : https://prove2.me/submissions/ef5cfaf4-3d8f-4d7e-a2ad-7c717d7a5519

import Mathlib
import Definitions.Def_EinsteinFieldEquationsD_Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open EinsteinFieldEquationsD

theorem solution {D : ℕ} (g : Tensor2 D) (Λ κ : ℝ)
    (u : Coord D → Fin D → ℝ) :
    vacuumStressEnergy g Λ κ =
      perfectFluid g (Λ / κ) (-(Λ / κ)) u := by
  funext x a b
  simp [vacuumStressEnergy, perfectFluid]
