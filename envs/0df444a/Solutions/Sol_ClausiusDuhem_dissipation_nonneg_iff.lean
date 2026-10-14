-- Prove2me | solution 1 for ClausiusDuhem.dissipation_nonneg_iff
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-12T05:44:37.255562+00:00
-- url     : https://prove2.me/submissions/a3ab3b8a-d2b6-41ff-854a-5397ff30a016

import Definitions.Def_ClausiusDuhem_thermo_process
set_option autoImplicit false
open ClausiusDuhem
theorem solution (P : ThermoProcess) :
    (∀ t x, 0 ≤ P.dissipation t x) ↔ P.InternalEnergyInequality := by
  constructor
  · intro h t x
    have hh := h t x
    dsimp [ThermoProcess.dissipation] at hh
    nlinarith
  · intro h t x
    have hh := h t x
    dsimp [ThermoProcess.dissipation]
    nlinarith
#print axioms solution
