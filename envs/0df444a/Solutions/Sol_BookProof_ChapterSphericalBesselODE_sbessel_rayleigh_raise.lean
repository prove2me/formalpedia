-- Prove2me | solution 1 for BookProof.ChapterSphericalBesselODE.sbessel_rayleigh_raise
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:28:40.437325+00:00
-- url     : https://prove2.me/submissions/d086de0d-f017-4a20-90a4-7e69a3663c5e

-- Generated from ChapterSphericalBesselODE.lean — solution of BookProof.ChapterSphericalBesselODE.sbessel_rayleigh_raise
import Mathlib
import Definitions.Def_ChapterSphericalBesselODE
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_sbessel_eq
import Theorems.Thm_BookProof_ChapterSphericalBesselODE_deriv_gIter_eq
import Definitions.Def_ChapterSphericalBessel
open BookProof.ChapterSphericalBesselODE




open BookProof.ChapterSphericalBessel

set_option maxHeartbeats 1000000 in
theorem solution (l : ℕ) {r : ℝ} (hr : r ≠ 0) :
    sbessel (l + 1) r = -(r ^ l) * deriv (fun s => sbessel l s / s ^ l) r := by

  have hEq : (fun s : ℝ => sbessel l s / s ^ l) =ᶠ[nhds r] gIter l := by
    filter_upwards [isOpen_ne.mem_nhds hr] with s hs
    rw [sbessel_eq]
    field_simp
  rw [hEq.deriv_eq, deriv_gIter_eq l hr, sbessel_eq]
  ring
