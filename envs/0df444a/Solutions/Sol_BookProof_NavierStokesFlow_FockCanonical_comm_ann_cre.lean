-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockCanonical.comm_ann_cre
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T02:34:29.628741+00:00
-- url     : https://prove2.me/submissions/32df3b13-2f38-4993-9183-db1591027412

-- Generated from ChapterNavierStokesFockCanonical.lean — solution of BookProof.NavierStokesFlow.FockCanonical.comm_ann_cre
import Mathlib
import Definitions.Def_ChapterNavierStokesFockCanonical
import Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_ann_cre_coe
import Theorems.Thm_BookProof_NavierStokesFlow_FockCanonical_cre_ann_coe
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FockCanonical



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato ShiftHamiltonian FockManyMode HermiteCanonical

variable {d : ℕ} {κ : Fin d → ℝ}

variable {d : ℕ} {κ : Fin d → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (i : Fin d) :
    (ann i).comp (cre i) - (cre i).comp (ann i) = LinearMap.id := by

  refine LinearMap.ext fun x => Subtype.ext (lp.ext (funext fun α => ?_))
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, Submodule.coe_sub,
    lp.coeFn_sub, Pi.sub_apply, ann_cre_coe, cre_ann_coe]
  ring
