-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockCanonical.bracket_DS
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-03T02:33:55.845992+00:00
-- url     : https://prove2.me/submissions/af308d31-ab5d-496f-9c42-c117f32c0898

-- Generated from ChapterNavierStokesFockCanonical.lean — solution of BookProof.NavierStokesFlow.FockCanonical.bracket_DS
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
    (cre i - ann i).comp (cre i + ann i) - (cre i + ann i).comp (cre i - ann i)
      = (-2 : ℂ) • LinearMap.id := by

  refine LinearMap.ext fun x => Subtype.ext (lp.ext (funext fun α => ?_))
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_add, map_sub, Submodule.coe_sub, Submodule.coe_add, Submodule.coe_smul,
    lp.coeFn_sub, lp.coeFn_add, lp.coeFn_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, ann_cre_coe, cre_ann_coe]
  ring
