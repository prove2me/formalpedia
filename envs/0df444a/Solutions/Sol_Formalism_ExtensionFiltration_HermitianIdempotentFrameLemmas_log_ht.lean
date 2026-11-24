-- Prove2me | solution 1 for Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.log_ht
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:19.599212+00:00
-- url     : https://prove2.me/submissions/b5833edc-23c2-4010-85c6-0439bb48e06e

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_disc_pos
import Theorems.Thm_Formalism_HN_place_lattice_structure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
open Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (L : Submodule (𝓞 K) V) (hL : L.FG) :
    Real.log (ht b X L) = (nPl K : ℝ) * (rkK L : ℝ) * Real.log 2 - (rkK L : ℝ) / 2 * logDisc K -
      deg (Formalism.HermitianLatticesTheory.realize b X) L := by
  have hpos := (place_lattice_structure K V ι b X hX L hL).2.2
  have hc : Formalism.F.covol (zl (Formalism.HermitianLatticesTheory.realize b X) L) ≠ 0 := by
    intro h0
    rw [ht, h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  have h2 : ((2 : ℝ) ^ (nPl K * rkK L)) ≠ 0 := by positivity
  have h3 : |(NumberField.discr K : ℝ)| ^ (-(rkK L : ℝ) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos disc_pos _).ne'
  rw [ht, Real.log_mul (mul_ne_zero h2 h3) hc, Real.log_mul h2 h3, Real.log_pow,
    Real.log_rpow disc_pos]
  simp only [deg, Formalism.F.deg, logDisc]
  push_cast
  ring
end Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
