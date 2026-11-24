-- Prove2me | solution 1 for Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.log_htQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:39.726114+00:00
-- url     : https://prove2.me/submissions/44f4ccbf-9f31-470a-9695-fdea751fe30a

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_disc_pos
import Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_log_ht
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_saturation_basic_properties


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
    (L S : Submodule (𝓞 K) V) (hL : L.FG) (hS : S.FG) (hsat : IsSat (Formalism.HermitianLatticesTheory.realize b X) L S)
    (hpos : 0 < htQ b X L S) :
    Real.log (htQ b X L S) = Real.log (ht b X L) - Real.log (ht b X S) := by
  have hlat := (place_lattice_structure K V ι b X hX L hL).1
  have hq := ((saturation_basic_properties (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) L hlat).2.2.2.2.2.2.2 S hsat).2.2
  have hc : Formalism.F.covol (Formalism.F.quot (zl (Formalism.HermitianLatticesTheory.realize b X) L) (zl (Formalism.HermitianLatticesTheory.realize b X) S)) ≠ 0 := by
    intro h0
    rw [htQ, h0, mul_zero] at hpos
    exact lt_irrefl _ hpos
  have h2 : ((2 : ℝ) ^ ((nPl K : ℝ) * ((rkK L : ℝ) - rkK S))) ≠ 0 :=
    (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have h3 : |(NumberField.discr K : ℝ)| ^ (-((rkK L : ℝ) - rkK S) / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos disc_pos _).ne'
  rw [log_ht b X hX L hL, log_ht b X hX S hS, htQ, Real.log_mul (mul_ne_zero h2 h3) hc,
    Real.log_mul h2 h3, Real.log_rpow (by norm_num), Real.log_rpow disc_pos]
  have hq' : Real.log (Formalism.F.covol (Formalism.F.quot (zl (Formalism.HermitianLatticesTheory.realize b X) L)
      (zl (Formalism.HermitianLatticesTheory.realize b X) S))) =
      -(deg (Formalism.HermitianLatticesTheory.realize b X) L - deg (Formalism.HermitianLatticesTheory.realize b X) S) := by
    rw [← hq, Formalism.F.deg, neg_neg]
  rw [hq']
  simp only [logDisc]
  ring
end Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
