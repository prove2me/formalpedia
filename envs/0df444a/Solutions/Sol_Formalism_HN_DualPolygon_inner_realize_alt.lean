-- Prove2me | solution 1 for Formalism.HN.DualPolygon.inner_realize_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:21.39883+00:00
-- url     : https://prove2.me/submissions/fc2d2503-d0df-4abc-af13-53ab77d595b5

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Theorems.Thm_Formalism_HN_DualPolygon_cE_apply
import Theorems.Thm_Formalism_HN_DualPolygon_ident_trace_eq
import Theorems.Thm_Formalism_HN_DualPolygon_ident_sum_fcoord
import Theorems.Thm_Formalism_HN_PlaceLattice_realize_apply0
import Theorems.Thm_Formalism_HN_PlaceLattice_realize_apply1


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
open Formalism Formalism.HN Formalism.HN.DualPolygon
open Formalism.HN
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.HN.DualPolygon
theorem _root_.solution [IsTotallyComplex K] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (x : V) (f : Module.Dual K V) :
    inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) ((2 : ℝ) • cE (Formalism.HermitianLatticesTheory.realize b.dualBasis (dualFrame X) f)) =
      ((Algebra.trace ℚ K (f x) : ℚ) : ℝ) := by
  rw [ident_trace_eq, PiLp.inner_apply]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, PiLp.smul_apply, cE_apply,
    PlaceLattice.realize_apply0, PlaceLattice.realize_apply1, RCLike.inner_apply, conj_trivial,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← ident_sum_fcoord b X hX v f x, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.mul_re, if_true, show ¬ ((1 : Fin 2) = 0) from by decide, if_false]
  ring
end Formalism.HN.DualPolygon
