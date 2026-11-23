-- Prove2me | solution 1 for Formalism.L2.Indef.IndefRows.RR_spec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:48.93098+00:00
-- url     : https://prove2.me/submissions/8e2d574c-172d-4fc5-849f-fdb57b9acd0e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_JacquetSubsetSums_SeparationTR
import Definitions.Def_Formalism_DivisorInequality_StatementObj
import Definitions.Def_Formalism_QuotientMetricDivisors_DivIntoDualShift
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Theorems.Thm_Formalism_L2_Indef_matLat_lattice
import Theorems.Thm_Formalism_L2_Indef_twisted_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.L2.Indef
namespace IndefRows
theorem _root_.solution (hG : LatticeGlue) {Bs : DefBase K} {Df : DefSide Bs} (wf : Df.WF)
    (S : IndefRows Df) :
    Submodule.IsLattice K S.RR ∧ ∀ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal S.RR =
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (S.ι (S.μ w)) (Df.abelian₂ (S.μ w))) := by
  refine hG K S.D (matLat (S.ι Bs.μ0) (Df.abelian₂ Bs.μ0)) (fun w => matLat (S.ι (S.μ w)) (Df.abelian₂ (S.μ w)))
    (matLat_lattice _ (S.l1c.1 _).2 _ (wf.Lam_lat _)) (fun w => matLat_lattice _ (S.l1c.1 _).2 _ (wf.Lam_lat _))
    ((twisted_finite S).subset fun w hw => ?_)
  intro h
  apply hw
  show Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (S.ι (S.μ w)) (Df.abelian₂ (S.μ w))) = _
  rw [h]
end IndefRows
end Formalism.L2.Indef
