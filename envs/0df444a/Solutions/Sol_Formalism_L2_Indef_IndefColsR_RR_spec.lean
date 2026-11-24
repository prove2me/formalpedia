-- Prove2me | solution 1 for Formalism.L2.Indef.IndefColsR.RR_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:12:47.587638+00:00
-- url     : https://prove2.me/submissions/f0ba45ef-fdb0-4e3e-9363-090b49456c5b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity
import Theorems.Thm_Formalism_L2_Indef_matLat_lattice


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
open Formalism.L2.Indef.IndefColsR
variable {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}
  (S : IndefColsR Df Dc Sp N)
namespace Formalism.L2.Indef.IndefColsR
theorem _root_.solution (hG : LatticeGlue) (wf : Df.WF) :
    Submodule.IsLattice K S.RR ∧ ∀ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal S.RR =
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (S.ι (S.μ w)) (Df.abelian₂ (S.μ w))) := by
  have hfin : {w | S.μ w ≠ Bs.μ0}.Finite := S.Tw.finite_toSet.subset fun w hw => (S.h0.2 w).2 hw
  refine hG K S.D (matLat (S.ι Bs.μ0) (Df.abelian₂ Bs.μ0)) (fun w => matLat (S.ι (S.μ w)) (Df.abelian₂ (S.μ w)))
    (matLat_lattice _ (S.l1c.1 _).2 _ (wf.Lam_lat _)) (fun w => matLat_lattice _ (S.l1c.1 _).2 _ (wf.Lam_lat _))
    (hfin.subset fun w hw => ?_)
  intro h
  apply hw
  show Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (S.ι (S.μ w)) (Df.abelian₂ (S.μ w))) = _
  rw [h]
end Formalism.L2.Indef.IndefColsR
