-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x7.Hess.quotE_out
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:04.970935+00:00
-- url     : https://prove2.me/submissions/2eeaa7ec-c521-4817-b3ad-2de54debc507

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussIndexIndependentOfChoice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x7 Formalism.FourierDecayAlt.P.A6x7.Hess
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.A6x7.Hess
theorem _root_.solution (b : Kˣ) (Λ : AddSubgroup K) (y : K ⧸ Λ) :
    (Quotient.out (quotE b Λ y) : K) - (b : K) * (Quotient.out y : K) ∈ mulLat (b : K) Λ := by
  have h1 : ((Quotient.out (quotE b Λ y) : K) : K ⧸ mulLat (b : K) Λ) = quotE b Λ y :=
    QuotientAddGroup.out_eq' _
  have h2 : (((b : K) * (Quotient.out y : K) : K) : K ⧸ mulLat (b : K) Λ) = quotE b Λ y := by
    conv_rhs => rw [← QuotientAddGroup.out_eq' y]
    rfl
  have h3 := h2.trans h1.symm
  rw [QuotientAddGroup.eq] at h3
  rw [sub_eq_neg_add]
  exact h3
end Formalism.FourierDecayAlt.P.A6x7.Hess
