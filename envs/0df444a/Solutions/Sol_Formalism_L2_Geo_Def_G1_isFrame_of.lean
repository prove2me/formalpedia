-- Prove2me | solution 1 for Formalism.L2.Geo.Def.G1.isFrame_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:12:34.297795+00:00
-- url     : https://prove2.me/submissions/47ad5caf-faad-4df6-a01d-5074e2acefe7

import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_QuotientMetricDivisors_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_DualFrame
import Theorems.Thm_Formalism_L2_Geo_Def_G1_hform_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Matrix
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.G1
variable {K : Type} [Field K] [StarRing K]
namespace Formalism.L2.Geo.Def.G1
theorem _root_.solution {n k : ℕ} (H : Matrix (Fin n) (Fin n) K) (g w : Fin k → Fin n → K)
    (h : ∀ z : Fin n → K, z = ∑ i, Formalism.DivisionValues.hform H (w i) z • g i) : IsFrame H g w := by
  intro a b
  have key := congrFun (h (Pi.single b 1)) a
  rw [Finset.sum_apply] at key
  simp only [Pi.smul_apply, smul_eq_mul, hform_eq, Formalism.UG.hform, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, starRingEnd_apply] at key
  rw [key]
  exact Finset.sum_congr rfl fun i _ => by ring
end Formalism.L2.Geo.Def.G1
