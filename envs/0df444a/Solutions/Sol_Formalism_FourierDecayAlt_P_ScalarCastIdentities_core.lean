-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ScalarCastIdentities.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:12:52.781686+00:00
-- url     : https://prove2.me/submissions/c4a35111-07dd-41fe-951d-4ddcba826de7

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AlgebraicQuantumDeterminant
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ScalarCastIdentities
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
namespace Formalism.FourierDecayAlt.P.ScalarCastIdentities
theorem _root_.solution {A ι : Type*} [Ring A] [Fintype ι] (y η : ι → A) (C : A) (m1 m0 mm : ι → ι → A)
    (n0 nm : ι → ι → ι → ι → A)
    (hyη : ∀ a b, y a * η b = η b * y a)
    (J : ∀ i q l p, m1 i l * m0 q p - m1 q l * m0 i p = C * n0 i q l p)
    (DV : ∀ j, C * y j = y j * C - ∑ l, y l * m1 j l)
    (MC : ∀ q p i, m0 q p * η i - η i * m0 q p = ∑ a, n0 a q i p * η a)
    (BaseTypeSubspacesMapOntoBothSides : ∀ j, ∑ i, η i * mm i j = ∑ i, m0 i j * η i)
    (PairingFactorsThroughPeriods : ∀ j, ∑ i, η i * m0 i j = ∑ i, m1 i j * η i)
    (L3 : ∀ q c p, ∑ a, η a * nm a q c p = ∑ a, n0 a q c p * η a) (q p : ι) :
    C * (∑ a, ∑ c, η a * y c * nm a q c p) + (∑ j, y j * m1 q j) * (∑ i, η i * mm i p) =
      (∑ i, ∑ j, η i * y j * m0 i j) * m0 q p := by
  have h1 : ∑ a, ∑ c, η a * y c * nm a q c p = ∑ c, y c * ∑ a, n0 a q c p * η a := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← L3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hyη, mul_assoc]
  have h2 : ∑ i, ∑ j, η i * y j * m0 i j = ∑ j, y j * ∑ i, m1 i j * η i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← PairingFactorsThroughPeriods, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hyη, mul_assoc]
  rw [h1, h2, BaseTypeSubspacesMapOntoBothSides]
  have e1 : C * ∑ c, y c * ∑ a, n0 a q c p * η a =
      ∑ l, y l * (C * ∑ a, n0 a q l p * η a) - ∑ l, y l * ∑ c, m1 c l * ∑ a, n0 a q c p * η a := by
    rw [Finset.mul_sum]
    have : ∀ c, C * (y c * ∑ a, n0 a q c p * η a) =
        y c * (C * ∑ a, n0 a q c p * η a) - ∑ l, y l * (m1 c l * ∑ a, n0 a q c p * η a) := by
      intro c
      rw [← mul_assoc, DV, sub_mul, Finset.sum_mul, mul_assoc]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_assoc]
    rw [Finset.sum_congr rfl fun c _ => this c, Finset.sum_sub_distrib, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
  have e2 : (∑ j, y j * ∑ i, m1 i j * η i) * m0 q p =
      ∑ l, y l * (∑ i, m1 i l * (m0 q p * η i)) - ∑ l, y l * ∑ c, m1 c l * ∑ a, n0 a q c p * η a := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_assoc, Finset.sum_mul, ← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, ← mul_sub, ← MC, sub_sub_cancel]
  rw [e1, e2, sub_add_eq_add_sub]
  congr 1
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_assoc, ← mul_add]
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← add_mul, ← J, sub_add_cancel]
end Formalism.FourierDecayAlt.P.ScalarCastIdentities
