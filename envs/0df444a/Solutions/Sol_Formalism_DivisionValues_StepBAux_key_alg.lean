-- Prove2me | solution 1 for Formalism.DivisionValues.StepBAux.key_alg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:04:17.020091+00:00
-- url     : https://prove2.me/submissions/10feebc2-36d4-4b27-ad57-77c0262bbe88

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ProdFormula
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LcvBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_RatHerm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_LocBasis
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open Formalism.DivisionValues.StepBAux
namespace Formalism.DivisionValues.StepBAux
theorem _root_.solution {J : Type} [Fintype J] (D : ℕ) (gE0 gE1 dR0 dR1 G0 G1 Ny κ ρ : ℂ)
    (gW0 gW1 dθ0 dθ1 gT0 gT1 Nz : J → ℂ)
    (h1 : gE1 = Ny * gE0) (h21 : gE1 = dR1 * G1) (h20 : gE0 = dR0 * G0)
    (h31 : dR1 = (κ * ρ) ^ D * ∏ j, dθ1 j) (h30 : dR0 = κ ^ D * ∏ j, dθ0 j)
    (h4 : ∀ j, gW1 j = Nz j * gW0 j) (h51 : ∀ j, gW1 j = dθ1 j * gT1 j)
    (h50 : ∀ j, gW0 j = dθ0 j * gT0 j) (hκ : κ ≠ 0) (hθ : ∀ j, dθ0 j ≠ 0) :
    ρ ^ D * G1 * ∏ j, (Nz j * gT0 j) = Ny * G0 * ∏ j, gT1 j := by
  have hP : (∏ j, dθ1 j) * ∏ j, gT1 j = (∏ j, dθ0 j) * ∏ j, (Nz j * gT0 j) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [← h51, h4, h50]; ring
  have hne : κ ^ D * ∏ j, dθ0 j ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hκ) (Finset.prod_ne_zero_iff.mpr fun j _ => hθ j)
  apply mul_right_cancel₀ hne
  calc (ρ ^ D * G1 * ∏ j, (Nz j * gT0 j)) * (κ ^ D * ∏ j, dθ0 j)
      = (κ * ρ) ^ D * G1 * ((∏ j, dθ0 j) * ∏ j, (Nz j * gT0 j)) := by rw [mul_pow]; ring
    _ = (κ * ρ) ^ D * G1 * ((∏ j, dθ1 j) * ∏ j, gT1 j) := by rw [hP]
    _ = gE1 * ∏ j, gT1 j := by rw [h21, h31]; ring
    _ = Ny * (dR0 * G0) * ∏ j, gT1 j := by rw [h1, h20]
    _ = (Ny * G0 * ∏ j, gT1 j) * (κ ^ D * ∏ j, dθ0 j) := by rw [h30]; ring
end Formalism.DivisionValues.StepBAux
