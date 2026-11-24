-- Prove2me | solution 1 for Formalism.NG.BlockDetAlt.coeff_det_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:09:40.457992+00:00
-- url     : https://prove2.me/submissions/ae139151-e267-481e-9d25-b671ffcf18e6

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IsUnitDetOfConst

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
open Formalism Formalism.NG
open Formalism.NG.BlockDetAlt
variable {O : Type*} [CommRing O] {X' : Type*}
variable {d : Type} [Fintype d] [DecidableEq d]
variable {K : Type*} [CommRing K]
namespace Formalism.NG.BlockDetAlt
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ)
    (U V : Matrix ι ι (PowerSeries K))
    (h : ∀ i j, ∀ k ≤ m, PowerSeries.coeff k (U i j) = PowerSeries.coeff k (V i j)) :
    PowerSeries.coeff m U.det = PowerSeries.coeff m V.det := by
  have hdiv : ∀ i j, (PowerSeries.X : PowerSeries K) ^ (m + 1) ∣ U i j - V i j := fun i j =>
    PowerSeries.X_pow_dvd_iff.2 (fun k hk => by rw [map_sub, h i j k (by omega), sub_self])
  have hUV : (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ (m + 1)})).mapMatrix U =
      (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ (m + 1)})).mapMatrix V := by
    ext i j
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (hdiv i j))
  have hdet : Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ (m + 1)}) U.det =
      Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries K) ^ (m + 1)}) V.det := by
    rw [RingHom.map_det, RingHom.map_det, hUV]
  have hd := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 hdet)
  have h0 := PowerSeries.X_pow_dvd_iff.1 hd m (by omega)
  rwa [map_sub, sub_eq_zero] at h0
end Formalism.NG.BlockDetAlt
