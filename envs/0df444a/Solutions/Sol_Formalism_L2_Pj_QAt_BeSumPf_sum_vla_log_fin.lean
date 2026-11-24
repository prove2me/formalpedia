-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.BeSumPf.sum_vla_log_fin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:23:14.49563+00:00
-- url     : https://prove2.me/submissions/a5d26d4d-01ba-47e2-baef-6a9c5dcfb054

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumStatement
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinitePlaceArcs_BeSumPf
import Theorems.Thm_Formalism_L2_Pj_QAt_BeSumPf_maxPow_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
open NumberField IsDedekindDomain
open Formalism.L2.Pj.QAt.BeSumPf
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.Pj.QAt.BeSumPf
theorem _root_.solution (I : Ideal (𝓞 K)) (hI : I ≠ 0) (s : Finset (HeightOneSpectrum (𝓞 K)))
    (hs : ∀ v, vla v I ≠ 0 → v ∈ s) :
    ∑ v ∈ s, (vla v I : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) = Real.log (Ideal.absNorm I : ℝ) := by
  have hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) => v.maxPowDividing I) ⊆ ↑s := by
    intro v hv
    apply hs
    intro h0
    exact hv (by show v.maxPowDividing I = 1; rw [maxPow_eq, h0, pow_zero])
  have hfac : ∏ v ∈ s, v.maxPowDividing I = I := by
    rw [← finprod_eq_prod_of_mulSupport_subset _ hsub]
    exact Ideal.finprod_heightOneSpectrum_factorization hI
  have hN : (Ideal.absNorm I : ℝ) = ∏ v ∈ s, ((Ideal.absNorm v.asIdeal : ℝ)) ^ vla v I := by
    conv_lhs => rw [← hfac]
    rw [map_prod, Nat.cast_prod]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    rw [maxPow_eq, map_pow, Nat.cast_pow]
  rw [hN, Real.log_prod]
  · refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Real.log_pow]
  · intro v _
    apply pow_ne_zero
    exact Nat.cast_ne_zero.mpr (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
end Formalism.L2.Pj.QAt.BeSumPf
