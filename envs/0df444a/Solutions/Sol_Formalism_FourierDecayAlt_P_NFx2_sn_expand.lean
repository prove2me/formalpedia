-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sn_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:21:21.509804+00:00
-- url     : https://prove2.me/submissions/03059e0b-e5e4-4c13-aec2-c744769fb60b

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx2
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.NF
noncomputable section
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {L : R.LevelData A P.r}
  {κ : (M.Ty P → ℂ) →ₐ[ℂ] A} {SS : ℕ → A}
namespace Formalism.FourierDecayAlt.P.NFx2
theorem _root_.solution {G Gi x xi m l S12 weightedSumBis : A} (hGG : Gi * G = 1) (hx : x * xi = 1) (hxi : xi * x = 1)
    (hmx : m * x = x * m) (hxGi : x * Gi = Gi * x) (hxiG : xi * G = G * xi) :
    (G * x * m + S12) * (Gi * xi) * (G * x * l + weightedSumBis) =
      G * x * m * l + G * m * Gi * weightedSumBis + S12 * l + S12 * (Gi * xi) * weightedSumBis := by
  have k1 : G * x * m * (Gi * xi) = G * m * Gi := by
    calc G * x * m * (Gi * xi) = G * (m * x) * Gi * xi := by rw [hmx]; noncomm_ring
      _ = G * m * (x * Gi) * xi := by noncomm_ring
      _ = G * m * Gi * (x * xi) := by rw [hxGi]; noncomm_ring
      _ = G * m * Gi := by rw [hx, mul_one]
  have k2 : Gi * xi * (G * x * l) = l := by
    calc Gi * xi * (G * x * l) = Gi * (xi * G) * x * l := by noncomm_ring
      _ = (Gi * G) * (xi * x) * l := by rw [hxiG]; noncomm_ring
      _ = l := by rw [hGG, hxi, one_mul, one_mul]
  have k3 : G * m * Gi * (G * x * l) = G * x * m * l := by
    calc G * m * Gi * (G * x * l) = G * m * (Gi * G) * x * l := by noncomm_ring
      _ = G * (m * x) * l := by rw [hGG]; noncomm_ring
      _ = G * x * m * l := by rw [hmx]; noncomm_ring
  calc (G * x * m + S12) * (Gi * xi) * (G * x * l + weightedSumBis)
      = (G * x * m * (Gi * xi)) * (G * x * l) + (G * x * m * (Gi * xi)) * weightedSumBis + S12 * (Gi * xi * (G * x * l)) +
          S12 * (Gi * xi) * weightedSumBis := by noncomm_ring
    _ = _ := by rw [k1, k2, k3]
end Formalism.FourierDecayAlt.P.NFx2
