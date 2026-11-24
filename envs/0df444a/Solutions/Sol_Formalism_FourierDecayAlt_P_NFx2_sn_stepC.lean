-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.NFx2.sn_stepC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:43:31.317192+00:00
-- url     : https://prove2.me/submissions/29ccebe3-494f-4a6c-9a91-43f130d6681b

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_kap_mul_pj
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_kGi
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_raises
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_ssGi
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_kxl_ss
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_kxl_sss

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
theorem _root_.solution (hc : RelCore (⟨L, κ, SS⟩ : Q.NFData P A)) (hs : Fr.IsStarLevel L) (j : ℕ) (τ : M.Ty P) (Y : ℂ) :
    Q.NFData.S12 (⟨L, κ, SS⟩ : Q.NFData P A) Y * (L.GGi * (SS j * proj κ τ)) =
      L.GGi * ∑ l ∈ Icc 1 (P.k - 1), sn_hsh P l j τ Y • (star (SS l) * SS j * proj κ τ) := by
  unfold Q.NFData.S12
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only
  have e1 : (κ fun ρ => M.xEx P {l} ρ Y) * star (SS l) * (L.GGi * (SS j * proj κ τ)) =
      L.GGi * (star (SS l) * ((κ fun ρ => M.xEx P {l} ρ Y) * SS j) * proj κ τ) := by
    rw [sn_kxl_sss hc l Y]
    have a := (sn_ssGi hc hs l).eq
    have b := (sn_kGi hc (fun ρ => M.xEx P {l} ρ Y)).eq
    calc star (SS l) * (κ fun ρ => M.xEx P {l} ρ Y) * (L.GGi * (SS j * proj κ τ))
        = star (SS l) * ((κ fun ρ => M.xEx P {l} ρ Y) * L.GGi) * SS j * proj κ τ := by noncomm_ring
      _ = (star (SS l) * L.GGi) * (κ fun ρ => M.xEx P {l} ρ Y) * SS j * proj κ τ := by rw [b]; noncomm_ring
      _ = _ := by rw [a]; noncomm_ring
  rw [e1, sn_kxl_ss (sn_raises hc) j l Y]
  rw [show star (SS l) * (SS j * κ fun ρ => sn_hsh P l j ρ Y) * proj κ τ =
      star (SS l) * SS j * ((κ fun ρ => sn_hsh P l j ρ Y) * proj κ τ) by noncomm_ring, kap_mul_pj,
    mul_smul_comm]
end Formalism.FourierDecayAlt.P.NFx2
