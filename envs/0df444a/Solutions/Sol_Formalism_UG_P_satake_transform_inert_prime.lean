-- Prove2me | solution 1 for Formalism.UG.P.satake_transform_inert_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:38:07.124121+00:00
-- url     : https://prove2.me/submissions/31d95d97-177d-48a2-b2a1-4fe4635c176c

import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeConvolutionMemHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatake
import Theorems.Thm_Formalism_UG_P_fSatake_key
import Theorems.Thm_Formalism_UG_P_fSatake_hAct_sph

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (hSphericalExistsU : Formalism.UG.SphericalExistsU) : Formalism.UG.SatakeInert := by
  intro L _ _ _ ϖ σ q n m hU hm hm' α hα h hh φ hφ
  obtain ⟨φ0, -, -, huniq⟩ := hSphericalExistsU L ϖ σ q n m hU hm hm' α hα
  have h1 := huniq _ (fSatake_hAct_sph hh hφ)
  have h2 := huniq _ hφ
  have hv : hAct (KU σ n) h φ 1 = SatU ϖ q h α * φ 1 := by
    unfold hAct
    simp only [one_mul, smul_eq_mul]
    exact fSatake_key hSphericalExistsU hU hm hm' hα hh hφ
  rw [h1, hv]
  conv_rhs => rw [h2]
  funext g
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
end Formalism.UG.P
