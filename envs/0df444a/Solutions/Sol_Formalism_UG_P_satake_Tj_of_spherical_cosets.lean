-- Prove2me | solution 1 for Formalism.UG.P.satake_Tj_of_spherical_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:35:10.830061+00:00
-- url     : https://prove2.me/submissions/ecd7f3e5-0746-43d9-a7ff-0fb603eac9fc

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Satake
import Theorems.Thm_Formalism_UG_P_satake_res_finite
import Theorems.Thm_Formalism_UG_P_satake_sum_chi
import Theorems.Thm_Formalism_UG_P_satake_value_one
import Theorems.Thm_Formalism_UG_P_satake_hAct_spherical

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution (hSphericalExists : Formalism.UG.SphericalExists) (hTjCosets : Formalism.UG.TjCosets) :
    Formalism.UG.SatakeTj := by
  intro F _ _ v n ϖ hϖ hu α hα φ hφ j hj
  have := satake_res_finite v hϖ hu
  let _ : Fintype (satakeRes (Ov F v) ⟨ϖ, hϖ⟩) := Fintype.ofFinite _
  obtain ⟨φ₀, -, -, huniq⟩ := hSphericalExists F v n α hα
  have hsph := satake_hAct_spherical v (ϖ := ϖ) j α φ hφ
  have h1 := satake_value_one v hϖ hu hTjCosets hj α φ hφ
  rw [satake_sum_chi v hϖ hu α j] at h1
  have e1 := huniq _ hsph
  have e2 := huniq φ hφ
  funext g
  have e1g : hAct (GLint (Fin n) (Ov F v)) (Tj ℂ n (Ov F v) ϖ j) φ g =
      hAct (GLint (Fin n) (Ov F v)) (Tj ℂ n (Ov F v) ϖ j) φ 1 * φ₀ g := congrFun e1 g
  have e2g : φ g = φ 1 * φ₀ g := congrFun e2 g
  rw [Pi.smul_apply, smul_eq_mul, e1g, h1, e2g]
  ring
end Formalism.UG.P
