-- Prove2me | solution 1 for Formalism.L2.DIV.residue_character_ramified_of_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:43:54.578866+00:00
-- url     : https://prove2.me/submissions/152a6d84-8712-416b-be06-6df1d29b80a9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_L2_DIV_d_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
namespace Formalism.L2.DIV
theorem _root_.solution (hExU : TpExU) (hW : TpWild) (hA : TpApprox) (hC : TpComap) (hO : TpOff)
    (hEx : ResCharEx) (hConj : ResCharConj) :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (_ : Module.finrank F E = 2) (L : Type) [Field L]
    (ξ : Chr F E L), (∀ v : HeightOneSpectrum (𝓞 F), wildAt E v ≤ ξ.ker) → (idF F E).range ≤ ξ.ker →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (P P' : HeightOneSpectrum (𝓞 E)), P ≠ P' →
      Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = P.asIdeal * P'.asIdeal →
      (v ∈ Qprime ξ ↔ resChar ξ P ≠ 1) := by
  intro F E _ _ _ _ _ hdeg L _ ξ ht hF v P P' hne hv
  have hk := d_key hExU hW hA hC hO hEx hConj hdeg ξ ht hF v P P' hne hv 1
  simp only [pow_one] at hk
  rw [Ne, ← hk]
  exact not_congr ⟨fun h x hx => MonoidHom.mem_ker.mp (h hx), fun h x hx => MonoidHom.mem_ker.mpr (h x hx)⟩
end Formalism.L2.DIV
