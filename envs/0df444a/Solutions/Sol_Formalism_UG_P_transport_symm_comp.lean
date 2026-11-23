-- Prove2me | solution 1 for Formalism.UG.P.transport_symm_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:26.230946+00:00
-- url     : https://prove2.me/submissions/64bf8d18-5ffd-4c05-80eb-327005442561

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Transport

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
namespace Formalism.UG.P
theorem _root_.solution {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) (σ' : B →+* B)
    (φ : A ≃+* B) (h : (φ : A →+* B).comp σ = σ'.comp φ) :
    (φ.symm : B →+* A).comp σ' = σ.comp φ.symm := by
  ext x
  have h1 := RingHom.congr_fun h (φ.symm x)
  simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply] at h1 ⊢
  rw [← h1, RingEquiv.symm_apply_apply]
end Formalism.UG.P
