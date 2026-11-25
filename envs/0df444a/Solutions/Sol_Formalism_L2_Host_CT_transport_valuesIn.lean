-- Prove2me | solution 1 for Formalism.L2.Host.CT.transport_valuesIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:12:46.657474+00:00
-- url     : https://prove2.me/submissions/f3384762-eb7d-4f65-9fe6-8b6bd18b5b23

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_UnrAe
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_CharTransport
import Theorems.Thm_Formalism_L2_Host_CT_plMap_plMap_symm
import Theorems.Thm_Formalism_L2_Host_CT_transport_valTw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open Formalism Formalism.L2 Formalism.L2.Host Formalism.L2.Host.CT
open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀
variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L]
namespace Formalism.L2.Host.CT
theorem _root_.solution (j : E ≃+* L) (χ : HChar L) (s : ℝ) {C : Type} [Field C] (e : C →+* ℂ) :
    (transport j χ).ValuesIn s e ↔ χ.ValuesIn s e := by
  constructor
  · intro h v hv
    have hv' : (transport j χ).UnrAt (plMap j.symm v) := (transport_unrAt_symm j χ v).2 hv
    obtain ⟨y, hy⟩ := h _ hv'
    refine ⟨y, hy.trans ?_⟩
    have h2 := transport_valTw j χ s (plMap j.symm v) (by rwa [plMap_plMap_symm])
    rwa [plMap_plMap_symm] at h2
  · intro h w hw
    have hw' : χ.UnrAt (plMap j w) := (transport_unrAt_iff j χ w).1 hw
    obtain ⟨y, hy⟩ := h _ hw'
    exact ⟨y, hy.trans (transport_valTw j χ s w hw').symm⟩
end Formalism.L2.Host.CT
