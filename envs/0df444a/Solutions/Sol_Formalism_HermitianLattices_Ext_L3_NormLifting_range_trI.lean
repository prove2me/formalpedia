-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.NormLifting.range_trI
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:25:32.039729+00:00
-- url     : https://prove2.me/submissions/683738c5-a890-4b9f-8adf-27dcb7d85cf5

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFiberMulCardRange
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_mem_fixSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_exists_trace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.NormLifting
variable {A : Type*} [CommRing A] (σ : A →+* A) (I : Ideal A)
variable {σ I}
namespace Formalism.HermitianLattices.Ext.L3.NormLifting
theorem _root_.solution (hσ : ∀ a, σ (σ a) = a) (hI : ∀ a ∈ I, σ a ∈ I) {θ e : A}
    (he : (θ - σ θ) * e = 1) : (trI σ I).range = fixSub σ I := by

  ext x
  rw [mem_fixSub, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨w, rfl⟩
    show ((w : A) + σ w) ∈ I ∧ σ ((w : A) + σ w) = (w : A) + σ w
    refine ⟨I.add_mem w.2 (hI _ w.2), ?_⟩
    rw [map_add, hσ, add_comm]
  · intro hx
    obtain ⟨v, hv, hv2⟩ := exists_trace hσ he ((mem_fixSub σ I).mpr hx)
    exact ⟨⟨v, hv⟩, hv2⟩
end Formalism.HermitianLattices.Ext.L3.NormLifting
