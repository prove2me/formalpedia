-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieLDB.span_inf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:58:17.033315+00:00
-- url     : https://prove2.me/submissions/3e75b110-5d8a-46f5-82a7-fab9fd6e6d73

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDB
import Theorems.Thm_Formalism_L2_Pj_QAt_TieLDB_exists_smul_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.QAt.TieLDB
open Module
variable {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime]
  {V : Type*} [AddCommGroup V] [Module A V] [Module (Localization.AtPrime p) V]
  [IsScalarTower A (Localization.AtPrime p) V]
namespace Formalism.L2.Pj.QAt.TieLDB
theorem _root_.solution (M : Submodule A V) (W : Submodule (Localization.AtPrime p) V) :
    Submodule.span (Localization.AtPrime p) ((M ⊓ W.restrictScalars A : Submodule A V) : Set V) =
      Submodule.span (Localization.AtPrime p) (M : Set V) ⊓ W := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact ⟨Submodule.subset_span hx.1, hx.2⟩
  · rintro x ⟨hxM, hxW⟩
    obtain ⟨s, hs, hsx⟩ := exists_smul_mem p M hxM
    have hu := IsLocalization.map_units (Localization.AtPrime p) (⟨s, hs⟩ : p.primeCompl)
    have hmem : s • x ∈ Submodule.span (Localization.AtPrime p)
        ((M ⊓ W.restrictScalars A : Submodule A V) : Set V) :=
      Submodule.subset_span ⟨hsx, W.smul_of_tower_mem s hxW⟩
    have hx : x = hu.unit⁻¹ • (s • x) := by
      rw [← algebraMap_smul (Localization.AtPrime p) s x]
      change x = hu.unit⁻¹ • (hu.unit • x)
      rw [inv_smul_smul]
    rw [hx]
    exact Submodule.smul_of_tower_mem _ _ hmem
end Formalism.L2.Pj.QAt.TieLDB
