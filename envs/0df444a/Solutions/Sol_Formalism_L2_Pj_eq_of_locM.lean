-- Prove2me | solution 1 for Formalism.L2.Pj.eq_of_locM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:33.713954+00:00
-- url     : https://prove2.me/submissions/bdc9e7cd-833a-46cb-ab1a-de0aee7e090c

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartWD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
variable {pts mapR borR}
namespace Formalism.L2.Pj
theorem _root_.solution {S : Type} [CommRing S] [Algebra K S] {x y : S}
    (h : ∀ (m : Ideal S) (_ : m.IsMaximal), locM K m x = locM K m y) : x = y := by
  rw [← sub_eq_zero]
  apply eq_zero_of_localization
  intro J hJ
  haveI := hJ
  have hxy := h J hJ
  simp only [locM, IsScalarTower.coe_toAlgHom'] at hxy
  rw [map_sub, hxy, sub_self]
end Formalism.L2.Pj
