-- Prove2me | solution 1 for Formalism.UG.P.finite_support_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:09:25.409882+00:00
-- url     : https://prove2.me/submissions/ad21f25c-3987-4663-8658-1987b8a2f1f7

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FiniteCosetsInDoset
import Theorems.Thm_Formalism_UG_P_finite_cosets_in_doset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {G : Type} [Group G]
namespace Formalism.UG.P
theorem _root_.solution {k : Type} [Zero k] {K : Subgroup G} (hK : IsCommensurated K)
    {f : G → k} (hf : FinDosetSupp K f) :
    {x : G ⧸ K | f x.out ≠ 0}.Finite := by
  obtain ⟨S, hS⟩ := hf
  refine (S.finite_toSet.biUnion fun s _ => finite_cosets_in_doset hK s).subset ?_
  intro x hx
  obtain ⟨s, hs, a, b, h⟩ := hS _ hx
  exact Set.mem_biUnion hs ⟨a, b, h⟩
end Formalism.UG.P
