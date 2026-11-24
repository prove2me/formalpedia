-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.marker_mem_of_nonempty_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:22:09.920953+00:00
-- url     : https://prove2.me/submissions/5f318794-bf82-4a7e-b707-140c39113534

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*}
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution {w t : Word (Option A)}
    (hw : w ≠ []) (hpre : w <+: none :: t) : none ∈ w := by
  rcases List.prefix_cons_iff.mp hpre with hnil | ⟨v, rfl, _⟩
  · exact False.elim (hw hnil)
  · exact List.mem_cons_self
end BalanceSpecification.MarkerExtension
