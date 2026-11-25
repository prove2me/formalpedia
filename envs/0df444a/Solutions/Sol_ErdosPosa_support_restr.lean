-- Prove2me | solution 1 for ErdosPosa.support_restr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:33:19.294606+00:00
-- url     : https://prove2.me/submissions/0c97aeb9-e378-4c77-bcc1-2844e0bc375c

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMaximal
public import Definitions.Def_ErdosPosaLib_EPPin
public import Theorems.Thm_ErdosPosa_support_subset_of_adj


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution {G : SimpleGraph V} {X : Set V} {a b : V} (p : (restr G X).Walk a b)
    (ha : a ∈ X) : ∀ y ∈ p.support, y ∈ X :=
  support_subset_of_adj (fun a b (h : (restr G X).Adj a b) => h.2.2) p ha
end ErdosPosa
