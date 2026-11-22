-- Prove2me | solution 1 for DeciSigma1.Arithmetic.isChain_and
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:13:27.319797+00:00
-- url     : https://prove2.me/submissions/737ecc0a-00f6-49bb-baf2-b95da2c55501

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Mathlib.Order.Nat
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
variable {β : Type*}
namespace DeciSigma1.Arithmetic
theorem _root_.solution {R R' : β → β → Prop} :
    ∀ {p : List β}, p.IsChain R → p.IsChain R' → p.IsChain (fun x y => R x y ∧ R' x y)
  | [], _, _ => List.IsChain.nil
  | [_], _, _ => List.IsChain.singleton _
  | _ :: _ :: _, h, h' => by
    rw [List.isChain_cons_cons] at h h' ⊢
    exact ⟨⟨h.1, h'.1⟩, solution h.2 h'.2⟩
end DeciSigma1.Arithmetic
