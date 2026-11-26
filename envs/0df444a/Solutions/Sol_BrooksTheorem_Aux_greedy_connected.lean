-- Prove2me | solution 1 for BrooksTheorem.Aux.greedy_connected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:37:44.708524+00:00
-- url     : https://prove2.me/submissions/0e0f1a16-f278-48b8-bd4b-a7b2d252197c

module
public import Definitions.Def_BrooksLib_BrooksCore
public import Definitions.Def_BrooksLib_Cycle
public import Definitions.Def_BrooksLib_BrooksLow
public import Theorems.Thm_BrooksTheorem_Aux_greedy_reach
public import Theorems.Thm_BrooksTheorem_Aux_mem_nb
public import Theorems.Thm_BrooksTheorem_Aux_restr_adj
attribute [local simp] BrooksTheorem.Aux.mem_nb
attribute [local simp] BrooksTheorem.Aux.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*} [Fintype V]
namespace BrooksTheorem.Aux
theorem _root_.solution (G : SimpleGraph V) (hconn : G.Connected) (k : ℕ)
    (hdeg : ∀ v, (nb G v).card ≤ k) (hdef : ∃ v0, (nb G v0).card < k) :
    ∃ f : V → Fin k, Proper G f := by
  classical
  obtain ⟨v0, hv0⟩ := hdef
  have hk : 0 < k := by omega
  have key : ∀ {a b : V} (p : G.Walk a b), (nb G b).card < k →
      near G ∅ (fun w => (nb G w).card < k) p.length a := by
    intro a b p
    induction p with
    | nil => exact id
    | cons h _ ihp => exact fun hb => ⟨_, h, by simp, ihp hb⟩
  obtain ⟨g, -, hg⟩ := greedy_reach G k hdeg ∅ (fun _ => ⟨0, hk⟩) (by simp)
    (fun w => (nb G w).card < k) (fun w _ hw => by simpa using hw)
    (fun w _ => ⟨_, key (hconn.preconnected w v0).some hv0⟩)
  exact ⟨g, hg⟩
end BrooksTheorem.Aux
