-- Prove2me | solution 1 for FFactor.outer_notMem_of_inner_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:02:50.337291+00:00
-- url     : https://prove2.me/submissions/60449aca-2a20-409c-9551-6cd5a64e3719

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Definitions.Def_FFactorLib_FFactorGadget
public import Definitions.Def_FFactorLib_FFactorSuff
public import Theorems.Thm_FFactor_gadget_adj_inl_inl
public import Theorems.Thm_FFactor_gadget_adj_inl_inr
public import Theorems.Thm_FFactor_gadget_adj_inr_inl
public import Theorems.Thm_FFactor_gadget_adj_inr_inr
public import Theorems.Thm_FFactor_mem_del_verts
attribute [local simp] FFactor.gadget_adj_inl_inl
attribute [local simp] FFactor.gadget_adj_inl_inr
attribute [local simp] FFactor.gadget_adj_inr_inl
attribute [local simp] FFactor.gadget_adj_inr_inr
attribute [local simp] FFactor.mem_del_verts



set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {f : V → ℕ}
variable {U : Set (GV G f)}
namespace FFactor
theorem _root_.solution (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) {v : V}
    (hT : ∀ i, (.inr ⟨v, i⟩ : GV G f) ∈ U) {d : G.Dart} (hd : d.fst = v) :
    (.inl d : GV G f) ∉ U := by
  intro hdU
  apply hmin _ hdU
  intro a b c ha hb hc
  have key : ∀ a : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts,
      (gadget G f).Adj (.inl d) a → a.val = .inl d.symm := by
    rintro ⟨a | ⟨w, i⟩, haU⟩ ha
    · simp only [gadget_adj_inl_inl] at ha
      simp [ha]
    · have hw : d.fst = w := ha
      obtain rfl : w = v := hw.symm.trans hd
      exact absurd (hT i) ((mem_del_verts _).mp haU)
  have : a = b := Subtype.ext ((key a ha).trans (key b hb).symm)
  exact Or.inl (this ▸ Reachable.refl _)
end FFactor
