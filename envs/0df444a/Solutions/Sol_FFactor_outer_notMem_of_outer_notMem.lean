-- Prove2me | solution 1 for FFactor.outer_notMem_of_outer_notMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:02:56.558615+00:00
-- url     : https://prove2.me/submissions/dbbb5b73-e5c3-4c88-8ad3-f139179ce132

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
    (hT : ∀ i, (.inr ⟨v, i⟩ : GV G f) ∉ U) {z : G.Dart} (hz : z.fst = v)
    (hzU : (.inl z : GV G f) ∉ U) {d : G.Dart} (hd : d.fst = v) :
    (.inl d : GV G f) ∉ U := by
  intro hdU
  apply hmin _ hdU
  intro a b c ha hb hc
  let zv : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts :=
    ⟨.inl z, (mem_del_verts _).mpr hzU⟩
  have key : ∀ a : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts,
      (gadget G f).Adj (.inl d) a → a.val = .inl d.symm ∨ (del (gadget G f) U).Reachable a zv := by
    rintro ⟨a | ⟨w, i⟩, haU⟩ ha
    · left
      simp only [gadget_adj_inl_inl] at ha
      simp [ha]
    · right
      have hw : d.fst = w := ha
      obtain rfl : w = v := hw.symm.trans hd
      exact Adj.reachable ((del_adj _).mpr (show (gadget G f).Adj (.inr ⟨_, i⟩) (.inl z) from hz))
  have eqR : ∀ a b : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts, a.val = b.val →
      (del (gadget G f) U).Reachable a b := fun a b h => by rw [Subtype.ext h]
  have zR : ∀ a b : ((⊤ : (gadget G f).Subgraph).deleteVerts U).verts,
      (del (gadget G f) U).Reachable a zv → (del (gadget G f) U).Reachable b zv →
      (del (gadget G f) U).Reachable a b := fun _ _ h h' => h.trans h'.symm
  rcases key a ha with h1 | h1 <;> rcases key b hb with h2 | h2 <;>
    rcases key c hc with h3 | h3 <;>
    first
    | exact Or.inl (eqR _ _ (h1.trans h2.symm))
    | exact Or.inl (zR _ _ h1 h2)
    | exact Or.inr (Or.inl (eqR _ _ (h1.trans h3.symm)))
    | exact Or.inr (Or.inl (zR _ _ h1 h3))
    | exact Or.inr (Or.inr (eqR _ _ (h2.trans h3.symm)))
    | exact Or.inr (Or.inr (zR _ _ h2 h3))
end FFactor
