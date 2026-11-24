-- Prove2me | solution 1 for FFactor.reach_inner_of_reachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:09:56.647974+00:00
-- url     : https://prove2.me/submissions/325baac4-03ed-4087-95a2-228623b9976a

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Definitions.Def_FFactorLib_FFactorGadget
public import Definitions.Def_FFactorLib_FFactorSuff
public import Theorems.Thm_FFactor_exists_inner_of_notMem_Tset
public import Theorems.Thm_FFactor_reach_inner
public import Theorems.Thm_FFactor_reach_inner_inner
public import Theorems.Thm_FFactor_mem_del_verts
attribute [local simp] FFactor.mem_del_verts



set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {f : V → ℕ}
variable [DecidableEq V] {U : Set (GV G f)}
namespace FFactor
theorem _root_.solution (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x)
    {u w : ↥(((Sset G f U ∪ Tset G f U : Finset V) : Set V)ᶜ)} (p : (Gr G f U).Walk u w) :
    ∀ (i : Fin (G.degree u.1 - f u.1)) (i' : Fin (G.degree w.1 - f w.1)),
    (del (gadget G f) U).Reachable
      ⟨.inr ⟨u.1, i⟩, (mem_del_verts _).mpr (F1 hmin (notMem_T_of_notMem_union u.2) i)⟩
      ⟨.inr ⟨w.1, i'⟩, (mem_del_verts _).mpr (F1 hmin (notMem_T_of_notMem_union w.2) i')⟩ := by
  induction p with
  | @nil x =>
    intro i i'
    exact reach_inner hmin x.2 (.inr ⟨_, i⟩) (F1 hmin (notMem_T_of_notMem_union x.2) i) rfl i'
  | @cons a b c hadj p ih =>
    intro i i'
    obtain ⟨i'', -⟩ := exists_inner_of_notMem_Tset (notMem_T_of_notMem_union b.2)
    exact (reach_inner_inner hmin a.2 b.2 hadj i i'').trans (ih i'' i')
end FFactor
