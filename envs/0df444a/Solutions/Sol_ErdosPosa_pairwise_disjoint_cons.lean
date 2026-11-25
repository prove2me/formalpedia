-- Prove2me | solution 1 for ErdosPosa.pairwise_disjoint_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:28:36.948715+00:00
-- url     : https://prove2.me/submissions/bb05d3a7-216f-4622-a640-456fd48f0517

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPShort
public import Definitions.Def_ErdosPosaLib_EPPacking
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution {k : ℕ} (X : Set V) (F : Fin k → Set V)
    (hF : Pairwise (fun i j => Disjoint (F i) (F j))) (hX : ∀ i, Disjoint X (F i)) :
    Pairwise (fun i j => Disjoint ((Fin.cons X F : Fin (k + 1) → Set V) i)
      ((Fin.cons X F : Fin (k + 1) → Set V) j)) := by
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact absurd rfl hij
    | succ j => simpa using hX j
  | succ i =>
    induction j using Fin.cases with
    | zero => simpa using (hX i).symm
    | succ j =>
      simp only [Fin.cons_succ]
      exact hF (fun h => hij (by rw [h]))
end ErdosPosa
