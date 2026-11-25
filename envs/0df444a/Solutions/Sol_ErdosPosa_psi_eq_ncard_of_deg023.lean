-- Prove2me | solution 1 for ErdosPosa.psi_eq_ncard_of_deg023
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:35:17.866806+00:00
-- url     : https://prove2.me/submissions/d5cf454e-189d-4bd7-adf4-bb92ac3f8645

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPPin
public import Definitions.Def_ErdosPosaLib_EPMain
public import Theorems.Thm_ErdosPosa_ncard_eq_sum_ite
public import Theorems.Thm_ErdosPosa_restr_adj
attribute [local simp] ErdosPosa.restr_adj



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
namespace ErdosPosa
theorem _root_.solution [Fintype V] {H : SimpleGraph V} (hH : Deg023 H) :
    psi H = ({v | deg H v = 3}.ncard : ℤ) := by
  classical
  rw [ncard_eq_sum_ite]
  push_cast
  unfold psi
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rcases hH v with h | h | h <;> simp [h, wt]
end ErdosPosa
