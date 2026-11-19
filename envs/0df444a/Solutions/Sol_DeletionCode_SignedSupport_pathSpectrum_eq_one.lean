-- Prove2me | solution 1 for DeletionCode.SignedSupport.pathSpectrum_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:18:07.920771+00:00
-- url     : https://prove2.me/submissions/1a32160a-7682-4720-b1b6-3fd9715b1c8c

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport

set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators
namespace DeletionCode.SignedSupport
theorem _root_.solution (p : Letters) (L D : ℕ) (g : Gram L)
    (hinj : Function.Injective (fun i : Fin (D + 1) => gram p L i.val))
    (hg : g ∈ windowSet p L D) : pathSpectrum p L D g = 1 := by
  classical
  obtain ⟨i, hi⟩ := hg
  rw [← hi]
  simp only [pathSpectrum, hinj.eq_iff]
  have hsingle := Finset.sum_eq_single (s := Finset.univ)
    (f := fun j : Fin (D + 1) => if j = i then (1 : ℤ) else 0) i
    (fun j _ hji => if_neg hji)
    (fun hnot => False.elim (hnot (Finset.mem_univ i)))
  exact hsingle.trans (by simp)
end DeletionCode.SignedSupport
