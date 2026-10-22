-- Prove2me | solution 1 for DirS.bip_dir_density
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T21:49:36.656764+00:00
-- url     : https://prove2.me/submissions/6aed87ee-92d3-4891-8f20-c7c7d1214976

import Mathlib
import Definitions.Def_DirS_gr
import Definitions.Def_DirS_gw
open DirS

theorem g73t_oe_ll {m n : ℕ} (H : BipGraph m n) (i j : Fin m) :
    orientEdge m n H (Fin.castAdd n i) (Fin.castAdd n j) = false := by
  unfold orientEdge
  rw [dif_neg]
  simp only [Fin.val_castAdd, not_and, not_le]
  intro _; exact j.isLt

theorem g73t_oe_lr {m n : ℕ} (H : BipGraph m n) (i : Fin m) (j : Fin n) :
    orientEdge m n H (Fin.castAdd n i) (Fin.natAdd m j) = H.adj i j := by
  unfold orientEdge
  rw [dif_pos ⟨by simp, by simp⟩]
  congr 1
  ext; simp

theorem g73t_oe_r {m n : ℕ} (H : BipGraph m n) (i : Fin n) (y : Fin (m + n)) :
    orientEdge m n H (Fin.natAdd m i) y = false := by
  unfold orientEdge
  rw [dif_neg]
  simp

theorem solution (dg : DirGraphon) (m n : ℕ) (H : BipGraph m n) :
    dg.tIn (orientOf H) = dg.tInBip H := by
  unfold DirGraphon.tIn DirGraphon.tInBip DirGraphon.EX
  rw [← dg.exp_transport (Fin m ⊕ Fin n) (Fin (m + n)) _ _ finSumFinEquiv]
  congr 1
  funext x
  simp only [orientOf, Fin.prod_univ_add, g73t_oe_ll, g73t_oe_lr, g73t_oe_r,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, cond_false,
    Finset.prod_const_one, mul_one, one_mul]
