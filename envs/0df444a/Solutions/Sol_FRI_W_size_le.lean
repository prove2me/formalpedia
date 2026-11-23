-- Prove2me | solution 1 for FRI_W_size_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:25:40.367218+00:00
-- url     : https://prove2.me/submissions/0ea324c1-f9fc-4963-bec1-916b545c8a6b

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State
import Theorems.Thm_card_block_le_m


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P)
    (i : ℕ) (h : i < P.num_foldings) :
    (FRI_W P f_0 T i).card ≤ P.m ⟨i, h⟩ * (FRI_W P f_0 T (i + 1)).card := by
  have hWi_succ : FRI_W P f_0 T (i + 1) = pow_domain (FRI_W P f_0 T i) (P.m ⟨i, h⟩) :=
    dif_pos h
  have hWi_card : ∀ y ∈ FRI_W P f_0 T (i + 1),
      (Block (FRI_W P f_0 T i) (P.m ⟨i, h⟩) y).card ≤ P.m ⟨i, h⟩ :=
    fun _ _ ↦ card_block_le_m _ _ _ (P.h_m_pos _)
  have hWi_card_sum : (FRI_W P f_0 T i).card =
      ∑ y ∈ FRI_W P f_0 T (i + 1), (Block (FRI_W P f_0 T i) (P.m ⟨i, h⟩) y).card := by
    rw [hWi_succ, ← Finset.card_biUnion]
    · congr with x
      simp only [pow_domain, Finset.mem_biUnion, Finset.mem_image,
        Block, Finset.mem_filter, exists_eq_right_right', iff_and_self]
      exact fun hx ↦ ⟨x, hx, rfl⟩
    · intro x hx y hy hxy
      simp_all [Finset.disjoint_left, Block]
  calc (FRI_W P f_0 T i).card
      = ∑ y ∈ FRI_W P f_0 T (i + 1),
          (Block (FRI_W P f_0 T i) (P.m ⟨i, h⟩) y).card := hWi_card_sum
    _ ≤ ∑ y ∈ FRI_W P f_0 T (i + 1), P.m ⟨i, h⟩ := Finset.sum_le_sum hWi_card
    _ = P.m ⟨i, h⟩ * (FRI_W P f_0 T (i + 1)).card := by
        rw [Finset.sum_const, Nat.nsmul_eq_mul, mul_comm]
