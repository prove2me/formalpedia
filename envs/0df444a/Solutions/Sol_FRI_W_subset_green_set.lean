-- Prove2me | solution 1 for FRI_W_subset_green_set
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T09:43:14.890842+00:00
-- url     : https://prove2.me/submissions/ed023188-6cf8-40ec-abb6-17bc6eb0556d

import Definitions.Def_SimpleRbrFri_FoldingSoundness
import Definitions.Def_SimpleRbrFri_QuerySoundness
import Theorems.Thm_FRI_local_check_implies_green
import Theorems.Thm_FRI_W_subset_domain


set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P)
    (i : ℕ) (h : i ≤ P.num_foldings) :
    FRI_W P f_0 T i ⊆ FRI_green_set P f_0 T i := by
  induction i generalizing T with
  | zero =>
    intro x
    simp only [FRI_W, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right,
      forall_exists_index, FRI_BadQuery_Points, Finset.mem_filter, Finset.mem_attach, true_and,
      FRI_green_set]
    exact fun hx hlocal ↦ ⟨hx, FRI_local_check_implies_green P f_0 T x hlocal⟩
  | succ i ih =>
    have h' : i < P.num_foldings := Nat.lt_of_succ_le h
    simp only [FRI_W, h', ↓reduceDIte, FRI_green_set]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    classical
    have hy_green := (Finset.mem_filter.mp (ih T (Nat.le_of_succ_le h) hy)).2
    have hx_green : FRI_is_green P f_0 T (i + 1) (y ^ (P.m ⟨i, h'⟩)) := by
      unfold FRI_is_green at hy_green
      grind
    simp only [FRI_domain, h', ↓reduceDIte, Finset.mem_filter, pow_domain, Finset.mem_image]
    exact ⟨⟨y, FRI_W_subset_domain P f_0 T i hy, rfl⟩, hx_green⟩
