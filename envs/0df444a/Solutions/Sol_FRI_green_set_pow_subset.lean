-- Prove2me | solution 1 for FRI_green_set_pow_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:57:45.921607+00:00
-- url     : https://prove2.me/submissions/2a188eaf-c533-4e26-aec7-b460640809ad

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution {F : Type*} [Field F] [DecidableEq F]
    (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P)
    (i : ℕ) (h : i < P.num_foldings) :
    pow_domain (FRI_green_set P f_0 T i) (P.m ⟨i, h⟩) ⊆ FRI_green_set P f_0 T (i + 1) := by
  rw [pow_domain, Finset.image_subset_iff]
  simp only [FRI_green_set, Finset.mem_filter, and_imp]
  intro x hx hgreen
  have hgreen_succ : FRI_is_green P f_0 T (i + 1) (x ^ (P.m ⟨i, h⟩)) := by
    unfold FRI_is_green at hgreen
    grind
  exact ⟨(FRI_domain_succ_eq P i h).symm ▸ Finset.mem_image_of_mem _ hx, hgreen_succ⟩
