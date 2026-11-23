-- Prove2me | solution 1 for FRI_W_subset_domain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T08:57:07.99969+00:00
-- url     : https://prove2.me/submissions/622bd08e-5cad-4865-8fa0-9aeb9cdc36d4

import Definitions.Def_SimpleRbrFri_Core
import Definitions.Def_SimpleRbrFri_State

set_option autoImplicit true
variable {F : Type*} [Field F] [DecidableEq F]
theorem _root_.solution (P : FRIParameters F) (f_0 : P.D_0 → F) (T : FRITranscript P) (i : ℕ) :
    FRI_W P f_0 T i ⊆ FRI_domain P i := by
  induction i using Nat.strong_induction_on with | _ i ih => ?_
  rcases i with (_ | i)
  · intro x hx
    simp only [FRI_W, Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right] at hx
    exact hx.1
  · by_cases h : i < P.num_foldings <;> simp_all only [FRI_W, ↓reduceDIte, not_lt]
    · exact FRI_domain_succ_eq P i h ▸ Finset.image_subset_image (ih i (Nat.lt_succ_self i))
    · grind
