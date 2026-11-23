-- Prove2me | solution 1 for ConcatInf_IterStar_IterOmega
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T04:35:07.372794+00:00
-- url     : https://prove2.me/submissions/14f4e455-8ae2-4b11-a92c-fe1fbc51def4

import Definitions.Def_AutomataTheory_Sequences_Segments
import Definitions.Def_AutomataTheory_Languages_Basic
import Theorems.Thm_subset_IterStar_epsilon
import Theorems.Thm_ConcatInf_self_IterOmega

set_option autoImplicit true
open Function Finset Set Filter Stream'
open scoped Computability
variable {A : Type}
theorem _root_.solution {L : Set (List A)} :
    L∗ * L^ω = L^ω := by
  ext as ; constructor
  · rintro ⟨al0, as1, h_al0, h_as1, rfl⟩
    change al0 ∈ IterStar L at h_al0
    simp only [IterStar, Set.mem_iUnion] at h_al0
    obtain ⟨n, h_al0⟩ := h_al0
    change al0 ∈ IterFin L n at h_al0
    induction' n with n h_ind generalizing al0 as1 <;> simp [IterFin] at h_al0
    · simpa [h_al0, nil_append_stream]
    obtain ⟨al1, al2, h_al1, h_al2, rfl⟩ := h_al0
    have h_as2 : al2 ++ₛ as1 ∈ L^ω := by
      rw [← ConcatInf_self_IterOmega] ; use al2,  as1
    specialize h_ind al1 (al2 ++ₛ as1) h_as2 h_al1
    simpa [append_append_stream]
  · intro h_as ; use [], as
    simp [h_as, nil_append_stream]
    apply subset_IterStar_epsilon ; rfl
