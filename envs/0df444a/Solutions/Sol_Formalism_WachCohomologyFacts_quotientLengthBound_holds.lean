-- Prove2me | solution 1 for Formalism.WachCohomologyFacts.quotientLengthBound_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:54:13.899613+00:00
-- url     : https://prove2.me/submissions/849e3048-cbf0-4b83-9163-44658710d626

import Definitions.Def_Formalism_FrobeniusContraction_Statement
import Definitions.Def_Formalism_FrobeniusContraction_FrobeniusContractionProofs_LenBound
import Theorems.Thm_Formalism_WachCohomologyFacts_PLenBound_length_le_of_span
import Theorems.Thm_Formalism_WachCohomologyFacts_PLenBound_length_quot_pow_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.WachCohomologyFacts
open PLenBound
namespace Formalism.WachCohomologyFacts
theorem _root_.solution : Formalism.WachCohomologyFacts.LenBound := by
  intro O M _ _ _ ℓ g e Z Bc I s hs hZ hBI hkill
  classical
  have hsZ : ∀ x ∈ s, x ∈ Z := fun x hx => hZ ▸ Submodule.mem_sup_left (Submodule.subset_span hx)
  let v : s → ↥Z ⧸ I.comap Z.subtype := fun x => Submodule.Quotient.mk ⟨x.1, hsZ x.1 x.2⟩
  have hspan : Submodule.span O (Set.range v) = ⊤ := by
    have hle' : Submodule.span O (s : Set M) ⊔ Bc ≤
        ((Submodule.span O (Set.range v)).comap (I.comap Z.subtype).mkQ).map Z.subtype := by
      rw [sup_le_iff, Submodule.span_le]
      constructor
      · intro x hx
        refine ⟨⟨x, hsZ x hx⟩, ?_, rfl⟩
        exact Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩
      · intro b hb
        have hbZ : b ∈ Z := hZ ▸ Submodule.mem_sup_right hb
        refine ⟨⟨b, hbZ⟩, ?_, rfl⟩
        show Submodule.Quotient.mk _ ∈ Submodule.span O (Set.range v)
        rw [(Submodule.Quotient.mk_eq_zero _).2 (show (⟨b, hbZ⟩ : Z) ∈ I.comap Z.subtype from hBI hb)]
        exact Submodule.zero_mem _
    have hle := hZ.symm.le.trans hle'
    rw [eq_top_iff]
    rintro q -
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨t, ht, htz⟩ := hle z.2
    have htz' : t = z := Subtype.ext htz
    rw [← htz']
    exact ht
  have hv : ∀ i, ((ℓ : O) ^ e) • v i = 0 := by
    intro i
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    show ((ℓ : O) ^ e) • (i.1 : M) ∈ I
    have := hkill i.1 (hsZ i.1 i.2)
    rwa [← Nat.cast_smul_eq_nsmul O, Nat.cast_pow] at this
  have h1 := length_le_of_span v ((ℓ : O) ^ e) hspan hv
  have h2 := length_quot_pow_le (ℓ : O) e
  have hcard : (Fintype.card s : ℕ∞) ≤ g := by
    rw [Fintype.card_coe]
    exact_mod_cast hs
  calc Module.length O (↥Z ⧸ I.comap Z.subtype)
      ≤ (Fintype.card s : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O) ^ e}) := h1
    _ ≤ (g : ℕ∞) * ((e : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})) := mul_le_mul' hcard h2
    _ = (g : ℕ∞) * (e : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) := by rw [mul_assoc]
end Formalism.WachCohomologyFacts
