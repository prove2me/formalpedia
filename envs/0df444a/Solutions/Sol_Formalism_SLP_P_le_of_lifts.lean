-- Prove2me | solution 1 for Formalism.SLP.P.le_of_lifts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:37:25.488583+00:00
-- url     : https://prove2.me/submissions/6446be5b-a688-4f36-b053-2a66288d2e4d

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SubgroupCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SLP Formalism.SLP.P
open AddSubgroup
namespace Formalism.SLP.P
theorem _root_.solution {A : Type*} [AddCommGroup A] {H₁ H₂ : AddSubgroup (ℤ × A)} {ι : Type*}
    (v : ι → A) (hv : AddSubgroup.closure (Set.range v) = H₁.map (AddMonoidHom.snd ℤ A))
    (hk : H₁.comap (AddMonoidHom.inl ℤ A) ≤ H₂.comap (AddMonoidHom.inl ℤ A))
    (hlift : ∀ i, ∃ x : ℤ, (x, v i) ∈ H₁ ⊓ H₂) : H₁ ≤ H₂ := by
  intro h hh
  have hle : H₁.map (AddMonoidHom.snd ℤ A) ≤ (H₁ ⊓ H₂).map (AddMonoidHom.snd ℤ A) := by
    rw [← hv, closure_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨x, hx⟩ := hlift i
    exact ⟨(x, v i), hx, rfl⟩
  obtain ⟨t, ht, hts⟩ := hle ⟨h, hh, rfl⟩
  have hts' : t.2 = h.2 := hts
  have h1 : (h.1 - t.1, (0 : A)) ∈ H₁ := by
    have hm : h - t ∈ H₁ := H₁.sub_mem hh ht.1
    have he : h - t = (h.1 - t.1, (0 : A)) := by
      ext
      · rfl
      · simp [hts']
    rwa [he] at hm
  have h2 : (h.1 - t.1, (0 : A)) ∈ H₂ := hk h1
  have he : h = (h.1 - t.1, (0 : A)) + t := by
    ext
    · simp
    · simp [hts']
  rw [he]
  exact H₂.add_mem h2 ht.2
end Formalism.SLP.P
