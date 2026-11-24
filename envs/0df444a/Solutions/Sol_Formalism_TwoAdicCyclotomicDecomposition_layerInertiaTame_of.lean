-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.layerInertiaTame_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:20:18.790551+00:00
-- url     : https://prove2.me/submissions/3b1c5aa8-85c2-49f8-9e20-0c6fd4725b61

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementField
import Definitions.Def_Formalism_TameInertiaTowers_InvLength
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_NormalOrderTwoCentral
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_cyc_inertia
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_sgn_inertia
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_ram_ne_one
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_inertia_back
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_mem_Iq
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_mem_Id

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Ideal
noncomputable section
open Formalism Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.TwoAdicCyclotomicDecomposition
theorem _root_.solution (hG : LayerGalois) : LayerInertiaTame := by
  intro n q d hn hqd L _ _ ζ a b h
  obtain ⟨hq, hd, hqd', hq2, hd2⟩ := hqd
  obtain ⟨hGal, -, -, hbij⟩ := hG n q d hn ⟨hq, hd, hqd', hq2, hd2⟩ L ζ a b h
  have : IsGalois ℚ L := hGal
  have ha : a ^ 2 = ((-(q : ℤ) : ℤ) : L) := by rw [h.2.1]; push_cast; rfl
  have hb : b ^ 2 = ((-(d : ℤ) : ℤ) : L) := by rw [h.2.2.1]; push_cast; rfl
  have h1 : galMap h.1 a b 1 = 1 := by simp [galMap, sgn]
  refine ⟨fun P _ _ σ => ?_, fun P _ _ σ => ?_⟩
  · have : Fact q.Prime := ⟨hq⟩
    have hfwd : ∀ τ : Gal(L/ℚ), (∀ x : 𝓞 L, τ • x - x ∈ P) →
        galMap h.1 a b τ = 1 ∨ galMap h.1 a b τ = (1, -1, 1) := by
      intro τ hτ
      have c1 := odd_cyc_inertia h.1 q hq hq2 P τ hτ
      have c3 := odd_sgn_inertia q hq hq2 P τ hτ b d hb
        (fun hdv => hqd' ((Nat.prime_dvd_prime_iff_eq hq hd).mp hdv))
      rcases Int.units_eq_one_or (sgn τ a) with c2 | c2
      · left; simp only [galMap, c1, c2, c3]; rfl
      · right; simp only [galMap, c1, c2, c3]
    rw [odd_mem_Iq]
    refine ⟨hfwd σ, fun hσ => ?_⟩
    rcases hσ with hσ | hσ
    · have : σ = 1 := hbij.1 (hσ.trans h1.symm)
      subst this
      intro x
      simp
    · exact odd_inertia_back (galMap h.1 a b) hbij.1 h1 _ q P hfwd
        (odd_ram_ne_one q hq P a ha) σ hσ
  · have : Fact d.Prime := ⟨hd⟩
    have hfwd : ∀ τ : Gal(L/ℚ), (∀ x : 𝓞 L, τ • x - x ∈ P) →
        galMap h.1 a b τ = 1 ∨ galMap h.1 a b τ = (1, 1, -1) := by
      intro τ hτ
      have c1 := odd_cyc_inertia h.1 d hd hd2 P τ hτ
      have c2 := odd_sgn_inertia d hd hd2 P τ hτ a q ha
        (fun hdv => hqd' ((Nat.prime_dvd_prime_iff_eq hd hq).mp hdv).symm)
      rcases Int.units_eq_one_or (sgn τ b) with c3 | c3
      · left; simp only [galMap, c1, c2, c3]; rfl
      · right; simp only [galMap, c1, c2, c3]
    rw [odd_mem_Id]
    refine ⟨hfwd σ, fun hσ => ?_⟩
    rcases hσ with hσ | hσ
    · have : σ = 1 := hbij.1 (hσ.trans h1.symm)
      subst this
      intro x
      simp
    · exact odd_inertia_back (galMap h.1 a b) hbij.1 h1 _ d P hfwd
        (odd_ram_ne_one d hd P b hb) σ hσ
end Formalism.TwoAdicCyclotomicDecomposition
