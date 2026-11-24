-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.Mu.mu_ram_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:34:19.072694+00:00
-- url     : https://prove2.me/submissions/da335cd4-88e8-4876-a8db-5232b904fcff

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_MuCardLeTwo
import Theorems.Thm_Formalism_FrobeniusOrbits_Mu_mu_card_le_two
import Theorems.Thm_Formalism_FrobeniusOrbits_Frob_frob_mul_inertia
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerFrob
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_layerInertiaTame
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_odd_card


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.Mu
variable {L : Type} [Field L] [NumberField L]
variable {e q d : ℕ} {ζ a b : L}
namespace Formalism.FrobeniusOrbits.Mu
theorem _root_.solution (hqd : HypOdd q d) (h : IsLayer (e + 2) q d ζ a b) (p : ℕ)
    [Fact p.Prime] (hp2 : p ≠ 2) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] :
    Q.ramificationIdx ℤ ≤ 2 ∧ (p ≠ q → p ≠ d → Q.ramificationIdx ℤ ≤ 1) := by
  obtain ⟨hGal, -, -, hbij⟩ := Formalism.FrobeniusOrbits.Galois.layer_galois hqd h
  haveI := hGal
  rw [← Formalism.TwoAdicCyclotomicDecomposition.odd_card L p Q]
  have hinjF := hbij.1
  have key : p ≠ q → p ≠ d → Nat.card (Q.inertia Gal(L/ℚ)) ≤ 1 := by
    intro hpq hpd
    obtain ⟨⟨σ, hσ⟩, hiff⟩ :=
      Formalism.TwoAdicCyclotomicDecomposition.layerFrob (e + 2) q d (by omega) hqd L ζ a b h p hp2 hpq hpd Q
    have hρ1 : ∀ ρ ∈ Q.inertia Gal(L/ℚ), ρ = 1 := by
      intro ρ hρ
      have hf := Formalism.FrobeniusOrbits.Frob.frob_mul_inertia Q ρ σ hρ hσ
      have A := (hiff _).1 hf
      have B := (hiff _).1 hσ
      have heq : galMap h.1 a b (ρ * σ) = galMap h.1 a b σ :=
        Prod.ext (Units.ext (A.1.trans B.1.symm))
          (Prod.ext (Units.ext (A.2.1.trans B.2.1.symm)) (Units.ext (A.2.2.trans B.2.2.symm)))
      have h3 := hinjF heq
      first
        | exact mul_eq_right.mp h3
        | exact mul_left_eq_self.mp h3
    have hsub : Subsingleton (Q.inertia Gal(L/ℚ)) := by
      constructor
      rintro ⟨ρ, hρ⟩ ⟨ρ', hρ'⟩
      have e1 := hρ1 ρ hρ
      have e2 := hρ1 ρ' hρ'
      subst e1
      subst e2
      rfl
    first
      | exact Nat.card_le_one_iff_subsingleton.mpr hsub
      | exact Finite.card_le_one_iff_subsingleton.mpr hsub
  have tame := Formalism.TwoAdicCyclotomicDecomposition.layerInertiaTame (e + 2) q d (by omega) hqd L ζ a b h
  have two_of : ∀ t : GalL (e + 2), t ^ 2 = 1 →
      (∀ ρ ∈ Q.inertia Gal(L/ℚ), galMap h.1 a b ρ ∈ Subgroup.zpowers t) →
      Nat.card (Q.inertia Gal(L/ℚ)) ≤ 2 := by
    intro t ht hmem
    refine mu_card_le_two (galMap h.1 a b) hinjF t _ ?_
    intro ρ hρ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hmem ρ hρ)
    have ht' : t ^ (2 : ℤ) = 1 := by
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
      exact ht
    rw [← hk, zpow_eq_zpow_emod k ht']
    rcases Int.emod_two_eq_zero_or_one k with h0 | h0 <;> rw [h0] <;> simp
  refine ⟨?_, fun hpq hpd => key hpq hpd⟩
  by_cases hpq : p = q
  · subst hpq
    exact two_of ((1, -1, 1) : GalL (e + 2)) (by simp [sq])
      (fun ρ hρ => (tame.1 Q ρ).1 hρ)
  · by_cases hpd : p = d
    · subst hpd
      exact two_of ((1, 1, -1) : GalL (e + 2)) (by simp [sq])
        (fun ρ hρ => (tame.2 Q ρ).1 hρ)
    · exact (key hpq hpd).trans (by norm_num)
end Formalism.FrobeniusOrbits.Mu
