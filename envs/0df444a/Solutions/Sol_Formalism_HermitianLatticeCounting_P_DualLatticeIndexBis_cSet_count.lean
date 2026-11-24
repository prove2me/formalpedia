-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.cSet_count
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:11.1091+00:00
-- url     : https://prove2.me/submissions/3f5d4a19-4b4f-40d3-9bf9-2e8b980d794d

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
namespace Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
theorem _root_.solution (E : Type) [Field E] [NumberField E] (D : ℕ)
    (hS : {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D}.Finite) :
    (cSet E D).Finite ∧ (cSet E D).ncard ≤ Nat.card (NumberField.Units.torsion E) *
      {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D}.ncard ^ 2 := by
  classical
  set S := {I : Ideal (𝓞 E) | 1 ≤ Ideal.absNorm I ∧ Ideal.absNorm I ≤ D} with hSdef
  have hSf : Finite S := hS.to_subtype
  have hpair : ∀ c : cSet E D, ∃ p : S × S,
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) (c : E) *
        ((p.2 : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) =
      ((p.1 : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) := by
    rintro ⟨c, hc, aa, aa', h1, h2, h3, h4, h5⟩
    exact ⟨(⟨aa, h1, h2⟩, ⟨aa', h3, h4⟩), h5⟩
  choose pr hpr using hpair
  have hrep : ∀ p : S × S, ∃ c0 : E, ∀ c : cSet E D, pr c = p →
      ∃ u : NumberField.Units.torsion E, (c : E) = (((u : (𝓞 E)ˣ) : 𝓞 E) : E) * c0 := by
    intro p
    by_cases h : ∃ c : cSet E D, pr c = p
    · obtain ⟨c0, hc0⟩ := h
      refine ⟨c0, fun c hc => ?_⟩
      have e1 := hpr c
      have e0 := hpr c0
      rw [hc] at e1
      rw [hc0] at e0
      have hne : ((p.2 : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0 := by
        rw [FractionalIdeal.coeIdeal_ne_zero]
        intro hb
        have := p.2.2.1
        rw [hb, Ideal.absNorm_bot] at this
        omega
      have e2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) (c0 : E) =
          FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) (c : E) :=
        mul_right_cancel₀ hne (e0.trans e1.symm)
      obtain ⟨z, hz⟩ := FractionalIdeal.spanSingleton_eq_spanSingleton.mp e2
      have hz' : (c : E) = ((z : 𝓞 E) : E) * c0 := by
        rw [← hz, Units.smul_def, Algebra.smul_def]
      refine ⟨⟨z, ?_⟩, hz'⟩
      rw [NumberField.Units.mem_torsion]
      intro w
      have h1 := c.2.1 w
      have h0 := c0.2.1 w
      rw [hz', map_mul, h0, mul_one] at h1
      exact h1
    · exact ⟨1, fun c hc => absurd ⟨c, hc⟩ h⟩
  choose rep hrep using hrep
  choose u hu using fun c : cSet E D => hrep (pr c) c rfl
  have hinj : Function.Injective (fun c : cSet E D => (pr c, u c)) := by
    intro c c' h
    simp only [Prod.mk.injEq] at h
    apply Subtype.ext
    rw [hu c, hu c', h.1, h.2]
  have hfin : Finite (cSet E D) := Finite.of_injective _ hinj
  refine ⟨Set.toFinite _, ?_⟩
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  calc Nat.card (cSet E D) ≤ Nat.card ((S × S) × NumberField.Units.torsion E) :=
        Nat.card_le_card_of_injective _ hinj
    _ = _ := by rw [Nat.card_prod, Nat.card_prod]; ring
end Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
