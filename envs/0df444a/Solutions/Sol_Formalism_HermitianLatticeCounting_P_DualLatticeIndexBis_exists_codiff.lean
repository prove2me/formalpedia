-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.exists_codiff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:12.338313+00:00
-- url     : https://prove2.me/submissions/a92a679d-9fad-4feb-a98f-24f00bd52436

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
open scoped Pointwise
namespace Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
theorem _root_.solution (E : Type) [Field E] [NumberField E] [StarRing E] :
    ∃ (δ : 𝓞 E) (K : Ideal (𝓞 E)), δ ≠ 0 ∧ K ≠ ⊥ ∧ ∀ z : E,
      (∃ o : 𝓞 E, (o : E) = (δ : E) * z) ↔
        ∀ a ∈ K, ∃ n : ℤ, Algebra.trace ℚ E (star (a : E) * z) = n := by
  let σ : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)
  have hσ : ∀ a : 𝓞 E, ((σ a : 𝓞 E) : E) = star (a : E) := fun a => rfl
  have hσσ : ∀ a : 𝓞 E, σ (σ a) = a := by
    intro a
    apply RingOfIntegers.ext
    rw [hσ, hσ, star_star]
  let Dd : FractionalIdeal (nonZeroDivisors (𝓞 E)) E :=
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
  have hDd0 : Dd ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero
  let δ : 𝓞 E := (Dd.den : 𝓞 E)
  have hδ : δ ≠ 0 := nonZeroDivisors.ne_zero Dd.den.2
  have hδE : (δ : E) ≠ 0 := by
    intro h0
    exact hδ (RingOfIntegers.ext (by simpa using h0))
  have F1 : ∀ a₀ ∈ Dd.num, ∃ w ∈ Dd, (a₀ : E) = (δ : E) * w := by
    intro a₀ ha₀
    have h1 : (a₀ : E) ∈ Submodule.map (Algebra.linearMap (𝓞 E) E) Dd.num := ⟨a₀, ha₀, rfl⟩
    rw [← FractionalIdeal.den_mul_self_eq_num] at h1
    obtain ⟨w, hw, hw'⟩ := h1
    refine ⟨w, hw, ?_⟩
    rw [← hw']
    exact Algebra.smul_def δ w
  have F2 : ∀ w ∈ Dd, ∃ a₀ ∈ Dd.num, (a₀ : E) = (δ : E) * w := by
    intro w hw
    have h1 : Dd.den • w ∈ Dd.den • (Dd : Submodule (𝓞 E) E) :=
      Submodule.smul_mem_pointwise_smul _ _ _ hw
    rw [FractionalIdeal.den_mul_self_eq_num] at h1
    obtain ⟨a₀, ha₀, ha₀'⟩ := h1
    refine ⟨a₀, ha₀, ?_⟩
    have h2 : (a₀ : E) = Dd.den • w := ha₀'
    rw [h2]
    exact Algebra.smul_def δ w
  have hone : (1 : E) ∈ Dd := FractionalIdeal.one_le_dual_one ℤ ℚ (FractionalIdeal.one_mem_one _)
  refine ⟨δ, Ideal.comap σ Dd.num, hδ, ?_, ?_⟩
  · intro hbot
    obtain ⟨a₀, ha₀, ha₀'⟩ := F2 1 hone
    have h1 : σ a₀ ∈ Ideal.comap σ Dd.num := by
      rw [Ideal.mem_comap, hσσ]; exact ha₀
    rw [hbot, Ideal.mem_bot] at h1
    have h2 : a₀ = 0 := by rw [← hσσ a₀, h1, map_zero]
    rw [h2, mul_one] at ha₀'
    exact hδE (by simpa using ha₀'.symm)
  · intro z
    constructor
    · rintro ⟨o, ho⟩ a ha
      obtain ⟨w, hw, hw'⟩ := F1 (σ a) ha
      have h1 := (FractionalIdeal.mem_dual (A := ℤ) (K := ℚ)
        (one_ne_zero : (1 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0)).mp hw (o : E)
        ((FractionalIdeal.mem_one_iff _).mpr ⟨o, rfl⟩)
      obtain ⟨n, hn⟩ := h1
      refine ⟨n, ?_⟩
      rw [← hσ, hw', mul_comm (δ : E) w, mul_assoc, ← ho]
      rw [Algebra.traceForm_apply] at hn
      exact hn.symm
    · intro H
      have h1 : (δ : E) * z ∈ FractionalIdeal.dual ℤ ℚ Dd := by
        rw [FractionalIdeal.mem_dual hDd0]
        intro w hw
        obtain ⟨a₀, ha₀, ha₀'⟩ := F2 w hw
        obtain ⟨n, hn⟩ := H (σ a₀) (by rw [Ideal.mem_comap, hσσ]; exact ha₀)
        refine ⟨n, ?_⟩
        rw [Algebra.traceForm_apply]
        rw [← hσ, hσσ, ha₀'] at hn
        rw [show (δ : E) * z * w = (δ : E) * w * z by ring, hn]
        rfl
      rw [FractionalIdeal.dual_dual, FractionalIdeal.mem_one_iff] at h1
      exact h1
end Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
