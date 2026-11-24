-- Prove2me | solution 1 for Formalism.HC.Der.Rd.dvd_discr_of_inertia
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:55.277406+00:00
-- url     : https://prove2.me/submissions/db05bf46-8c0d-4101-9324-d4fdc180e710

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdDiff
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdBound
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DvdDiscrOfInertia

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits
open Formalism.HC.Der.Rd
namespace Formalism.HC.Der.Rd
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsGalois ℚ E] {l : ℕ} (hl : l.Prime)
    (h : ∀ (P : Ideal (𝓞 E)) [P.IsPrime] [P.LiesOver (span {(l : ℤ)})],
      ∃ σ : E ≃ₐ[ℚ] E, σ ≠ 1 ∧ ∀ x : 𝓞 E, σ • x - x ∈ P) : (l : ℤ) ∣ discr E := by
  by_contra hn
  have : Fact l.Prime := ⟨hl⟩
  have hl' := Nat.prime_iff_prime_int.mp hl
  have hpr : (span {(l : ℤ)}).IsPrime := (span_singleton_prime hl'.ne_zero).mpr hl'
  obtain ⟨⟨P, h1, h2⟩⟩ : Nonempty ((span {(l : ℤ)}).primesOver (𝓞 E)) := inferInstance
  have hpb : span {(l : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hl'.ne_zero
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hpb P
  have hun := (not_dvd_discr_iff_forall_liesOver E (𝓞 E) hl').mp hn P (h1.isMaximal hP0) h2
  have hcard := card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[ℚ] E) (span {(l : ℤ)}) P
  rw [ramificationIdxIn_eq_ramificationIdx (span {(l : ℤ)}) P (E ≃ₐ[ℚ] E),
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt, Subgroup.card_eq_one] at hcard
  obtain ⟨σ, hσ1, hσ⟩ := h P
  have h3 : σ ∈ P.inertia (E ≃ₐ[ℚ] E) := AddSubgroup.mem_inertia.mpr hσ
  rw [hcard, Subgroup.mem_bot] at h3
  exact hσ1 h3
end Formalism.HC.Der.Rd
