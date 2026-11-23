-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x6.exists_multiplier
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:45.966465+00:00
-- url     : https://prove2.me/submissions/15d4e549-47a6-4c32-9408-c134047e728b

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LocalisationTypedIndependentExponent
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x6_mem_ann
import Theorems.Thm_Formalism_FourierDecayAlt_P_S6x6_ann_ne_bot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x6
open NumberField NumberField.IsCMField Module Formalism.FourierDecayAlt.S6
open scoped nonZeroDivisors
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {E}
namespace Formalism.FourierDecayAlt.P.S6x6
theorem _root_.solution {L : Submodule ℤ E} (hL : IsFLattice E L)
    (P : Ideal (𝓞 (maximalRealSubfield E))) (hP : P.IsMaximal) (τ : E) :
    ∃ e : 𝓞 (maximalRealSubfield E),
      algebraMap (𝓞 (maximalRealSubfield E)) E e * τ - τ ∈ locAt E P L ∧
      ∀ Q : Ideal (𝓞 (maximalRealSubfield E)), Q.IsMaximal → Q ≠ P →
        algebraMap (𝓞 (maximalRealSubfield E)) E e * τ ∈ locAt E Q L := by
  have hfin : FiniteMultiplicity P (ann hL τ) :=
    FiniteMultiplicity.of_not_isUnit (fun h => hP.ne_top (Ideal.isUnit_iff.mp h)) (ann_ne_bot hL τ)
  obtain ⟨J, hJ, hPJ⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  generalize multiplicity P (ann hL τ) = k at hJ
  rw [Ideal.dvd_iff_le] at hPJ
  obtain ⟨b, hbJ, hbP⟩ := SetLike.not_le_iff_exists.mp hPJ
  have hcop : IsCoprime P J := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    have h1 : P = P ⊔ J := hP.eq_of_le h le_sup_left
    exact hPJ (h1 ▸ le_sup_right)
  obtain ⟨u, hu, e, he, hue⟩ := Ideal.isCoprime_iff_exists.mp (hcop.pow_left (m := k))
  refine ⟨e, ⟨b, hbP, ?_⟩, ?_⟩
  · have h1 : u * b ∈ ann hL τ := hJ ▸ Ideal.mul_mem_mul hu hbJ
    rw [mem_ann] at h1
    have h2 : algebraMap (𝓞 (maximalRealSubfield E)) E b *
        (algebraMap (𝓞 (maximalRealSubfield E)) E e * τ - τ) =
        -(algebraMap (𝓞 (maximalRealSubfield E)) E (u * b) * τ) := by
      have h3 : algebraMap (𝓞 (maximalRealSubfield E)) E u +
          algebraMap (𝓞 (maximalRealSubfield E)) E e = 1 := by
        rw [← map_add, hue, map_one]
      rw [map_mul]
      linear_combination (algebraMap (𝓞 (maximalRealSubfield E)) E b * τ) * h3
    rw [h2]; exact L.neg_mem h1
  · intro Q hQ hQP
    have hnle : ¬ P ≤ Q := fun h => hQP (hP.eq_of_le hQ.ne_top h).symm
    obtain ⟨c, hcP, hcQ⟩ := SetLike.not_le_iff_exists.mp hnle
    refine ⟨c ^ k, fun h => hcQ (hQ.isPrime.mem_of_pow_mem _ h), ?_⟩
    have h1 : c ^ k * e ∈ ann hL τ := hJ ▸ Ideal.mul_mem_mul (Ideal.pow_mem_pow hcP k) he
    rw [mem_ann, map_mul, mul_assoc] at h1
    exact h1
end Formalism.FourierDecayAlt.P.S6x6
