-- Prove2me | solution 1 for Formalism.NG.IdempotentNormalFormsLenFacts.length_ker_of_det_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:09:42.301142+00:00
-- url     : https://prove2.me/submissions/a196d015-7aa5-4615-8296-3682b3af30e6

import Definitions.Def_Formalism_CharacterColumnKernels_Statement
import Definitions.Def_Lemmata_SecondBlockLemmaA_Imports
import Definitions.Def_Lemmata_AddValuationProducts_AddValProd
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_LengthKerOfDetEqZero
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_length_quot_span
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_mk_eq_zero_iff
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_matQ_mk
import Theorems.Thm_Formalism_NG_IdempotentNormalFormsLenFacts_map_mulVec_fun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDiscreteValuationRing Matrix
noncomputable section
open Formalism Formalism.NG
open Formalism.NG.IdempotentNormalFormsLenFacts
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace Formalism.NG.IdempotentNormalFormsLenFacts
theorem _root_.solution (A : Matrix ι ι O) (hd : A.det = 0) :
    Module.length O (LinearMap.ker (matQ O A)) = ⊤ := by
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw0
  obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ (fun i => addVal O (w i))
    ⟨j, Finset.mem_univ _⟩
  have hwi0 : w i0 ≠ 0 := by
    intro h
    have := hi0 j (Finset.mem_univ _)
    rw [h, addVal_zero, top_le_iff, addVal_eq_top_iff] at this
    exact hj this
  choose w' hw' using fun i => (addVal_le_iff_dvd (a := w i0) (b := w i)).mp
    (hi0 i (Finset.mem_univ _))
  have hw'i0 : w' i0 = 1 := by
    have := hw' i0
    exact (mul_left_cancel₀ hwi0 (this.symm.trans (mul_one _).symm))
  have hAw' : A *ᵥ w' = 0 := by
    have : w = w i0 • w' := funext fun i => by simp [hw' i]
    rw [this, Matrix.mulVec_smul] at hw
    exact (smul_eq_zero.mp hw).resolve_left hwi0
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible O
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  rw [ENat.eq_top_iff_forall_ge]
  intro k
  let c : FractionRing O := (algebraMap O (FractionRing O) (ϖ ^ k))⁻¹
  have hc : algebraMap O (FractionRing O) (ϖ ^ k) ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap O (FractionRing O))]
    exact fun h => pow_ne_zero k hϖ0 (IsFractionRing.injective O (FractionRing O) h)
  have hc1 : algebraMap O (FractionRing O) (ϖ ^ k) * c = 1 := mul_inv_cancel₀ hc
  let v : ι → KO O := fun i => Submodule.Quotient.mk (c * algebraMap O (FractionRing O) (w' i))
  have hv : v ∈ LinearMap.ker (matQ O A) := by
    rw [LinearMap.mem_ker]
    have : (fun i => c * algebraMap O (FractionRing O) (w' i)) =
        c • (fun i => algebraMap O (FractionRing O) (w' i)) := by
      ext i; simp
    show matQ O A (fun i => (Submodule.Quotient.mk (c * algebraMap O (FractionRing O) (w' i)) : KO O)) = 0
    rw [matQ_mk, this, Matrix.mulVec_smul, ← map_mulVec_fun, hAw']
    ext i
    exact (mk_eq_zero_iff _).mpr ⟨0, by simp⟩
  let χ : O →ₗ[O] (ι → KO O) := LinearMap.toSpanSingleton O _ v
  have hker : LinearMap.ker χ = Ideal.span ({ϖ ^ k} : Set O) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply, Ideal.mem_span_singleton]
    constructor
    · intro h
      have h0 := congrFun h i0
      simp only [v, Pi.smul_apply, Pi.zero_apply, hw'i0, map_one, mul_one,
        ← Submodule.Quotient.mk_smul] at h0
      obtain ⟨z, hz⟩ := (mk_eq_zero_iff _).mp h0
      refine ⟨z, ?_⟩
      apply IsFractionRing.injective O (FractionRing O)
      rw [Algebra.smul_def] at hz
      rw [map_mul, hz, mul_left_comm, hc1, mul_one]
    · rintro ⟨z, rfl⟩
      ext i
      simp only [v, Pi.smul_apply, Pi.zero_apply, ← Submodule.Quotient.mk_smul]
      refine (mk_eq_zero_iff _).mpr ⟨z * w' i, ?_⟩
      rw [Algebra.smul_def, map_mul, map_mul,
        show algebraMap O (FractionRing O) (ϖ ^ k) * algebraMap O (FractionRing O) z *
          (c * algebraMap O (FractionRing O) (w' i)) =
          (algebraMap O (FractionRing O) (ϖ ^ k) * c) *
          (algebraMap O (FractionRing O) z * algebraMap O (FractionRing O) (w' i)) by ring,
        hc1, one_mul]
  have hrange : LinearMap.range χ ≤ LinearMap.ker (matQ O A) := by
    rintro _ ⟨x, rfl⟩
    exact Submodule.smul_mem _ x hv
  have hle := Module.length_le_of_injective (Submodule.inclusion hrange)
    (Submodule.inclusion_injective hrange)
  rw [← (LinearMap.quotKerEquivRange χ).length_eq,
    (Submodule.quotEquivOfEq _ _ hker).length_eq, length_quot_span, hϖ.addVal_pow] at hle
  simpa using hle
end Formalism.NG.IdempotentNormalFormsLenFacts
