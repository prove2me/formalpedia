-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.Th_supp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:30:32.915449+00:00
-- url     : https://prove2.me/submissions/b5da9c85-9737-44f5-bf5d-acc1deb43d72

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Th_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)
variable {ι : Type} [Fintype ι]
variable (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (ζ ζ' : D.EM) (h : ζ' ∈ (D.Th j cc PP (monomial ζ 1)).support) :
    ∃ b, ∃ ξ ∈ (PP b).support, ζ' = eOut (D.outSeg j) ζ + ξ := by
  rw [Th_monomial, MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial_mul'] at h
  split_ifs at h with hle
  · rw [one_mul, MvPolynomial.coeff_sum] at h
    obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    rw [MvPolynomial.coeff_smul, smul_eq_mul] at hb
    refine ⟨b, ζ' - eOut (D.outSeg j) ζ, ?_, ?_⟩
    · rw [MvPolynomial.mem_support_iff]
      exact right_ne_zero_of_mul hb
    · exact (add_tsub_cancel_of_le hle).symm
  · exact absurd rfl h
end Formalism.MainNotions.PlaneGram.TwistData
