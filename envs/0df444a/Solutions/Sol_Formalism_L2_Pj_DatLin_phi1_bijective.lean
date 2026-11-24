-- Prove2me | solution 1 for Formalism.L2.Pj.DatLin.phi1_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:35:27.451521+00:00
-- url     : https://prove2.me/submissions/dff78153-1dfb-4ee4-bac1-820e1e41219e

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaH_Imports
import Definitions.Def_Lemmata_GeneralBFactThirdVariant_Imports
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatTheta
import Theorems.Thm_Formalism_L2_Pj_DatLin_phi1_tmul
import Theorems.Thm_Formalism_L2_Pj_DatLin_li1
import Theorems.Thm_Formalism_L2_Pj_DatLin_two_card

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open NumberField TensorProduct
open scoped nonZeroDivisors ComplexConjugate
variable {E : Type} [Field E] [NumberField E]
variable (Ψ : Finset (E →+* ℂ))
variable {Ψ}
namespace Formalism.L2.Pj.DatLin
theorem _root_.solution (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ) :
    Function.Bijective (phi1 Ψ) := by
  classical
  have hinj : Function.Injective (phi1 Ψ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    let B := Algebra.TensorProduct.basis ℝ (RingOfIntegers.basis E)
    have hx := li1 hΨ (fun k => B.repr t k) (fun τ hτ => by
      have h1 := congrFun ht ⟨τ, hτ⟩
      rw [← B.sum_repr t, map_sum] at h1
      simpa [B, Algebra.TensorProduct.basis_apply, phi1_tmul, Finset.sum_apply, Complex.real_smul]
        using h1)
    have : B.repr t = 0 := by
      ext k
      exact congrFun hx k
    simpa using B.repr.injective (this.trans (map_zero _).symm)
  refine ⟨hinj, ?_⟩
  rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
  rw [Module.finrank_baseChange, RingOfIntegers.rank, Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Fintype.card_coe]
  rw [← two_card hΨ]
  ring
end Formalism.L2.Pj.DatLin
