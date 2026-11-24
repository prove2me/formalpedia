-- Prove2me | solution 1 for Formalism.MainNotions.G.SymmetricFormBlocks.decode_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:00:08.519805+00:00
-- url     : https://prove2.me/submissions/9b348c11-9af1-4f9a-90d0-4c5c5a7bda39

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialFactorials_LiRenameMon
import Theorems.Thm_Formalism_GM_M_SSD_kap_gen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.SymmetricFormBlocks
open MvPolynomial Finset Formalism.GM.M.SSD
variable {σ τ K : Type} [Field K] [DecidableEq σ] (e : τ → σ) (he : Function.Injective e)
namespace Formalism.MainNotions.G.SymmetricFormBlocks
theorem _root_.solution (M : Finset (σ →₀ ℕ)) (hM : ∀ β ∈ M, ∀ x, β (e x) = 0) (y : MvPolynomial τ K) (β : M) :
    decode e he M (rename e y * monomial (β : σ →₀ ℕ) 1) = Pi.single β y := by
  funext γ
  have h1 : rename e y * monomial (β : σ →₀ ℕ) (1 : K) = monomial 0 1 * rename e y * monomial (β : σ →₀ ℕ) 1 := by
    rw [← MvPolynomial.C_apply, MvPolynomial.C_1, one_mul]
  have hg : ∀ w ∈ (monomial (β : σ →₀ ℕ) (1 : K)).support, ∀ x, w (e x) = 0 := by
    intro w hw x
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial] at hw
    split_ifs at hw with h
    · rw [← h]
      exact hM _ β.2 x
    · exact absurd rfl hw
  show kap _ (F_inj e he 0 (γ : σ →₀ ℕ)) (rename e y * monomial (β : σ →₀ ℕ) 1) = (Pi.single β y : M → MvPolynomial τ K) γ
  rw [h1, kap_gen e he 0 (γ : σ →₀ ℕ) (hM _ γ.2) y _ hg, MvPolynomial.coeff_monomial, Pi.single_apply]
  by_cases h : γ = β
  · subst h
    simp
  · rw [if_neg h, if_neg (fun h' => h (Subtype.ext h'.symm))]
    exact zero_smul K y
end Formalism.MainNotions.G.SymmetricFormBlocks
