-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crP_coeff_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:46:57.382719+00:00
-- url     : https://prove2.me/submissions/78fd83d3-3ada-4100-ac69-dd43c5f934b9

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Theorems.Thm_Formalism_L2_Pj_Crude_crP_isWeightedHomogeneous_crW
import Theorems.Thm_Formalism_L2_Pj_Crude_crW_weight
import Theorems.Thm_Formalism_L2_Pj_Crude_crDiagExp_dl
import Theorems.Thm_Formalism_L2_Pj_Crude_crDiagExp_off
import Theorems.Thm_Formalism_L2_Pj_Crude_crRho_coeff
import Theorems.Thm_Formalism_L2_Pj_Crude_crRho_supported
import Theorems.Thm_Formalism_L2_Pj_Crude_crRho_P

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPolynomial Formalism.L2.Pj
variable {T : Type} [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ)
variable {r n}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (k : Type) [Field k] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ)
    (hβ : Function.Injective β) (ha : Dom r a) : (crP r n k β a).coeff (diagExp r n β a) = 1 := by
  obtain ⟨E, hE⟩ := crRho_P k β a hβ
  have hEdiag : ∀ ℓ ∈ E.support, ℓ.2.2 = β ⟨ℓ.1, ℓ.2.1⟩ := by
    have h1 := crRho_supported k β (crP r n k β a)
    rw [hE, mem_supported, vars_monomial one_ne_zero] at h1
    intro ℓ hℓ
    exact h1 hℓ
  have hcoeffE : (crP r n k β a).coeff E = 1 := by
    rw [← crRho_coeff k β _ E hEdiag, hE, coeff_monomial, if_pos rfl]
  have hEeq : E = diagExp r n β a := by
    ext ℓ
    obtain ⟨σ, i, b⟩ := ℓ
    by_cases hb : b = β ⟨σ, i⟩
    · subst hb
      have hd : diagExp r n β a (crDl β ⟨σ, i⟩) = a σ i := crDiagExp_dl β a ⟨σ, i⟩
      have hw := crP_isWeightedHomogeneous_crW k β a ha σ i
        (show (crP r n k β a).coeff E ≠ 0 by rw [hcoeffE]; exact one_ne_zero)
      rw [crW_weight] at hw
      change E ⟨σ, i, β ⟨σ, i⟩⟩ = diagExp r n β a (crDl β ⟨σ, i⟩)
      rw [hd, ← hw, Finset.sum_eq_single (β ⟨σ, i⟩)]
      · intro b' _ hb'
        by_contra hne
        exact hb' (hEdiag _ (Finsupp.mem_support_iff.mpr hne))
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [crDiagExp_off]
      · by_contra hne
        exact hb (hEdiag _ (Finsupp.mem_support_iff.mpr hne))
      · intro p hp
        apply hb
        obtain ⟨σ', i'⟩ := p
        obtain ⟨h1, h2⟩ := Sigma.mk.inj hp
        subst h1
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (eq_of_heq h2)
        rfl
  rw [← hEeq]
  exact hcoeffE
end Formalism.L2.Pj.Crude
