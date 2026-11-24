-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.proj_keeps_letter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:33:23.234409+00:00
-- url     : https://prove2.me/submissions/973b655b-76c9-4cb9-901e-88286af42f2b

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Theorems.Thm_Formalism_MainNotions_PlaneGram_euler_eq_dg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_eq_sum_f
import Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_mem_PolK_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open MvPolynomial Finset
namespace Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}
section Generic
variable {L : Type} [Fintype L] [DecidableEq L] (sg : L → Bool) {r : ℕ} [NeZero r] (d : L → ℕ)
end Generic
section Torus
variable {L : Type} [DecidableEq L] (sg : L → Bool) {r : ℕ}
private theorem coeff_dg_eq_mul_coeff {σ : Type} (f : (σ →₀ ℕ) → K) (F : MvPolynomial σ K)
    (α : σ →₀ ℕ) : (dg f F).coeff α = f α * F.coeff α := by
  classical
  rw [dg_eq_sum_f, MvPolynomial.coeff_sum]
  by_cases h : α ∈ F.support
  · rw [Finset.sum_eq_single α (fun β _ hβ => by rw [MvPolynomial.coeff_monomial, if_neg hβ])
      (fun h' => absurd h h'), MvPolynomial.coeff_monomial, if_pos rfl]
  · have h0 : F.coeff α = 0 := by simpa using h
    rw [h0, mul_zero]
    exact Finset.sum_eq_zero (fun β hβ => by
      rw [MvPolynomial.coeff_monomial, if_neg (fun (e : β = α) => h (e ▸ hβ))])
end Torus
end Formalism.MainNotions.PlaneGram
end
end

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}
variable {L : Type} [DecidableEq L] (sg : L → Bool) {r : ℕ}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (d : L → ℕ)
    (Pr : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K) (i : L)
    (hcomm : ∀ (a : Fin r), ∀ F ∈ PolK K r d,
      Pr (X (i, a) * pderiv (i, a) F) = X (i, a) * pderiv (i, a) (Pr F))
    (ζ : L × Fin r →₀ ℕ) (hζ : ∀ k, ldeg ζ k = d k) (ζ' : L × Fin r →₀ ℕ)
    (hζ' : ζ' ∈ (Pr (monomial ζ 1)).support) (a : Fin r) : ζ' (i, a) = ζ (i, a) := by
  classical
  have hmono : (monomial ζ (1 : K) : MvPolynomial (L × Fin r) K) ∈ PolK K r d := by
    rw [mem_PolK_iff]
    intro α hα k
    have hαζ : α = ζ := by
      by_contra hne
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial, if_neg (Ne.symm hne)] at hα
      exact hα rfl
    rw [hαζ]
    exact hζ k
  have h := hcomm a _ hmono
  rw [euler_eq_dg, euler_eq_dg] at h
  simp only [dg_monomial, mul_one] at h
  have h' := congrArg (fun G => MvPolynomial.coeff ζ' G) h
  simp only [coeff_dg_eq_mul_coeff] at h'
  have hsm : (monomial ζ ((ζ (i, a) : ℕ) : K) : MvPolynomial (L × Fin r) K) =
      ((ζ (i, a) : ℕ) : K) • monomial ζ (1 : K) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hsm, map_smul, MvPolynomial.coeff_smul, smul_eq_mul] at h'
  have hne : (Pr (monomial ζ 1)).coeff ζ' ≠ 0 := by simpa using hζ'
  have hc := mul_right_cancel₀ hne h'
  exact_mod_cast hc.symm
end Formalism.MainNotions.PlaneGram
