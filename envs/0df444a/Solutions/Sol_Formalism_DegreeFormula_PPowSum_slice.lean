-- Prove2me | solution 1 for Formalism.DegreeFormula.PPowSum.slice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:17.989964+00:00
-- url     : https://prove2.me/submissions/9a467f07-24c6-417b-a256-16a57d308d3f

import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PermExpInj
import Definitions.Def_Formalism_DegreeFormula_PointDegree_PowSum
import Theorems.Thm_Formalism_DegreeFormula_PPowSum_permExp_apply
import Theorems.Thm_Formalism_DegreeFormula_PPowSum_coeff_Xpow_mul
import Theorems.Thm_Formalism_DegreeFormula_PPowSum_permSign_mulSingle_swap_mul
import Theorems.Thm_Formalism_DegreeFormula_PPowSum_mulSingle_mul_apply
import Theorems.Thm_Formalism_DegreeFormula_PPowSum_rem_eq
import Theorems.Thm_Formalism_DegreeFormula_PPowSum_sum_eq_zero_of_anti

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.DegreeFormula Formalism.DegreeFormula.PPowSum
open Formalism.DegreeFormula
namespace Formalism.DegreeFormula.PPowSum
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ} (τ : ι) (k : ℕ) (hk : 1 ≤ k)
    (P : MvPolynomial (ι × Fin N) ℝ) (j : Fin N) :
    ∑ σ : ι → Equiv.Perm (Fin N), sgnP σ * (X (τ, (σ τ).symm j) ^ k * P).coeff (permExp σ) = 0 := by
  have hjN := j.isLt
  by_cases hjk : (j : ℕ) + k < N
  · have hne : j ≠ (⟨(j : ℕ) + k, hjk⟩ : Fin N) := by
      intro h
      have := congrArg Fin.val h
      simp only at this
      omega
    refine sum_eq_zero_of_anti (Pi.mulSingle τ (Equiv.swap j ⟨(j : ℕ) + k, hjk⟩))
      (fun σ => sgnP σ * (X (τ, (σ τ).symm j) ^ k * P).coeff (permExp σ)) ?_
    intro σ
    have hsymm : ((Pi.mulSingle τ (Equiv.swap j ⟨(j : ℕ) + k, hjk⟩) * σ : ι → Equiv.Perm (Fin N)) τ).symm j =
        (σ τ).symm ⟨(j : ℕ) + k, hjk⟩ := by
      rw [Equiv.symm_apply_eq, Pi.mul_apply, Pi.mulSingle_eq_same, Equiv.Perm.mul_apply,
        Equiv.apply_symm_apply, Equiv.swap_apply_right]
    have hc : permExp (Pi.mulSingle τ (Equiv.swap j ⟨(j : ℕ) + k, hjk⟩) * σ)
        (τ, (σ τ).symm ⟨(j : ℕ) + k, hjk⟩) = permExp σ (τ, (σ τ).symm j) := by
      simp only [permExp_apply, mulSingle_mul_apply, if_true, Equiv.apply_symm_apply,
        Equiv.swap_apply_right]
    rw [hsymm, permSign_mulSingle_swap_mul τ _ _ hne, coeff_Xpow_mul, coeff_Xpow_mul, hc,
      rem_eq σ τ k j _ rfl hne]
    ring
  · refine Finset.sum_eq_zero fun σ _ => ?_
    rw [coeff_Xpow_mul, if_neg, mul_zero]
    simp only [permExp_apply, Equiv.apply_symm_apply]
    omega
end Formalism.DegreeFormula.PPowSum
