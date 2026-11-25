-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ColDictValCPf.high_existence_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:35:29.955251+00:00
-- url     : https://prove2.me/submissions/81b2f0a9-bc61-425d-9e6d-a9c50514b337

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighExistenceHolds
import Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_bigDiv_support

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ColDictValCPf
open MvPolynomial
namespace Formalism.L2.SG.Pf.ColDictValCPf
theorem _root_.solution : HiEx := by
  intro ι _ _ n M hM hne
  classical
  have key : ∀ e : ℕ, ∀ P ∈ M, P ≠ 0 →
      (∀ m, coeff m P ≠ 0 → Finsupp.weight (fun v : ι × Fin n × Fin n => (v.2.1 : ℕ)) m < e) →
      ∃ Q ∈ M, Q ≠ 0 ∧ ∀ (τ : ι) (a b : Fin n), a < b → ∀ k, 1 ≤ k → bigDiv τ a b k Q = 0 := by
    intro e
    induction e with
    | zero =>
      intro P _ hP0 hb
      obtain ⟨m, hm⟩ := ne_zero_iff.mp hP0
      exact absurd (hb m hm) (Nat.not_lt_zero _)
    | succ e ih =>
      intro P hPM hP0 hb
      by_cases hall : ∀ (τ : ι) (a b : Fin n), a < b → ∀ k, 1 ≤ k → bigDiv τ a b k P = 0
      · exact ⟨P, hPM, hP0, hall⟩
      · push Not at hall
        obtain ⟨τ, a, b, hab, k, hk, hQ⟩ := hall
        refine ih _ (hM τ a b k P hPM) hQ ?_
        intro m' hm'
        obtain ⟨m, hm, heq⟩ := bigDiv_support τ a b hab k P m' hm'
        have h1 := hb m hm
        have hab' : (a : ℕ) < b := hab
        have h2 : 1 ≤ k * ((b : ℕ) - a) :=
          Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
        generalize k * ((b : ℕ) - a) = t at heq h2
        omega
  obtain ⟨P, hPM, hP0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact key (P.support.sup (Finsupp.weight (fun v : ι × Fin n × Fin n => (v.2.1 : ℕ))) + 1) P hPM hP0
    fun m hm => Nat.lt_succ_of_le (Finset.le_sup (mem_support_iff.mpr hm))
end Formalism.L2.SG.Pf.ColDictValCPf
