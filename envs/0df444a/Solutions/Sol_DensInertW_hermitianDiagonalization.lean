-- Prove2me | solution 1 for DensInertW.hermitianDiagonalization
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:32.211422+00:00
-- url     : https://prove2.me/submissions/f09b0835-bdef-4d95-beb7-5d0f8303a24a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_HermitianDiagonalization
import Theorems.Thm_DensInertW_diag_of_hyps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
open DensInertW
open DensInertW.Sub
namespace DensInertW
theorem _root_.solution : Diag := by
  intro K L _ _ _ _ _ h2 m B hB
  obtain ⟨n, hp, hcard⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hp⟩
  haveI : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have hadd : ∀ a b : L, (a + b) ^ Fintype.card K = a ^ Fintype.card K + b ^ Fintype.card K := fun a b => by
    rw [hcard]
    exact add_pow_char_pow a b _ _
  have hcL : Fintype.card L = Fintype.card K ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := K) (V := L), h2]
  have hinv : ∀ a : L, (a ^ Fintype.card K) ^ Fintype.card K = a := fun a => by
    rw [← pow_mul, ← sq, ← hcL, FiniteField.pow_card]
  have hq2 : 2 ≤ Fintype.card K := Fintype.one_lt_card

  have htr : ∀ z : L, z ≠ 0 → ∃ c : L, c * z + (c * z) ^ Fintype.card K ≠ 0 := by
    intro z hz
    by_contra hall
    push_neg at hall
    let P : Polynomial L := Polynomial.X ^ Fintype.card K + Polynomial.X
    have hroot : ∀ y : L, P.eval y = 0 := fun y => by
      have h := hall (y / z)
      rw [div_mul_cancel₀ y hz] at h
      simp only [P, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X]
      linear_combination h
    have hP0 : P ≠ 0 := by
      intro h0
      have h := congrArg (Polynomial.coeff · 1) h0
      simp only [P, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X_one,
        Polynomial.coeff_zero] at h
      split_ifs at h with hh
      · omega
      · norm_num at h
    have hdeg : P.natDegree ≤ Fintype.card K :=
      (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) (by simp; omega))
    have hsub : (Finset.univ : Finset L).val ≤ P.roots :=
      (Multiset.le_iff_subset Finset.univ.nodup).mpr fun y _ => (Polynomial.mem_roots hP0).mpr (hroot y)
    have hc := (Multiset.card_le_card hsub).trans ((Polynomial.card_roots' P).trans hdeg)
    rw [Finset.card_val, Finset.card_univ, hcL] at hc
    nlinarith
  exact diag_of_hyps B hadd hinv hB htr
end DensInertW
