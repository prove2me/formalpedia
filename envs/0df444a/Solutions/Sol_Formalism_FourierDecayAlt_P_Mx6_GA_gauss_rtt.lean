-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx6.GA.gauss_rtt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:29.686889+00:00
-- url     : https://prove2.me/submissions/b9e8306a-d015-4d66-94a8-d578d31866a7

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_GA_solve_right
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_GA_solve_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_GA_assoc_var
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_GA_mul_assoc_four_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx6 Formalism.FourierDecayAlt.P.Mx6.GA
variable {B : Type*} [Ring B] [Algebra ℂ B]
namespace Formalism.FourierDecayAlt.P.Mx6.GA
theorem _root_.solution (D : ℂ) (hD0 : D ≠ 0) (hD1 : D ≠ 1) (hD2 : D ≠ -1) (τ τ' d d' l l' m m' : B)
    (c1 : τ' * τ = τ * τ') (c2 : d' * d = d * d') (c3 : d' * τ = τ * d') (c4 : d * τ' = τ' * d)
    (D1 : D • (τ * l' - l' * τ) = -(τ * (l - l'))) (D1s : D • (τ' * l - l * τ') = -(τ' * (l - l')))
    (D2 : D • (d * l' - l' * d) = d * (l - l')) (D2s : D • (d' * l - l * d') = d' * (l - l'))
    (E1 : D • (τ * m' - m' * τ) = (m - m') * τ) (TwistedContraction : D • (τ' * m - m * τ') = (m - m') * τ')
    (E2 : D • (d * m' - m' * d) = -((m - m') * d)) (E2VanishingOtherColumns : D • (d' * m - m * d') = -((m - m') * d'))
    (D3 : D • (l * l' - l' * l) = (l - l') * (l - l')) (E3 : D • (m * m' - m' * m) = -((m - m') * (m - m')))
    (D4 : D • (τ' * m * l' * τ - τ' * l' * m * τ) = d' * τ - τ' * d)
    (D4s : D • (τ * m' * l * τ' - τ * l * m' * τ') = τ * d' - d * τ') :
    ∀ i j k n : Fin 2,
      D • ((!![d + m * τ * l, m * τ; τ * l, τ] : Matrix (Fin 2) (Fin 2) B) i j *
            (!![d' + m' * τ' * l', m' * τ'; τ' * l', τ'] : Matrix (Fin 2) (Fin 2) B) k n -
          (!![d' + m' * τ' * l', m' * τ'; τ' * l', τ'] : Matrix (Fin 2) (Fin 2) B) k n *
            (!![d + m * τ * l, m * τ; τ * l, τ] : Matrix (Fin 2) (Fin 2) B) i j) =
        (!![d + m * τ * l, m * τ; τ * l, τ] : Matrix (Fin 2) (Fin 2) B) k j *
            (!![d' + m' * τ' * l', m' * τ'; τ' * l', τ'] : Matrix (Fin 2) (Fin 2) B) i n -
          (!![d' + m' * τ' * l', m' * τ'; τ' * l', τ'] : Matrix (Fin 2) (Fin 2) B) k j *
            (!![d + m * τ * l, m * τ; τ * l, τ] : Matrix (Fin 2) (Fin 2) B) i n := by
  have hm1 : D - 1 ≠ 0 := sub_ne_zero.mpr hD1
  have hp1 : D + 1 ≠ 0 := by intro h; exact hD2 (by linear_combination h)
  have r1 : l' * τ = τ * l' - D⁻¹ • -(τ * (l - l')) := solve_right hD0 D1
  have r2 : l * τ' = τ' * l - D⁻¹ • -(τ' * (l - l')) := solve_right hD0 D1s
  have r3 : l' * d = d * l' - D⁻¹ • (d * (l - l')) := solve_right hD0 D2
  have r4 : l * d' = d' * l - D⁻¹ • (d' * (l - l')) := solve_right hD0 D2s
  have r5 : τ * m' = m' * τ + D⁻¹ • ((m - m') * τ) := solve_left hD0 E1
  have r6 : τ' * m = m * τ' + D⁻¹ • ((m - m') * τ') := solve_left hD0 TwistedContraction
  have r7 : d * m' = m' * d + D⁻¹ • -((m - m') * d) := solve_left hD0 E2
  have r8 : d' * m = m * d' + D⁻¹ • -((m - m') * d') := solve_left hD0 E2VanishingOtherColumns
  have s1 : τ' * (l' * (m * τ)) = τ' * (m * (l' * τ)) - D⁻¹ • (d' * τ - τ' * d) := by
    have := solve_right hD0 D4
    simpa only [mul_assoc] using this
  have s2 : τ * (l * (m' * τ')) = τ * (m' * (l * τ')) - D⁻¹ • (τ * d' - d * τ') := by
    have := solve_right hD0 D4s
    simpa only [mul_assoc] using this
  have o1 : l' * l = (D - 1)⁻¹ • ((D + 1) • (l * l') - l * l - l' * l') := by
    have h : (D - 1) • (l' * l) = (D + 1) • (l * l') - l * l - l' * l' := by
      have h2 : D • (l * l') - D • (l' * l) = l * l - l * l' - l' * l + l' * l' := by
        rw [← smul_sub, D3]; noncomm_ring
      rw [sub_smul, add_smul, one_smul, one_smul]
      have h3 : D • (l' * l) = D • (l * l') - (l * l - l * l' - l' * l + l' * l') := by rw [← h2]; abel
      rw [h3]; abel
    rw [← h, smul_smul, inv_mul_cancel₀ hm1, one_smul]
  have o2 : m' * m = (D + 1)⁻¹ • ((D - 1) • (m * m') + m * m + m' * m') := by
    have h : (D + 1) • (m' * m) = (D - 1) • (m * m') + m * m + m' * m' := by
      have h2 : D • (m * m') - D • (m' * m) = -(m * m - m * m' - m' * m + m' * m') := by
        rw [← smul_sub, E3]; noncomm_ring
      rw [sub_smul, add_smul, one_smul, one_smul]
      have h3 : D • (m' * m) = D • (m * m') + (m * m - m * m' - m' * m + m' * m') := by
        have : D • (m' * m) = D • (m * m') - (D • (m * m') - D • (m' * m)) := by abel
        rw [this, h2]; abel
      rw [h3]; abel
    rw [← h, smul_smul, inv_mul_cancel₀ hp1, one_smul]
  intro i j k n
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases n <;>
  simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.head_cons, Matrix.head_fin_const,
    mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, smul_add, smul_sub, smul_neg, smul_smul,
    smul_mul_assoc, mul_smul_comm, mul_assoc,
    s1, s2, mul_assoc_four_right s1, mul_assoc_four_right s2,
    r1, r2, r3, r4, r5, r6, r7, r8, assoc_var r1, assoc_var r2, assoc_var r3, assoc_var r4,
    assoc_var r5, assoc_var r6, assoc_var r7, assoc_var r8, o1, o2, assoc_var o1, assoc_var o2,
    c1, c2, c3, c4, assoc_var c1, assoc_var c2, assoc_var c3, assoc_var c4]
  all_goals (match_scalars <;> field_simp <;> ring)
end Formalism.FourierDecayAlt.P.Mx6.GA
