-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormFactor.Mv_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:22:15.784836+00:00
-- url     : https://prove2.me/submissions/06eb4644-492f-4550-84f0-b745ad6c208d

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_cm_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_Kg_meas
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_gram_trace
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_slice_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {m P Q : Type} [Fintype m] [DecidableEq m] [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]
  {H : Matrix m m ℂ} {Ep : Matrix m P ℂ} {Em : Matrix m Q ℂ}
attribute [local instance] isAddHaarMeasure_matrix_volume
attribute [local instance] haar_prod2
open scoped Pointwise
namespace Formalism.FourierDecayAlt.P.HermitianFormFactor
theorem _root_.solution : 0 < Mv P Q 1 := by
  have hf : Measurable (fun X : Q → Q → ℂ => ∫⁻ B : Q → P → ℂ, Kf P Q 1 (gramF X, B)) :=
    (Kg_meas 1).lintegral_prod_right'
  unfold Mv
  rw [lintegral_pos_iff_support hf]
  have hopen : IsOpen {X : Q → Q → ℂ | (cm X).det ≠ 0 ∧ (Matrix.trace (gram X)).re < 1} := by
    have o1 : IsOpen {X : Q → Q → ℂ | (cm X).det ≠ 0} :=
      isOpen_ne_fun (Continuous.matrix_det cm_cont) continuous_const
    have o2 : IsOpen {X : Q → Q → ℂ | (Matrix.trace (gram X)).re < 1} :=
      isOpen_lt (Complex.continuous_re.comp (Continuous.matrix_trace
        (Continuous.matrix_mul (Continuous.matrix_conjTranspose cm_cont) cm_cont))) continuous_const
    exact o1.inter o2
  have hne : {X : Q → Q → ℂ | (cm X).det ≠ 0 ∧ (Matrix.trace (gram X)).re < 1}.Nonempty := by
    set c : ℝ := 1 / ((Fintype.card Q : ℝ) + 1) with hc
    have hc0 : 0 < c := by positivity
    refine ⟨fun i j => if i = j then (c : ℂ) else 0, ?_, ?_⟩
    · have : cm (fun i j : Q => if i = j then (c : ℂ) else 0) = (c : ℂ) • (1 : Matrix Q Q ℂ) := by
        ext i j
        show (if j = i then (c : ℂ) else 0) = ((c : ℂ) • (1 : Matrix Q Q ℂ)) i j
        simp [Matrix.one_apply, eq_comm]
      rw [this, Matrix.det_smul, Matrix.det_one, mul_one]
      exact pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hc0.ne')
    · rw [gram_trace]
      have : ∀ i : Q, ∑ j, Complex.normSq (if i = j then (c : ℂ) else 0) = c ^ 2 := by
        intro i
        rw [Finset.sum_eq_single i]
        · simp [Complex.normSq_ofReal, sq]
        · intro j _ hj
          simp [hj.symm]
        · intro h; exact absurd (Finset.mem_univ i) h
      simp_rw [this]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
      have hq : (0 : ℝ) ≤ Fintype.card Q := Nat.cast_nonneg _
      rw [div_pow, one_pow, mul_one_div, div_lt_one (by positivity)]
      nlinarith
  refine lt_of_lt_of_le (hopen.measure_pos volume hne) (measure_mono ?_)
  rintro X ⟨h1, h2⟩
  have hpd : (gram X).PosDef := by
    refine Matrix.PosDef.conjTranspose_mul_self _ ?_
    exact Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h1))
  exact (slice_pos (P := P) (T := gramF X) ⟨hpd, h2.le⟩).ne'
end Formalism.FourierDecayAlt.P.HermitianFormFactor
