-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.Vol.one_add_mem_cong
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:52:44.105795+00:00
-- url     : https://prove2.me/submissions/0de91fe9-a48a-44bd-94a1-b701498acfe8

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementV
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_MeasureUniformizerMatrixSetMulCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.Vol
variable {F : Type} [Field F]
namespace Formalism.DoubleCosetMeasures.P.Vol
theorem _root_.solution (O : Subring F) (ϖ : F) (hϖ : ϖ ∈ O) (hϖ0 : ϖ ≠ 0)
    (hloc : IsLocalAt O ϖ) {a : ℕ} (w : Matrix (Fin a) (Fin a) F) (hw : IsInt O w) :
    ∃ k : GL (Fin a) F, k ∈ congSub O ϖ a ∧
      (k : Matrix (Fin a) (Fin a) F) = 1 + ϖ • w := by
  classical
  let P : O := ⟨ϖ, hϖ⟩
  let W : Matrix (Fin a) (Fin a) O := fun i j => ⟨w i j, hw i j⟩
  let A : Matrix (Fin a) (Fin a) O := 1 + P • W
  have hA : O.subtype.mapMatrix A = 1 + ϖ • w := by
    ext i j
    show (((1 + P • W : Matrix (Fin a) (Fin a) O) i j : O) : F) = (1 + ϖ • w) i j
    rw [Matrix.add_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul,
      smul_eq_mul, Subring.coe_add, Subring.coe_mul]
    by_cases h : i = j <;> simp [Matrix.one_apply, h, P, W]
  have hdet : (1 + ϖ • w).det = ((A.det : O) : F) := by
    rw [← hA, ← RingHom.map_det]
    rfl
  let q := Ideal.Quotient.mk (Ideal.span {P})
  have hqP : q P = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have hqA : q.mapMatrix A = 1 := by
    ext i j
    by_cases h : i = j <;> simp [A, hqP, Matrix.one_apply, h, Matrix.smul_apply, Pi.smul_apply]
  have hq : q A.det = q 1 := by rw [RingHom.map_det, hqA, Matrix.det_one, map_one]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hq)
  have hc' := congrArg Subtype.val hc
  change (c : F) * ϖ = (A.det : F) - 1 at hc'
  have hdF : (1 + ϖ • w).det = 1 + ϖ * c := by
    rw [hdet]
    linear_combination -hc'
  have hdO : (1 + ϖ • w).det ∈ O := by
    rw [hdF]
    exact O.add_mem O.one_mem (O.mul_mem hϖ c.2)
  have hdnot : ∀ o ∈ O, (1 + ϖ • w).det ≠ ϖ * o := by
    intro o ho h
    apply hloc.1
    rw [hdF] at h
    have h1 : ϖ * (o - c) = 1 := by linear_combination -h
    rw [inv_eq_of_mul_eq_one_right h1]
    exact O.sub_mem ho c.2
  have hd0 : (1 + ϖ • w).det ≠ 0 := fun h => hdnot 0 O.zero_mem (by rw [h, mul_zero])
  have hdinv : ((1 + ϖ • w).det)⁻¹ ∈ O := hloc.2 _ hdO hdnot
  have hadj : (1 + ϖ • w).adjugate = O.subtype.mapMatrix A.adjugate := by
    rw [← hA, RingHom.map_adjugate]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (1 + ϖ • w) hd0, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
  · intro i j
    show (1 + ϖ • w) i j ∈ O
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    refine O.add_mem ?_ (O.mul_mem hϖ (hw i j))
    by_cases h : i = j <;> simp [Matrix.one_apply, h, O.one_mem, O.zero_mem]
  · intro i j
    rw [Matrix.coe_units_inv]
    show (1 + ϖ • w)⁻¹ i j ∈ O
    rw [Matrix.inv_def, hadj, Ring.inverse_eq_inv']
    simp only [Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact O.mul_mem hdinv (A.adjugate i j).2
  · intro i j
    show (ϖ⁻¹ • ((1 + ϖ • w) - 1)) i j ∈ O
    rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hϖ0, one_smul]
    exact hw i j
end Formalism.DoubleCosetMeasures.P.Vol
