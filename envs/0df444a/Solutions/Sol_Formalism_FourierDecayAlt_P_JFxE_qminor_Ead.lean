-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.qminor_Ead
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:20.753999+00:00
-- url     : https://prove2.me/submissions/9fb308ff-0de2-4130-9f12-5e3603b18c7e

import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DetRowsZero
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_Tm_Ead
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_prod_expand
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_rowsum_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_det_rows_perm
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_det_rows_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxE_sum_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution (E : Fin n → Fin n → A) {P Q : Matrix (Fin n) (Fin n) ℂ} (hQP : Q * P = 1) {t : ℕ}
    (e : Fin t ≃ Fin n) (u : ℂ) :
    qminor (Ead E P Q) e e u = P.det • ∑ β : Fin t → Fin n, (∏ j, Q (e j) (β j)) • qminor E e β u := by
  have step1 : ∀ σ : Equiv.Perm (Fin t),
      (List.ofFn fun k : Fin t => Tm (Ead E P Q) (u - (k : ℂ)) (e (σ k)) (e k)).prod =
        ∑ β : Fin t → Fin n, ∑ α : Fin t → Fin n,
          ((∏ j, P (α j) (e (σ j))) * ∏ j, Q (e j) (β j)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod := by
    intro σ
    calc (List.ofFn fun k : Fin t => Tm (Ead E P Q) (u - (k : ℂ)) (e (σ k)) (e k)).prod
        = (List.ofFn fun j : Fin t => ∑ x : Fin n × Fin n,
            (P x.1 (e (σ j)) * Q (e j) x.2) • Tm E (u - (j : ℂ)) x.1 x.2).prod := by
          simp only [Tm_Ead E hQP, ← Finset.sum_product', Finset.univ_product_univ]
      _ = ∑ φ : Fin t → Fin n × Fin n, (∏ j, (P (φ j).1 (e (σ j)) * Q (e j) (φ j).2)) •
            (List.ofFn fun j => Tm E (u - (j : ℂ)) (φ j).1 (φ j).2).prod :=
          by exact prod_expand (X := Fin n × Fin n) t _ _
      _ = _ := by
          rw [← (Equiv.arrowProdEquivProdArrow (Fin t) (fun _ => Fin n) (fun _ => Fin n)).symm.sum_comp, Fintype.sum_prod_type,
            Finset.sum_comm]
          refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => ?_
          simp [Equiv.arrowProdEquivProdArrow, Finset.prod_mul_distrib]
  have inner : ∀ β α : Fin t → Fin n,
      ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : A) *
        (((∏ j, P (α j) (e (σ j))) * ∏ j, Q (e j) (β j)) •
          (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod) =
      ((Matrix.of fun i j : Fin t => P (α i) (e j)).det * ∏ j, Q (e j) (β j)) •
          (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod := by
    intro β α
    rw [← rowsum_det P e α, Finset.sum_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [show ((Equiv.Perm.sign σ : ℤ) : A) = algebraMap ℂ A ((Equiv.Perm.sign σ : ℤ) : ℂ) by simp,
      ← Algebra.smul_def, smul_smul, mul_assoc]
  calc qminor (Ead E P Q) e e u
      = ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : A) * ∑ β : Fin t → Fin n, ∑ α : Fin t → Fin n,
          ((∏ j, P (α j) (e (σ j))) * ∏ j, Q (e j) (β j)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod := by
        unfold qminor; simp only [step1]
    _ = ∑ β : Fin t → Fin n, ∑ α : Fin t → Fin n, ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : A) *
          (((∏ j, P (α j) (e (σ j))) * ∏ j, Q (e j) (β j)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun β _ => Finset.sum_comm
    _ = ∑ β : Fin t → Fin n, ∑ α : Fin t → Fin n,
          ((Matrix.of fun i j : Fin t => P (α i) (e j)).det * ∏ j, Q (e j) (β j)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod := by
        simp only [inner]
    _ = ∑ β : Fin t → Fin n, ∑ γ : Equiv.Perm (Fin t),
          ((Matrix.of fun i j : Fin t => P (e (γ i)) (e j)).det * ∏ j, Q (e j) (β j)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (e (γ k)) (β k)).prod := by
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [sum_inj e _ (fun α hα => by rw [det_rows_zero P e α hα, zero_mul, zero_smul])]
        rfl
    _ = ∑ β : Fin t → Fin n, P.det • ((∏ j, Q (e j) (β j)) • qminor E e β u) := by
        refine Finset.sum_congr rfl fun β _ => ?_
        unfold qminor
        rw [Finset.smul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [det_rows_perm P e γ,
          show ((Equiv.Perm.sign γ : ℤ) : A) = algebraMap ℂ A ((Equiv.Perm.sign γ : ℤ) : ℂ) by simp,
          ← Algebra.smul_def, smul_smul, smul_smul]
        congr 1
        ring
    _ = _ := by rw [Finset.smul_sum]
end Formalism.FourierDecayAlt.P.JFxE
