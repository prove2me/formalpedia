-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x8.key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:38.336508+00:00
-- url     : https://prove2.me/submissions/2eb7b0b2-399b-4aa4-9ea9-817615b04863

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CentreBlockStructure
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_lead_top
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_solveL
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x8_solveR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x8
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A F : Type} [CommRing A] [CommRing F]
namespace Formalism.FourierDecayAlt.P.S3x8
theorem _root_.solution (φ : A →+* F) (hφ : Function.Injective φ) (I : AddSubgroup F)
    (hI : ∀ a x, x ∈ I → φ a * x ∈ I) :
    ∀ (r : ℕ) (M M' : Matrix (Fin r) (Fin r) A) (L U : Matrix (Fin r) (Fin r) F),
      IsLowUni L → IsUpUni U → L * M'.map φ = M.map φ * U →
      (∀ a b, φ (M' a b - M a b) ∈ I) →
      (∀ (l : ℕ) (hl : l ≤ r), IsUnit (lead M l hl)) →
      (∀ a b, (L - 1) a b ∈ I) ∧ (∀ a b, (U - 1) a b ∈ I) ∧
        ∀ (l : ℕ) (hl : l ≤ r), lead M' l hl = lead M l hl := by
  intro r
  induction r with
  | zero =>
    intro M M' L U _ _ _ _ _
    refine ⟨fun a => a.elim0, fun a => a.elim0, fun l hl => ?_⟩
    obtain rfl : l = 0 := Nat.le_zero.1 hl
    simp [lead]
  | succ r ih =>
    intro M M' L U hL hU hE hd hu
    have E : ∀ a b, ∑ c, L a c * φ (M' c b) = ∑ c, φ (M a c) * U c b := fun a b => by
      have := congrFun (congrFun hE a) b
      simpa [Matrix.mul_apply] using this
    have L0 : ∀ a : Fin r, L a.castSucc (Fin.last r) = 0 := fun a =>
      hL.1 (by simp)
    have U0 : ∀ a : Fin r, U (Fin.last r) a.castSucc = 0 := fun a =>
      hU.1 (by simp)
    have hL' : IsLowUni (L.submatrix Fin.castSucc Fin.castSucc) :=
      ⟨fun i j h => hL.1 (by simpa using h), fun a => hL.2 _⟩
    have hU' : IsUpUni (U.submatrix Fin.castSucc Fin.castSucc) :=
      ⟨fun i j h => hU.1 (by simpa using h), fun a => hU.2 _⟩
    have hE' : L.submatrix Fin.castSucc Fin.castSucc * (M'.submatrix Fin.castSucc Fin.castSucc).map φ =
        (M.submatrix Fin.castSucc Fin.castSucc).map φ * U.submatrix Fin.castSucc Fin.castSucc := by
      ext a b
      have := E a.castSucc b.castSucc
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, L0, U0] at this
      simpa [Matrix.mul_apply] using this
    obtain ⟨iL, iU, il⟩ := ih (M.submatrix Fin.castSucc Fin.castSucc)
      (M'.submatrix Fin.castSucc Fin.castSucc) _ _ hL' hU' hE' (fun a b => hd _ _)
      (fun l hl => hu l (hl.trans (Nat.le_succ r)))
    have hM : IsUnit (M.submatrix Fin.castSucc Fin.castSucc).det := by
      rw [← lead_top]; exact hu r (Nat.le_succ r)
    have hM' : IsUnit (M'.submatrix Fin.castSucc Fin.castSucc).det := by
      rw [← lead_top, il r le_rfl, lead_top]; exact hM

    have cU : ∀ a : Fin r, U a.castSucc (Fin.last r) ∈ I := by
      refine solveL φ I hI _ hM (fun c => U c.castSucc (Fin.last r))
        (fun a => ∑ c, (L.submatrix Fin.castSucc Fin.castSucc - 1) a c * φ (M' c.castSucc (Fin.last r)) +
          φ (M' a.castSucc (Fin.last r) - M a.castSucc (Fin.last r))) ?_ ?_
      · funext a
        have := E a.castSucc (Fin.last r)
        rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, L0, hU.2] at this
        simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.submatrix_apply,
          Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply, ite_mul, one_mul,
          zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_sub]
        linear_combination -this
      · intro a
        refine add_mem (sum_mem fun c _ => ?_) (hd _ _)
        rw [mul_comm]; exact hI _ _ (iL a c)
    have rL : ∀ a : Fin r, L (Fin.last r) a.castSucc ∈ I := by
      refine solveR φ I hI _ hM' (fun c => L (Fin.last r) c.castSucc)
        (fun b => ∑ c, φ (M (Fin.last r) c.castSucc) * (U.submatrix Fin.castSucc Fin.castSucc - 1) c b -
          φ (M' (Fin.last r) b.castSucc - M (Fin.last r) b.castSucc)) ?_ ?_
      · funext b
        have := E (Fin.last r) b.castSucc
        rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, U0, hL.2] at this
        simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Matrix.submatrix_apply,
          Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib, Matrix.one_apply, mul_ite, mul_one,
          mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_sub]
        linear_combination this
      · intro b
        refine sub_mem (sum_mem fun c _ => ?_) (hd _ _)
        exact hI _ _ (iU c b)
    refine ⟨?_, ?_, ?_⟩
    · intro a b
      refine Fin.lastCases ?_ (fun a => ?_) a <;> refine Fin.lastCases ?_ (fun b => ?_) b
      · simp [hL.2]
      · simpa [Matrix.one_apply, (Fin.castSucc_lt_last b).ne'] using rL b
      · simp [L0, Matrix.one_apply, (Fin.castSucc_lt_last a).ne]
      · simpa [Matrix.one_apply] using iL a b
    · intro a b
      refine Fin.lastCases ?_ (fun a => ?_) a <;> refine Fin.lastCases ?_ (fun b => ?_) b
      · simp [hU.2]
      · simp [U0, Matrix.one_apply, (Fin.castSucc_lt_last b).ne']
      · simpa [Matrix.one_apply, (Fin.castSucc_lt_last a).ne] using cU a
      · simpa [Matrix.one_apply] using iU a b
    · intro l hl
      rcases Nat.lt_or_ge l (r + 1) with h | h
      · exact il l (Nat.lt_succ_iff.1 h)
      · obtain rfl : l = r + 1 := le_antisymm hl h
        rw [lead_top, lead_top]
        apply hφ
        have := congrArg Matrix.det hE
        rw [Matrix.det_mul, Matrix.det_mul, isLowUni_det F hL, isUpUni_det F hU, one_mul, mul_one] at this
        simpa [RingHom.map_det, RingHom.mapMatrix_apply] using this
end Formalism.FourierDecayAlt.P.S3x8
