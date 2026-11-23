-- Prove2me | solution 1 for Formalism.UG.P.fIwasawa_chi_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:35.625153+00:00
-- url     : https://prove2.me/submissions/9bccb478-8104-4c1a-9f4e-c1be743cb27e

import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawaE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawa
import Theorems.Thm_Formalism_UG_P_fIwasawa_ordL_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.UG Matrix
namespace Formalism.UG.P
section FIwasawaFinal
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable (σ : L →+* L) {n m : ℕ} (q : ℕ) (α : Fin m → ℂ)
private lemma blockTriangular_mul_diag (B C : Matrix (Fin n) (Fin n) L)
    (hB : B.BlockTriangular id) (hC : C.BlockTriangular id) (i : Fin n) :
    (B * C) i i = B i i * C i i := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [hB (show id k < id i from h), zero_mul]
    · rw [hC (show id i < id k from h), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h
private lemma GL_blockTriangular_diag_ne_zero (g : GL (Fin n) L)
    (hg : (g : Matrix (Fin n) (Fin n) L).BlockTriangular id) (i : Fin n) :
    (g : Matrix (Fin n) (Fin n) L) i i ≠ 0 := by
  have hdet : (g : Matrix (Fin n) (Fin n) L).det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det (Units.mul_inv g)
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h1
    exact zero_ne_one h1
  rw [Matrix.det_of_upperTriangular hg] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ _)
end FIwasawaFinal
end Formalism.UG.P
end

set_option autoImplicit false
open Formalism.UG Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
variable (σ : L →+* L) {n m : ℕ} (q : ℕ) (α : Fin m → ℂ)
namespace Formalism.UG.P
theorem _root_.solution (hα : ∀ i, α i ≠ 0) (hq : (q : ℂ) ≠ 0) (b c : GU σ n)
    (hb : ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id)
    (hc : ((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).BlockTriangular id) :
    chiDeltaU q α (b * c) = chiDeltaU q α b * chiDeltaU q α c := by
  have hdb := GL_blockTriangular_diag_ne_zero (b : GL (Fin n) L) hb
  have hdc := GL_blockTriangular_diag_ne_zero (c : GL (Fin n) L) hc
  have hbc : ∀ i : Fin n, (((b * c : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i =
      ((b : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i * ((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i :=
    fun i => blockTriangular_mul_diag _ _ hb hc i
  unfold Formalism.UG.chiDeltaU
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  split_ifs with h
  · rw [hbc ⟨i.val, h⟩, fIwasawa_ordL_mul _ _ (hdb ⟨i.val, h⟩) (hdc ⟨i.val, h⟩)]
    rw [zpow_add₀ (hα i), neg_add, add_mul, zpow_add₀ hq]
    ring
  · rw [mul_one]
end Formalism.UG.P
