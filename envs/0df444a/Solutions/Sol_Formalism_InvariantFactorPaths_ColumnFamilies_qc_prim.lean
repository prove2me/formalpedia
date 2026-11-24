-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_prim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:34.409697+00:00
-- url     : https://prove2.me/submissions/b7e33c7f-4ee3-41fd-aa92-a54e5d4d8c98

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLGenPtInt
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_canT_std

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n] {M : GLMod n} {mu : Fin n → ℤ} {β : M.ι → GLCoord ℤ n}
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hS : SBasis) (hmu : Dominant mu) (hβ : IsSMu M mu β)
    (ph : Matrix M.ι (TIdx mu) ℤ) (hph : ∀ I, ∑ i, ph i I • β i = brk mu I) (m : ℤ)
    (hm : ∀ i, m ∣ ph i (canT mu)) : m ∣ 1 := by
  classical
  have : Fintype {I : TIdx mu // StdT I} := Fintype.ofFinite _
  choose q hq using hm
  have hy : ∑ i, q i • β i ∈ Submodule.span ℤ (Set.range fun I : {I : TIdx mu // StdT I} => brk mu I.1) := by
    rw [(hS n mu hmu).2, ← hβ.2.1]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy
  have hcan : brk mu (canT mu) = m • ∑ i, q i • β i := by
    rw [← hph]
    simp only [zsmul_eq_mul, Finset.mul_sum, hq, Int.cast_mul, mul_assoc]
  let c0 : {I : TIdx mu // StdT I} := ⟨canT mu, qc_canT_std mu⟩
  have h0 : ∑ I : {I : TIdx mu // StdT I}, ((if I = c0 then 1 else 0) - m * r I) • brk mu I.1 = 0 := by
    have h2 : ∀ I : {I : TIdx mu // StdT I}, ((if I = c0 then 1 else 0) - m * r I) • brk mu I.1 =
        (if I = c0 then brk mu I.1 else 0) - (m : GLCoord ℤ n) * (r I • brk mu I.1) := by
      intro I
      split_ifs <;> simp [zsmul_eq_mul, sub_mul, mul_assoc]
    simp only [h2, Finset.sum_sub_distrib, ← Finset.mul_sum, hr, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [sub_eq_zero, ← zsmul_eq_mul]
    exact hcan
  have h1 := Fintype.linearIndependent_iff.1 (hS n mu hmu).1 _ h0 c0
  simp only [if_true] at h1
  exact ⟨r c0, by linarith⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
