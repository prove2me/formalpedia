-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qr_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:44:36.333151+00:00
-- url     : https://prove2.me/submissions/1244b384-fdc5-4b11-b3e0-699934f5869d

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_KStableHighestWeightVector
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StripDataTensorColumnFamilies
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_ClosureBranching

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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {n : ℕ} [NeZero n] {M : GLMod n} {mu : Fin n → ℤ} {β : M.ι → GLCoord ℤ n}
    (hS : SBasis) (hmu : Dominant mu) (hβ : IsSMu M mu β)
    (ph : Matrix M.ι (TIdx mu) ℤ) (hph : ∀ I, ∑ i, ph i I • β i = brk mu I) (I0 : TIdx mu) (hI0 : StdT I0) (d : ℤ)
    (hd : ∀ i, d ∣ ph i I0) : d ∣ 1 := by
  classical
  have : Fintype {I : TIdx mu // StdT I} := Fintype.ofFinite _
  choose q hq using hd
  have hy : ∑ i, q i • β i ∈ Submodule.span ℤ (Set.range fun I : {I : TIdx mu // StdT I} => brk mu I.1) := by
    rw [(hS n mu hmu).2, ← hβ.2.1]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hy
  have hcan : brk mu I0 = d • ∑ i, q i • β i := by
    rw [← hph]
    simp only [zsmul_eq_mul, Finset.mul_sum, hq, Int.cast_mul, mul_assoc]
  let c0 : {I : TIdx mu // StdT I} := ⟨I0, hI0⟩
  have h0 : ∑ I : {I : TIdx mu // StdT I}, ((if I = c0 then 1 else 0) - d * r I) • brk mu I.1 = 0 := by
    have h2 : ∀ I : {I : TIdx mu // StdT I}, ((if I = c0 then 1 else 0) - d * r I) • brk mu I.1 =
        (if I = c0 then brk mu I.1 else 0) - (d : GLCoord ℤ n) * (r I • brk mu I.1) := by
      intro I
      split_ifs <;> simp [zsmul_eq_mul, sub_mul, mul_assoc]
    simp only [h2, Finset.sum_sub_distrib, ← Finset.mul_sum, hr, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [sub_eq_zero, ← zsmul_eq_mul]
    exact hcan
  have h1 := Fintype.linearIndependent_iff.1 (hS n mu hmu).1 _ h0 c0
  simp only [if_true] at h1
  exact ⟨r c0, by linarith⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
