-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD.pair_sum_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:09.169187+00:00
-- url     : https://prove2.me/submissions/f45cc591-c1c3-4ae1-b0e1-7e2f7fb4560f

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZDefs
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_CountZPair
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_mulLevel_ne_one
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimitiveCharacterCasts_ZD_mulLevel_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Finset
noncomputable section
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
private lemma sum_range_natCast_zmod_eq_sum_univ {Q : ℕ} [NeZero Q] (f : ZMod Q → ℂ) :
    ∑ n ∈ Finset.range Q, f (n : ZMod Q) = ∑ x : ZMod Q, f x := by
  refine Finset.sum_nbij (fun n : ℕ => (n : ZMod Q)) (fun _ _ => Finset.mem_univ _) ?_ ?_
    (fun _ _ => rfl)
  · intro a ha b hb hab
    have ha' : a < Q := Finset.mem_range.mp ha
    have hb' : b < Q := Finset.mem_range.mp hb
    have h := congrArg ZMod.val hab
    simp only at h
    rwa [ZMod.val_natCast_of_lt ha', ZMod.val_natCast_of_lt hb'] at h
  · intro x _
    exact ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩
private lemma sum_range_modulus_shift_eq_zero_of_ne_one {Q : ℕ} [NeZero Q] (ψ : DirichletCharacter ℂ Q) (hψ : ψ ≠ 1) (M : ℕ) :
    ∑ n ∈ Finset.range Q, ψ ((M + n : ℕ) : ZMod Q) = 0 := by
  calc ∑ n ∈ Finset.range Q, ψ ((M + n : ℕ) : ZMod Q)
        = ∑ n ∈ Finset.range Q, (fun x => ψ ((M : ZMod Q) + x)) (n : ZMod Q) := by
          simp [Nat.cast_add]
    _ = ∑ x : ZMod Q, ψ ((M : ZMod Q) + x) := sum_range_natCast_zmod_eq_sum_univ (fun x => ψ ((M : ZMod Q) + x))
    _ = ∑ x : ZMod Q, ψ x := Equiv.sum_comp (Equiv.addLeft (M : ZMod Q)) ψ
    _ = 0 := MulChar.sum_eq_zero_of_ne_one hψ
private lemma norm_charSum_range_le_modulus_of_ne_one {Q : ℕ} [NeZero Q] (ψ : DirichletCharacter ℂ Q) (hψ : ψ ≠ 1) (M : ℕ) :
    ‖∑ n ∈ Finset.range M, ψ (n : ZMod Q)‖ ≤ (Q : ℝ) := by
  have hQ : 0 < Q := NeZero.pos Q
  refine Nat.strong_induction_on M ?_
  intro M ih
  by_cases hM : M < Q
  · calc ‖∑ n ∈ Finset.range M, ψ (n : ZMod Q)‖
          ≤ ∑ n ∈ Finset.range M, ‖ψ (n : ZMod Q)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range M, (1 : ℝ) :=
          Finset.sum_le_sum fun n _ => DirichletCharacter.norm_le_one ψ _
      _ = M := by simp
      _ ≤ Q := by exact_mod_cast hM.le
  · obtain ⟨K, hK⟩ : ∃ K, M = K + Q := ⟨M - Q, by omega⟩
    subst hK
    rw [Finset.sum_range_add, sum_range_modulus_shift_eq_zero_of_ne_one ψ hψ K, add_zero]
    exact ih K (by omega)
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
end
end

set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
namespace Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
theorem _root_.solution : PairSum := by
  intro p p' hp hp' hne M
  have h := norm_charSum_range_le_modulus_of_ne_one (mulLevel p p') (mulLevel_ne_one p p' hp hp' hne) M
  simpa only [mulLevel_apply] using h
end Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD
