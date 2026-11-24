-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.block_minor_sum_explicit_of_fibre_finite_of_prod_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:47.679998+00:00
-- url     : https://prove2.me/submissions/db2af4cd-229f-4ae8-abb5-0a15b1d0aee7

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_integral_minors_weight_sum_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory NumberField Formalism.HermitianLatticeCounting.ExpansionTerms
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (hf : BlockEndMinorFibreFinite) (hb : CompositionBlockProdBound) (hs : IdealInversePowerSum) : BlockMinorSumExplicit := by
  classical
  intro E _ _ _ r S hS
  set f := Fintype.card (InfinitePlace E) with hfdef
  set B : ℝ := Real.exp (((r : ℝ) + 1) / Real.exp 1) * 16 ^ (f * (r + 1)) with hB
  have hB0 : 0 ≤ B := by positivity
  have key : ∀ c : Composition (r + 1),
      ∑ t ∈ S.preimage (Sigma.mk c) sigma_mk_injective.injOn, (blockMinorWeight (⟨c, t⟩ : Σ c : Composition (r + 1), (Fin c.length → E)))⁻¹ ≤ B := by
    intro c
    have hmemT : ∀ t ∈ S.preimage (Sigma.mk c) sigma_mk_injective.injOn,
        (⟨c, t⟩ : Σ c : Composition (r + 1), (Fin c.length → E)) ∈ S := fun t ht => Finset.mem_preimage.mp ht
    generalize S.preimage (Sigma.mk c) sigma_mk_injective.injOn = T at hmemT ⊢
    have hpt : ∀ t ∈ T, ∀ a : Fin c.length,
        IsIntegral ℤ (IndexedMinorEntry c.blocksFun t a) ∧ IndexedMinorEntry c.blocksFun t a ≠ 0 := by
      intro t ht
      have h := hS _ (hmemT t ht)
      unfold BlockEndMinorsIntegral at h
      exact h
    have h1 := integral_minors_weight_sum_le hf hs E c.length c.blocksFun (fun a => c.one_le_blocksFun a)
      T hpt
    have h0 : ∀ t : Fin c.length → E, blockMinorWeight (⟨c, t⟩ : Σ c : Composition (r + 1), (Fin c.length → E)) =
        ∏ a : Fin c.length, ∏ w : InfinitePlace E, (1 + (w (IndexedMinorEntry c.blocksFun t a)) ^ 2) ^ 2 := fun t => rfl
    simp_rw [h0]
    refine h1.trans ?_
    have h2 : ((∏ a, c.blocksFun a : ℕ) : ℝ) ≤ Real.exp (((r : ℝ) + 1) / Real.exp 1) := by
      have := hb (r + 1) c
      have e : c.blocks.prod = ∏ a, c.blocksFun a := by
        rw [← c.ofFn_blocksFun, List.prod_ofFn]
      rw [e] at this
      push_cast at this ⊢
      exact this
    have h3 : (16 : ℝ) ^ (f * c.length) ≤ 16 ^ (f * (r + 1)) :=
      pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ c.length_le)
    exact mul_le_mul h2 h3 (by positivity) (Real.exp_pos _).le
  have e0 : ∑ γ ∈ S, (blockMinorWeight γ)⁻¹ = ∑ c ∈ S.image Sigma.fst,
      ∑ t ∈ S.preimage (Sigma.mk c) sigma_mk_injective.injOn, (blockMinorWeight (⟨c, t⟩ : Σ c : Composition (r + 1), (Fin c.length → E)))⁻¹ := by
    conv_lhs => rw [← Finset.sigma_image_fst_preimage_mk S]
    rw [Finset.sum_sigma]
  rw [e0]
  refine (Finset.sum_le_sum fun c _ => key c).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hc : ((S.image Sigma.fst).card : ℝ) ≤ 2 ^ r := by
    have h1 : (S.image Sigma.fst).card ≤ Fintype.card (Composition (r + 1)) := Finset.card_le_univ _
    rw [composition_card] at h1
    simp only [Nat.add_sub_cancel] at h1
    exact_mod_cast h1
  calc ((S.image Sigma.fst).card : ℝ) * B ≤ 2 ^ r * B := mul_le_mul_of_nonneg_right hc hB0
    _ = _ := by rw [hB]; ring
end Formalism.HermitianLatticeCounting.P
