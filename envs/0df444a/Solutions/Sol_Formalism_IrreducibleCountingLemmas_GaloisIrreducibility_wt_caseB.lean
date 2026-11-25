-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.wt_caseB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:04:08.075666+00:00
-- url     : https://prove2.me/submissions/07fc3d9a-f2b4-4881-bede-70251a6e8b25

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CrossFactorCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_SquareSetMemExceptionalUnion
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_sqWeight_irreducible
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_mem_e3I
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_mem_e3C
import Theorems.Thm_P2M_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_e3__nonneg_6e96a0337fe1
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wt_e3D_le
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_card_pow_sub_one_pos
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_cross_factor_count
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_irreducible_count_upper_unit
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_monic
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_natDegree
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_sqWeight_mul
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wtOf_biUnion_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (N δ δ' l : ℕ) (hl : l.Prime) (hδ : 1 ≤ δ) (hδ' : 1 ≤ δ')
    (hBB : l ^ (4 * padicValNat l (Fintype.card K ^ δ - 1)) ≤ Fintype.card K ^ δ) :
    wtOf (e3μ K N) (⋃ c'' ∈ e3I K δ', ⋃ c' ∈ e3C K L δ l (monicOf c''),
        e3D K N (monicOf c' * monicOf c'')) ≤
      (Fintype.card K : ℝ) ^ ((δ : ℝ) / 4) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ := by
  have hpos := card_pow_sub_one_pos K δ hδ
  have hpos' := card_pow_sub_one_pos K δ' hδ'
  set G : ℝ := (Fintype.card K : ℝ) with hG
  have hG0 : 0 ≤ G := by positivity
  have hinner : ∀ c'' ∈ e3I K δ', wtOf (e3μ K N) (⋃ c' ∈ e3C K L δ l (monicOf c''),
      e3D K N (monicOf c' * monicOf c'')) ≤ G ^ ((δ : ℝ) / 4) * ((G ^ δ - 1)⁻¹ * (G ^ δ' - 1)⁻¹) := by
    intro c'' hc''
    obtain ⟨hirr'', h0''⟩ := mem_e3I.mp hc''
    calc wtOf (e3μ K N) (⋃ c' ∈ e3C K L δ l (monicOf c''), e3D K N (monicOf c' * monicOf c''))
        ≤ ∑ c' ∈ e3C K L δ l (monicOf c''), wtOf (e3μ K N) (e3D K N (monicOf c' * monicOf c'')) :=
          wtOf_biUnion_le _ (e3μ_nonneg K N) _ _
      _ ≤ ∑ _c' ∈ e3C K L δ l (monicOf c''), ((G ^ δ - 1)⁻¹ * (G ^ δ' - 1)⁻¹) := by
          refine Finset.sum_le_sum (fun c' hc' => ?_)
          have hirr : Irreducible (monicOf c') := ((mem_e3C L).mp hc').1
          refine (wt_e3D_le K N _ ((monicOf_monic c').mul (monicOf_monic c''))).trans_eq ?_
          rw [sqWeight_mul _ _ (monicOf_monic c').ne_zero (monicOf_monic c'').ne_zero,
            sqWeight_irreducible _ hirr (monicOf_monic c'),
            sqWeight_irreducible _ hirr'' (monicOf_monic c''), monicOf_natDegree,
            monicOf_natDegree]
      _ = ((e3C K L δ l (monicOf c'')).card : ℝ) * ((G ^ δ - 1)⁻¹ * (G ^ δ' - 1)⁻¹) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
          (cross_factor_count K L δ l (monicOf c'') hl hδ hirr'' h0'' hBB)
          (mul_nonneg (inv_nonneg.mpr hpos.le) (inv_nonneg.mpr hpos'.le))
  have hI : ((e3I K δ').card : ℝ) ≤ G ^ δ' - 1 := by
    have h1 := irreducible_count_upper_unit K δ' hδ'
    have h2 : (e3I K δ').card ≤ Fintype.card K ^ δ' - 1 := by
      refine le_trans ?_ h1
      exact Nat.le_mul_of_pos_left _ (by omega)
    have h3 : 1 ≤ Fintype.card K ^ δ' := Nat.one_le_pow _ _ Fintype.card_pos
    have h4 : ((e3I K δ').card : ℝ) ≤ ((Fintype.card K ^ δ' - 1 : ℕ) : ℝ) := by exact_mod_cast h2
    rw [Nat.cast_sub h3] at h4
    push_cast at h4
    exact h4
  have hr0 : 0 ≤ G ^ ((δ : ℝ) / 4) := Real.rpow_nonneg hG0 _
  calc wtOf (e3μ K N) (⋃ c'' ∈ e3I K δ', ⋃ c' ∈ e3C K L δ l (monicOf c''),
        e3D K N (monicOf c' * monicOf c''))
      ≤ ∑ c'' ∈ e3I K δ', wtOf (e3μ K N) (⋃ c' ∈ e3C K L δ l (monicOf c''),
        e3D K N (monicOf c' * monicOf c'')) := wtOf_biUnion_le _ (e3μ_nonneg K N) _ _
    _ ≤ ∑ _c'' ∈ e3I K δ', G ^ ((δ : ℝ) / 4) * ((G ^ δ - 1)⁻¹ * (G ^ δ' - 1)⁻¹) :=
        Finset.sum_le_sum hinner
    _ = ((e3I K δ').card : ℝ) * (G ^ ((δ : ℝ) / 4) * ((G ^ δ - 1)⁻¹ * (G ^ δ' - 1)⁻¹)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (G ^ δ' - 1) * (G ^ ((δ : ℝ) / 4) * ((G ^ δ - 1)⁻¹ * (G ^ δ' - 1)⁻¹)) :=
        mul_le_mul_of_nonneg_right hI (mul_nonneg hr0
          (mul_nonneg (inv_nonneg.mpr hpos.le) (inv_nonneg.mpr hpos'.le)))
    _ = G ^ ((δ : ℝ) / 4) * (G ^ δ - 1)⁻¹ := by
        field_simp
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
