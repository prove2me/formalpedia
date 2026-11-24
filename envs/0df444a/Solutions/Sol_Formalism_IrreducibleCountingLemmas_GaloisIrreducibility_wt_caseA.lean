-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.wt_caseA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:09:58.558054+00:00
-- url     : https://prove2.me/submissions/5f4af6c1-32be-46d7-936e-d3cb7c722b5d

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CrossFactorCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_SquareSetMemExceptionalUnion
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_sqWeight_irreducible
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_mem_e3A
import Theorems.Thm_P2M_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_e3__nonneg_6e96a0337fe1
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wt_e3D_le
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_card_pow_sub_one_pos
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_monic
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_natDegree
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_same_factor_count
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
theorem _root_.solution (N δ l : ℕ) (hl : l.Prime) (hδ : 2 ≤ δ)
    (hBB : l ^ (4 * padicValNat l (Fintype.card K ^ δ - 1)) ≤ Fintype.card K ^ δ) :
    wtOf (e3μ K N) (⋃ c' ∈ e3A K L δ l, e3D K N (monicOf c')) ≤
      (Fintype.card K : ℝ) ^ (3 * (δ : ℝ) / 4) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ := by
  have hpos := card_pow_sub_one_pos K δ (by omega)
  calc wtOf (e3μ K N) (⋃ c' ∈ e3A K L δ l, e3D K N (monicOf c'))
      ≤ ∑ c' ∈ e3A K L δ l, wtOf (e3μ K N) (e3D K N (monicOf c')) :=
        wtOf_biUnion_le _ (e3μ_nonneg K N) _ _
    _ ≤ ∑ _c' ∈ e3A K L δ l, ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ := by
        refine Finset.sum_le_sum (fun c' hc' => ?_)
        have hirr : Irreducible (monicOf c') := ((mem_e3A L).mp hc').1
        refine (wt_e3D_le K N _ (monicOf_monic c')).trans_eq ?_
        rw [sqWeight_irreducible _ hirr (monicOf_monic c'), monicOf_natDegree]
    _ = ((e3A K L δ l).card : ℝ) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (same_factor_count K L δ l hl hδ hBB)
        (inv_nonneg.mpr hpos.le)
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
