-- Prove2me | solution 1 for Formalism.ResultantValuation.LaplaceProof.card_compl_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:36:42.084956+00:00
-- url     : https://prove2.me/submissions/cfc8f053-7574-4970-9589-b73ebeace007

import Definitions.Def_Formalism_ResultantValuation_ResultantConjugate
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Laplace
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_natAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_natAdd
section
open Finset Equiv
noncomputable section
namespace Formalism.ResultantValuation
namespace LaplaceProof
variable {a b : ℕ}
private lemma card_filter_le_orderEmbOfFin (J : Finset (Fin (a + b))) (h : J.card = a) (i : Fin a) :
    (J.filter (· ≤ J.orderEmbOfFin h i)).card = (i : ℕ) + 1 := by
  have hm : J.filter (· ≤ J.orderEmbOfFin h i) = (Finset.Iic i).map (J.orderEmbOfFin h).toEmbedding := by
    ext y
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_Iic]
    constructor
    · rintro ⟨hy, hyt⟩
      have hr : y ∈ Set.range (J.orderEmbOfFin h) := by
        rw [Finset.range_orderEmbOfFin]
        exact Finset.mem_coe.mpr hy
      obtain ⟨k, rfl⟩ := hr
      exact ⟨k, (J.orderEmbOfFin h).le_iff_le.mp hyt, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem _ _ _, (J.orderEmbOfFin h).le_iff_le.mpr hk⟩
  rw [hm, Finset.card_map, Fin.card_Iic]
end LaplaceProof
end Formalism.ResultantValuation
end
end

set_option autoImplicit false
open Finset Equiv
noncomputable section
open Formalism Formalism.ResultantValuation
open Formalism.ResultantValuation.LaplaceProof
variable {a b : ℕ}
namespace Formalism.ResultantValuation.LaplaceProof
theorem _root_.solution (J : Finset (Fin (a + b))) (h : J.card = a) (i : Fin a) :
    (Jᶜ.filter (· ≤ J.orderEmbOfFin h i)).card + (i : ℕ) = (J.orderEmbOfFin h i : ℕ) := by
  have h1 := card_filter_le_orderEmbOfFin J h i
  have h2 : (J.filter (· ≤ J.orderEmbOfFin h i)).card + (Jᶜ.filter (· ≤ J.orderEmbOfFin h i)).card
      = (Finset.Iic (J.orderEmbOfFin h i)).card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter disjoint_compl_right),
      ← Finset.filter_union, Finset.union_compl]
    congr 1
    ext y
    simp
  rw [Fin.card_Iic] at h2
  omega
end Formalism.ResultantValuation.LaplaceProof
