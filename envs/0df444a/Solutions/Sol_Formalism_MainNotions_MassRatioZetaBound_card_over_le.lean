-- Prove2me | solution 1 for Formalism.MainNotions.MassRatioZetaBound.card_over_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:41:40.795769+00:00
-- url     : https://prove2.me/submissions/18ceded1-d20b-46af-8c16-484cdb2b9bca

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_MassRatioBound
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_absNorm_nat
import Theorems.Thm_Formalism_MainNotions_MassRatioZetaBound_absNorm_ge

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.MassRatioZetaBound
open NumberField
variable {K : Type*} [Field K] [NumberField K]
namespace Formalism.MainNotions.MassRatioZetaBound
theorem _root_.solution {l : ℕ} (hl : l.Prime) (S : Finset (Ideal (𝓞 K))) (hS : ∀ P ∈ S, P.IsMaximal ∧ (l : 𝓞 K) ∈ P) :
    S.card ≤ Module.finrank ℚ K := by
  classical
  have hcop : (S : Set (Ideal (𝓞 K))).Pairwise (fun P Q => IsCoprime P Q) := by
    intro P hPS Q hQS hPQ
    rw [Ideal.isCoprime_iff_sup_eq]
    have hPm := (hS P hPS).1
    have hQm := (hS Q hQS).1
    by_contra h
    have h1 : P ⊔ Q = P := (hPm.eq_of_le h le_sup_left).symm
    have h2 : Q ≤ P := h1 ▸ le_sup_right
    exact hPQ (hQm.eq_of_le hPm.ne_top h2).symm
  have hdvd : ∏ P ∈ S, P ∣ Ideal.span {(l : 𝓞 K)} := by
    refine Finset.prod_dvd_of_coprime hcop fun P hP => ?_
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
    exact (hS P hP).2
  have hN : ∏ P ∈ S, Ideal.absNorm P ∣ l ^ Module.finrank ℚ K := by
    rw [← map_prod, ← absNorm_nat]
    exact map_dvd Ideal.absNorm hdvd
  have hN' : ∏ P ∈ S, Ideal.absNorm P ≤ l ^ Module.finrank ℚ K :=
    Nat.le_of_dvd (pow_pos hl.pos _) hN
  have hge : l ^ S.card ≤ ∏ P ∈ S, Ideal.absNorm P := by
    rw [← Finset.prod_const]
    refine Finset.prod_le_prod' fun P hP => ?_
    have := (hS P hP).1
    exact (absNorm_ge P hl (hS P hP).2).2
  exact (Nat.pow_le_pow_iff_right hl.two_le).1 (hge.trans hN')
end Formalism.MainNotions.MassRatioZetaBound
