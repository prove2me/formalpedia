-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.prodDeltaLossBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:59:31.965047+00:00
-- url     : https://prove2.me/submissions/cb5e8243-fd20-4a98-b66e-ad65dffd71e8

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_prodMaxInvLeSq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_prod_prod_max_le_pow_mul_thresholdSize
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
private theorem one_le_finset_prod_of_forall_one_le {ι : Type*} (s : Finset ι) (y : ι → ℝ) (h : ∀ v ∈ s, 1 ≤ y v) :
    1 ≤ ∏ v ∈ s, y v := by
  calc (1:ℝ) = ∏ v ∈ s, (1:ℝ) := by simp
    _ ≤ ∏ v ∈ s, y v := Finset.prod_le_prod (fun _ _ => zero_le_one) h
private theorem finset_prod_real_mono_of_subset_of_one_le {ι : Type*} (s t : Finset ι) (hst : s ⊆ t) (y : ι → ℝ)
    (h : ∀ v ∈ t, 1 ≤ y v) : ∏ v ∈ s, y v ≤ ∏ v ∈ t, y v := by
  classical
  rw [← Finset.prod_sdiff hst]
  have h1 : 1 ≤ ∏ v ∈ t \ s, y v :=
    one_le_finset_prod_of_forall_one_le _ _ (fun v hv => h v (Finset.mem_sdiff.mp hv).1)
  have h2 : 0 ≤ ∏ v ∈ s, y v :=
    Finset.prod_nonneg (fun v hv => zero_le_one.trans (h v (hst hv)))
  exact le_mul_of_one_le_left h2 h1
private theorem finset_prod_max_one_nonneg {ι : Type*} (s : Finset ι) (y : ι → ℝ) :
    0 ≤ ∏ v ∈ s, max 1 (y v) :=
  Finset.prod_nonneg (fun _ _ => zero_le_one.trans (le_max_left _ _))
end Formalism.HermitianLatticeCounting.P
end

set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : LossPrimeProd := by
  classical
  intro ι l _ E D De H₁ H₂ e Sg hH₁ hH₂ hD hDprod hDe0 hDe
  have hH₁0 : 0 ≤ H₁ := by linarith
  have hDv : ∀ v, De v ≤ ∏ i ∈ E, max 1 (1 / D i v) := by
    intro v
    rcases hDe v with h | ⟨i, hi, h⟩
    · exact h.trans (one_le_finset_prod_of_forall_one_le _ _ (fun i _ => le_max_left _ _))
    · rw [← Finset.mul_prod_erase E _ hi]
      calc De v ≤ max 1 (1 / D i v) := h.trans (le_max_right _ _)
        _ ≤ max 1 (1 / D i v) * ∏ j ∈ E.erase i, max 1 (1 / D j v) :=
            le_mul_of_one_le_right (zero_le_one.trans (le_max_left _ _))
              (one_le_finset_prod_of_forall_one_le _ _ (fun j _ => le_max_left _ _))
  have hinv : ∏ v, ∏ i ∈ E, max 1 (1 / D i v) ≤
      H₂ ^ (Fintype.card ι * E.card) * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂ := by
    rw [Finset.prod_comm]
    calc ∏ i ∈ E, ∏ v, max 1 (1 / D i v) ≤ ∏ i ∈ E, ∏ v, max 1 (D i v) :=
          Finset.prod_le_prod (fun i _ => finset_prod_max_one_nonneg _ _)
            (fun i hi => (prodMaxInvLeSq ι (D i) Finset.univ (hD i hi) (hDprod i hi)).2)
      _ ≤ _ := prod_prod_max_le_pow_mul_thresholdSize E D H₂ hH₂ hD
  rw [Finset.prod_pow]
  apply pow_le_pow_left₀ (Finset.prod_nonneg (fun v _ => mul_nonneg hH₁0 (hDe0 v)))
  calc ∏ v ∈ Sg, H₁ * De v ≤ ∏ v ∈ Sg, (H₁ * ∏ i ∈ E, max 1 (1 / D i v)) :=
        Finset.prod_le_prod (fun v _ => mul_nonneg hH₁0 (hDe0 v))
          (fun v _ => mul_le_mul_of_nonneg_left (hDv v) hH₁0)
    _ = (∏ _v ∈ Sg, H₁) * ∏ v ∈ Sg, ∏ i ∈ E, max 1 (1 / D i v) := Finset.prod_mul_distrib
    _ ≤ H₁ ^ Fintype.card ι * ∏ v, ∏ i ∈ E, max 1 (1 / D i v) := by
        apply mul_le_mul _ (finset_prod_real_mono_of_subset_of_one_le _ _ (Finset.subset_univ _) _
          (fun v _ => one_le_finset_prod_of_forall_one_le _ _ (fun i _ => le_max_left _ _)))
          (Finset.prod_nonneg (fun v _ => finset_prod_max_one_nonneg _ _)) (pow_nonneg hH₁0 _)
        rw [Finset.prod_const]
        exact pow_le_pow_right₀ hH₁ (Finset.card_le_univ Sg)
    _ ≤ H₁ ^ Fintype.card ι * (H₂ ^ (Fintype.card ι * E.card) * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂) :=
        mul_le_mul_of_nonneg_left hinv (pow_nonneg hH₁0 _)
    _ = H₁ ^ Fintype.card ι * H₂ ^ (Fintype.card ι * E.card) * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂ := by ring
end Formalism.HermitianLatticeCounting.P
