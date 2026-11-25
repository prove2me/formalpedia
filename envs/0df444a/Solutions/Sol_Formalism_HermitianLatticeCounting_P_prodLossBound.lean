-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.prodLossBound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:11:11.339768+00:00
-- url     : https://prove2.me/submissions/d86a6207-340e-416b-86cd-fd731b746d24

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_prodMaxLeProdMaxDiv
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_prodMaxInvLeSq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_prodMaxMulMaxInvLe
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
private theorem max_self_inv_le_max_one_mul_max_one_inv {x : ℝ} (hx : 0 < x) :
    max x (1 / x) ≤ max 1 x * max 1 (1 / x) := by
  have h0 : 0 ≤ max 1 (1 / x) := zero_le_one.trans (le_max_left _ _)
  apply max_le
  · calc x ≤ max 1 x := le_max_right _ _
      _ = max 1 x * 1 := (mul_one _).symm
      _ ≤ max 1 x * max 1 (1 / x) := mul_le_mul_of_nonneg_left (le_max_left _ _)
          (zero_le_one.trans (le_max_left _ _))
  · exact (le_max_right 1 (1 / x)).trans (le_mul_of_one_le_left h0 (le_max_left _ _))
private theorem LatticeSumBounds_size_nonneg {ι l : Type*} [Fintype ι] (E : Finset l) (D : l → ι → ℝ) (H₂ : ℝ) :
    0 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂ :=
  Finset.prod_nonneg (fun _ _ => finset_prod_max_one_nonneg _ _)
end Formalism.HermitianLatticeCounting.P
end

set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : LossProd := by
  classical
  intro ι l _ E D G B H₂ e₁ e₂ l₀ Sg hB hH hl₀ hD hDprod hG hGprod hGD
  have hB0 : 0 ≤ B := by linarith
  have hH0 : 0 ≤ H₂ := by linarith
  have hthr := LatticeSumBounds_size_nonneg E D H₂
  have P1 : ∏ _v ∈ Sg, B ≤ B ^ Fintype.card ι := by
    rw [Finset.prod_const]; exact pow_le_pow_right₀ hB (Finset.card_le_univ Sg)
  have hT : ∏ v, max 1 (D l₀ v) ≤ H₂ ^ Fintype.card ι * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂ := by
    refine (prodMaxLeProdMaxDiv ι (D l₀) H₂ hH (fun v => (hD l₀ hl₀ v).le)).trans ?_
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hH0 _)
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.size
    apply Finset.prod_le_prod (fun v _ => zero_le_one.trans (le_max_left _ _))
    intro v _
    rw [← Finset.mul_prod_erase E _ hl₀]
    exact le_mul_of_one_le_right (zero_le_one.trans (le_max_left _ _))
      (one_le_finset_prod_of_forall_one_le _ _ (fun i _ => le_max_left _ _))
  have hGm : ∏ v, max 1 (G v) ≤ (∏ v, max 1 (D l₀ v)) ^ 2 := by
    rw [← Finset.prod_pow]
    apply Finset.prod_le_prod (fun v _ => zero_le_one.trans (le_max_left _ _))
    intro v _
    exact max_le (one_le_pow₀ (le_max_left _ _))
      ((hGD v).trans (pow_le_pow_left₀ (hD l₀ hl₀ v).le (le_max_right _ _) 2))
  have P2 : ∏ v ∈ Sg, max (G v) (1 / G v) ^ e₁ ≤
      (H₂ ^ Fintype.card ι * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂) ^ (4 * e₁) := by
    rw [Finset.prod_pow, pow_mul (H₂ ^ Fintype.card ι * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂) 4 e₁]
    apply pow_le_pow_left₀ (Finset.prod_nonneg (fun v _ => (hG v).le.trans (le_max_left _ _)))
    calc ∏ v ∈ Sg, max (G v) (1 / G v) ≤ (∏ v, max 1 (G v)) ^ 2 :=
          (prodMaxInvLeSq ι G Sg hG hGprod).1
      _ ≤ ((∏ v, max 1 (D l₀ v)) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (finset_prod_max_one_nonneg _ _) hGm 2
      _ ≤ ((H₂ ^ Fintype.card ι * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (by positivity)
            (pow_le_pow_left₀ (finset_prod_max_one_nonneg _ _) hT 2) 2
      _ = (H₂ ^ Fintype.card ι * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂) ^ 4 := by ring
  have P3 : ∏ v ∈ Sg, ∏ i ∈ E, max (D i v) (1 / D i v) ^ e₂ ≤
      (H₂ ^ (Fintype.card ι * E.card) * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂) ^ (2 * e₂) := by
    simp only [Finset.prod_pow]
    rw [pow_mul (H₂ ^ (Fintype.card ι * E.card) * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂) 2 e₂]
    apply pow_le_pow_left₀ (Finset.prod_nonneg (fun v _ => Finset.prod_nonneg
      (fun i hi => (hD i hi v).le.trans (le_max_left _ _))))
    calc ∏ v ∈ Sg, ∏ i ∈ E, max (D i v) (1 / D i v)
          ≤ ∏ v ∈ Sg, ∏ i ∈ E, (max 1 (D i v) * max 1 (1 / D i v)) := by
          apply Finset.prod_le_prod (fun v _ => Finset.prod_nonneg
            (fun i hi => (hD i hi v).le.trans (le_max_left _ _)))
          intro v _
          exact Finset.prod_le_prod (fun i hi => (hD i hi v).le.trans (le_max_left _ _))
            (fun i hi => max_self_inv_le_max_one_mul_max_one_inv (hD i hi v))
      _ ≤ ∏ v, ∏ i ∈ E, (max 1 (D i v) * max 1 (1 / D i v)) :=
          finset_prod_real_mono_of_subset_of_one_le _ _ (Finset.subset_univ _) _ (fun v _ => one_le_finset_prod_of_forall_one_le _ _
            (fun i _ => one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _)))
      _ ≤ H₂ ^ (2 * Fintype.card ι * E.card) * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂ ^ 2 :=
          prodMaxMulMaxInvLe ι l E D H₂ hH hD hDprod
      _ = (H₂ ^ (Fintype.card ι * E.card) * Formalism.HermitianLatticeCounting.LatticeSumBounds.size E D H₂) ^ 2 := by ring
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  exact mul_le_mul (mul_le_mul P1 P2
      (Finset.prod_nonneg (fun v _ => pow_nonneg ((hG v).le.trans (le_max_left _ _)) _))
      (pow_nonneg hB0 _)) P3
    (Finset.prod_nonneg (fun v _ => Finset.prod_nonneg
      (fun i hi => pow_nonneg ((hD i hi v).le.trans (le_max_left _ _)) _)))
    (mul_nonneg (pow_nonneg hB0 _) (pow_nonneg (mul_nonneg (pow_nonneg hH0 _) hthr) _))
end Formalism.HermitianLatticeCounting.P
