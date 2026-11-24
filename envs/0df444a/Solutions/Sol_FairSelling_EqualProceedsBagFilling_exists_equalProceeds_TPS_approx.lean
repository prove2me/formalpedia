-- Prove2me | solution 1 for FairSelling.EqualProceedsBagFilling.exists_equalProceeds_TPS_approx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:41:06.484455+00:00
-- url     : https://prove2.me/submissions/a4b2f1e5-8318-4989-837b-b8cefb271609

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_EqualProceedsBagFilling
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_priceSum_nonneg
import Theorems.Thm_FairSelling_EqualProceedsBagFilling_bagFilling_induction
import Theorems.Thm_FairSelling_TPS_nonneg
import Theorems.Thm_FairSelling_TPS_truncSum


set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.EqualProceedsBagFilling
variable {G : Type*} {n : ℕ}
variable {vi p : G → ℝ} {tk : ℝ}
variable [Fintype G] [DecidableEq G]
namespace FairSelling.EqualProceedsBagFilling
theorem _root_.solution (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧ o.EqualProceeds p ∧
      ∀ i, TPS n (v i) p / n ≤ util (v i) o i := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set t : Fin n → ℝ := fun i => TPS n (v i) p with htdef
  have ht : ∀ i, 0 ≤ t i := fun i => TPS_nonneg (v i) p hp
  have hfix : ∀ i, effSum (v i) p (t i) Finset.univ = (n : ℝ) * t i := by
    intro i
    have h := TPS_truncSum (n := n) (v i) p hp
    unfold truncSum at h
    unfold effSum effVal
    rw [div_eq_iff (ne_of_gt hn')] at h
    rw [h]
    ring
  obtain ⟨C, D, hCR, hDR, hCdisj, hCD, hsat⟩ :=
    bagFilling_induction v p t hv hp ht hn Finset.univ Finset.univ 0 le_rfl (by
      intro k _
      rw [hfix k, Finset.card_univ, Fintype.card_fin]
      simp)
  refine ⟨⟨D, C, fun _ => priceSum p D / n⟩, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact fun j => (hCD j).symm
  · exact hCdisj
  · intro j
    have := priceSum_nonneg hp D
    positivity
  · have : ∑ _j : Fin n, priceSum p D / n = priceSum p D := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_div_cancel₀ _ (ne_of_gt hn')]
    simpa [priceSum] using this.le
  · intro i
    simp [priceSum]
  · intro i
    have h := hsat i (Finset.mem_univ i)
    have ht' : t i = TPS n (v i) p := rfl
    rw [ht'] at h
    simp only [util]
    linarith
end FairSelling.EqualProceedsBagFilling
