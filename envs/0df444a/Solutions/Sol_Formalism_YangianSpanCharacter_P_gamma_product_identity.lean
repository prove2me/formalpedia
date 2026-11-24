-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.gamma_product_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:42:19.620812+00:00
-- url     : https://prove2.me/submissions/8e4d602d-7378-481d-8c58-9e95874313c5

import Definitions.Def_Formalism_YangianSpanCharacter_StatementE
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_SpanCharacterIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.YangianSpanCharacter.P
open Finset
private lemma weier {ι : Type} (s : Finset ι) (a : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ a i)
    (h1 : ∀ i ∈ s, a i ≤ 1) : 1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have ih' := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have haj0 := h0 j (Finset.mem_insert_self j s)
    have haj1 := h1 j (Finset.mem_insert_self j s)
    have hS : 0 ≤ ∑ i ∈ s, a i :=
      Finset.sum_nonneg fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    have := mul_le_mul_of_nonneg_left ih' (sub_nonneg.mpr haj1)
    nlinarith
private lemma geom_le (g : ℝ) (hg : 3 ≤ g) (k : ℕ) :
    ∑ i ∈ Finset.Ico 1 k, (g ^ i)⁻¹ ≤ 1 / (g - 1) := by
  have hr0 : 0 < g⁻¹ := by positivity
  have hr1 : g⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  simp_rw [← inv_pow]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Finset.Ico_eq_empty_of_le (Nat.zero_le 1), Finset.sum_empty]
    exact div_nonneg zero_le_one (by linarith)
  · have hm := geom_sum_Ico_mul g⁻¹ (show 1 ≤ k from hk)
    have hS : (∑ i ∈ Finset.Ico 1 k, g⁻¹ ^ i) * (1 - g⁻¹) ≤ g⁻¹ := by
      have : 0 ≤ g⁻¹ ^ k := by positivity
      nlinarith
    have hpos : 0 < 1 - g⁻¹ := by linarith
    have he : 1 / (g - 1) = g⁻¹ / (1 - g⁻¹) := by
      have : g ≠ 0 := by linarith
      have : g - 1 ≠ 0 := by linarith
      field_simp
    rw [he, le_div_iff₀ hpos]
    exact hS
end Formalism.YangianSpanCharacter.P
end

set_option autoImplicit false
open Formalism Formalism.YangianSpanCharacter Formalism.YangianSpanCharacter.P
open Finset
namespace Formalism.YangianSpanCharacter.P
theorem _root_.solution : Formalism.YangianSpanCharacter.E.GGProd := by
  intro g hg k
  have hg0 : 0 < g := by linarith
  rw [Finset.prod_inv_distrib]
  have hW := weier (Finset.Ico 1 k) (fun i => (g ^ i)⁻¹)
    (fun i _ => by positivity)
    (fun i hi => by
      have hi1 : i ≠ 0 := by
        have := (Finset.mem_Ico.mp hi).1; omega
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith)))
  have hG := geom_le g hg k
  have hq : g / (g + 3) ≤ 1 - 1 / (g - 1) := by
    have h1 : 0 < g - 1 := by linarith
    have h3 : 0 < g + 3 := by linarith
    rw [div_le_iff₀ h3, sub_mul, div_mul_eq_mul_div, one_mul, le_sub_iff_add_le,
      ← le_sub_iff_add_le', div_le_iff₀ h1]
    nlinarith
  have hP : g / (g + 3) ≤ ∏ i ∈ Finset.Ico 1 k, (1 - (g ^ i)⁻¹) := by
    have hW' : 1 - ∑ i ∈ Finset.Ico 1 k, (g ^ i)⁻¹ ≤ ∏ i ∈ Finset.Ico 1 k, (1 - (g ^ i)⁻¹) := hW
    linarith
  have hPpos : 0 < ∏ i ∈ Finset.Ico 1 k, (1 - (g ^ i)⁻¹) :=
    lt_of_lt_of_le (by positivity) hP
  rw [inv_le_comm₀ hPpos (by positivity)]
  have : (1 + 3 / g)⁻¹ = g / (g + 3) := by
    field_simp
  rw [this]; exact hP
end Formalism.YangianSpanCharacter.P
