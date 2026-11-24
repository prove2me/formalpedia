-- Prove2me | solution 1 for BalanceSpecification.MarkerExtension.exists_wordCount_exp_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:44.653022+00:00
-- url     : https://prove2.me/submissions/74a45fd8-a17e-45ce-bc6f-a1429716031d

module
public import Definitions.Def_BalanceSpecificaton_MarkerSuffix
public import Definitions.Def_BalanceSpecificaton_RenewalBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerWordBounds
public import Theorems.Thm_BalanceSpecification_MarkerExtension_mem_endingMarkerFinset
public import Theorems.Thm_BalanceSpecification_MarkerExtension_wordCount_le_lastMarker_sum
public import Theorems.Thm_BalanceSpecification_MarkerExtension_endingMarker_exp_bound
public import Theorems.Thm_BalanceSpecification_MarkerEmbedding_block_mapConfiguration
public import Theorems.Thm_BalanceSpecification_MarkerExtension_mem_payloadSuffixFinset
public import Theorems.Thm_BalanceSpecification_convolution_le_geometric_envelope
public import Theorems.Thm_BalanceSpecification_entropy_nonneg
public import Theorems.Thm_BalanceSpecification_follower_card_reverseLanguage
public import Theorems.Thm_BalanceSpecification_getElem_block
public import Theorems.Thm_BalanceSpecification_length_block
public import Theorems.Thm_BalanceSpecification_mem_allWords
public import Theorems.Thm_BalanceSpecification_mem_followerFinset
public import Theorems.Thm_BalanceSpecification_mem_forbiddenShift_iff
public import Theorems.Thm_BalanceSpecification_mem_predecessorFinset
public import Theorems.Thm_BalanceSpecification_mem_shortWords
public import Theorems.Thm_BalanceSpecification_mem_wordFinset
public import Theorems.Thm_BalanceSpecification_nil_mem_generatedWords
public import Theorems.Thm_BalanceSpecification_periodicConfiguration_shift
public import Theorems.Thm_BalanceSpecification_wordCount_reverseLanguage
attribute [local simp] BalanceSpecification.MarkerEmbedding.block_mapConfiguration
attribute [local simp] BalanceSpecification.MarkerExtension.mem_payloadSuffixFinset
attribute [local simp] BalanceSpecification.follower_card_reverseLanguage
attribute [local simp] BalanceSpecification.getElem_block
attribute [local simp] BalanceSpecification.length_block
attribute [local simp] BalanceSpecification.mem_allWords
attribute [local simp] BalanceSpecification.mem_followerFinset
attribute [local simp] BalanceSpecification.mem_forbiddenShift_iff
attribute [local simp] BalanceSpecification.mem_predecessorFinset
attribute [local simp] BalanceSpecification.mem_shortWords
attribute [local simp] BalanceSpecification.mem_wordFinset
attribute [local simp] BalanceSpecification.nil_mem_generatedWords
attribute [local simp] BalanceSpecification.periodicConfiguration_shift
attribute [local simp] BalanceSpecification.wordCount_reverseLanguage


attribute [local simp] BalanceSpecification.MarkerExtension.mem_endingMarkerFinset

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace (Option A)] [DiscreteTopology (Option A)]
variable {Y : ShiftSpace A} (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
omit [DiscreteTopology A]
namespace BalanceSpecification.MarkerExtension
theorem _root_.solution {hY : Y.carrier.Nonempty} {C ρ : ℝ}
    (hC : 1 ≤ C)
    (hupper : ∀ n : ℕ, (wordCount (language Y) n : ℝ) ≤ C * Real.exp ((n : ℝ) * entropy Y hY))
    (hstrict : StrictMono s) (hsize : ∀ n : ℕ, 1 ≤ n → 4 * (n + M) ≤ s n)
    (hcofinal : ∀ L : ℕ, ∃ n : ℕ, 1 ≤ n ∧ L ≤ s n)
    (hρlo : Real.exp (entropy Y hY / 4) < ρ) (hρhi : ρ < Real.exp (entropy Y hY))
    (hgen : ∀ n : ℕ, (wordCount (generatedWords (code M hM x s)) n : ℝ) ≤ ρ ^ n) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, (wordCount (language (shift M hM x s)) n : ℝ) ≤
      K * Real.exp ((n : ℝ) * entropy Y hY) := by
  let β := Real.exp (entropy Y hY)
  let B := C / (1 - Real.exp (entropy Y hY / 4) / ρ)
  let e : ℕ → ℝ := fun k => (endingMarkerFinset (shift M hM x s) (k + 1)).card
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hρpos : 0 < ρ := (Real.exp_pos _).trans hρlo
  have hβpos : 0 < β := Real.exp_pos _
  have hβone : 1 ≤ β := Real.one_le_exp (entropy_nonneg hY)
  have hB : 0 ≤ B := div_nonneg hC0 (sub_nonneg.mpr ((div_lt_one hρpos).mpr hρlo).le)
  have hden : 0 < 1 - ρ / β := sub_pos.mpr ((div_lt_one hβpos).mpr hρhi)
  have he0 : ∀ k, 0 ≤ e k := fun k => Nat.cast_nonneg _
  have hebound : ∀ k, e k ≤ B * ρ ^ k :=
    endingMarker_exp_bound M hM x s hC hupper hstrict hsize hcofinal hρlo hgen
  have hsource : ∀ n : ℕ, (wordCount (language Y) n : ℝ) ≤ C * β ^ n := by
    intro n
    simpa only [β, Real.exp_nat_mul] using hupper n
  let K := C + C * (B / (1 - ρ / β))
  have hK : 1 ≤ K := by
    have H := mul_nonneg hC0 (div_nonneg hB hden.le)
    dsimp only [K]
    linarith only [hC, H]
  refine ⟨K, hK, ?_⟩
  intro n
  have hcount : (wordCount (language (shift M hM x s)) n : ℝ) ≤
      (wordCount (language Y) n : ℝ) +
        ∑ k ∈ Finset.range n, e k * (wordCount (language Y) (n - (k + 1)) : ℝ) := by
    dsimp only [e]
    exact_mod_cast wordCount_le_lastMarker_sum M hM x s n
  have hsum : (∑ k ∈ Finset.range n, e k *
      (wordCount (language Y) (n - (k + 1)) : ℝ)) ≤
      C * (∑ k ∈ Finset.range n, e k * β ^ (n - k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    have htail : (wordCount (language Y) (n - (k + 1)) : ℝ) ≤ C * β ^ (n - k) :=
      (hsource _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hβone (by omega)) hC0)
    calc
      e k * (wordCount (language Y) (n - (k + 1)) : ℝ) ≤ e k * (C * β ^ (n - k)) :=
        mul_le_mul_of_nonneg_left htail (he0 k)
      _ = C * (e k * β ^ (n - k)) := by ring
  have hsum_extend : (∑ k ∈ Finset.range n, e k * β ^ (n - k)) ≤
      ∑ k ∈ Finset.range (n + 1), e k * β ^ (n - k) := by
    rw [Finset.sum_range_succ]
    exact le_add_of_nonneg_right (mul_nonneg (he0 n) (pow_nonneg hβpos.le _))
  have hconv : (∑ k ∈ Finset.range (n + 1), e k * β ^ (n - k)) ≤
      (B / (1 - ρ / β)) * β ^ n :=
    convolution_le_geometric_envelope hρpos.le hβpos hρhi hB he0 hebound
      (fun k => le_rfl) n
  have H : (wordCount (language (shift M hM x s)) n : ℝ) ≤ K * β ^ n := by
    calc
      _ ≤ (wordCount (language Y) n : ℝ) +
          ∑ k ∈ Finset.range n, e k * (wordCount (language Y) (n - (k + 1)) : ℝ) := hcount
      _ ≤ C * β ^ n + C * (∑ k ∈ Finset.range n, e k * β ^ (n - k)) :=
        add_le_add (hsource n) hsum
      _ ≤ C * β ^ n + C * ((B / (1 - ρ / β)) * β ^ n) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (hsum_extend.trans hconv) hC0)
      _ = K * β ^ n := by dsimp only [K]; ring
  simpa only [β, Real.exp_nat_mul] using H
end BalanceSpecification.MarkerExtension
