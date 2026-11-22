-- Prove2me | solution 1 for BellSampling.Learn.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:10:29.760214+00:00
-- url     : https://prove2.me/submissions/e2cf95d8-a199-48a5-b441-2866013de6d0

import Mathlib
import Definitions.Def_StabilizerRank
import Definitions.Def_BellSampling_Learn_Setting
import Theorems.Thm_BellSampling_Learn_bell_outcome_uniform
import Theorems.Thm_BellSampling_Learn_stabSet_subspace
import Theorems.Thm_BellSampling_Learn_span_failure_le
import Theorems.Thm_BellSampling_Learn_determined_by_signs
open StabilizerRank
open BellSampling.Learn
set_option autoImplicit false

private lemma pstr_add_self {n : ℕ} (x : PStr n) : x + x = 0 := by
  have hz2 : ∀ a : ZMod 2, a + a = 0 := by decide
  ext i
  · exact hz2 (x i).1
  · exact hz2 (x i).2

private lemma pstr_add_cancel_middle {n : ℕ} (a b c : PStr n) :
    (a + b) + (b + c) = a + c := by
  calc
    (a + b) + (b + c) = a + (b + b) + c := by abel
    _ = a + 0 + c := by rw [pstr_add_self]
    _ = a + c := by abel

theorem solution (n : ℕ) (ψ : QState n) (hψ : IsStabilizerState ψ) :
    1 - 1 / (2 : ℝ) ^ n ≤ algo1Prob ψ (algo1Success ψ) ∧
    ∀ b : Fin n → PStr n, (∀ j, b j ∈ stabSet ψ) → LinearIndependent (ZMod 2) b →
      (∀ j, (pauliH (b j)).mulVec ψ = ψ ∨ (pauliH (b j)).mulVec ψ = -ψ) ∧
      ∀ φ : QState n,
        (∀ j (e : ℂ), (pauliH (b j)).mulVec ψ = e • ψ → (pauliH (b j)).mulVec φ = e • φ) →
        ∃ c : ℂ, φ = c • ψ := by
  refine ⟨?_, fun b hb hli => BellSampling.Learn.determined_by_signs ψ hψ b hb hli⟩
  classical
  obtain ⟨W, hW_set, hW_rank⟩ := BellSampling.Learn.stabSet_subspace ψ hψ
  obtain ⟨s, hs⟩ := BellSampling.Learn.bell_outcome_uniform ψ hψ
  have hprob_eq : ∀ x : PStr n,
      bellProb ψ x = if x + s ∈ W then (1 / (2 : ℝ) ^ n) else 0 := by
    intro x
    by_cases hx : x + s ∈ W
    · rw [if_pos hx]
      exact (hs x).1 (by rwa [← hW_set])
    · rw [if_neg hx]
      exact (hs x).2 (by rwa [← hW_set])
  have hcardW : Fintype.card W = 2 ^ n := by
    have hc := Module.card_eq_pow_finrank (K := ZMod 2) (V := W)
    simpa [ZMod.card, hW_rank] using hc
  have hsum_r0 : (∑ r₀ : PStr n, if r₀ + s ∈ W then (1 / (2 : ℝ) ^ n) else 0) = 1 := by
    have h_equiv : (∑ r₀ : PStr n, if r₀ + s ∈ W then (1 / (2 : ℝ) ^ n) else 0) =
        ∑ u : PStr n, if u ∈ W then (1 / (2 : ℝ) ^ n) else 0 :=
      Equiv.sum_comp (Equiv.addRight s)
        (fun u : PStr n => if u ∈ W then (1 / (2 : ℝ) ^ n) else 0)
    have h_sub : (∑ u : PStr n, if u ∈ W then (1 / (2 : ℝ) ^ n) else 0) =
        ∑ _w : W, (1 / (2 : ℝ) ^ n) := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter fun u : PStr n => u ∈ W)
        (fun u => by simp) (fun _ => (1 / (2 : ℝ) ^ n))
    rw [h_equiv, h_sub, Finset.sum_const, Finset.card_univ, hcardW, nsmul_eq_mul,
      Nat.cast_pow, Nat.cast_ofNat]
    have h2n_ne : (2 : ℝ) ^ n ≠ 0 := by positivity
    exact mul_one_div_cancel h2n_ne
  set q : ℝ := 1 / (2 : ℝ) ^ n
  have hq_nonneg : 0 ≤ q := by unfold q; positivity
  set f_u : (Fin (2 * n) → PStr n) → ℝ := fun u =>
    if Submodule.span (ZMod 2) (Set.range u) = W then q ^ (2 * n) else 0
  set S_u : ℝ := ∑ u : Fin (2 * n) → PStr n, f_u u
  have h_inner_r0 : ∀ r₀ : PStr n,
      (∑ r : Fin (2 * n) → PStr n,
        if algo1Success ψ r₀ r then bellProb ψ r₀ * ∏ i, bellProb ψ (r i) else 0) =
      (if r₀ + s ∈ W then q else 0) * S_u := by
    intro r₀
    by_cases hr₀ : r₀ + s ∈ W
    · have hbr₀ : bellProb ψ r₀ = q := by rw [hprob_eq, if_pos hr₀]
      rw [if_pos hr₀]
      have h_term : ∀ r : Fin (2 * n) → PStr n,
          (if algo1Success ψ r₀ r then bellProb ψ r₀ * ∏ i, bellProb ψ (r i) else 0) =
          q * f_u (fun i => r i + r₀) := by
        intro r
        have h_succ_iff : algo1Success ψ r₀ r ↔
            Submodule.span (ZMod 2) (Set.range fun i => r i + r₀) = W := by
          unfold algo1Success
          rw [← hW_set, SetLike.coe_set_eq]
        by_cases hsucc : Submodule.span (ZMod 2) (Set.range fun i => r i + r₀) = W
        · have ha : algo1Success ψ r₀ r := h_succ_iff.mpr hsucc
          simp only [f_u, if_pos ha, if_pos hsucc, hbr₀]
          congr 1
          have h_ri : ∀ i : Fin (2 * n), bellProb ψ (r i) = q := by
            intro i
            have h_in_span : r i + r₀ ∈ Submodule.span (ZMod 2) (Set.range fun j => r j + r₀) :=
              Submodule.subset_span ⟨i, rfl⟩
            rw [hsucc] at h_in_span
            have h_in_W : r i + s ∈ W := by
              rw [← pstr_add_cancel_middle (r i) r₀ s]
              exact W.add_mem h_in_span hr₀
            rw [hprob_eq, if_pos h_in_W]
          simp [h_ri]
        · have ha : ¬ algo1Success ψ r₀ r := fun h => hsucc (h_succ_iff.mp h)
          simp [f_u, ha, hsucc]
      simp_rw [h_term, ← Finset.mul_sum]
      congr 1
      exact Equiv.sum_comp (Equiv.addRight (fun _ : Fin (2 * n) => r₀)) f_u
    · have hbr₀ : bellProb ψ r₀ = 0 := by rw [hprob_eq, if_neg hr₀]
      simp [hr₀, hbr₀]
  have halgo_eq : algo1Prob ψ (algo1Success ψ) = S_u := by
    unfold algo1Prob
    simp_rw [h_inner_r0, ← Finset.sum_mul, hsum_r0, one_mul]
  rw [halgo_eq]
  let emb : (Fin (2 * n) → W) → (Fin (2 * n) → PStr n) := fun v i => (v i : PStr n)
  have hemb_inj : Function.Injective emb :=
    fun v₁ v₂ h => funext fun i => Subtype.ext (congr_fun h i)
  have h_span_emb : ∀ v : Fin (2 * n) → W,
      Submodule.span (ZMod 2) (Set.range v) = ⊤ →
        Submodule.span (ZMod 2) (Set.range (emb v)) = W := by
    intro v hv
    have h_range : Set.range (emb v) = W.subtype '' Set.range v := by
      ext x
      simp [emb]
    rw [h_range, ← Submodule.map_span, hv, Submodule.map_top, Submodule.range_subtype]
  set GoodV := Finset.univ.filter
    (fun v : Fin (2 * n) → W => Submodule.span (ZMod 2) (Set.range v) = ⊤)
  set BadV := Finset.univ.filter
    (fun v : Fin (2 * n) → W => ¬ Submodule.span (ZMod 2) (Set.range v) = ⊤)
  have h_su_ge : (GoodV.card : ℝ) * q ^ (2 * n) ≤ S_u := by
    have h1 : (GoodV.card : ℝ) * q ^ (2 * n) = ∑ v ∈ GoodV, f_u (emb v) := by
      have h_congr : ∀ v ∈ GoodV, f_u (emb v) = q ^ (2 * n) := by
        intro v hv
        simp only [f_u, if_pos (h_span_emb v (Finset.mem_filter.mp hv).2)]
      rw [Finset.sum_congr rfl h_congr, Finset.sum_const, nsmul_eq_mul]
    rw [h1, ← Finset.sum_image (f := f_u) (fun v₁ _ v₂ _ h => hemb_inj h)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun u _ _ => by simp only [f_u]; split_ifs <;> positivity)
  have h_card_part : GoodV.card + BadV.card = (Fintype.card W) ^ (2 * n) := by
    rw [Finset.card_filter_add_card_filter_not]
    simp [Fintype.card_fin]
  have h_bad_ncard : BadV.card =
      Set.ncard {v : Fin (2 * n) → W | Submodule.span (ZMod 2) (Set.range v) ≠ ⊤} := by
    have h_set : (BadV : Set (Fin (2 * n) → W)) =
        {v : Fin (2 * n) → W | Submodule.span (ZMod 2) (Set.range v) ≠ ⊤} := by
      ext v
      simp [BadV]
    rw [← Set.ncard_coe_finset, h_set]
  have h_fail_le : (BadV.card : ℝ) ≤ 1 / 2 ^ n * (Fintype.card W : ℝ) ^ (2 * n) := by
    rw [h_bad_ncard]
    exact BellSampling.Learn.span_failure_le n hW_rank
  have h_good_ge : (1 - 1 / (2 : ℝ) ^ n) * (Fintype.card W : ℝ) ^ (2 * n) ≤ (GoodV.card : ℝ) := by
    have h_part_r : (GoodV.card : ℝ) + (BadV.card : ℝ) = (Fintype.card W : ℝ) ^ (2 * n) := by
      exact_mod_cast h_card_part
    linarith
  have h_cancel : (Fintype.card W : ℝ) ^ (2 * n) * q ^ (2 * n) = 1 := by
    rw [hcardW, Nat.cast_pow, Nat.cast_ofNat, ← mul_pow]
    simp [q]
  calc
    1 - 1 / (2 : ℝ) ^ n
        = (1 - 1 / (2 : ℝ) ^ n) * ((Fintype.card W : ℝ) ^ (2 * n) * q ^ (2 * n)) := by
          rw [h_cancel, mul_one]
    _ = ((1 - 1 / (2 : ℝ) ^ n) * (Fintype.card W : ℝ) ^ (2 * n)) * q ^ (2 * n) := by ring
    _ ≤ (GoodV.card : ℝ) * q ^ (2 * n) :=
          mul_le_mul_of_nonneg_right h_good_ge (by positivity)
    _ ≤ S_u := h_su_ge
