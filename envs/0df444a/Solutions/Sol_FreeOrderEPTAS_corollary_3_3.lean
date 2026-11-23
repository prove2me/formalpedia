-- Prove2me | solution 1 for FreeOrderEPTAS.corollary_3_3
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T14:17:38.176714+00:00
-- url     : https://prove2.me/submissions/a61e3cec-4870-40ff-ae1c-bf6bd71215ed

import Mathlib
import Definitions.Def_FreeOrderEPTAS_santaClaus
import Definitions.Def_FreeOrderEPTAS_prophetInstance
import Definitions.Def_FreeOrderEPTAS_IPProphets
import Definitions.Def_FreeOrderEPTAS_orc
import Theorems.Thm_FreeOrderEPTAS_theorem_2_1

open MeasureTheory

namespace FreeOrderEPTAS.Cor33

open FreeOrderEPTAS

lemma excess_nonneg {n : ℕ} (I : Instance n) (j : Fin n) (b : ℝ) : 0 ≤ excess I j b := by
  unfold excess
  exact integral_nonneg (fun x => le_max_right _ _)

lemma orc_sub {n : ℕ} (I : Instance n) (j : Fin n) (b : ℝ) :
    orc I j b - b = excess I j b := by
  unfold orc excess
  have h1 : Integrable (fun x : ℝ => max x b) (I.μ j) :=
    (I.integrable j).sup (integrable_const b)
  have h2 : (fun x : ℝ => max (x - b) 0) = fun x => max x b - b := by
    funext x
    rcases le_total x b with h | h
    · rw [max_eq_right h, max_eq_right (by linarith)]; ring
    · rw [max_eq_left h, max_eq_left (by linarith)]
  rw [h2, integral_sub h1 (integrable_const b)]
  simp

lemma bit_nonneg (c : Bool) : 0 ≤ bit c := by unfold bit; split_ifs <;> norm_num

lemma bit_le_one (c : Bool) : bit c ≤ 1 := by unfold bit; split_ifs <;> norm_num

/-- `∑ min(a_j,1) x_j ≥ 1` when `∑ a_j x_j ≥ 1` and `a ≥ 0`. -/
lemma sum_trunc_ge {n : ℕ} (a : Fin n → ℝ) (x : Fin n → Bool) (ha : ∀ j, 0 ≤ a j)
    (h : 1 ≤ ∑ j, a j * bit (x j)) : 1 ≤ ∑ j, max 0 (min (a j) 1) * bit (x j) := by
  have hnn : ∀ j, 0 ≤ max 0 (min (a j) 1) * bit (x j) :=
    fun j => mul_nonneg (le_max_left _ _) (bit_nonneg _)
  by_cases hex : ∃ j, x j = true ∧ 1 ≤ a j
  · obtain ⟨j, hx, hj⟩ := hex
    have : max 0 (min (a j) 1) * bit (x j) = 1 := by
      simp [hx, bit, min_eq_right hj]
    calc (1 : ℝ) = _ := this.symm
      _ ≤ _ := Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ j)
  · push Not at hex
    calc (1 : ℝ) ≤ _ := h
      _ = _ := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        cases hx : x j
        · simp [bit]
        · have := hex j hx
          rw [min_eq_left this.le, max_eq_right (ha j)]

lemma trunc_le {a : ℝ} (ha : 0 ≤ a) : max 0 (min a 1) ≤ a :=
  max_le ha (min_le_left _ _)

lemma feasible_of {m n : ℕ} (I : Instance n) (b Δ : Fin m → ℝ)
    (h : IPProphetsFeasible I b Δ) :
    IPFeasible (prophetInstance (fun i j => orc I j (b i) - b i) Δ) := by
  obtain ⟨ξ, ⟨hc1, hc2⟩, hl⟩ := h
  refine ⟨ξ, ⟨hc1, fun i => ?_⟩, fun i d hd => ?_⟩
  · simp only [prophetInstance]
    split_ifs with hi
    · exact hc2 i hi
    · exact (Finset.card_filter_le _ _).trans (by simp)
  · simp only [prophetInstance] at hd
    split_ifs at hd with hΔ
    · simp only [load, prophetInstance, if_pos hΔ, orc_sub]
      apply sum_trunc_ge _ _ (fun j => div_nonneg (excess_nonneg _ _ _) hΔ.le)
      have : ∑ j, excess I j (b i) / Δ i * bit (ξ i j)
          = (∑ j, excess I j (b i) * bit (ξ i j)) / Δ i := by
        rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun j _ => by ring)
      rw [this, le_div_iff₀ hΔ, one_mul]; exact hl i
    · simp at hd

lemma good_of {m n : ℕ} (I : Instance n) (b Δ : Fin m → ℝ) (ε : ℝ) (hε : ε ≤ 1)
    (x : Assignment m n)
    (h1 : MeetsCard (prophetInstance (fun i j => orc I j (b i) - b i) Δ) x)
    (h2 : LoadAtLeast (prophetInstance (fun i j => orc I j (b i) - b i) Δ) x (1 - ε)) :
    ProphetCard x ∧ ∀ i, (1 - ε) * Δ i ≤ ∑ j, excess I j (b i) * bit (x i j) := by
  obtain ⟨hc1, hc2⟩ := h1
  refine ⟨⟨hc1, fun i hi => ?_⟩, fun i => ?_⟩
  · have := hc2 i
    simp only [prophetInstance, if_pos hi] at this
    exact this
  · have hS : 0 ≤ ∑ j, excess I j (b i) * bit (x i j) :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (excess_nonneg _ _ _) (bit_nonneg _))
    by_cases hΔ : 0 < Δ i
    · have hm : (0 : Fin 1) ∈ (prophetInstance (fun i j => orc I j (b i) - b i) Δ).A i := by
        simp [prophetInstance, hΔ]
      have := h2 i 0 hm
      simp only [load, prophetInstance, if_pos hΔ, orc_sub] at this
      have hle : ∑ j, max 0 (min (excess I j (b i) / Δ i) 1) * bit (x i j)
          ≤ (∑ j, excess I j (b i) * bit (x i j)) / Δ i := by
        rw [Finset.sum_div]
        refine Finset.sum_le_sum (fun j _ => ?_)
        rw [mul_div_right_comm]
        exact mul_le_mul_of_nonneg_right
          (trunc_le (div_nonneg (excess_nonneg _ _ _) hΔ.le)) (bit_nonneg _)
      have := this.trans hle
      rwa [le_div_iff₀ hΔ] at this
    · push Not at hΔ
      exact (mul_nonpos_of_nonneg_of_nonpos (by linarith) hΔ).trans hS

lemma pr_mono {α : Type} (p : PMF α) {S T : Set α} (h : S ⊆ T) : pr p S ≤ pr p T := by
  unfold pr
  have hT : p.toOuterMeasure T ≤ 1 := by
    rw [← (PMF.toOuterMeasure_apply_eq_one_iff p Set.univ).2 (Set.subset_univ _)]
    exact p.toOuterMeasure.mono (Set.subset_univ _)
  exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top hT)
    (p.toOuterMeasure.mono h)

end FreeOrderEPTAS.Cor33

open FreeOrderEPTAS FreeOrderEPTAS.Cor33 in
theorem solution :
    ∃ (t : ℕ → ℕ) (d : ℕ), ∀ (q : ℕ), 2 ≤ q → ∀ (m n : ℕ), m ≤ 2 * q + 1 →
      ∀ (I : Instance n) (b Δ : Fin m → ℝ), (∀ i, 0 ≤ b i) →
      ∀ (lp : LPSolver) (rnd : Rounding), IsLPSolver lp → IsDependentRounding rnd →
        (IPProphetsFeasible I b Δ → (1 / 2 : ℝ) ≤
          pr ((santaClaus (1 / (q : ℝ)) (prophetInstance (fun i j => orc I j (b i) - b i) Δ)
            lp rnd).run 0)
            {r | ∃ x, r.1 = some x ∧ ProphetCard x ∧
              ∀ i, (1 - 1 / (q : ℝ)) * Δ i ≤ ∑ j, excess I j (b i) * bit (x i j)}) ∧
        ∀ r ∈ ((santaClaus (1 / (q : ℝ)) (prophetInstance (fun i j => orc I j (b i) - b i) Δ)
            lp rnd).run 0).support,
          (∀ x, r.1 = some x → ProphetCard x ∧
            ∀ i, (1 - 1 / (q : ℝ)) * Δ i ≤ ∑ j, excess I j (b i) * bit (x i j)) ∧
          r.2.total ≤ t q * (n + 1) ^ d ∧ r.2.maxSize ≤ t q * (n + 1) := by
  obtain ⟨f, d, hf⟩ := theorem_2_1
  refine ⟨fun q => ∑ m ∈ Finset.range (2 * q + 2), f q m 1, d, ?_⟩
  intro q hq m n hm I b Δ _hb lp rnd hlp hrnd
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hε0 : 0 < 1 / (q : ℝ) := by positivity
  have hε1 : 1 / (q : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hceil : ⌈1 / (1 / (q : ℝ))⌉₊ = q := by simp
  have hfle : f q m 1 ≤ ∑ m ∈ Finset.range (2 * q + 2), f q m 1 :=
    Finset.single_le_sum (f := fun m => f q m 1) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (show m < 2 * q + 2 by omega))
  obtain ⟨hA, hB⟩ := hf (1 / (q : ℝ)) hε0 hε1 m 1 n
    (prophetInstance (fun i j => orc I j (b i) - b i) Δ) lp rnd hlp hrnd
  rw [hceil] at hB
  refine ⟨fun hfeas => (hA (feasible_of I b Δ hfeas)).trans (pr_mono _ ?_), fun r hr => ?_⟩
  · rintro r ⟨X, hX, h1, h2⟩
    exact ⟨X, hX, good_of I b Δ _ hε1.le X h1 h2⟩
  · obtain ⟨h1, h2, h3⟩ := hB r hr
    refine ⟨fun x hx => ?_, h2.trans ?_, h3.trans ?_⟩
    · obtain ⟨a, c⟩ := h1 x hx
      exact good_of I b Δ _ hε1.le x a c
    · exact Nat.mul_le_mul_right _ hfle
    · exact Nat.mul_le_mul_right _ hfle
