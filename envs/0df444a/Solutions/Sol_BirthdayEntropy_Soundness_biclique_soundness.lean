-- Prove2me | solution 1 for BirthdayEntropy.Soundness.biclique_soundness
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:41:07.913314+00:00
-- url     : https://prove2.me/submissions/f9424cec-0f97-4254-8db2-60403b202ad8

import Theorems.Thm_BirthdayEntropy_Soundness_fixed_flattening_energy
import Theorems.Thm_BirthdayEntropy_Soundness_flattening_entropy
import Theorems.Thm_BirthdayEntropy_Soundness_entropy_cell_counting
noncomputable section
open scoped Classical
open BirthdayEntropy.Soundness OAI.ThorpCompatibility

private lemma cross_flatten {n m ℓ r : ℕ} (φ : CSP n m) (H : Finset (Vertex n ℓ))
    (X : Tuple n ℓ r) (hX : X ∈ accepted φ H r) : CrossConsistent (flatten X) := by
  classical
  intro i b hi hj
  obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.mp hi
  obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp hj
  have hadj := (Finset.mem_filter.mp hX).2.2.2 a c
  have hcons := hadj.2.1 i
  have ha' : (i,b) ∈ signed (X.1 a) ∪ signed (X.2 c) := Finset.mem_union_left _ ha
  have hc' : (i,!b) ∈ signed (X.1 a) ∪ signed (X.2 c) := Finset.mem_union_right _ hc
  cases b <;> exact hcons (by simpa [and_comm] using And.intro ha' hc')

private lemma mean_mul {α : Type*} [Fintype α] (Q : Law α) (c : ℝ) (f : α → ℝ) :
    Q.mean (fun a => c * f a) = c * Q.mean f := by
  simp only [Law.mean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

private lemma mean_floor {α : Type*} [Fintype α] (Ω : Finset α) (hΩ : Ω.Nonempty)
    (f : α → ℝ) (c : ℝ) (hf : ∀ a ∈ Ω, c ≤ f a) :
    c ≤ (uniformOn Ω hΩ).mean f := by
  let Q := uniformOn Ω hΩ
  have hmass : ∀ a, 0 < Q.mass a → a ∈ Ω := by
    intro a ha
    by_contra hn
    have hz : Q.mass a = 0 := by
      unfold Q uniformOn Law.map Law.uniform
      simp only
      apply Finset.sum_eq_zero
      intro x hx
      have hne : x.val ≠ a := by intro h; exact hn (h ▸ x.property)
      simp [hne]
    linarith
  calc
    c = ∑ a, Q.mass a * c := by rw [← Finset.sum_mul, Q.total, one_mul]
    _ ≤ ∑ a, Q.mass a * f a := by
      apply Finset.sum_le_sum
      intro a ha
      by_cases hp : 0 < Q.mass a
      · exact mul_le_mul_of_nonneg_left (hf a (hmass a hp)) (Q.nonneg a)
      · have hz : Q.mass a = 0 := le_antisymm (le_of_not_gt hp) (Q.nonneg a)
        simp [hz]

private lemma energy_floor {n ℓ : ℕ} (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hn : 0 ≤ (n : ℝ)) (hx : 0 ≤ ratio n ℓ) (hx1 : ratio n ℓ ≤ 1) (F : Flattening n) :
    β * n * ratio n ℓ ≤ energy ℓ β F := by
  unfold energy
  by_cases ht : ((terrible F).card : ℝ) < β * n
  · by_cases hb : (badCount F : ℝ) < β * n
    · rw [if_pos ⟨ht,hb⟩]
      apply le_trans _ (le_trans (le_max_right _ _) (le_max_right _ _))
      nlinarith [mul_nonneg hn hx]
    · apply le_trans _ (le_trans (le_max_left _ _) (le_max_right _ _))
      nlinarith [mul_le_mul_of_nonneg_left (le_of_not_gt hb) hx]
  · apply le_trans _ (le_max_left _ _)
    nlinarith [mul_le_mul_of_nonneg_left hx1 (mul_nonneg hβ.le hn), le_of_not_gt ht]

theorem solution (d ε : ℝ) (hd : 1 ≤ d) (hε : 0 < ε) :
    ∃ C₀ x₀ Cstar c : ℝ, 0 < C₀ ∧ 0 < x₀ ∧ x₀ < min (beta d ε) (1/2) ∧
      0 < Cstar ∧ 0 < c ∧
      ∀ (n m : ℕ) (φ : CSP n m), Source φ d → Gap φ ε →
      ∀ (ℓ : ℕ), Admitted n ℓ C₀ x₀ →
      ∀ (H : Finset (Vertex n ℓ)), H.card = Nat.choose n ℓ →
        acceptanceProbability φ H (repetition n ℓ Cstar) ≤
          Real.exp (-c * n * ratio n ℓ * logScale n ℓ) := by
  classical
  obtain ⟨c₀,hc₀,hfixed⟩ := fixed_flattening_energy d ε hd hε
  obtain ⟨C,D₁,D₂,hC,hD₁,hD₂,hent⟩ := flattening_entropy d ε hd hε
  have hβ : 0 < beta d ε := by
    unfold beta
    exact lt_min (by norm_num) (div_pos hε (by linarith))
  have hβ1 : beta d ε ≤ 1 := (min_le_left _ _).trans (by norm_num)
  let Cstar := (C+1)/c₀
  let C₀ := 2*(D₂+1)/beta d ε
  let x₀ := min (beta d ε) (1/2) / 2
  refine ⟨C₀,x₀,Cstar,beta d ε/12, by dsimp [C₀]; positivity,
    by dsimp [x₀]; positivity, ?_, by dsimp [Cstar]; positivity, by positivity, ?_⟩
  · dsimp [x₀]
    have : 0 < min (beta d ε) (1/2) := lt_min hβ (by norm_num)
    linarith
  intro n m φ hsrc hgap ℓ hadm H hH
  have hℓ : 2 ≤ ℓ := hadm.1
  have hn : 0 < (n : ℝ) := by
    have : 0 ≤ (n : ℝ) := by positivity
    by_contra h
    have hz : (n : ℝ) = 0 := le_antisymm (le_of_not_gt h) this
    have hs := hadm.2.1
    rw [hz, mul_zero] at hs
    have : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  have hx₀ : 0 < x₀ := by dsimp [x₀]; positivity
  have hx₀min : x₀ < min (beta d ε) (1/2) := by dsimp [x₀]; have := lt_min hβ (by norm_num : (0:ℝ)<1/2); linarith
  have hx : 0 < ratio n ℓ := div_pos (by exact_mod_cast lt_of_lt_of_le (by decide : 0<2) hℓ) hn
  have hxx : ratio n ℓ ≤ x₀ := (div_le_iff₀ hn).mpr hadm.2.1
  have hxhalf : ratio n ℓ < 1/2 := hxx.trans_lt (hx₀min.trans_le (min_le_right _ _))
  have hx1 : ratio n ℓ ≤ 1 := by linarith
  have hscale : (ℓ : ℝ) < min (beta d ε) (1/2) * n :=
    lt_of_le_of_lt hadm.2.1 (mul_lt_mul_of_pos_right hx₀min hn)
  have hℓn : ℓ ≤ n := by
    have : (ℓ : ℝ) ≤ n := by
      have := (div_le_iff₀ hn).mp hx1
      simpa using this
    exact_mod_cast this
  have hK : (0 : ℝ) < Nat.choose n ℓ := by exact_mod_cast Nat.choose_pos hℓn
  have hA : 0 < logScale n ℓ := by
    unfold logScale
    apply Real.log_pos
    rw [lt_div_iff₀ hx]
    have : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith
  let r := repetition n ℓ Cstar
  let Ω := accepted φ H r
  by_cases hΩ : Ω.Nonempty
  swap
  · have hempty : Ω = ∅ := Finset.not_nonempty_iff_eq_empty.mp hΩ
    change (Ω.card : ℝ) / (H.card : ℝ)^(2*r) ≤ _
    rw [hempty, Finset.card_empty, Nat.cast_zero, zero_div]
    exact (Real.exp_pos _).le
  let Q := uniformOn Ω hΩ
  let E := Q.mean (fun X => energy ℓ (beta d ε) (flatten X))
  let M : ℝ := (Nat.choose n ℓ : ℝ)^(2*r)
  have hM : 0 < M := pow_pos hK _
  have hΩcard : (0 : ℝ) < Ω.card := by exact_mod_cast hΩ.card_pos
  have hcell : ∀ F, (cell Ω flatten F).Nonempty →
      ((cell Ω flatten F).card : ℝ) ≤ M * Real.exp (-c₀ * r * ratio n ℓ * energy ℓ (beta d ε) F) := by
    intro F hF
    obtain ⟨X,hX⟩ := hF
    have hX' : X ∈ Ω ∧ flatten X = F := by simpa only [cell, Finset.mem_filter] using hX
    have hXm := hX'.1
    have heq := hX'.2
    have hcross : CrossConsistent F := heq ▸ cross_flatten φ H X hXm
    exact hfixed n m φ hsrc hgap ℓ hℓ hscale H hH r F hcross
  have hc := (entropy_cell_counting Ω hΩ flatten
      (fun F => M * Real.exp (-c₀ * r * ratio n ℓ * energy ℓ (beta d ε) F)) hcell).2
      M (fun F => c₀ * r * ratio n ℓ * energy ℓ (beta d ε) F) (by intro F hF; simp [neg_mul])
  rw [mean_mul] at hc
  have he := (hent n m φ hsrc hgap ℓ hℓ hscale H hH r hΩ).2
  have hprob : acceptanceProbability φ H r = (Ω.card : ℝ) / M := by simp only [acceptanceProbability, hH]; rfl
  rw [hprob] at he
  have hlog : Real.log (1 / ((Ω.card : ℝ) / M)) = Real.log (M / Ω.card) := by congr 1; field_simp
  rw [hlog] at he
  have hE : beta d ε * n * ratio n ℓ ≤ E :=
    mean_floor Ω hΩ _ _ (fun X hX => energy_floor _ hβ hβ1 hn.le hx.le hx1 _)
  have hE0 : 0 ≤ E := le_trans (by positivity) hE
  have hr : Cstar * logScale n ℓ / ratio n ℓ ≤ (r : ℝ) := Nat.le_ceil _
  have hrx : Cstar * logScale n ℓ ≤ (r : ℝ) * ratio n ℓ := (div_le_iff₀ hx).mp hr
  have hcoef : logScale n ℓ ≤ c₀ * r * ratio n ℓ - C * logScale n ℓ := by
    have h := mul_le_mul_of_nonneg_left hrx hc₀.le
    have heq : c₀ * Cstar = C+1 := by dsimp [Cstar]; field_simp <;> ring
    nlinarith
  have hcE : logScale n ℓ * E ≤ (c₀ * r * ratio n ℓ - C * logScale n ℓ) * E :=
    mul_le_mul_of_nonneg_right hcoef hE0
  have hAE : logScale n ℓ * (beta d ε * n * ratio n ℓ) ≤ logScale n ℓ * E :=
    mul_le_mul_of_nonneg_left hE hA.le
  have hlogn : Real.log (n : ℝ) ≤ Real.log ((n : ℝ)+1) := Real.log_le_log hn (by linarith)
  have hlognp : 0 ≤ Real.log ((n : ℝ)+1) := Real.log_nonneg (by linarith)
  have hscale2 := hadm.2.2
  have hℓratio : (n : ℝ) * ratio n ℓ = ℓ := by unfold ratio; field_simp
  have hscale3 : 2 * D₂ * Real.log ((n : ℝ)+1) ≤ beta d ε * n * ratio n ℓ * logScale n ℓ := by
    have hs := mul_le_mul_of_nonneg_left hscale2 hβ.le
    have heq : beta d ε * C₀ = 2*(D₂+1) := by dsimp [C₀]; field_simp <;> ring
    rw [← mul_assoc, heq] at hs
    rw [mul_assoc (beta d ε) (n : ℝ) (ratio n ℓ), hℓratio]
    nlinarith
  have hL : beta d ε / 12 * n * ratio n ℓ * logScale n ℓ ≤ Real.log (M / Ω.card) := by
    change c₀ * (r : ℝ) * ratio n ℓ * E - (Q.map flatten).entropy ≤ Real.log (M / Ω.card) at hc
    change (Q.map flatten).entropy ≤ 5 * Real.log (M / Ω.card) + C * logScale n ℓ * E + D₂ * Real.log (n : ℝ) at he
    have := mul_le_mul_of_nonneg_left hlogn hD₂
    nlinarith
  rw [hprob]
  have hp : 0 < (Ω.card : ℝ) / M := div_pos hΩcard hM
  have hlogp : Real.log (M / Ω.card) = - Real.log ((Ω.card : ℝ) / M) := by
    rw [Real.log_div hM.ne' hΩcard.ne', Real.log_div hΩcard.ne' hM.ne']
    ring
  rw [hlogp] at hL
  rw [← Real.exp_log hp]
  apply Real.exp_le_exp.mpr
  linarith
