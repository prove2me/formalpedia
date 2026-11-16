-- Prove2me | solution 1 for DetANN.theorem_3_2_greedy
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-16T03:06:43.215649+00:00
-- url     : https://prove2.me/submissions/96d0064b-f9eb-4a5a-9e87-61031f8e11d7

import Mathlib
import Definitions.Def_DetANN_SignedBlocks
import Definitions.Def_DetANN_BalancedBlocks
import Definitions.Def_DetANN_SignChoice
import Theorems.Thm_DetANN_lemma_6_2
import Theorems.Thm_DetANN_expected_potential
import Theorems.Thm_DetANN_parseval_signed_blocks

open DetANN

namespace DetANNGreedyAux

/-! ### Averages -/

lemma avgOver_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (f : β → ℝ) :
    avgOver f = avgOver (f ∘ e) := by
  unfold avgOver
  rw [Fintype.card_congr e, Function.comp_def, e.sum_comp f]

lemma avgOver_prod_mul {α β : Type*} [Fintype α] [Fintype β] (f : α → ℝ) (g : β → ℝ) :
    avgOver (fun p : α × β => f p.1 * g p.2) = avgOver f * avgOver g := by
  unfold avgOver
  rw [Fintype.card_prod, Fintype.sum_prod_type, Nat.cast_mul, mul_inv]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  ring

lemma avgOver_sum {α ι : Type*} [Fintype α] (s : Finset ι) (f : ι → α → ℝ) :
    avgOver (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, avgOver (f i) := by
  unfold avgOver
  rw [Finset.sum_comm, Finset.mul_sum]

lemma avgOver_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    avgOver (fun a => c * f a) = c * avgOver f := by
  unfold avgOver
  rw [← Finset.mul_sum]; ring

lemma avgOver_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    avgOver (fun _ : α => c) = c := by
  unfold avgOver
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-! ### Item 4: the method of conditional expectations -/

/-- The conditional average of `f` given the partial assignment `(μ, u)`. -/
noncomputable def condAvg {L d : ℕ} (f : (Fin L → Fin d → Bool) → ℝ) (μ u : Fin L → Fin d → Bool) :
    ℝ :=
  avgOver fun ξ => f (completeSigns μ u ξ)

lemma complete_succ {L d : ℕ} (k : ℕ) (b : Bool) (u ξ : Fin L → Fin d → Bool) :
    completeSigns (prefixMask L d (k + 1)) (setSignAt k b u) ξ =
      completeSigns (prefixMask L d k) u (setSignAt k b ξ) := by
  funext ℓ r
  simp only [completeSigns, prefixMask, setSignAt, decide_eq_true_eq]
  by_cases e : (ℓ : ℕ) * d + r = k
  · simp [e]
  · have : ((ℓ : ℕ) * d + r < k + 1) ↔ ((ℓ : ℕ) * d + r < k) := by omega
    simp [e, this]

/-- Flip the sign at position `k`. -/
def flipAt {L d : ℕ} (k : ℕ) (ξ : Fin L → Fin d → Bool) : Fin L → Fin d → Bool :=
  fun ℓ r => if (ℓ : ℕ) * d + r = k then !ξ ℓ r else ξ ℓ r

lemma flipAt_invol {L d : ℕ} (k : ℕ) : Function.Involutive (flipAt (L := L) (d := d) k) := by
  intro ξ; funext ℓ r; simp only [flipAt]; split_ifs <;> simp

lemma pos_unique {L d : ℕ} {k : ℕ} {ℓ₀ ℓ : Fin L} {r₀ r : Fin d} (h₀ : (ℓ₀ : ℕ) * d + r₀ = k)
    (h : (ℓ : ℕ) * d + r = k) : ℓ = ℓ₀ ∧ r = r₀ := by
  have hr : (r : ℕ) < d := r.2
  have hr₀ : (r₀ : ℕ) < d := r₀.2
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hr
  have e1 : (ℓ : ℕ) = k / d := by
    rw [← h, Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hr, zero_add]
  have e2 : (ℓ₀ : ℕ) = k / d := by
    rw [← h₀, Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hr₀, zero_add]
  have e3 : (ℓ : ℕ) = ℓ₀ := e1.trans e2.symm
  refine ⟨Fin.ext e3, Fin.ext ?_⟩
  rw [e3] at h; omega

lemma pair_sum {L d : ℕ} (k : ℕ) (g : (Fin L → Fin d → Bool) → ℝ) (ξ : Fin L → Fin d → Bool) :
    g ξ + g (flipAt k ξ) = g (setSignAt k true ξ) + g (setSignAt k false ξ) := by
  by_cases hp : ∃ ℓ₀ : Fin L, ∃ r₀ : Fin d, (ℓ₀ : ℕ) * d + r₀ = k
  · obtain ⟨ℓ₀, r₀, h₀⟩ := hp
    have key : ∀ b : Bool, ξ ℓ₀ r₀ = b → setSignAt k b ξ = ξ ∧ setSignAt k (!b) ξ = flipAt k ξ := by
      intro b hb
      constructor <;> funext ℓ r <;> simp only [setSignAt, flipAt] <;> split_ifs with e
      · obtain ⟨rfl, rfl⟩ := pos_unique h₀ e; exact hb.symm
      · rfl
      · obtain ⟨rfl, rfl⟩ := pos_unique h₀ e; rw [hb]
      · rfl
    cases hb : ξ ℓ₀ r₀
    · obtain ⟨e1, e2⟩ := key false hb
      simp only [Bool.not_false] at e2
      rw [e1, e2]; ring
    · obtain ⟨e1, e2⟩ := key true hb
      simp only [Bool.not_true] at e2
      rw [e1, e2]
  · push Not at hp
    have e : ∀ b : Bool, setSignAt k b ξ = ξ := fun b => by
      funext ℓ r; simp [setSignAt, hp ℓ r]
    have ef : flipAt k ξ = ξ := by funext ℓ r; simp [flipAt, hp ℓ r]
    rw [e, e, ef]

lemma avg_split {L d : ℕ} (k : ℕ) (g : (Fin L → Fin d → Bool) → ℝ) :
    avgOver g = (avgOver (fun ξ => g (setSignAt k true ξ)) +
      avgOver (fun ξ => g (setSignAt k false ξ))) / 2 := by
  have hflip : ∑ ξ, g (flipAt k ξ) = ∑ ξ, g ξ :=
    Equiv.sum_comp (flipAt_invol (L := L) (d := d) k).toPerm g
  have hsum : 2 * ∑ ξ, g ξ = ∑ ξ, g (setSignAt k true ξ) + ∑ ξ, g (setSignAt k false ξ) := by
    rw [two_mul]
    nth_rewrite 2 [← hflip]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ξ _ => pair_sum k g ξ
  unfold avgOver
  rw [← mul_add, ← hsum]; ring

lemma condAvg_step {L d : ℕ} (f : (Fin L → Fin d → Bool) → ℝ) (k : ℕ) (u : Fin L → Fin d → Bool) :
    condAvg f (prefixMask L d k) u =
      (condAvg f (prefixMask L d (k + 1)) (setSignAt k true u) +
        condAvg f (prefixMask L d (k + 1)) (setSignAt k false u)) / 2 := by
  unfold condAvg
  simp_rw [complete_succ]
  exact avg_split k _

/-- **Method of conditional expectations.** If the score `F` is the conditional average of `f`,
the greedy choice never increases it, so the final assignment is at most the average of `f`. -/
theorem greedy_le_avg {L d : ℕ} (f : (Fin L → Fin d → Bool) → ℝ)
    (F : (Fin L → Fin d → Bool) → (Fin L → Fin d → Bool) → ℝ) (hF : ∀ μ u, F μ u = condAvg f μ u) :
    f (greedySigns F (L * d)) ≤ avgOver f := by
  have inv : ∀ k, condAvg f (prefixMask L d k) (greedySigns F k) ≤ avgOver f := by
    intro k
    induction k with
    | zero =>
      have : ∀ u ξ : Fin L → Fin d → Bool, completeSigns (prefixMask L d 0) u ξ = ξ := by
        intro u ξ; funext ℓ r; simp [completeSigns, prefixMask]
      simp only [condAvg, this, le_refl]
    | succ k ih =>
      have hs := condAvg_step f k (greedySigns F k)
      simp only [greedySigns]
      rw [hF, hF]
      split_ifs with hle
      · linarith
      · push Not at hle; linarith
  have hfull : ∀ u ξ : Fin L → Fin d → Bool, completeSigns (prefixMask L d (L * d)) u ξ = u := by
    intro u ξ; funext ℓ r
    have : (ℓ : ℕ) * d + r < L * d := by
      have h1 : (ℓ : ℕ) + 1 ≤ L := ℓ.2
      have h2 : (r : ℕ) < d := r.2
      nlinarith
    simp [completeSigns, prefixMask, this]
  have hfin := inv (L * d)
  rw [condAvg] at hfin
  simp_rw [hfull] at hfin
  have hne : Nonempty (Fin L → Fin d → Bool) := ⟨fun _ _ => false⟩
  rwa [avgOver_const] at hfin

end DetANNGreedyAux

open DetANNGreedyAux in
theorem solution :
    ∃ C₀s : ℝ, 0 < C₀s ∧ ∀ C₀ : ℝ, C₀s ≤ C₀ → ∀ d : ℕ, 1 ≤ d →
      ∀ h : Matrix (Fin d) (Fin d) ℝ, (∀ j r, h j r = 1 ∨ h j r = -1) →
        h.transpose * h = (d : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) →
        ∀ τ : ℝ, 0 < τ → τ < 1 →
          ∀ P D : Finset (EuclideanSpace ℝ (Fin d)), (∀ v ∈ D, v ≠ 0) →
            (∀ x ∈ P, ∀ y ∈ P, x ≠ y → x - y ∈ D ∨ y - x ∈ D) → 1 ≤ D.card →
            potential h (numReps C₀ τ (momentOrder D.card d))
                (greedySigns (lemma62Expr h (numReps C₀ τ (momentOrder D.card d)) τ
                  (momentOrder D.card d) D) (numReps C₀ τ (momentOrder D.card d) * d))
                τ (momentOrder D.card d) D ≤ 1 / 8 ∧
              (∀ v ∈ D, ∀ j : Fin d,
                |(d : ℝ) * ‖signedBlocks h (numReps C₀ τ (momentOrder D.card d))
                    (greedySigns (lemma62Expr h (numReps C₀ τ (momentOrder D.card d)) τ
                      (momentOrder D.card d) D) (numReps C₀ τ (momentOrder D.card d) * d)) j v‖ ^ 2
                    - ‖v‖ ^ 2| < τ * ‖v‖ ^ 2) ∧
              IsBalancedBlockSystem τ P (signedBlocks h (numReps C₀ τ (momentOrder D.card d))
                (greedySigns (lemma62Expr h (numReps C₀ τ (momentOrder D.card d)) τ
                  (momentOrder D.card d) D) (numReps C₀ τ (momentOrder D.card d) * d))) := by
  obtain ⟨C, hC, C₀s, hC₀s, hEP⟩ := expected_potential
  refine ⟨C₀s, hC₀s, ?_⟩
  intro C₀ hC₀ d hd h hpm hh τ hτ0 hτ1 P D hD hdiff hN
  set p₀ := momentOrder D.card d with hp₀def
  set L := numReps C₀ τ p₀ with hLdef
  set ξ := greedySigns (lemma62Expr h L τ p₀ D) (L * d) with hξdef
  obtain ⟨e1, e2, e3⟩ := hEP C₀ hC₀ d hd h hpm τ hτ0 hτ1 D hD hN
  have havg : avgOver (fun ξ : Fin L → Fin d → Bool => potential h L ξ τ p₀ D) ≤ 1 / 8 :=
    e1.trans (e2.trans e3)
  -- p₀ ≥ 1 and L ≥ 1 (needed for Parseval)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hNR : (1 : ℝ) ≤ D.card := by exact_mod_cast hN
  have hp₀pos : 1 ≤ p₀ := by
    rw [hp₀def, momentOrder, Nat.one_le_ceil_iff]
    have : (1 : ℝ) ≤ D.card * d := one_le_mul_of_one_le_of_one_le hNR (by exact_mod_cast hd)
    exact Real.logb_pos (by norm_num) (by push_cast; nlinarith)
  have hL1 : 1 ≤ L := by
    rw [hLdef, numReps, Nat.one_le_ceil_iff]
    have hp : (0 : ℝ) < p₀ := by exact_mod_cast hp₀pos
    exact mul_pos (mul_pos (lt_of_lt_of_le hC₀s hC₀) (by positivity)) hp
  -- the greedy choice, driven by the Lemma 6.2 expression, ends below the average
  have hξ : potential h L ξ τ p₀ D ≤ 1 / 8 := by
    refine le_trans (greedy_le_avg (fun ξ => potential h L ξ τ p₀ D) _ ?_) havg
    intro μ u
    rw [← lemma_6_2 hd h L hL1 τ p₀ D μ u]
    rfl
  -- every summand of Φ is at most Φ, hence < 1, which is the balance on 𝒟
  have hbalD : ∀ v ∈ D, ∀ j : Fin d,
      |(d : ℝ) * ‖signedBlocks h L ξ j v‖ ^ 2 - ‖v‖ ^ 2| < τ * ‖v‖ ^ 2 := by
    intro v hv j
    have hv0 : 0 < ‖v‖ ^ 2 := by have := norm_pos_iff.2 (hD v hv); positivity
    have hnn : ∀ w ∈ D, ∀ i ∈ (Finset.univ : Finset (Fin d)),
        0 ≤ (((d : ℝ) * ‖signedBlocks h L ξ i w‖ ^ 2 - ‖w‖ ^ 2) / (τ * ‖w‖ ^ 2)) ^ (2 * p₀) :=
      fun w _ i _ => (even_two_mul p₀).pow_nonneg _
    have hterm : (((d : ℝ) * ‖signedBlocks h L ξ j v‖ ^ 2 - ‖v‖ ^ 2) / (τ * ‖v‖ ^ 2)) ^ (2 * p₀)
        ≤ potential h L ξ τ p₀ D := by
      unfold potential
      calc _ ≤ ∑ i : Fin d,
            (((d : ℝ) * ‖signedBlocks h L ξ i v‖ ^ 2 - ‖v‖ ^ 2) / (τ * ‖v‖ ^ 2)) ^ (2 * p₀) :=
            Finset.single_le_sum (hnn v hv) (Finset.mem_univ j)
        _ ≤ _ := Finset.single_le_sum (f := fun w => ∑ i : Fin d,
              (((d : ℝ) * ‖signedBlocks h L ξ i w‖ ^ 2 - ‖w‖ ^ 2) / (τ * ‖w‖ ^ 2)) ^ (2 * p₀))
            (fun w hw => Finset.sum_nonneg (hnn w hw)) hv
    set t := ((d : ℝ) * ‖signedBlocks h L ξ j v‖ ^ 2 - ‖v‖ ^ 2) / (τ * ‖v‖ ^ 2)
    have ht : |t| < 1 := by
      by_contra hge
      push_neg at hge
      have : 1 ≤ t ^ (2 * p₀) := by
        rw [← (even_two_mul p₀).pow_abs]; exact one_le_pow₀ hge
      linarith
    have hpos : 0 < τ * ‖v‖ ^ 2 := mul_pos hτ0 hv0
    rw [abs_div, abs_of_pos hpos, div_lt_one hpos] at ht
    exact ht
  refine ⟨hξ, hbalD, ?_, ?_⟩
  · -- Parseval holds for every sign assignment
    intro z
    exact (parseval_signed_blocks h hh L hL1 ξ z).2
  · -- balance on all pairs of points of P
    intro x hx y hy i
    by_cases hxy : x = y
    · subst hxy; simp
    · have key : ∀ w ∈ D, (1 - τ) / d * ‖w‖ ^ 2 ≤ ‖signedBlocks h L ξ i w‖ ^ 2 ∧
          ‖signedBlocks h L ξ i w‖ ^ 2 ≤ (1 + τ) / d * ‖w‖ ^ 2 := by
        intro w hw
        have hb := hbalD w hw i
        rw [abs_lt] at hb
        constructor
        · rw [div_mul_eq_mul_div, div_le_iff₀ hdR]; linarith
        · rw [div_mul_eq_mul_div, le_div_iff₀ hdR]; linarith
      rcases hdiff x hx y hy hxy with hm | hm
      · exact key _ hm
      · have h1 : ‖signedBlocks h L ξ i (x - y)‖ = ‖signedBlocks h L ξ i (y - x)‖ := by
          rw [map_sub, map_sub, norm_sub_rev]
        have h2 : ‖x - y‖ = ‖y - x‖ := norm_sub_rev x y
        rw [h1, h2]
        exact key _ hm
