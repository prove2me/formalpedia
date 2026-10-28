-- Prove2me | solution 1 for BBBV.RandomPermutation.theorem_3_6
-- status  : ACCEPTED   (prove)
-- author  : @Victorized
-- created : 2026-10-26T06:40:14.896656+00:00
-- url     : https://prove2.me/submissions/e636079b-029b-4220-b9be-73a88757ea79

import Definitions.Def_BBBV_RandomPermutation_Chain
import Theorems.Thm_BBBV_RandomPermutation_theorem_3_1
import Theorems.Thm_BBBV_RandomPermutation_piChain_uniform
import Theorems.Thm_BBBV_RandomPermutation_prob_membership_differs
import Theorems.Thm_BBBV_RandomPermutation_expected_dist_le

noncomputable section
open Classical Finset BBBV.RandomPermutation
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace WentaoBBBVRoot

private lemma avg_indicator {n K : ℕ} (P : Ω n K → Prop) [DecidablePred P] :
    avg (fun ω => if P ω then (1 : ℝ) else 0) =
      ((univ.filter P).card : ℝ) / (Fintype.card (Ω n K) : ℝ) := by
  classical
  simp [avg, sum_ite]

private lemma avg_mono {n K : ℕ} (f g : Ω n K → ℝ) (h : ∀ ω, f ω ≤ g ω) :
    avg f ≤ avg g := by
  unfold avg
  exact div_le_div_of_nonneg_right (sum_le_sum fun ω _ => h ω) (Nat.cast_nonneg _)

private lemma avg_add {n K : ℕ} (f g : Ω n K → ℝ) :
    avg (fun ω => f ω + g ω) = avg f + avg g := by
  simp only [avg, sum_add_distrib, add_div]

private lemma avg_mul {n K : ℕ} (c : ℝ) (f : Ω n K → ℝ) :
    avg (fun ω => c * f ω) = c * avg f := by
  unfold avg
  rw [← mul_sum]
  ring

private lemma avg_uniform {n K : ℕ}
    (p : Ω n K → Equiv.Perm (BBBV.RandomOracle.Str n))
    (hp : ∀ σ, ((univ.filter fun ω => p ω = σ).card : ℝ) /
      (Fintype.card (Ω n K) : ℝ) =
        1 / (Fintype.card (Equiv.Perm (BBBV.RandomOracle.Str n)) : ℝ))
    (Q : Equiv.Perm (BBBV.RandomOracle.Str n) → Prop) [DecidablePred Q] :
    avg (fun ω => if Q (p ω) then (1 : ℝ) else 0) =
      ((univ.filter Q).card : ℝ) /
        (Fintype.card (Equiv.Perm (BBBV.RandomOracle.Str n)) : ℝ) := by
  classical
  let f := fun σ : Equiv.Perm (BBBV.RandomOracle.Str n) => if Q σ then (1 : ℝ) else 0
  have hsum : (∑ ω : Ω n K, f (p ω)) =
      ∑ σ : Equiv.Perm (BBBV.RandomOracle.Str n),
        ((univ.filter fun ω => p ω = σ).card : ℝ) * f σ := by
    have hh := sum_fiberwise_of_maps_to' (s := (univ : Finset (Ω n K)))
      (t := (univ : Finset (Equiv.Perm (BBBV.RandomOracle.Str n))))
      (g := p) (fun _ _ => mem_univ _) f
    simpa only [sum_const, nsmul_eq_mul] using hh.symm
  change (∑ ω : Ω n K, f (p ω)) / (Fintype.card (Ω n K) : ℝ) = _
  rw [hsum, sum_div]
  calc
    _ = ∑ σ : Equiv.Perm (BBBV.RandomOracle.Str n),
        (1 / (Fintype.card (Equiv.Perm (BBBV.RandomOracle.Str n)) : ℝ)) * f σ := by
      apply sum_congr rfl
      intro σ _
      rw [← div_mul_eq_mul_div, hp σ]
    _ = (∑ σ : Equiv.Perm (BBBV.RandomOracle.Str n), f σ) /
        (Fintype.card (Equiv.Perm (BBBV.RandomOracle.Str n)) : ℝ) := by
      rw [← mul_sum]
      ring
    _ = _ := by simp [f, sum_ite]

private lemma state_unit {X R W : Type} [Fintype X] [Fintype R] [Fintype W]
    [AddCommGroup R] {T : ℕ} (M : QueryAlg X R W T) (g : Fin T → X → R) (i : ℕ) :
    ‖state M g i‖ = 1 := by
  induction i with
  | zero => exact M.init_norm
  | succ i ih =>
    have hrec : state M g (i + 1) = if h : i < T then
        M.U ⟨i, h⟩ (oracleOp (g ⟨i, h⟩) (state M g i)) else state M g i := rfl
    rw [hrec]
    split_ifs <;> simp [ih]

private lemma acceptance_bound {X R W : Type} [Fintype X] [Fintype R] [Fintype W]
    [AddCommGroup R] {T : ℕ} (M : QueryAlg X R W T) (g h : Fin T → X → R) :
    |acceptProb M g - acceptProb M h| ≤ 4 * ‖final M g - final M h‖ := by
  classical
  unfold acceptProb
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ c ∈ M.accept, |‖(final M g) c‖ ^ 2 - ‖(final M h) c‖ ^ 2| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ c : BBBV.RandomOracle.Config X R W,
        |‖(final M g) c‖ ^ 2 - ‖(final M h) c‖ ^ 2| :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => abs_nonneg _)
    _ ≤ _ := theorem_3_1 _ _ (state_unit M g T) (state_unit M h T) _ le_rfl

private lemma pair_bound {n K T : ℕ} (hn : 0 < n) {W : Type} [Fintype W]
    (M : QueryAlg (BBBV.RandomOracle.Str n) (BBBV.RandomOracle.Str n) W T)
    (p q : Ω n K → Equiv.Perm (BBBV.RandomOracle.Str n))
    (hp : ∀ σ, ((univ.filter fun ω => p ω = σ).card : ℝ) /
      (Fintype.card (Ω n K) : ℝ) =
        1 / (Fintype.card (Equiv.Perm (BBBV.RandomOracle.Str n)) : ℝ))
    (hq : ∀ σ, ((univ.filter fun ω => q ω = σ).card : ℝ) /
      (Fintype.card (Ω n K) : ℝ) =
        1 / (Fintype.card (Equiv.Perm (BBBV.RandomOracle.Str n)) : ℝ))
    (hdiff : avg (fun ω => if
        ((firstBit hn ((p ω).symm (BBBV.RandomOracle.ones n)) = 1) ↔
          ¬ (firstBit hn ((q ω).symm (BBBV.RandomOracle.ones n)) = 1))
        then (1 : ℝ) else 0) = 1 / 2)
    (hdist : avg (fun ω => ‖final M (fun _ => ⇑(p ω)) -
        final M (fun _ => ⇑(q ω))‖) ≤ 1 / 50) :
    (1 / 8 : ℝ) ≤
      ((univ.filter fun σ : Equiv.Perm (BBBV.RandomOracle.Str n) =>
        ¬ Decides M (fun _ => ⇑σ)
          (firstBit hn (σ.symm (BBBV.RandomOracle.ones n)) = 1)).card : ℝ) /
        (Fintype.card (Equiv.Perm (BBBV.RandomOracle.Str n)) : ℝ) := by
  classical
  let b := fun σ : Equiv.Perm (BBBV.RandomOracle.Str n) =>
    firstBit hn (σ.symm (BBBV.RandomOracle.ones n)) = 1
  let fail : Equiv.Perm (BBBV.RandomOracle.Str n) → Prop :=
    fun σ => ¬ Decides M (fun _ => ⇑σ) (b σ)
  let R : ℝ := ((univ.filter fail).card : ℝ) /
    (Fintype.card (Equiv.Perm (BBBV.RandomOracle.Str n)) : ℝ)
  let I := fun ω : Ω n K => if b (p ω) ↔ ¬ b (q ω) then (1 : ℝ) else 0
  let Bp := fun ω : Ω n K => if fail (p ω) then (1 : ℝ) else 0
  let Bq := fun ω : Ω n K => if fail (q ω) then (1 : ℝ) else 0
  let d := fun ω : Ω n K => ‖final M (fun _ => ⇑(p ω)) - final M (fun _ => ⇑(q ω))‖
  have hBp : avg Bp = R := avg_uniform p hp fail
  have hBq : avg Bq = R := avg_uniform q hq fail
  have hI : avg I = 1 / 2 := hdiff
  have hpoint (ω : Ω n K) : (2 / 25 : ℝ) * I ω ≤
      (2 / 25 : ℝ) * (Bp ω + Bq ω) + d ω := by
    dsimp [I, Bp, Bq]
    by_cases hdiffω : b (p ω) ↔ ¬ b (q ω)
    · rw [if_pos hdiffω]
      by_cases hfp : fail (p ω)
      · simp only [if_pos hfp]
        split_ifs <;> dsimp [d] <;> nlinarith [norm_nonneg
          (final M (fun _ => ⇑(p ω)) - final M (fun _ => ⇑(q ω)))]
      · by_cases hfq : fail (q ω)
        · simp only [if_neg hfp, if_pos hfq]
          dsimp [d]
          nlinarith [norm_nonneg (final M (fun _ => ⇑(p ω)) - final M (fun _ => ⇑(q ω)))]
        · simp only [if_neg hfp, if_neg hfq]
          have hgoodp : Decides M (fun _ => ⇑(p ω)) (b (p ω)) := by simpa only [fail, not_not] using hfp
          have hgoodq : Decides M (fun _ => ⇑(q ω)) (b (q ω)) := by simpa only [fail, not_not] using hfq
          have hm := acceptance_bound M (fun _ => ⇑(p ω)) (fun _ => ⇑(q ω))
          change |acceptProb M (fun _ => ⇑(p ω)) - acceptProb M (fun _ => ⇑(q ω))| ≤ 4 * d ω at hm
          by_cases hbp : b (p ω)
          · have hbq : ¬ b (q ω) := hdiffω.mp hbp
            have hpacc := hgoodp.1 hbp
            have hqacc := hgoodq.2 hbq
            have hh := (le_abs_self _).trans hm
            linarith
          · have hbq : b (q ω) := by
              by_contra hh
              exact hbp (hdiffω.mpr hh)
            have hpacc := hgoodp.2 hbp
            have hqacc := hgoodq.1 hbq
            have hh := (neg_le_abs _).trans hm
            linarith
    · rw [if_neg hdiffω]
      split_ifs <;> dsimp [d] <;> nlinarith [norm_nonneg
        (final M (fun _ => ⇑(p ω)) - final M (fun _ => ⇑(q ω)))]
  have hmean : (2 / 25 : ℝ) * (1 / 2) ≤ (2 / 25 : ℝ) * (2 * R) + 1 / 50 := by
    calc
      _ = avg (fun ω => (2 / 25 : ℝ) * I ω) := by rw [avg_mul, hI]
      _ ≤ avg (fun ω => (2 / 25 : ℝ) * (Bp ω + Bq ω) + d ω) := avg_mono _ _ hpoint
      _ = (2 / 25 : ℝ) * (2 * R) + avg d := by
        rw [avg_add, avg_mul, avg_add, hBp, hBq]
        ring
      _ ≤ _ := by
        have hd : avg d ≤ 1 / 50 := hdist
        linarith
  change (1 / 8 : ℝ) ≤ R
  linarith

end WentaoBBBVRoot

open WentaoBBBVRoot

theorem solution (n : ℕ) (hn : 0 < n) (W : Type) [Fintype W] (T : ℕ)
    (hT : (T : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 3) / 100)
    (M : QueryAlg (BBBV.RandomOracle.Str n) (BBBV.RandomOracle.Str n) W T) :
    (1 / 8 : ℝ) ≤
      ((Finset.univ.filter fun A : Equiv.Perm (BBBV.RandomOracle.Str n) =>
          ¬ Decides M (fun _ => ⇑A) (firstBit hn (A.symm (BBBV.RandomOracle.ones n)) = 1)).card : ℝ) /
        (Fintype.card (Equiv.Perm (BBBV.RandomOracle.Str n)) : ℝ) := by
  classical
  by_cases ht : 1 ≤ T
  · apply pair_bound hn M (fun ω : Ω n T => piChain ω T)
      (fun ω : Ω n T => piChain ω (T - 1))
      (fun σ => (piChain_uniform T (by omega) σ).1)
      (fun σ => (piChain_uniform (T - 1) (by omega) σ).1)
    · rw [avg_indicator]
      exact prob_membership_differs hn ht
    · exact expected_dist_le M ht hT
  · have ht0 : T = 0 := by omega
    subst T
    apply pair_bound hn M (fun ω : Ω n 1 => piChain ω 1)
      (fun ω : Ω n 1 => piChain ω 0)
      (fun σ => (piChain_uniform 1 (by omega) σ).1)
      (fun σ => (piChain_uniform 0 (by omega) σ).1)
    · rw [avg_indicator]
      exact prob_membership_differs hn (by omega : 1 ≤ 1)
    · norm_num [avg, final, state]
