-- Prove2me | solution 1 for GaoCascadePricing.UCB.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T09:06:12.191386+00:00
-- url     : https://prove2.me/submissions/df1df589-521a-4c89-ac77-bd62e9a0db66

import Mathlib
import Definitions.Def_GaoCascadePricing_UCB_Market
open scoped BigOperators
namespace GCT
open GaoCascadePricing.UCB

lemma nat_bound (c u : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hu : ∀ n, 0 ≤ u n) (hcu : ∀ n, c n + u n ≤ 1)
    (a : ℕ) : ∀ b, a ≤ b →
    ∑ j ∈ Finset.Ico a b, (∏ l ∈ Finset.Ico a j, c l) * u j ≤ 1 - ∏ l ∈ Finset.Ico a b, c l := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, Finset.prod_Ico_succ_top hab]
    have hp : 0 ≤ ∏ l ∈ Finset.Ico a b, c l := Finset.prod_nonneg fun l _ => hc l
    have := hcu b
    nlinarith [mul_nonneg hp (hu b)]

lemma fin_bound {J : ℕ} (c u : Fin J → ℝ) (hc : ∀ n, 0 ≤ c n) (hu : ∀ n, 0 ≤ u n)
    (hcu : ∀ n, c n + u n ≤ 1) (i : Fin J) :
    ∑ j ∈ Finset.Ioi i, (∏ l ∈ Finset.Ioo i j, c l) * u j ≤ 1 := by
  let cN : ℕ → ℝ := fun n => if h : n < J then c ⟨n, h⟩ else 0
  let uN : ℕ → ℝ := fun n => if h : n < J then u ⟨n, h⟩ else 0
  have hcN : ∀ n, 0 ≤ cN n := fun n => by
    by_cases h : n < J <;> simp [cN, h, hc]
  have huN : ∀ n, 0 ≤ uN n := fun n => by
    by_cases h : n < J <;> simp [uN, h, hu]
  have hcuN : ∀ n, cN n + uN n ≤ 1 := fun n => by
    by_cases h : n < J
    · simpa [cN, uN, h] using hcu ⟨n, h⟩
    · simp [cN, uN, h]
  have key := nat_bound cN uN hcN huN hcuN (i.val + 1) J (by omega)
  have h1 : ∑ j ∈ Finset.Ioi i, (∏ l ∈ Finset.Ioo i j, c l) * u j =
      ∑ j ∈ Finset.Ioi i, (∏ l ∈ Finset.Ico (i.val+1) j.val, cN l) * uN j.val := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hprod : ∏ l ∈ Finset.Ioo i j, c l = ∏ l ∈ Finset.Ico (i.val+1) j.val, cN l := by
      have e1 : ∏ l ∈ Finset.Ioo i j, c l = ∏ l ∈ Finset.Ioo i j, cN l.val :=
        Finset.prod_congr rfl fun l _ => by simp [cN, l.isLt]
      rw [e1]
      have := Finset.prod_map (Finset.Ioo i j) Fin.valEmbedding cN
      rw [Fin.map_valEmbedding_Ioo] at this
      exact this.symm
    rw [hprod]; simp [uN, j.isLt]
  rw [h1]
  have h2 : ∑ j ∈ Finset.Ioi i, (∏ l ∈ Finset.Ico (i.val+1) j.val, cN l) * uN j.val =
      ∑ n ∈ Finset.Ico (i.val+1) J, (∏ l ∈ Finset.Ico (i.val+1) n, cN l) * uN n := by
    have := Finset.sum_map (Finset.Ioi i) Fin.valEmbedding
      (fun n => (∏ l ∈ Finset.Ico (i.val+1) n, cN l) * uN n)
    rw [Fin.map_valEmbedding_Ioi] at this
    exact this.symm
  rw [h2]
  have : 0 ≤ ∏ l ∈ Finset.Ico (i.val+1) J, cN l := Finset.prod_nonneg fun l _ => hcN l
  linarith

lemma prod_split {J : ℕ} (f : Fin J → ℝ) (i j : Fin J) (hij : i < j) :
    ∏ l ∈ Finset.Iio j, f l = (∏ l ∈ Finset.Iio i, f l) * f i * ∏ l ∈ Finset.Ioo i j, f l := by
  have h : Finset.Iio j = Finset.Iio i ∪ ({i} ∪ Finset.Ioo i j) := by
    ext x
    simp only [Finset.mem_Iio, Finset.mem_union, Finset.mem_singleton, Finset.mem_Ioo, Fin.lt_def, Fin.ext_iff] at *
    omega
  rw [h, Finset.prod_union, Finset.prod_union, Finset.prod_singleton, mul_assoc]
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_Ioo, Finset.mem_singleton, Fin.lt_def, Fin.ext_iff] at *
    omega
  · rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_Iio, Finset.mem_union, Finset.mem_singleton, Finset.mem_Ioo, Fin.lt_def, Fin.ext_iff] at *
    omega

lemma caseB (α γ ζ pr P S Δ : ℝ) (ha0 : 0 ≤ α) (ha1 : α ≤ 1) (hg0 : 0 ≤ γ) (hg1 : γ ≤ 1)
    (hz0 : 0 ≤ ζ) (hz1 : ζ ≤ 1) (hp0 : 0 ≤ pr) (hpP : pr ≤ P) (hS0 : 0 ≤ S) (hSP : S ≤ P) :
    |Δ * α * pr + (Δ * (-γ + (1-α)*ζ)) * S| ≤ P * |Δ| := by
  have : Δ * α * pr + (Δ * (-γ + (1-α)*ζ)) * S = Δ * (α * pr + (-γ + (1-α)*ζ) * S) := by ring
  rw [this, abs_mul, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  rw [abs_le]
  have h1 : α * pr ≤ α * P := mul_le_mul_of_nonneg_left hpP ha0
  have h2 : (1-α) * ζ * S ≤ (1-α) * P := by
    have : ζ * S ≤ P := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 this)]
  have h3 : γ * S ≤ P := by nlinarith
  have h4 : 0 ≤ α * pr := mul_nonneg ha0 hp0
  have h5 : 0 ≤ (1-α) * ζ * S := mul_nonneg (mul_nonneg (sub_nonneg.2 ha1) hz0) hS0
  constructor <;> nlinarith

lemma caseA (β ζ pr P S Δ : ℝ) (hb0 : 0 ≤ β) (hb1 : β ≤ 1)
    (hz0 : 0 ≤ ζ) (hz1 : ζ ≤ 1) (hp0 : 0 ≤ pr) (hpP : pr ≤ P) (hS0 : 0 ≤ S) (hSP : S ≤ P) :
    |Δ * β * pr + (Δ * (-(β * ζ))) * S| ≤ P * |Δ| := by
  have : Δ * β * pr + (Δ * (-(β * ζ))) * S = Δ * (β * (pr - ζ * S)) := by ring
  rw [this, abs_mul, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  rw [abs_mul, abs_of_nonneg hb0]
  have h1 : |pr - ζ * S| ≤ P := by
    rw [abs_le]
    have : ζ * S ≤ S := by nlinarith
    constructor <;> nlinarith
  calc β * |pr - ζ * S| ≤ 1 * P := mul_le_mul hb1 h1 (abs_nonneg _) zero_le_one
    _ = P := one_mul P

lemma caseG (β S P Δ : ℝ) (hb0 : 0 ≤ β) (hb1 : β ≤ 1) (hS0 : 0 ≤ S) (hSP : S ≤ P) :
    |(Δ * (1 - β)) * S| ≤ P * |Δ| := by
  rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.2 hb1), abs_of_nonneg hS0]
  have : (1 - β) * S ≤ P := by nlinarith
  nlinarith [abs_nonneg Δ]

lemma caseZ (β α S P Δ : ℝ) (hb0 : 0 ≤ β) (hb1 : β ≤ 1) (ha0 : 0 ≤ α) (ha1 : α ≤ 1)
    (hS0 : 0 ≤ S) (hSP : S ≤ P) :
    |(Δ * (β * (1 - α))) * S| ≤ P * |Δ| := by
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hb0, abs_of_nonneg (sub_nonneg.2 ha1), abs_of_nonneg hS0]
  have h1 : β * (1 - α) ≤ 1 := by nlinarith
  have h2 : β * (1 - α) * S ≤ P := by nlinarith [mul_nonneg hb0 (sub_nonneg.2 ha1)]
  nlinarith [abs_nonneg Δ]

lemma rev_diff {J K : ℕ} (M : Market J K) (θ θ' : Cascade J K) (p : Action J K) (i : Fin J)
    (hother : ∀ j, j ≠ i →
      (∀ k, θ.beta j k = θ'.beta j k ∧ θ.alpha j k = θ'.alpha j k) ∧
      θ.gamma j = θ'.gamma j ∧ θ.zeta j = θ'.zeta j) :
    revenue M θ p - revenue M θ' p =
      reach θ' p i * (θ.beta i (p i) * θ.alpha i (p i) * M.price (p i)
          - θ'.beta i (p i) * θ'.alpha i (p i) * M.price (p i))
      + reach θ' p i * (continuation θ p i - continuation θ' p i) *
        ∑ j ∈ Finset.Ioi i, (∏ l ∈ Finset.Ioo i j, continuation θ' p l) *
          (θ'.beta j (p j) * θ'.alpha j (p j)) * M.price (p j) := by
  have hcont : ∀ l, l ≠ i → continuation θ p l = continuation θ' p l := by
    intro l hl
    obtain ⟨h1, h2, h3⟩ := hother l hl
    unfold continuation
    rw [(h1 (p l)).1, (h1 (p l)).2, h2, h3]
  have hb : ∀ l, l ≠ i → θ.beta l (p l) = θ'.beta l (p l) := fun l hl => ((hother l hl).1 (p l)).1
  have ha : ∀ l, l ≠ i → θ.alpha l (p l) = θ'.alpha l (p l) := fun l hl => ((hother l hl).1 (p l)).2
  have hlt : ∀ j, j < i → reach θ p j = reach θ' p j := by
    intro j hj
    unfold reach
    refine Finset.prod_congr rfl fun l hl => hcont l ?_
    simp only [Finset.mem_Iio] at hl
    exact ne_of_lt (lt_trans hl hj)
  have hmid : ∀ j, i < j → reach θ p j = reach θ p i * continuation θ p i * ∏ l ∈ Finset.Ioo i j, continuation θ' p l := by
    intro j hij
    unfold reach
    rw [prod_split _ i j hij]
    congr 1
    refine Finset.prod_congr rfl fun l hl => hcont l ?_
    simp only [Finset.mem_Ioo] at hl
    exact ne_of_gt hl.1
  have hmid' : ∀ j, i < j → reach θ' p j = reach θ' p i * continuation θ' p i * ∏ l ∈ Finset.Ioo i j, continuation θ' p l := by
    intro j hij
    unfold reach
    exact prod_split _ i j hij
  have hri : reach θ p i = reach θ' p i := by
    unfold reach
    exact Finset.prod_congr rfl fun l hl => hcont l (by simp only [Finset.mem_Iio] at hl; exact ne_of_lt hl)
  unfold revenue
  rw [← Finset.sum_sub_distrib]
  have hpt : ∀ j, reach θ p j * θ.beta j (p j) * θ.alpha j (p j) * M.price (p j) -
      reach θ' p j * θ'.beta j (p j) * θ'.alpha j (p j) * M.price (p j) =
      (if j = i then reach θ' p i * (θ.beta i (p i) * θ.alpha i (p i) * M.price (p i)
          - θ'.beta i (p i) * θ'.alpha i (p i) * M.price (p i)) else 0) +
      (if i < j then reach θ' p i * (continuation θ p i - continuation θ' p i) *
        ((∏ l ∈ Finset.Ioo i j, continuation θ' p l) *
          (θ'.beta j (p j) * θ'.alpha j (p j)) * M.price (p j)) else 0) := by
    intro j
    rcases lt_trichotomy j i with h | h | h
    · rw [hlt j h, hb j (ne_of_lt h), ha j (ne_of_lt h)]
      simp [ne_of_lt h, not_lt.2 h.le]
    · subst h
      simp [hri]
      ring
    · have hne : j ≠ i := ne_of_gt h
      rw [hmid j h, hmid' j h, hb j hne, ha j hne]
      simp [hne, h]
      rw [hri]
      ring
  rw [Finset.sum_congr rfl fun j _ => hpt j, Finset.sum_add_distrib]
  congr 1
  · simp
  · rw [Finset.mul_sum, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext j; simp

end GCT

open GaoCascadePricing.UCB in
theorem step_one {J K : ℕ} (M : Market J K)
    (θ θ' : Cascade J K) (hθ : θ.Valid) (hθ' : θ'.Valid)
    (p : Action J K) (i : Fin J) (a : Fin 4)
    (hother : ∀ j, j ≠ i →
      (∀ k, θ.beta j k = θ'.beta j k ∧ θ.alpha j k = θ'.alpha j k) ∧
      θ.gamma j = θ'.gamma j ∧ θ.zeta j = θ'.zeta j)
    (hsame : ∀ b : Fin 4, b ≠ a → parameter θ p i b = parameter θ' p i b)
    (hdiff : parameter θ p i a ≠ parameter θ' p i a) :
    |revenue M θ p - revenue M θ' p| ≤
      priceNorm M p * reach θ' p i * |parameter θ p i a - parameter θ' p i a| := by
  obtain ⟨hb1', ha1', hg1', hz1', -⟩ := hθ'
  obtain ⟨hb1, ha1, hg1, hz1, -⟩ := hθ
  set P := priceNorm M p with hP
  have hpr : ∀ j, M.price (p j) ≤ P := by
    intro j
    have : |M.price (p j)| ≤ P := le_csSup (Set.finite_range _).bddAbove ⟨j, rfl⟩
    rwa [abs_of_nonneg (M.price_nonneg _)] at this
  have hprnn : ∀ j, 0 ≤ M.price (p j) := fun j => M.price_nonneg _
  have hc0 : ∀ j, 0 ≤ continuation θ' p j := fun j => by
    have := hb1' j (p j); have := hg1' j; have := hz1' j; have := ha1' j (p j)
    simp only [Set.mem_Icc] at *
    unfold continuation
    have : 0 ≤ (1 - θ'.beta j (p j)) * θ'.gamma j := mul_nonneg (by linarith) (by linarith)
    have : 0 ≤ θ'.beta j (p j) * (1 - θ'.alpha j (p j)) * θ'.zeta j :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    linarith
  have hu0 : ∀ j, 0 ≤ θ'.beta j (p j) * θ'.alpha j (p j) := fun j =>
    mul_nonneg (hb1' j (p j)).1 (ha1' j (p j)).1
  have hcu : ∀ j, continuation θ' p j + θ'.beta j (p j) * θ'.alpha j (p j) ≤ 1 := fun j => by
    have h1 := hb1' j (p j); have h2 := hg1' j; have h3 := hz1' j; have h4 := ha1' j (p j)
    simp only [Set.mem_Icc] at h1 h2 h3 h4
    unfold continuation
    have : (1 - θ'.beta j (p j)) * θ'.gamma j ≤ (1 - θ'.beta j (p j)) :=
      mul_le_of_le_one_right (by linarith) h2.2
    have : θ'.beta j (p j) * (1 - θ'.alpha j (p j)) * θ'.zeta j ≤ θ'.beta j (p j) * (1 - θ'.alpha j (p j)) :=
      mul_le_of_le_one_right (mul_nonneg h1.1 (by linarith)) h3.2
    nlinarith
  set S := ∑ j ∈ Finset.Ioi i, (∏ l ∈ Finset.Ioo i j, continuation θ' p l) *
          (θ'.beta j (p j) * θ'.alpha j (p j)) * M.price (p j) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Finset.prod_nonneg fun l _ => hc0 l) (hu0 j)) (hprnn j)
  have hSP : S ≤ P := by
    have h1 : S ≤ ∑ j ∈ Finset.Ioi i, ((∏ l ∈ Finset.Ioo i j, continuation θ' p l) *
          (θ'.beta j (p j) * θ'.alpha j (p j))) * P :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hpr j)
        (mul_nonneg (Finset.prod_nonneg fun l _ => hc0 l) (hu0 j))
    rw [← Finset.sum_mul] at h1
    have h2 := GCT.fin_bound (fun l => continuation θ' p l) (fun j => θ'.beta j (p j) * θ'.alpha j (p j))
      hc0 hu0 hcu i
    have hP0 : 0 ≤ P := le_trans (hprnn i) (hpr i)
    nlinarith
  have hr : 0 ≤ reach θ' p i := Finset.prod_nonneg fun l _ => hc0 l
  have hP0 : 0 ≤ P := le_trans (hprnn i) (hpr i)
  rw [GCT.rev_diff M θ θ' p i hother]
  have e : ∀ X Y : ℝ, reach θ' p i * X + reach θ' p i * Y * S = reach θ' p i * (X + Y * S) := by
    intro X Y; ring
  rw [e]
  have fin : ∀ Δ : ℝ, ∀ X Y : ℝ, |X + Y * S| ≤ P * |Δ| →
      |reach θ' p i * (X + Y * S)| ≤ P * reach θ' p i * |Δ| := by
    intro Δ X Y h
    rw [abs_mul, abs_of_nonneg hr]
    nlinarith
  have hbb := hb1 i (p i); have hbb' := hb1' i (p i)
  have haa := ha1 i (p i); have haa' := ha1' i (p i)
  have hgg := hg1 i; have hgg' := hg1' i
  have hzz := hz1 i; have hzz' := hz1' i
  simp only [Set.mem_Icc] at hbb hbb' haa haa' hgg hgg' hzz hzz'
  have hs1 : (1:Fin 4) ≠ a → θ.alpha i (p i) = θ'.alpha i (p i) := fun h => by
    simpa [parameter] using hsame 1 h
  have hs2 : (2:Fin 4) ≠ a → θ.gamma i = θ'.gamma i := fun h => by
    simpa [parameter] using hsame 2 h
  have hs3 : (3:Fin 4) ≠ a → θ.zeta i = θ'.zeta i := fun h => by
    simpa [parameter] using hsame 3 h
  have hs0 : (0:Fin 4) ≠ a → θ.beta i (p i) = θ'.beta i (p i) := fun h => by
    simpa [parameter] using hsame 0 h
  fin_cases a
  · have e1 := hs1 (by decide); have e2 := hs2 (by decide); have e3 := hs3 (by decide)
    simp only [parameter] at *
    simp only [Fin.zero_eta, if_true, one_ne_zero, if_false] at hdiff ⊢
    unfold continuation
    rw [e1, e2, e3]
    apply fin (θ.beta i (p i) - θ'.beta i (p i))
    have := GCT.caseB (θ'.alpha i (p i)) (θ'.gamma i) (θ'.zeta i) (M.price (p i)) P S
      (θ.beta i (p i) - θ'.beta i (p i)) haa'.1 haa'.2 hgg'.1 hgg'.2 hzz'.1 hzz'.2 (hprnn i) (hpr i) hS0 hSP
    convert this using 2
    ring
  · have e0 := hs0 (by decide); have e2 := hs2 (by decide); have e3 := hs3 (by decide)
    simp only [parameter] at *
    simp only [Fin.mk_one, if_true, one_ne_zero, if_false] at hdiff ⊢
    unfold continuation
    rw [e0, e2, e3]
    apply fin (θ.alpha i (p i) - θ'.alpha i (p i))
    have := GCT.caseA (θ'.beta i (p i)) (θ'.zeta i) (M.price (p i)) P S
      (θ.alpha i (p i) - θ'.alpha i (p i)) hbb'.1 hbb'.2 hzz'.1 hzz'.2 (hprnn i) (hpr i) hS0 hSP
    convert this using 2
    ring
  · have e0 := hs0 (by decide); have e1 := hs1 (by decide); have e3 := hs3 (by decide)
    simp only [parameter] at *
    simp only [Fin.reduceFinMk, Fin.reduceEq, if_true, if_false] at hdiff ⊢
    unfold continuation
    rw [e0, e1, e3]
    apply fin (θ.gamma i - θ'.gamma i)
    have := GCT.caseG (θ'.beta i (p i)) S P (θ.gamma i - θ'.gamma i) hbb'.1 hbb'.2 hS0 hSP
    convert this using 2
    ring
  · have e0 := hs0 (by decide); have e1 := hs1 (by decide); have e2 := hs2 (by decide)
    simp only [parameter] at *
    simp only [Fin.reduceFinMk, Fin.reduceEq, if_true, if_false] at hdiff ⊢
    unfold continuation
    rw [e0, e1, e2]
    apply fin (θ.zeta i - θ'.zeta i)
    have := GCT.caseZ (θ'.beta i (p i)) (θ'.alpha i (p i)) S P (θ.zeta i - θ'.zeta i) hbb'.1 hbb'.2 haa'.1 haa'.2 hS0 hSP
    convert this using 2
    ring

open GaoCascadePricing.UCB

namespace GCT

lemma rev_congr {J K : ℕ} (M : Market J K) (X Y : Cascade J K) (p : Action J K)
    (h1 : ∀ j, X.beta j (p j) = Y.beta j (p j)) (h2 : ∀ j, X.alpha j (p j) = Y.alpha j (p j))
    (h3 : ∀ j, X.gamma j = Y.gamma j) (h4 : ∀ j, X.zeta j = Y.zeta j) :
    revenue M X p = revenue M Y p := by
  simp only [revenue, reach, continuation, h1, h2, h3, h4]

def Agree {J K : ℕ} (A B : Cascade J K) (i : Fin J) : Prop :=
  ∀ j, j ≠ i → (∀ k, A.beta j k = B.beta j k ∧ A.alpha j k = B.alpha j k) ∧
      A.gamma j = B.gamma j ∧ A.zeta j = B.zeta j

lemma reach_agree {J K : ℕ} (A B : Cascade J K) (p : Action J K) (i : Fin J) (h : Agree A B i) :
    reach A p i = reach B p i := by
  unfold reach
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := ne_of_lt (Finset.mem_Iio.1 hj)
  obtain ⟨h1, h2, h3⟩ := h j hji
  simp only [continuation, (h1 (p j)).1, (h1 (p j)).2, h2, h3]

lemma step {J K : ℕ} (M : Market J K) (X Y : Cascade J K) (hX : X.Valid) (hY : Y.Valid)
    (p : Action J K) (i : Fin J) (a : Fin 4) (hother : Agree X Y i)
    (hsame : ∀ b : Fin 4, b ≠ a → parameter X p i b = parameter Y p i b) :
    |revenue M X p - revenue M Y p| ≤
      priceNorm M p * reach Y p i * |parameter X p i a - parameter Y p i a| := by
  by_cases hd : parameter X p i a = parameter Y p i a
  · have hall : ∀ b : Fin 4, parameter X p i b = parameter Y p i b := by
      intro b
      by_cases hb : b = a
      · rw [hb]; exact hd
      · exact hsame b hb
    have e0 := hall 0
    have e1 := hall 1
    have e2 := hall 2
    have e3 := hall 3
    simp only [parameter] at e0 e1 e2 e3
    simp at e0 e1 e2 e3
    have : revenue M X p = revenue M Y p := by
      apply rev_congr
      · intro j
        by_cases hj : j = i
        · subst hj; exact e0
        · exact ((hother j hj).1 (p j)).1
      · intro j
        by_cases hj : j = i
        · subst hj; exact e1
        · exact ((hother j hj).1 (p j)).2
      · intro j
        by_cases hj : j = i
        · subst hj; exact e2
        · exact (hother j hj).2.1
      · intro j
        by_cases hj : j = i
        · subst hj; exact e3
        · exact (hother j hj).2.2
    rw [this, hd]; simp
  · exact step_one M X Y hX hY p i a hother hsame hd

def updB {J K : ℕ} (A B : Cascade J K) (i : Fin J) : Cascade J K :=
  { A with beta := fun j k => if j = i then B.beta j k else A.beta j k }
def updA {J K : ℕ} (A B : Cascade J K) (i : Fin J) : Cascade J K :=
  { A with alpha := fun j k => if j = i then B.alpha j k else A.alpha j k }
def updG {J K : ℕ} (A B : Cascade J K) (i : Fin J) : Cascade J K :=
  { A with gamma := fun j => if j = i then B.gamma j else A.gamma j }
def updZ {J K : ℕ} (A B : Cascade J K) (i : Fin J) : Cascade J K :=
  { A with zeta := fun j => if j = i then B.zeta j else A.zeta j }

lemma stage {J K : ℕ} (M : Market J K) (A B : Cascade J K) (hA : A.Valid) (hB : B.Valid)
    (p : Action J K) (i : Fin J) (hAB : Agree A B i) :
    |revenue M A p - revenue M B p| ≤ priceNorm M p * reach A p i *
      (|B.beta i (p i) - A.beta i (p i)| + |B.alpha i (p i) - A.alpha i (p i)| +
        |B.gamma i - A.gamma i| + |B.zeta i - A.zeta i|) := by
  obtain ⟨hb, ha, hg, hz, hl⟩ := hA
  obtain ⟨hb', ha', hg', hz', hl'⟩ := hB
  set C1 := updB A B i with hC1
  set C2 := updA C1 B i with hC2
  set C3 := updG C2 B i with hC3
  set C4 := updZ C3 B i with hC4
  have v1 : C1.Valid := by
    refine ⟨?_, ha, hg, hz, hl⟩
    intro j k; simp only [hC1, updB]; split_ifs
    · exact hb' j k
    · exact hb j k
  have v2 : C2.Valid := by
    refine ⟨v1.1, ?_, v1.2.2.1, v1.2.2.2.1, v1.2.2.2.2⟩
    intro j k; simp only [hC2, updA]; split_ifs
    · exact ha' j k
    · exact v1.2.1 j k
  have v3 : C3.Valid := by
    refine ⟨v2.1, v2.2.1, ?_, v2.2.2.2.1, ?_⟩
    · intro j; simp only [hC3, updG]; split_ifs
      · exact hg' j
      · exact v2.2.2.1 j
    · intro j hj; simp only [hC3, updG]; split_ifs with h
      · exact ⟨(hl' j hj).1, v2.2.2.2.2 j hj |>.2⟩
      · exact v2.2.2.2.2 j hj
  have v4 : C4.Valid := by
    refine ⟨v3.1, v3.2.1, v3.2.2.1, ?_, ?_⟩
    · intro j; simp only [hC4, updZ]; split_ifs
      · exact hz' j
      · exact v3.2.2.2.1 j
    · intro j hj; simp only [hC4, updZ]; split_ifs with h
      · exact ⟨v3.2.2.2.2 j hj |>.1, (hl' j hj).2⟩
      · exact v3.2.2.2.2 j hj
  have a1 : Agree A C1 i := by
    intro j hj; simp [hC1, updB, hj]
  have a2 : Agree C1 C2 i := by
    intro j hj; simp [hC2, updA, hj]
  have a3 : Agree C2 C3 i := by
    intro j hj; simp [hC3, updG, hj]
  have a4 : Agree C3 C4 i := by
    intro j hj; simp [hC4, updZ, hj]
  have r1 : reach C1 p i = reach A p i := (reach_agree _ _ p i a1).symm
  have r2 : reach C2 p i = reach A p i := by
    rw [← r1]; exact (reach_agree _ _ p i a2).symm
  have r3 : reach C3 p i = reach A p i := by
    rw [← r2]; exact (reach_agree _ _ p i a3).symm
  have r4 : reach C4 p i = reach A p i := by
    rw [← r3]; exact (reach_agree _ _ p i a4).symm
  have s1 := step M A C1 ⟨hb, ha, hg, hz, hl⟩ v1 p i 0 a1 (by
    intro b hb0
    have : b ≠ 0 := hb0
    fin_cases b <;> simp_all [parameter, hC1, updB])
  have s2 := step M C1 C2 v1 v2 p i 1 a2 (by
    intro b hb0
    fin_cases b <;> simp_all [parameter, hC2, updA])
  have s3 := step M C2 C3 v2 v3 p i 2 a3 (by
    intro b hb0
    fin_cases b <;> simp_all [parameter, hC3, updG])
  have s4 := step M C3 C4 v3 v4 p i 3 a4 (by
    intro b hb0
    fin_cases b <;> simp_all [parameter, hC4, updZ])
  have e4 : revenue M C4 p = revenue M B p := by
    apply rev_congr
    · intro j
      by_cases hj : j = i
      · subst hj; simp [hC4, updZ, hC3, updG, hC2, updA, hC1, updB]
      · simp [hC4, updZ, hC3, updG, hC2, updA, hC1, updB, hj, (hAB j hj).1 (p j) |>.1]
    · intro j
      by_cases hj : j = i
      · subst hj; simp [hC4, updZ, hC3, updG, hC2, updA, hC1, updB]
      · simp [hC4, updZ, hC3, updG, hC2, updA, hC1, updB, hj, (hAB j hj).1 (p j) |>.2]
    · intro j
      by_cases hj : j = i
      · subst hj; simp [hC4, updZ, hC3, updG, hC2, updA, hC1, updB]
      · simp [hC4, updZ, hC3, updG, hC2, updA, hC1, updB, hj, (hAB j hj).2.1]
    · intro j
      by_cases hj : j = i
      · subst hj; simp [hC4, updZ, hC3, updG, hC2, updA, hC1, updB]
      · simp [hC4, updZ, hC3, updG, hC2, updA, hC1, updB, hj, (hAB j hj).2.2]
  rw [r1] at s1
  rw [r2] at s2
  rw [r3] at s3
  rw [r4] at s4
  have t1 : |parameter A p i 0 - parameter C1 p i 0| = |B.beta i (p i) - A.beta i (p i)| := by
    simp [parameter, hC1, updB, abs_sub_comm]
  have t2 : |parameter C1 p i 1 - parameter C2 p i 1| = |B.alpha i (p i) - A.alpha i (p i)| := by
    simp [parameter, hC1, hC2, updB, updA, abs_sub_comm]
  have t3 : |parameter C2 p i 2 - parameter C3 p i 2| = |B.gamma i - A.gamma i| := by
    simp [parameter, hC1, hC2, hC3, updB, updA, updG, abs_sub_comm]
  have t4 : |parameter C3 p i 3 - parameter C4 p i 3| = |B.zeta i - A.zeta i| := by
    simp [parameter, hC1, hC2, hC3, hC4, updB, updA, updG, updZ, abs_sub_comm]
  rw [t1] at s1
  rw [t2] at s2
  rw [t3] at s3
  rw [t4] at s4
  have k1 : |revenue M A p - revenue M B p| ≤ |revenue M A p - revenue M C1 p| +
      |revenue M C1 p - revenue M C2 p| + |revenue M C2 p - revenue M C3 p| +
      |revenue M C3 p - revenue M C4 p| := by
    have h1 : revenue M A p - revenue M B p = (revenue M A p - revenue M C1 p) +
      (revenue M C1 p - revenue M C2 p) + (revenue M C2 p - revenue M C3 p) +
      (revenue M C3 p - revenue M C4 p) := by rw [← e4]; ring
    rw [h1]
    refine (abs_add_le _ _).trans ?_
    gcongr
    refine (abs_add_le _ _).trans ?_
    gcongr
    exact abs_add_le _ _
  nlinarith [k1, s1, s2, s3, s4]

end GCT

namespace GCT

def Hy {J K : ℕ} (θ θ' : Cascade J K) (m : ℕ) : Cascade J K where
  beta := fun j k => if j.val < m then θ'.beta j k else θ.beta j k
  alpha := fun j k => if j.val < m then θ'.alpha j k else θ.alpha j k
  gamma := fun j => if j.val < m then θ'.gamma j else θ.gamma j
  zeta := fun j => if j.val < m then θ'.zeta j else θ.zeta j

lemma Hy_valid {J K : ℕ} (θ θ' : Cascade J K) (hθ : θ.Valid) (hθ' : θ'.Valid) (m : ℕ) :
    (Hy θ θ' m).Valid := by
  obtain ⟨hb, ha, hg, hz, hl⟩ := hθ
  obtain ⟨hb', ha', hg', hz', hl'⟩ := hθ'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j k; simp only [Hy]; split_ifs
    · exact hb' j k
    · exact hb j k
  · intro j k; simp only [Hy]; split_ifs
    · exact ha' j k
    · exact ha j k
  · intro j; simp only [Hy]; split_ifs
    · exact hg' j
    · exact hg j
  · intro j; simp only [Hy]; split_ifs
    · exact hz' j
    · exact hz j
  · intro j hj; simp only [Hy]; split_ifs
    · exact hl' j hj
    · exact hl j hj

lemma Hy_agree {J K : ℕ} (θ θ' : Cascade J K) (i : Fin J) :
    Agree (Hy θ θ' i.val) (Hy θ θ' (i.val + 1)) i := by
  intro j hj
  have hj' : j.val ≠ i.val := fun h => hj (Fin.ext h)
  have : (j < i) ↔ (j ≤ i) := ⟨le_of_lt, fun h => lt_of_le_of_ne h hj⟩
  simp [Hy, this]

lemma Hy_reach {J K : ℕ} (θ θ' : Cascade J K) (p : Action J K) (i : Fin J) :
    reach (Hy θ θ' i.val) p i = reach θ' p i := by
  unfold reach
  apply Finset.prod_congr rfl
  intro j hj
  have : j < i := Finset.mem_Iio.1 hj
  simp [continuation, Hy, this]

lemma Hy_zero {J K : ℕ} (M : Market J K) (θ θ' : Cascade J K) (p : Action J K) :
    revenue M (Hy θ θ' 0) p = revenue M θ p := by
  apply rev_congr <;> intro j <;> simp [Hy]

lemma Hy_top {J K : ℕ} (M : Market J K) (θ θ' : Cascade J K) (p : Action J K) :
    revenue M (Hy θ θ' J) p = revenue M θ' p := by
  apply rev_congr <;> intro j <;> simp [Hy, j.isLt]

end GCT

open GaoCascadePricing.UCB in
theorem solution {J K : ℕ} (M : Market J K)
    (θ θ' : Cascade J K) (hθ : θ.Valid) (hθ' : θ'.Valid) (p : Action J K) :
    |revenue M θ p - revenue M θ' p| ≤ priceNorm M p *
      ∑ i, reach θ' p i *
        (|θ'.beta i (p i) - θ.beta i (p i)| +
         |θ'.alpha i (p i) - θ.alpha i (p i)| +
         |θ'.gamma i - θ.gamma i| + |θ'.zeta i - θ.zeta i|) := by
  set T : Fin J → ℝ := fun i => priceNorm M p * (reach θ' p i *
        (|θ'.beta i (p i) - θ.beta i (p i)| +
         |θ'.alpha i (p i) - θ.alpha i (p i)| +
         |θ'.gamma i - θ.gamma i| + |θ'.zeta i - θ.zeta i|)) with hT
  have hstage : ∀ i : Fin J, |revenue M (GCT.Hy θ θ' i.val) p - revenue M (GCT.Hy θ θ' (i.val+1)) p| ≤ T i := by
    intro i
    have := GCT.stage M _ _ (GCT.Hy_valid θ θ' hθ hθ' _) (GCT.Hy_valid θ θ' hθ hθ' _) p i
      (GCT.Hy_agree θ θ' i)
    rw [GCT.Hy_reach] at this
    have q1 : (GCT.Hy θ θ' i.val).beta i (p i) = θ.beta i (p i) := by simp [GCT.Hy]
    have q2 : (GCT.Hy θ θ' i.val).alpha i (p i) = θ.alpha i (p i) := by simp [GCT.Hy]
    have q3 : (GCT.Hy θ θ' i.val).gamma i = θ.gamma i := by simp [GCT.Hy]
    have q4 : (GCT.Hy θ θ' i.val).zeta i = θ.zeta i := by simp [GCT.Hy]
    have q5 : (GCT.Hy θ θ' (i.val+1)).beta i (p i) = θ'.beta i (p i) := by simp [GCT.Hy]
    have q6 : (GCT.Hy θ θ' (i.val+1)).alpha i (p i) = θ'.alpha i (p i) := by simp [GCT.Hy]
    have q7 : (GCT.Hy θ θ' (i.val+1)).gamma i = θ'.gamma i := by simp [GCT.Hy]
    have q8 : (GCT.Hy θ θ' (i.val+1)).zeta i = θ'.zeta i := by simp [GCT.Hy]
    rw [q1, q2, q3, q4, q5, q6, q7, q8] at this
    simp only [hT]
    rw [← mul_assoc]; exact this
  have tele : revenue M θ p - revenue M θ' p =
      ∑ m ∈ Finset.range J, (revenue M (GCT.Hy θ θ' m) p - revenue M (GCT.Hy θ θ' (m+1)) p) := by
    rw [Finset.sum_range_sub' (fun m => revenue M (GCT.Hy θ θ' m) p), GCT.Hy_zero, GCT.Hy_top]
  have hsum : (priceNorm M p * ∑ i, reach θ' p i *
        (|θ'.beta i (p i) - θ.beta i (p i)| +
         |θ'.alpha i (p i) - θ.alpha i (p i)| +
         |θ'.gamma i - θ.gamma i| + |θ'.zeta i - θ.zeta i|)) = ∑ i, T i := by
    rw [Finset.mul_sum]
  rw [hsum, tele]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∑ i : Fin J, T i = ∑ m ∈ Finset.range J, (if h : m < J then T ⟨m, h⟩ else 0) := by
    rw [← Fin.sum_univ_eq_sum_range (fun m => if h : m < J then T ⟨m, h⟩ else 0) J]
    simp
  rw [this]
  apply Finset.sum_le_sum
  intro m hm
  have hm' : m < J := Finset.mem_range.1 hm
  rw [dif_pos hm']
  exact hstage ⟨m, hm'⟩
