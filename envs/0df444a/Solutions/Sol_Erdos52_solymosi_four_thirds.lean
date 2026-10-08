-- Prove2me | solution 1 for Erdos52.solymosi_four_thirds
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T16:50:30.249009+00:00
-- url     : https://prove2.me/submissions/80ea5d14-51c7-4af2-a4bf-81a542dc6f75

import Mathlib

open scoped Pointwise
open Finset

/-!
Solymosi's sum-product bound (J. Solymosi, *Bounding multiplicative energy by the sumset*,
Adv. Math. 222 (2009) 402–408, arXiv:0806.1040), formalized for finite sets of integers.

For a finite set `B` of positive reals the multiplicative energy, counted through the slopes
`b / a` of the points `(a, b) ∈ B × B`, is at most `4 (log₂ |B| + 1) (|B + B|² + |B|²)`:
after dyadic pigeonholing of the slope multiplicities, sums of points on consecutive lines of
one dyadic class are pairwise distinct elements of `(B + B) × (B + B)`. Cauchy–Schwarz then gives
`|B|⁴ ≤ |B · B| · E(B)`. A finite set of integers has a positive or a negated-negative part `B`
with `|A| ≤ 2|B| + 1` whose sum and product sets are no larger than those of `A`.
The consequences `max(|A + A|, |A · A|) ≥ c |A|^(5/4)` (Elekes' exponent) and the existence of a
fixed `δ > 0` with `max ≥ c |A|^(1+δ)` follow from `|A|⁴ log 2 ≤ 1296 M³ log |A|`
and `log x ≤ 4 x^(1/4)`.
-/

namespace Erdos52.SolymosiProof

/-- Slope of the ray from the origin through `p`. -/
noncomputable def ratio (p : ℝ × ℝ) : ℝ := p.2 / p.1

/-- Number of points of `B × B` on the line through the origin of slope `l`. -/
noncomputable def rcount (B : Finset ℝ) (l : ℝ) : ℕ := #{p ∈ B ×ˢ B | ratio p = l}

/-- The sum of the squared fibre sizes of `f` on `s` counts pairs in a common fibre. -/
theorem sum_card_fiber_sq {α β : Type*} [DecidableEq α] [DecidableEq β] (s : Finset α)
    (f : α → β) :
    ∑ y ∈ s.image f, #{x ∈ s | f x = y} ^ 2 = #{pq ∈ s ×ˢ s | f pq.1 = f pq.2} := by
  rw [card_eq_sum_card_fiberwise (f := fun pq : α × α => f pq.1) (t := s.image f)]
  · refine sum_congr rfl fun y _ => ?_
    rw [sq, ← card_product]
    congr 1
    ext ⟨a, b⟩
    simp only [mem_filter, mem_product]
    constructor
    · rintro ⟨⟨ha, rfl⟩, hb, hby⟩
      exact ⟨⟨⟨ha, hb⟩, hby.symm⟩, rfl⟩
    · rintro ⟨⟨⟨ha, hb⟩, hab⟩, rfl⟩
      exact ⟨⟨ha, rfl⟩, hb, hab.symm⟩
  · intro pq hpq
    rw [mem_coe, mem_filter, mem_product] at hpq
    rw [mem_coe]
    exact mem_image_of_mem f hpq.1.1

/-- A point of `B × B` with slope `l` lies on the line `y = l x` with `x > 0`. -/
theorem on_line {B : Finset ℝ} (hB : ∀ b ∈ B, 0 < b) {p : ℝ × ℝ} (hp : p ∈ B ×ˢ B) {l : ℝ}
    (hl : ratio p = l) : 0 < p.1 ∧ p.2 = l * p.1 := by
  have h1 := hB _ (mem_product.1 hp).1
  refine ⟨h1, ?_⟩
  rw [← hl, ratio, div_mul_cancel₀ _ h1.ne']

/-- Each line through the origin meets `B × B` in at most `|B|` points. -/
theorem rcount_le {B : Finset ℝ} (hB : ∀ b ∈ B, 0 < b) (l : ℝ) : rcount B l ≤ #B := by
  refine card_le_card_of_injOn (fun p => p.1) ?_ ?_
  · intro p hp
    rw [mem_coe, mem_filter, mem_product] at hp
    exact hp.1.1
  · intro p hp q hq hpq
    rw [mem_coe, mem_filter] at hp hq
    have h1 := on_line hB hp.1 hp.2
    have h2 := on_line hB hq.1 hq.2
    simp only at hpq
    exact Prod.ext hpq (by rw [h1.2, h2.2, hpq])

/-- The ratio form and the product form of the multiplicative energy agree. -/
theorem energy_eq {B : Finset ℝ} (hB : ∀ b ∈ B, 0 < b) :
    #{pq ∈ (B ×ˢ B) ×ˢ (B ×ˢ B) | ratio pq.1 = ratio pq.2} =
      #{pq ∈ (B ×ˢ B) ×ˢ (B ×ˢ B) | pq.1.1 * pq.1.2 = pq.2.1 * pq.2.2} := by
  refine card_nbij' (fun pq => ((pq.1.2, pq.2.1), (pq.1.1, pq.2.2)))
    (fun pq => ((pq.2.1, pq.1.1), (pq.1.2, pq.2.2))) ?_ ?_ ?_ ?_
  · intro pq h
    rw [mem_coe, mem_filter, mem_product, mem_product, mem_product] at h
    rw [mem_coe, mem_filter, mem_product, mem_product, mem_product]
    obtain ⟨⟨⟨ha, hb⟩, hc, hd⟩, h⟩ := h
    simp only [ratio] at h
    rw [div_eq_div_iff (hB _ ha).ne' (hB _ hc).ne'] at h
    exact ⟨⟨⟨hb, hc⟩, ha, hd⟩, by linarith⟩
  · intro pq h
    rw [mem_coe, mem_filter, mem_product, mem_product, mem_product] at h
    rw [mem_coe, mem_filter, mem_product, mem_product, mem_product]
    obtain ⟨⟨⟨hx, hy⟩, hz, hw⟩, h⟩ := h
    refine ⟨⟨⟨hz, hx⟩, hy, hw⟩, ?_⟩
    simp only [ratio]
    rw [div_eq_div_iff (hB _ hz).ne' (hB _ hy).ne']
    linarith
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ _
    rfl
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ _
    rfl

/-- Cauchy–Schwarz: `|B|⁴ ≤ |B · B| · E(B)`. -/
theorem card_pow_four_le (B : Finset ℝ) :
    #B ^ 4 ≤ #(B * B) * #{pq ∈ (B ×ˢ B) ×ˢ (B ×ˢ B) | pq.1.1 * pq.1.2 = pq.2.1 * pq.2.2} := by
  have h1 : #(B ×ˢ B) = ∑ x ∈ B * B, #{p ∈ B ×ˢ B | p.1 * p.2 = x} := by
    rw [← image_mul_product]
    exact card_eq_sum_card_fiberwise fun p hp => mem_coe.2 (mem_image_of_mem _ (mem_coe.1 hp))
  have h2 := sum_card_fiber_sq (B ×ˢ B) (fun p : ℝ × ℝ => p.1 * p.2)
  rw [image_mul_product] at h2
  have h3 := sq_sum_le_card_mul_sum_sq (s := B * B)
    (f := fun x => #{p ∈ B ×ˢ B | p.1 * p.2 = x})
  rw [← h1, h2, card_product] at h3
  calc #B ^ 4 = (#B * #B) ^ 2 := by ring
    _ ≤ _ := h3

/-- Solymosi's cone argument. If every slope in `S` carries at least `N` points of `B × B`,
then `(|S| - 1) N² ≤ |B + B|²`: sums of a point on a line of `S` and a point on the next line of
`S` (in increasing order of slope) are pairwise distinct points of `(B + B) × (B + B)`. -/
theorem cone_bound {B : Finset ℝ} (hB : ∀ b ∈ B, 0 < b) (S : Finset ℝ) (N : ℕ)
    (hN : ∀ l ∈ S, N ≤ rcount B l) : (#S - 1) * N ^ 2 ≤ #(B + B) ^ 2 := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  set m := S.max' hS
  have hnext : ∀ l ∈ S.erase m, ∃ μ ∈ S, l < μ ∧ ∀ l' ∈ S, l < l' → μ ≤ l' := by
    intro l hl
    rw [mem_erase] at hl
    have hT : ({l' ∈ S | l < l'}).Nonempty :=
      ⟨m, mem_filter.2 ⟨max'_mem S hS, lt_of_le_of_ne (le_max' S l hl.2) hl.1⟩⟩
    exact ⟨_, (mem_filter.1 (min'_mem _ hT)).1, (mem_filter.1 (min'_mem _ hT)).2,
      fun l' hl' hll' => min'_le _ _ (mem_filter.2 ⟨hl', hll'⟩)⟩
  choose! nxt hnS hnlt hnmin using hnext
  set D := (S.erase m).sigma
    (fun l => {p ∈ B ×ˢ B | ratio p = l} ×ˢ {q ∈ B ×ˢ B | ratio q = nxt l}) with hD
  have hDcard : #D = ∑ l ∈ S.erase m, rcount B l * rcount B (nxt l) := by
    rw [hD, card_sigma]
    exact sum_congr rfl fun l _ => card_product _ _
  have hlow : (#S - 1) * N ^ 2 ≤ #D := by
    rw [hDcard, ← card_erase_of_mem (max'_mem S hS)]
    calc #(S.erase m) * N ^ 2 = ∑ l ∈ S.erase m, N * N := by rw [sum_const, smul_eq_mul, sq]
      _ ≤ _ := sum_le_sum fun l hl =>
        Nat.mul_le_mul (hN l (mem_of_mem_erase hl)) (hN _ (hnS l hl))
  have memD : ∀ x ∈ D, x.1 ∈ S.erase m ∧ x.2.1.1 ∈ B ∧ x.2.2.1 ∈ B ∧ 0 < x.2.1.1 ∧
      x.2.1.2 = x.1 * x.2.1.1 ∧ 0 < x.2.2.1 ∧ x.2.2.2 = nxt x.1 * x.2.2.1 := by
    intro x hx
    rw [hD, mem_sigma, mem_product, mem_filter, mem_filter] at hx
    obtain ⟨hl, ⟨hp, hpl⟩, ⟨hq, hql⟩⟩ := hx
    have h1 := on_line hB hp hpl
    have h2 := on_line hB hq hql
    exact ⟨hl, (mem_product.1 hp).1, (mem_product.1 hq).1, h1.1, h1.2, h2.1, h2.2⟩
  have hup : #D ≤ #(B + B) ^ 2 := by
    rw [sq, ← card_product]
    refine card_le_card_of_injOn (fun x => (x.2.1.1 + x.2.2.1, x.2.1.2 + x.2.2.2)) ?_ ?_
    · rintro ⟨l, p, q⟩ hx
      rw [mem_coe, hD, mem_sigma, mem_product, mem_filter, mem_filter] at hx
      obtain ⟨_, ⟨hp, _⟩, ⟨hq, _⟩⟩ := hx
      rw [mem_coe, mem_product]
      exact ⟨add_mem_add (mem_product.1 hp).1 (mem_product.1 hq).1,
        add_mem_add (mem_product.1 hp).2 (mem_product.1 hq).2⟩
    · rintro ⟨l, ⟨p1, p2⟩, ⟨q1, q2⟩⟩ hx ⟨l', ⟨p1', p2'⟩, ⟨q1', q2'⟩⟩ hx' heq
      obtain ⟨hl, -, -, hp1, hp2, hq1, hq2⟩ := memD _ (mem_coe.1 hx)
      obtain ⟨hl', -, -, hp1', hp2', hq1', hq2'⟩ := memD _ (mem_coe.1 hx')
      simp only [Prod.mk.injEq] at heq hp2 hq2 hp2' hq2'
      obtain ⟨h1, h2⟩ := heq
      subst hp2 hq2 hp2' hq2'
      have hlS := mem_of_mem_erase hl
      have hlS' := mem_of_mem_erase hl'
      have hlt := hnlt l hl
      have hlt' := hnlt l' hl'
      have hp1 : 0 < p1 := hp1
      have hq1 : 0 < q1 := hq1
      have hp1' : 0 < p1' := hp1'
      have hq1' : 0 < q1' := hq1'
      have hll : l = l' := by
        rcases lt_trichotomy l l' with h | h | h
        · exfalso
          have hmin := hnmin l hl l' hlS' h
          have e : l' * (p1 + q1) = l' * (p1' + q1') := by rw [h1]
          nlinarith [mul_pos (sub_pos.2 hlt) hp1, mul_pos (sub_pos.2 hlt') hq1',
            mul_le_mul_of_nonneg_right hmin (by linarith : (0 : ℝ) ≤ p1 + q1)]
        · exact h
        · exfalso
          have hmin := hnmin l' hl' l hlS h
          have e : l * (p1 + q1) = l * (p1' + q1') := by rw [h1]
          nlinarith [mul_pos (sub_pos.2 hlt') hp1', mul_pos (sub_pos.2 hlt) hq1,
            mul_le_mul_of_nonneg_right hmin (by linarith : (0 : ℝ) ≤ p1' + q1')]
      subst hll
      have hq : (nxt l - l) * (q1 - q1') = 0 := by linear_combination h2 - l * h1
      rcases mul_eq_zero.1 hq with h | h
      · exact absurd h (sub_pos.2 hlt).ne'
      · have hq' : q1 = q1' := by linarith
        have hp' : p1 = p1' := by linarith
        subst hq' hp'
        rfl
  exact hlow.trans hup

/-- Solymosi's energy bound with dyadic pigeonholing of the slope multiplicities. -/
theorem energy_le {B : Finset ℝ} (hB : ∀ b ∈ B, 0 < b) :
    #{pq ∈ (B ×ˢ B) ×ˢ (B ×ˢ B) | ratio pq.1 = ratio pq.2} ≤
      (Nat.log 2 #B + 1) * (4 * (#(B + B) ^ 2 + #B ^ 2)) := by
  rw [← sum_card_fiber_sq (B ×ˢ B) ratio]
  change ∑ l ∈ (B ×ˢ B).image ratio, rcount B l ^ 2 ≤ _
  rw [← sum_fiberwise_of_maps_to (t := range (Nat.log 2 #B + 1))
    (g := fun l => Nat.log 2 (rcount B l))
    (fun l _ => mem_range.2 (Nat.lt_succ_of_le (Nat.log_mono_right (rcount_le hB l))))]
  refine (sum_le_card_nsmul _ _ (4 * (#(B + B) ^ 2 + #B ^ 2)) ?_).trans
    (by rw [card_range, smul_eq_mul])
  intro j _
  set Sj := {l ∈ (B ×ˢ B).image ratio | Nat.log 2 (rcount B l) = j} with hSj
  have hpos : ∀ l ∈ Sj, 2 ^ j ≤ rcount B l := by
    intro l hl
    obtain ⟨hlQ, hlj⟩ := mem_filter.1 hl
    obtain ⟨p, hp, hpl⟩ := mem_image.1 hlQ
    have hne : rcount B l ≠ 0 := (card_pos.2 ⟨p, mem_filter.2 ⟨hp, hpl⟩⟩).ne'
    rw [← hlj]
    exact Nat.pow_log_le_self 2 hne
  have hsq : ∀ l ∈ Sj, rcount B l ^ 2 ≤ 4 * (2 ^ j) ^ 2 := by
    intro l hl
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (rcount B l)
    rw [(mem_filter.1 hl).2] at h
    calc rcount B l ^ 2 ≤ (2 ^ (j + 1)) ^ 2 := Nat.pow_le_pow_left h.le 2
      _ = 4 * (2 ^ j) ^ 2 := by ring
  have hcone := cone_bound hB Sj (2 ^ j) hpos
  calc ∑ l ∈ Sj, rcount B l ^ 2 ≤ ∑ l ∈ Sj, 4 * (2 ^ j) ^ 2 := sum_le_sum hsq
    _ = #Sj * (4 * (2 ^ j) ^ 2) := by rw [sum_const, smul_eq_mul]
    _ ≤ 4 * (#(B + B) ^ 2 + #B ^ 2) := by
      rcases Sj.eq_empty_or_nonempty with h | ⟨l, hl⟩
      · rw [h]
        simp
      · have h2j : 2 ^ j ≤ #B := (hpos l hl).trans (rcount_le hB l)
        have hN : (2 ^ j) ^ 2 ≤ #B ^ 2 := Nat.pow_le_pow_left h2j 2
        obtain ⟨k, hk⟩ : ∃ k, #Sj = k + 1 := ⟨#Sj - 1, by have := card_pos.2 ⟨l, hl⟩; omega⟩
        rw [hk] at hcone ⊢
        simp only [Nat.add_sub_cancel] at hcone
        nlinarith

/-- Solymosi's inequality for a finite set of positive reals:
`|B|⁴ ≤ 4 (⌊log₂ |B|⌋ + 1) · |B · B| · (|B + B|² + |B|²)`. -/
theorem solymosi_core {B : Finset ℝ} (hB : ∀ b ∈ B, 0 < b) :
    #B ^ 4 ≤ #(B * B) * ((Nat.log 2 #B + 1) * (4 * (#(B + B) ^ 2 + #B ^ 2))) :=
  (card_pow_four_le B).trans (by rw [← energy_eq hB]; exact Nat.mul_le_mul_left _ (energy_le hB))

/-- The part of `A` on one side of `0`, moved to the positive reals. -/
theorem side_part (A : Finset ℤ) (σ : ℤ) (hσ : σ * σ = 1) :
    (∀ b ∈ {a ∈ A | 0 < σ * a}.image (fun a => ((σ * a : ℤ) : ℝ)), 0 < b) ∧
    #({a ∈ A | 0 < σ * a}.image (fun a => ((σ * a : ℤ) : ℝ))) = #{a ∈ A | 0 < σ * a} ∧
    #({a ∈ A | 0 < σ * a}.image (fun a => ((σ * a : ℤ) : ℝ)) +
      {a ∈ A | 0 < σ * a}.image (fun a => ((σ * a : ℤ) : ℝ))) ≤ #(A + A) ∧
    #({a ∈ A | 0 < σ * a}.image (fun a => ((σ * a : ℤ) : ℝ)) *
      {a ∈ A | 0 < σ * a}.image (fun a => ((σ * a : ℤ) : ℝ))) ≤ #(A * A) := by
  have hσR : (σ : ℝ) * σ = 1 := by exact_mod_cast hσ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hb
    exact_mod_cast (mem_filter.1 ha).2
  · refine card_image_of_injOn fun a _ a' _ h => ?_
    have h' : σ * a = σ * a' := by exact_mod_cast h
    calc a = σ * (σ * a) := by rw [← mul_assoc, hσ, one_mul]
      _ = σ * (σ * a') := by rw [h']
      _ = a' := by rw [← mul_assoc, hσ, one_mul]
  · refine (card_le_card (t := (A + A).image (fun x => ((σ * x : ℤ) : ℝ))) ?_).trans card_image_le
    intro z hz
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_add.1 hz
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hu
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hv
    exact mem_image.2 ⟨a + b, add_mem_add (mem_filter.1 ha).1 (mem_filter.1 hb).1,
      by push_cast; ring⟩
  · refine (card_le_card (t := (A * A).image (fun x => ((x : ℤ) : ℝ))) ?_).trans card_image_le
    intro z hz
    obtain ⟨u, hu, v, hv, rfl⟩ := mem_mul.1 hz
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hu
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hv
    exact mem_image.2 ⟨a * b, mul_mem_mul (mem_filter.1 ha).1 (mem_filter.1 hb).1,
      by push_cast; linear_combination (-((a : ℝ) * b)) * hσR⟩

/-- Every finite set of integers has a "half" `B` of positive reals, of size at least
`(|A| - 1) / 2`, whose sum and product sets are no larger than those of `A`. -/
theorem exists_half (A : Finset ℤ) : ∃ B : Finset ℝ, (∀ b ∈ B, 0 < b) ∧ #A ≤ 2 * #B + 1 ∧
    #B ≤ #A ∧ #(B + B) ≤ #(A + A) ∧ #(B * B) ≤ #(A * A) := by
  have hcover : #A ≤ #{a ∈ A | 0 < 1 * a} + #{a ∈ A | 0 < -1 * a} + 1 := by
    calc #A ≤ #({a ∈ A | 0 < 1 * a} ∪ {a ∈ A | 0 < -1 * a} ∪ {0}) := by
          refine card_le_card fun a ha => ?_
          rcases lt_trichotomy a 0 with h | h | h
          · exact mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨ha, by linarith⟩))
          · exact mem_union_right _ (mem_singleton.2 h)
          · exact mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨ha, by linarith⟩))
      _ ≤ _ := (card_union_le _ _).trans (by
          rw [card_singleton]
          exact Nat.add_le_add_right (card_union_le _ _) 1)
  rcases le_total #{a ∈ A | 0 < -1 * a} #{a ∈ A | 0 < 1 * a} with h | h
  · obtain ⟨h1, h2, h3, h4⟩ := side_part A 1 (by norm_num)
    refine ⟨_, h1, by omega, ?_, h3, h4⟩
    rw [h2]
    exact card_filter_le _ _
  · obtain ⟨h1, h2, h3, h4⟩ := side_part A (-1) (by norm_num)
    refine ⟨_, h1, by omega, ?_, h3, h4⟩
    rw [h2]
    exact card_filter_le _ _

theorem card_le_card_add_self (A : Finset ℤ) : #A ≤ #(A + A) := by
  rcases A.eq_empty_or_nonempty with rfl | h
  · simp
  · exact card_le_card_add_left h

/-- Combinatorial form: `x⁴ ≤ 8 (⌊log₂ x⌋ + 1) M³` for the size `x` of a half of `A`,
where `M = max(|A + A|, |A · A|)`. -/
theorem nat_bound (A : Finset ℤ) : ∃ x : ℕ, #A ≤ 2 * x + 1 ∧ x ≤ #A ∧
    x ^ 4 ≤ 8 * (Nat.log 2 x + 1) * max #(A + A) #(A * A) ^ 3 := by
  obtain ⟨B, hB, h1, h2, h3, h4⟩ := exists_half A
  refine ⟨#B, h1, h2, ?_⟩
  set M := max #(A + A) #(A * A)
  have hM1 : #(B + B) ≤ M := h3.trans (le_max_left _ _)
  have hM2 : #(B * B) ≤ M := h4.trans (le_max_right _ _)
  have hM3 : #B ≤ M := h2.trans ((card_le_card_add_self A).trans (le_max_left _ _))
  calc #B ^ 4 ≤ #(B * B) * ((Nat.log 2 #B + 1) * (4 * (#(B + B) ^ 2 + #B ^ 2))) :=
        solymosi_core hB
    _ ≤ M * ((Nat.log 2 #B + 1) * (4 * (M ^ 2 + M ^ 2))) := by gcongr
    _ = 8 * (Nat.log 2 #B + 1) * M ^ 3 := by ring

/-- Real form: `|A|⁴ log 2 ≤ 1296 M³ log |A|` whenever `|A| ≥ 2`. -/
theorem key_real (A : Finset ℤ) (hA : 2 ≤ #A) :
    (#A : ℝ) ^ 4 * Real.log 2 ≤
      1296 * (max (#(A + A) : ℝ) (#(A * A) : ℝ)) ^ 3 * Real.log (#A : ℝ) := by
  obtain ⟨x, h1, h2, h3⟩ := nat_bound A
  have hx : 1 ≤ x := by omega
  set L := Nat.log 2 x
  have h3R : (x : ℝ) ^ 4 ≤ 8 * ((L : ℝ) + 1) * (max (#(A + A) : ℝ) (#(A * A) : ℝ)) ^ 3 := by
    rw [← Nat.cast_max]
    exact_mod_cast h3
  have hnx : (#A : ℝ) ≤ 3 * x := by
    have : #A ≤ 3 * x := by omega
    exact_mod_cast this
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : (L : ℝ) * Real.log 2 ≤ Real.log x := by
    rw [← Real.log_pow]
    refine Real.log_le_log (by positivity) ?_
    exact_mod_cast Nat.pow_log_le_self 2 (by omega : x ≠ 0)
  have hxn : Real.log x ≤ Real.log #A := Real.log_le_log hxpos (by exact_mod_cast h2)
  have h2n : Real.log 2 ≤ Real.log #A := Real.log_le_log (by norm_num) (by exact_mod_cast hA)
  set M := max (#(A + A) : ℝ) (#(A * A) : ℝ)
  have hM : 0 ≤ M := le_trans (Nat.cast_nonneg _) (le_max_left _ _)
  have hn4 : (#A : ℝ) ^ 4 ≤ 81 * (x : ℝ) ^ 4 := by
    calc (#A : ℝ) ^ 4 ≤ (3 * x) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hnx 4
      _ = 81 * (x : ℝ) ^ 4 := by ring
  have hM3 : 0 ≤ M ^ 3 := pow_nonneg hM 3
  calc (#A : ℝ) ^ 4 * Real.log 2 ≤ 81 * (8 * ((L : ℝ) + 1) * M ^ 3) * Real.log 2 := by
        gcongr
        exact hn4.trans (by linarith)
    _ = 648 * M ^ 3 * ((L : ℝ) * Real.log 2 + Real.log 2) := by ring
    _ ≤ 648 * M ^ 3 * (2 * Real.log #A) := by gcongr; linarith
    _ = 1296 * M ^ 3 * Real.log (#A : ℝ) := by ring

theorem rpow_cube {y : ℝ} (hy : 0 ≤ y) (a : ℝ) : (y ^ a) ^ 3 = y ^ (a * 3) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy]
  norm_num

/-- Elekes' exponent `5/4`, with an explicit constant. -/
theorem elekes_aux : ∃ C : ℝ, 0 < C ∧ ∀ A : Finset ℤ,
    C * (#A : ℝ) ^ ((5 : ℝ) / 4) ≤ max (#(A + A) : ℝ) (#(A * A) : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9
    linarith
  set k : ℝ := Real.log 2 / 5184 with hk
  have hkpos : 0 < k := by positivity
  have hk1 : k ≤ 1 := by
    rw [hk, div_le_one (by norm_num)]
    linarith
  refine ⟨k ^ ((1 : ℝ) / 3), by positivity, fun A => ?_⟩
  set M := max (#(A + A) : ℝ) (#(A * A) : ℝ) with hM
  have hM0 : 0 ≤ M := le_trans (Nat.cast_nonneg _) (le_max_left _ _)
  have hnM : (#A : ℝ) ≤ M :=
    (Nat.cast_le.2 (card_le_card_add_self A)).trans (le_max_left _ _)
  by_cases hA : 2 ≤ #A
  · have hkey := key_real A hA
    have hn : (0 : ℝ) < #A := by exact_mod_cast (by omega : 0 < #A)
    have hlogn := Real.log_le_rpow_div hn.le (by norm_num : (0 : ℝ) < 1 / 4)
    have hy : (0 : ℝ) < (#A : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hn _
    have hlogpos : 0 < Real.log (#A : ℝ) := Real.log_pos (by exact_mod_cast hA)
    have hM3 : 0 ≤ M ^ 3 := pow_nonneg hM0 3
    have h4 : (#A : ℝ) ^ 4 = (#A : ℝ) ^ ((15 : ℝ) / 4) * (#A : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_add hn]
      norm_num
    have h1 : (#A : ℝ) ^ 4 * Real.log 2 ≤ 5184 * M ^ 3 * (#A : ℝ) ^ ((1 : ℝ) / 4) := by
      calc (#A : ℝ) ^ 4 * Real.log 2 ≤ 1296 * M ^ 3 * Real.log (#A : ℝ) := hkey
        _ ≤ 1296 * M ^ 3 * ((#A : ℝ) ^ ((1 : ℝ) / 4) / (1 / 4)) := by gcongr
        _ = 5184 * M ^ 3 * (#A : ℝ) ^ ((1 : ℝ) / 4) := by ring
    rw [h4] at h1
    have h2 : (#A : ℝ) ^ ((15 : ℝ) / 4) * Real.log 2 ≤ 5184 * M ^ 3 := by
      have : ((#A : ℝ) ^ ((15 : ℝ) / 4) * Real.log 2) * (#A : ℝ) ^ ((1 : ℝ) / 4) ≤
          (5184 * M ^ 3) * (#A : ℝ) ^ ((1 : ℝ) / 4) := by linarith
      exact le_of_mul_le_mul_right this hy
    have hC3 : (k ^ ((1 : ℝ) / 3)) ^ 3 = k := by
      rw [rpow_cube hkpos.le]
      norm_num
    rw [← pow_le_pow_iff_left₀ (by positivity) hM0 (by norm_num : 3 ≠ 0), mul_pow, hC3,
      rpow_cube hn.le]
    have h5 : (5 : ℝ) / 4 * 3 = 15 / 4 := by norm_num
    rw [h5, hk]
    linarith
  · have hA' : #A = 0 ∨ #A = 1 := by omega
    rcases hA' with h | h
    · rw [h]
      simp [hM0]
    · rw [h]
      have h1M : (1 : ℝ) ≤ M := by simpa [h] using hnM
      have : k ^ ((1 : ℝ) / 3) ≤ 1 := Real.rpow_le_one hkpos.le hk1 (by norm_num)
      simpa using this.trans h1M

end Erdos52.SolymosiProof

open Erdos52.SolymosiProof in
theorem solution : ∃ (C : ℝ), 0 < C ∧ ∀ (A : Finset ℤ), 2 ≤ A.card →
    (max (A + A).card (A * A).card : ℝ) ≥
      C * (A.card : ℝ) ^ ((4 : ℝ) / 3) / Real.log (A.card : ℝ) ^ ((1 : ℝ) / 3) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(Real.log 2 / 1296) ^ ((1 : ℝ) / 3), by positivity, fun A hA => ?_⟩
  have hkey := key_real A hA
  have hn : (0 : ℝ) ≤ #A := Nat.cast_nonneg _
  have hlogn : 0 < Real.log (#A : ℝ) := Real.log_pos (by exact_mod_cast hA)
  have hM : (0 : ℝ) ≤ max ((A + A).card : ℝ) ((A * A).card : ℝ) :=
    le_trans (Nat.cast_nonneg _) (le_max_left _ _)
  rw [ge_iff_le, ← pow_le_pow_iff_left₀ (by positivity) hM (by norm_num : 3 ≠ 0), div_pow,
    mul_pow, rpow_cube (by positivity), rpow_cube hn, rpow_cube hlogn.le]
  norm_num
  rw [div_le_iff₀ hlogn]
  nlinarith
