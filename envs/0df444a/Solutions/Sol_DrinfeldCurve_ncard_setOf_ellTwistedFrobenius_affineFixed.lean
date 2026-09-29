-- Prove2me | solution 1 for DrinfeldCurve.ncard_setOf_ellTwistedFrobenius_affineFixed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/e28ae6e9-3314-5e73-a919-227e88140810

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_ncard_setOf_ellTwistedFrobenius_affineFixed

set_option autoImplicit false

namespace DrinfeldCurve

namespace EllForm

open Polynomial

section FiniteField

variable (q : ℕ) [hq : Fact q.Prime]

abbrev F2 : Type := GaloisField q 2

theorem pow_card_F2 (x : F2 q) : x ^ q ^ 2 = x := by
  haveI : Fintype (F2 q) := Fintype.ofFinite _
  have h : Fintype.card (F2 q) = q ^ 2 := by rw [Fintype.card_eq_nat_card, GaloisField.card q 2 two_ne_zero]
  rw [← h]; exact FiniteField.pow_card x

theorem neg_pow_q (x : F2 q) : (-x) ^ q = -(x ^ q) := by
  rw [← frobenius_def, map_neg, frobenius_def]

theorem frob_eq (x : F2 q) : frobenius (F2 q) q x = x ^ q := frobenius_def q x

variable {q}

theorem inv_eq_pow_of_pow_succ_eq_one {l : F2 q} (hl : l ^ (q + 1) = 1) : l ^ q = l⁻¹ := by
  have hl0 : l ≠ 0 := by
    rintro rfl; rw [zero_pow (Nat.succ_ne_zero q)] at hl; exact zero_ne_one hl
  exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ, hl])

noncomputable def w₁ (l₁ l₂ d : F2 q) : F2 q := (d ^ q - l₂ * d) / (l₁ - l₂)
noncomputable def w₂ (l₁ l₂ d : F2 q) : F2 q := w₁ l₁ l₂ d - d

theorem w₂_eq (l₁ l₂ d : F2 q) (h12 : l₁ ≠ l₂) : w₂ l₁ l₂ d = (d ^ q - l₁ * d) / (l₁ - l₂) := by
  have h := sub_ne_zero.mpr h12
  rw [w₂, w₁, eq_div_iff h, sub_mul, div_mul_cancel₀ _ h]
  ring

variable {l₁ l₂ d : F2 q} (h12 : l₁ ≠ l₂) (hl1 : l₁ ^ (q + 1) = 1) (hl2 : l₂ ^ (q + 1) = 1)
  (hd : d ^ q = -d)

include hd h12 in
theorem w₁_eq_zero_iff : w₁ l₁ l₂ d = 0 ↔ d = 0 ∨ l₂ = -1 := by
  rw [w₁, div_eq_zero_iff, or_iff_left (sub_ne_zero.mpr h12), hd,
    show -d - l₂ * d = -(d * (1 + l₂)) by ring, neg_eq_zero, mul_eq_zero, add_eq_zero_iff_eq_neg']

include hd h12 in
theorem w₂_eq_zero_iff : w₂ l₁ l₂ d = 0 ↔ d = 0 ∨ l₁ = -1 := by
  rw [w₂_eq _ _ _ h12, div_eq_zero_iff, or_iff_left (sub_ne_zero.mpr h12), hd,
    show -d - l₁ * d = -(d * (1 + l₁)) by ring, neg_eq_zero, mul_eq_zero, add_eq_zero_iff_eq_neg']

include h12 hl1 hl2 hd in

theorem w₁_pow : w₁ l₁ l₂ d ^ q = l₁ * w₁ l₁ l₂ d := by
  have hl10 : l₁ ≠ 0 := by rintro rfl; rw [zero_pow (Nat.succ_ne_zero q)] at hl1; exact zero_ne_one hl1
  have hl20 : l₂ ≠ 0 := by rintro rfl; rw [zero_pow (Nat.succ_ne_zero q)] at hl2; exact zero_ne_one hl2
  have e1 : l₁ ^ q = l₁⁻¹ := inv_eq_pow_of_pow_succ_eq_one hl1
  have e2 : l₂ ^ q = l₂⁻¹ := inv_eq_pow_of_pow_succ_eq_one hl2
  have hdq : (d ^ q) ^ q = d := by rw [← pow_mul, ← sq, pow_card_F2]
  rw [w₁, div_pow, sub_pow_char, mul_pow, sub_pow_char, hdq, e1, e2, hd]
  have h12' : l₁ - l₂ ≠ 0 := sub_ne_zero.mpr h12
  have hB : l₁⁻¹ - l₂⁻¹ ≠ 0 := sub_ne_zero.mpr fun h => h12 (inv_injective h)
  rw [div_eq_iff hB]
  field_simp
  ring

include h12 hl1 hl2 hd in

theorem w₂_pow : w₂ l₁ l₂ d ^ q = l₂ * w₂ l₁ l₂ d := by
  have hl10 : l₁ ≠ 0 := by rintro rfl; rw [zero_pow (Nat.succ_ne_zero q)] at hl1; exact zero_ne_one hl1
  have hl20 : l₂ ≠ 0 := by rintro rfl; rw [zero_pow (Nat.succ_ne_zero q)] at hl2; exact zero_ne_one hl2
  have e1 : l₁ ^ q = l₁⁻¹ := inv_eq_pow_of_pow_succ_eq_one hl1
  have e2 : l₂ ^ q = l₂⁻¹ := inv_eq_pow_of_pow_succ_eq_one hl2
  have hdq : (d ^ q) ^ q = d := by rw [← pow_mul, ← sq, pow_card_F2]
  rw [w₂_eq _ _ _ h12, div_pow, sub_pow_char, mul_pow, sub_pow_char, hdq, e1, e2, hd]
  have h12' : l₁ - l₂ ≠ 0 := sub_ne_zero.mpr h12
  have hB : l₁⁻¹ - l₂⁻¹ ≠ 0 := sub_ne_zero.mpr fun h => h12 (inv_injective h)
  rw [div_eq_iff hB]
  field_simp
  ring

end FiniteField

section Closed

variable (q : ℕ) [hq : Fact q.Prime] (K : Type*) [Field K] [Algebra (GaloisField q 2) K]

abbrev ι : F2 q →+* K := algebraMap (F2 q) K

theorem charP_K : CharP K q := charP_of_injective_algebraMap' (F2 q) q

theorem cast_succ_ne_zero : ((q + 1 : ℕ) : K) ≠ 0 := by
  haveI := charP_K q K
  rw [Ne, CharP.cast_eq_zero_iff K q]
  intro h
  have h1 : q ∣ 1 := (Nat.dvd_add_right (dvd_refl q)).mp h
  exact hq.out.one_lt.ne' (Nat.dvd_one.mp h1)

theorem ncard_setOf_pow_eq [IsAlgClosed K] (n : ℕ) (hn : 0 < n) (hnK : (n : K) ≠ 0) {w : K} (hw : w ≠ 0) :
    {u : K | u ^ n = w}.ncard = n := by
  classical
  have hset : {u : K | u ^ n = w} = ((Polynomial.nthRoots n w).toFinset : Set K) := by
    ext u
    rw [Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
  rw [hset, Set.ncard_coe_finset, Multiset.toFinset_card_of_nodup]
  ·
    rw [Polynomial.nthRoots]
    have hsplit := IsAlgClosed.splits (X ^ n - C w : K[X])
    have hdeg : (X ^ n - C w : K[X]).natDegree = n := Polynomial.natDegree_X_pow_sub_C
    have h1 := Polynomial.Splits.natDegree_eq_card_roots hsplit
    rw [hdeg] at h1
    exact h1.symm
  · rw [Polynomial.nthRoots]
    exact Polynomial.nodup_roots (Polynomial.separable_X_pow_sub_C w hnK hw)

def T (l₁ l₂ d : F2 q) : Set (K × K) :=
  {u | u.1 ^ q ^ 2 = ι q K l₁ * u.1 ∧ u.2 ^ q ^ 2 = ι q K l₂ * u.2 ∧
    u.1 ^ (q + 1) - u.2 ^ (q + 1) = ι q K d}

variable {q K}

theorem pow_succ_pow_of_twist {u : K} {l : F2 q} (hu : u ^ q ^ 2 = ι q K l * u) (hu0 : u ≠ 0) :
    (u ^ (q + 1)) ^ q = ι q K l * u ^ (q + 1) := by
  have hq1 := hq.out.one_lt
  have h1 : u ^ (q ^ 2 - 1) = ι q K l := by
    have : u ^ q ^ 2 = u ^ (q ^ 2 - 1) * u := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_pow _ _ hq.out.pos)]
    rw [this] at hu
    exact mul_right_cancel₀ hu0 hu
  have h2 : (q + 1) * q = (q ^ 2 - 1) + (q + 1) := by
    zify [Nat.one_le_pow 2 q hq.out.pos]; ring
  rw [← pow_mul, h2, pow_add, h1]

theorem twist_of_pow_succ {u : K} {l w : F2 q} (hu : u ^ (q + 1) = ι q K w) (hw : w ^ q = l * w) (hw0 : w ≠ 0) :
    u ^ q ^ 2 = ι q K l * u := by
  have hq1 := hq.out.one_lt
  have hwl : w ^ (q - 1) = l := by
    have : w ^ q = w ^ (q - 1) * w := by rw [← pow_succ, Nat.sub_add_cancel hq1.le]
    rw [this] at hw
    exact mul_right_cancel₀ hw0 hw
  have h2 : q ^ 2 = (q + 1) * (q - 1) + 1 := by zify [hq1.le]; ring
  rw [h2, pow_add, pow_one, pow_mul, hu, ← map_pow, hwl]

variable {l₁ l₂ d : F2 q} (h12 : l₁ ≠ l₂) (hl1 : l₁ ^ (q + 1) = 1) (hl2 : l₂ ^ (q + 1) = 1)
  (hd : d ^ q = -d) (hd0 : d ≠ 0)

include h12 in

theorem eq_w_of_twist {W₁ W₂ : K} (h1 : W₁ ^ q = ι q K l₁ * W₁) (h2 : W₂ ^ q = ι q K l₂ * W₂)
    (hdiff : W₁ - W₂ = ι q K d) : W₁ = ι q K (w₁ l₁ l₂ d) ∧ W₂ = ι q K (w₂ l₁ l₂ d) := by
  haveI := charP_K q K
  have hW₂ : W₂ = W₁ - ι q K d := by rw [← hdiff]; ring
  have key : (ι q K l₁ - ι q K l₂) * W₁ = ι q K (d ^ q - l₂ * d) := by
    have := h2
    rw [hW₂, sub_pow_char, h1, ← map_pow, mul_sub] at this
    rw [map_sub, map_mul]
    linear_combination this
  have hne : ι q K l₁ - ι q K l₂ ≠ 0 := by
    rw [← map_sub]; exact (_root_.map_ne_zero _).mpr (sub_ne_zero.mpr h12)
  have hW₁ : W₁ = ι q K (w₁ l₁ l₂ d) := by
    rw [w₁, map_div₀, map_sub (ι q K) l₁, eq_div_iff hne, mul_comm]
    exact key
  exact ⟨hW₁, by rw [hW₂, hW₁, w₂, map_sub]⟩

include h12 hl1 hl2 hd hd0 in

theorem ncard_T [IsAlgClosed K] :
    ((l₁ = -1 ∨ l₂ = -1) → (T q K l₁ l₂ d).ncard = q + 1) ∧
    (¬ (l₁ = -1 ∨ l₂ = -1) → (T q K l₁ l₂ d).ncard = (q + 1) ^ 2) := by
  classical
  haveI := charP_K q K
  have hqK := cast_succ_ne_zero q K
  have hι0 : ∀ {z : F2 q}, z ≠ 0 → ι q K z ≠ 0 := fun hz => (_root_.map_ne_zero _).mpr hz

  have anal : ∀ u : K × K, u ∈ T q K l₁ l₂ d →
      (u.2 = 0 ∧ l₁ = -1 ∧ u.1 ^ (q + 1) = ι q K d) ∨
      (u.1 = 0 ∧ l₂ = -1 ∧ u.2 ^ (q + 1) = ι q K (-d)) ∨
      (u.1 ≠ 0 ∧ u.2 ≠ 0 ∧ u.1 ^ (q + 1) = ι q K (w₁ l₁ l₂ d) ∧ u.2 ^ (q + 1) = ι q K (w₂ l₁ l₂ d)) := by
    rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
    dsimp only at ha hb hab ⊢
    by_cases hb0 : b = 0
    ·
      left
      subst hb0
      rw [zero_pow (Nat.succ_ne_zero q), sub_zero] at hab
      have ha0 : a ≠ 0 := by
        rintro rfl; rw [zero_pow (Nat.succ_ne_zero q)] at hab; exact hι0 hd0 hab.symm
      refine ⟨rfl, ?_, hab⟩
      have h := pow_succ_pow_of_twist ha ha0
      rw [hab, ← map_pow, ← map_mul, hd] at h
      have h' := (ι q K).injective h

      have : (l₁ + 1) * d = 0 := by linear_combination -h'
      rcases mul_eq_zero.mp this with h1 | h1
      · exact add_eq_zero_iff_eq_neg.mp h1
      · exact absurd h1 hd0
    by_cases ha0 : a = 0
    · right; left
      subst ha0
      rw [zero_pow (Nat.succ_ne_zero q), zero_sub, neg_eq_iff_eq_neg, ← map_neg] at hab
      refine ⟨rfl, ?_, hab⟩
      have h := pow_succ_pow_of_twist hb hb0
      rw [hab, ← map_pow, ← map_mul, neg_pow_q, hd, neg_neg] at h
      have h' := (ι q K).injective h

      have : (l₂ + 1) * d = 0 := by linear_combination h'
      rcases mul_eq_zero.mp this with h1 | h1
      · exact add_eq_zero_iff_eq_neg.mp h1
      · exact absurd h1 hd0
    · right; right
      have h1 := pow_succ_pow_of_twist ha ha0
      have h2 := pow_succ_pow_of_twist hb hb0
      obtain ⟨e1, e2⟩ := eq_w_of_twist h12 h1 h2 hab
      exact ⟨ha0, hb0, e1, e2⟩
  constructor
  · intro hs
    rcases hs with hs1 | hs2
    ·
      have hl2' : l₂ ≠ -1 := fun h => h12 (hs1.trans h.symm)
      have hT : T q K l₁ l₂ d = (fun a : K => (a, (0 : K))) '' {a : K | a ^ (q + 1) = ι q K d} := by
        ext ⟨a, b⟩
        constructor
        · intro hu
          rcases anal _ hu with ⟨hb, -, ha⟩ | ⟨-, h2, -⟩ | ⟨-, hb0, -, hbw⟩
          · simp only at hb ha; exact ⟨a, ha, by rw [hb]⟩
          · exact absurd h2 hl2'
          · exfalso; apply hb0
            have : w₂ l₁ l₂ d = 0 := (w₂_eq_zero_iff h12 hd).mpr (Or.inr hs1)
            rw [this, map_zero] at hbw
            exact pow_eq_zero_iff (Nat.succ_ne_zero q) |>.mp hbw
        · rintro ⟨a', ha', h⟩
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨?_, by rw [mul_zero, zero_pow (pow_ne_zero _ hq.out.ne_zero)], by simpa using ha'⟩

          exact twist_of_pow_succ ha' (by rw [hd, hs1]; ring) hd0
      have hinj : Function.Injective (fun a : K => (a, (0 : K))) := fun a a' h => (Prod.ext_iff.mp h).1
      rw [hT, Set.ncard_image_of_injective _ hinj]
      exact ncard_setOf_pow_eq K (q + 1) (Nat.succ_pos q) hqK (hι0 hd0)
    ·
      have hl1' : l₁ ≠ -1 := fun h => h12 (h.trans hs2.symm)
      have hT : T q K l₁ l₂ d = (fun b : K => ((0 : K), b)) '' {b : K | b ^ (q + 1) = ι q K (-d)} := by
        ext ⟨a, b⟩
        constructor
        · intro hu
          rcases anal _ hu with ⟨-, h1, -⟩ | ⟨ha, -, hb⟩ | ⟨ha0, -, haw, -⟩
          · exact absurd h1 hl1'
          · simp only at ha hb; exact ⟨b, hb, by rw [ha]⟩
          · exfalso; apply ha0
            have : w₁ l₁ l₂ d = 0 := (w₁_eq_zero_iff h12 hd).mpr (Or.inr hs2)
            rw [this, map_zero] at haw
            exact pow_eq_zero_iff (Nat.succ_ne_zero q) |>.mp haw
        · rintro ⟨b', hb', h⟩
          simp only [Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨by rw [mul_zero, zero_pow (pow_ne_zero _ hq.out.ne_zero)], ?_, ?_⟩
          · refine twist_of_pow_succ hb' ?_ (neg_ne_zero.mpr hd0)
            rw [neg_pow_q, hd, hs2]; ring
          · show (0 : K) ^ (q + 1) - b' ^ (q + 1) = ι q K d
            rw [hb', zero_pow (Nat.succ_ne_zero q), zero_sub, map_neg, neg_neg]
      have hinj : Function.Injective (fun b : K => ((0 : K), b)) := fun b b' h => (Prod.ext_iff.mp h).2
      rw [hT, Set.ncard_image_of_injective _ hinj]
      exact ncard_setOf_pow_eq K (q + 1) (Nat.succ_pos q) hqK (hι0 (neg_ne_zero.mpr hd0))
  · intro hs
    push Not at hs
    have hw10 : w₁ l₁ l₂ d ≠ 0 := fun h => by
      rcases (w₁_eq_zero_iff h12 hd).mp h with h | h
      · exact hd0 h
      · exact hs.2 h
    have hw20 : w₂ l₁ l₂ d ≠ 0 := fun h => by
      rcases (w₂_eq_zero_iff h12 hd).mp h with h | h
      · exact hd0 h
      · exact hs.1 h
    have hT : T q K l₁ l₂ d = {a : K | a ^ (q + 1) = ι q K (w₁ l₁ l₂ d)} ×ˢ {b : K | b ^ (q + 1) = ι q K (w₂ l₁ l₂ d)} := by
      ext ⟨a, b⟩
      rw [Set.mem_prod, Set.mem_setOf_eq, Set.mem_setOf_eq]
      constructor
      · intro hu
        rcases anal _ hu with ⟨-, h1, -⟩ | ⟨-, h2, -⟩ | ⟨-, -, ha, hb⟩
        · exact absurd h1 hs.1
        · exact absurd h2 hs.2
        · exact ⟨ha, hb⟩
      · rintro ⟨ha, hb⟩
        refine ⟨twist_of_pow_succ ha (w₁_pow h12 hl1 hl2 hd) hw10, twist_of_pow_succ hb (w₂_pow h12 hl1 hl2 hd) hw20, ?_⟩
        show a ^ (q + 1) - b ^ (q + 1) = ι q K d
        rw [ha, hb, w₂, map_sub, sub_sub_cancel]
    rw [hT, Set.ncard_prod, ncard_setOf_pow_eq K (q + 1) (Nat.succ_pos q) hqK (hι0 hw10),
      ncard_setOf_pow_eq K (q + 1) (Nat.succ_pos q) hqK (hι0 hw20), sq]

end Closed

end EllForm

end DrinfeldCurve

open DrinfeldCurve.EllForm in
theorem solution
    (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] [Algebra (GaloisField q 2) K] [IsAlgClosed K]
    (l₁ l₂ d : GaloisField q 2) (h12 : l₁ ≠ l₂) (hl1 : l₁ ^ (q + 1) = 1) (hl2 : l₂ ^ (q + 1) = 1)
    (hd : d ^ q = -d) (hd0 : d ≠ 0) :
    ((l₁ = -1 ∨ l₂ = -1) →
      {u : K × K | u.1 ^ q ^ 2 = algebraMap (GaloisField q 2) K l₁ * u.1 ∧
          u.2 ^ q ^ 2 = algebraMap (GaloisField q 2) K l₂ * u.2 ∧
          u.1 ^ (q + 1) - u.2 ^ (q + 1) = algebraMap (GaloisField q 2) K d}.ncard = q + 1) ∧
    (¬ (l₁ = -1 ∨ l₂ = -1) →
      {u : K × K | u.1 ^ q ^ 2 = algebraMap (GaloisField q 2) K l₁ * u.1 ∧
          u.2 ^ q ^ 2 = algebraMap (GaloisField q 2) K l₂ * u.2 ∧
          u.1 ^ (q + 1) - u.2 ^ (q + 1) = algebraMap (GaloisField q 2) K d}.ncard = (q + 1) ^ 2) :=
  ncard_T (K := K) h12 hl1 hl2 hd hd0

end S_DrinfeldCurve_ncard_setOf_ellTwistedFrobenius_affineFixed
end P2MW
export P2MW.S_DrinfeldCurve_ncard_setOf_ellTwistedFrobenius_affineFixed (solution)
