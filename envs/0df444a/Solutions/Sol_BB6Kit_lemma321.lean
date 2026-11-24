-- Prove2me | solution 1 for BB6Kit.lemma321
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-24T16:21:51.899464+00:00
-- url     : https://prove2.me/submissions/485a6cfb-5aef-4805-81c9-9a3fc0fca519

import Mathlib

open Finset

namespace L321

def d1 (x y : ℕ × ℕ × ℕ) : ℤ := (x.1 : ℤ) - y.1
def d2 (x y : ℕ × ℕ × ℕ) : ℤ := (x.2.1 : ℤ) - y.2.1
def d3 (x y : ℕ × ℕ × ℕ) : ℤ := (x.2.2 : ℤ) - y.2.2

/-- Naturals in `[0,S]` that are pairwise congruent mod `a` number at most `S/a + 1`. -/
lemma count_mod (s : Finset ℕ) (S a : ℕ) (ha : 0 < a) (hs : ∀ x ∈ s, x ≤ S)
    (hd : ∀ x ∈ s, ∀ y ∈ s, (a : ℤ) ∣ (x : ℤ) - y) : s.card ≤ S / a + 1 := by
  have h := Finset.card_le_card_of_injOn (fun x => x / a) (t := Finset.range (S / a + 1))
    (by
      intro x hx
      simp only [coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right (hs x hx)))
    (by
      intro x hx y hy hxy
      have hm : y % a = x % a := Nat.modEq_iff_dvd.mpr (hd x hx y hy)
      have hxy' : x / a = y / a := hxy
      rw [← Nat.div_add_mod x a, ← Nat.div_add_mod y a, hxy', hm])
  simpa using h

/-- Generic injection count into `[0,B]`. -/
lemma inj_count {α : Type*} (F : Finset α) (f : α → ℕ) (B : ℕ) (hf : ∀ x ∈ F, f x ≤ B)
    (hinj : ∀ x ∈ F, ∀ y ∈ F, f x = f y → x = y) : F.card ≤ B + 1 := by
  have h := Finset.card_le_card_of_injOn f (t := Finset.range (B + 1))
    (by
      intro x hx
      simp only [coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (hf x hx))
    (by intro x hx y hy hxy; exact hinj x hx y hy hxy)
  simpa using h

lemma numeric (a g S T m : ℤ) (ha : 1 ≤ a) (hg : 1 ≤ g) (haS : a ≤ S) (hgT : g ≤ T)
    (hSm : S ≤ m) (hTm : T ≤ m) :
    (S + a) * (T + g) ≤ (S + 1) * (T + 1) + a * g * m := by
  have t1 : 0 ≤ (m - S) * (g - 1) := mul_nonneg (by linarith) (by linarith)
  have t2 : 0 ≤ (m - T) * (a - 1) := mul_nonneg (by linarith) (by linarith)
  rcases eq_or_lt_of_le ha with h1 | h1
  · subst h1
    nlinarith
  · have t3 : 0 ≤ (g - 1) * ((m - 1) * (a - 1) - 1) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith

/-- Lemma 3.18-type count in the plane: a set of lattice points of the box `[0,S]×[0,T]` lying in
one class of `p s + q t mod d` (with `gcd(d,p,q)=1`) and having at least `S+T+2` points satisfies
`d (#A - max(S,T)) ≤ (S+1)(T+1)`. -/
lemma plane2 (A : Finset (ℕ × ℕ)) (S T d : ℕ) (p q : ℤ) (hd : 0 < d)
    (hbox : ∀ x ∈ A, x.1 ≤ S ∧ x.2 ≤ T)
    (hcong : ∀ x ∈ A, ∀ y ∈ A, (d : ℤ) ∣ p * ((x.1 : ℤ) - y.1) + q * ((x.2 : ℤ) - y.2))
    (hg : Int.gcd (Int.gcd (d : ℤ) p : ℤ) q = 1) (hN : S + T + 2 ≤ A.card) :
    (d : ℤ) * ((A.card : ℤ) - ((max S T : ℕ) : ℤ)) ≤ ((S : ℤ) + 1) * ((T : ℤ) + 1) := by
  obtain ⟨g, hgdef⟩ : ∃ g, g = Int.gcd (d : ℤ) p := ⟨_, rfl⟩
  rw [← hgdef] at hg
  have hg0 : 0 < g := by
    rw [hgdef]; exact Int.gcd_pos_of_ne_zero_left _ (by exact_mod_cast hd.ne')
  have hgd : (g : ℤ) ∣ (d : ℤ) := by rw [hgdef]; exact Int.gcd_dvd_left ..
  have hgp : (g : ℤ) ∣ p := by rw [hgdef]; exact Int.gcd_dvd_right ..
  have hgdN : g ∣ d := by exact_mod_cast hgd
  obtain ⟨a, hadef⟩ : ∃ a, a = d / g := ⟨_, rfl⟩
  have hag : a * g = d := by rw [hadef]; exact Nat.div_mul_cancel hgdN
  have ha0 : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h, zero_mul] at hag; omega
    · exact h
  have hdZ : (d : ℤ) = (a : ℤ) * g := by exact_mod_cast hag.symm
  have hcop : Int.gcd (a : ℤ) (p / g) = 1 := by
    have h := Int.gcd_div_gcd_div_gcd (i := (d : ℤ)) (j := p) (by rw [← hgdef]; exact hg0)
    rw [← hgdef] at h
    have e : (d : ℤ) / (g : ℤ) = (a : ℤ) := by
      rw [hdZ]; exact Int.mul_ediv_cancel _ (by exact_mod_cast hg0.ne')
    rw [e] at h
    exact h
  have hrow : ∀ x ∈ A, ∀ y ∈ A, (g : ℤ) ∣ (x.2 : ℤ) - y.2 := by
    intro x hx y hy
    have h1 : (g : ℤ) ∣ p * ((x.1 : ℤ) - y.1) + q * ((x.2 : ℤ) - y.2) :=
      dvd_trans hgd (hcong x hx y hy)
    have h3 : (g : ℤ) ∣ p * ((x.1 : ℤ) - y.1) := dvd_mul_of_dvd_left hgp _
    have h2 : (g : ℤ) ∣ q * ((x.2 : ℤ) - y.2) := (dvd_add_right h3).mp h1
    exact Int.dvd_of_dvd_mul_right_of_gcd_one h2 hg
  have hcol : ∀ x ∈ A, ∀ y ∈ A, x.2 = y.2 → (a : ℤ) ∣ (x.1 : ℤ) - y.1 := by
    intro x hx y hy he
    have h1 := hcong x hx y hy
    rw [he, sub_self, mul_zero, add_zero] at h1
    have e : (p / g * ((x.1 : ℤ) - y.1)) * g = p * ((x.1 : ℤ) - y.1) := by
      rw [mul_right_comm, Int.ediv_mul_cancel hgp]
    have h1' : (a : ℤ) * g ∣ (p / g * ((x.1 : ℤ) - y.1)) * g := by
      rw [e, ← hdZ]; exact h1
    have hg0' : (g : ℤ) ≠ 0 := by exact_mod_cast hg0.ne'
    have h4 : (a : ℤ) ∣ p / g * ((x.1 : ℤ) - y.1) := (mul_dvd_mul_iff_right hg0').mp h1'
    exact Int.dvd_of_dvd_mul_right_of_gcd_one h4 hcop
  have hrows : (A.image Prod.snd).card ≤ T / g + 1 := by
    apply count_mod _ T g hg0
    · intro t ht
      obtain ⟨x, hx, rfl⟩ := mem_image.mp ht
      exact (hbox x hx).2
    · intro t ht t' ht'
      obtain ⟨x, hx, rfl⟩ := mem_image.mp ht
      obtain ⟨y, hy, rfl⟩ := mem_image.mp ht'
      exact hrow x hx y hy
  have hfib : ∀ t ∈ A.image Prod.snd, (A.filter (fun x => Prod.snd x = t)).card ≤ S / a + 1 := by
    intro t _
    rw [← card_image_of_injOn (f := Prod.fst) (s := A.filter (fun x => Prod.snd x = t))]
    · apply count_mod _ S a ha0
      · intro r hr
        obtain ⟨x, hx, rfl⟩ := mem_image.mp hr
        exact (hbox x (mem_filter.mp hx).1).1
      · intro r hr r' hr'
        obtain ⟨x, hx, rfl⟩ := mem_image.mp hr
        obtain ⟨y, hy, rfl⟩ := mem_image.mp hr'
        rw [mem_filter] at hx hy
        exact hcol x hx.1 y hy.1 (hx.2.trans hy.2.symm)
    · intro x hx y hy hxy
      have hx' := mem_filter.mp (mem_coe.mp hx)
      have hy' := mem_filter.mp (mem_coe.mp hy)
      exact Prod.ext hxy (hx'.2.trans hy'.2.symm)
  have hcard : A.card ≤ (S / a + 1) * (A.image Prod.snd).card :=
    card_le_mul_card_image (f := Prod.snd) A (S / a + 1) hfib
  have hxa : S / a * a ≤ S := Nat.div_mul_le_self S a
  have hyg : T / g * g ≤ T := Nat.div_mul_le_self T g
  obtain ⟨x, hxdef⟩ : ∃ x, x = S / a := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ y, y = T / g := ⟨_, rfl⟩
  rw [← hxdef] at hcard hxa
  rw [← hydef] at hrows hyg
  have hN2 : A.card ≤ (x + 1) * (y + 1) := le_trans hcard (Nat.mul_le_mul_left _ hrows)
  have hyT : y ≤ T := by nlinarith
  have hxS : x ≤ S := by nlinarith
  have hx1 : 1 ≤ x := by
    by_contra h0
    have hx0 : x = 0 := by omega
    rw [hx0] at hN2
    omega
  have hy1 : 1 ≤ y := by
    by_contra h0
    have hy0 : y = 0 := by omega
    rw [hy0] at hN2
    omega
  have haS : a ≤ S := by nlinarith
  have hgT : g ≤ T := by nlinarith
  -- integer bookkeeping
  have hN2' : (A.card : ℤ) ≤ ((x : ℤ) + 1) * ((y : ℤ) + 1) := by exact_mod_cast hN2
  have hxa' : (x : ℤ) * a ≤ S := by exact_mod_cast hxa
  have hyg' : (y : ℤ) * g ≤ T := by exact_mod_cast hyg
  have hSm : (S : ℤ) ≤ ((max S T : ℕ) : ℤ) := by exact_mod_cast le_max_left S T
  have hTm : (T : ℤ) ≤ ((max S T : ℕ) : ℤ) := by exact_mod_cast le_max_right S T
  have key := numeric a g S T ((max S T : ℕ) : ℤ) (by exact_mod_cast ha0) (by exact_mod_cast hg0)
    (by exact_mod_cast haS) (by exact_mod_cast hgT) hSm hTm
  have step1 : (d : ℤ) * ((A.card : ℤ) - ((max S T : ℕ) : ℤ)) ≤
      (d : ℤ) * (((x : ℤ) + 1) * ((y : ℤ) + 1) - ((max S T : ℕ) : ℤ)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have p1 : ((x : ℤ) + 1) * a ≤ S + a := by linarith
  have p2 : ((y : ℤ) + 1) * g ≤ T + g := by linarith
  have prod : (((x : ℤ) + 1) * a) * (((y : ℤ) + 1) * g) ≤ ((S : ℤ) + a) * ((T : ℤ) + g) :=
    mul_le_mul p1 p2 (by positivity) (by positivity)
  rw [hdZ] at step1 ⊢
  nlinarith [step1, prod, key]

/-- Projection along the first coordinate of a plane with primitive integer normal. -/
lemma proj3 {α : Type*} [DecidableEq α] (F : Finset α) (φ : α → ℤ) (π1 π2 : α → ℕ) (S T : ℕ)
    (u1 u2 u3 : ℤ) (hbox : ∀ x ∈ F, π1 x ≤ S ∧ π2 x ≤ T)
    (hinj : ∀ x ∈ F, ∀ y ∈ F, φ x = φ y → π1 x = π1 y → π2 x = π2 y → x = y)
    (heq : ∀ x ∈ F, ∀ y ∈ F,
      u1 * (φ x - φ y) + u2 * ((π1 x : ℤ) - π1 y) + u3 * ((π2 x : ℤ) - π2 y) = 0)
    (hg : Int.gcd (Int.gcd u1 u2 : ℤ) u3 = 1) (hN : S + T + 2 ≤ F.card) :
    |u1| * ((F.card : ℤ) - ((max S T : ℕ) : ℤ)) ≤ ((S : ℤ) + 1) * ((T : ℤ) + 1) := by
  rcases eq_or_ne u1 0 with h0 | h0
  · rw [h0, abs_zero, zero_mul]; positivity
  have hinjA : Set.InjOn (fun x => (π1 x, π2 x)) (F : Set α) := by
    intro x hx y hy hxy
    simp only [Prod.mk.injEq] at hxy
    apply hinj x hx y hy _ hxy.1 hxy.2
    have h := heq x hx y hy
    rw [hxy.1, hxy.2, sub_self, sub_self, mul_zero, mul_zero, add_zero, add_zero] at h
    have h' := (mul_eq_zero.mp h).resolve_left h0
    linarith
  have hcardA : (F.image (fun x => (π1 x, π2 x))).card = F.card := card_image_of_injOn hinjA
  have hres := plane2 (F.image (fun x => (π1 x, π2 x))) S T u1.natAbs u2 u3
    (Int.natAbs_pos.mpr h0) ?_ ?_ ?_ (by rw [hcardA]; exact hN)
  · rw [hcardA, Int.natCast_natAbs] at hres
    exact hres
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    exact hbox x hx
  · intro z hz w hw
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hz
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hw
    show ((u1.natAbs : ℕ) : ℤ) ∣ u2 * ((π1 x : ℤ) - π1 y) + u3 * ((π2 x : ℤ) - π2 y)
    have h1 : ((u1.natAbs : ℕ) : ℤ) ∣ u1 * (φ x - φ y) :=
      dvd_mul_of_dvd_left (Int.natAbs_dvd.mpr dvd_rfl) _
    have e : u2 * ((π1 x : ℤ) - π1 y) + u3 * ((π2 x : ℤ) - π2 y) = -(u1 * (φ x - φ y)) := by
      linarith [heq x hx y hy]
    rw [e]
    exact (dvd_neg).mpr h1
  · have e : Int.gcd ((u1.natAbs : ℕ) : ℤ) u2 = Int.gcd u1 u2 := by
      simp [Int.gcd, Int.natAbs_abs]
    rw [e]
    exact hg

lemma det_zero (n1 n2 n3 a1 a2 a3 c1 c2 c3 z1 z2 z3 : ℝ) (hn : n1 ≠ 0 ∨ n2 ≠ 0)
    (ha : n1 * a1 + n2 * a2 + n3 * a3 = 0) (hc : n1 * c1 + n2 * c2 + n3 * c3 = 0)
    (hz : n1 * z1 + n2 * z2 + n3 * z3 = 0) :
    (a2 * c3 - a3 * c2) * z1 + (a3 * c1 - a1 * c3) * z2 + (a1 * c2 - a2 * c1) * z3 = 0 := by
  rcases hn with h | h
  · have e : n1 * ((a2 * c3 - a3 * c2) * z1 + (a3 * c1 - a1 * c3) * z2 + (a1 * c2 - a2 * c1) * z3) = 0 := by
      linear_combination (c2 * z3 - c3 * z2) * ha - (a2 * z3 - a3 * z2) * hc + (a2 * c3 - a3 * c2) * hz
    exact (mul_eq_zero.mp e).resolve_left h
  · have e : n2 * ((a2 * c3 - a3 * c2) * z1 + (a3 * c1 - a1 * c3) * z2 + (a1 * c2 - a2 * c1) * z3) = 0 := by
      linear_combination (c3 * z1 - c1 * z3) * ha - (a3 * z1 - a1 * z3) * hc + (a3 * c1 - a1 * c3) * hz
    exact (mul_eq_zero.mp e).resolve_left h

/-- One fibre of the projection has at most `M` points, unless (2.15) holds. -/
lemma fibre_bound (F : Finset (ℕ × ℕ × ℕ)) (R S T b1 b2 b3 : ℕ) (n1 n2 n3 M : ℝ)
    (hbox : ∀ x ∈ F, x.1 ≤ R ∧ x.2.1 ≤ S ∧ x.2.2 ≤ T)
    (hn : n1 ≠ 0 ∨ n2 ≠ 0)
    (hpl : ∀ x ∈ F, ∀ y ∈ F,
      n1 * ((x.1 : ℝ) - y.1) + n2 * ((x.2.1 : ℝ) - y.2.1) + n3 * ((x.2.2 : ℝ) - y.2.2) = 0)
    (hb : n1 * b1 + n2 * b2 + n3 * (-(b3 : ℝ)) = 0)
    (hM1 : (R : ℝ) + S + 1 ≤ M) (hM2 : (S : ℝ) + T + 1 ≤ M) (hM3 : (R : ℝ) + T + 1 ≤ M)
    (h215 : ¬ (∃ u1 u2 u3 : ℤ, u1 * (b1 : ℤ) + u2 * (b2 : ℤ) + u3 * (b3 : ℤ) = 0 ∧
        Int.gcd (Int.gcd u1 u2 : ℤ) u3 = 1 ∧
        (|u1| : ℝ) ≤ ((S : ℝ) + 1) * ((T : ℝ) + 1) / (M - max (S : ℝ) T) ∧
        (|u2| : ℝ) ≤ ((R : ℝ) + 1) * ((T : ℝ) + 1) / (M - max (R : ℝ) T) ∧
        (|u3| : ℝ) ≤ ((R : ℝ) + 1) * ((S : ℝ) + 1) / (M - max (R : ℝ) S))) :
    (F.card : ℝ) ≤ M := by
  by_contra hlt
  push_neg at hlt
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  have hT0 : (0 : ℝ) ≤ T := Nat.cast_nonneg _
  have hc1 : R + S + 2 ≤ F.card := by
    have h : ((R + S + 1 : ℕ) : ℝ) < F.card := by push_cast; linarith
    have := Nat.cast_lt.mp h; omega
  have hc2 : S + T + 2 ≤ F.card := by
    have h : ((S + T + 1 : ℕ) : ℝ) < F.card := by push_cast; linarith
    have := Nat.cast_lt.mp h; omega
  have hc3 : R + T + 2 ≤ F.card := by
    have h : ((R + T + 1 : ℕ) : ℝ) < F.card := by push_cast; linarith
    have := Nat.cast_lt.mp h; omega
  have hpl' : ∀ x ∈ F, ∀ y ∈ F,
      n1 * ((d1 x y : ℤ) : ℝ) + n2 * ((d2 x y : ℤ) : ℝ) + n3 * ((d3 x y : ℤ) : ℝ) = 0 := by
    intro x hx y hy
    simp only [d1, d2, d3]
    push_cast
    exact hpl x hx y hy
  obtain ⟨x0, hx0⟩ : F.Nonempty := card_pos.mp (by omega)
  by_cases hnc : ∃ x1 ∈ F, ∃ x2 ∈ F,
      ¬ (d2 x1 x0 * d3 x2 x0 - d3 x1 x0 * d2 x2 x0 = 0 ∧
         d3 x1 x0 * d1 x2 x0 - d1 x1 x0 * d3 x2 x0 = 0 ∧
         d1 x1 x0 * d2 x2 x0 - d2 x1 x0 * d1 x2 x0 = 0)
  · obtain ⟨x1, hx1, x2, hx2, hw⟩ := hnc
    obtain ⟨w1, hw1⟩ : ∃ w, w = d2 x1 x0 * d3 x2 x0 - d3 x1 x0 * d2 x2 x0 := ⟨_, rfl⟩
    obtain ⟨w2, hw2⟩ : ∃ w, w = d3 x1 x0 * d1 x2 x0 - d1 x1 x0 * d3 x2 x0 := ⟨_, rfl⟩
    obtain ⟨w3, hw3⟩ : ∃ w, w = d1 x1 x0 * d2 x2 x0 - d2 x1 x0 * d1 x2 x0 := ⟨_, rfl⟩
    rw [← hw1, ← hw2, ← hw3] at hw
    have hperp : ∀ z1 z2 z3 : ℤ, n1 * (z1 : ℝ) + n2 * (z2 : ℝ) + n3 * (z3 : ℝ) = 0 →
        w1 * z1 + w2 * z2 + w3 * z3 = 0 := by
      intro z1 z2 z3 hz
      have hR := det_zero n1 n2 n3 (d1 x1 x0) (d2 x1 x0) (d3 x1 x0) (d1 x2 x0) (d2 x2 x0)
        (d3 x2 x0) z1 z2 z3 hn (hpl' x1 hx1 x0 hx0) (hpl' x2 hx2 x0 hx0) hz
      have h : ((w1 * z1 + w2 * z2 + w3 * z3 : ℤ) : ℝ) = 0 := by
        rw [hw1, hw2, hw3]; push_cast; linear_combination hR
      exact_mod_cast h
    -- primitive normal
    obtain ⟨G, hGdef⟩ : ∃ G, G = Int.gcd (Int.gcd w1 w2 : ℤ) w3 := ⟨_, rfl⟩
    have hG0 : 0 < G := by
      apply Nat.pos_of_ne_zero
      intro h0
      rw [hGdef, Int.gcd_eq_zero_iff] at h0
      obtain ⟨h12, h3⟩ := h0
      have h12' : Int.gcd w1 w2 = 0 := by exact_mod_cast h12
      rw [Int.gcd_eq_zero_iff] at h12'
      exact hw ⟨h12'.1, h12'.2, h3⟩
    have hGne : (G : ℤ) ≠ 0 := by exact_mod_cast hG0.ne'
    have hGd1 : (G : ℤ) ∣ w1 := by
      rw [hGdef]; exact dvd_trans (Int.gcd_dvd_left ..) (Int.gcd_dvd_left ..)
    have hGd2 : (G : ℤ) ∣ w2 := by
      rw [hGdef]; exact dvd_trans (Int.gcd_dvd_left ..) (Int.gcd_dvd_right ..)
    have hGd3 : (G : ℤ) ∣ w3 := by
      rw [hGdef]; exact Int.gcd_dvd_right ..
    obtain ⟨u1, hu1⟩ : ∃ u, u = w1 / G := ⟨_, rfl⟩
    obtain ⟨u2, hu2⟩ : ∃ u, u = w2 / G := ⟨_, rfl⟩
    obtain ⟨u3, hu3⟩ : ∃ u, u = w3 / G := ⟨_, rfl⟩
    have e1 : w1 = u1 * G := by rw [hu1, Int.ediv_mul_cancel hGd1]
    have e2 : w2 = u2 * G := by rw [hu2, Int.ediv_mul_cancel hGd2]
    have e3 : w3 = u3 * G := by rw [hu3, Int.ediv_mul_cancel hGd3]
    have huperp : ∀ z1 z2 z3 : ℤ, n1 * (z1 : ℝ) + n2 * (z2 : ℝ) + n3 * (z3 : ℝ) = 0 →
        u1 * z1 + u2 * z2 + u3 * z3 = 0 := by
      intro z1 z2 z3 hz
      have h := hperp z1 z2 z3 hz
      rw [e1, e2, e3] at h
      have h' : (u1 * z1 + u2 * z2 + u3 * z3) * G = 0 := by linear_combination h
      exact (mul_eq_zero.mp h').resolve_right hGne
    have hugcd : Int.gcd (Int.gcd u1 u2 : ℤ) u3 = 1 := by
      obtain ⟨h, hhdef⟩ : ∃ h, h = Int.gcd (Int.gcd u1 u2 : ℤ) u3 := ⟨_, rfl⟩
      rw [← hhdef]
      have hh1 : (h : ℤ) ∣ u1 := by
        rw [hhdef]; exact dvd_trans (Int.gcd_dvd_left ..) (Int.gcd_dvd_left ..)
      have hh2 : (h : ℤ) ∣ u2 := by
        rw [hhdef]; exact dvd_trans (Int.gcd_dvd_left ..) (Int.gcd_dvd_right ..)
      have hh3 : (h : ℤ) ∣ u3 := by
        rw [hhdef]; exact Int.gcd_dvd_right ..
      have k1 : (h : ℤ) * G ∣ w1 := by rw [e1]; exact mul_dvd_mul_right hh1 _
      have k2 : (h : ℤ) * G ∣ w2 := by rw [e2]; exact mul_dvd_mul_right hh2 _
      have k3 : (h : ℤ) * G ∣ w3 := by rw [e3]; exact mul_dvd_mul_right hh3 _
      have k12 : (h : ℤ) * G ∣ (Int.gcd w1 w2 : ℤ) := by
        rw [Int.gcd_eq_gcd_ab w1 w2]
        exact dvd_add (dvd_mul_of_dvd_left k1 _) (dvd_mul_of_dvd_left k2 _)
      have kG0 : (h : ℤ) * G ∣ ((Int.gcd (Int.gcd w1 w2 : ℤ) w3 : ℕ) : ℤ) := by
        rw [Int.gcd_eq_gcd_ab (Int.gcd w1 w2 : ℤ) w3]
        exact dvd_add (dvd_mul_of_dvd_left k12 _) (dvd_mul_of_dvd_left k3 _)
      have kG : (h : ℤ) * G ∣ (G : ℤ) := by nth_rewrite 2 [hGdef]; exact kG0
      have h1 : (h : ℤ) ∣ 1 := by
        apply (mul_dvd_mul_iff_right hGne).mp
        rw [one_mul]; exact kG
      have h1' : h ∣ 1 := by exact_mod_cast h1
      exact Nat.dvd_one.mp h1'
    have hrel : u1 * (b1 : ℤ) + u2 * (b2 : ℤ) + (-u3) * (b3 : ℤ) = 0 := by
      have h := huperp b1 b2 (-(b3 : ℤ)) (by push_cast; linarith [hb])
      linear_combination h
    have heqF : ∀ x ∈ F, ∀ y ∈ F, u1 * d1 x y + u2 * d2 x y + u3 * d3 x y = 0 :=
      fun x hx y hy => huperp _ _ _ (hpl' x hx y hy)
    -- the three projections
    have r1 := proj3 F (fun x => (x.1 : ℤ)) (fun x => x.2.1) (fun x => x.2.2) S T u1 u2 u3
      (fun x hx => ⟨(hbox x hx).2.1, (hbox x hx).2.2⟩)
      (by
        intro x _ y _ h1 h2 h3
        try dsimp only at h1 h2 h3
        exact Prod.ext (by exact_mod_cast h1) (Prod.ext h2 h3))
      (by
        intro x hx y hy
        try dsimp only
        have h := heqF x hx y hy
        simp only [d1, d2, d3] at h
        linear_combination h)
      hugcd hc2
    have r2 := proj3 F (fun x => (x.2.1 : ℤ)) (fun x => x.1) (fun x => x.2.2) R T u2 u1 u3
      (fun x hx => ⟨(hbox x hx).1, (hbox x hx).2.2⟩)
      (by
        intro x _ y _ h1 h2 h3
        try dsimp only at h1 h2 h3
        exact Prod.ext h2 (Prod.ext (by exact_mod_cast h1) h3))
      (by
        intro x hx y hy
        try dsimp only
        have h := heqF x hx y hy
        simp only [d1, d2, d3] at h
        linear_combination h)
      (by rw [Int.gcd_comm u2 u1]; exact hugcd) hc3
    have r3 := proj3 F (fun x => (x.2.2 : ℤ)) (fun x => x.1) (fun x => x.2.1) R S u3 u1 u2
      (fun x hx => ⟨(hbox x hx).1, (hbox x hx).2.1⟩)
      (by
        intro x _ y _ h1 h2 h3
        try dsimp only at h1 h2 h3
        exact Prod.ext h2 (Prod.ext h3 (by exact_mod_cast h1)))
      (by
        intro x hx y hy
        try dsimp only
        have h := heqF x hx y hy
        simp only [d1, d2, d3] at h
        linear_combination h)
      (by rw [Int.gcd_assoc, Int.gcd_comm]; exact hugcd) hc1
    have r1' := (Int.cast_le (R := ℝ)).mpr r1
    have r2' := (Int.cast_le (R := ℝ)).mpr r2
    have r3' := (Int.cast_le (R := ℝ)).mpr r3
    push_cast at r1' r2' r3'
    have hp1 : 0 < M - max (S : ℝ) T := by
      have : max (S : ℝ) T < M := max_lt (by linarith) (by linarith)
      linarith
    have hp2 : 0 < M - max (R : ℝ) T := by
      have : max (R : ℝ) T < M := max_lt (by linarith) (by linarith)
      linarith
    have hp3 : 0 < M - max (R : ℝ) S := by
      have : max (R : ℝ) S < M := max_lt (by linarith) (by linarith)
      linarith
    apply h215
    refine ⟨u1, u2, -u3, hrel, ?_, ?_, ?_, ?_⟩
    · have e : Int.gcd (Int.gcd u1 u2 : ℤ) (-u3) = Int.gcd (Int.gcd u1 u2 : ℤ) u3 := by
        simp only [Int.gcd, Int.natAbs_neg]
      rw [e]; exact hugcd
    · rw [le_div_iff₀ hp1]
      calc |(u1 : ℝ)| * (M - max (S : ℝ) T)
          ≤ |(u1 : ℝ)| * ((F.card : ℝ) - max (S : ℝ) T) :=
            mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
        _ ≤ _ := r1'
    · rw [le_div_iff₀ hp2]
      calc |(u2 : ℝ)| * (M - max (R : ℝ) T)
          ≤ |(u2 : ℝ)| * ((F.card : ℝ) - max (R : ℝ) T) :=
            mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
        _ ≤ _ := r2'
    · rw [Int.cast_neg, abs_neg, le_div_iff₀ hp3]
      calc |(u3 : ℝ)| * (M - max (R : ℝ) S)
          ≤ |(u3 : ℝ)| * ((F.card : ℝ) - max (R : ℝ) S) :=
            mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
        _ ≤ _ := r3'
  · -- collinear case
    push_neg at hnc
    obtain ⟨x1, hx1, hne⟩ := exists_mem_ne (by omega : 1 < F.card) x0
    have key : ∀ x ∈ F, d2 x1 x0 * d3 x x0 = d3 x1 x0 * d2 x x0 ∧
        d3 x1 x0 * d1 x x0 = d1 x1 x0 * d3 x x0 ∧ d1 x1 x0 * d2 x x0 = d2 x1 x0 * d1 x x0 := by
      intro x hx
      obtain ⟨h1, h2, h3⟩ := hnc x1 hx1 x hx
      exact ⟨by linarith, by linarith, by linarith⟩
    have hcardle : ∀ B : ℕ, (B : ℝ) + 1 ≤ M → F.card ≤ B + 1 → False := by
      intro B hB hF
      have : (F.card : ℝ) ≤ B + 1 := by exact_mod_cast hF
      linarith
    by_cases ha1 : d1 x1 x0 = 0
    · by_cases ha2 : d2 x1 x0 = 0
      · by_cases ha3 : d3 x1 x0 = 0
        · apply hne
          simp only [d1, d2, d3] at ha1 ha2 ha3
          exact Prod.ext (by omega) (Prod.ext (by omega) (by omega))
        · -- injective in the third coordinate
          apply hcardle T (by linarith)
          apply inj_count F (fun x => x.2.2) T (fun x hx => (hbox x hx).2.2)
          intro x hx y hy hxy
          try dsimp only at hxy
          have kx := key x hx
          have ky := key y hy
          have hd3 : d3 x x0 = d3 y x0 := by simp only [d3]; rw [hxy]
          have e1 : d3 x1 x0 * (d1 x x0 - d1 y x0) = 0 := by
            linear_combination kx.2.1 - ky.2.1 + d1 x1 x0 * hd3
          have e2 : d3 x1 x0 * (d2 x x0 - d2 y x0) = 0 := by
            linear_combination -kx.1 + ky.1 + d2 x1 x0 * hd3
          have f1 := (mul_eq_zero.mp e1).resolve_left ha3
          have f2 := (mul_eq_zero.mp e2).resolve_left ha3
          simp only [d1, d2] at f1 f2
          exact Prod.ext (by omega) (Prod.ext (by omega) hxy)
      · apply hcardle S (by linarith)
        apply inj_count F (fun x => x.2.1) S (fun x hx => (hbox x hx).2.1)
        intro x hx y hy hxy
        try dsimp only at hxy
        have kx := key x hx
        have ky := key y hy
        have hd2 : d2 x x0 = d2 y x0 := by simp only [d2]; rw [hxy]
        have e1 : d2 x1 x0 * (d1 x x0 - d1 y x0) = 0 := by
          linear_combination -kx.2.2 + ky.2.2 + d1 x1 x0 * hd2
        have e3 : d2 x1 x0 * (d3 x x0 - d3 y x0) = 0 := by
          linear_combination kx.1 - ky.1 + d3 x1 x0 * hd2
        have f1 := (mul_eq_zero.mp e1).resolve_left ha2
        have f3 := (mul_eq_zero.mp e3).resolve_left ha2
        simp only [d1, d3] at f1 f3
        exact Prod.ext (by omega) (Prod.ext hxy (by omega))
    · apply hcardle R (by linarith)
      apply inj_count F (fun x => x.1) R (fun x hx => (hbox x hx).1)
      intro x hx y hy hxy
      try dsimp only at hxy
      have kx := key x hx
      have ky := key y hy
      have hd1 : d1 x x0 = d1 y x0 := by simp only [d1]; rw [hxy]
      have e2 : d1 x1 x0 * (d2 x x0 - d2 y x0) = 0 := by
        linear_combination kx.2.2 - ky.2.2 + d2 x1 x0 * hd1
      have e3 : d1 x1 x0 * (d3 x x0 - d3 y x0) = 0 := by
        linear_combination ky.2.1 - kx.2.1 + d3 x1 x0 * hd1
      have f2 := (mul_eq_zero.mp e2).resolve_left ha1
      have f3 := (mul_eq_zero.mp e3).resolve_left ha1
      simp only [d2, d3] at f2 f3
      exact Prod.ext hxy (Prod.ext (by omega) (by omega))

lemma final_count {α : Type*} [DecidableEq α] (box : Finset α) (f : α → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ y, ((box.filter (fun x => f x = y)).card : ℝ) ≤ M) :
    (box.card : ℝ) ≤ M * ((box.image f).card : ℝ) := by
  have hfib : ∀ y ∈ box.image f, (box.filter (fun x => f x = y)).card ≤ ⌊M⌋₊ :=
    fun y _ => Nat.le_floor (h y)
  have hc := card_le_mul_card_image (f := f) box ⌊M⌋₊ hfib
  have hc' : (box.card : ℝ) ≤ (⌊M⌋₊ : ℝ) * ((box.image f).card : ℝ) := by exact_mod_cast hc
  exact le_trans hc' (mul_le_mul_of_nonneg_right (Nat.floor_le hM) (Nat.cast_nonneg _))

end L321

open L321 in
theorem solution (R1 S1 T1 b1 b2 b3 : ℕ) (χ : ℝ) (hR : 0 < R1) (hS : 0 < S1) (hT : 0 < T1)
    (hb1 : 0 < b1) (hb2 : 0 < b2) (hb3 : 0 < b3) (hgcd : Nat.gcd (Nat.gcd b1 b2) b3 = 1) (hχ : 0 < χ)
    (hcard : ((Finset.range (R1 + 1) ×ˢ Finset.range (S1 + 1) ×ˢ Finset.range (T1 + 1)).image (fun x => ((x.1 : ℝ) + x.2.2 * ((b1 : ℝ) / b3), (x.2.1 : ℝ) + x.2.2 * ((b2 : ℝ) / b3)))).card =
      (R1 + 1) * (S1 + 1) * (T1 + 1))
    (h215 : ¬ (∃ u1 u2 u3 : ℤ, u1 * (b1 : ℤ) + u2 * (b2 : ℤ) + u3 * (b3 : ℤ) = 0 ∧ Int.gcd (Int.gcd u1 u2 : ℤ) u3 = 1 ∧
        (|u1| : ℝ) ≤ ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1) / ((max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) - max (S1 : ℝ) T1) ∧
        (|u2| : ℝ) ≤ ((R1 : ℝ) + 1) * ((T1 : ℝ) + 1) / ((max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) - max (R1 : ℝ) T1) ∧
        (|u3| : ℝ) ≤ ((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) / ((max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) - max (R1 : ℝ) S1))) :
    ∀ l m : ℝ, (l, m) ≠ (0, 0) →
      (((R1 + 1) * (S1 + 1) * (T1 + 1) : ℕ) : ℝ) ≤ (max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) *
        (((Finset.range (R1 + 1) ×ˢ Finset.range (S1 + 1) ×ˢ Finset.range (T1 + 1)).image (fun x => l * ((x.1 : ℝ) + x.2.2 * ((b1 : ℝ) / b3)) + m * ((x.2.1 : ℝ) + x.2.2 * ((b2 : ℝ) / b3)))).card : ℝ) := by
  intro l m hlm
  have hM1 : (R1 : ℝ) + S1 + 1 ≤ max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1)))) :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hM2 : (S1 : ℝ) + T1 + 1 ≤ max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1)))) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hM3 : (R1 : ℝ) + T1 + 1 ≤ max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1)))) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hR0 : (0 : ℝ) ≤ R1 := Nat.cast_nonneg _
  have hS0 : (0 : ℝ) ≤ S1 := Nat.cast_nonneg _
  have hb3R : (b3 : ℝ) ≠ 0 := by exact_mod_cast hb3.ne'
  have hinv : (b3 : ℝ) * (b3 : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hb3R
  have hn : l * b3 ≠ 0 ∨ m * b3 ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hlm
    have hl : l = 0 := (mul_eq_zero.mp hc.1).resolve_right hb3R
    have hm : m = 0 := (mul_eq_zero.mp hc.2).resolve_right hb3R
    rw [hl, hm]
  have key := final_count (Finset.range (R1 + 1) ×ˢ Finset.range (S1 + 1) ×ˢ Finset.range (T1 + 1))
    (fun x => l * ((x.1 : ℝ) + x.2.2 * ((b1 : ℝ) / b3)) + m * ((x.2.1 : ℝ) + x.2.2 * ((b2 : ℝ) / b3)))
    (max (max ((R1 : ℝ) + S1 + 1) ((S1 : ℝ) + T1 + 1)) (max ((R1 : ℝ) + T1 + 1) (χ * Real.sqrt (((R1 : ℝ) + 1) * ((S1 : ℝ) + 1) * ((T1 : ℝ) + 1))))) (by linarith)
    (by
      intro y
      apply fibre_bound _ R1 S1 T1 b1 b2 b3 (l * b3) (m * b3) (l * b1 + m * b2) _ _ hn _ _
        hM1 hM2 hM3 h215
      · intro x hx
        have hx' := (mem_filter.mp hx).1
        simp only [mem_product, mem_range] at hx'
        omega
      · intro x hx z hz
        have ex := (mem_filter.mp hx).2
        have ez := (mem_filter.mp hz).2
        have e := ex.trans ez.symm
        rw [div_eq_mul_inv, div_eq_mul_inv] at e
        linear_combination (b3 : ℝ) * e - (l * b1 + m * b2) * ((x.2.2 : ℝ) - z.2.2) * hinv
      · ring)
  refine le_trans (le_of_eq ?_) key
  simp only [card_product, card_range]
  push_cast
  ring
