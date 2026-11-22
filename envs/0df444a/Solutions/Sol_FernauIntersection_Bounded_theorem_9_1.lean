-- Prove2me | solution 1 for FernauIntersection.Bounded.theorem_9_1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T08:17:36.511361+00:00
-- url     : https://prove2.me/submissions/c2c992e8-c9a5-4edf-bcd9-2421cf3e7c69

import Mathlib

theorem solution (k : ℕ) (m : Fin k → ℕ) (hm : ∀ i, 0 < m i) (r : Fin k → ℤ) :
    ((∃ x : ℤ, ∀ i, x ≡ r i [ZMOD (m i : ℤ)]) ↔
        ∀ i j, i ≠ j → ((Nat.gcd (m i) (m j) : ℕ) : ℤ) ∣ r i - r j) ∧
      (∀ x y : ℤ, (∀ i, x ≡ r i [ZMOD (m i : ℤ)]) → (∀ i, y ≡ r i [ZMOD (m i : ℤ)]) →
        x ≡ y [ZMOD ((Finset.univ.lcm m : ℕ) : ℤ)]) ∧
      ((∃ x : ℕ, ∀ i, (x : ℤ) ≡ r i [ZMOD (m i : ℤ)]) ↔
        ∀ i j, r i ≡ r j [ZMOD ((Nat.gcd (m i) (m j) : ℕ) : ℤ)]) := by
  -- gcd-lcm distributivity
  have hgcd_lcm : ∀ a b c : ℕ, a ≠ 0 → b ≠ 0 → c ≠ 0 →
      Nat.gcd (Nat.lcm a b) c = Nat.lcm (Nat.gcd a c) (Nat.gcd b c) := by
    intro a b c ha hb hc
    apply Nat.eq_of_factorization_eq
    · exact Nat.gcd_ne_zero_left (Nat.lcm_ne_zero ha hb)
    · exact Nat.lcm_ne_zero (Nat.gcd_ne_zero_right hc) (Nat.gcd_ne_zero_right hc)
    intro p
    rw [Nat.factorization_gcd (Nat.lcm_ne_zero ha hb) hc, Nat.factorization_lcm ha hb,
      Nat.factorization_lcm (Nat.gcd_ne_zero_right hc) (Nat.gcd_ne_zero_right hc),
      Nat.factorization_gcd ha hc, Nat.factorization_gcd hb hc]
    simp only [Finsupp.sup_apply, Finsupp.inf_apply]
    omega
  -- lcm of the moduli is nonzero
  have hlcm_ne : ∀ s : Finset (Fin k), s.lcm m ≠ 0 := by
    intro s h0
    have hdvd : s.lcm m ∣ ∏ i ∈ s, m i :=
      Finset.lcm_dvd (fun i hi => Finset.dvd_prod_of_mem m hi)
    rw [h0] at hdvd
    have hpos : 0 < ∏ i ∈ s, m i := Finset.prod_pos (fun i hi => hm i)
    exact hpos.ne' (Nat.eq_zero_of_zero_dvd hdvd)
  have hgcd_lcm_finset : ∀ (s : Finset (Fin k)) (c : ℕ), c ≠ 0 →
      Nat.gcd (s.lcm m) c = s.lcm (fun i => Nat.gcd (m i) c) := by
    intro s
    induction s using Finset.induction with
    | empty =>
        intro c _
        simp [Finset.lcm_empty]
    | insert a s ha ih =>
        intro c hc
        rw [Finset.lcm_insert, Finset.lcm_insert]
        change Nat.gcd (Nat.lcm (m a) (s.lcm m)) c =
          Nat.lcm (Nat.gcd (m a) c) (s.lcm fun i => Nat.gcd (m i) c)
        rw [hgcd_lcm (m a) (s.lcm m) c (hm a).ne' (hlcm_ne s) hc]
        rw [ih c hc]
  -- two-congruence existence lemma
  have htwo : ∀ (M N : ℕ) (R S : ℤ), 0 < M → 0 < N →
      ((Nat.gcd M N : ℕ) : ℤ) ∣ R - S →
      ∃ x : ℤ, x ≡ R [ZMOD (M : ℤ)] ∧ x ≡ S [ZMOD (N : ℤ)] := by
    intro M N R S hM hN hdvd
    set g : ℕ := Nat.gcd M N with hg
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left N hM
    set M' : ℕ := M / g with hM'def
    set N' : ℕ := N / g with hN'def
    have hM_eq : M = g * M' := by rw [hM'def, Nat.mul_div_cancel' (Nat.gcd_dvd_left M N)]
    have hN_eq : N = g * N' := by rw [hN'def, Nat.mul_div_cancel' (Nat.gcd_dvd_right M N)]
    have hcop : Nat.Coprime N' M' := by
      rw [hN'def, hM'def, hg]
      exact (Nat.coprime_div_gcd_div_gcd hgpos).symm
    obtain ⟨u, hu⟩ := Int.mod_coprime hcop
    have hdiv : (g : ℤ) ∣ R - S := by simpa [hg] using hdvd
    obtain ⟨kk, hk⟩ : ∃ kk : ℤ, R - S = (g : ℤ) * kk := by
      obtain ⟨kk, hk⟩ := hdiv
      exact ⟨kk, by linarith [hk]⟩
    refine ⟨S + (N : ℤ) * (kk * u), ?_, ?_⟩
    · rw [Int.modEq_iff_dvd]
      have hMcast : (M : ℤ) = (g : ℤ) * (M' : ℤ) := by rw [hM_eq]; push_cast; ring
      have hNcast : (N : ℤ) = (g : ℤ) * (N' : ℤ) := by rw [hN_eq]; push_cast; ring
      have hku : (M' : ℤ) ∣ 1 - (N' : ℤ) * u := Int.modEq_iff_dvd.mp hu
      obtain ⟨w, hw⟩ : ∃ w : ℤ, kk * (1 - (N' : ℤ) * u) = (M' : ℤ) * w :=
        dvd_mul_of_dvd_right hku kk
      refine ⟨w, ?_⟩
      rw [hMcast, hNcast]
      have e : R - (S + (g : ℤ) * (N' : ℤ) * (kk * u)) = (g : ℤ) * (kk * (1 - (N' : ℤ) * u)) := by
        rw [show R = S + (g : ℤ) * kk from by linarith [hk]]
        ring
      rw [e, hw]
      ring
    · rw [Int.modEq_iff_dvd]
      refine ⟨-(kk * u), ?_⟩
      ring
  -- induction: pairwise compatibility gives an integer solution
  have key : ∀ s : Finset (Fin k),
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ((Nat.gcd (m i) (m j) : ℕ) : ℤ) ∣ r i - r j) →
      ∃ x : ℤ, ∀ i ∈ s, x ≡ r i [ZMOD (m i : ℤ)] := by
    intro s
    induction s using Finset.induction with
    | empty => intro _; exact ⟨0, by simp⟩
    | insert a s ha ih =>
        intro hcomp
        obtain ⟨x, hx⟩ := ih (fun i hi j hj hij =>
          hcomp i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
        have hLpos : 0 < s.lcm m := Nat.pos_of_ne_zero (hlcm_ne s)
        have hcompat : ((Nat.gcd (s.lcm m) (m a) : ℕ) : ℤ) ∣ x - r a := by
          rw [hgcd_lcm_finset s (m a) (hm a).ne', Int.natCast_dvd]
          apply Finset.lcm_dvd
          intro i hi
          rw [← Int.natCast_dvd]
          have hia : i ≠ a := fun h => ha (h ▸ hi)
          have h1 : ((Nat.gcd (m i) (m a) : ℕ) : ℤ) ∣ x - r i := by
            have hmul : ((Nat.gcd (m i) (m a) : ℕ) : ℤ) ∣ (m i : ℤ) := by
              exact_mod_cast Nat.gcd_dvd_left (m i) (m a)
            have hxi : (m i : ℤ) ∣ r i - x := Int.modEq_iff_dvd.mp (hx i hi)
            have hxi' : (m i : ℤ) ∣ x - r i := by simpa using dvd_neg.mpr hxi
            exact hmul.trans hxi' 
          have h2 : ((Nat.gcd (m i) (m a) : ℕ) : ℤ) ∣ r i - r a :=
            hcomp i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self a s) hia
          have h3 := dvd_add h1 h2
          rwa [show x - r i + (r i - r a) = x - r a by ring] at h3
        obtain ⟨y, hyL, hya⟩ := htwo (s.lcm m) (m a) x (r a) hLpos (hm a) hcompat
        refine ⟨y, ?_⟩
        intro i hi
        rcases Finset.mem_insert.mp hi with hia | hi
        · subst hia; exact hya
        · have hdvd : (m i : ℤ) ∣ ((s.lcm m : ℕ) : ℤ) := by
            exact_mod_cast Finset.dvd_lcm hi
          exact (Int.ModEq.of_dvd hdvd hyL).trans (hx i hi)
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1
    constructor
    · rintro ⟨x, hx⟩ i j hij
      have h1 : ((Nat.gcd (m i) (m j) : ℕ) : ℤ) ∣ (m i : ℤ) := by
        exact_mod_cast Nat.gcd_dvd_left (m i) (m j)
      have h2 : ((Nat.gcd (m i) (m j) : ℕ) : ℤ) ∣ (m j : ℤ) := by
        exact_mod_cast Nat.gcd_dvd_right (m i) (m j)
      have h3 : (m i : ℤ) ∣ r i - x := Int.modEq_iff_dvd.mp (hx i)
      have h4 : (m j : ℤ) ∣ r j - x := Int.modEq_iff_dvd.mp (hx j)
      have h5 : ((Nat.gcd (m i) (m j) : ℕ) : ℤ) ∣ r i - r j := by
        have h := dvd_sub (h1.trans h3) (h2.trans h4)
        rwa [show r i - x - (r j - x) = r i - r j by ring] at h
      exact h5
    · intro hpair
      have := key Finset.univ (fun i _ j _ hij => hpair i j hij)
      simpa using this
  · -- Part 2: uniqueness modulo the lcm
    intro x y hx hy
    have hkey : ∀ s : Finset (Fin k), x ≡ y [ZMOD ((s.lcm m : ℕ) : ℤ)] := by
      intro s
      induction s using Finset.induction with
      | empty => simp [Finset.lcm_empty, Int.modEq_one]
      | insert a s ha ih =>
          rw [Finset.lcm_insert, Int.modEq_iff_dvd, Int.natCast_dvd]
          apply Nat.lcm_dvd
          · rw [← Int.natCast_dvd]
            exact Int.modEq_iff_dvd.mp ((hx a).trans (hy a).symm)
          · rw [← Int.natCast_dvd]
            exact Int.modEq_iff_dvd.mp ih
    exact hkey Finset.univ
  · -- Part 3: natural-number solutions
    constructor
    · rintro ⟨x, hx⟩ i j
      have h1 : ((Nat.gcd (m i) (m j) : ℕ) : ℤ) ∣ (m i : ℤ) := by
        exact_mod_cast Nat.gcd_dvd_left (m i) (m j)
      have h2 : ((Nat.gcd (m i) (m j) : ℕ) : ℤ) ∣ (m j : ℤ) := by
        exact_mod_cast Nat.gcd_dvd_right (m i) (m j)
      exact ((Int.ModEq.of_dvd h1 (hx i)).symm.trans (Int.ModEq.of_dvd h2 (hx j)))
    · intro hpair
      have hpair' : ∀ i j, i ≠ j → ((Nat.gcd (m i) (m j) : ℕ) : ℤ) ∣ r i - r j := by
        intro i j hij
        have h : (↑((m i).gcd (m j)) : ℤ) ∣ r j - r i := (hpair i j).dvd
        simpa using dvd_neg.mpr h
      have hkey := key Finset.univ (fun i _ j _ hij => hpair' i j hij)
      simp only [Finset.mem_univ, forall_const] at hkey
      obtain ⟨x, hx⟩ := hkey
      have hLpos : 0 < Finset.univ.lcm m := Nat.pos_of_ne_zero (hlcm_ne Finset.univ)
      refine ⟨(x + ((Finset.univ.lcm m : ℕ) : ℤ) * |x|).toNat, ?_⟩
      have hnonneg : 0 ≤ x + ((Finset.univ.lcm m : ℕ) : ℤ) * |x| := by
        have hL1 : (1 : ℤ) ≤ ((Finset.univ.lcm m : ℕ) : ℤ) := by exact_mod_cast hLpos
        have habs : 0 ≤ |x| := abs_nonneg x
        have hLnn : (0 : ℤ) ≤ ((Finset.univ.lcm m : ℕ) : ℤ) := by linarith
        have h2 : 0 ≤ x + |x| := by linarith [neg_abs_le x]
        have h3 : 0 ≤ (((Finset.univ.lcm m : ℕ) : ℤ) - 1) * |x| :=
          mul_nonneg (by linarith) habs
        have h4 : x + ((Finset.univ.lcm m : ℕ) : ℤ) * |x| =
            (x + |x|) + (((Finset.univ.lcm m : ℕ) : ℤ) - 1) * |x| := by ring
        linarith [h2, h3, h4]
      rw [show (((x + ((Finset.univ.lcm m : ℕ) : ℤ) * |x|).toNat : ℕ) : ℤ) =
          x + ((Finset.univ.lcm m : ℕ) : ℤ) * |x| from Int.toNat_of_nonneg hnonneg]
      intro i
      have hthis : x + ((Finset.univ.lcm m : ℕ) : ℤ) * |x| ≡ x [ZMOD (m i : ℤ)] := by
        rw [Int.modEq_iff_dvd]
        have hLi : (m i : ℤ) ∣ ((Finset.univ.lcm m : ℕ) : ℤ) := by
          exact_mod_cast Finset.dvd_lcm (Finset.mem_univ i)
        have hmul : (m i : ℤ) ∣ (((Finset.univ.lcm m : ℕ) : ℤ) * |x|) := hLi.mul_right |x|
        have h := dvd_neg.mpr hmul
        simpa using h
      exact hthis.trans (hx i)
