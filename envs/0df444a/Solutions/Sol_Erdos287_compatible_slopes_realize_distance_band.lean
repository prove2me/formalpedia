-- Prove2me | solution 1 for Erdos287.compatible_slopes_realize_distance_band
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T03:40:47.059942+00:00
-- url     : https://prove2.me/submissions/e2ef3d7b-70e2-40b0-9037-634a0c448962

import Mathlib

open Finset

set_option autoImplicit false

private def pairs (n : ℕ) : Finset (ℕ × ℕ) :=
  ((range n) ×ˢ (range n)).filter fun p => p.1 < p.2

private theorem mem_pairs {n : ℕ} {p : ℕ × ℕ} :
    p ∈ pairs n ↔ p.1 < p.2 ∧ p.2 < n := by
  simp only [pairs, mem_filter, mem_product, mem_range]
  omega

private def diff (b : ℕ → ℤ) (p : ℕ × ℕ) : ℤ := b p.2 - b p.1

private def det (z b : ℕ → ℤ) (p q : ℕ × ℕ) : ℤ :=
  diff z p * diff b q - diff z q * diff b p

private theorem generic_intercepts (z : ℕ → ℤ) (hz : StrictMono z) (n : ℕ) :
    ∃ b : ℕ → ℤ, (∀ i < n, 0 < b i) ∧
      (∀ p ∈ pairs n, diff b p ≠ 0 ∧ diff b p ∣ b p.1) ∧
      (pairs n : Set (ℕ × ℕ)).Pairwise (fun p q => det z b p q ≠ 0) := by
  induction n with
  | zero =>
    refine ⟨fun _ => 1, by omega, ?_, ?_⟩
    · intro p hp
      have := mem_pairs.mp hp
      omega
    · intro p hp
      have := mem_pairs.mp (show p ∈ pairs 0 from hp)
      omega
  | succ n ih =>
    obtain ⟨b, hb, hpair, hdet⟩ := ih
    let B := 1 + ∑ i ∈ range n, b i
    let Z := z n - z 0 + 1
    let P := ∏ p ∈ pairs n, |diff b p|
    have hB (i : ℕ) (hi : i < n) : b i ≤ B := by
      have h := single_le_sum (f := b) (fun j hj => (hb j (mem_range.mp hj)).le)
        (mem_range.mpr hi)
      dsimp [B]
      omega
    have hBpos : 0 < B := by
      have h : 0 ≤ ∑ i ∈ range n, b i :=
        sum_nonneg (fun i hi => (hb i (mem_range.mp hi)).le)
      dsimp [B]
      omega
    have hZ : 1 ≤ Z := by
      have := hz.monotone (Nat.zero_le n)
      dsimp [Z]
      omega
    have hzbd (p : ℕ × ℕ) (hp : p ∈ pairs (n + 1)) :
        1 ≤ diff z p ∧ diff z p ≤ Z := by
      obtain ⟨h₁, h₂⟩ := mem_pairs.mp hp
      have h₃ := hz h₁
      have h₄ := hz.monotone (Nat.zero_le p.1)
      have h₅ := hz.monotone (show p.2 ≤ n by omega)
      dsimp [diff, Z]
      omega
    have hP : 1 ≤ P :=
      Int.add_one_le_iff.mpr (prod_pos fun p hp => abs_pos.mpr (hpair p hp).1)
    have hdP (p : ℕ × ℕ) (hp : p ∈ pairs n) : diff b p ∣ P :=
      ((dvd_abs _ _).mpr dvd_rfl).trans (dvd_prod_of_mem (fun q => |diff b q|) hp)
    let T := P * (B * Z + 1)
    have hBZ : 0 ≤ B * Z := mul_nonneg hBpos.le (by omega)
    have hT : B * Z < T := by
      have h := mul_le_mul_of_nonneg_right hP (show 0 ≤ B * Z + 1 by omega)
      rw [one_mul] at h
      exact (Int.lt_add_one_iff.mpr le_rfl).trans_le h
    have hTpos : 0 < T := hBZ.trans_lt hT
    let R := ∏ i ∈ range n, (b i + T)
    have hR : 1 ≤ R := Int.add_one_le_iff.mpr (prod_pos fun i hi =>
      add_pos (hb i (mem_range.mp hi)) hTpos)
    let W := (T + B + 1) * (P * R)
    have hW : T + B < W := by
      have h := mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le hP hR)
        (show 0 ≤ T + B + 1 by omega)
      rw [mul_one] at h
      exact (Int.lt_add_one_iff.mpr le_rfl).trans_le h
    have hPdW : P ∣ W := dvd_mul_of_dvd_right (dvd_mul_right _ _) _
    have hRdW : R ∣ W := dvd_mul_of_dvd_right (dvd_mul_left _ _) _
    let b' (i : ℕ) := if i < n then W - (b i + T) else W
    have hcase (p : ℕ × ℕ) (hp : p ∈ pairs (n + 1)) :
        p ∈ pairs n ∨ p.2 = n := by
      rw [mem_pairs] at hp ⊢
      omega
    have hold (p : ℕ × ℕ) (hp : p ∈ pairs n) :
        diff b' p = -diff b p := by
      obtain ⟨h₁, h₂⟩ := mem_pairs.mp hp
      simp only [diff, b', if_pos (h₁.trans h₂), if_pos h₂]
      ring
    have hnew (p : ℕ × ℕ) (hp : p ∈ pairs (n + 1)) (he : p.2 = n) :
        diff b' p = b p.1 + T := by
      have h₁ : p.1 < n := he ▸ (mem_pairs.mp hp).1
      simp [diff, b', he, h₁]
    have hmix (p q : ℕ × ℕ) (hp : p ∈ pairs n)
        (hq : q ∈ pairs (n + 1)) (he : q.2 = n) : 0 < det z b' p q := by
      have hp' : p ∈ pairs (n + 1) := mem_pairs.mpr
        ⟨(mem_pairs.mp hp).1, by have := (mem_pairs.mp hp).2; omega⟩
      have hp₁ := (mem_pairs.mp hp).1.trans (mem_pairs.mp hp).2
      have hq₁ : q.1 < n := he ▸ (mem_pairs.mp hq).1
      have hdb : diff b' p ≤ B := by
        rw [hold p hp]
        have := hB p.1 hp₁
        have := hb p.2 (mem_pairs.mp hp).2
        dsimp [diff]
        omega
      have hprod : diff z q * diff b' p ≤ Z * B :=
        (mul_le_mul_of_nonneg_left hdb (by have := (hzbd q hq).1; omega)).trans
          (mul_le_mul_of_nonneg_right (hzbd q hq).2 hBpos.le)
      rw [det, hnew q hq he]
      have hprod' : b q.1 + T ≤ diff z p * (b q.1 + T) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hzbd p hp').1
          (add_nonneg (hb q.1 hq₁).le hTpos.le)
      nlinarith [hb q.1 hq₁]
    have hboth (p q : ℕ × ℕ) (hp : p ∈ pairs (n + 1)) (hq : q ∈ pairs (n + 1))
        (hpn : p.2 = n) (hqn : q.2 = n) (hlt : p.1 < q.1) :
        0 < det z b' p q := by
      have hp₁ : p.1 < n := hpn ▸ (mem_pairs.mp hp).1
      have hq₁ : q.1 < n := hqn ▸ (mem_pairs.mp hq).1
      have hdiff : 1 ≤ diff z p - diff z q := by
        have := hz hlt
        simp only [diff, hpn, hqn]
        omega
      have hmul : T ≤ (diff z p - diff z q) * T := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hdiff hTpos.le
      have hprod : diff z q * b p.1 ≤ Z * B :=
        (mul_le_mul_of_nonneg_left (hB p.1 hp₁) (by have := (hzbd q hq).1; omega)).trans
          (mul_le_mul_of_nonneg_right (hzbd q hq).2 hBpos.le)
      have hpos := mul_nonneg
        (show 0 ≤ diff z p by have := (hzbd p hp).1; omega) (hb q.1 hq₁).le
      rw [det, hnew p hp hpn, hnew q hq hqn]
      nlinarith
    refine ⟨b', ?_, ?_, ?_⟩
    · intro i hi
      by_cases hn : i < n
      · have := hB i hn
        simp only [b', if_pos hn]
        omega
      · simp only [b', if_neg hn]
        omega
    · intro p hp
      rcases hcase p hp with holdmem | he
      · have h₁ := (mem_pairs.mp holdmem).1.trans (mem_pairs.mp holdmem).2
        have hdiv := (hdP p holdmem).trans (dvd_mul_right P (B * Z + 1))
        rw [hold p holdmem, neg_ne_zero, neg_dvd]
        simp only [b', if_pos h₁]
        exact ⟨(hpair p holdmem).1, ((hdP p holdmem).trans hPdW).sub
          ((hpair p holdmem).2.add hdiv)⟩
      · have h₁ : p.1 < n := he ▸ (mem_pairs.mp hp).1
        have hdiv : b p.1 + T ∣ R := dvd_prod_of_mem (fun i => b i + T) (mem_range.mpr h₁)
        rw [hnew p hp he]
        simp only [b', if_pos h₁]
        exact ⟨(add_pos (hb p.1 h₁) hTpos).ne', (hdiv.trans hRdW).sub dvd_rfl⟩
    · intro p hp q hq hne
      change p ∈ pairs (n + 1) at hp
      change q ∈ pairs (n + 1) at hq
      have hswap : det z b' p q = -det z b' q p := by unfold det; ring
      rcases hcase p hp with hpo | hpn <;> rcases hcase q hq with hqo | hqn
      · have hrev : det z b' p q = -det z b p q := by
          simp only [det, hold p hpo, hold q hqo]
          ring
        rw [hrev, neg_ne_zero]
        exact hdet hpo hqo hne
      · exact (hmix p q hpo hq hqn).ne'
      · rw [hswap, neg_ne_zero]
        exact (hmix q p hqo hp hpn).ne'
      · rcases lt_trichotomy p.1 q.1 with hl | he | hl
        · exact (hboth p q hp hq hpn hqn hl).ne'
        · exact (hne (Prod.ext he (hpn.trans hqn.symm))).elim
        · rw [hswap, neg_ne_zero]
          exact (hboth q p hq hp hqn hpn hl).ne'

private theorem large_crt {ι : Type*} (s : Finset ι) (m : ι → ℕ) (r : ι → ℤ)
    (hm : ∀ i ∈ s, m i ≠ 0) (hc : (s : Set ι).Pairwise (fun i j => (m i).Coprime (m j)))
    (B : ℝ) :
    ∃ A : ℕ, B < (A : ℝ) ∧ ∀ i ∈ s, (m i : ℤ) ∣ (A : ℤ) - r i := by
  classical
  let ρ (i : ι) := (r i % (m i : ℤ)).toNat
  let c := Nat.chineseRemainderOfFinset ρ m s hm hc
  let Q := ∏ i ∈ s, m i
  have hQ : 0 < Q := prod_pos fun i hi => Nat.pos_of_ne_zero (hm i hi)
  obtain ⟨w, hw⟩ := exists_nat_gt B
  let A := (c : ℕ) + Q * w
  refine ⟨A, hw.trans_le (by exact_mod_cast (show w ≤ A by
    have := Nat.mul_le_mul_right w hQ
    dsimp [A]
    omega)), ?_⟩
  intro i hi
  have hstep : m i ∣ Q * w := dvd_mul_of_dvd_left (dvd_prod_of_mem m hi) _
  have hA : A ≡ ρ i [MOD m i] := by
    simpa only [add_zero] using (c.property i hi).add (Nat.modEq_zero_iff_dvd.mpr hstep)
  have hn : (m i : ℤ) ≠ 0 := by exact_mod_cast hm i hi
  have hρ : (ρ i : ℤ) = r i % (m i : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ hn)
  have hres : (r i) ≡ (ρ i : ℤ) [ZMOD (m i : ℤ)] := by
    rw [hρ]
    simp only [Int.ModEq, Int.emod_emod]
  exact Int.modEq_iff_dvd.mp (hres.trans
    (Int.modEq_iff_dvd.mpr (Nat.modEq_iff_dvd.mp hA.symm)))

private theorem approximate_compatible (n : ℕ) (z : ℕ → ℕ) (hz : StrictMono z)
    (δ : ℝ) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    ∃ a : ℕ → ℕ, ∃ A C : ℝ, 0 < A ∧ 0 < C ∧
      (∀ i < n, A ≤ (a i : ℝ) ∧ (a i : ℝ) ≤ (1 + δ) * A) ∧
      ∀ i j, i < j → j < n → a i < a j ∧ (a j - a i) ∣ a i ∧
        |((a j - a i : ℕ) : ℝ) / C - ((z j : ℝ) - z i)| < δ := by
  classical
  let f (i : ℕ) : ℤ := z i
  have hf : StrictMono f := by
    intro i j hij
    change (z i : ℤ) < (z j : ℤ)
    exact_mod_cast hz hij
  obtain ⟨b, hb, hpair, hdet⟩ := generic_intercepts f hf n
  let P := ∏ p ∈ pairs n, |diff b p|
  have hP : 1 ≤ P :=
    Int.add_one_le_iff.mpr (prod_pos fun p hp => abs_pos.mpr (hpair p hp).1)
  have hbP (p : ℕ × ℕ) (hp : p ∈ pairs n) : diff b p ∣ P :=
    ((dvd_abs _ _).mpr dvd_rfl).trans (dvd_prod_of_mem (fun q => |diff b q|) hp)
  let D := ∏ p ∈ pairs n, ∏ q ∈ pairs n, if p = q then 1 else |det f b p q|
  have hD : 1 ≤ D := Int.add_one_le_iff.mpr (prod_pos fun p hp => prod_pos fun q hq => by
    by_cases he : p = q
    · simp [he]
    · simpa [he] using abs_pos.mpr (hdet hp hq he))
  have hdetD (p q : ℕ × ℕ) (hp : p ∈ pairs n) (hq : q ∈ pairs n) (hne : p ≠ q) :
      det f b p q ∣ D := by
    have hd₁ := dvd_prod_of_mem (fun s => if p = s then 1 else |det f b p s|) hq
    have hd₂ := dvd_prod_of_mem (fun t => ∏ s ∈ pairs n,
      if t = s then 1 else |det f b t s|) hp
    rw [if_neg hne] at hd₁
    exact ((dvd_abs _ _).mpr dvd_rfl).trans (hd₁.trans hd₂)
  let B := 1 + ∑ i ∈ range n, b i
  have hbd (p : ℕ × ℕ) (hp : p ∈ pairs n) : |diff b p| ≤ B := by
    have hsum (i : ℕ) (hi : i < n) := single_le_sum (f := b)
      (fun j hj => (hb j (mem_range.mp hj)).le) (mem_range.mpr hi)
    obtain ⟨h₁, h₂⟩ := mem_pairs.mp hp
    have := hsum p.1 (h₁.trans h₂)
    have := hsum p.2 h₂
    have := hb p.1 (h₁.trans h₂)
    have := hb p.2 h₂
    apply abs_le.mpr
    dsimp [diff, B]
    omega
  obtain ⟨k, hk⟩ := exists_nat_gt (max 1 ((B : ℝ) / δ))
  let w := D * (k : ℤ)
  let C := P * P * w
  have hk₁ : (1 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hkw : (k : ℤ) ≤ w := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hD (Int.natCast_nonneg k)
  have hwp : 0 < w := by
    have hkz : (1 : ℤ) < k := by exact_mod_cast hk₁
    omega
  have hwC : w ≤ C := by
    have hPP := one_le_mul_of_one_le_of_one_le hP hP
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hPP hwp.le
  have hCp : 0 < C := hwp.trans_le hwC
  have hCR : (0 : ℝ) < C := by exact_mod_cast hCp
  have hδC : (B : ℝ) < δ * C := by
    have h₁ := (le_max_right (1 : ℝ) ((B : ℝ) / δ)).trans_lt hk
    have h₂ : (k : ℝ) ≤ C := by exact_mod_cast hkw.trans hwC
    simpa only [mul_comm] using (div_lt_iff₀ hδ).mp (h₁.trans_le h₂)
  let h (i : ℕ) := C * f i + b i
  have hh (i : ℕ) (hi : i < n) : 0 < h i :=
    add_pos_of_nonneg_of_pos (mul_nonneg hCp.le (Int.natCast_nonneg _)) (hb i hi)
  have hdiff (p : ℕ × ℕ) : diff h p = C * diff f p + diff b p := by
    simp only [diff, h]
    ring
  have hgeom (p : ℕ × ℕ) (hp : p ∈ pairs n) :
      |(diff h p : ℝ) / C - (diff f p : ℝ)| < δ := by
    have h₁ : (diff h p : ℝ) = (C : ℝ) * (diff f p : ℝ) + (diff b p : ℝ) := by
      exact_mod_cast hdiff p
    rw [show (diff h p : ℝ) / C - (diff f p : ℝ) = (diff b p : ℝ) / C by
      rw [h₁, add_div, mul_comm (C : ℝ), mul_div_cancel_right₀ _ hCR.ne']
      ring, abs_div, abs_of_pos hCR, div_lt_iff₀ hCR]
    have h₂ : |(diff b p : ℝ)| ≤ (B : ℝ) := by exact_mod_cast hbd p hp
    exact h₂.trans_lt hδC
  have hdpos (p : ℕ × ℕ) (hp : p ∈ pairs n) : 0 < diff h p := by
    have h₁ := (abs_lt.mp (hgeom p hp)).1
    have hz₁ := hf (mem_pairs.mp hp).1
    have h₂ : (1 : ℝ) ≤ diff f p := by
      exact_mod_cast (show 1 ≤ diff f p by dsimp [diff]; omega)
    have h₃ : 0 < (diff h p : ℝ) / C := by linarith
    exact_mod_cast ((div_pos_iff_of_pos_right hCR).mp h₃)
  let e (p : ℕ × ℕ) := 1 + P * ((P / diff b p) * w * diff f p)
  have hfactor (p : ℕ × ℕ) (hp : p ∈ pairs n) : diff h p = diff b p * e p := by
    have h₁ : diff b p * (P / diff b p) = P := by
      simpa only [mul_comm] using Int.ediv_mul_cancel (hbP p hp)
    rw [hdiff]
    calc
      C * diff f p + diff b p =
          P * P * w * diff f p + diff b p := rfl
      _ = diff b p * (1 + P * ((P / diff b p) * w * diff f p)) := by
        linear_combination -P * w * diff f p * h₁
  have he_ne (p : ℕ × ℕ) (hp : p ∈ pairs n) : (e p).natAbs ≠ 0 := by
    intro he
    have he' : e p = 0 := Int.natAbs_eq_zero.mp he
    have h₁ := hdpos p hp
    rw [hfactor p hp, he', mul_zero] at h₁
    exact (lt_irrefl _ h₁)
  have hunit (p : ℕ × ℕ) {v : ℤ} (hvP : v ∣ P) (hve : v ∣ e p) : v ∣ 1 := by
    have := hve.sub (dvd_mul_of_dvd_left hvP ((P / diff b p) * w * diff f p))
    simpa [e] using this
  have hPE (p : ℕ × ℕ) : P.natAbs.Coprime (e p).natAbs := by
    apply Nat.coprime_of_dvd
    intro v hp hvP hve
    exact hp.not_dvd_one (by exact_mod_cast hunit p (Int.natCast_dvd.mpr hvP) (Int.natCast_dvd.mpr hve))
  have hEE (p q : ℕ × ℕ) (hp : p ∈ pairs n) (hq : q ∈ pairs n) (hne : p ≠ q) :
      (e p).natAbs.Coprime (e q).natAbs := by
    apply Nat.coprime_of_dvd
    intro v hv hvep hveq
    have hvep' := Int.natCast_dvd.mpr hvep
    have hveq' := Int.natCast_dvd.mpr hveq
    have hdp : (v : ℤ) ∣ diff h p := by
      rw [hfactor p hp]
      exact dvd_mul_of_dvd_right hvep' (diff b p)
    have hdq : (v : ℤ) ∣ diff h q := by
      rw [hfactor q hq]
      exact dvd_mul_of_dvd_right hveq' (diff b q)
    have hd : (v : ℤ) ∣ det f b p q := by
      have heq : det f b p q = diff f p * diff h q - diff f q * diff h p := by
        simp only [det, hdiff]
        ring
      rw [heq]
      exact (dvd_mul_of_dvd_right hdq (diff f p)).sub
        (dvd_mul_of_dvd_right hdp (diff f q))
    have hwv : (v : ℤ) ∣ C :=
      dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (hd.trans (hdetD p q hp hq hne)) (k : ℤ)) _
    rw [hdiff] at hdp
    have hvb : (v : ℤ) ∣ diff b p := (dvd_add_right (dvd_mul_of_dvd_left hwv _)).mp hdp
    exact hv.not_dvd_one (by exact_mod_cast hunit p (hvb.trans (hbP p hp)) hvep')
  let s : Finset (Option (ℕ × ℕ)) := insert none ((pairs n).map ⟨some, Option.some_injective _⟩)
  have hs (p : ℕ × ℕ) : some p ∈ s ↔ p ∈ pairs n := by simp [s]
  have hs₀ : none ∈ s := mem_insert_self _ _
  let m : Option (ℕ × ℕ) → ℕ := fun o => o.elim P.natAbs (fun p => (e p).natAbs)
  let r : Option (ℕ × ℕ) → ℤ := fun o => o.elim 0 (fun p => -h p.1)
  have hm : ∀ o ∈ s, m o ≠ 0 := by
    intro o ho
    cases o with
    | none =>
      intro he
      have := Int.natAbs_eq_zero.mp (show P.natAbs = 0 from he)
      omega
    | some p => exact he_ne p ((hs p).mp ho)
  have hc : (s : Set (Option (ℕ × ℕ))).Pairwise (fun i j => (m i).Coprime (m j)) := by
    intro i hi j hj hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact hPE _
    · exact (hPE _).symm
    · exact hEE _ _ ((hs _).mp hi) ((hs _).mp hj) (fun he => hij (congrArg some he))
  let H := 1 + ∑ i ∈ range n, h i
  obtain ⟨A, hA, hmod⟩ := large_crt s m r hm hc (max 0 ((H : ℝ) / δ))
  have hAp : (0 : ℝ) < A := (le_max_left _ _).trans_lt hA
  have hHA : (H : ℝ) < δ * A := by
    simpa only [mul_comm] using (div_lt_iff₀ hδ).mp ((le_max_right _ _).trans_lt hA)
  let a (i : ℕ) := A + (h i).toNat
  have haZ (i : ℕ) (hi : i < n) : (a i : ℤ) = (A : ℤ) + h i := by
    simp [a, Int.toNat_of_nonneg (hh i hi).le]
  have hPdvd : P ∣ (A : ℤ) := by
    have h₁ := hmod none hs₀
    simpa [m, r, Int.natCast_natAbs, abs_dvd] using h₁
  refine ⟨a, A, C, hAp, hCR, ?_, ?_⟩
  · intro i hi
    have haR : (a i : ℝ) = (A : ℝ) + (h i : ℝ) := by exact_mod_cast haZ i hi
    have hhi₁ : (0 : ℝ) ≤ h i := by exact_mod_cast (hh i hi).le
    have hhi₂ : (h i : ℝ) ≤ H := by
      have h₁ := single_le_sum (f := h) (fun j hj => (hh j (mem_range.mp hj)).le)
        (mem_range.mpr hi)
      exact_mod_cast (show h i ≤ H by dsimp [H]; omega)
    rw [haR]
    exact ⟨by linarith, by linarith [hhi₂.trans_lt hHA]⟩
  · intro i j hij hj
    let p := (i, j)
    have hp : p ∈ pairs n := mem_pairs.mpr ⟨hij, hj⟩
    have hi := hij.trans hj
    have hsub : (a j : ℤ) - (a i : ℤ) = diff h p := by
      rw [haZ i hi, haZ j hj]
      simp only [diff, p]
      ring
    have hlt : a i < a j := by
      have := hdpos p hp
      omega
    have hsub' : ((a j - a i : ℕ) : ℤ) = diff h p := by
      rw [Int.ofNat_sub hlt.le, hsub]
    refine ⟨hlt, ?_, ?_⟩
    · have hde : (e p).natAbs ∣ a i := by
        apply Int.natCast_dvd_natCast.mp
        rw [haZ i hi]
        simpa [m, r, p] using hmod (some p) ((hs p).mpr hp)
      have hbd' : diff b p ∣ (a i : ℤ) := by
        rw [haZ i hi]
        apply ((hbP p hp).trans hPdvd).add
        exact (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (hbP p hp) P) w)
          (f i)).add (hpair p hp).2
      have hdiv : (diff b p).natAbs * (e p).natAbs ∣ a i :=
        (Nat.Coprime.coprime_dvd_left (Int.natAbs_dvd_natAbs.mpr (hbP p hp))
          (hPE p)).mul_dvd_of_dvd_of_dvd
          (Int.dvd_natCast.mp hbd') hde
      have heq : (a j - a i) = (diff b p).natAbs * (e p).natAbs := by
        simpa only [Int.natAbs_natCast, Int.natAbs_mul] using
          congrArg Int.natAbs (hsub'.trans (hfactor p hp))
      rwa [heq]
    · have hdist : ((a j - a i : ℕ) : ℝ) = (diff h p : ℝ) := by exact_mod_cast hsub'
      have hzdist : (diff f p : ℝ) = (z j : ℝ) - z i := by simp [diff, f, p]
      simpa only [hdist, hzdist] using hgeom p hp

/-- Any strict distance band of ratio below e can be realized by compatible affine slopes. -/
theorem solution (n : ℕ) (z : ℕ → ℕ) (hz : StrictMono z)
    (u v : ℝ) (hu : 0 < u) (huv : u ≤ v) (hv : v < Real.exp 1 * u) :
    ∃ (a : ℕ → ℕ) (L U : ℝ), 0 < L ∧ L ≤ U ∧ U < Real.exp 1 * L ∧
      (∀ i < n, 0 < a i) ∧
      ∀ i j, i < j → j < n →
        a i < a j ∧ (a j - a i) ∣ a i ∧
        (u ≤ (z j : ℝ) - z i → (z j : ℝ) - z i ≤ v →
          L ≤ ((a i / (a j - a i) : ℕ) : ℝ) * a j ∧
          ((a i / (a j - a i) : ℕ) : ℝ) * a j ≤ U) := by
  let Q := 3 * v + 4 + Real.exp 1
  have hQ : 0 < Q := by dsimp [Q]; linarith [hu.trans_le huv, Real.exp_pos 1]
  let δ := min (1 / 2 : ℝ) (min (u / 2) ((Real.exp 1 * u - v) / (2 * Q)))
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min (by positivity)
    (div_pos (sub_pos.mpr hv) (mul_pos (by norm_num) hQ)))
  have hδ₁ : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hδu : δ ≤ u / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδQ : δ * (2 * Q) ≤ Real.exp 1 * u - v :=
    (le_div_iff₀ (mul_pos (by norm_num) hQ)).mp
      ((min_le_right _ _).trans (min_le_right _ _))
  have hmargin : (1 + δ) ^ 2 * (v + δ) < Real.exp 1 * (u - δ) := by
    have hs : δ ^ 2 ≤ δ := by nlinarith only [mul_nonneg hδ.le (sub_nonneg.mpr hδ₁)]
    have hc : δ ^ 3 ≤ δ := by
      have := mul_le_mul_of_nonneg_right hs hδ.le
      nlinarith only [this, hs]
    have hg := mul_nonneg (hu.trans_le huv).le (sub_nonneg.mpr hs)
    dsimp [Q] at hδQ
    nlinarith only [hs, hc, hg, hδQ, hv]
  obtain ⟨a, A, C, hA, hC, ha, hd⟩ := approximate_compatible n z hz δ hδ hδ₁
  let L := A ^ 2 / ((v + δ) * C)
  let U := (1 + δ) ^ 2 * A ^ 2 / ((u - δ) * C)
  have hLden : 0 < (v + δ) * C := mul_pos (add_pos (hu.trans_le huv) hδ) hC
  have hUden : 0 < (u - δ) * C := mul_pos (by linarith) hC
  have hnum : A ^ 2 ≤ (1 + δ) ^ 2 * A ^ 2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (show 1 ≤ (1 + δ) ^ 2 by nlinarith [sq_nonneg δ]) (sq_nonneg A)
  have hLU : L ≤ U := by
    calc
      L ≤ A ^ 2 / ((u - δ) * C) :=
        div_le_div_of_nonneg_left (sq_nonneg A) hUden
          (mul_le_mul_of_nonneg_right (by linarith) hC.le)
      _ ≤ U := div_le_div_of_nonneg_right hnum hUden.le
  have hUL : U < Real.exp 1 * L := by
    calc
      U < (Real.exp 1 * A ^ 2) / ((v + δ) * C) := by
        dsimp [U]
        apply (div_lt_div_iff₀ hUden hLden).mpr
        have hh := mul_lt_mul_of_pos_right hmargin (mul_pos (pow_pos hA 2) hC)
        convert hh using 1 <;> ring
      _ = Real.exp 1 * L := by rw [mul_div_assoc]
  refine ⟨a, L, U, div_pos (pow_pos hA _) hLden, hLU, hUL, ?_, ?_⟩
  · intro i hi
    exact_mod_cast hA.trans_le (ha i hi).1
  · intro i j hij hj
    obtain ⟨hlt, hdiv, hgeom⟩ := hd i j hij hj
    refine ⟨hlt, hdiv, ?_⟩
    intro hlo hhi
    let d := a j - a i
    have hdp : (0 : ℝ) < d := by exact_mod_cast Nat.sub_pos_of_lt hlt
    have hdl : (u - δ) * C < (d : ℝ) :=
      (lt_div_iff₀ hC).mp (by linarith [(abs_lt.mp hgeom).1])
    have hdu : (d : ℝ) < (v + δ) * C :=
      (div_lt_iff₀ hC).mp (by linarith [(abs_lt.mp hgeom).2])
    have hi := hij.trans hj
    have haij : A ^ 2 ≤ (a i : ℝ) * a j := by
      simpa only [pow_two] using mul_le_mul (ha i hi).1 (ha j hj).1 (le_of_lt hA) (Nat.cast_nonneg _)
    have haij' : (a i : ℝ) * a j ≤ (1 + δ) ^ 2 * A ^ 2 := by
      calc
        (a i : ℝ) * a j ≤ ((1 + δ) * A) * ((1 + δ) * A) :=
          mul_le_mul (ha i hi).2 (ha j hj).2 (Nat.cast_nonneg _)
            (mul_nonneg (by positivity) hA.le)
        _ = (1 + δ) ^ 2 * A ^ 2 := by ring
    have hcoef : ((a i / d : ℕ) : ℝ) * a j = (a i : ℝ) * a j / d := by
      apply (eq_div_iff hdp.ne').mpr
      have he : ((a i / d : ℕ) : ℝ) * (d : ℝ) = (a i : ℝ) := by
        exact_mod_cast Nat.div_mul_cancel hdiv
      linear_combination (a j : ℝ) * he
    change L ≤ ((a i / d : ℕ) : ℝ) * a j ∧ ((a i / d : ℕ) : ℝ) * a j ≤ U
    rw [hcoef]
    refine ⟨?_, ?_⟩
    · calc
        L ≤ A ^ 2 / (d : ℝ) := div_le_div_of_nonneg_left (sq_nonneg A) hdp hdu.le
        _ ≤ (a i : ℝ) * a j / d := div_le_div_of_nonneg_right haij hdp.le
    · calc
        (a i : ℝ) * a j / d ≤ ((1 + δ) ^ 2 * A ^ 2) / d :=
          div_le_div_of_nonneg_right haij' hdp.le
        _ ≤ U := div_le_div_of_nonneg_left (by positivity) hUden hdl.le

