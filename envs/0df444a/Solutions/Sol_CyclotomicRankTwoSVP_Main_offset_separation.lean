-- Prove2me | solution 1 for CyclotomicRankTwoSVP.Main.offset_separation
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:43:00.453259+00:00
-- url     : https://prove2.me/submissions/5b893d89-7009-4e6d-9ac6-a19b25627739

import Mathlib
import Definitions.Def_CyclotomicRankTwoSVP_Main_Checker

open CyclotomicRankTwoSVP.Main
open scoped BigOperators

set_option maxHeartbeats 1000000

theorem solution (q M n : ℕ) [Fact q.Prime] (hq : Odd q)
    (A : Incidence M n) (hA : IsX3C A) (hnd : Nondegenerate A)
    (α : Fin n → ℕ) (hα : IsSidon α) (hsep : 4 * beta α M < q) :
    (∀ ij ∈ incidences A, offset q α ij ≠ 0 ∧ -offset q α ij ≠ 0) ∧
    (Function.Injective fun p : {ij // ij ∈ incidences A} × Bool =>
      if p.2 then offset q α p.1.val else -offset q α p.1.val) ∧
    0 ∉ Dbad q A α ∧ Disjoint (Dbad q A α) (Dwit q α) ∧
    (Dbad q A α).card ≤ 2 * W A ^ 2 ∧ (Dbad q A α).card ≤ 18 * n ^ 2 := by
  classical
  obtain ⟨hM, hn, hrows⟩ := hnd
  have hq : 0 < q := (Fact.out : q.Prime).pos
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  let d : Fin M × Fin n → ℤ := fun ij =>
    (beta α (ij.1.val + 1) : ℤ) - (α ij.2 : ℤ)
  have ha (j : Fin n) : α j ≤ alphaStar α := by
    exact Finset.le_sup (f := α) (Finset.mem_univ j)
  have haZ (j : Fin n) : (α j : ℤ) ≤ (alphaStar α : ℤ) := by
    exact_mod_cast ha j
  have hbZ : (4 : ℤ) * (beta α M : ℤ) < (q : ℤ) := by exact_mod_cast hsep
  have hbqZ : (beta α M : ℤ) < (q : ℤ) := by omega
  have d_lo (ij : Fin M × Fin n) : (alphaStar α : ℤ) + 1 ≤ d ij := by
    have hblo : beta α 1 ≤ beta α (ij.1.val + 1) := by
      exact Nat.mul_le_mul_left _ (by omega)
    have hbloZ : (beta α 1 : ℤ) ≤ (beta α (ij.1.val + 1) : ℤ) := by
      exact_mod_cast hblo
    have hb1 : (beta α 1 : ℤ) = 2 * (alphaStar α : ℤ) + 1 := by
      simp [beta, tau]
    have haj := haZ ij.2
    dsimp [d]
    omega
  have d_hi (ij : Fin M × Fin n) : d ij ≤ (beta α M : ℤ) := by
    have hbhi : beta α (ij.1.val + 1) ≤ beta α M := by
      exact Nat.mul_le_mul_left _ (by omega)
    have hbhiZ : (beta α (ij.1.val + 1) : ℤ) ≤ (beta α M : ℤ) := by
      exact_mod_cast hbhi
    dsimp [d]
    omega
  have ha_beta : (alphaStar α : ℤ) < (beta α M : ℤ) := by
    let ij : Fin M × Fin n := (⟨0, hM⟩, ⟨0, hn⟩)
    have hlo := d_lo ij
    have hhi := d_hi ij
    omega
  have d_nonneg (ij : Fin M × Fin n) : 0 ≤ d ij := by
    have := d_lo ij
    omega
  have d_ne_zero (ij : Fin M × Fin n) : d ij ≠ 0 := by
    have := d_lo ij
    omega
  have d_lt_q (ij : Fin M × Fin n) : d ij < (q : ℤ) := by
    have := d_hi ij
    omega
  have diff_abs_small (ij kl : Fin M × Fin n) : |d ij - d kl| < (q : ℤ) := by
    rw [abs_lt]
    constructor <;> have h1 := d_lo ij <;> have h2 := d_lo kl <;>
      have h3 := d_hi ij <;> have h4 := d_hi kl <;> omega
  have diff_abs_add_alphaStar_lt_beta (ij kl : Fin M × Fin n) :
      |d ij - d kl| + (alphaStar α : ℤ) < (beta α M : ℤ) := by
    have habs : |d ij - d kl| ≤
        (beta α M : ℤ) - (alphaStar α : ℤ) - 1 := by
      rw [abs_sub_le_iff]
      constructor <;> have h1 := d_lo ij <;> have h2 := d_lo kl <;>
        have h3 := d_hi ij <;> have h4 := d_hi kl <;> omega
    omega
  have beta_gap (ij kl : Fin M × Fin n) (hrow : ij.1 ≠ kl.1) :
      (tau α : ℤ) ≤
        |(beta α (ij.1.val + 1) : ℤ) - (beta α (kl.1.val + 1) : ℤ)| := by
    have hval : ij.1.val ≠ kl.1.val := by
      intro h
      exact hrow (Fin.ext h)
    rcases lt_or_gt_of_ne hval with hlt | hlt
    · have hgap : beta α (ij.1.val + 1) + tau α ≤ beta α (kl.1.val + 1) := by
        calc
          beta α (ij.1.val + 1) + tau α = tau α * (ij.1.val + 2) := by
            simp [beta]
            ring
          _ ≤ tau α * (kl.1.val + 1) := Nat.mul_le_mul_left _ (by omega)
          _ = beta α (kl.1.val + 1) := rfl
      have hgapZ : (beta α (ij.1.val + 1) : ℤ) + (tau α : ℤ) ≤
          (beta α (kl.1.val + 1) : ℤ) := by exact_mod_cast hgap
      rw [abs_of_nonpos (by omega)]
      omega
    · have hgap : beta α (kl.1.val + 1) + tau α ≤ beta α (ij.1.val + 1) := by
        calc
          beta α (kl.1.val + 1) + tau α = tau α * (kl.1.val + 2) := by
            simp [beta]
            ring
          _ ≤ tau α * (ij.1.val + 1) := Nat.mul_le_mul_left _ (by omega)
          _ = beta α (ij.1.val + 1) := rfl
      have hgapZ : (beta α (kl.1.val + 1) : ℤ) + (tau α : ℤ) ≤
          (beta α (ij.1.val + 1) : ℤ) := by exact_mod_cast hgap
      rw [abs_of_nonneg (by omega)]
      omega
  have cross_lower (ij kl : Fin M × Fin n) (hrow : ij.1 ≠ kl.1) :
      (alphaStar α : ℤ) < |d ij - d kl| := by
    have hg := beta_gap ij kl hrow
    have ht : (tau α : ℤ) = 2 * (alphaStar α : ℤ) + 1 := by simp [tau]
    have haij := haZ ij.2
    have hakl := haZ kl.2
    rcases le_total 0 ((beta α (ij.1.val + 1) : ℤ) -
        (beta α (kl.1.val + 1) : ℤ)) with hb | hb
    · rw [abs_of_nonneg hb] at hg
      have hx : (alphaStar α : ℤ) + 1 ≤ d ij - d kl := by
        dsimp [d]
        omega
      rw [abs_of_nonneg (by omega)]
      omega
    · rw [abs_of_nonpos hb] at hg
      have hx : (alphaStar α : ℤ) + 1 ≤ d kl - d ij := by
        dsimp [d]
        omega
      rw [abs_of_nonpos (by omega)]
      omega
  have sum_lower (ij kl : Fin M × Fin n) :
      (alphaStar α : ℤ) < |d ij + d kl| := by
    have h1 := d_lo ij
    have h2 := d_lo kl
    rw [abs_of_nonneg (by omega)]
    omega
  have sum_abs_add_alphaStar_lt_q (ij kl : Fin M × Fin n) :
      |d ij + d kl| + (alphaStar α : ℤ) < (q : ℤ) := by
    have h1 := d_lo ij
    have h2 := d_lo kl
    have h3 := d_hi ij
    have h4 := d_hi kl
    rw [abs_of_nonneg (by omega)]
    omega
  have intCast_ne_zero {x : ℤ} (hx : x ≠ 0) (habs : |x| < (q : ℤ)) :
      (x : ZMod q) ≠ 0 := by
    intro h
    have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd x q).mp h
    exact hx (Int.eq_zero_of_abs_lt_dvd hdvd habs)
  have eq_of_cast_eq {x y : ℤ} (hsmall : |x - y| < (q : ℤ))
      (h : (x : ZMod q) = (y : ZMod q)) : x = y := by
    have hz : ((x - y : ℤ) : ZMod q) = 0 := by
      simp only [Int.cast_sub, sub_eq_zero]
      exact h
    have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd (x - y) q).mp hz
    exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hdvd hsmall)
  have d_injective : Function.Injective d := by
    intro ij kl h
    by_cases hrow : ij.1 = kl.1
    · have halpha : α ij.2 = α kl.2 := by
        have hid : (beta α (ij.1.val + 1) : ℤ) =
            (beta α (kl.1.val + 1) : ℤ) := by rw [hrow]
        dsimp [d] at h
        exact_mod_cast (show (α ij.2 : ℤ) = (α kl.2 : ℤ) by omega)
      exact Prod.ext hrow (hα.1.injective halpha)
    · have hc := cross_lower ij kl hrow
      rw [h] at hc
      simp at hc
      omega
  have offset_eq (ij : Fin M × Fin n) : offset q α ij = (d ij : ZMod q) := by
    simp [offset, d]
  have cast_d_injective : Function.Injective (fun ij => (d ij : ZMod q)) := by
    intro ij kl h
    exact d_injective (eq_of_cast_eq (diff_abs_small ij kl) h)
  have cast_d_ne_zero (ij : Fin M × Fin n) : (d ij : ZMod q) ≠ 0 := by
    apply intCast_ne_zero (d_ne_zero ij)
    rw [abs_of_nonneg (d_nonneg ij)]
    exact d_lt_q ij
  have cast_sum_ne_zero (ij kl : Fin M × Fin n) :
      ((d ij + d kl : ℤ) : ZMod q) ≠ 0 := by
    apply intCast_ne_zero
    · have h1 := d_lo ij
      have h2 := d_lo kl
      omega
    · have h := sum_abs_add_alphaStar_lt_q ij kl
      omega
  have hnonzero : ∀ ij ∈ incidences A, offset q α ij ≠ 0 ∧ -offset q α ij ≠ 0 := by
    intro ij hij
    rw [offset_eq]
    exact ⟨cast_d_ne_zero ij, neg_ne_zero.mpr (cast_d_ne_zero ij)⟩
  have hinj : Function.Injective (fun p : {ij // ij ∈ incidences A} × Bool =>
      if p.2 then offset q α p.1.val else -offset q α p.1.val) := by
    intro p r h
    rcases p with ⟨⟨ij, hij⟩, b⟩
    rcases r with ⟨⟨kl, hkl⟩, c⟩
    cases b <;> cases c <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    · have hd : (d ij : ZMod q) = (d kl : ZMod q) := by
        simpa only [← offset_eq] using (neg_inj.mp h)
      have heq := cast_d_injective hd
      subst kl
      rfl
    · have hz : ((d ij + d kl : ℤ) : ZMod q) = 0 := by
        simp only [Int.cast_add, ← offset_eq]
        rw [← h]
        simp
      exact (cast_sum_ne_zero ij kl hz).elim
    · have hz : ((d ij + d kl : ℤ) : ZMod q) = 0 := by
        simp only [Int.cast_add, ← offset_eq]
        rw [h]
        simp
      exact (cast_sum_ne_zero ij kl hz).elim
    · have hd : (d ij : ZMod q) = (d kl : ZMod q) := by
        simpa only [← offset_eq] using h
      have heq := cast_d_injective hd
      subst kl
      rfl
  have bad_repr {z : ZMod q} (hz : z ∈ Dbad q A α) :
      ∃ B : ℤ, (B : ZMod q) = z ∧ (alphaStar α : ℤ) < |B| ∧
        |B| + (alphaStar α : ℤ) < (q : ℤ) := by
    rw [Dbad, Finset.mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨p, hp, hpz⟩ := Finset.mem_image.mp hz
      rw [Finset.mem_filter] at hp
      refine ⟨d p.1 - d p.2, ?_, cross_lower p.1 p.2 hp.2, ?_⟩
      · simp only [Int.cast_sub, ← offset_eq]
        exact hpz
      · have h := diff_abs_add_alphaStar_lt_beta p.1 p.2
        omega
    · obtain ⟨p, hp, hpz⟩ := Finset.mem_image.mp hz
      refine ⟨d p.1 + d p.2, ?_, sum_lower p.1 p.2,
        sum_abs_add_alphaStar_lt_q p.1 p.2⟩
      simp only [Int.cast_add, ← offset_eq]
      exact hpz
  have hzero : 0 ∉ Dbad q A α := by
    intro hz
    obtain ⟨B, hB, hBlo, hBq⟩ := bad_repr hz
    apply intCast_ne_zero (x := B) (by
      intro h
      rw [h] at hBlo
      simp only [abs_zero] at hBlo
      omega) (by omega)
    exact hB
  have hdisjoint : Disjoint (Dbad q A α) (Dwit q α) := by
    rw [Finset.disjoint_left]
    intro z hzbad hzwit
    obtain ⟨B, hB, hBlo, hBq⟩ := bad_repr hzbad
    obtain ⟨jl, hjl, hjlz⟩ := Finset.mem_image.mp hzwit
    let w : ℤ := (α jl.2 : ℤ) - (α jl.1 : ℤ)
    have hw : |w| ≤ (alphaStar α : ℤ) := by
      rw [abs_sub_le_iff]
      constructor
      · have h1 := haZ jl.1
        have h2 := haZ jl.2
        omega
      · have h1 := haZ jl.1
        have h2 := haZ jl.2
        omega
    have hBw : |B - w| < (q : ℤ) := by
      have htri : |B - w| ≤ |B| + |w| := abs_sub B w
      omega
    have hcast : (B : ZMod q) = (w : ZMod q) := by
      rw [hB]
      dsimp [w]
      simp only [Int.cast_sub, Int.cast_natCast]
      exact hjlz.symm
    have heq := eq_of_cast_eq hBw hcast
    rw [heq] at hBlo
    omega
  have hW : W A = 3 * n := by
    unfold W
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ) (by
      intro x hx
      simp)]
    have hfiber (j : Fin n) : {a ∈ incidences A | a.2 = j}.card = 3 := by
      have heq : {a ∈ incidences A | a.2 = j} =
          (Finset.univ.filter fun i => A i j) ×ˢ ({j} : Finset (Fin n)) := by
        ext ⟨i, k⟩
        simp only [incidences, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_product, Finset.mem_singleton]
        constructor
        · rintro ⟨hAik, rfl⟩
          exact ⟨hAik, rfl⟩
        · rintro ⟨hAij, hjk⟩
          subst k
          exact ⟨hAij, rfl⟩
      rw [heq, Finset.card_product, hA j]
      simp
    simp [hfiber, Nat.mul_comm]
  have hcard : (Dbad q A α).card ≤ 2 * W A ^ 2 := by
    unfold Dbad
    calc
      (((incidences A ×ˢ incidences A).filter fun p => p.1.1 ≠ p.2.1).image
          (fun p => offset q α p.1 - offset q α p.2) ∪
        (incidences A ×ˢ incidences A).image
          (fun p => offset q α p.1 + offset q α p.2)).card ≤
          (((incidences A ×ˢ incidences A).filter fun p => p.1.1 ≠ p.2.1).image
            (fun p => offset q α p.1 - offset q α p.2)).card +
          ((incidences A ×ˢ incidences A).image
            (fun p => offset q α p.1 + offset q α p.2)).card :=
        Finset.card_union_le _ _
      _ ≤ ((incidences A ×ˢ incidences A).filter fun p => p.1.1 ≠ p.2.1).card +
          (incidences A ×ˢ incidences A).card :=
        Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ ≤ (incidences A ×ˢ incidences A).card +
          (incidences A ×ˢ incidences A).card :=
        Nat.add_le_add (Finset.card_filter_le _ _) (le_refl _)
      _ = 2 * W A ^ 2 := by
        simp [W, pow_two]
        ring
  refine ⟨hnonzero, hinj, hzero, hdisjoint, hcard, ?_⟩
  calc
    (Dbad q A α).card ≤ 2 * W A ^ 2 := hcard
    _ = 18 * n ^ 2 := by rw [hW]; ring
