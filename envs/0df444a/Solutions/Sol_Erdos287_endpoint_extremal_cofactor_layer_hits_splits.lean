-- Prove2me | solution 1 for Erdos287.endpoint_extremal_cofactor_layer_hits_splits
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-27T00:40:35.280688+00:00
-- url     : https://prove2.me/submissions/b556251e-1bfb-469d-a983-5061a83bab8c

import Mathlib
import Theorems.Thm_Erdos287_cofactor_cut_congruence
import Theorems.Thm_Erdos287_endpoint_extremal_cover_trimmed_mass_obstruction

open Finset

set_option autoImplicit false

/-- The prime-power layer containing the lower endpoint passes the carry
test and meets every in-range reciprocal decomposition of that endpoint
within the same layer. -/
theorem solution (D : Finset ℕ) (p e c M L j : ℕ) (hp : p.Prime) (he : 1 ≤ e)
    (hLp : p ^ j ∣ L) :
    let q := p ^ e
    let m := c * q
    let U := Finset.Icc c (M / q)
    let C := U.filter (fun a => a * q ∈ D)
    1 < m → m ∈ D → D ⊆ Finset.Icc m M →
    (∀ x, m ≤ x → x + 1 ≤ M → x ∈ D ∨ x + 1 ∈ D) →
    (∑ n ∈ D, (1 : ℚ) / n = 1) →
    (∀ (a b : ℕ) (F : Finset ℕ), 1 < a → a ∈ F → b ∈ F →
      F ⊆ Finset.Icc a b → (∀ x, a ≤ x → x + 1 ≤ b → x ∈ F ∨ x + 1 ∈ F) →
      (∑ n ∈ F, (1 : ℚ) / n = 1) → M ≤ b ∧ (b = M → a ≤ m)) →
    (∀ a ∈ U, a ∣ L) →
    c ∈ C ∧ p ^ (j + 1) ∣ (∑ a ∈ C, L / a) ∧
      ∀ A ⊆ Finset.Ioc c (M / q), (∑ a ∈ A, (1 : ℚ) / a = (1 : ℚ) / c) →
        ∃ a ∈ A, a ∈ C := by
  classical
  intro q m U C hm hmD hD hcover hsum hEnd hL
  have hq : 0 < q := pow_pos hp.pos _
  have hmM : m ≤ M := (mem_Icc.mp (hD hmD)).2
  have hcM : c ≤ M / q := (Nat.le_div_iff_mul_le hq).mpr hmM
  have hC : c ∈ C := mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hcM⟩, hmD⟩
  have cofactor {n : ℕ} (hn : n ∈ D) (hd : q ∣ n) : n / q ∈ U := by
    have hI := mem_Icc.mp (hD hn)
    exact mem_Icc.mpr ⟨(Nat.le_div_iff_mul_le hq).mpr hI.1, Nat.div_le_div_right hI.2⟩
  have hImage : C.image (fun a => a * q) = D.filter (fun n => q ∣ n) := by
    ext n
    constructor
    · rintro hn
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hn
      exact mem_filter.mpr ⟨(mem_filter.mp ha).2, dvd_mul_left q a⟩
    · intro hn
      obtain ⟨hnD, hnd⟩ := mem_filter.mp hn
      have heq := Nat.div_mul_cancel hnd
      exact mem_image.mpr ⟨n / q, mem_filter.mpr ⟨cofactor hnD hnd, heq.symm ▸ hnD⟩, heq⟩
  have hInj : Function.Injective (fun a : ℕ => a * q) :=
    fun _ _ h => Nat.eq_of_mul_eq_mul_right hq h
  have hDiv : p ^ (j + 1) ∣ ∑ a ∈ C, L / a := by
    have carry := Erdos287.cofactor_cut_congruence D p e L j hp he
      (fun n hn => hm.le.trans (mem_Icc.mp (hD hn)).1) hsum
      (fun n hn hnd => hL _ (cofactor hn hnd)) hLp
    change p ^ (j + 1) ∣ ∑ n ∈ D.filter (fun n => q ∣ n), L / (n / q) at carry
    rw [← hImage, sum_image hInj.injOn] at carry
    simpa only [Nat.mul_div_cancel _ hq] using carry
  refine ⟨hC, hDiv, ?_⟩
  intro A hA hexact
  by_contra! hmiss
  let B := A.image (fun a => a * q)
  have hB : B ⊆ Icc (m + 1) M := by
    intro n hn
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hn
    obtain ⟨hla, hau⟩ := mem_Ioc.mp (hA ha)
    exact mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.mul_lt_mul_of_pos_right hla hq),
      (Nat.le_div_iff_mul_le hq).mp hau⟩
  have hBD : Disjoint B D := disjoint_left.mpr (fun {n} hn hnd => by
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hn
    obtain ⟨hla, hau⟩ := mem_Ioc.mp (hA ha)
    exact hmiss a ha (mem_filter.mpr ⟨mem_Icc.mpr ⟨hla.le, hau⟩, hnd⟩))
  have hTrim : D.filter (fun n => n < m + 1 ∨ M < n) = {m} := by
    ext n
    simp only [mem_filter, mem_singleton]
    constructor
    · rintro ⟨hn, hnm⟩
      have hi := mem_Icc.mp (hD hn)
      omega
    · rintro rfl
      exact ⟨hmD, Or.inl (by omega)⟩
  have hEq : ∑ n ∈ B, (1 : ℚ) / n = (1 : ℚ) / m := by
    change (∑ n ∈ A.image (fun a => a * q), (1 : ℚ) / n) = _
    rw [sum_image hInj.injOn]
    calc
      (∑ a ∈ A, (1 : ℚ) / ((a * q : ℕ) : ℚ)) = ∑ a ∈ A, ((1 : ℚ) / a) / q := by
        apply sum_congr rfl
        intro a _
        rw [Nat.cast_mul, div_div]
      _ = (1 : ℚ) / m := by rw [← sum_div, hexact, div_div, ← Nat.cast_mul]
  have hblock := Erdos287.endpoint_extremal_cover_trimmed_mass_obstruction D B m M (m + 1) M
    hm hcover hsum hEnd (by omega) le_rfl (Or.inl (by omega)) hB hBD
  rw [hTrim, sum_singleton] at hblock
  exact hblock hEq

