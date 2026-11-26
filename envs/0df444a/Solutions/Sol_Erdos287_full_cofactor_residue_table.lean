-- Prove2me | solution 1 for Erdos287.full_cofactor_residue_table
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T11:53:21.446055+00:00
-- url     : https://prove2.me/submissions/68c68bcb-2a85-495c-ae20-b0cf297d3534

import Mathlib
import Theorems.Thm_Erdos287_cofactor_adic_period

open Finset

set_option autoImplicit false
set_option maxHeartbeats 1500000

private theorem norm_iff_cofactor_carry {p : ℕ} [Fact p.Prime] (T : Finset ℕ)
    (c : ℕ) (hc : 0 < c) :
    let L := ∏ d ∈ T, (c + d)
    let A := ∑ i ∈ T, ∏ d ∈ T.erase i, (c + d)
    padicNorm p (∑ d ∈ T, (1 : ℚ) / ((c + d : ℕ) : ℚ)) ≤ (p : ℚ)⁻¹ ↔
      p ^ (padicValNat p L + 1) ∣ A := by
  intro L A
  have hp : p.Prime := Fact.out
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp.pos
  have hLpos : 0 < L := by
    change 0 < ∏ d ∈ T, (c + d)
    exact prod_pos (fun d _ => by omega)
  have hLQ : (0 : ℚ) < L := by exact_mod_cast hLpos
  have hscaled : (∑ d ∈ T, (1 : ℚ) / ((c + d : ℕ) : ℚ)) = (A : ℚ) / L := by
    change _ = ((∑ i ∈ T, ∏ d ∈ T.erase i, (c + d) : ℕ) : ℚ) / L
    rw [Nat.cast_sum, Finset.sum_div]
    apply sum_congr rfl
    intro d hd
    have hdQ : (0 : ℚ) < ((c + d : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < c + d)
    apply (div_eq_div_iff hdQ.ne' hLQ.ne').mpr
    rw [one_mul]
    exact_mod_cast (prod_erase_mul T (fun b => c + b) hd).symm
  let j := padicValNat p L
  have hnorm : padicNorm p (L : ℚ) = (p : ℚ) ^ (-(j : ℤ)) := by
    rw [padicNorm.eq_zpow_of_nonzero hLQ.ne', padicValRat.of_nat]
  have hpow : (p : ℚ)⁻¹ * (p : ℚ) ^ (-(j : ℤ)) = (p : ℚ) ^ (-((j + 1 : ℕ) : ℤ)) := by
    rw [← zpow_neg_one, ← zpow_add₀ hpQ.ne']
    congr 1
    omega
  rw [hscaled, padicNorm.div, hnorm, div_le_iff₀ (zpow_pos hpQ _), hpow]
  have ha := (padicNorm.dvd_iff_norm_le (p := p) (n := j + 1) (z := (A : ℤ))).symm
  simpa only [Int.cast_natCast, Int.natCast_dvd_natCast] using ha

/-- A finite residue table for arbitrary cofactor patterns. The table
checks the full divisibility by the carry modulus in a positive
representative of each translation class. -/
theorem solution (p h : ℕ) (hp : p.Prime) (F : Finset (Finset ℕ))
    (hwidth : ∀ T ∈ F, ∀ a ∈ T, ∀ b ∈ T, a < b + p ^ (h + 1)) :
    let P := p ^ (2 * h + 1)
    ∃ R : Finset (ZMod P),
      (∀ z : ZMod P, z ∈ R ↔ ∃ T ∈ F, T.Nonempty ∧
        let c := z.val + P
        let L := ∏ d ∈ T, (c + d)
        p ^ (padicValNat p L + 1) ∣ ∑ i ∈ T, ∏ d ∈ T.erase i, (c + d)) ∧
      ∀ (D : Finset ℕ) (e c : ℕ), 1 ≤ e → 0 < c →
        (∀ n ∈ D, 0 < n) → (∑ n ∈ D, (1 : ℚ) / n = 1) →
        ∀ T ∈ F,
          T.image (fun d => (c + d) * p ^ e) = D.filter (fun n => p ^ e ∣ n) →
          T.Nonempty → (c : ZMod P) ∈ R := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro P
  have hP : 0 < P := pow_pos hp.pos _
  have : NeZero P := ⟨hP.ne'⟩
  let good (z : ZMod P) (T : Finset ℕ) : Prop :=
    let c := z.val + P
    let L := ∏ d ∈ T, (c + d)
    p ^ (padicValNat p L + 1) ∣ ∑ i ∈ T, ∏ d ∈ T.erase i, (c + d)
  let R : Finset (ZMod P) := univ.filter (fun z => ∃ T ∈ F, T.Nonempty ∧ good z T)
  refine ⟨R, fun z => by simp [R, good], ?_⟩
  intro D e c he hc hpos hsum T hT hshape hne
  let z : ZMod P := c
  have hmod : c ≡ z.val + P [MOD P] := by
    apply (ZMod.natCast_eq_natCast_iff c (z.val + P) P).mp
    rw [Nat.cast_add, ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val]
  have hrep : 0 < z.val + P := by omega
  have hcN := (Erdos287.cofactor_adic_period p hp).1 D T e c he hc hpos hsum hshape
  have hshift := (Erdos287.cofactor_adic_period p hp).2 T h c (z.val + P)
    hc hrep (hwidth T hT) hmod
  have hgood : good z T := (norm_iff_cofactor_carry (p := p) T (z.val + P) hrep).mp (hshift.mp hcN)
  exact mem_filter.mpr ⟨mem_univ _, T, hT, hne, hgood⟩

