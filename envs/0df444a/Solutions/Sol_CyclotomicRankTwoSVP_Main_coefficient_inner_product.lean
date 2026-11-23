-- Prove2me | solution 1 for CyclotomicRankTwoSVP.Main.coefficient_inner_product
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:56:23.865801+00:00
-- url     : https://prove2.me/submissions/ed636bf0-64fb-43a9-94da-3391cefbcf19

import Mathlib
import Definitions.Def_CyclotomicRankTwoSVP_Main_Arithmetic

noncomputable section
namespace CyclotomicRankTwoSVP.Main
open scoped BigOperators

private lemma zeta_primitive (q : ℕ) [Fact q.Prime] : IsPrimitiveRoot (zeta q) q := by
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  letI : NeZero q := ⟨hq0⟩
  letI : NeZero (q : ℚ) := ⟨Nat.cast_ne_zero.mpr hq0⟩
  letI : IsCyclotomicExtension {q} ℚ (K q) := CyclotomicField.isCyclotomicExtension q ℚ
  simp only [zeta, dif_neg hq0]
  exact IsCyclotomicExtension.zeta_spec q ℚ (K q)

private lemma sum_embeddings_eq_sum_units (q : ℕ) [Fact q.Prime]
    (c : ℂ) (hc : IsPrimitiveRoot c q) (F : ℂ → ℝ) :
    (∑ σ : K q →ₐ[ℚ] ℂ, F (σ (zeta q))) =
      ∑ t : (ZMod q)ˣ, F (c ^ (t : ZMod q).val) := by
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hqpos : 0 < q := (Fact.out : q.Prime).pos
  letI : NeZero q := ⟨hq0⟩
  letI : NeZero (q : ℚ) := ⟨Nat.cast_ne_zero.mpr hq0⟩
  letI : IsCyclotomicExtension {q} ℚ (K q) := CyclotomicField.isCyclotomicExtension q ℚ
  have hζ := zeta_primitive q
  let pb := hζ.powerBasis ℚ
  have hgen : pb.gen = zeta q := hζ.powerBasis_gen ℚ
  have hmin : minpoly ℚ (zeta q) = Polynomial.cyclotomic q ℚ :=
    (hζ.minpoly_eq_cyclotomic_of_irreducible (Polynomial.cyclotomic.irreducible_rat hqpos)).symm
  have hex (σ : K q →ₐ[ℚ] ℂ) :
      ∃ i < q, c ^ i = σ (zeta q) :=
    hc.eq_pow_of_pow_eq_one ((hζ.map_of_injective σ.injective).pow_eq_one)
  let idx (σ : K q →ₐ[ℚ] ℂ) : ℕ := Classical.choose (hex σ)
  have idx_lt (σ : K q →ₐ[ℚ] ℂ) : idx σ < q := (Classical.choose_spec (hex σ)).1
  have idx_pow (σ : K q →ₐ[ℚ] ℂ) : c ^ idx σ = σ (zeta q) :=
    (Classical.choose_spec (hex σ)).2
  have idx_coprime (σ : K q →ₐ[ℚ] ℂ) : (idx σ).Coprime q := by
    apply (hc.pow_iff_coprime hqpos (idx σ)).mp
    rw [idx_pow]
    exact hζ.map_of_injective σ.injective
  let eu (σ : K q →ₐ[ℚ] ℂ) : (ZMod q)ˣ :=
    ((ZMod.isUnit_iff_coprime (idx σ) q).mpr (idx_coprime σ)).unit
  have eu_val (σ : K q →ₐ[ℚ] ℂ) : ((eu σ : ZMod q).val) = idx σ := by
    have h := congrArg ZMod.val
      (((ZMod.isUnit_iff_coprime (idx σ) q).mpr (idx_coprime σ)).unit_spec)
    simpa only [ZMod.val_natCast_of_lt (idx_lt σ)] using h
  have eu_pow (σ : K q →ₐ[ℚ] ℂ) : c ^ ((eu σ : ZMod q).val) = σ (zeta q) := by
    rw [eu_val]
    exact idx_pow σ
  apply Finset.sum_bij (fun σ _ => eu σ)
  · intro σ hσ
    exact Finset.mem_univ _
  · intro σ _ τ _ hst
    apply pb.algHom_ext
    rw [hgen]
    have h := congrArg (fun t : (ZMod q)ˣ => c ^ (t : ZMod q).val) hst
    exact (eu_pow σ).symm.trans (h.trans (eu_pow τ))
  · intro t _
    have hcop : ((t : ZMod q).val).Coprime q := by
      rw [← ZMod.isUnit_iff_coprime]
      simpa only [ZMod.natCast_val, ZMod.cast_id] using t.isUnit
    have hprim : IsPrimitiveRoot (c ^ (t : ZMod q).val) q := hc.pow_of_coprime _ hcop
    have hroot : Polynomial.aeval (c ^ (t : ZMod q).val) (minpoly ℚ (zeta q)) = 0 := by
      rw [hmin, Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_cyclotomic]
      exact hprim.isRoot_cyclotomic hqpos
    let σ : K q →ₐ[ℚ] ℂ := pb.lift (c ^ (t : ZMod q).val) hroot
    have hσ : σ (zeta q) = c ^ (t : ZMod q).val := by
      change (pb.lift (c ^ (t : ZMod q).val) hroot) (zeta q) = _
      rw [← hgen]
      exact pb.lift_gen _ _
    refine ⟨σ, Finset.mem_univ _, ?_⟩
    apply Units.ext
    apply ZMod.val_injective q
    rw [eu_val]
    apply hc.pow_inj (idx_lt σ) (ZMod.val_lt _)
    rw [idx_pow, hσ]
  · intro σ _
    rw [eu_pow]

private lemma sum_units_pow (q : ℕ) [Fact q.Prime] (z : ℂ) (hzq : z ^ q = 1) :
    (∑ t : (ZMod q)ˣ, z ^ (t : ZMod q).val) =
      if z = 1 then ((q - 1 : ℕ) : ℂ) else -1 := by
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hqpos : 0 < q := (Fact.out : q.Prime).pos
  letI : NeZero q := ⟨hq0⟩
  by_cases hz : z = 1
  · subst z
    simp [ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : q.Prime)]
  · rw [if_neg hz]
    have hreindex : (∑ t : (ZMod q)ˣ, z ^ (t : ZMod q).val) =
        ∑ i ∈ (Finset.range q).erase 0, z ^ i := by
      refine Finset.sum_bij (s := Finset.univ) (t := (Finset.range q).erase 0)
        (fun t _ => (t : ZMod q).val) ?_ ?_ ?_ ?_
      · intro t _
        simp only [Finset.mem_erase, Finset.mem_range]
        refine ⟨?_, ZMod.val_lt _⟩
        intro hv
        exact (Units.ne_zero t) ((ZMod.val_eq_zero _).mp hv)
      · intro s _ t _ hst
        apply Units.ext
        apply ZMod.val_injective q
        exact hst
      · intro i hi
        simp only [Finset.mem_erase, Finset.mem_range] at hi
        have hci : (i : ZMod q) ≠ 0 := by
          intro h
          have hv := congrArg ZMod.val h
          simp only [ZMod.val_natCast_of_lt hi.2, ZMod.val_zero] at hv
          exact hi.1 hv
        let u : (ZMod q)ˣ := (isUnit_iff_ne_zero.mpr hci).unit
        refine ⟨u, Finset.mem_univ _, ?_⟩
        have h := congrArg ZMod.val ((isUnit_iff_ne_zero.mpr hci).unit_spec)
        simpa only [ZMod.val_natCast_of_lt hi.2] using h
      · intros
        rfl
    rw [hreindex]
    have hfull : ∑ i ∈ Finset.range q, z ^ i = 0 := by
      rw [geom_sum_eq hz q, hzq]
      simp
    have herase := Finset.sum_erase_add (Finset.range q) (fun i => z ^ i)
      (Finset.mem_range.mpr hqpos)
    rw [hfull, pow_zero] at herase
    linear_combination herase

private lemma root_unit_sum_re (q : ℕ) [Fact q.Prime]
    (c : ℂ) (hc : IsPrimitiveRoot c q) (a b : ZMod q) :
    (∑ t : (ZMod q)ˣ, (c ^ ((t : ZMod q).val * a.val) *
      star (c ^ ((t : ZMod q).val * b.val))).re) =
      if a = b then (q : ℝ) - 1 else -1 := by
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hqpos : 0 < q := (Fact.out : q.Prime).pos
  letI : NeZero q := ⟨hq0⟩
  have hcne : c ≠ 0 := hc.ne_zero hq0
  have hnorm : ‖c‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hc.pow_eq_one hq0
  have hstar : star c = c⁻¹ := by
    rw [Complex.star_def, ← Complex.inv_eq_conj hnorm]
  let z : ℂ := c ^ a.val * star (c ^ b.val)
  have hz : ∀ t : (ZMod q)ˣ,
      c ^ ((t : ZMod q).val * a.val) * star (c ^ ((t : ZMod q).val * b.val)) =
        z ^ (t : ZMod q).val := by
    intro t
    simp only [z, mul_pow, star_pow, pow_mul]
    ring
  have hzq : z ^ q = 1 := by
    calc
      z ^ q = (c ^ q) ^ a.val * star ((c ^ q) ^ b.val) := by
        simp only [z, star_pow, mul_pow, ← pow_mul]
        ring
      _ = 1 := by rw [hc.pow_eq_one]; simp
  have hziff : z = 1 ↔ a = b := by
    constructor
    · intro hzone
      change c ^ a.val * star (c ^ b.val) = 1 at hzone
      have hzpow : c ^ ((a.val : ℤ) - b.val) = 1 := by
        rw [zpow_sub₀ hcne, zpow_natCast, zpow_natCast, div_eq_one_iff_eq (pow_ne_zero _ hcne)]
        have h := congrArg (fun w : ℂ => w * c ^ b.val) hzone
        simpa [hstar, mul_assoc, pow_ne_zero _ hcne] using h
      have hdvd : (q : ℤ) ∣ (a.val : ℤ) - b.val :=
        (hc.zpow_eq_one_iff_dvd _).mp hzpow
      have hn : (q : ℤ).natAbs ∣ ((a.val : ℤ) - b.val).natAbs :=
        Int.natAbs_dvd_natAbs.mpr hdvd
      simp only [Int.natAbs_natCast] at hn
      have hz0 : ((a.val : ℤ) - b.val).natAbs = 0 := by
        apply Nat.eq_zero_of_dvd_of_lt hn
        have ha := ZMod.val_lt a
        have hb := ZMod.val_lt b
        omega
      have hab : a.val = b.val := by
        have := Int.natAbs_eq_zero.mp hz0
        omega
      exact ZMod.val_injective q hab
    · rintro rfl
      simp [z, hstar, hcne]
  simp_rw [hz]
  rw [← Complex.re_sum, sum_units_pow q z hzq]
  by_cases hab : a = b
  · have hz1 : z = 1 := hziff.mpr hab
    rw [if_pos hz1, if_pos hab]
    norm_num [Nat.cast_sub hqpos]
  · have hz1 : z ≠ 1 := fun h => hab (hziff.mp h)
    rw [if_neg hz1, if_neg hab]
    norm_num

private lemma term_re (x y : ℚ) (u v : ℂ) :
    (((x : ℂ) * u) * star ((y : ℂ) * v)).re =
      (x : ℝ) * (y : ℝ) * (u * star v).re := by
  simp [Complex.mul_re, Complex.mul_im]
  ring

private lemma expansion_re {q : ℕ} [NeZero q]
    (x y : ZMod q → ℚ) (u v : ZMod q → ℂ) :
    ((∑ a, (x a : ℂ) * u a) * star (∑ b, (y b : ℂ) * v b)).re =
      ∑ a, ∑ b, (x a : ℝ) * (y b : ℝ) * (u a * star (v b)).re := by
  simp only [star_sum, Finset.mul_sum, Finset.sum_mul, Complex.re_sum, term_re]
  rw [Finset.sum_comm]

private lemma double_delta {R : Type*} [CommRing R] (q : ℕ) [NeZero q]
    (x y : ZMod q → R) (r : R) :
    (∑ a, ∑ b, x a * y b * (if a = b then r - 1 else -1)) =
      r * (∑ a, x a * y a) - (∑ a, x a) * (∑ a, y a) := by
  classical
  have hrow (a : ZMod q) :
      (∑ b, x a * y b * (if a = b then r - 1 else -1)) =
        x a * y a * (r - 1) - ∑ b ∈ Finset.univ.erase a, x a * y b := by
    calc
      _ = (∑ b ∈ Finset.univ.erase a, x a * y b * (if a = b then r - 1 else -1)) +
          x a * y a * (if a = a then r - 1 else -1) :=
        (Finset.sum_erase_add Finset.univ _ (Finset.mem_univ a)).symm
      _ = _ := by
        rw [if_pos rfl]
        have hoff : (∑ b ∈ Finset.univ.erase a,
            x a * y b * (if a = b then r - 1 else -1)) =
            -(∑ b ∈ Finset.univ.erase a, x a * y b) := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro b hb
          have hba : b ≠ a := (Finset.mem_erase.mp hb).1
          rw [if_neg (Ne.symm hba)]
          ring
        rw [hoff]
        ring
  simp_rw [hrow]
  rw [Finset.sum_sub_distrib]
  have herase (a : ZMod q) :
      (∑ b ∈ Finset.univ.erase a, x a * y b) = x a * (∑ b, y b) - x a * y a := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (ZMod q)) (fun b => x a * y b)
      (Finset.mem_univ a)
    rw [Finset.mul_sum]
    linear_combination h
  simp_rw [herase]
  rw [Finset.sum_sub_distrib]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

private lemma ordered_diff_sq (q : ℕ) [NeZero q] (v : ZMod q → ℝ) :
    (∑ a, ∑ b, if a.val < b.val then (v a - v b) ^ 2 else 0) =
      (q : ℝ) * (∑ a, v a ^ 2) - (∑ a, v a) * (∑ a, v a) := by
  have hcross2 : (∑ a, ∑ b, 2 * v a * v b) =
      2 * (∑ a, ∑ b, v b * v a) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have hsplit (a b : ZMod q) : (v a - v b) ^ 2 =
      (if a.val < b.val then (v a - v b) ^ 2 else 0) +
      (if b.val < a.val then (v a - v b) ^ 2 else 0) := by
    by_cases hab : a = b
    · subst b
      simp
    · have hne : a.val ≠ b.val := fun h => hab (ZMod.val_injective q h)
      rcases lt_or_gt_of_ne hne with h | h
      · simp [h, show ¬ b.val < a.val by omega]
      · simp [h, show ¬ a.val < b.val by omega]
  have hswap :
      (∑ a, ∑ b, (if b.val < a.val then (v a - v b) ^ 2 else 0)) =
      ∑ a, ∑ b, (if a.val < b.val then (v a - v b) ^ 2 else 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    by_cases h : a.val < b.val <;> simp [h] <;> ring
  have hT : (∑ a, ∑ b, (v a - v b) ^ 2) =
      2 * (∑ a, ∑ b, if a.val < b.val then (v a - v b) ^ 2 else 0) := by
    calc
      _ = ∑ a, ((∑ b, (if a.val < b.val then (v a - v b) ^ 2 else 0)) +
          ∑ b, (if b.val < a.val then (v a - v b) ^ 2 else 0)) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro b hb
        exact hsplit a b
      _ = (∑ a, ∑ b, (if a.val < b.val then (v a - v b) ^ 2 else 0)) +
          ∑ a, ∑ b, (if b.val < a.val then (v a - v b) ^ 2 else 0) :=
        Finset.sum_add_distrib
      _ = _ := by rw [hswap]; ring
  have halg : (∑ a, ∑ b, (v a - v b) ^ 2) =
      2 * ((q : ℝ) * (∑ a, v a ^ 2) - (∑ a, v a) * (∑ a, v a)) := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.mul_sum, Finset.sum_mul, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul]
    rw [hcross2]
    ring
  apply mul_left_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num)
  exact hT.symm.trans halg

private lemma N_eq_canonicalInner {q : ℕ} (y : K q) : N y = canonicalInner y y := by
  unfold N canonicalInner
  apply Finset.sum_congr rfl
  intro σ hσ
  have h := RCLike.mul_conj (σ y)
  rw [Complex.star_def, h]
  norm_cast

private lemma evalQ_intCast {q : ℕ} [NeZero q] (z : ZMod q → ℤ) :
    evalQ (fun a => (z a : ℚ)) = evalZ z := by
  unfold evalQ evalZ
  apply Finset.sum_congr rfl
  intro a ha
  norm_num

theorem solution (q : ℕ) [Fact q.Prime] (hq : Odd q) :
    (∀ x y : ZMod q → ℚ,
      canonicalInner (evalQ x) (evalQ y) =
        q * (∑ a, (x a : ℝ) * (y a : ℝ)) - (∑ a, (x a : ℝ)) * (∑ a, (y a : ℝ))) ∧
    (∀ z : ZMod q → ℤ,
      N (evalZ z) = q * coeffNorm z - (coeffSum z : ℝ) ^ 2 ∧
      N (evalZ z) = ∑ a, ∑ b, if a.val < b.val then ((z a : ℝ) - z b) ^ 2 else 0) := by
  have hq0 : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  letI : NeZero q := ⟨hq0⟩
  let c : ℂ := Complex.exp (2 * Real.pi * Complex.I / q)
  have hc : IsPrimitiveRoot c q := Complex.isPrimitiveRoot_exp q hq0
  have hemb (σ : K q →ₐ[ℚ] ℂ) (x : ZMod q → ℚ) :
      σ (evalQ x) = ∑ a, (x a : ℂ) * (σ (zeta q)) ^ a.val := by
    simp [evalQ, AlgHom.commutes]
  have hinner : ∀ x y : ZMod q → ℚ,
      canonicalInner (evalQ x) (evalQ y) =
        q * (∑ a, (x a : ℝ) * (y a : ℝ)) - (∑ a, (x a : ℝ)) * (∑ a, (y a : ℝ)) := by
    intro x y
    calc
      canonicalInner (evalQ x) (evalQ y) =
          ∑ σ : K q →ₐ[ℚ] ℂ,
            (((∑ a, (x a : ℂ) * (σ (zeta q)) ^ a.val) *
              star (∑ b, (y b : ℂ) * (σ (zeta q)) ^ b.val)).re) := by
        unfold canonicalInner
        apply Finset.sum_congr rfl
        intro σ hσ
        rw [hemb, hemb]
      _ = ∑ σ : K q →ₐ[ℚ] ℂ, ∑ a, ∑ b, (x a : ℝ) * (y b : ℝ) *
          ((σ (zeta q)) ^ a.val * star ((σ (zeta q)) ^ b.val)).re := by
        apply Finset.sum_congr rfl
        intro σ hσ
        exact expansion_re x y _ _
      _ = ∑ a, ∑ b, (x a : ℝ) * (y b : ℝ) *
          ∑ σ : K q →ₐ[ℚ] ℂ, ((σ (zeta q)) ^ a.val * star ((σ (zeta q)) ^ b.val)).re := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b hb
        rw [Finset.mul_sum]
      _ = ∑ a, ∑ b, (x a : ℝ) * (y b : ℝ) *
          ∑ t : (ZMod q)ˣ, (c ^ ((t : ZMod q).val * a.val) *
            star (c ^ ((t : ZMod q).val * b.val))).re := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        rw [sum_embeddings_eq_sum_units q c hc
          (fun z : ℂ => (z ^ a.val * star (z ^ b.val)).re)]
        simp only [pow_mul]
      _ = ∑ a, ∑ b, (x a : ℝ) * (y b : ℝ) *
          (if a = b then (q : ℝ) - 1 else -1) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        rw [root_unit_sum_re q c hc a b]
      _ = _ := double_delta q (fun a => (x a : ℝ)) (fun a => (y a : ℝ)) (q : ℝ)
  refine ⟨hinner, ?_⟩
  intro z
  have hnorm : N (evalZ z) = q * coeffNorm z - (coeffSum z : ℝ) ^ 2 := by
    rw [N_eq_canonicalInner, ← evalQ_intCast z, hinner]
    simp only [Rat.cast_intCast, coeffNorm, coeffSum, Int.cast_sum, Int.cast_pow]
    ring
  refine ⟨hnorm, ?_⟩
  rw [hnorm, ordered_diff_sq q (fun a => (z a : ℝ))]
  simp only [coeffNorm, coeffSum, Int.cast_sum, Int.cast_pow]
  ring

end CyclotomicRankTwoSVP.Main

open CyclotomicRankTwoSVP.Main
open scoped BigOperators

theorem solution (q : ℕ) [Fact q.Prime] (hq : Odd q) :
    (∀ x y : ZMod q → ℚ,
      canonicalInner (evalQ x) (evalQ y) =
        q * (∑ a, (x a : ℝ) * (y a : ℝ)) - (∑ a, (x a : ℝ)) * (∑ a, (y a : ℝ))) ∧
    (∀ z : ZMod q → ℤ,
      N (evalZ z) = q * coeffNorm z - (coeffSum z : ℝ) ^ 2 ∧
      N (evalZ z) = ∑ a, ∑ b, if a.val < b.val then ((z a : ℝ) - z b) ^ 2 else 0) :=
  CyclotomicRankTwoSVP.Main.solution q hq
