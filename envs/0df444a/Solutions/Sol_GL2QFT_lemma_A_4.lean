-- Prove2me | solution 1 for GL2QFT.lemma_A_4
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T03:21:39.217962+00:00
-- url     : https://prove2.me/submissions/ac6061f9-9c38-40c2-92b2-8ec5e49c7c17

import Definitions.Def_GL2QFT_Characters

noncomputable section

open Classical
open scoped ComplexConjugate

namespace GL2QFT

namespace FieldData

/-! ### Helper lemmas for field cardinalities, generators, and characters -/

lemma card_Fq (D : FieldData) : Fintype.card D.Fq = D.q := by
  have hdim : Module.finrank (ZMod D.p) D.Fq = D.r := by
    rw [(AdjoinRoot.powerBasis' D.f_monic).finrank, AdjoinRoot.powerBasis'_dim, D.f_deg]
  rw [Module.card_eq_pow_finrank (K := ZMod D.p) (V := D.Fq), ZMod.card, hdim, FieldData.q]

lemma card_Fq2 (D : FieldData) : Fintype.card D.Fq2 = D.q ^ 2 := by
  have hdim : Module.finrank D.Fq D.Fq2 = 2 := by
    rw [(AdjoinRoot.powerBasis' D.F_monic).finrank, AdjoinRoot.powerBasis'_dim, D.F_deg]
  rw [Module.card_eq_pow_finrank (K := D.Fq) (V := D.Fq2), D.card_Fq, hdim]

lemma h_order_eq (D : FieldData) : orderOf D.h = D.q ^ 2 - 1 := by
  rw [D.h_order, FieldData.q]

lemma h_ne_zero (D : FieldData) : D.h ≠ 0 := by
  intro h0
  have hord := D.h_order_eq
  rw [h0, orderOf_zero] at hord
  have hq : 1 < D.q := D.one_lt_q
  have hsq : 1 < D.q ^ 2 := by nlinarith
  omega

lemma gen_algebraMap (D : FieldData) :
    algebraMap D.Fq D.Fq2 D.gen = D.h ^ (D.q + 1) := by
  unfold FieldData.gen
  have hnorm := FiniteField.algebraMap_norm_eq_pow (K := D.Fq) (K' := D.Fq2) (x := D.h)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, D.card_Fq2, D.card_Fq] at hnorm
  have hq : 1 < D.q := D.one_lt_q
  have hsq : 1 ≤ D.q ^ 2 := by nlinarith
  have hdiv : (D.q ^ 2 - 1) / (D.q - 1) = D.q + 1 := by
    have hmul : D.q ^ 2 - 1 = (D.q + 1) * (D.q - 1) := by
      zify [hq.le, hsq]
      ring
    rw [hmul, Nat.mul_div_cancel _ (by omega)]
  rwa [hdiv] at hnorm

lemma gen_ne_zero (D : FieldData) : D.gen ≠ 0 := by
  intro h0
  have hu : ((Units.mk0 D.h D.h_ne_zero ^ (D.q + 1) : D.Fq2ˣ) : D.Fq2) = 0 := by
    simp [← D.gen_algebraMap, h0]
  exact Units.ne_zero _ hu

lemma gen_order (D : FieldData) : orderOf D.gen = D.q - 1 := by
  have hinj : Function.Injective (algebraMap D.Fq D.Fq2) := RingHom.injective _
  have hord_map : orderOf ((algebraMap D.Fq D.Fq2).toMonoidHom D.gen) = orderOf D.gen :=
    orderOf_injective (algebraMap D.Fq D.Fq2).toMonoidHom hinj D.gen
  change orderOf (algebraMap D.Fq D.Fq2 D.gen) = orderOf D.gen at hord_map
  let hu : D.Fq2ˣ := Units.mk0 D.h D.h_ne_zero
  have hu_pow : ((hu ^ (D.q + 1) : D.Fq2ˣ) : D.Fq2) = D.h ^ (D.q + 1) := by simp [hu]
  have hu_ord : orderOf hu = D.q ^ 2 - 1 := by
    rw [← orderOf_units, Units.val_mk0, D.h_order_eq]
  rw [← hord_map, D.gen_algebraMap, ← hu_pow, orderOf_units, orderOf_pow, hu_ord]
  have hq : 1 < D.q := D.one_lt_q
  have hsq : 1 ≤ D.q ^ 2 := by nlinarith
  have hmul : D.q ^ 2 - 1 = (D.q - 1) * (D.q + 1) := by
    zify [hq.le, hsq]
    ring
  rw [hmul, Nat.gcd_eq_right (dvd_mul_left (D.q + 1) (D.q - 1))]
  exact Nat.mul_div_cancel _ (by omega)

end FieldData

end GL2QFT

section AbstractCharacters

open GL2QFT

private noncomputable def genDlog {K : Type} [Field K] (g x : K) : ℕ :=
  if hx : ∃ n : ℕ, g ^ n = x then Nat.find hx else 0

private noncomputable def genChar {K : Type} [Field K] (g : K) (N : ℕ)
    (α : ZMod N) (x : K) : ℂ :=
  if x = 0 then 0
  else Complex.exp (2 * Real.pi * Complex.I * ((α.val * genDlog g x : ℕ) : ℂ) / (N : ℂ))

private lemma exp_two_pi_I_mod {N : ℕ} (hN : 0 < N) {a b : ℕ} (hab : a ≡ b [MOD N]) :
    Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (N : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (b : ℂ) / (N : ℂ)) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hrem : a % N = b % N := hab
  have haN : N * (a / N) + a % N = a := Nat.div_add_mod a N
  have hbN : N * (b / N) + b % N = b := Nat.div_add_mod b N
  let k : ℤ := (a / N : ℤ) - (b / N : ℤ)
  have hZ : (a : ℤ) = (b : ℤ) + k * (N : ℤ) := by
    have haZ : (N : ℤ) * (a / N : ℤ) + (a % N : ℤ) = (a : ℤ) := by exact_mod_cast haN
    have hbZ : (N : ℤ) * (b / N : ℤ) + (b % N : ℤ) = (b : ℤ) := by exact_mod_cast hbN
    have hrZ : (a % N : ℤ) = (b % N : ℤ) := by exact_mod_cast hrem
    dsimp [k]
    linarith
  have ha : (a : ℂ) = (b : ℂ) + (k : ℂ) * (N : ℂ) := by exact_mod_cast hZ
  have hexp : 2 * Real.pi * Complex.I * (a : ℂ) / (N : ℂ) =
      2 * Real.pi * Complex.I * (b : ℂ) / (N : ℂ) + (k : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [ha]
    field_simp [hN0]
  rw [hexp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private lemma generator_surj {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {g : K} {N : ℕ} (hN : 0 < N) (hord : orderOf g = N) (hcard : Fintype.card K - 1 = N) :
    ∀ x : K, x ≠ 0 → ∃ n : ℕ, g ^ n = x := by
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, orderOf_zero] at hord
    omega
  let u : Kˣ := Units.mk0 g hg0
  have hu_ord : orderOf u = N := by
    rw [← orderOf_units, Units.val_mk0, hord]
  have htop : Subgroup.zpowers u = ⊤ := by
    apply Subgroup.eq_top_of_le_card
    rw [Nat.card_zpowers, hu_ord, Nat.card_eq_fintype_card, Fintype.card_units, hcard]
  intro x hx
  have hmem : Units.mk0 x hx ∈ Subgroup.zpowers u := htop ▸ Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hNpos_int : (0 : ℤ) < (N : ℤ) := Int.natCast_pos.mpr hN
  let r : ℕ := (k % (N : ℤ)).toNat
  have hr_nonneg : 0 ≤ k % (N : ℤ) := Int.emod_nonneg k hNpos_int.ne'
  have hr_cast : (r : ℤ) = k % (N : ℤ) := Int.toNat_of_nonneg hr_nonneg
  have huN : u ^ (N : ℤ) = 1 := by
    rw [zpow_natCast, ← hu_ord, pow_orderOf_eq_one]
  have hk_eq : u ^ k = u ^ r := by
    have hdiv : (N : ℤ) * (k / (N : ℤ)) + k % (N : ℤ) = k := Int.mul_ediv_add_emod k N
    calc
      u ^ k = u ^ ((N : ℤ) * (k / (N : ℤ)) + k % (N : ℤ)) := by rw [hdiv]
      _ = (u ^ (N : ℤ)) ^ (k / (N : ℤ)) * u ^ (k % (N : ℤ)) := by rw [zpow_add, zpow_mul]
      _ = u ^ (r : ℤ) := by rw [huN, one_zpow, one_mul, hr_cast]
      _ = u ^ r := zpow_natCast u r
  refine ⟨r, ?_⟩
  have := congrArg (fun v : Kˣ => (v : K)) (hk_eq.symm.trans hk)
  simpa [u] using this

private lemma genDlog_spec {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {g : K} {N : ℕ} (hN : 0 < N) (hord : orderOf g = N) (hcard : Fintype.card K - 1 = N)
    {x : K} (hx : x ≠ 0) :
    g ^ genDlog g x = x := by
  have hex := generator_surj hN hord hcard x hx
  simp only [genDlog, dif_pos hex]
  convert Nat.find_spec hex

private lemma genChar_eq_of_pow {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {g : K} {N : ℕ} (hN : 0 < N) (hord : orderOf g = N) (hcard : Fintype.card K - 1 = N)
    (α : ZMod N) {x : K} (hx : x ≠ 0) {n : ℕ} (hn : g ^ n = x) :
    genChar g N α x =
      Complex.exp (2 * Real.pi * Complex.I * ((α.val * n : ℕ) : ℂ) / (N : ℂ)) := by
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, orderOf_zero] at hord
    omega
  let u : Kˣ := Units.mk0 g hg0
  have hu_ord : orderOf u = N := by
    rw [← orderOf_units, Units.val_mk0, hord]
  have hdlog := genDlog_spec hN hord hcard hx
  have hupow : u ^ n = u ^ genDlog g x := by
    ext
    simp [u, hn, hdlog]
  have hmod : n ≡ genDlog g x [MOD N] := by
    rw [← hu_ord]
    exact pow_eq_pow_iff_modEq.mp hupow
  have hmod' : α.val * genDlog g x ≡ α.val * n [MOD N] := (hmod.symm).mul_left α.val
  simp only [genChar, if_neg hx]
  exact exp_two_pi_I_mod hN hmod'

private lemma genChar_zero {K : Type} [Field K] (g : K) (N : ℕ) (α : ZMod N) :
    genChar g N α 0 = 0 := by
  simp [genChar]

private lemma genChar_one {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {g : K} {N : ℕ} (hN : 0 < N) (hord : orderOf g = N) (hcard : Fintype.card K - 1 = N)
    (α : ZMod N) :
    genChar g N α 1 = 1 := by
  rw [genChar_eq_of_pow hN hord hcard α one_ne_zero (pow_zero g)]
  simp

private lemma genChar_mul {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {g : K} {N : ℕ} (hN : 0 < N) (hord : orderOf g = N) (hcard : Fintype.card K - 1 = N)
    (α : ZMod N) (x y : K) :
    genChar g N α (x * y) = genChar g N α x * genChar g N α y := by
  by_cases hx : x = 0
  · subst hx; simp [genChar_zero]
  by_cases hy : y = 0
  · subst hy; simp [genChar_zero]
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  have hpow : g ^ (genDlog g x + genDlog g y) = x * y := by
    rw [pow_add, genDlog_spec hN hord hcard hx, genDlog_spec hN hord hcard hy]
  rw [genChar_eq_of_pow hN hord hcard α hxy hpow]
  simp only [genChar, if_neg hx, if_neg hy, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma genChar_zero_label {K : Type} [Field K] (g : K) (N : ℕ) [NeZero N]
    {x : K} (hx : x ≠ 0) :
    genChar g N 0 x = 1 := by
  simp [genChar, hx]

private lemma genChar_add {K : Type} [Field K] (g : K) {N : ℕ} (hN : 0 < N) [NeZero N]
    (α β : ZMod N) (x : K) :
    genChar g N (α + β) x = genChar g N α x * genChar g N β x := by
  by_cases hx : x = 0
  · subst hx; simp [genChar_zero]
  have hmod : (α + β).val * genDlog g x ≡ α.val * genDlog g x + β.val * genDlog g x [MOD N] := by
    have h1 : (α + β).val ≡ α.val + β.val [MOD N] := by
      rw [ZMod.val_add]
      exact Nat.mod_modEq _ _
    simpa [add_mul] using h1.mul_right (genDlog g x)
  simp only [genChar, if_neg hx]
  rw [exp_two_pi_I_mod hN hmod, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma genChar_conj {K : Type} [Field K] (g : K) (N : ℕ) (α : ZMod N) (x : K) :
    conj (genChar g N α x) = (genChar g N α x)⁻¹ ∨ x = 0 := by
  by_cases hx : x = 0
  · exact Or.inr hx
  left
  simp only [genChar, if_neg hx, ← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  have hmul : 2 * Real.pi * Complex.I * ((α.val * genDlog g x : ℕ) : ℂ) / (N : ℂ) =
      (((2 * Real.pi * ((α.val * genDlog g x : ℕ) : ℝ) / (N : ℝ) : ℝ) : ℂ)) * Complex.I := by
    push_cast
    ring
  rw [hmul, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

private lemma genChar_neg {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {g : K} {N : ℕ} (hN : 0 < N) [NeZero N]
    (α : ZMod N) (x : K) :
    genChar g N (-α) x = conj (genChar g N α x) := by
  by_cases hx : x = 0
  · subst hx; simp [genChar_zero]
  have hprod : genChar g N (-α) x * genChar g N α x = 1 := by
    rw [← genChar_add g hN, neg_add_cancel, genChar_zero_label g N hx]
  have hconj := (genChar_conj g N α x).resolve_right hx
  rw [hconj]
  exact eq_inv_of_mul_eq_one_left hprod

private lemma genChar_inv {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {g : K} {N : ℕ} (hN : 0 < N) [NeZero N] (hord : orderOf g = N) (hcard : Fintype.card K - 1 = N)
    (α : ZMod N) (x : K) :
    genChar g N α x⁻¹ = conj (genChar g N α x) := by
  by_cases hx : x = 0
  · subst hx; simp [genChar_zero]
  have hprod : genChar g N α x⁻¹ * genChar g N α x = 1 := by
    rw [← genChar_mul hN hord hcard, inv_mul_cancel₀ hx, genChar_one hN hord hcard]
  have hconj := (genChar_conj g N α x).resolve_right hx
  rw [hconj]
  exact eq_inv_of_mul_eq_one_left hprod

private lemma genChar_generator_ne_one {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {g : K} {N : ℕ} (hN : 0 < N) [NeZero N] (hord : orderOf g = N) (hcard : Fintype.card K - 1 = N)
    {α : ZMod N} (hα : α ≠ 0) :
    genChar g N α g ≠ 1 := by
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, orderOf_zero] at hord
    omega
  rw [genChar_eq_of_pow hN hord hcard α hg0 (pow_one g)]
  intro heq
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp heq
  have h2piI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hC : (((α.val : ℝ) / (N : ℝ) : ℝ) : ℂ) = ((k : ℝ) : ℂ) := by
    push_cast
    have hk' : (2 * Real.pi * Complex.I) * (((α.val : ℕ) : ℂ) / (N : ℂ)) =
        (2 * Real.pi * Complex.I) * (k : ℂ) := by
      calc
        (2 * Real.pi * Complex.I) * (((α.val : ℕ) : ℂ) / (N : ℂ))
            = 2 * Real.pi * Complex.I * ((α.val * 1 : ℕ) : ℂ) / (N : ℂ) := by
                simp; ring
        _ = (k : ℂ) * (2 * Real.pi * Complex.I) := hk
        _ = (2 * Real.pi * Complex.I) * (k : ℂ) := by ring
    exact mul_left_cancel₀ h2piI hk'
  have hR : (α.val : ℝ) / (N : ℝ) = (k : ℝ) := Complex.ofReal_inj.mp hC
  have hval_lt : α.val < N := ZMod.val_lt α
  have hNposR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hdiv_nonneg : 0 ≤ (α.val : ℝ) / (N : ℝ) := by positivity
  have hdiv_lt : (α.val : ℝ) / (N : ℝ) < 1 := (div_lt_one hNposR).mpr (Nat.cast_lt.mpr hval_lt)
  have hk_ge : (0 : ℤ) ≤ k := by exact_mod_cast (hR ▸ hdiv_nonneg)
  have hk_lt : k < 1 := by exact_mod_cast (hR ▸ hdiv_lt)
  have hk0 : k = 0 := by omega
  rw [hk0, Int.cast_zero, div_eq_zero_iff] at hR
  have hval0 : α.val = 0 := by
    rcases hR with h | h
    · exact Nat.cast_eq_zero.mp h
    · linarith
  exact hα ((ZMod.val_eq_zero α).mp hval0)

private lemma sum_genChar {K : Type} [Field K] [Fintype K] [DecidableEq K]
    {g : K} {N : ℕ} (hN : 0 < N) [NeZero N] (hord : orderOf g = N) (hcard : Fintype.card K - 1 = N)
    (α : ZMod N) :
    ∑ x ∈ Finset.univ.filter (fun x : K => x ≠ 0), genChar g N α x =
      if α = 0 then (N : ℂ) else 0 := by
  let S : Finset K := Finset.univ.filter (fun x : K => x ≠ 0)
  by_cases hα : α = 0
  · subst hα
    rw [if_pos rfl]
    have hsum : ∑ x ∈ S, genChar g N 0 x = ∑ _x ∈ S, (1 : ℂ) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      exact genChar_zero_label g N (Finset.mem_filter.mp hx).2
    rw [hsum, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hS : S = Finset.univ.erase (0 : K) := by
      ext x; simp [S, and_comm]
    rw [hS, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, hcard]
  · rw [if_neg hα]
    have hg0 : g ≠ 0 := by
      intro h0
      rw [h0, orderOf_zero] at hord
      omega
    have hbij : ∑ x ∈ S, genChar g N α x = ∑ x ∈ S, genChar g N α (g * x) := by
      refine (Finset.sum_bij (fun x _ => g * x) ?_ ?_ ?_ ?_).symm
      · intro x hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mul_ne_zero hg0 (Finset.mem_filter.mp hx).2⟩
      · intro x _ y _ hxy
        exact mul_left_cancel₀ hg0 hxy
      · intro y hy
        refine ⟨g⁻¹ * y, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          mul_ne_zero (inv_ne_zero hg0) (Finset.mem_filter.mp hy).2⟩, ?_⟩
        simp [hg0]
      · intro x _; rfl
    have hmul : ∑ x ∈ S, genChar g N α (g * x) =
        genChar g N α g * ∑ x ∈ S, genChar g N α x := by
      simp_rw [genChar_mul hN hord hcard, ← Finset.mul_sum]
    have hsub : (1 - genChar g N α g) * ∑ x ∈ S, genChar g N α x = 0 := by
      linear_combination hbij.trans hmul
    have hne : 1 - genChar g N α g ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (genChar_generator_ne_one hN hord hcard hα))
    exact (mul_eq_zero.mp hsub).resolve_left hne

end AbstractCharacters

namespace GL2QFT

namespace FieldData

lemma chi_zero (D : FieldData) (α : D.Lab) : D.chi α 0 = 0 :=
  genChar_zero D.gen (D.q - 1) α

lemma chi_one (D : FieldData) (α : D.Lab) : D.chi α 1 = 1 :=
  genChar_one (Nat.sub_pos_of_lt D.one_lt_q) D.gen_order
    (by rw [D.card_Fq]) α

lemma chi_mul (D : FieldData) (α : D.Lab) (x y : D.Fq) :
    D.chi α (x * y) = D.chi α x * D.chi α y :=
  genChar_mul (Nat.sub_pos_of_lt D.one_lt_q) D.gen_order
    (by rw [D.card_Fq]) α x y

lemma chi_zero_label (D : FieldData) {x : D.Fq} (hx : x ≠ 0) : D.chi 0 x = 1 :=
  genChar_zero_label D.gen (D.q - 1) hx

lemma chi_add (D : FieldData) (α β : D.Lab) (x : D.Fq) :
    D.chi (α + β) x = D.chi α x * D.chi β x :=
  genChar_add D.gen (Nat.sub_pos_of_lt D.one_lt_q) α β x

lemma chi_neg (D : FieldData) (α : D.Lab) (x : D.Fq) :
    D.chi (-α) x = conj (D.chi α x) :=
  genChar_neg (Nat.sub_pos_of_lt D.one_lt_q) α x

lemma chi_inv (D : FieldData) (α : D.Lab) (x : D.Fq) :
    D.chi α x⁻¹ = conj (D.chi α x) :=
  genChar_inv (Nat.sub_pos_of_lt D.one_lt_q) D.gen_order
    (by rw [D.card_Fq]) α x

lemma chi_neg_eq_chi_inv (D : FieldData) (α : D.Lab) (x : D.Fq) :
    D.chi (-α) x = D.chi α x⁻¹ := by
  rw [D.chi_neg, D.chi_inv]

lemma sum_chi (D : FieldData) (α : D.Lab) :
    ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0), D.chi α x =
      if α = 0 then ((D.q - 1 : ℕ) : ℂ) else 0 :=
  sum_genChar (Nat.sub_pos_of_lt D.one_lt_q) D.gen_order
    (by rw [D.card_Fq]) α

private lemma q_sq_sub_one_pos (D : FieldData) : 0 < D.q ^ 2 - 1 := by
  have hq : 1 < D.q := D.one_lt_q
  have hsq : 1 < D.q ^ 2 := by nlinarith
  omega

lemma theta_zero (D : FieldData) (k : D.Lab2) : D.theta k 0 = 0 :=
  genChar_zero D.h (D.q ^ 2 - 1) k

lemma theta_one (D : FieldData) (k : D.Lab2) : D.theta k 1 = 1 :=
  genChar_one D.q_sq_sub_one_pos D.h_order_eq (by rw [D.card_Fq2]) k

lemma theta_mul (D : FieldData) (k : D.Lab2) (z w : D.Fq2) :
    D.theta k (z * w) = D.theta k z * D.theta k w :=
  genChar_mul D.q_sq_sub_one_pos D.h_order_eq (by rw [D.card_Fq2]) k z w

lemma theta_inv (D : FieldData) (k : D.Lab2) (z : D.Fq2) :
    D.theta k z⁻¹ = conj (D.theta k z) :=
  genChar_inv D.q_sq_sub_one_pos D.h_order_eq (by rw [D.card_Fq2]) k z

lemma sum_theta (D : FieldData) (k : D.Lab2) :
    ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => z ≠ 0), D.theta k z =
      if k = 0 then ((D.q ^ 2 - 1 : ℕ) : ℂ) else 0 :=
  sum_genChar D.q_sq_sub_one_pos D.h_order_eq (by rw [D.card_Fq2]) k

/-! ### Additive character `psi` and `psi ∘ tr` -/

lemma psi_zero (D : FieldData) : D.psi 0 = 1 := by
  simp [FieldData.psi]

lemma psi_add (D : FieldData) (x y : D.Fq) : D.psi (x + y) = D.psi x * D.psi y := by
  have htr : Algebra.trace (ZMod D.p) D.Fq (x + y) =
      Algebra.trace (ZMod D.p) D.Fq x + Algebra.trace (ZMod D.p) D.Fq y := map_add _ x y
  have hmod : (Algebra.trace (ZMod D.p) D.Fq (x + y)).val ≡
      (Algebra.trace (ZMod D.p) D.Fq x).val + (Algebra.trace (ZMod D.p) D.Fq y).val [MOD D.p] := by
    rw [htr, ZMod.val_add]
    exact Nat.mod_modEq _ _
  simp only [FieldData.psi]
  rw [exp_two_pi_I_mod D.hp.pos hmod, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma psi_neg (D : FieldData) (x : D.Fq) : D.psi (-x) = conj (D.psi x) := by
  have hprod : D.psi (-x) * D.psi x = 1 := by
    rw [← D.psi_add, neg_add_cancel, D.psi_zero]
  have hconj : conj (D.psi x) = (D.psi x)⁻¹ := by
    simp only [FieldData.psi, ← Complex.exp_conj, ← Complex.exp_neg]
    congr 1
    have hmul : 2 * Real.pi * Complex.I *
        (((Algebra.trace (ZMod D.p) D.Fq x).val : ℕ) : ℂ) / (D.p : ℂ) =
        (((2 * Real.pi * (((Algebra.trace (ZMod D.p) D.Fq x).val : ℕ) : ℝ) / (D.p : ℝ) : ℝ) : ℂ)) *
          Complex.I := by
      push_cast; ring
    rw [hmul, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hconj]
  exact eq_inv_of_mul_eq_one_left hprod

lemma psi_nontrivial (D : FieldData) : ∃ x₀ : D.Fq, D.psi x₀ ≠ 1 := by
  obtain ⟨x₀, hx₀⟩ := Algebra.trace_surjective (ZMod D.p) D.Fq 1
  refine ⟨x₀, ?_⟩
  simp only [FieldData.psi, hx₀]
  have h1 : (1 : ZMod D.p).val = 1 := by
    have : Fact (1 < D.p) := ⟨D.hp.one_lt⟩
    exact ZMod.val_one D.p
  rw [h1]
  intro heq
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp heq
  have h2piI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have hp0 : (D.p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.hp.ne_zero
  have hC : (1 : ℂ) / (D.p : ℂ) = (k : ℂ) := by
    have hk' : (2 * Real.pi * Complex.I) * ((1 : ℂ) / (D.p : ℂ)) =
        (2 * Real.pi * Complex.I) * (k : ℂ) := by
      calc
        (2 * Real.pi * Complex.I) * ((1 : ℂ) / (D.p : ℂ))
            = 2 * Real.pi * Complex.I * ((1 : ℕ) : ℂ) / (D.p : ℂ) := by simp; ring
        _ = (k : ℂ) * (2 * Real.pi * Complex.I) := hk
        _ = (2 * Real.pi * Complex.I) * (k : ℂ) := by ring
    exact mul_left_cancel₀ h2piI hk'
  have hC' : (((1 / (D.p : ℝ) : ℝ) : ℂ)) = ((k : ℝ) : ℂ) := by
    simpa using hC
  have hR : (1 : ℝ) / (D.p : ℝ) = (k : ℝ) := Complex.ofReal_inj.mp hC'
  have hp1 : (1 : ℝ) < (D.p : ℝ) := by exact_mod_cast D.hp.one_lt
  have hpos : (0 : ℝ) < 1 / (D.p : ℝ) := by positivity
  have hlt : 1 / (D.p : ℝ) < 1 := (div_lt_one (by positivity)).mpr hp1
  have hk_pos : (0 : ℤ) < k := by exact_mod_cast (hR ▸ hpos)
  have hk_lt : k < 1 := by exact_mod_cast (hR ▸ hlt)
  omega

private lemma sum_addChar {K : Type} [Field K] [Fintype K]
    (φ : K → ℂ) (hφ0 : φ 0 = 1) (hφ_add : ∀ x y : K, φ (x + y) = φ x * φ y)
    (hφ_nt : ∃ y₀ : K, φ y₀ ≠ 1) (b : K) :
    ∑ x : K, φ (b * x) = if b = 0 then (Fintype.card K : ℂ) else 0 := by
  by_cases hb : b = 0
  · subst hb
    simp [hφ0]
  · rw [if_neg hb]
    obtain ⟨y₀, hy₀⟩ := hφ_nt
    let y : K := b⁻¹ * y₀
    have hby : φ (b * y) ≠ 1 := by
      have : b * y = y₀ := by simp [y, hb]
      rwa [this]
    have hshift : ∑ x : K, φ (b * x) = ∑ x : K, φ (b * (x + y)) := by
      refine (Fintype.sum_equiv (Equiv.addRight y) _ _ fun x => ?_).symm
      simp
    have hmul : ∑ x : K, φ (b * (x + y)) = φ (b * y) * ∑ x : K, φ (b * x) := by
      simp_rw [mul_add, hφ_add, mul_comm (φ (b * _)) (φ (b * y)), ← Finset.mul_sum]
    have hsub : (1 - φ (b * y)) * ∑ x : K, φ (b * x) = 0 := by
      linear_combination hshift.trans hmul
    exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr (Ne.symm hby))

lemma sum_psi (D : FieldData) (b : D.Fq) :
    ∑ x : D.Fq, D.psi (b * x) = if b = 0 then (D.q : ℂ) else 0 := by
  rw [sum_addChar D.psi D.psi_zero D.psi_add D.psi_nontrivial b, D.card_Fq]

private lemma exists_add_pow_ne_zero {K : Type} [Field K] [Fintype K] {q : ℕ}
    (hq1 : 1 < q) (hcard : Fintype.card K = q ^ 2) :
    ∃ z : K, z + z ^ q ≠ 0 := by
  let P : Polynomial K := Polynomial.X ^ q + Polynomial.X
  have hdeg_X : (Polynomial.X : Polynomial K).natDegree <
      (Polynomial.X ^ q : Polynomial K).natDegree := by
    simpa using hq1
  have hP_deg : P.natDegree = q := by
    dsimp [P]
    rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt hdeg_X, Polynomial.natDegree_X_pow]
  have hP_ne : P ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hP_deg
    omega
  have hcard_lt : P.roots.card < Fintype.card K := by
    have h1 : P.roots.card ≤ P.natDegree := Polynomial.card_roots' P
    have h2 : q < q ^ 2 := by nlinarith
    rw [hP_deg] at h1
    rw [hcard]
    omega
  by_contra hall
  have hmem : ∀ z : K, z ∈ P.roots := fun z => by
    rw [Polynomial.mem_roots hP_ne, Polynomial.IsRoot]
    have hz : z + z ^ q = 0 := not_ne_iff.mp (fun h => hall ⟨z, h⟩)
    dsimp [P]
    simpa [add_comm] using hz
  have hsub : Finset.univ ⊆ P.roots.toFinset := fun z _ =>
    Multiset.mem_toFinset.mpr (hmem z)
  have hle := Finset.card_le_card hsub
  rw [Finset.card_univ] at hle
  have hle2 := Multiset.toFinset_card_le P.roots
  omega

lemma sum_psi_tr (D : FieldData) (w : D.Fq2) :
    ∑ z : D.Fq2, D.psi (D.tr (w * z)) = if w = 0 then ((D.q ^ 2 : ℕ) : ℂ) else 0 := by
  have htr0 : D.psi (D.tr 0) = 1 := by simp [FieldData.tr, D.psi_zero]
  have htr_add : ∀ z₁ z₂ : D.Fq2, D.psi (D.tr (z₁ + z₂)) =
      D.psi (D.tr z₁) * D.psi (D.tr z₂) := by
    intro z₁ z₂
    simp [FieldData.tr, map_add, D.psi_add]
  have htr_nt : ∃ z₀ : D.Fq2, D.psi (D.tr z₀) ≠ 1 := by
    obtain ⟨x₀, hx₀⟩ := D.psi_nontrivial
    have htr_ne : ∃ z₁ : D.Fq2, D.tr z₁ ≠ 0 := by
      obtain ⟨z₁, hz₁⟩ := exists_add_pow_ne_zero D.one_lt_q D.card_Fq2
      refine ⟨z₁, fun htr0 => hz₁ ?_⟩
      have htr_sum := FiniteField.algebraMap_trace_eq_sum_pow D.Fq D.Fq2 z₁
      have hdim : Module.finrank D.Fq D.Fq2 = 2 := by
        rw [(AdjoinRoot.powerBasis' D.F_monic).finrank, AdjoinRoot.powerBasis'_dim, D.F_deg]
      rw [hdim, Nat.card_eq_fintype_card, D.card_Fq, Finset.sum_range_succ, Finset.sum_range_one,
        pow_zero, pow_one, pow_one] at htr_sum
      change algebraMap D.Fq D.Fq2 (D.tr z₁) = z₁ + z₁ ^ D.q at htr_sum
      rw [htr0, map_zero] at htr_sum
      exact htr_sum.symm
    obtain ⟨z₁, hz₁⟩ := htr_ne
    let z₀ : D.Fq2 := (x₀ * (D.tr z₁)⁻¹) • z₁
    refine ⟨z₀, ?_⟩
    have htr_z₀ : D.tr z₀ = x₀ := by
      change Algebra.trace D.Fq D.Fq2 ((x₀ * (D.tr z₁)⁻¹) • z₁) = x₀
      rw [map_smul, smul_eq_mul, mul_assoc]
      change x₀ * ((D.tr z₁)⁻¹ * D.tr z₁) = x₀
      rw [inv_mul_cancel₀ hz₁, mul_one]
    rwa [htr_z₀]
  rw [sum_addChar (fun z => D.psi (D.tr z)) htr0 htr_add htr_nt w, D.card_Fq2]

end FieldData

end GL2QFT

section GaussNorm

private lemma norm_gauss_abstract {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (μ φ : K → ℂ)
    (hμ1 : μ 1 = 1) (hμ_mul : ∀ x y : K, μ (x * y) = μ x * μ y)
    (hμ_inv : ∀ x : K, conj (μ x) = μ x⁻¹)
    (hμ_sum : ∑ x ∈ Finset.univ.filter (fun x : K => x ≠ 0), μ x = 0)
    (hφ0 : φ 0 = 1) (hφ_add : ∀ x y : K, φ (x + y) = φ x * φ y)
    (hφ_neg : ∀ x : K, conj (φ x) = φ (-x))
    (hφ_sum : ∀ b : K, ∑ x : K, φ (b * x) = if b = 0 then (Fintype.card K : ℂ) else 0) :
    ‖∑ x ∈ Finset.univ.filter (fun x : K => x ≠ 0), μ x * φ x‖ =
      Real.sqrt (Fintype.card K) := by
  let S : Finset K := Finset.univ.filter (fun x : K => x ≠ 0)
  let G : ℂ := ∑ x ∈ S, μ x * φ x
  have hG : G * conj G = (Fintype.card K : ℂ) := by
    calc
      G * conj G
          = (∑ x ∈ S, μ x * φ x) * (∑ y ∈ S, conj (μ y) * conj (φ y)) := by
              simp [G, map_sum, map_mul]
      _ = ∑ y ∈ S, ∑ x ∈ S, (μ x * μ y⁻¹) * (φ x * φ (-y)) := by
              rw [Finset.sum_mul]
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
              rw [hμ_inv y, hφ_neg y]
              ring
      _ = ∑ y ∈ S, ∑ x ∈ S, μ (x * y⁻¹) * φ (x - y) := by
              refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
              rw [← hμ_mul, ← hφ_add, sub_eq_add_neg]
      _ = ∑ y ∈ S, ∑ u ∈ S, μ u * φ (y * (u - 1)) := by
              refine Finset.sum_congr rfl fun y hy => ?_
              have hy0 : y ≠ 0 := (Finset.mem_filter.mp hy).2
              refine (Finset.sum_bij (fun u _ => u * y) ?_ ?_ ?_ ?_).symm
              · intro u hu
                exact Finset.mem_filter.mpr
                  ⟨Finset.mem_univ _, mul_ne_zero (Finset.mem_filter.mp hu).2 hy0⟩
              · intro u₁ _ u₂ _ hu
                exact mul_right_cancel₀ hy0 hu
              · intro x hx
                refine ⟨x * y⁻¹, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
                  mul_ne_zero (Finset.mem_filter.mp hx).2 (inv_ne_zero hy0)⟩, ?_⟩
                simp [hy0]
              · intro u _
                have h1 : (u * y) * y⁻¹ = u := by simp [hy0]
                have h2 : u * y - y = y * (u - 1) := by ring
                rw [h1, h2]
      _ = ∑ u ∈ S, μ u * ∑ y ∈ S, φ (y * (u - 1)) := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun u _ => ?_
              rw [Finset.mul_sum]
      _ = ∑ u ∈ S, μ u * ((if u = 1 then (Fintype.card K : ℂ) else 0) - 1) := by
              refine Finset.sum_congr rfl fun u _ => ?_
              congr 1
              have hS : S = Finset.univ.erase (0 : K) := by
                ext y; simp [S, and_comm]
              have htot : φ (0 * (u - 1)) + ∑ y ∈ S, φ (y * (u - 1)) =
                  ∑ y : K, φ ((u - 1) * y) := by
                rw [hS, Finset.add_sum_erase Finset.univ (fun y => φ (y * (u - 1))) (Finset.mem_univ 0)]
                refine Finset.sum_congr rfl fun y _ => ?_
                rw [mul_comm]
              have h0val : φ (0 * (u - 1)) = 1 := by rw [zero_mul, hφ0]
              rw [h0val, hφ_sum (u - 1)] at htot
              simp only [sub_eq_zero] at htot
              exact eq_sub_of_add_eq' htot
      _ = (∑ u ∈ S, (if u = 1 then μ u * (Fintype.card K : ℂ) else 0)) -
            ∑ u ∈ S, μ u := by
              simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib, mul_ite, mul_zero]
      _ = (Fintype.card K : ℂ) := by
              have h1mem : (1 : K) ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, one_ne_zero⟩
              rw [Finset.sum_ite_eq' S (1 : K) (fun u => μ u * (Fintype.card K : ℂ)),
                if_pos h1mem, hμ1, one_mul, hμ_sum, sub_zero]
  have hsqC : ((‖G‖ ^ 2 : ℝ) : ℂ) = ((Fintype.card K : ℝ) : ℂ) := by
    calc
      ((‖G‖ ^ 2 : ℝ) : ℂ) = (‖G‖ : ℂ) ^ 2 := by push_cast; rfl
      _ = G * conj G := (Complex.mul_conj' G).symm
      _ = (Fintype.card K : ℂ) := hG
      _ = ((Fintype.card K : ℝ) : ℂ) := by push_cast; rfl
  have hsqR : ‖G‖ ^ 2 = (Fintype.card K : ℝ) := Complex.ofReal_inj.mp hsqC
  rw [← Real.sqrt_sq (norm_nonneg G), hsqR]

end GaussNorm

open GL2QFT FieldData

theorem solution (D : FieldData) :
    (∀ (α : D.Lab) (b : D.Fq), b ≠ 0 → D.gaussG α b = D.chi (-α) b * D.gauss α) ∧
    (∀ α : D.Lab, conj (D.gauss α) = D.chi α (-1) * D.gauss (-α)) ∧
    (∀ α β : D.Lab, α + β ≠ 0 → D.gauss α * D.gauss β = D.jacobi α β * D.gauss (α + β)) ∧
    D.gauss 0 = -1 ∧
    (∀ α : D.Lab, α ≠ 0 → ‖D.gauss α‖ = Real.sqrt D.q) ∧
    (∀ k : D.Lab2, k ≠ 0 → ‖D.gaussQ2 (D.theta k)‖ = D.q) := by
  have h267 : ∀ (α : D.Lab) (b : D.Fq), b ≠ 0 → D.gaussG α b = D.chi (-α) b * D.gauss α := by
    intro α b hb
    let S : Finset D.Fq := Finset.univ.filter (fun x : D.Fq => x ≠ 0)
    calc
      D.gaussG α b
          = ∑ x ∈ S, D.chi α x * D.psi (b * x) := rfl
      _ = ∑ u ∈ S, D.chi α (b⁻¹ * u) * D.psi (1 * u) := by
            refine Finset.sum_bij (fun x _ => b * x) ?_ ?_ ?_ ?_
            · intro x hx
              exact Finset.mem_filter.mpr
                ⟨Finset.mem_univ _, mul_ne_zero hb (Finset.mem_filter.mp hx).2⟩
            · intro x _ y _ hxy
              exact mul_left_cancel₀ hb hxy
            · intro u hu
              refine ⟨b⁻¹ * u, Finset.mem_filter.mpr
                ⟨Finset.mem_univ _, mul_ne_zero (inv_ne_zero hb) (Finset.mem_filter.mp hu).2⟩, ?_⟩
              simp [hb]
            · intro x _
              rw [← mul_assoc, inv_mul_cancel₀ hb, one_mul, one_mul]
      _ = D.chi (-α) b * D.gauss α := by
            simp only [D.chi_mul, ← D.chi_neg_eq_chi_inv, mul_assoc]
            rw [← Finset.mul_sum]
            rfl
  refine ⟨h267, ?_, ?_, ?_, ?_, ?_⟩
  · -- (268): conj(g_q(α)) = χ_α(-1) g_q(-α)
    intro α
    have hconj : conj (D.gauss α) = D.gaussG (-α) (-1) := by
      simp only [FieldData.gauss, FieldData.gaussG, map_sum, map_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← D.chi_neg, one_mul, ← D.psi_neg, neg_one_mul]
    rw [hconj, h267 (-α) (-1) (neg_ne_zero.mpr one_ne_zero), neg_neg]
  · -- (269): g_q(α) g_q(β) = J(α, β) g_q(α + β) for α + β ≠ 0
    intro α β hαβ
    have hgauss_univ : ∀ γ : D.Lab, D.gauss γ = ∑ x : D.Fq, D.chi γ x * D.psi x := by
      intro γ
      simp only [FieldData.gauss, FieldData.gaussG, one_mul]
      have hS : Finset.univ.filter (fun x : D.Fq => x ≠ 0) = Finset.univ.erase (0 : D.Fq) := by
        ext x; simp [and_comm]
      rw [hS]
      have h0 : D.chi γ 0 * D.psi 0 = 0 := by rw [D.chi_zero, zero_mul]
      rw [← zero_add (∑ x ∈ Finset.univ.erase 0, D.chi γ x * D.psi x), ← h0]
      exact Finset.add_sum_erase Finset.univ (fun x => D.chi γ x * D.psi x) (Finset.mem_univ 0)
    have hjacobi_univ : D.jacobi α β = ∑ u : D.Fq, D.chi α u * D.chi β (1 - u) := by
      simp only [FieldData.jacobi]
      have hsub : Finset.univ.filter (fun x : D.Fq => x ≠ 0 ∧ x ≠ 1) ⊆ Finset.univ :=
        Finset.filter_subset _ _
      refine Finset.sum_subset hsub fun u _ hu => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not] at hu
      by_cases hu0 : u = 0
      · simp [hu0, D.chi_zero]
      · have hu1 : u = 1 := hu hu0
        simp [hu1, D.chi_zero]
    rw [hgauss_univ α, hgauss_univ β, hgauss_univ (α + β), hjacobi_univ]
    calc
      (∑ x : D.Fq, D.chi α x * D.psi x) * (∑ y : D.Fq, D.chi β y * D.psi y)
          = ∑ x : D.Fq, ∑ y : D.Fq, D.chi α x * D.chi β y * D.psi (x + y) := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun y _ => ?_
              rw [D.psi_add]
              ring
      _ = ∑ x : D.Fq, ∑ z : D.Fq, D.chi α x * D.chi β (z - x) * D.psi z := by
              refine Finset.sum_congr rfl fun x _ => ?_
              refine (Fintype.sum_equiv (Equiv.subRight x) _ _ fun z => ?_).symm
              simp [add_sub_cancel]
      _ = ∑ z : D.Fq, ∑ x : D.Fq, D.chi α x * D.chi β (z - x) * D.psi z := Finset.sum_comm
      _ = (∑ x : D.Fq, D.chi α x * D.chi β (0 - x) * D.psi 0) +
            ∑ z ∈ Finset.univ.erase (0 : D.Fq),
              ∑ x : D.Fq, D.chi α x * D.chi β (z - x) * D.psi z :=
              (Finset.add_sum_erase Finset.univ
                (fun z => ∑ x : D.Fq, D.chi α x * D.chi β (z - x) * D.psi z)
                (Finset.mem_univ 0)).symm
      _ = 0 + ∑ z ∈ Finset.univ.erase (0 : D.Fq),
            (D.chi (α + β) z * D.psi z) * ∑ u : D.Fq, D.chi α u * D.chi β (1 - u) := by
              congr 1
              · have h0sum : ∑ x : D.Fq, D.chi α x * D.chi β (0 - x) * D.psi 0 =
                    D.chi β (-1) * ∑ x : D.Fq, D.chi (α + β) x := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun x _ => ?_
                  rw [zero_sub, show (-x : D.Fq) = (-1) * x by ring, D.chi_mul, D.chi_add,
                    D.psi_zero, mul_one]
                  ring
                have hchi_univ : ∑ x : D.Fq, D.chi (α + β) x = 0 := by
                  rw [← Finset.add_sum_erase Finset.univ (fun x => D.chi (α + β) x)
                    (Finset.mem_univ 0), D.chi_zero, zero_add]
                  have hS : Finset.univ.erase (0 : D.Fq) =
                      Finset.univ.filter (fun x : D.Fq => x ≠ 0) := by
                    ext x; simp [and_comm]
                  rw [hS, D.sum_chi (α + β), if_neg hαβ]
                rw [h0sum, hchi_univ, mul_zero]
              · refine Finset.sum_congr rfl fun z hz => ?_
                have hz0 : z ≠ 0 := (Finset.mem_erase.mp hz).1
                rw [Finset.mul_sum]
                refine (Fintype.sum_equiv (Equiv.mulLeft₀ z hz0) _ _ fun u => ?_).symm
                simp only [Equiv.mulLeft₀_apply]
                have hsub : z - z * u = z * (1 - u) := by ring
                rw [hsub, D.chi_mul, D.chi_mul, D.chi_add]
                ring
      _ = (∑ z ∈ Finset.univ.erase (0 : D.Fq), D.chi (α + β) z * D.psi z) *
            ∑ u : D.Fq, D.chi α u * D.chi β (1 - u) := by
              rw [zero_add, ← Finset.sum_mul]
      _ = (∑ u : D.Fq, D.chi α u * D.chi β (1 - u)) *
            ∑ z : D.Fq, D.chi (α + β) z * D.psi z := by
              have h0 : D.chi (α + β) 0 * D.psi 0 = 0 := by rw [D.chi_zero, zero_mul]
              rw [mul_comm]
              congr 1
              rw [← zero_add (∑ z ∈ Finset.univ.erase 0, D.chi (α + β) z * D.psi z), ← h0]
              exact Finset.add_sum_erase Finset.univ
                (fun z => D.chi (α + β) z * D.psi z) (Finset.mem_univ 0)
  · -- (270a): g_q(0) = -1
    simp only [FieldData.gauss, FieldData.gaussG, one_mul]
    have h1 : ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0), D.chi 0 x * D.psi x =
        ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0), D.psi x := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [D.chi_zero_label (Finset.mem_filter.mp hx).2, one_mul]
    have hS : Finset.univ.filter (fun x : D.Fq => x ≠ 0) = Finset.univ.erase (0 : D.Fq) := by
      ext x; simp [and_comm]
    have htot := Finset.add_sum_erase Finset.univ D.psi (Finset.mem_univ (0 : D.Fq))
    rw [D.psi_zero, ← hS] at htot
    have hsum1 := D.sum_psi 1
    simp only [one_mul, one_ne_zero, ↓reduceIte] at hsum1
    rw [hsum1] at htot
    rw [h1]
    exact eq_neg_of_add_eq_zero_right htot
  · -- (270b): ‖g_q(α)‖ = √q for α ≠ 0
    intro α hα
    have hsum : ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0), D.chi α x = 0 := by
      rw [D.sum_chi, if_neg hα]
    have hpsi_sum : ∀ b : D.Fq, ∑ x : D.Fq, D.psi (b * x) =
        if b = 0 then (Fintype.card D.Fq : ℂ) else 0 := by
      intro b
      rw [D.sum_psi b, D.card_Fq]
    have hnorm := norm_gauss_abstract (D.chi α) D.psi (D.chi_one α) (D.chi_mul α)
      (fun x => (D.chi_inv α x).symm) hsum D.psi_zero D.psi_add (fun x => (D.psi_neg x).symm)
      hpsi_sum
    simpa [FieldData.gauss, FieldData.gaussG, D.card_Fq] using hnorm
  · -- ‖g_{q²}(θ_k)‖ = q for k ≠ 0
    intro k hk
    have hsum : ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => z ≠ 0), D.theta k z = 0 := by
      rw [D.sum_theta, if_neg hk]
    have htr0 : D.psi (D.tr 0) = 1 := by simp [FieldData.tr, D.psi_zero]
    have htr_add : ∀ z₁ z₂ : D.Fq2, D.psi (D.tr (z₁ + z₂)) =
        D.psi (D.tr z₁) * D.psi (D.tr z₂) := by
      intro z₁ z₂
      simp [FieldData.tr, map_add, D.psi_add]
    have htr_neg : ∀ z : D.Fq2, conj (D.psi (D.tr z)) = D.psi (D.tr (-z)) := by
      intro z
      simp [FieldData.tr, map_neg, ← D.psi_neg]
    have htr_sum : ∀ w : D.Fq2, ∑ z : D.Fq2, D.psi (D.tr (w * z)) =
        if w = 0 then (Fintype.card D.Fq2 : ℂ) else 0 := by
      intro w
      rw [D.sum_psi_tr w, D.card_Fq2]
    have hnorm := norm_gauss_abstract (D.theta k) (fun z => D.psi (D.tr z)) (D.theta_one k)
      (D.theta_mul k) (fun z => (D.theta_inv k z).symm) hsum htr0 htr_add htr_neg htr_sum
    rw [D.card_Fq2] at hnorm
    have hsqrt : Real.sqrt ((D.q ^ 2 : ℕ) : ℝ) = (D.q : ℝ) := by
      push_cast
      exact Real.sqrt_sq (Nat.cast_nonneg D.q)
    simpa [FieldData.gaussQ2, hsqrt] using hnorm
