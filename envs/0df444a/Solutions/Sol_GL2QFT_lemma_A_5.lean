-- Prove2me | solution 1 for GL2QFT.lemma_A_5
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T03:20:19.681819+00:00
-- url     : https://prove2.me/submissions/e9fbf405-e650-4f8b-8540-b130a98a7e01

import Definitions.Def_GL2QFT_Characters

noncomputable section

open Classical
open scoped ComplexConjugate
open GL2QFT FieldData

private lemma finrank_fq (D : FieldData) : Module.finrank (ZMod D.p) D.Fq = D.r := by
  rw [(AdjoinRoot.powerBasis' D.f_monic).finrank, AdjoinRoot.powerBasis'_dim, D.f_deg]

private lemma card_fq (D : FieldData) : Fintype.card D.Fq = D.q := by
  rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := ZMod D.p) (V := D.Fq),
    finrank_fq, Nat.card_zmod, FieldData.q]

private lemma finrank_fq2 (D : FieldData) : Module.finrank D.Fq D.Fq2 = 2 := by
  rw [(AdjoinRoot.powerBasis' D.F_monic).finrank, AdjoinRoot.powerBasis'_dim, D.F_deg]

private lemma card_fq2 (D : FieldData) : Fintype.card D.Fq2 = D.q ^ 2 := by
  rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := D.Fq) (V := D.Fq2),
    finrank_fq2, ← Fintype.card_eq_nat_card, card_fq]

private lemma h_ne_zero (D : FieldData) : D.h ≠ 0 := by
  intro h0
  have ho : orderOf D.h = 0 := by rw [h0, orderOf_zero]
  rw [D.h_order] at ho
  exact NeZero.ne (D.q ^ 2 - 1) ho

private lemma h_ne_one (D : FieldData) : D.h ≠ 1 := by
  intro h1
  have ho : orderOf D.h = 1 := by rw [h1, orderOf_one]
  rw [D.h_order] at ho
  change D.q ^ 2 - 1 = 1 at ho
  have hq2 : 4 ≤ D.q ^ 2 := by nlinarith [D.one_lt_q]
  omega

private lemma dlog2_h (D : FieldData) : D.dlog2 D.h = 1 := by
  have hex : ∃ n : ℕ, D.h ^ n = D.h := ⟨1, pow_one _⟩
  simp only [FieldData.dlog2, dif_pos hex]
  rw [Nat.find_eq_iff]
  refine ⟨pow_one _, ?_⟩
  intro m hm
  have hm0 : m = 0 := by omega
  subst hm0
  simpa using (h_ne_one D).symm

private lemma exists_pow_h (D : FieldData) : ∀ z : D.Fq2, z ≠ 0 → ∃ n : ℕ, D.h ^ n = z := by
  intro z hz
  let u : D.Fq2ˣ := Units.mk0 D.h (h_ne_zero D)
  have hu_ord : orderOf u = Nat.card D.Fq2ˣ := by
    rw [← orderOf_units, Units.val_mk0, D.h_order]
    change D.q ^ 2 - 1 = _
    rw [Nat.card_units D.Fq2, Nat.card_eq_fintype_card, card_fq2]
  have htop : Subgroup.zpowers u = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hu_ord]
  have hv : Units.mk0 z hz ∈ Subgroup.zpowers u := by
    rw [htop]
    trivial
  rw [← mem_powers_iff_mem_zpowers] at hv
  rcases hv with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  have := congrArg Units.val hn
  simpa [u] using this

private lemma h_pow_dlog2 (D : FieldData) {z : D.Fq2} (hz : z ≠ 0) :
    D.h ^ D.dlog2 z = z := by
  have hex := exists_pow_h D z hz
  simp only [FieldData.dlog2, dif_pos hex]
  exact Nat.find_spec hex

private lemma cexp_two_pi_I_mul_div_mod {a b M : ℕ} (hM : M ≠ 0) (h : a % M = b % M) :
    Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (M : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (b : ℂ) / (M : ℂ)) := by
  have hM0 : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have split : ∀ n : ℕ,
      2 * Real.pi * Complex.I * (n : ℂ) / (M : ℂ) =
        2 * Real.pi * Complex.I * ((n % M : ℕ) : ℂ) / (M : ℂ) +
          ((n / M : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    intro n
    have hn : (n : ℂ) = (M : ℂ) * ((n / M : ℕ) : ℂ) + ((n % M : ℕ) : ℂ) := by
      exact_mod_cast (Nat.div_add_mod n M).symm
    rw [hn]
    field_simp [hM0]
    ring
  rw [split a, split b, Complex.exp_add, Complex.exp_add,
    Complex.exp_nat_mul_two_pi_mul_I, Complex.exp_nat_mul_two_pi_mul_I, mul_one, mul_one, h]

private lemma theta_mul (D : FieldData) (k : D.Lab2) (z₁ z₂ : D.Fq2) :
    D.theta k (z₁ * z₂) = D.theta k z₁ * D.theta k z₂ := by
  by_cases hz₁ : z₁ = 0
  · subst hz₁; simp [FieldData.theta]
  by_cases hz₂ : z₂ = 0
  · subst hz₂; simp [FieldData.theta]
  have hz : z₁ * z₂ ≠ 0 := mul_ne_zero hz₁ hz₂
  simp only [FieldData.theta, if_neg hz, if_neg hz₁, if_neg hz₂]
  rw [← Complex.exp_add]
  let u : D.Fq2ˣ := Units.mk0 D.h (h_ne_zero D)
  have hpow : u ^ D.dlog2 (z₁ * z₂) = u ^ (D.dlog2 z₁ + D.dlog2 z₂) := by
    apply Units.ext
    push_cast
    change D.h ^ D.dlog2 (z₁ * z₂) = D.h ^ (D.dlog2 z₁ + D.dlog2 z₂)
    rw [pow_add, h_pow_dlog2 D hz₁, h_pow_dlog2 D hz₂, h_pow_dlog2 D hz]
  rw [pow_eq_pow_iff_modEq, ← orderOf_units] at hpow
  change D.dlog2 (z₁ * z₂) ≡ D.dlog2 z₁ + D.dlog2 z₂ [MOD orderOf D.h] at hpow
  rw [D.h_order] at hpow
  change D.dlog2 (z₁ * z₂) ≡ D.dlog2 z₁ + D.dlog2 z₂ [MOD (D.q ^ 2 - 1)] at hpow
  have hmod : (k.val * D.dlog2 (z₁ * z₂)) % (D.q ^ 2 - 1) =
      (k.val * D.dlog2 z₁ + k.val * D.dlog2 z₂) % (D.q ^ 2 - 1) := by
    have := Nat.ModEq.mul_left k.val hpow
    rwa [mul_add] at this
  have hadd :
      2 * Real.pi * Complex.I * ((k.val * D.dlog2 z₁ : ℕ) : ℂ) / ((D.q ^ 2 - 1 : ℕ) : ℂ) +
        2 * Real.pi * Complex.I * ((k.val * D.dlog2 z₂ : ℕ) : ℂ) / ((D.q ^ 2 - 1 : ℕ) : ℂ) =
      2 * Real.pi * Complex.I * ((k.val * D.dlog2 z₁ + k.val * D.dlog2 z₂ : ℕ) : ℂ) /
        ((D.q ^ 2 - 1 : ℕ) : ℂ) := by
    push_cast
    ring
  rw [hadd]
  exact cexp_two_pi_I_mul_div_mod (NeZero.ne (D.q ^ 2 - 1)) hmod

private lemma theta_h_ne_one (D : FieldData) {k : D.Lab2} (hk : k ≠ 0) :
    D.theta k D.h ≠ 1 := by
  simp only [FieldData.theta, if_neg (h_ne_zero D), dlog2_h, mul_one]
  rw [Ne, Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (NeZero.ne (D.q ^ 2 - 1))]
  have hk_pos : 0 < k.val := Nat.pos_of_ne_zero (mt (ZMod.val_eq_zero k).mp hk)
  have hk_lt : k.val < D.q ^ 2 - 1 := ZMod.val_lt k
  exact Nat.not_dvd_of_pos_of_lt hk_pos hk_lt

private lemma sum_theta_eq_zero (D : FieldData) {k : D.Lab2} (hk : k ≠ 0) :
    ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => z ≠ 0), D.theta k z = 0 := by
  let S := ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => z ≠ 0), D.theta k z
  have hshift : D.theta k D.h * S = S := by
    dsimp [S]
    rw [Finset.mul_sum]
    refine Finset.sum_bij (fun z _ => D.h * z) ?_ ?_ ?_ ?_
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact mul_ne_zero (h_ne_zero D) hz
    · intro z₁ _ z₂ _ heq
      exact mul_left_cancel₀ (h_ne_zero D) heq
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      refine ⟨D.h⁻¹ * w, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact mul_ne_zero (inv_ne_zero (h_ne_zero D)) hw
      · rw [← mul_assoc, mul_inv_cancel₀ (h_ne_zero D), one_mul]
    · intro z _
      exact (theta_mul D k D.h z).symm
  have hmul0 : (D.theta k D.h - 1) * S = 0 := by
    rw [sub_mul, one_mul, hshift, sub_self]
  exact (mul_eq_zero.mp hmul0).resolve_left (sub_ne_zero.mpr (theta_h_ne_one D hk))

private lemma algebraMap_gen (D : FieldData) :
    algebraMap D.Fq D.Fq2 D.gen = D.h ^ (D.q + 1) := by
  unfold FieldData.gen
  have hnorm := FiniteField.algebraMap_norm_eq_pow_sum D.Fq D.Fq2 D.h
  rw [finrank_fq2, Nat.card_eq_fintype_card, card_fq] at hnorm
  have hsum : ∑ i ∈ Finset.range 2, D.q ^ i = D.q + 1 := by
    simp [Finset.sum_range_succ, add_comm]
  rwa [hsum] at hnorm

private lemma orderOf_gen (D : FieldData) : orderOf D.gen = D.q - 1 := by
  have hinj : Function.Injective (algebraMap D.Fq D.Fq2) := RingHom.injective _
  have hord : orderOf D.gen = orderOf (algebraMap D.Fq D.Fq2 D.gen) :=
    (orderOf_injective (algebraMap D.Fq D.Fq2).toMonoidHom hinj D.gen).symm
  rw [hord, algebraMap_gen, orderOf_pow' _ (Nat.succ_ne_zero D.q), D.h_order]
  change (D.q ^ 2 - 1) / Nat.gcd (D.q ^ 2 - 1) (D.q + 1) = D.q - 1
  have hq : 1 < D.q := D.one_lt_q
  have hq2 : 1 ≤ D.q ^ 2 := by nlinarith
  have hfac : D.q ^ 2 - 1 = (D.q - 1) * (D.q + 1) := by
    zify [hq.le, hq2]
    ring
  rw [hfac, Nat.gcd_eq_right (dvd_mul_left _ _), Nat.mul_div_cancel _ (by omega)]

private lemma gen_ne_zero (D : FieldData) : D.gen ≠ 0 := by
  intro h0
  have ho : orderOf D.gen = 0 := by rw [h0, orderOf_zero]
  rw [orderOf_gen] at ho
  exact NeZero.ne (D.q - 1) ho

private lemma gen_ne_one (D : FieldData) (hq : 2 < D.q) : D.gen ≠ 1 := by
  intro h1
  have ho : orderOf D.gen = 1 := by rw [h1, orderOf_one]
  rw [orderOf_gen] at ho
  omega

private lemma dlog_gen (D : FieldData) (hq : 2 < D.q) : D.dlog D.gen = 1 := by
  have hex : ∃ n : ℕ, D.gen ^ n = D.gen := ⟨1, pow_one _⟩
  simp only [FieldData.dlog, dif_pos hex]
  rw [Nat.find_eq_iff]
  refine ⟨pow_one _, ?_⟩
  intro m hm
  have hm0 : m = 0 := by omega
  subst hm0
  simpa using (gen_ne_one D hq).symm

private lemma chi_zero_eq_one (D : FieldData) {x : D.Fq} (hx : x ≠ 0) :
    D.chi 0 x = 1 := by
  simp [FieldData.chi, if_neg hx]

private lemma chi_gen_ne_one (D : FieldData) {α : D.Lab} (hα : α ≠ 0) :
    D.chi α D.gen ≠ 1 := by
  have hq_sub_ne : D.q - 1 ≠ 1 := by
    intro h1
    have : Subsingleton D.Lab := by
      change Subsingleton (ZMod (D.q - 1))
      rw [h1]
      infer_instance
    exact hα (Subsingleton.elim _ _)
  have hq2 : 2 < D.q := by have := D.one_lt_q; omega
  simp only [FieldData.chi, if_neg (gen_ne_zero D), dlog_gen D hq2, mul_one]
  rw [Ne, Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (NeZero.ne (D.q - 1))]
  have hα_pos : 0 < α.val := Nat.pos_of_ne_zero (mt (ZMod.val_eq_zero α).mp hα)
  have hα_lt : α.val < D.q - 1 := ZMod.val_lt α
  exact Nat.not_dvd_of_pos_of_lt hα_pos hα_lt

private lemma psi_zero (D : FieldData) : D.psi 0 = 1 := by
  simp [FieldData.psi]

private lemma psi_add (D : FieldData) (x y : D.Fq) :
    D.psi (x + y) = D.psi x * D.psi y := by
  simp only [FieldData.psi]
  rw [← Complex.exp_add, map_add]
  set a := Algebra.trace (ZMod D.p) D.Fq x
  set b := Algebra.trace (ZMod D.p) D.Fq y
  have hadd :
      2 * Real.pi * Complex.I * ((a.val : ℕ) : ℂ) / (D.p : ℂ) +
        2 * Real.pi * Complex.I * ((b.val : ℕ) : ℂ) / (D.p : ℂ) =
      2 * Real.pi * Complex.I * ((a.val + b.val : ℕ) : ℂ) / (D.p : ℂ) := by
    push_cast
    ring
  rw [hadd]
  apply cexp_two_pi_I_mul_div_mod D.hp.ne_zero
  rw [ZMod.val_add, Nat.mod_mod]

private lemma gauss_zero (D : FieldData) : D.gauss 0 = -1 := by
  have hsurj : Function.Surjective (Algebra.trace (ZMod D.p) D.Fq) :=
    Algebra.trace_surjective (ZMod D.p) D.Fq
  obtain ⟨c, hc⟩ := hsurj 1
  have hpsi_c : D.psi c ≠ 1 := by
    simp only [FieldData.psi, hc]
    have : Fact (1 < D.p) := ⟨D.hp.one_lt⟩
    rw [ZMod.val_one, Nat.cast_one, mul_one, Ne]
    have hiff := Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (k := 1) D.hp.ne_zero
    simp only [Nat.cast_one, mul_one] at hiff
    rw [hiff]
    exact Nat.not_dvd_of_pos_of_lt Nat.one_pos D.hp.one_lt
  have hsum_univ : ∑ x : D.Fq, D.psi x = 0 := by
    have hshift : ∑ x : D.Fq, D.psi x = ∑ x : D.Fq, D.psi (x + c) := by
      refine (Equiv.sum_comp (Equiv.addRight c) D.psi).symm
    have hmul : ∑ x : D.Fq, D.psi x = D.psi c * ∑ x : D.Fq, D.psi x := by
      calc
        ∑ x : D.Fq, D.psi x = ∑ x : D.Fq, D.psi (x + c) := hshift
        _ = ∑ x : D.Fq, D.psi c * D.psi x := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [psi_add, mul_comm]
        _ = D.psi c * ∑ x : D.Fq, D.psi x := (Finset.mul_sum _ _ _).symm
    have hmul0 : (D.psi c - 1) * ∑ x : D.Fq, D.psi x = 0 := by
      rw [sub_mul, one_mul, ← hmul, sub_self]
    exact (mul_eq_zero.mp hmul0).resolve_left (sub_ne_zero.mpr hpsi_c)
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset D.Fq) D.psi (Finset.mem_univ 0)
  rw [hsum_univ, psi_zero] at hsplit
  have hfilt : Finset.univ.erase (0 : D.Fq) = Finset.univ.filter (fun x : D.Fq => x ≠ 0) := by
    ext x; simp
  have hgauss : D.gauss 0 = ∑ x ∈ Finset.univ.erase (0 : D.Fq), D.psi x := by
    rw [FieldData.gauss, FieldData.gaussG, hfilt]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [chi_zero_eq_one D hx, one_mul, one_mul]
  rw [← hgauss] at hsplit
  exact eq_neg_of_add_eq_zero_right hsplit

private lemma tr_algebraMap_mul (D : FieldData) (t : D.Fq) (z : D.Fq2) :
    D.tr (algebraMap D.Fq D.Fq2 t * z) = t * D.tr z := by
  rw [FieldData.tr, ← Algebra.smul_def, map_smul, smul_eq_mul]
  rfl

private lemma mem_ker_tr_iff (D : FieldData) {ζ : D.Fq2} (hζ0 : ζ ≠ 0) (hζtr : D.tr ζ = 0)
    (z : D.Fq2) :
    D.tr z = 0 ↔ ∃ x : D.Fq, algebraMap D.Fq D.Fq2 x * ζ = z := by
  constructor
  · intro hztr
    let T : D.Fq2 →ₗ[D.Fq] D.Fq := Algebra.trace D.Fq D.Fq2
    have hperf : PerfectField D.Fq := PerfectField.ofFinite
    have halg : Algebra.IsAlgebraic D.Fq D.Fq2 := Algebra.IsAlgebraic.of_finite D.Fq D.Fq2
    have hsurj : Function.Surjective T :=
      @Algebra.trace_surjective D.Fq D.Fq2 _ _ _ _
        (@Algebra.IsAlgebraic.isSeparable_of_perfectField D.Fq D.Fq2 _ _ _ halg hperf)
    have hrange : LinearMap.range T = ⊤ := LinearMap.range_eq_top.mpr hsurj
    have hrn := LinearMap.finrank_range_add_finrank_ker T
    rw [hrange, finrank_top, Module.finrank_self, finrank_fq2] at hrn
    have hker_dim : Module.finrank D.Fq (LinearMap.ker T) = 1 := by omega
    have hle : Submodule.span D.Fq {ζ} ≤ LinearMap.ker T := by
      rw [Submodule.span_singleton_le_iff_mem]
      exact hζtr
    have hspan_dim : Module.finrank D.Fq (Submodule.span D.Fq {ζ}) = 1 :=
      finrank_span_singleton hζ0
    have heq : Submodule.span D.Fq {ζ} = LinearMap.ker T :=
      Submodule.eq_of_le_of_finrank_eq hle (hspan_dim.trans hker_dim.symm)
    have hzmem : z ∈ Submodule.span D.Fq {ζ} := by
      rw [heq]
      exact hztr
    rw [Submodule.mem_span_singleton] at hzmem
    rcases hzmem with ⟨x, hx⟩
    exact ⟨x, by simpa [Algebra.smul_def] using hx⟩
  · rintro ⟨x, rfl⟩
    rw [tr_algebraMap_mul, hζtr, mul_zero]

theorem solution (D : FieldData) (k : D.Lab2) (α : D.Lab)
    (hres : ∀ x : D.Fq, x ≠ 0 → D.theta k (algebraMap D.Fq D.Fq2 x) = D.chi α x) :
    let S : D.Fq → ℂ := fun t =>
      ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => z ≠ 0 ∧ D.tr z = t), D.theta k z
    (∀ t : D.Fq, t ≠ 0 → S t = D.chi α t * S 1) ∧
    D.gaussQ2 (D.theta k) = S 0 + D.gauss α * S 1 ∧
    (∀ ζ : D.Fq2, ζ ≠ 0 → D.tr ζ = 0 →
      S 0 = if α = 0 then ((D.q : ℂ) - 1) * D.theta k ζ else 0) ∧
    (k ≠ 0 → α = 0 → ∀ ζ : D.Fq2, ζ ≠ 0 → D.tr ζ = 0 →
      S 1 = -D.theta k ζ ∧ D.gaussQ2 (D.theta k) = (D.q : ℂ) * D.theta k ζ) := by
  intro S
  have h1 : ∀ t : D.Fq, t ≠ 0 → S t = D.chi α t * S 1 := by
    intro t ht
    dsimp [S]
    rw [Finset.mul_sum]
    have hut : algebraMap D.Fq D.Fq2 t ≠ 0 := by simpa using ht
    refine Finset.sum_bij (fun z _ => algebraMap D.Fq D.Fq2 t * z) ?_ ?_ ?_ ?_ |>.symm
    · intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      refine ⟨mul_ne_zero hut hz.1, ?_⟩
      rw [tr_algebraMap_mul, hz.2, mul_one]
    · intro z₁ _ z₂ _ heq
      exact mul_left_cancel₀ hut heq
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      refine ⟨(algebraMap D.Fq D.Fq2 t)⁻¹ * w, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨mul_ne_zero (inv_ne_zero hut) hw.1, ?_⟩
        rw [← map_inv₀, tr_algebraMap_mul, hw.2, inv_mul_cancel₀ ht]
      · rw [← mul_assoc, mul_inv_cancel₀ hut, one_mul]
    · intro z _
      rw [theta_mul, hres t ht]
  have h2 : D.gaussQ2 (D.theta k) = S 0 + D.gauss α * S 1 := by
    rw [FieldData.gaussQ2]
    have hpart := (Finset.sum_fiberwise_of_maps_to
      (s := Finset.univ.filter (fun z : D.Fq2 => z ≠ 0))
      (t := (Finset.univ : Finset D.Fq))
      (g := D.tr)
      (f := fun z => D.theta k z * D.psi (D.tr z))
      (fun _ _ => Finset.mem_univ _)).symm
    rw [hpart]
    have hterm : ∑ t : D.Fq,
        ∑ z ∈ (Finset.univ.filter (fun z : D.Fq2 => z ≠ 0)).filter (fun z => D.tr z = t),
          D.theta k z * D.psi (D.tr z) =
        ∑ t : D.Fq, S t * D.psi t := by
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.filter_filter]
      dsimp [S]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun z hz => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
      rw [hz.2]
    rw [hterm]
    have hsplit := Finset.add_sum_erase (Finset.univ : Finset D.Fq)
      (fun t => S t * D.psi t) (Finset.mem_univ 0)
    rw [← hsplit, psi_zero, mul_one]
    congr 1
    have hfilt : Finset.univ.erase (0 : D.Fq) = Finset.univ.filter (fun t : D.Fq => t ≠ 0) := by
      ext t; simp
    rw [hfilt, FieldData.gauss, FieldData.gaussG, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t ht => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [h1 t ht, one_mul]
    ring
  have h3 : ∀ ζ : D.Fq2, ζ ≠ 0 → D.tr ζ = 0 →
      S 0 = if α = 0 then ((D.q : ℂ) - 1) * D.theta k ζ else 0 := by
    intro ζ hζ0 hζtr
    have hS0 : S 0 = (∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0), D.chi α x) * D.theta k ζ := by
      dsimp [S]
      rw [Finset.sum_mul]
      refine Finset.sum_bij (fun x _ => algebraMap D.Fq D.Fq2 x * ζ) ?_ ?_ ?_ ?_ |>.symm
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        refine ⟨mul_ne_zero (by simpa using hx) hζ0, ?_⟩
        rw [tr_algebraMap_mul, hζtr, mul_zero]
      · intro x₁ _ x₂ _ heq
        exact (algebraMap D.Fq D.Fq2).injective (mul_right_cancel₀ hζ0 heq)
      · intro z hz
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
        obtain ⟨x, rfl⟩ := (mem_ker_tr_iff D hζ0 hζtr z).mp hz.2
        refine ⟨x, ?_, rfl⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro hx0
        apply hz.1
        rw [hx0, map_zero, zero_mul]
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rw [theta_mul, hres x hx]
    rw [hS0]
    by_cases hα : α = 0
    · rw [if_pos hα]
      subst hα
      have hsum : ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0), D.chi 0 x = (D.q : ℂ) - 1 := by
        have h1s : ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0), D.chi 0 x =
            ∑ _x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0), (1 : ℂ) := by
          refine Finset.sum_congr rfl fun x hx => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          exact chi_zero_eq_one D hx
        rw [h1s, Finset.sum_const, nsmul_eq_mul, mul_one]
        have hfilt : Finset.univ.filter (fun x : D.Fq => x ≠ 0) = Finset.univ.erase (0 : D.Fq) := by
          ext x; simp
        rw [hfilt, Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, card_fq]
        have hq : 1 ≤ D.q := D.one_lt_q.le
        rw [Nat.cast_sub hq, Nat.cast_one]
      rw [hsum]
    · rw [if_neg hα]
      have hsum : ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0), D.chi α x = 0 := by
        let T := ∑ x ∈ Finset.univ.filter (fun x : D.Fq => x ≠ 0), D.chi α x
        have hshift : D.chi α D.gen * T = T := by
          dsimp [T]
          rw [Finset.mul_sum]
          refine Finset.sum_bij (fun x _ => D.gen * x) ?_ ?_ ?_ ?_
          · intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
            exact mul_ne_zero (gen_ne_zero D) hx
          · intro x₁ _ x₂ _ heq
            exact mul_left_cancel₀ (gen_ne_zero D) heq
          · intro y hy
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
            refine ⟨D.gen⁻¹ * y, ?_, ?_⟩
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
              exact mul_ne_zero (inv_ne_zero (gen_ne_zero D)) hy
            · rw [← mul_assoc, mul_inv_cancel₀ (gen_ne_zero D), one_mul]
          · intro x hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
            rw [← hres (D.gen * x) (mul_ne_zero (gen_ne_zero D) hx), map_mul, theta_mul,
              hres D.gen (gen_ne_zero D), hres x hx]
        have hmul0 : (D.chi α D.gen - 1) * T = 0 := by
          rw [sub_mul, one_mul, hshift, sub_self]
        exact (mul_eq_zero.mp hmul0).resolve_left (sub_ne_zero.mpr (chi_gen_ne_one D hα))
      rw [hsum, zero_mul]
  refine ⟨h1, h2, h3, ?_⟩
  intro hk hα ζ hζ0 hζtr
  have htot : ∑ z ∈ Finset.univ.filter (fun z : D.Fq2 => z ≠ 0), D.theta k z = 0 :=
    sum_theta_eq_zero D hk
  have hpart := (Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ.filter (fun z : D.Fq2 => z ≠ 0))
    (t := (Finset.univ : Finset D.Fq))
    (g := D.tr)
    (f := D.theta k)
    (fun _ _ => Finset.mem_univ _)).symm
  rw [htot] at hpart
  have hpart' : ∑ t : D.Fq, S t = 0 := by
    rw [hpart]
    refine Finset.sum_congr rfl fun t _ => ?_
    dsimp [S]
    rw [Finset.filter_filter]
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset D.Fq) S (Finset.mem_univ 0)
  rw [hpart'] at hsplit
  have hfilt : Finset.univ.erase (0 : D.Fq) = Finset.univ.filter (fun t : D.Fq => t ≠ 0) := by
    ext t; simp
  have hnonzero : ∑ t ∈ Finset.univ.erase (0 : D.Fq), S t = ((D.q : ℂ) - 1) * S 1 := by
    rw [hfilt]
    have hconst : ∑ t ∈ Finset.univ.filter (fun t : D.Fq => t ≠ 0), S t =
        ∑ _t ∈ Finset.univ.filter (fun t : D.Fq => t ≠ 0), S 1 := by
      refine Finset.sum_congr rfl fun t ht => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
      rw [h1 t ht, hα, chi_zero_eq_one D ht, one_mul]
    rw [hconst, Finset.sum_const, nsmul_eq_mul, ← hfilt, Finset.card_erase_of_mem (Finset.mem_univ 0),
      Finset.card_univ, card_fq]
    have hq : 1 ≤ D.q := D.one_lt_q.le
    rw [Nat.cast_sub hq, Nat.cast_one]
  have hS0 : S 0 = ((D.q : ℂ) - 1) * D.theta k ζ := by
    simpa [hα] using h3 ζ hζ0 hζtr
  rw [hS0, hnonzero] at hsplit
  have hq_sub_ne : (D.q : ℂ) - 1 ≠ 0 := by
    have hq : (D.q : ℂ) ≠ 1 := by exact_mod_cast D.one_lt_q.ne'
    exact sub_ne_zero.mpr hq
  have hfac : ((D.q : ℂ) - 1) * (D.theta k ζ + S 1) = 0 := by
    rw [← mul_add] at hsplit
    exact hsplit
  have hS1_sum : D.theta k ζ + S 1 = 0 := (mul_eq_zero.mp hfac).resolve_left hq_sub_ne
  have hS1 : S 1 = -D.theta k ζ := eq_neg_of_add_eq_zero_right hS1_sum
  refine ⟨hS1, ?_⟩
  rw [h2, hS0, hα, gauss_zero, hS1]
  ring
