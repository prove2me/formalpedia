-- Prove2me | solution 1 for GL2QFT.lemma_A_6
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T03:23:04.924064+00:00
-- url     : https://prove2.me/submissions/322286ee-7a36-4891-8f82-e1270653bcb0

import Definitions.Def_GL2QFT_Characters

noncomputable section

open Classical

namespace GL2QFT.LemmaA6

open Polynomial FieldData

local instance (D : FieldData) : Field D.Fq := AdjoinRoot.instField
local instance (D : FieldData) : Field D.Fq2 := AdjoinRoot.instField
local instance (D : FieldData) : IsDomain D.Fq2 := inferInstance
local instance (D : FieldData) : IsReduced D.Fq2 := inferInstance

private lemma finrank_Fq (D : FieldData) : Module.finrank (ZMod D.p) D.Fq = D.r := by
  change Module.finrank (ZMod D.p) (AdjoinRoot D.f) = D.r
  rw [(AdjoinRoot.powerBasis' D.f_monic).finrank, AdjoinRoot.powerBasis'_dim, D.f_deg]

private lemma card_Fq (D : FieldData) : Fintype.card D.Fq = D.q := by
  rw [Module.card_eq_pow_finrank (K := ZMod D.p) (V := D.Fq), ZMod.card, finrank_Fq, q]

private lemma finrank_Fq2 (D : FieldData) : Module.finrank D.Fq D.Fq2 = 2 := by
  change Module.finrank D.Fq (AdjoinRoot D.F) = 2
  rw [(AdjoinRoot.powerBasis' D.F_monic).finrank, AdjoinRoot.powerBasis'_dim, D.F_deg]

private lemma card_Fq2 (D : FieldData) : Fintype.card D.Fq2 = D.q ^ 2 := by
  rw [Module.card_eq_pow_finrank (K := D.Fq) (V := D.Fq2), card_Fq, finrank_Fq2]

private lemma charP_Fq (D : FieldData) : CharP D.Fq D.p :=
  charP_of_injective_algebraMap (algebraMap (ZMod D.p) D.Fq).injective D.p

private lemma charP_Fq2 (D : FieldData) : CharP D.Fq2 D.p := by
  have : CharP D.Fq D.p := charP_Fq D
  exact charP_of_injective_algebraMap (algebraMap D.Fq D.Fq2).injective D.p

private lemma add_pow_q (D : FieldData) (a b : D.Fq2) :
    (a + b) ^ D.q = a ^ D.q + b ^ D.q := by
  have : Fact D.p.Prime := ⟨D.hp⟩
  have : CharP D.Fq2 D.p := charP_Fq2 D
  exact add_pow_char_pow a b D.p D.r

private lemma algebraMap_tr (D : FieldData) (z : D.Fq2) :
    algebraMap D.Fq D.Fq2 (D.tr z) = z + z ^ D.q := by
  rw [tr, FiniteField.algebraMap_trace_eq_sum_pow D.Fq D.Fq2 z, finrank_Fq2,
    ← Fintype.card_eq_nat_card, card_Fq, Finset.sum_range_succ, Finset.sum_range_one,
    pow_zero, pow_one, pow_one]

private lemma algebraMap_nrm (D : FieldData) (z : D.Fq2) :
    algebraMap D.Fq D.Fq2 (D.nrm z) = z * z ^ D.q := by
  rw [nrm, FiniteField.algebraMap_norm_eq_prod_pow D.Fq D.Fq2 z, finrank_Fq2,
    ← Fintype.card_eq_nat_card, card_Fq, Finset.prod_range_succ, Finset.prod_range_one,
    pow_zero, pow_one, pow_one]

private lemma algebraMap_pow_q (D : FieldData) (x : D.Fq) :
    (algebraMap D.Fq D.Fq2 x) ^ D.q = algebraMap D.Fq D.Fq2 x := by
  rw [← map_pow, ← card_Fq D, FiniteField.pow_card]

private lemma pow_q_eq_self_iff (D : FieldData) (z : D.Fq2) :
    z ^ D.q = z ↔ z ∈ Set.range (algebraMap D.Fq D.Fq2) := by
  constructor
  · intro hz
    let ι := algebraMap D.Fq D.Fq2
    let S : Finset D.Fq2 := Finset.univ.image ι
    let P : D.Fq2[X] := X ^ D.q - X
    have hP_ne : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero D.Fq2 D.one_lt_q
    have hP_deg : P.natDegree = D.q := FiniteField.X_pow_card_sub_X_natDegree_eq D.Fq2 D.one_lt_q
    let R : Finset D.Fq2 := P.roots.toFinset
    have hSR : S ⊆ R := by
      intro w hw
      rcases Finset.mem_image.mp hw with ⟨x, _, rfl⟩
      rw [Multiset.mem_toFinset, mem_roots hP_ne, IsRoot.def,
        eval_sub, eval_pow, eval_X, algebraMap_pow_q, sub_self]
    have hcardS : S.card = D.q := by
      rw [Finset.card_image_of_injective _ ι.injective, Finset.card_univ, card_Fq]
    have hcardR : R.card ≤ S.card := by
      rw [hcardS, ← hP_deg]
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' P)
    have hEq : S = R := Finset.eq_of_subset_of_card_le hSR hcardR
    have hzR : z ∈ R := by
      rw [Multiset.mem_toFinset, mem_roots hP_ne, IsRoot.def,
        eval_sub, eval_pow, eval_X, hz, sub_self]
    rw [← hEq] at hzR
    rcases Finset.mem_image.mp hzR with ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact algebraMap_pow_q D x

private lemma h_ne_zero (D : FieldData) : D.h ≠ 0 := by
  intro h0
  have hord := D.h_order
  rw [h0, orderOf_zero] at hord
  have hq : 1 < D.q := D.one_lt_q
  have hq2 : 1 < D.q ^ 2 := one_lt_pow₀ hq (by decide)
  change 0 = D.q ^ 2 - 1 at hord
  omega

private lemma exists_gen_pow_eq (D : FieldData) {x : D.Fq} (hx : x ≠ 0) :
    ∃ n : ℕ, D.gen ^ n = x := by
  let hu : (D.Fq2)ˣ := Units.mk0 D.h (h_ne_zero D)
  have hord_u : orderOf hu = Fintype.card (D.Fq2)ˣ := by
    rw [← orderOf_units, Units.val_mk0, D.h_order, Fintype.card_units, card_Fq2, q]
  obtain ⟨w, hw⟩ := FiniteField.unitsMap_norm_surjective D.Fq D.Fq2 (Units.mk0 x hx)
  have hw_mem : w ∈ Subgroup.zpowers hu := by
    have htop : Subgroup.zpowers hu = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, hord_u, Fintype.card_eq_nat_card]
    rw [htop]
    trivial
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw_mem
  obtain ⟨n, hn_eq⟩ : ∃ n : ℕ, hu ^ n = w := by
    rw [← hk]
    refine ⟨(k % (orderOf hu : ℤ)).toNat, ?_⟩
    have hpos : (0 : ℤ) < orderOf hu := Int.natCast_pos.mpr (orderOf_pos hu)
    have hnonneg : 0 ≤ k % (orderOf hu : ℤ) := Int.emod_nonneg k hpos.ne'
    rw [← zpow_natCast, Int.toNat_of_nonneg hnonneg, zpow_mod_orderOf]
  refine ⟨n, ?_⟩
  have h1 : (Units.map (Algebra.norm D.Fq : D.Fq2 →* D.Fq) w : D.Fq) = x := by
    rw [hw]; rfl
  rw [← hn_eq, map_pow, Units.val_pow_eq_pow_val, Units.coe_map, Units.val_mk0] at h1
  exact h1

private lemma dlog_spec (D : FieldData) {x : D.Fq} (hx : x ≠ 0) : D.gen ^ D.dlog x = x := by
  have hex : ∃ n : ℕ, D.gen ^ n = x := exists_gen_pow_eq D hx
  rw [dlog, dif_pos hex]
  exact Nat.find_spec hex

private lemma orderOf_gen (D : FieldData) : orderOf D.gen = D.q - 1 := by
  have hmap : algebraMap D.Fq D.Fq2 D.gen = D.h ^ (D.q + 1) := by
    rw [gen]
    change algebraMap D.Fq D.Fq2 (D.nrm D.h) = D.h ^ (D.q + 1)
    rw [algebraMap_nrm, mul_comm, ← pow_succ]
  have hinj : orderOf ((algebraMap D.Fq D.Fq2 : D.Fq →* D.Fq2) D.gen) = orderOf D.gen :=
    orderOf_injective (algebraMap D.Fq D.Fq2 : D.Fq →* D.Fq2)
      (algebraMap D.Fq D.Fq2).injective D.gen
  rw [← hinj]
  change orderOf (algebraMap D.Fq D.Fq2 D.gen) = D.q - 1
  rw [hmap, orderOf_pow' D.h (by omega), D.h_order]
  have hq : 1 < D.q := D.one_lt_q
  have hq2 : 1 ≤ D.q ^ 2 := by nlinarith
  have hsq : (D.p ^ D.r) ^ 2 - 1 = (D.q - 1) * (D.q + 1) := by
    change D.q ^ 2 - 1 = (D.q - 1) * (D.q + 1)
    zify [hq.le, hq2]
    ring
  rw [hsq, Nat.gcd_mul_left_left, Nat.mul_div_cancel _ (by omega)]

private lemma chi_zero (D : FieldData) (α : D.Lab) : D.chi α 0 = 0 := by
  simp [chi]

private lemma chi_mul (D : FieldData) (α : D.Lab) (x y : D.Fq) :
    D.chi α (x * y) = D.chi α x * D.chi α y := by
  by_cases hx : x = 0
  · subst hx; simp [chi_zero]
  by_cases hy : y = 0
  · subst hy; simp [chi_zero]
  have hxy : x * y ≠ 0 := mul_ne_zero hx hy
  simp only [chi, if_neg hx, if_neg hy, if_neg hxy, ← Complex.exp_add]
  have hpow : D.gen ^ D.dlog (x * y) = D.gen ^ (D.dlog x + D.dlog y) := by
    rw [pow_add, dlog_spec D hx, dlog_spec D hy, dlog_spec D hxy]
  have hfin : IsOfFinOrder D.gen := by
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨D.q - 1, Nat.sub_pos_of_lt D.one_lt_q, ?_⟩
    rw [← orderOf_gen D, pow_orderOf_eq_one]
  have hmod : D.dlog (x * y) ≡ D.dlog x + D.dlog y [MOD (D.q - 1)] := by
    rw [← orderOf_gen D]
    exact (hfin.pow_eq_pow_iff_modEq).mp hpow
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp (Int.natCast_modEq_iff.mpr hmod).symm
  have hq0 : ((D.q - 1 : ℕ) : ℂ) ≠ 0 := by
    have := D.one_lt_q
    exact_mod_cast (by omega : D.q - 1 ≠ 0)
  have hkc : ((D.dlog (x * y) : ℕ) : ℂ) =
      ((D.dlog x : ℕ) : ℂ) + ((D.dlog y : ℕ) : ℂ) + (k : ℂ) * ((D.q - 1 : ℕ) : ℂ) := by
    have h1 := congrArg (Int.cast (R := ℂ)) hk
    push_cast at h1 ⊢
    linear_combination h1
  have hdiff : (2 * Real.pi * Complex.I * ((α.val * D.dlog (x * y) : ℕ) : ℂ) / ((D.q - 1 : ℕ) : ℂ)) =
      (2 * Real.pi * Complex.I * ((α.val * D.dlog x : ℕ) : ℂ) / ((D.q - 1 : ℕ) : ℂ) +
       2 * Real.pi * Complex.I * ((α.val * D.dlog y : ℕ) : ℂ) / ((D.q - 1 : ℕ) : ℂ)) +
      (((α.val : ℤ) * k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    rw [hkc]
    field_simp
  rw [hdiff, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private lemma psi_add (D : FieldData) (x y : D.Fq) : D.psi (x + y) = D.psi x * D.psi y := by
  simp only [psi, ← Complex.exp_add]
  have hp0 : (D.p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.hp.ne_zero
  let a := Algebra.trace (ZMod D.p) D.Fq x
  let b := Algebra.trace (ZMod D.p) D.Fq y
  let qn : ℕ := (a.val + b.val) / D.p
  have hab : Algebra.trace (ZMod D.p) D.Fq (x + y) = a + b := map_add _ x y
  rw [hab, ZMod.val_add]
  have hdiv : ((a.val : ℂ) + (b.val : ℂ)) =
      (((a.val + b.val) % D.p : ℕ) : ℂ) + (qn : ℂ) * (D.p : ℂ) := by
    have hnat : D.p * qn + (a.val + b.val) % D.p = a.val + b.val := Nat.div_add_mod _ _
    have h1 : ((D.p * qn + (a.val + b.val) % D.p : ℕ) : ℂ) = ((a.val + b.val : ℕ) : ℂ) := by
      exact_mod_cast hnat
    push_cast at h1
    linear_combination -h1
  have h1 : (((a.val + b.val) % D.p : ℕ) : ℂ) =
      (a.val : ℂ) + (b.val : ℂ) - (qn : ℂ) * (D.p : ℂ) := by
    linear_combination -hdiv
  have heq : 2 * Real.pi * Complex.I * (((a.val + b.val) % D.p : ℕ) : ℂ) / (D.p : ℂ) =
      (2 * Real.pi * Complex.I * ((a.val : ℕ) : ℂ) / (D.p : ℂ) +
       2 * Real.pi * Complex.I * ((b.val : ℕ) : ℂ) / (D.p : ℂ)) +
      ((-(qn : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [h1]
    push_cast
    field_simp
    ring
  rw [heq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private lemma sum_psi_eq_zero (D : FieldData) : ∑ t : D.Fq, D.psi t = 0 := by
  have hne : Algebra.trace (ZMod D.p) D.Fq ≠ 0 := by
    have : Fact D.p.Prime := ⟨D.hp⟩
    have h1 := (traceForm_nondegenerate_tfae (ZMod D.p) D.Fq).out 0 1
    exact h1.mp inferInstance
  obtain ⟨c, hc⟩ : ∃ c : D.Fq, Algebra.trace (ZMod D.p) D.Fq c ≠ 0 := by
    by_contra! hall
    apply hne
    ext x
    exact hall x
  have hpsi_ne : D.psi c ≠ 1 := by
    intro h1
    rw [psi, Complex.exp_eq_one_iff] at h1
    obtain ⟨k, hk⟩ := h1
    have h2pi : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hp0 : (D.p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr D.hp.ne_zero
    have hkc : (((Algebra.trace (ZMod D.p) D.Fq c).val : ℕ) : ℂ) = (k : ℂ) * (D.p : ℂ) := by
      have hdiv : 2 * Real.pi * Complex.I * (((Algebra.trace (ZMod D.p) D.Fq c).val : ℕ) : ℂ) /
          (D.p : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := hk
      field_simp at hdiv
      linear_combination hdiv
    have hkz : ((Algebra.trace (ZMod D.p) D.Fq c).val : ℤ) = k * (D.p : ℤ) := by
      exact_mod_cast hkc
    have : NeZero D.p := ⟨D.hp.ne_zero⟩
    have hpos : 0 < (Algebra.trace (ZMod D.p) D.Fq c).val :=
      Nat.pos_of_ne_zero (fun h0 => hc (ZMod.val_eq_zero _ |>.mp h0))
    have hlt : (Algebra.trace (ZMod D.p) D.Fq c).val < D.p := ZMod.val_lt _
    have hk_pos : 0 < k := by nlinarith
    nlinarith
  have hshift : D.psi c * ∑ t : D.Fq, D.psi t = ∑ t : D.Fq, D.psi t := by
    rw [Finset.mul_sum]
    simp_rw [← psi_add]
    exact Fintype.sum_equiv (Equiv.addLeft c) _ _ fun _ => rfl
  have hmul : (D.psi c - 1) * ∑ t : D.Fq, D.psi t = 0 := by
    linear_combination hshift
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hpsi_ne)

private lemma gauss_eq_sum (D : FieldData) (α : D.Lab) :
    D.gauss α = ∑ x : D.Fq, D.chi α x * D.psi x := by
  rw [gauss, gaussG, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x = 0
  · subst hx; simp [chi_zero]
  · simp [hx]

private lemma gaussQ2_eq_sum (D : FieldData) (α : D.Lab) :
    D.gaussQ2 (fun z => D.chi α (D.nrm z)) = ∑ z : D.Fq2, D.chi α (D.nrm z) * D.psi (D.tr z) := by
  rw [gaussQ2, Finset.sum_filter]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : z = 0
  · subst hz; simp [nrm, chi_zero]
  · simp [hz]

private def phi (D : FieldData) : (D.Fq × D.Fq) ⊕ D.Fq2 → D.Fq × D.Fq
  | Sum.inl (x, y) => (x + y, x * y)
  | Sum.inr z => (D.tr z, D.nrm z)

private lemma quad_monic (D : FieldData) (t u : D.Fq) :
    (X ^ 2 - C t * X + C u : D.Fq[X]).Monic := by
  have hdeg : (-C t * X + C u : D.Fq[X]).degree < (X ^ 2 : D.Fq[X]).degree := by
    compute_degree!
  have hEq : (X ^ 2 - C t * X + C u : D.Fq[X]) = X ^ 2 + (-C t * X + C u) := by ring
  rw [hEq]
  exact (monic_X_pow 2).add_of_left hdeg

private lemma quad_natDegree (D : FieldData) (t u : D.Fq) :
    (X ^ 2 - C t * X + C u : D.Fq[X]).natDegree = 2 := by
  have hdeg : (-C t * X + C u : D.Fq[X]).degree < (X ^ 2 : D.Fq[X]).degree := by
    compute_degree!
  have hEq : (X ^ 2 - C t * X + C u : D.Fq[X]) = X ^ 2 + (-C t * X + C u) := by ring
  rw [hEq, natDegree_add_eq_left_of_degree_lt hdeg, natDegree_X_pow]

private lemma eval_quad_iff (D : FieldData) {t u x : D.Fq} :
    (X ^ 2 - C t * X + C u).IsRoot x ↔ x ^ 2 - t * x + u = 0 := by
  simp [IsRoot.def]

private lemma quad_factor_of_isRoot (D : FieldData) {t u x : D.Fq}
    (hx : (X ^ 2 - C t * X + C u).IsRoot x) :
    (X ^ 2 - C t * X + C u) = (X - C x) * (X - C (t - x)) := by
  rw [eval_quad_iff] at hx
  have hu : u = t * x - x ^ 2 := by linear_combination hx
  rw [hu]
  simp only [C_sub, C_mul, C_pow]
  ring

private lemma pair_iff_isRoot (D : FieldData) (t u : D.Fq) (p : D.Fq × D.Fq) :
    (p.1 + p.2 = t ∧ p.1 * p.2 = u) ↔
      ((X ^ 2 - C t * X + C u).IsRoot p.1 ∧ p.2 = t - p.1) := by
  constructor
  · rintro ⟨hadd, hmul⟩
    have hp2 : p.2 = t - p.1 := eq_sub_of_add_eq' hadd
    refine ⟨?_, hp2⟩
    rw [eval_quad_iff, ← hadd, ← hmul]
    ring
  · rintro ⟨hr, hp2⟩
    rw [eval_quad_iff] at hr
    refine ⟨by rw [hp2]; ring, ?_⟩
    rw [hp2]
    linear_combination -hr

private lemma card_fiber_eq_two (D : FieldData) (t u : D.Fq) :
    (Finset.univ.filter (fun s => phi D s = (t, u))).card = 2 := by
  let L : Finset (D.Fq × D.Fq) := Finset.univ.filter (fun p => p.1 + p.2 = t ∧ p.1 * p.2 = u)
  let R : Finset D.Fq2 := Finset.univ.filter (fun z => D.tr z = t ∧ D.nrm z = u)
  have hsplit : (Finset.univ.filter (fun s => phi D s = (t, u))).card = L.card + R.card := by
    have hdisj : Disjoint
        (L.map ⟨Sum.inl, Sum.inl_injective⟩)
        (R.map ⟨Sum.inr, Sum.inr_injective⟩) := by
      rw [Finset.disjoint_left]
      rintro s hs1 hs2
      rcases Finset.mem_map.mp hs1 with ⟨p, _, rfl⟩
      rcases Finset.mem_map.mp hs2 with ⟨z, _, hz⟩
      dsimp at hz
      cases hz
    have hEq : Finset.univ.filter (fun s => phi D s = (t, u)) =
        (L.map ⟨Sum.inl, Sum.inl_injective⟩) ∪ (R.map ⟨Sum.inr, Sum.inr_injective⟩) := by
      ext s
      cases s with
      | inl p =>
        simp [L, phi, Prod.ext_iff]
      | inr z =>
        simp [R, phi, Prod.ext_iff]
    rw [hEq, Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map]
  rw [hsplit]
  let P : D.Fq[X] := X ^ 2 - C t * X + C u
  have hP_monic : P.Monic := quad_monic D t u
  have hP_deg : P.natDegree = 2 := quad_natDegree D t u
  have hP_ne : P ≠ 0 := hP_monic.ne_zero
  have hL_card : L.card = P.roots.toFinset.card := by
    refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_filter] at hp
      have hr := ((pair_iff_isRoot D t u p).mp hp.2).1
      rw [Multiset.mem_toFinset, mem_roots hP_ne]
      exact hr
    · intro p₁ hp₁ p₂ hp₂ h12
      rw [Finset.mem_filter] at hp₁ hp₂
      have hp12 := ((pair_iff_isRoot D t u p₁).mp hp₁.2).2
      have hp22 := ((pair_iff_isRoot D t u p₂).mp hp₂.2).2
      ext
      · exact h12
      · rw [hp12, hp22, h12]
    · intro x hx
      rw [Multiset.mem_toFinset, mem_roots hP_ne] at hx
      refine ⟨(x, t - x), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (pair_iff_isRoot D t u (x, t - x)).mpr ⟨hx, rfl⟩⟩, rfl⟩
  rw [hL_card]
  have hle2 : P.roots.toFinset.card ≤ 2 := by
    calc P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ = 2 := hP_deg
  let ι := algebraMap D.Fq D.Fq2
  have htr_nrm_root : ∀ z : D.Fq2, D.tr z = t ∧ D.nrm z = u → (P.map ι).IsRoot z := by
    rintro z ⟨htz, huz⟩
    rw [IsRoot.def]
    have hev : (P.map ι).eval z = z ^ 2 - ι t * z + ι u := by
      simp [P]
    rw [hev, ← htz, ← huz, algebraMap_tr, algebraMap_nrm]
    ring
  rcases Nat.lt_trichotomy P.roots.toFinset.card 1 with h0 | h1 | hgt1
  · have h0' : P.roots.toFinset.card = 0 := by omega
    rw [h0', zero_add]
    have hnoRoot : ∀ x : D.Fq, ¬ P.IsRoot x := by
      intro x hx
      have hx' : x ∈ P.roots.toFinset := by
        rw [Multiset.mem_toFinset, mem_roots hP_ne]
        exact hx
      rw [Finset.card_eq_zero.mp h0'] at hx'
      exact Finset.notMem_empty x hx'
    have hIrr : Irreducible P := by
      by_contra hnot
      rw [hP_monic.not_irreducible_iff_exists_add_mul_eq_coeff hP_deg] at hnot
      obtain ⟨c₁, c₂, hc0, hc1⟩ := hnot
      have hc0' : P.coeff 0 = u := by simp [P, coeff_C]
      have hc1' : P.coeff 1 = -t := by simp [P, coeff_C]
      apply hnoRoot (-c₁)
      rw [eval_quad_iff D]
      have : (-c₁) ^ 2 - t * (-c₁) + u = c₁ ^ 2 - (P.coeff 1) * c₁ + P.coeff 0 := by
        rw [hc0', hc1']; ring
      rw [this, hc0, hc1]
      ring
    have hSep : P.Separable := by
      have : PerfectField D.Fq := PerfectField.ofFinite
      exact PerfectField.separable_of_irreducible hIrr
    have hMapSep : (P.map ι).Separable := hSep.map
    have hdvd : P ∣ X ^ (D.q ^ 2) - X := by
      have hdvd' := (_root_.Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X
        (k := D.Fq) hIrr (n := 2)).mp (by rw [hP_deg])
      rwa [← Fintype.card_eq_nat_card, card_Fq] at hdvd'
    have hMapDvd : P.map ι ∣ X ^ (D.q ^ 2) - X := by
      simpa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X] using map_dvd ι hdvd
    have hSplitsAll : (X ^ (D.q ^ 2) - X : D.Fq2[X]).Splits := by
      rw [splits_iff_card_roots]
      have hcard := FiniteField.roots_X_pow_card_sub_X (K := D.Fq2)
      rw [card_Fq2] at hcard
      have hnd : (X ^ (D.q ^ 2) - X : D.Fq2[X]).natDegree = D.q ^ 2 := by
        have hq2 : 1 < D.q ^ 2 := one_lt_pow₀ D.one_lt_q (by decide)
        exact FiniteField.X_pow_card_sub_X_natDegree_eq D.Fq2 hq2
      rw [hcard, hnd, ← Finset.card_def, Finset.card_univ, card_Fq2]
    have hNe0All : (X ^ (D.q ^ 2) - X : D.Fq2[X]) ≠ 0 := by
      have hq2 : 1 < D.q ^ 2 := one_lt_pow₀ D.one_lt_q (by decide)
      exact FiniteField.X_pow_card_sub_X_ne_zero D.Fq2 hq2
    have hMapSplits : (P.map ι).Splits := Splits.of_dvd hSplitsAll hNe0All hMapDvd
    have hMapRootsCard : (P.map ι).roots.card = 2 := by
      rw [splits_iff_card_roots.mp hMapSplits, hP_monic.natDegree_map, hP_deg]
    have hMapNodup : (P.map ι).roots.Nodup := nodup_roots hMapSep
    have hFinCard : (P.map ι).roots.toFinset.card = 2 := by
      rw [Multiset.toFinset_card_of_nodup hMapNodup, hMapRootsCard]
    have hREq : R = (P.map ι).roots.toFinset := by
      ext z
      rw [Finset.mem_filter, Multiset.mem_toFinset, mem_roots (hP_monic.map ι).ne_zero]
      refine ⟨fun hz => htr_nrm_root z hz.2, fun hz => ⟨Finset.mem_univ _, ?_⟩⟩
      have hnotrange : z ∉ Set.range ι := by
        rintro ⟨x, rfl⟩
        apply hnoRoot x
        rw [IsRoot.def] at hz ⊢
        have hev : (P.map ι).eval (ι x) = ι (P.eval x) := by
          simp [P]
        rw [hev] at hz
        exact ι.injective (by simpa using hz)
      have hzq_ne : z ^ D.q ≠ z := mt (pow_q_eq_self_iff D z).mp hnotrange
      have hzeval : z ^ 2 + ι u = ι t * z := by
        rw [IsRoot.def] at hz
        have hev : (P.map ι).eval z = z ^ 2 - ι t * z + ι u := by simp [P]
        rw [hev] at hz
        linear_combination hz
      have hzq_eval : (z ^ D.q) ^ 2 - ι t * (z ^ D.q) + ι u = 0 := by
        have hp := congrArg (· ^ D.q) hzeval
        rw [add_pow_q, mul_pow, pow_right_comm, algebraMap_pow_q, algebraMap_pow_q] at hp
        linear_combination hp
      have hMapEq : P.map ι = (X - C z) * (X - C (z ^ D.q)) := by
        have hd1 : X - C z ∣ P.map ι := dvd_iff_isRoot.mpr hz
        rcases hd1 with ⟨Q, hQ⟩
        have hQ_eval : Q.eval (z ^ D.q) = 0 := by
          have := congrArg (eval (z ^ D.q)) hQ
          rw [eval_mul, eval_sub, eval_X, eval_C] at this
          have hP_eval : (P.map ι).eval (z ^ D.q) = 0 := by
            have hev : (P.map ι).eval (z ^ D.q) = (z ^ D.q) ^ 2 - ι t * (z ^ D.q) + ι u := by
              simp [P]
            rw [hev, hzq_eval]
          rw [hP_eval] at this
          exact (mul_eq_zero.mp this.symm).resolve_left (sub_ne_zero.mpr hzq_ne)
        rcases dvd_iff_isRoot.mpr hQ_eval with ⟨R', hR'⟩
        have hP_mul : P.map ι = (X - C z) * (X - C (z ^ D.q)) * R' := by
          rw [hQ, hR']; ring
        have hMon12 : ((X - C z) * (X - C (z ^ D.q))).Monic :=
          (monic_X_sub_C z).mul (monic_X_sub_C (z ^ D.q))
        have hDeg12 : ((X - C z) * (X - C (z ^ D.q))).natDegree = 2 := by
          rw [(monic_X_sub_C z).natDegree_mul (monic_X_sub_C _), natDegree_X_sub_C,
            natDegree_X_sub_C]
        have hR'ne : R' ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hP_mul
          exact (hP_monic.map ι).ne_zero hP_mul
        have hDegR' : R'.natDegree = 0 := by
          have hdg := congrArg natDegree hP_mul
          rw [hP_monic.natDegree_map, hP_deg, hMon12.natDegree_mul' hR'ne, hDeg12] at hdg
          omega
        have hLead : R'.leadingCoeff = 1 := by
          have hlc := congrArg leadingCoeff hP_mul
          rw [(hP_monic.map ι).leadingCoeff, leadingCoeff_mul, hMon12.leadingCoeff, one_mul] at hlc
          exact hlc.symm
        have hR'one : R' = 1 := by
          rw [eq_C_of_natDegree_eq_zero hDegR']
          have := hLead
          rw [eq_C_of_natDegree_eq_zero hDegR', leadingCoeff_C] at this
          rw [this, C_1]
        rw [hP_mul, hR'one, mul_one]
      have hPoly : X ^ 2 - C (ι t) * X + C (ι u) =
          X ^ 2 - C (z + z ^ D.q) * X + C (z * z ^ D.q) := by
        calc X ^ 2 - C (ι t) * X + C (ι u)
          _ = P.map ι := by simp [P]
          _ = (X - C z) * (X - C (z ^ D.q)) := hMapEq
          _ = X ^ 2 - C (z + z ^ D.q) * X + C (z * z ^ D.q) := by
              simp only [C_add, C_mul]; ring
      have hc1 := congrArg (fun q : D.Fq2[X] => q.coeff 1) hPoly
      have hc0 := congrArg (fun q : D.Fq2[X] => q.coeff 0) hPoly
      simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_X, coeff_C] at hc1 hc0
      norm_num at hc1 hc0
      have ht_eq : ι t = z + z ^ D.q := by linear_combination -hc1
      have hu_eq : ι u = z * z ^ D.q := by linear_combination hc0
      rw [← algebraMap_tr] at ht_eq
      rw [← algebraMap_nrm] at hu_eq
      exact ⟨ι.injective ht_eq.symm, ι.injective hu_eq.symm⟩
    rw [hREq, hFinCard]
  · rw [h1]
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
    have hxr : P.IsRoot x := by
      have hxmem : x ∈ P.roots.toFinset := by rw [hx]; exact Finset.mem_singleton_self x
      rw [Multiset.mem_toFinset, mem_roots hP_ne] at hxmem
      exact hxmem
    have hPfac : P = (X - C x) * (X - C (t - x)) := quad_factor_of_isRoot D hxr
    have hyr : P.IsRoot (t - x) := by rw [hPfac]; simp [IsRoot.def]
    have hy_eq : t - x = x := by
      have hymem : t - x ∈ P.roots.toFinset := by
        rw [Multiset.mem_toFinset, mem_roots hP_ne]
        exact hyr
      rw [hx, Finset.mem_singleton] at hymem
      exact hymem
    have ht_eq : t = x + x := by linear_combination hy_eq
    have hu_eq : u = x * x := by
      rw [eval_quad_iff D] at hxr
      linear_combination hxr + x * ht_eq
    have hPsq : P = (X - C x) ^ 2 := by rw [hPfac, hy_eq, sq]
    have hREq : R = {ι x} := by
      ext z
      rw [Finset.mem_filter, Finset.mem_singleton]
      refine ⟨?_, ?_⟩
      · rintro ⟨_, hz⟩
        have hzroot := htr_nrm_root z hz
        rw [hPsq, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
          IsRoot.def, eval_pow, eval_sub, eval_X, eval_C, sq_eq_zero_iff, sub_eq_zero] at hzroot
        exact hzroot
      · rintro rfl
        refine ⟨Finset.mem_univ _, ?_⟩
        constructor
        · apply ι.injective
          rw [algebraMap_tr, algebraMap_pow_q, ht_eq, map_add]
        · apply ι.injective
          rw [algebraMap_nrm, algebraMap_pow_q, hu_eq, map_mul]
    rw [hREq, Finset.card_singleton]
  · have h2 : P.roots.toFinset.card = 2 := by omega
    rw [h2]
    obtain ⟨x, y, hxy, hset⟩ := Finset.card_eq_two.mp h2
    have hxr : P.IsRoot x := by
      have : x ∈ P.roots.toFinset := by rw [hset]; simp
      rwa [Multiset.mem_toFinset, mem_roots hP_ne] at this
    have hyr : P.IsRoot y := by
      have : y ∈ P.roots.toFinset := by rw [hset]; simp
      rwa [Multiset.mem_toFinset, mem_roots hP_ne] at this
    have hPfac : P = (X - C x) * (X - C (t - x)) := quad_factor_of_isRoot D hxr
    have htx_root : P.IsRoot (t - x) := by rw [hPfac]; simp [IsRoot.def]
    have htx_mem : t - x ∈ P.roots.toFinset := by
      rw [Multiset.mem_toFinset, mem_roots hP_ne]
      exact htx_root
    rw [hset, Finset.mem_insert, Finset.mem_singleton] at htx_mem
    have hy_eq : t - x = y := by
      rcases htx_mem with htx | htx
      · exfalso
        have hPsq : P = (X - C x) ^ 2 := by rw [hPfac, htx, sq]
        rw [hPsq, IsRoot.def, eval_pow, eval_sub, eval_X, eval_C, sq_eq_zero_iff, sub_eq_zero] at hyr
        exact hxy hyr.symm
      · exact htx
    have ht_eq : t = x + y := by linear_combination hy_eq
    have hREq : R = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro z hz
      rw [Finset.mem_filter] at hz
      have hzroot := htr_nrm_root z hz.2
      rw [hPfac, hy_eq] at hzroot
      simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
        IsRoot.def, eval_mul, eval_sub, eval_X, eval_C, mul_eq_zero, sub_eq_zero] at hzroot
      rcases hzroot with rfl | rfl
      · have htr := congrArg ι hz.2.1
        rw [algebraMap_tr, algebraMap_pow_q, ht_eq, map_add] at htr
        change ι x + ι x = ι x + ι y at htr
        rw [← map_add, ← map_add] at htr
        exact hxy (add_left_cancel (ι.injective htr))
      · have htr := congrArg ι hz.2.1
        rw [algebraMap_tr, algebraMap_pow_q, ht_eq, map_add] at htr
        change ι y + ι y = ι x + ι y at htr
        rw [← map_add, ← map_add] at htr
        exact hxy (add_right_cancel (ι.injective htr)).symm
    rw [hREq, Finset.card_empty]

end GL2QFT.LemmaA6

open GL2QFT GL2QFT.FieldData GL2QFT.LemmaA6

theorem solution (D : FieldData) (α : D.Lab) :
    D.gaussQ2 (fun z => D.chi α (D.nrm z)) = -(D.gauss α) ^ 2 := by
  let F : D.Fq × D.Fq → ℂ := fun p => D.chi α p.2 * D.psi p.1
  have hsum_all : ∑ s : (D.Fq × D.Fq) ⊕ D.Fq2, F (phi D s) =
      2 * ∑ p : D.Fq × D.Fq, F p := by
    rw [← Finset.sum_fiberwise Finset.univ (phi D) (fun s => F (phi D s))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases p with ⟨t, u⟩
    have hcongr : ∑ s ∈ Finset.univ.filter (fun s => phi D s = (t, u)), F (phi D s) =
        ∑ _s ∈ Finset.univ.filter (fun s => phi D s = (t, u)), F (t, u) := by
      refine Finset.sum_congr rfl fun s hs => ?_
      rw [(Finset.mem_filter.mp hs).2]
    rw [hcongr, Finset.sum_const, card_fiber_eq_two D t u, nsmul_eq_mul]
    norm_num
  have hzero : ∑ p : D.Fq × D.Fq, F p = 0 := by
    rw [Fintype.sum_prod_type]
    dsimp only [F]
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum, sum_psi_eq_zero, mul_zero]
  have hsplit : ∑ s : (D.Fq × D.Fq) ⊕ D.Fq2, F (phi D s) =
      (D.gauss α) ^ 2 + D.gaussQ2 (fun z => D.chi α (D.nrm z)) := by
    rw [Fintype.sum_sum_type]
    have h1 : ∑ p : D.Fq × D.Fq, F (phi D (Sum.inl p)) = (D.gauss α) ^ 2 := by
      dsimp only [phi, F]
      simp only [chi_mul, psi_add]
      rw [Fintype.sum_prod_type]
      simp_rw [show ∀ x y : D.Fq,
          (D.chi α x * D.chi α y) * (D.psi x * D.psi y) =
          (D.chi α x * D.psi x) * (D.chi α y * D.psi y) by intros; ring]
      rw [← Finset.sum_mul_sum, ← gauss_eq_sum, sq]
    have h2 : ∑ z : D.Fq2, F (phi D (Sum.inr z)) = D.gaussQ2 (fun z => D.chi α (D.nrm z)) := by
      dsimp only [phi, F]
      rw [gaussQ2_eq_sum]
    rw [h1, h2]
  rw [hsplit, hzero, mul_zero] at hsum_all
  exact eq_neg_of_add_eq_zero_right hsum_all
