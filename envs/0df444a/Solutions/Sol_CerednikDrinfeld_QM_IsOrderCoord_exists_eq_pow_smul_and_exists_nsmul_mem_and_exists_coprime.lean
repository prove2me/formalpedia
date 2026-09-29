-- Prove2me | solution 1 for CerednikDrinfeld.QM.IsOrderCoord.exists_eq_pow_smul_and_exists_nsmul_mem_and_exists_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/0ee416f7-b5ba-5ceb-b8db-d404ff1c28cc

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_IsOrderCoord_exists_eq_pow_smul_and_exists_nsmul_mem_and_exists_coprime

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

namespace D2aLattice

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {q : ℕ} [Fact q.Prime]

theorem coe_zsmul (z : ℤ) (m : ↥Λ) : ((z • m : ↥Λ) : ℍ[ℚ, a, b]) = (z : ℚ) • (m : ℍ[ℚ, a, b]) := by
  rw [Submodule.coe_smul_of_tower, Int.cast_smul_eq_zsmul]

theorem coe_nsmul (n : ℕ) (m : ↥Λ) : ((n • m : ↥Λ) : ℍ[ℚ, a, b]) = (n : ℚ) • (m : ℍ[ℚ, a, b]) := by
  rw [Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul]

theorem eq_zero_of_zsmul_eq_zero {z : ℤ} (hz : z ≠ 0) {m : ↥Λ} (h : z • m = 0) : m = 0 := by
  have h1 : ((z • m : ↥Λ) : ℍ[ℚ, a, b]) = 0 := by rw [h]; rfl
  rw [coe_zsmul, smul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd (Int.cast_eq_zero.1 h1) hz
  · exact Subtype.ext h1

theorem zsmul_right_injective {z : ℤ} (hz : z ≠ 0) : Function.Injective (fun m : ↥Λ => z • m) := by
  intro m m' h
  have : z • (m - m') = 0 := by
    have h' : z • m = z • m' := h
    rw [smul_sub, h', sub_self]
  exact sub_eq_zero.1 (eq_zero_of_zsmul_eq_zero hz this)

variable (q) in

theorem isUnit_natCast_Zp2 {n : ℕ} (hn : n.Coprime q) : IsUnit (n : Zp2 q) := by
  apply WittVector.isUnit_of_coeff_zero_ne_zero
  rw [← WittVector.constantCoeff_apply, map_natCast]
  intro h
  rw [CharP.cast_eq_zero_iff (GaloisField q 2) q] at h
  have := Nat.Coprime.eq_one_of_dvd hn.symm |>.mt
  exact (Nat.Prime.one_lt (Fact.out : q.Prime)).ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hn) h)

variable (q) in
theorem natCast_q_ne_zero : ((q : ℕ) : Zp2 q) ≠ 0 := by
  intro h
  have h1 : (1 : Zp2 q) * (q : Zp2 q) = 0 := by rw [h, mul_zero]
  exact one_ne_zero (WittVector.eq_zero_of_p_mul_eq_zero _ h1)

variable (q) in
theorem pow_q_ne_zero (j : ℕ) : ((q : ℕ) : Zp2 q) ^ j ≠ 0 := pow_ne_zero _ (natCast_q_ne_zero q)

variable (q) in

theorem natCast_ne_zero_Zp2 {d : ℕ} (hd : d ≠ 0) : (d : Zp2 q) ≠ 0 := by
  obtain ⟨j, n, hn, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd q (Nat.Prime.one_lt (Fact.out : q.Prime)).ne'
  rw [Nat.cast_mul, Nat.cast_pow]
  have hcop : n.Coprime q := (Nat.Prime.coprime_iff_not_dvd (Fact.out : q.Prime)).2 hn |>.symm
  exact mul_ne_zero (pow_q_ne_zero q j) (isUnit_natCast_Zp2 q hcop).ne_zero

variable (q) in

theorem mem_span_pow_of_q_mul_mem {x : Zp2 q} {K : ℕ}
    (h : (q : Zp2 q) * x ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ (K + 1)}) : x ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ K} := by
  rw [Ideal.mem_span_singleton] at h ⊢
  obtain ⟨y, hy⟩ := h
  refine ⟨y, ?_⟩
  have : (q : Zp2 q) * (x - (q : Zp2 q) ^ K * y) = 0 := by
    rw [mul_sub, hy, pow_succ]; ring
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 (natCast_q_ne_zero q)
  · exact sub_eq_zero.1 h0

variable (coord : ↥Λ → Zp2 q × Zp2 q)

noncomputable def red (m : ↥Λ) : GaloisField q 2 × GaloisField q 2 :=
  (WittVector.constantCoeff (coord m).1, WittVector.constantCoeff (coord m).2)

variable {coord}
variable (hcoord : IsOrderCoord Λ q coord)
include hcoord

theorem coord_zero : coord 0 = 0 := by
  have h := hcoord.map_add 0 0
  rw [add_zero] at h
  exact add_eq_left.1 h.symm

theorem coord_nsmul (n : ℕ) (m : ↥Λ) : coord (n • m) = n • coord m := by
  induction n with
  | zero => rw [zero_smul, zero_smul, coord_zero hcoord]
  | succ n ih => rw [succ_nsmul, hcoord.map_add, ih, succ_nsmul]

theorem coord_neg (m : ↥Λ) : coord (-m) = -coord m := by
  have h := hcoord.map_add m (-m)
  rw [add_neg_cancel, coord_zero hcoord] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem coord_zsmul (z : ℤ) (m : ↥Λ) : coord (z • m) = z • coord m := by
  cases z with
  | ofNat n => rw [Int.ofNat_eq_natCast, natCast_zsmul, natCast_zsmul, coord_nsmul hcoord]
  | negSucc n => rw [negSucc_zsmul, negSucc_zsmul, coord_neg hcoord, coord_nsmul hcoord]

theorem coord_sub (m m' : ↥Λ) : coord (m - m') = coord m - coord m' := by
  rw [sub_eq_add_neg, hcoord.map_add, coord_neg hcoord, sub_eq_add_neg]

theorem coord_sum {ι : Type} (s : Finset ι) (f : ι → ↥Λ) : coord (∑ i ∈ s, f i) = ∑ i ∈ s, coord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, coord_zero hcoord]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hcoord.map_add, ih]

theorem red_add (m m' : ↥Λ) : red coord (m + m') = red coord m + red coord m' := by
  simp only [red, hcoord.map_add, Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk]

theorem red_zsmul (z : ℤ) (m : ↥Λ) : red coord (z • m) = (z : ZMod q) • red coord m := by
  rw [red, red, coord_zsmul hcoord, Prod.smul_fst, Prod.smul_snd, zsmul_eq_mul, zsmul_eq_mul, map_mul, map_mul,
    map_intCast]
  ext <;> simp [Algebra.smul_def]

theorem red_sum {ι : Type} (s : Finset ι) (f : ι → ↥Λ) : red coord (∑ i ∈ s, f i) = ∑ i ∈ s, red coord (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    simp only [red, coord_zero hcoord, Prod.fst_zero, Prod.snd_zero, map_zero, Prod.mk_zero_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, red_add hcoord, ih]

theorem red_surjective : Function.Surjective (red coord) := by
  rintro ⟨x, y⟩
  obtain ⟨m, h1, h2⟩ := hcoord.dense 1 (WittVector.teichmuller q x) (WittVector.teichmuller q y)
  rw [pow_one, WittVector.mem_span_p_iff_coeff_zero_eq_zero, ← WittVector.constantCoeff_apply, map_sub,
    WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero,
    sub_eq_zero] at h1 h2
  refine ⟨m, ?_⟩
  simp only [red, WittVector.constantCoeff_apply, h1, h2]

omit hcoord in

theorem red_eq_zero_iff (m : ↥Λ) :
    red coord m = 0 ↔ (coord m).1 ∈ Ideal.span {(q : Zp2 q)} ∧ (coord m).2 ∈ Ideal.span {(q : Zp2 q)} := by
  rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero, WittVector.mem_span_p_iff_coeff_zero_eq_zero, red,
    Prod.mk_eq_zero, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply]

omit hcoord in

theorem exists_primitive_relation {ι : Type} [Fintype ι] (m : ι → ↥Λ) :
    ∀ (N : ℕ) (z : ι → ℤ), (∑ i, (z i).natAbs) ≤ N → (∑ i, z i • m i = 0) → (∃ i, z i ≠ 0) →
      ∃ z' : ι → ℤ, (∑ i, z' i • m i = 0) ∧ (∀ i, z' i = 0 ↔ z i = 0) ∧ ∃ i, ¬ (q : ℤ) ∣ z' i := by
  intro N
  induction N with
  | zero =>
    intro z hN _ hnz
    obtain ⟨i, hi⟩ := hnz
    have : (z i).natAbs = 0 := by
      have := Finset.single_le_sum (fun j _ => Nat.zero_le ((z j).natAbs)) (Finset.mem_univ i)
      omega
    exact absurd (Int.natAbs_eq_zero.1 this) hi
  | succ N ih =>
    intro z hN hrel hnz
    by_cases hdiv : ∀ i, (q : ℤ) ∣ z i
    ·
      choose w hw using hdiv
      have hzw : z = fun i => (q : ℤ) * w i := funext hw
      have hwrel : ∑ i, w i • m i = 0 := by
        have h1 : (q : ℤ) • ∑ i, w i • m i = ∑ i, z i • m i := by
          rw [Finset.smul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hw i, mul_smul]
        rw [hrel] at h1
        exact eq_zero_of_zsmul_eq_zero (by exact_mod_cast (Fact.out : q.Prime).ne_zero) h1
      have hwnz : ∃ i, w i ≠ 0 := by
        obtain ⟨i, hi⟩ := hnz
        exact ⟨i, fun h => hi (by rw [hw i, h, mul_zero])⟩
      have hwN : ∑ i, (w i).natAbs ≤ N := by
        obtain ⟨i₀, hi₀⟩ := hwnz
        have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
        have hle : ∀ i, (w i).natAbs ≤ (z i).natAbs := by
          intro i
          rw [hw i, Int.natAbs_mul, Int.natAbs_natCast]
          exact Nat.le_mul_of_pos_left _ (by omega)
        have hlt : (w i₀).natAbs < (z i₀).natAbs := by
          rw [hw i₀, Int.natAbs_mul, Int.natAbs_natCast]
          have hpos : 0 < (w i₀).natAbs := Int.natAbs_pos.2 hi₀
          nlinarith
        have hsum : ∑ i, (w i).natAbs < ∑ i, (z i).natAbs :=
          Finset.sum_lt_sum (fun i _ => hle i) ⟨i₀, Finset.mem_univ _, hlt⟩
        omega
      obtain ⟨z', h1, h2, h3⟩ := ih w hwN hwrel hwnz
      refine ⟨z', h1, fun i => ?_, h3⟩
      rw [h2 i, hw i]
      constructor
      · intro h; rw [h, mul_zero]
      · intro h
        rcases mul_eq_zero.1 h with h | h
        · exact absurd h (by exact_mod_cast (Fact.out : q.Prime).ne_zero)
        · exact h
    · push Not at hdiv
      exact ⟨z, hrel, fun i => Iff.rfl, hdiv⟩

omit hcoord in

theorem exists_int_relation {ι : Type} [Fintype ι] [DecidableEq ι] (m : ι → ↥Λ) (g : ι → ℚ)
    (hrel : ∑ i, g i • (m i : ℍ[ℚ, a, b]) = 0) :
    ∃ z : ι → ℤ, (∑ i, z i • m i = 0) ∧ ∀ i, z i = 0 ↔ g i = 0 := by

  set D : ℕ := ∏ i, (g i).den with hD
  have hDpos : 0 < D := Finset.prod_pos fun i _ => (g i).den_pos
  let z : ι → ℤ := fun i => (g i).num * ∏ j ∈ Finset.univ.erase i, ((g j).den : ℤ)
  have hz : ∀ i, (z i : ℚ) = g i * D := by
    intro i
    simp only [z, hD]
    rw [← Finset.mul_prod_erase Finset.univ (fun j => (g j).den) (Finset.mem_univ i)]
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  refine ⟨z, ?_, fun i => ?_⟩
  · apply Subtype.ext
    rw [Submodule.coe_sum, Submodule.coe_zero]
    simp_rw [coe_zsmul, hz, mul_comm _ (D : ℚ), mul_smul, ← Finset.smul_sum, hrel, smul_zero]
  · constructor
    · intro h
      have h' : (z i : ℚ) = 0 := by rw [h, Int.cast_zero]
      rw [hz] at h'
      rcases mul_eq_zero.1 h' with h' | h'
      · exact h'
      · exact absurd h' (by exact_mod_cast hDpos.ne')
    · intro h
      simp only [z, Rat.num_eq_zero.2 h, zero_mul]

omit hcoord in

theorem exists_primitive_relation_of_four_lt {ι : Type} [Fintype ι] [DecidableEq ι] (hι : 4 < Fintype.card ι)
    (m : ι → ↥Λ) :
    ∃ z : ι → ℤ, (∑ i, z i • m i = 0) ∧ ∃ i, ¬ (q : ℤ) ∣ z i := by
  have hdep : ¬ LinearIndependent ℚ (fun i => (m i : ℍ[ℚ, a, b])) := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [QuaternionAlgebra.finrank_eq_four] at this
    omega
  obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hdep
  obtain ⟨z, hz, hz0⟩ := exists_int_relation m g hg
  obtain ⟨z', h1, -, h3⟩ := exists_primitive_relation (q := q) m _ z le_rfl hz ⟨i₀, fun h => hi₀ ((hz0 i₀).1 h)⟩
  exact ⟨z', h1, h3⟩

noncomputable def basis4 : Module.Basis (Fin 4) (ZMod q) (GaloisField q 2 × GaloisField q 2) :=
  (Module.finBasis (ZMod q) (GaloisField q 2 × GaloisField q 2)).reindex
    (finCongr (by rw [Module.finrank_prod, GaloisField.finrank q two_ne_zero]))

theorem exists_eq_q_smul (m₀ : ↥Λ) (h0 : red coord m₀ = 0) : ∃ m' : ↥Λ, m₀ = (q : ℤ) • m' := by
  classical

  have hs := red_surjective hcoord
  choose lift hlift using fun i : Fin 4 => hs (basis4 (q := q) i)

  let m : Fin 5 → ↥Λ := Fin.cons m₀ lift
  obtain ⟨z, hz, i₁, hi₁⟩ := exists_primitive_relation_of_four_lt (q := q) (by simp) m

  have hred : ∑ i : Fin 4, ((z i.succ : ℤ) : ZMod q) • basis4 (q := q) i = 0 := by
    have h1 := congrArg (red coord) hz
    rw [red_sum hcoord, Fin.sum_univ_succ] at h1
    simp only [red_zsmul hcoord, m, Fin.cons_zero, Fin.cons_succ, h0, smul_zero, zero_add, hlift] at h1
    rw [h1]
    simp [red, coord_zero hcoord]
  have hzsucc : ∀ i : Fin 4, ((z i.succ : ℤ) : ZMod q) = 0 :=
    fun i => Fintype.linearIndependent_iff.1 (basis4 (q := q)).linearIndependent _ hred i
  have hdvd : ∀ i : Fin 4, (q : ℤ) ∣ z i.succ := fun i => (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (hzsucc i)

  have h0ndvd : ¬ (q : ℤ) ∣ z 0 := by
    intro hd
    apply hi₁
    refine Fin.cases ?_ (fun i => ?_) i₁
    · exact hd
    · exact hdvd i

  choose w hw using hdvd
  have hz0 : z 0 • m₀ = (q : ℤ) • (-∑ i : Fin 4, w i • lift i) := by
    rw [Fin.sum_univ_succ] at hz
    simp only [m, Fin.cons_zero, Fin.cons_succ] at hz
    rw [smul_neg, Finset.smul_sum, eq_neg_iff_add_eq_zero, ← hz]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hw i, mul_smul]

  have hcop : IsCoprime (q : ℤ) (z 0) :=
    (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.1 Fact.out).irreducible).2 h0ndvd
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨u • m₀ + v • (-∑ i : Fin 4, w i • lift i), ?_⟩
  calc m₀ = (1 : ℤ) • m₀ := (one_smul ℤ m₀).symm
    _ = (u * q + v * z 0) • m₀ := by rw [huv]
    _ = u • ((q : ℤ) • m₀) + v • (z 0 • m₀) := by rw [add_smul, mul_smul, mul_smul]
    _ = (q : ℤ) • (u • m₀ + v • (-∑ i : Fin 4, w i • lift i)) := by
        rw [hz0, smul_add, smul_comm u (q : ℤ) m₀, smul_comm v (q : ℤ)]

theorem exists_eq_pow_smul (K : ℕ) : ∀ m : ↥Λ,
    (coord m).1 ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ K} → (coord m).2 ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ K} →
      ∃ m' : ↥Λ, m = (q ^ K : ℕ) • m' := by
  induction K with
  | zero => intro m _ _; exact ⟨m, by rw [pow_zero, one_smul]⟩
  | succ K ih =>
    intro m h1 h2

    have hq1 : (coord m).1 ∈ Ideal.span {(q : Zp2 q)} :=
      Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self _ (Nat.succ_ne_zero K)) h1
    have hq2 : (coord m).2 ∈ Ideal.span {(q : Zp2 q)} :=
      Ideal.span_singleton_le_span_singleton.2 (dvd_pow_self _ (Nat.succ_ne_zero K)) h2
    obtain ⟨m₁, rfl⟩ := exists_eq_q_smul hcoord m ((red_eq_zero_iff m).2 ⟨hq1, hq2⟩)
    rw [coord_zsmul hcoord] at h1 h2
    rw [Prod.smul_fst, zsmul_eq_mul, Int.cast_natCast] at h1
    rw [Prod.smul_snd, zsmul_eq_mul, Int.cast_natCast] at h2
    obtain ⟨m', hm'⟩ := ih m₁ (mem_span_pow_of_q_mul_mem q h1) (mem_span_pow_of_q_mul_mem q h2)
    refine ⟨m', ?_⟩
    rw [hm', ← natCast_zsmul m' (q ^ K), smul_smul, ← natCast_zsmul]
    congr 1
    push_cast
    ring

theorem linearIndependent_lift (lift : Fin 4 → ↥Λ) (hlift : ∀ i, red coord (lift i) = basis4 (q := q) i) :
    LinearIndependent ℚ (fun i => (lift i : ℍ[ℚ, a, b])) := by
  classical
  by_contra hdep
  obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hdep
  obtain ⟨z, hz, hz0⟩ := exists_int_relation lift g hg
  obtain ⟨z', h1, h2, i₁, hi₁⟩ :=
    exists_primitive_relation (q := q) lift _ z le_rfl hz ⟨i₀, fun h => hi₀ ((hz0 i₀).1 h)⟩
  have hred : ∑ i : Fin 4, ((z' i : ℤ) : ZMod q) • basis4 (q := q) i = 0 := by
    have h1' := congrArg (red coord) h1
    rw [red_sum hcoord] at h1'
    simp only [red_zsmul hcoord, hlift] at h1'
    rw [h1']
    simp [red, coord_zero hcoord]
  have := Fintype.linearIndependent_iff.1 (basis4 (q := q)).linearIndependent _ hred i₁
  exact hi₁ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this)

theorem exists_nsmul_mem (h : ℍ[ℚ, a, b]) : ∃ d : ℕ, 0 < d ∧ (d : ℚ) • h ∈ Λ := by
  classical
  have hs := red_surjective hcoord
  choose lift hlift using fun i : Fin 4 => hs (basis4 (q := q) i)
  have hli := linearIndependent_lift hcoord lift hlift
  have hspan : Submodule.span ℚ (Set.range fun i => (lift i : ℍ[ℚ, a, b])) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by rw [QuaternionAlgebra.finrank_eq_four]; simp)
  have hmem : h ∈ Submodule.span ℚ (Set.range fun i => (lift i : ℍ[ℚ, a, b])) := by rw [hspan]; trivial
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 hmem

  set D : ℕ := ∏ i, (g i).den with hD
  have hDpos : 0 < D := Finset.prod_pos fun i _ => (g i).den_pos
  let z : Fin 4 → ℤ := fun i => (g i).num * ∏ j ∈ Finset.univ.erase i, ((g j).den : ℤ)
  have hz : ∀ i, (z i : ℚ) = g i * D := by
    intro i
    simp only [z, hD]
    rw [← Finset.mul_prod_erase Finset.univ (fun j => (g j).den) (Finset.mem_univ i)]
    push_cast
    rw [← mul_assoc, Rat.mul_den_eq_num]
  refine ⟨D, hDpos, ?_⟩
  have : (D : ℚ) • h = ((∑ i, z i • lift i : ↥Λ) : ℍ[ℚ, a, b]) := by
    rw [Submodule.coe_sum, ← hg, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coe_zsmul, hz, smul_smul, mul_comm]
  rw [this]
  exact Submodule.coe_mem _

theorem exists_coprime_nsmul_mul_mem (m m' : ↥Λ) :
    ∃ n : ℕ, n.Coprime q ∧ (n : ℚ) • ((m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b])) ∈ Λ := by
  obtain ⟨d, hd, hdm⟩ := exists_nsmul_mem hcoord ((m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]))
  obtain ⟨j, n, hn, hdn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd.ne' q (Nat.Prime.one_lt (Fact.out : q.Prime)).ne'
  have hcop : n.Coprime q := ((Nat.Prime.coprime_iff_not_dvd (Fact.out : q.Prime)).2 hn).symm
  refine ⟨n, hcop, ?_⟩

  set y : ↥Λ := ⟨(d : ℚ) • ((m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b])), hdm⟩ with hy
  have hprod : ((d • m : ↥Λ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [coe_nsmul, smul_mul_assoc]; exact hdm
  have hyeq : y = ⟨((d • m : ↥Λ) : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]), hprod⟩ := by
    apply Subtype.ext
    simp only [hy, coe_nsmul, smul_mul_assoc]
  have hcy : coord y = d • ((coord m).1 * (coord m').1 + (q : Zp2 q) * ((coord m).2 * WittVector.frobenius (coord m').2),
      (coord m).1 * (coord m').2 + (coord m).2 * WittVector.frobenius (coord m').1) := by
    rw [hyeq, hcoord.map_mul, coord_nsmul hcoord, Prod.smul_fst, Prod.smul_snd, Prod.smul_mk]
    congr 1
    · simp only [nsmul_eq_mul]; ring
    · simp only [nsmul_eq_mul]; ring

  have hmem : ∀ c : Zp2 q, d • c ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ j} := by
    intro c
    rw [nsmul_eq_mul, hdn, Nat.cast_mul, Nat.cast_pow, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have h1 : (coord y).1 ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ j} := by rw [hcy, Prod.smul_fst]; exact hmem _
  have h2 : (coord y).2 ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ j} := by rw [hcy, Prod.smul_snd]; exact hmem _
  obtain ⟨y', hy'⟩ := exists_eq_pow_smul hcoord j y h1 h2

  have key : (n : ℚ) • ((m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b])) = (y' : ℍ[ℚ, a, b]) := by
    have e1 : ((y : ↥Λ) : ℍ[ℚ, a, b]) = ((q ^ j : ℕ) : ℚ) • (y' : ℍ[ℚ, a, b]) := by rw [hy', coe_nsmul]
    rw [hy] at e1
    change (d : ℚ) • ((m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b])) = _ at e1
    rw [hdn, Nat.cast_mul, mul_smul] at e1
    exact smul_right_injective _ (by exact_mod_cast pow_ne_zero j (Fact.out : q.Prime).ne_zero) e1
  rw [key]
  exact Submodule.coe_mem _

theorem coord_eq_of_coe_eq_natCast {d : ℕ} (hd : 0 < d) (x : ↥Λ) (hx : (x : ℍ[ℚ, a, b]) = ((d : ℚ) : ℍ[ℚ, a, b])) :
    coord x = ((d : Zp2 q), 0) := by

  have hxx' : (x : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) = ((d • x : ↥Λ) : ℍ[ℚ, a, b]) := by
    rw [coe_nsmul, hx, QuaternionAlgebra.coe_mul_eq_smul]
  have hxx : (x : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]) ∈ Λ := by rw [hxx']; exact Submodule.coe_mem _
  have hdx : (⟨(x : ℍ[ℚ, a, b]) * (x : ℍ[ℚ, a, b]), hxx⟩ : ↥Λ) = d • x := Subtype.ext hxx'
  have hmul := hcoord.map_mul x x hxx

  have htr : (x : ℍ[ℚ, a, b]) + star (x : ℍ[ℚ, a, b]) = (((2 * d : ℤ)) : ℚ) := by
    rw [hx, QuaternionAlgebra.star_coe, ← QuaternionAlgebra.coe_add]
    congr 1
    push_cast
    ring
  have htrace := hcoord.trace x (2 * d) htr
  rcases hc : coord x with ⟨α, β⟩
  rw [hdx, coord_nsmul hcoord, hc] at hmul
  rw [hc, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat] at htrace
  simp only [Prod.smul_mk, nsmul_eq_mul, Prod.mk.injEq] at hmul
  change α + WittVector.frobenius α = 2 * (d : Zp2 q) at htrace
  obtain ⟨h1, h2⟩ := hmul

  have hβ0 : β = 0 := by
    have e : (d : Zp2 q) * β = β * (α + WittVector.frobenius α) := by rw [h2]; ring
    rw [htrace] at e
    have e' : (d : Zp2 q) * β = 0 := by linear_combination -e
    rcases mul_eq_zero.1 e' with e' | e'
    · exact absurd e' (natCast_ne_zero_Zp2 q hd.ne')
    · exact e'

  rw [hβ0, zero_mul, mul_zero, add_zero] at h1
  have hα' : α = 0 ∨ α = d := by
    have : α * (α - d) = 0 := by linear_combination -h1
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  rcases hα' with h0 | hαd
  · exfalso
    have hc0 : coord x = coord 0 := by rw [coord_zero hcoord, hc, h0, hβ0]; rfl
    have hx0 := hcoord.injective hc0
    have : ((d : ℚ) : ℍ[ℚ, a, b]) = 0 := by rw [← hx, hx0]; rfl
    have : (d : ℚ) = 0 := QuaternionAlgebra.coe_injective this
    exact hd.ne' (by exact_mod_cast this)
  · rw [hαd, hβ0]

theorem exists_coprime_natCast_mem :
    ∃ n : ℕ, n.Coprime q ∧ ∃ h : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ, coord ⟨((n : ℚ) : ℍ[ℚ, a, b]), h⟩ = ((n : Zp2 q), 0) := by
  obtain ⟨d, hd, hdm⟩ := exists_nsmul_mem hcoord (1 : ℍ[ℚ, a, b])
  have hdm' : ((d : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by
    rw [Algebra.smul_def, mul_one] at hdm
    exact hdm
  obtain ⟨j, n, hn, hdn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd.ne' q (Nat.Prime.one_lt (Fact.out : q.Prime)).ne'
  have hcop : n.Coprime q := ((Nat.Prime.coprime_iff_not_dvd (Fact.out : q.Prime)).2 hn).symm
  have hcx := coord_eq_of_coe_eq_natCast hcoord hd ⟨((d : ℚ) : ℍ[ℚ, a, b]), hdm'⟩ rfl
  have h1 : (coord ⟨((d : ℚ) : ℍ[ℚ, a, b]), hdm'⟩).1 ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ j} := by
    rw [hcx]
    change (d : Zp2 q) ∈ _
    rw [hdn, Nat.cast_mul, Nat.cast_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have h2 : (coord ⟨((d : ℚ) : ℍ[ℚ, a, b]), hdm'⟩).2 ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ j} := by
    rw [hcx]
    exact Submodule.zero_mem _
  obtain ⟨y, hy⟩ := exists_eq_pow_smul hcoord j _ h1 h2

  have hyn : (y : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) := by
    have e1 := congrArg Subtype.val hy
    change ((d : ℚ) : ℍ[ℚ, a, b]) = ((((q ^ j : ℕ)) • y : ↥Λ) : ℍ[ℚ, a, b]) at e1
    rw [coe_nsmul] at e1
    have e2 : ((d : ℚ) : ℍ[ℚ, a, b]) = ((q ^ j : ℕ) : ℚ) • ((n : ℚ) : ℍ[ℚ, a, b]) := by
      rw [← QuaternionAlgebra.coe_mul_eq_smul, ← QuaternionAlgebra.coe_mul]
      congr 1
      rw [hdn]
      push_cast
      ring
    rw [e2] at e1
    exact (smul_right_injective _ (by exact_mod_cast pow_ne_zero j (Fact.out : q.Prime).ne_zero) e1).symm
  have hnmem : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ := by rw [← hyn]; exact Submodule.coe_mem _
  refine ⟨n, hcop, hnmem, ?_⟩
  have hn0 : 0 < n := Nat.pos_of_ne_zero fun h => hn (by rw [h]; exact dvd_zero _)
  exact coord_eq_of_coe_eq_natCast hcoord hn0 _ rfl

end D2aLattice

open D2aLattice in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord) :
    (∀ (K : ℕ) (m : ↥Λ), (coord m).1 ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ K} →
        (coord m).2 ∈ Ideal.span {((q : ℕ) : Zp2 q) ^ K} → ∃ m' : ↥Λ, m = (q ^ K : ℕ) • m') ∧
      (∀ h : ℍ[ℚ, a, b], ∃ d : ℕ, 0 < d ∧ (d : ℚ) • h ∈ Λ) ∧
      (∀ m m' : ↥Λ, ∃ n : ℕ, n.Coprime q ∧ (n : ℚ) • ((m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b])) ∈ Λ) ∧
      (∃ n : ℕ, n.Coprime q ∧ ∃ h : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
        coord ⟨((n : ℚ) : ℍ[ℚ, a, b]), h⟩ = ((n : Zp2 q), 0)) :=
  ⟨exists_eq_pow_smul hcoord, exists_nsmul_mem hcoord, exists_coprime_nsmul_mul_mem hcoord,
    exists_coprime_natCast_mem hcoord⟩

end S_CerednikDrinfeld_QM_IsOrderCoord_exists_eq_pow_smul_and_exists_nsmul_mem_and_exists_coprime
end P2MW
export P2MW.S_CerednikDrinfeld_QM_IsOrderCoord_exists_eq_pow_smul_and_exists_nsmul_mem_and_exists_coprime (solution)
