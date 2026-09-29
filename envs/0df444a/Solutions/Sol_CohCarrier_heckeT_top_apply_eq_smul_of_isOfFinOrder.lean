-- Prove2me | solution 1 for CohCarrier.heckeT_top_apply_eq_smul_of_isOfFinOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/08886d13-0802-587e-a4b4-5300027e55df

import Mathlib
import Definitions.Def_CohCarrier_Level
import Theorems.Thm_CohCarrier_index_GammaHUpper_of_prime
import Theorems.Thm_CohCarrier_transfer_restrict_eq_pow_index
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_heckeT_top_apply_eq_smul_of_isOfFinOrder

set_option autoImplicit false

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace K3bHeckeTFinOrder

def U (t : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (k + 2) => t * U t (k + 1) - U t k

@[scoped simp] theorem U_zero (t : ℤ) : U t 0 = 0 := rfl
@[scoped simp] theorem U_one (t : ℤ) : U t 1 = 1 := rfl
theorem U_add_two (t : ℤ) (k : ℕ) : U t (k + 2) = t * U t (k + 1) - U t k := rfl

theorem U_growth (t : ℤ) (ht : 2 ≤ |t|) :
    ∀ k : ℕ, (k : ℤ) ≤ |U t k| ∧ |U t k| + 1 ≤ |U t (k + 1)| := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨by push_cast; omega, ?_⟩
    rw [U_add_two]
    have h1 : |t * U t (k + 1)| - |U t k| ≤ |t * U t (k + 1) - U t k| :=
      abs_sub_abs_le_abs_sub _ _
    rw [abs_mul] at h1
    nlinarith [abs_nonneg (U t (k + 1)), abs_nonneg t, abs_nonneg (U t k)]

theorem mul_self_apply (M : SL(2, ℤ)) (i j : Fin 2) :
    M i 0 * M 0 j + M i 1 * M 1 j = (M 0 0 + M 1 1) * M i j - (if i = j then 1 else 0) := by
  have hdet := Matrix.SpecialLinearGroup.det_coe M
  rw [Matrix.det_fin_two] at hdet
  fin_cases i <;> fin_cases j <;> simp <;>
    first | ring1 | linear_combination -hdet

theorem pow_succ_apply (M : SL(2, ℤ)) (k : ℕ) : ∀ i j : Fin 2,
    (M ^ (k + 1)) i j =
      U (M 0 0 + M 1 1) (k + 1) * M i j - U (M 0 0 + M 1 1) k * (if i = j then 1 else 0) := by
  induction k with
  | zero => intro i j; simp
  | succ k ih =>
    intro i j
    have ch := mul_self_apply M i j
    have h0 := ih i 0
    have h1 := ih i 1
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, h0, h1,
      U_add_two]
    fin_cases i <;> fin_cases j <;> simp at ch ⊢ <;>
      linear_combination (U (M 0 0 + M 1 1) (k + 1)) * ch

theorem offDiag_eq_zero_or_natAbs_trace_le_one (M : SL(2, ℤ)) {n : ℕ} (hn : 0 < n)
    (h : M ^ n = 1) : (M 0 1 = 0 ∧ M 1 0 = 0) ∨ (M 0 0 + M 1 1).natAbs ≤ 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  set t := M 0 0 + M 1 1 with ht
  have e01 : U t (k + 1) * M 0 1 = 0 := by
    have := pow_succ_apply M k 0 1
    rw [h] at this
    simpa using this.symm
  have e10 : U t (k + 1) * M 1 0 = 0 := by
    have := pow_succ_apply M k 1 0
    rw [h] at this
    simpa using this.symm
  by_cases hU : U t (k + 1) = 0
  · right
    by_contra hlt
    have h2 : 2 ≤ |t| := by
      rw [Int.abs_eq_natAbs]; omega
    have := (U_growth t h2 (k + 1)).1
    rw [hU, abs_zero] at this
    push_cast at this
    omega
  · left
    exact ⟨(mul_eq_zero.mp e01).resolve_left hU, (mul_eq_zero.mp e10).resolve_left hU⟩

theorem norm_ne_two_mul {t : ℤ} (ht : t = 1 ∨ t = -1) {ℓ : ℕ} (hℓ : ℓ.Prime) (x y a r : ℤ)
    (hr : a ^ 2 - t * a + 1 = ℓ * r) (hQ : x ^ 2 + t * x * y + y ^ 2 = ℓ * 2) : False := by
  have hpar : ∀ u v w : ZMod 2, u ^ 2 + w * u * v + v ^ 2 = 0 → w = 0 ∨ (u = 0 ∧ v = 0) := by
    decide
  have hroot : ∀ u w : ZMod 2, w ≠ 0 → u ^ 2 - w * u + 1 ≠ 0 := by decide
  have ht2 : ((t : ℤ) : ZMod 2) ≠ 0 := by
    rcases ht with rfl | rfl
    · rw [Int.cast_one]; decide
    · rw [Int.cast_neg, Int.cast_one]; decide
  have h20 : ((2 : ℤ) : ZMod 2) = 0 := by decide
  have hc := congrArg (fun z : ℤ => (z : ZMod 2)) hQ
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, h20, mul_zero] at hc
  obtain h | ⟨hx0, hy0⟩ := hpar _ _ _ hc
  · exact ht2 h
  obtain ⟨x', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).mp hx0
  obtain ⟨y', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd y 2).mp hy0
  push_cast at hQ
  have hℓ2 : (ℓ : ℤ) = 2 * (x' ^ 2 + t * x' * y' + y' ^ 2) := by
    rcases ht with rfl | rfl <;> · ring_nf at hQ ⊢; linarith
  have h2dvd : (2 : ℕ) ∣ ℓ := Int.natCast_dvd_natCast.mp ⟨_, hℓ2⟩
  have hℓeq : ℓ = 2 := by
    rcases (Nat.dvd_prime hℓ).mp h2dvd with h | h
    · norm_num at h
    · exact h.symm
  subst hℓeq
  have hc' := congrArg (fun z : ℤ => (z : ZMod 2)) hr
  simp only [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_one, Nat.cast_ofNat,
    h20, zero_mul] at hc'
  exact hroot _ _ ht2 hc'

theorem norm_pos {t : ℤ} (ht : t = 0 ∨ t = 1 ∨ t = -1) {x y : ℤ} (hne : x ≠ 0 ∨ y ≠ 0) :
    0 < x ^ 2 + t * x * y + y ^ 2 := by
  rcases hne with h | h
  · have h0 : 0 < x ^ 2 := by positivity
    rcases ht with rfl | rfl | rfl <;> nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg y]
  · have h0 : 0 < y ^ 2 := by positivity
    rcases ht with rfl | rfl | rfl <;> nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg x]

theorem norm_le {t : ℤ} (ht : t = 0 ∨ t = 1 ∨ t = -1) {x y m : ℤ} (hxl : -m ≤ x) (hxu : x ≤ m)
    (hyl : -m ≤ y) (hyu : y ≤ m) : x ^ 2 + t * x * y + y ^ 2 ≤ 3 * m ^ 2 := by
  have hx2 : x ^ 2 ≤ m ^ 2 := by nlinarith
  have hy2 : y ^ 2 ≤ m ^ 2 := by nlinarith
  rcases ht with rfl | rfl | rfl <;> nlinarith [sq_nonneg (x + y), sq_nonneg (x - y)]

theorem exists_norm_eq_prime {ℓ : ℕ} (hℓ : ℓ.Prime) (t a : ℤ) (ht : t.natAbs ≤ 1)
    (ha : (ℓ : ℤ) ∣ a ^ 2 - t * a + 1) :
    ∃ x y : ℤ, x ^ 2 + t * x * y + y ^ 2 = ℓ ∧ (ℓ : ℤ) ∣ x + a * y := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨r, hr⟩ := ha

  set m : ℕ := Nat.sqrt ℓ with hm
  have hm1 : m * m ≤ ℓ := Nat.sqrt_le ℓ
  have hm2 : ℓ < (m + 1) * (m + 1) := Nat.lt_succ_sqrt ℓ
  have hm3 : m * m < ℓ := by
    refine lt_of_le_of_ne hm1 fun h => ?_
    have hdvd : m ∣ ℓ := ⟨m, h.symm⟩
    rcases (Nat.dvd_prime hℓ).mp hdvd with h1 | h1
    · rw [h1] at h
      exact hℓ.one_lt.ne' (by simpa using h.symm)
    · rw [h1] at h
      have := hℓ.two_le
      nlinarith

  let f : Fin (m + 1) × Fin (m + 1) → ZMod ℓ :=
    fun p => (((p.1 : ℕ) : ℤ) + a * ((p.2 : ℕ) : ℤ) : ℤ)
  have hcard : Fintype.card (ZMod ℓ) < Fintype.card (Fin (m + 1) × Fin (m + 1)) := by
    rw [ZMod.card, Fintype.card_prod, Fintype.card_fin]
    exact hm2
  obtain ⟨p, q, hpq, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  set x : ℤ := ((p.1 : ℕ) : ℤ) - ((q.1 : ℕ) : ℤ) with hx
  set y : ℤ := ((p.2 : ℕ) : ℤ) - ((q.2 : ℕ) : ℤ) with hy
  have hp1 := p.1.is_lt
  have hp2 := p.2.is_lt
  have hq1 := q.1.is_lt
  have hq2 := q.2.is_lt
  have hxl : -(m : ℤ) ≤ x := by omega
  have hxu : x ≤ m := by omega
  have hyl : -(m : ℤ) ≤ y := by omega
  have hyu : y ≤ m := by omega
  have hne : x ≠ 0 ∨ y ≠ 0 := by
    rcases eq_or_ne x 0 with hx0 | hx0
    · refine Or.inr fun hy0 => hpq ?_
      have h1 : (p.1 : ℕ) = q.1 := by omega
      have h2 : (p.2 : ℕ) = q.2 := by omega
      exact Prod.ext (Fin.ext h1) (Fin.ext h2)
    · exact Or.inl hx0
  have hdvd : (ℓ : ℤ) ∣ x + a * y := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have : ((x + a * y : ℤ) : ZMod ℓ) = f p - f q := by
      simp only [f, hx, hy]
      push_cast
      ring
    rw [this, hf, sub_self]
  obtain ⟨s, hs⟩ := hdvd
  refine ⟨x, y, ?_, ⟨s, hs⟩⟩

  set k : ℤ := s * (ℓ * s - 2 * a * y + t * y) + y ^ 2 * r with hk
  have hQk : x ^ 2 + t * x * y + y ^ 2 = ℓ * k := by
    rw [hk]
    linear_combination (x + ℓ * s - a * y + t * y) * hs + y ^ 2 * hr

  have hx2 : x ^ 2 ≤ (m : ℤ) ^ 2 := by nlinarith only [hxl, hxu]
  have hy2 : y ^ 2 ≤ (m : ℤ) ^ 2 := by nlinarith only [hyl, hyu]
  have hm3' : (m : ℤ) ^ 2 < ℓ := by
    have : ((m * m : ℕ) : ℤ) < ℓ := by exact_mod_cast hm3
    push_cast at this
    nlinarith only [this]
  have hℓpos : (0 : ℤ) < ℓ := by exact_mod_cast hℓ.pos
  have ht3 : t = 0 ∨ t = 1 ∨ t = -1 := by omega
  have hQpos : 0 < x ^ 2 + t * x * y + y ^ 2 := norm_pos ht3 hne
  have hQle : x ^ 2 + t * x * y + y ^ 2 ≤ 3 * (m : ℤ) ^ 2 := norm_le ht3 hxl hxu hyl hyu
  clear_value x y k
  have hk1 : 0 < k := by
    by_contra h
    rw [not_lt] at h
    nlinarith only [hQpos, hQk, hℓpos, h]
  have hk3 : k < 3 := by
    by_contra h
    rw [not_lt] at h
    nlinarith only [hQle, hm3', hQk, hℓpos, h]
  have hk12 : k = 1 ∨ k = 2 := by omega
  rcases hk12 with h1 | h2
  · rw [hQk, h1, mul_one]
  · exfalso
    rw [h2] at hQk
    rcases ht3 with rfl | rfl | rfl
    ·
      nlinarith only [hQk, hx2, hy2, hm3']
    · exact norm_ne_two_mul (Or.inl rfl) hℓ x y a r hr hQk
    · exact norm_ne_two_mul (Or.inr rfl) hℓ x y a r hr hQk

theorem inv_mul_mul_pow {G : Type*} [Group G] (a b : G) (n : ℕ) :
    (a⁻¹ * b * a) ^ n = a⁻¹ * b ^ n * a := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, pow_succ]; group

theorem exists_mul_eq_mul_conjUpperMat {ℓ : ℕ} (hℓ : ℓ.Prime) (N : ℤ) (δ : SL(2, ℤ))
    (hb : (ℓ : ℤ) ∣ δ 0 1) (hc : N ∣ δ 1 0) (ht : (δ 0 0 + δ 1 1).natAbs ≤ 1) :
    ∃ u : SL(2, ℤ), N ∣ u 1 0 ∧ δ * u = u * CohCarrier.conjUpperMat ℓ δ hb := by
  have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  obtain ⟨b', hb'⟩ := hb
  obtain ⟨c', hc'⟩ := hc
  have hdet := Matrix.SpecialLinearGroup.det_coe δ
  rw [Matrix.det_fin_two] at hdet

  have ha : (ℓ : ℤ) ∣ δ 0 0 ^ 2 - (δ 0 0 + δ 1 1) * δ 0 0 + 1 :=
    ⟨-(b' * δ 1 0), by linear_combination (-1 : ℤ) * hdet + (-(δ 1 0)) * hb'⟩
  obtain ⟨x, y, hQ, s, hs⟩ := exists_norm_eq_prime hℓ (δ 0 0 + δ 1 1) (δ 0 0) ht ha
  have hdiv : δ 0 1 / (ℓ : ℤ) = b' := by rw [hb']; exact Int.mul_ediv_cancel_left b' hℓ0
  have hdet' : (x + y * δ 1 1) * s - (-(y * b')) * (-(y * δ 1 0)) = 1 := by
    apply mul_left_cancel₀ hℓ0
    linear_combination hQ + y ^ 2 * hdet - (x + y * δ 1 1) * hs + y ^ 2 * δ 1 0 * hb'
  refine ⟨⟨!![x + y * δ 1 1, -(y * b'); -(y * δ 1 0), s], by rw [Matrix.det_fin_two_of]; exact hdet'⟩,
    ?_, ?_⟩
  · show N ∣ -(y * δ 1 0)
    rw [hc']
    exact ⟨-(y * c'), by ring⟩
  · apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [CohCarrier.conjUpperMat, Matrix.mul_apply, Fin.sum_univ_two, hdiv]
    · linear_combination (-(y * δ 1 0)) * hb'
    · linear_combination (-b') * hs + s * hb'
    · linear_combination (δ 1 0) * hs
    · ring

theorem apply_conjL_eq_of_pow_eq_one {N : ℕ} [NeZero N] {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime)
    {A : Type*} [AddCommGroup A] (φ : CohCarrier.H1 N ⊤ A)
    (k : ↥(CohCarrier.GammaHUpper N ⊤ ℓ)) {n : ℕ} (hn : 0 < n)
    (hk : (((k : ↥(CohCarrier.GammaH N ⊤)) : SL(2, ℤ))) ^ n = 1) :
    φ (Additive.ofMul (CohCarrier.conjL N ⊤ ℓ k)) =
      φ (Additive.ofMul (k : ↥(CohCarrier.GammaH N ⊤))) := by
  set δ : SL(2, ℤ) := ((k : ↥(CohCarrier.GammaH N ⊤)) : SL(2, ℤ)) with hδ
  have hb : (ℓ : ℤ) ∣ δ 0 1 := CohCarrier.dvd_of_mem_GammaHUpper N ⊤ ℓ k
  have hδ0 : δ ∈ Gamma0 N := CohCarrier.GammaH_le_Gamma0 ⊤ (k : ↥(CohCarrier.GammaH N ⊤)).2
  have hc : (N : ℤ) ∣ δ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hδ0)
  have hcoe : ((CohCarrier.conjL N ⊤ ℓ k : ↥(CohCarrier.GammaH N ⊤)) : SL(2, ℤ)) =
      CohCarrier.conjUpperMat ℓ δ hb := rfl
  rcases offDiag_eq_zero_or_natAbs_trace_le_one δ hn hk with ⟨h01, h10⟩ | ht
  ·
    have h01' : (((k : ↥(CohCarrier.GammaH N ⊤)) : SL(2, ℤ))) 0 1 = 0 := h01
    have h10' : (((k : ↥(CohCarrier.GammaH N ⊤)) : SL(2, ℤ))) 1 0 = 0 := h10
    have heq : CohCarrier.conjL N ⊤ ℓ k = (k : ↥(CohCarrier.GammaH N ⊤)) := by
      apply Subtype.ext
      rw [hcoe]
      apply Matrix.SpecialLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [CohCarrier.conjUpperMat, h01', h10', hδ]
    rw [heq]
  · obtain ⟨u, hu, hconj⟩ := exists_mul_eq_mul_conjUpperMat hℓ N δ hb hc ht
    have hu0 : u ∈ Gamma0 N := by
      rw [Gamma0_mem]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hu
    let Uu : ↥(CohCarrier.GammaH N ⊤) := ⟨u, by rw [CohCarrier.GammaH_top]; exact hu0⟩
    have heq : CohCarrier.conjL N ⊤ ℓ k = Uu⁻¹ * (k : ↥(CohCarrier.GammaH N ⊤)) * Uu := by
      apply Subtype.ext
      rw [hcoe]
      change CohCarrier.conjUpperMat ℓ δ hb = u⁻¹ * δ * u
      rw [mul_assoc, hconj, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [heq, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
    abel

end K3bHeckeTFinOrder
p2m_reactivate "P2MW.S_CohCarrier_heckeT_top_apply_eq_smul_of_isOfFinOrder.K3bHeckeTFinOrder"

open K3bHeckeTFinOrder in
theorem solution
    (N : ℕ) [NeZero N] (A : Type) [AddCommGroup A] (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (φ : CohCarrier.H1 N ⊤ A) (γ : ↥(CohCarrier.GammaH N ⊤)) (hγ : IsOfFinOrder γ) :
    (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; CohCarrier.heckeT N ⊤ ℓ A φ (Additive.ofMul γ)) =
      (ℓ + 1) • φ (Additive.ofMul γ) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  classical

  have hFR : ∀ k : ↥(CohCarrier.GammaHUpper N ⊤ ℓ), ∀ n : ℕ, 0 < n →
      (k : ↥(CohCarrier.GammaH N ⊤)) ^ n = 1 →
        ((AddMonoidHom.toMultiplicativeRight φ).comp (CohCarrier.conjL N ⊤ ℓ)) k =
          ((AddMonoidHom.toMultiplicativeRight φ).domRestrict (CohCarrier.GammaHUpper N ⊤ ℓ)) k := by
    intro k n hn hkn
    have hk' : (((k : ↥(CohCarrier.GammaH N ⊤)) : SL(2, ℤ))) ^ n = 1 := by
      rw [← Subgroup.coe_pow, hkn, Subgroup.coe_one]
    have := apply_conjL_eq_of_pow_eq_one hℓ φ k hn hk'
    change Multiplicative.ofAdd (φ (Additive.ofMul (CohCarrier.conjL N ⊤ ℓ k))) =
      Multiplicative.ofAdd (φ (Additive.ofMul (k : ↥(CohCarrier.GammaH N ⊤))))
    rw [this]

  have hψ : MonoidHom.transfer
      ((AddMonoidHom.toMultiplicativeRight φ).comp (CohCarrier.conjL N ⊤ ℓ) /
        (AddMonoidHom.toMultiplicativeRight φ).domRestrict (CohCarrier.GammaHUpper N ⊤ ℓ)) γ = 1 := by
    haveI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers γ)
        (↥(CohCarrier.GammaH N ⊤) ⧸ CohCarrier.GammaHUpper N ⊤ ℓ))) := Fintype.ofFinite _
    rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
    refine Finset.prod_eq_one fun q _ => ?_
    obtain ⟨n, hn, hγn⟩ := hγ.exists_pow_eq_one
    rw [MonoidHom.div_apply, div_eq_one]
    refine hFR _ n hn ?_
    show (q.out.out⁻¹ * γ ^ Function.minimalPeriod (γ • ·) q.out * q.out.out) ^ n = 1
    rw [inv_mul_mul_pow, pow_right_comm, hγn, one_pow, mul_one, inv_mul_cancel]

  change Multiplicative.toAdd (MonoidHom.transfer
    ((AddMonoidHom.toMultiplicativeRight φ).comp (CohCarrier.conjL N ⊤ ℓ)) γ) = _
  rw [← div_mul_cancel ((AddMonoidHom.toMultiplicativeRight φ).comp (CohCarrier.conjL N ⊤ ℓ))
      ((AddMonoidHom.toMultiplicativeRight φ).domRestrict (CohCarrier.GammaHUpper N ⊤ ℓ)),
    CohCarrier.transfer_mul, MonoidHom.mul_apply, hψ, one_mul,
    CohCarrier.transfer_restrict_eq_pow_index, CohCarrier.index_GammaHUpper_of_prime N ⊤ ℓ hℓ hℓN,
    MonoidHom.pow_apply, toAdd_pow]
  rfl

end S_CohCarrier_heckeT_top_apply_eq_smul_of_isOfFinOrder
end P2MW
export P2MW.S_CohCarrier_heckeT_top_apply_eq_smul_of_isOfFinOrder (solution)
