-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_span_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/776d6308-26ac-53a3-97e2-095958454a07

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_MvFormalGroup_EndRingV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_span_eq

set_option autoImplicit false

universe u

noncomputable section

namespace TChar

namespace C1cKit

open WittVector

variable (q : ℕ) [hq : Fact q.Prime]

theorem exists_natCast_of_pow_eq {K : Type*} [Field K] [CharP K q] (a : K) (ha : a ^ q = a) :
    ∃ m : ℕ, (m : K) = a := by
  classical

  set P : Polynomial K := Polynomial.X ^ q - Polynomial.X with hP
  have hq1 : 1 < q := hq.out.one_lt
  have hPdeg : P.natDegree = q := by
    rw [hP, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
      simp [Polynomial.natDegree_X_pow, Polynomial.natDegree_X, hq1]
  have hP0 : P ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at hPdeg; exact hq.out.ne_zero hPdeg.symm
  have hroot : ∀ b : K, b ^ q = b → b ∈ P.roots := by
    intro b hb
    rw [Polynomial.mem_roots hP0, hP, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_X, hb, sub_self]

  let ι : ZMod q →+* K := ZMod.castHom (dvd_refl q) K
  have hι : Function.Injective ι := ι.injective
  let S : Finset K := Finset.univ.image ι
  have hScard : S.card = q := by
    rw [Finset.card_image_of_injective _ hι, Finset.card_univ, ZMod.card]
  have hSsub : S ⊆ P.roots.toFinset := by
    intro b hb
    rw [Multiset.mem_toFinset]
    obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hb
    apply hroot
    rw [← map_pow, ZMod.pow_card]
  have hcard : P.roots.toFinset.card ≤ q := by
    calc P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
      _ = q := hPdeg
  have hSeq : S = P.roots.toFinset :=
    Finset.eq_of_subset_of_card_le hSsub (by rw [hScard]; exact hcard)
  have haS : a ∈ S := by rw [hSeq, Multiset.mem_toFinset]; exact hroot a ha
  obtain ⟨z, -, hz⟩ := Finset.mem_image.mp haS
  refine ⟨z.val, ?_⟩
  rw [← hz]
  show ((z.val : ℕ) : K) = (z.cast : K)
  rw [ZMod.cast_eq_val]

theorem frobenius_frobenius (x : CerednikDrinfeld.Zp2 q) :
    frobenius (frobenius x) = x := by
  classical
  haveI := Fintype.ofFinite (GaloisField q 2)
  ext n
  rw [coeff_frobenius_charP, coeff_frobenius_charP, ← pow_mul]
  have hc : Fintype.card (GaloisField q 2) = q ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card q 2 two_ne_zero
  have := FiniteField.pow_card (x.coeff n)
  rwa [hc, pow_two] at this

theorem exists_eq_natCast_add_mul_of_frobenius_eq (x : CerednikDrinfeld.Zp2 q) (hx : frobenius x = x) :
    ∃ (m : ℕ) (c : CerednikDrinfeld.Zp2 q), x = m + (q : CerednikDrinfeld.Zp2 q) * c := by
  have h0 : (x.coeff 0) ^ q = x.coeff 0 := by
    have := congrArg (fun y => WittVector.coeff y 0) hx
    simpa only [coeff_frobenius_charP] using this
  obtain ⟨m, hm⟩ := exists_natCast_of_pow_eq q (x.coeff 0) h0
  have hy : (x - m) ∈ Ideal.span {(q : CerednikDrinfeld.Zp2 q)} := by
    rw [mem_span_p_iff_coeff_zero_eq_zero, ← constantCoeff_apply, map_sub, map_natCast, constantCoeff_apply,
      ← hm, sub_self]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hy
  exact ⟨m, c, by rw [mul_comm, hc]; ring⟩

theorem exists_pow_ne : ∃ ζ : GaloisField q 2, ζ ^ q ≠ ζ := by
  classical
  by_contra h
  push Not at h
  have hsurj : Function.Surjective (fun m : ZMod q => (m.cast : GaloisField q 2)) := by
    intro a
    obtain ⟨m, hm⟩ := exists_natCast_of_pow_eq q a (h a)
    exact ⟨(m : ZMod q), by show ((m : ZMod q).cast : GaloisField q 2) = a; rw [ZMod.cast_natCast (dvd_refl q), hm]⟩
  haveI := Fintype.ofFinite (GaloisField q 2)
  have hle : Fintype.card (GaloisField q 2) ≤ Fintype.card (ZMod q) := Fintype.card_le_of_surjective _ hsurj
  rw [ZMod.card, ← Nat.card_eq_fintype_card, GaloisField.card q 2 two_ne_zero, pow_two] at hle
  have hq1 : 1 < q := hq.out.one_lt
  nlinarith

theorem exists_isUnit_sub_frobenius :
    ∃ z : CerednikDrinfeld.Zp2 q, IsUnit (z - frobenius z) := by
  obtain ⟨ζ, hζ⟩ := exists_pow_ne q
  refine ⟨teichmuller q ζ, isUnit_of_coeff_zero_ne_zero _ ?_⟩
  rw [← constantCoeff_apply, map_sub, constantCoeff_apply, constantCoeff_apply, teichmuller_coeff_zero,
    coeff_frobenius_charP, teichmuller_coeff_zero]
  exact sub_ne_zero.mpr (Ne.symm hζ)

end C1cKit

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule
open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff coeff
  subst_X constantCoeff_X constantCoeff_subst_eq_zero)

section main

variable {q : ℕ} [Fact q.Prime]
variable {k : Type u} [Field k] [CharP k q] {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)

omit X₀ in

theorem coeff_single_one_mul (f g : MvPowerSeries (Fin 2) k) (hg : constantCoeff g = 0) (j : Fin 2) :
    coeff (Finsupp.single j 1) (f * g) = constantCoeff f * coeff (Finsupp.single j 1) g := by
  classical
  rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single (0, Finsupp.single j 1)]
  · rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  · rintro ⟨a, b⟩ hab hne
    have hsum : a + b = Finsupp.single j 1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    rcases eq_or_ne a 0 with ha | ha
    · exfalso
      apply hne
      subst ha
      rw [zero_add] at hsum
      rw [hsum]
    · have hdeg : a.degree + b.degree = 1 := by
        rw [← map_add, hsum, Finsupp.degree_single]
      have ha' : a.degree ≠ 0 := fun h => ha ((Finsupp.degree_eq_zero_iff a).mp h)
      have hb : b = 0 := (Finsupp.degree_eq_zero_iff b).mp (by omega)
      rw [hb, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hg, mul_zero]
  · simp [Finset.HasAntidiagonal.mem_antidiagonal]

abbrev A (a : Zp2 q) : Matrix (Fin 2) (Fin 2) k := MvFormalGroup.linearPart (X₀.act a)

theorem act_cc (a : Zp2 q) : ∀ i, constantCoeff (X₀.act a i) = 0 := (X₀.isLawHom_act a).1
theorem varpi_cc : ∀ i, constantCoeff (X₀.varpi i) = 0 := X₀.isLawHom_varpi.1

theorem A_one : A X₀ 1 = 1 := by
  show MvFormalGroup.linearPart (X₀.act 1) = 1
  rw [X₀.act_one]
  exact MvFormalGroup.linearPart_X

theorem A_mul (a b : Zp2 q) : A X₀ (a * b) = A X₀ a * A X₀ b := by
  show MvFormalGroup.linearPart (X₀.act (a * b)) = _
  rw [X₀.act_mul]
  exact MvFormalGroup.linearPart_subst (act_cc X₀ b) (X₀.act a)

theorem A_add (a b : Zp2 q) : A X₀ (a + b) = A X₀ a + A X₀ b := by
  show MvFormalGroup.linearPart (X₀.act (a + b)) = _
  rw [X₀.act_add]
  exact MvFormalGroup.linearPart_subst_elim X₀.F (act_cc X₀ a) (act_cc X₀ b)

theorem lam_mul_A (b : Zp2 q) :
    MvFormalGroup.linearPart X₀.varpi * A X₀ b =
      A X₀ (WittVector.frobenius b) * MvFormalGroup.linearPart X₀.varpi := by
  have h1 : MvFormalGroup.linearPart (X₀.varpi.comp (X₀.act b)) =
      MvFormalGroup.linearPart X₀.varpi * A X₀ b := MvFormalGroup.linearPart_subst (act_cc X₀ b) X₀.varpi
  have h2 : MvFormalGroup.linearPart ((X₀.act (WittVector.frobenius b)).comp X₀.varpi) =
      A X₀ (WittVector.frobenius b) * MvFormalGroup.linearPart X₀.varpi :=
    MvFormalGroup.linearPart_subst (varpi_cc X₀) (X₀.act _)
  rw [← h1, ← h2, X₀.varpi_comp_act]

section normal

variable (hI : Ideal.span (Set.range X₀.varpi) =
      Ideal.span ({MvPowerSeries.X 1, MvPowerSeries.X 0 ^ (q ^ 2)} : Set (MvPowerSeries (Fin 2) k)))

include hI

theorem coeff_zero_of_mem {f : MvPowerSeries (Fin 2) k} (hf : f ∈ Ideal.span (Set.range X₀.varpi)) :
    coeff (Finsupp.single 0 1) f = 0 := by
  rw [hI, Ideal.mem_span_pair] at hf
  obtain ⟨a, b, rfl⟩ := hf
  rw [map_add]
  have h1 : coeff (Finsupp.single (0 : Fin 2) 1) (a * MvPowerSeries.X 1) = 0 := by
    have hd : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) ∣ a * MvPowerSeries.X 1 := dvd_mul_left _ _
    exact (MvPowerSeries.X_dvd_iff.mp hd) _ (by simp)
  have h2 : coeff (Finsupp.single (0 : Fin 2) 1) (b * MvPowerSeries.X 0 ^ (q ^ 2)) = 0 := by
    have hd : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) ^ (q ^ 2) ∣ b * MvPowerSeries.X 0 ^ (q ^ 2) :=
      dvd_mul_left _ _
    refine (MvPowerSeries.X_pow_dvd_iff.mp hd) _ ?_
    rw [Finsupp.single_eq_same]
    have hq : 2 ≤ q := (Fact.out : q.Prime).two_le
    calc 1 < 2 := by norm_num
      _ ≤ q := hq
      _ ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  rw [h1, h2, add_zero]

theorem lam_col_zero (i : Fin 2) : MvFormalGroup.linearPart X₀.varpi i 0 = 0 :=
  coeff_zero_of_mem X₀ hI (Ideal.subset_span ⟨i, rfl⟩)

theorem exists_lam_ne_zero : ∃ i : Fin 2, MvFormalGroup.linearPart X₀.varpi i 1 ≠ 0 := by
  classical
  have hX : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) ∈ Ideal.span (Set.range X₀.varpi) := by
    rw [hI]; exact Ideal.subset_span (Set.mem_insert _ _)
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hX
  have h := congrArg (coeff (Finsupp.single (1 : Fin 2) 1)) hc
  rw [MvPowerSeries.coeff_X, map_sum] at h
  by_contra hall
  push Not at hall
  have : ∑ i, coeff (Finsupp.single (1 : Fin 2) 1) (c i * X₀.varpi i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [coeff_single_one_mul _ _ (varpi_cc X₀ i)]
    have : coeff (Finsupp.single (1 : Fin 2) 1) (X₀.varpi i) = MvFormalGroup.linearPart X₀.varpi i 1 := rfl
    rw [this, hall i, mul_zero]
  rw [this, if_pos rfl] at h
  exact one_ne_zero h.symm

theorem A_one_zero (b : Zp2 q) : A X₀ b 1 0 = 0 := by
  obtain ⟨i, hi⟩ := exists_lam_ne_zero X₀ hI
  have h := congrFun (congrFun (lam_mul_A X₀ b) i) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, lam_col_zero X₀ hI, zero_mul, mul_zero, add_zero, zero_add] at h
  exact (mul_eq_zero.mp h).resolve_left hi

def tchar : Zp2 q →+* k where
  toFun a := A X₀ a 0 0
  map_one' := by show A X₀ 1 0 0 = 1; rw [A_one]; rfl
  map_mul' a b := by
    show A X₀ (a * b) 0 0 = A X₀ a 0 0 * A X₀ b 0 0
    rw [A_mul, Matrix.mul_apply, Fin.sum_univ_two, A_one_zero X₀ hI b, mul_zero, add_zero]
  map_zero' := by
    show A X₀ 0 0 0 = 0
    have h := A_add X₀ 0 0
    rw [add_zero] at h
    have : A X₀ 0 = 0 := by
      have h2 : A X₀ 0 + A X₀ 0 = A X₀ 0 + 0 := by rw [add_zero]; exact h.symm
      exact add_left_cancel h2
    rw [this]; rfl
  map_add' a b := by
    show A X₀ (a + b) 0 0 = A X₀ a 0 0 + A X₀ b 0 0
    rw [A_add]; rfl

theorem tchar_apply (a : Zp2 q) : tchar X₀ hI a = coeff (Finsupp.single 0 1) (X₀.act a 0) := rfl

private theorem _root_.TChar.main : ∃ a : Zp2 q, (coeff (Finsupp.single 0 1) (X₀.act a 0)) ^ q ≠ coeff (Finsupp.single 0 1) (X₀.act a 0) := by
  obtain ⟨ω, hω⟩ := C1cKit.exists_pow_ne q
  refine ⟨WittVector.teichmuller q ω, ?_⟩
  rw [← tchar_apply X₀ hI, ← map_pow, ← map_pow]
  intro h
  have hu : IsUnit (WittVector.teichmuller q (ω ^ q) - WittVector.teichmuller q ω) := by
    refine WittVector.isUnit_of_coeff_zero_ne_zero _ ?_
    rw [← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]
    exact sub_ne_zero.mpr hω
  have := hu.map (tchar X₀ hI)
  rw [map_sub, h, sub_self] at this
  exact not_isUnit_zero this

p2m_export "TChar" "main"
end normal

end main

end TChar

end

namespace CountNum

open MvPowerSeries

section

variable {k : Type u} [Field k]

noncomputable def ex (u v : ℕ) : (Fin 2 ⊕ Fin 2) →₀ ℕ :=
  Finsupp.single (Sum.inl (0 : Fin 2)) u + Finsupp.single (Sum.inr (0 : Fin 2)) v

theorem ex_apply_inl (u v : ℕ) : ex u v (Sum.inl 0) = u := by
  simp [ex]

theorem ex_inj_left {u v u' v' : ℕ} (h : ex u v = ex u' v') : u = u' := by
  have := congrArg (fun d : (Fin 2 ⊕ Fin 2) →₀ ℕ => d (Sum.inl 0)) h
  simpa [ex_apply_inl] using this

noncomputable def P (s : ℕ) : MvPowerSeries (Fin 2 ⊕ Fin 2) k :=
  (MvPowerSeries.X (Sum.inl (0 : Fin 2))) ^ s + (MvPowerSeries.X (Sum.inr (0 : Fin 2))) ^ s

theorem coeff_P_pow (s : ℕ) (hs : 0 < s) (N i : ℕ) (hi : i ≤ N) :
    coeff (ex (s * i) (s * (N - i))) ((P (k := k) s) ^ N) = (N.choose i : k) := by
  unfold P
  classical
  rw [add_pow, map_sum]
  have hterm : ∀ l ∈ Finset.range (N + 1),
      coeff (ex (s * i) (s * (N - i)))
        (((MvPowerSeries.X (Sum.inl (0 : Fin 2)) : MvPowerSeries (Fin 2 ⊕ Fin 2) k) ^ s) ^ l *
          ((MvPowerSeries.X (Sum.inr (0 : Fin 2)) : MvPowerSeries (Fin 2 ⊕ Fin 2) k) ^ s) ^ (N - l) *
          (N.choose l : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) =
      if l = i then (N.choose i : k) else 0 := by
    intro l _
    rw [← pow_mul, ← pow_mul, X_pow_eq, X_pow_eq, monomial_mul_monomial, one_mul, ← map_natCast (C (σ := Fin 2 ⊕ Fin 2) (R := k)),
      coeff_mul_C, coeff_monomial]
    by_cases hl : l = i
    · subst hl
      simp [ex]
    · rw [if_neg, if_neg hl, zero_mul]
      intro he
      exact hl (Nat.eq_of_mul_eq_mul_left hs (ex_inj_left he)).symm
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (N + 1)) i, if_pos (Finset.mem_range.mpr (by omega))]

theorem exists_coeff_X_add_X_pow_ne_zero {q : ℕ} [Fact q.Prime] [CharP k q]
    (n : ℕ) (h2 : 2 ≤ n) (hn : n < q ^ 2) (hnq : n ≠ q) :
    ∃ i : ℕ, 0 < i ∧ i < n ∧
      MvPowerSeries.coeff (Finsupp.single (Sum.inl (0 : Fin 2)) i + Finsupp.single (Sum.inr (0 : Fin 2)) (n - i))
        (((MvPowerSeries.X (Sum.inl 0) : MvPowerSeries (Fin 2 ⊕ Fin 2) k) + MvPowerSeries.X (Sum.inr 0)) ^ n) ≠ 0 := by
  have hq : q.Prime := Fact.out
  by_cases hdvd : q ∣ n
  ·
    obtain ⟨m, rfl⟩ := hdvd
    have hm1 : m ≠ 1 := fun h => hnq (by rw [h, mul_one])
    have hm0 : m ≠ 0 := fun h => by rw [h, mul_zero] at h2; omega
    have hmq : m < q := by
      rw [pow_two] at hn
      exact Nat.lt_of_mul_lt_mul_left hn
    have hm2 : 2 ≤ m := by omega
    refine ⟨q, hq.pos, ?_, ?_⟩
    · have : q * 1 < q * m := Nat.mul_lt_mul_of_pos_left (by omega) hq.pos
      simpa using this
    · haveI : CharP (MvPowerSeries (Fin 2 ⊕ Fin 2) k) q :=
        charP_of_injective_ringHom (MvPowerSeries.C_injective (σ := Fin 2 ⊕ Fin 2) (R := k)) q
      rw [pow_mul, add_pow_char]
      have e : (Finsupp.single (Sum.inl (0 : Fin 2)) q + Finsupp.single (Sum.inr (0 : Fin 2)) (q * m - q) :
          (Fin 2 ⊕ Fin 2) →₀ ℕ) = ex (q * 1) (q * (m - 1)) := by
        show _ = Finsupp.single _ _ + Finsupp.single _ _
        rw [mul_one, Nat.mul_sub_one]
      have eP : ((MvPowerSeries.X (Sum.inl 0) : MvPowerSeries (Fin 2 ⊕ Fin 2) k) ^ q + MvPowerSeries.X (Sum.inr 0) ^ q) =
          P (k := k) q := rfl
      rw [e, eP, coeff_P_pow q hq.pos m 1 (by omega), Nat.choose_one_right]
      rw [Ne, CharP.cast_eq_zero_iff k q]
      exact fun h => absurd (Nat.le_of_dvd (by omega) h) (not_le.mpr hmq)
  ·
    refine ⟨1, one_pos, by omega, ?_⟩
    have e : (Finsupp.single (Sum.inl (0 : Fin 2)) 1 + Finsupp.single (Sum.inr (0 : Fin 2)) (n - 1) :
        (Fin 2 ⊕ Fin 2) →₀ ℕ) = ex (1 * 1) (1 * (n - 1)) := by
      show _ = Finsupp.single _ _ + Finsupp.single _ _
      rw [one_mul, one_mul]
    have e2 : ((MvPowerSeries.X (Sum.inl 0) : MvPowerSeries (Fin 2 ⊕ Fin 2) k) + MvPowerSeries.X (Sum.inr 0)) =
        P (k := k) 1 := by
      show _ = MvPowerSeries.X _ ^ 1 + MvPowerSeries.X _ ^ 1
      rw [pow_one, pow_one]
    rw [e, e2, coeff_P_pow 1 one_pos n 1 (by omega), Nat.choose_one_right]
    rw [Ne, CharP.cast_eq_zero_iff k q]
    exact hdvd

end

end CountNum

noncomputable section

open MvPowerSeries

namespace CountSol

section MonIdeal

variable {R : Type*} [CommRing R] {σ : Type*}

theorem coeff_eq_zero_of_mem_spanPow [Fintype σ] (e : σ → ℕ) {f : MvPowerSeries σ R}
    (hf : f ∈ Ideal.span (Set.range fun s : σ => (X s : MvPowerSeries σ R) ^ e s))
    (d : σ →₀ ℕ) (hd : ∀ s, d s < e s) : coeff d f = 0 := by
  classical
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hf
  rw [map_sum]
  refine Finset.sum_eq_zero fun s _ => ?_
  have hdvd : (X s : MvPowerSeries σ R) ^ e s ∣ c s * X s ^ e s := dvd_mul_left _ _
  exact (X_pow_dvd_iff.mp hdvd) d (hd s)

theorem exists_eq_sum_X_pow_mul' [DecidableEq σ] (e : σ → ℕ) (T : Finset σ) :
    ∀ f : MvPowerSeries σ R, (∀ d : σ →₀ ℕ, (∀ s ∈ T, d s < e s) → coeff d f = 0) →
      ∃ r : σ → MvPowerSeries σ R, f = ∑ s ∈ T, X s ^ e s * r s := by
  induction T using Finset.induction_on with
  | empty =>
    intro f hf
    refine ⟨fun _ => 0, ?_⟩
    rw [Finset.sum_empty]
    ext d
    rw [map_zero]
    exact hf d (fun s hs => absurd hs (Finset.notMem_empty s))
  | @insert s T hs ih =>
    intro f hf
    let f₀ : MvPowerSeries σ R := fun d => if d s < e s then coeff d f else 0
    have hf₀ : ∀ d, coeff d f₀ = if d s < e s then coeff d f else 0 := fun d => rfl
    have hdvd : (X s : MvPowerSeries σ R) ^ e s ∣ f - f₀ := by
      rw [X_pow_dvd_iff]
      intro d hd
      rw [map_sub, hf₀, if_pos hd, sub_self]
    obtain ⟨q', hq'⟩ := hdvd
    obtain ⟨r, hr⟩ := ih f₀ (by
      intro d hd
      rw [hf₀]
      split_ifs with hds
      · exact hf d (fun t ht => by
          rcases Finset.mem_insert.mp ht with rfl | ht
          · exact hds
          · exact hd t ht)
      · rfl)
    refine ⟨Function.update r s q', ?_⟩
    rw [Finset.sum_insert hs, Function.update_self]
    have hrest : ∑ t ∈ T, X t ^ e t * Function.update r s q' t = ∑ t ∈ T, X t ^ e t * r t := by
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Function.update_of_ne (ne_of_mem_of_not_mem ht hs)]
    rw [hrest, ← hr, ← hq']
    ring

theorem mem_spanPow_of_coeff_eq_zero [Fintype σ] [DecidableEq σ] (e : σ → ℕ) {f : MvPowerSeries σ R}
    (hf : ∀ d : σ →₀ ℕ, (∀ s, d s < e s) → coeff d f = 0) :
    f ∈ Ideal.span (Set.range fun s : σ => (X s : MvPowerSeries σ R) ^ e s) := by
  obtain ⟨r, hr⟩ := exists_eq_sum_X_pow_mul' e Finset.univ f
    (fun d hd => hf d fun s => hd s (Finset.mem_univ s))
  rw [hr]
  exact Ideal.sum_mem _ fun s _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s, rfl⟩)

theorem subst_mem_span {τ : Type*} [Fintype σ] [DecidableEq σ] (φ : σ → MvPowerSeries τ R)
    (hφ : ∀ s, constantCoeff (φ s) = 0) (g : MvPowerSeries σ R) (hg : constantCoeff g = 0) :
    subst φ g ∈ Ideal.span (Set.range φ) := by
  have hs : HasSubst φ := hasSubst_of_constantCoeff_zero hφ
  obtain ⟨r, hr⟩ := exists_eq_sum_X_pow_mul' (R := R) (fun _ => 1) Finset.univ g (fun d hd => by
    have hd0 : d = 0 := by
      ext s
      have h1 : d s < 1 := hd s (Finset.mem_univ s)
      simp only [Finsupp.coe_zero, Pi.zero_apply]
      omega
    rw [hd0, coeff_zero_eq_constantCoeff_apply]
    exact hg)
  rw [hr, ← coe_substAlgHom hs, map_sum]
  refine Ideal.sum_mem _ fun s _ => ?_
  rw [map_mul, pow_one, coe_substAlgHom hs, subst_X hs s]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨s, rfl⟩)

end MonIdeal

section Degree

variable {R : Type*} [CommRing R] {σ : Type*}

theorem coeff_mul_eq_zero_of_degree (f g : MvPowerSeries σ R) (s t : ℕ)
    (hf : ∀ a : σ →₀ ℕ, a.degree < s → coeff a f = 0) (hg : ∀ b : σ →₀ ℕ, b.degree < t → coeff b g = 0)
    (d : σ →₀ ℕ) (hd : d.degree < s + t) : coeff d (f * g) = 0 := by
  classical
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hsum : p.1 + p.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  have hdeg : p.1.degree + p.2.degree = d.degree := by rw [← map_add, hsum]
  by_cases h1 : p.1.degree < s
  · rw [hf _ h1, zero_mul]
  · have h2 : p.2.degree < t := by omega
    rw [hg _ h2, mul_zero]

theorem coeff_pow_eq_zero_of_degree (f : MvPowerSeries σ R) (s : ℕ)
    (hf : ∀ a : σ →₀ ℕ, a.degree < s → coeff a f = 0) :
    ∀ (m : ℕ) (d : σ →₀ ℕ), d.degree < s * m → coeff d (f ^ m) = 0
  | 0, d, hd => by simp at hd
  | m + 1, d, hd => by
    rw [pow_succ]
    exact coeff_mul_eq_zero_of_degree _ _ (s * m) s (coeff_pow_eq_zero_of_degree f s hf m) hf d
      (by rw [Nat.mul_succ] at hd; exact hd)

theorem coeff_pow_eq_zero_of_constantCoeff (f : MvPowerSeries σ R) (hf : constantCoeff f = 0)
    (m : ℕ) (d : σ →₀ ℕ) (hd : d.degree < m) : coeff d (f ^ m) = 0 := by
  refine coeff_pow_eq_zero_of_degree f 1 (fun a ha => ?_) m d (by simpa using hd)
  have : a = 0 := by
    rw [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at ha
    exact ha
  rw [this, coeff_zero_eq_constantCoeff_apply, hf]

theorem coeff_single_one_mul [DecidableEq σ] (f g : MvPowerSeries σ R) (hg : constantCoeff g = 0) (j : σ) :
    coeff (Finsupp.single j 1) (f * g) = constantCoeff f * coeff (Finsupp.single j 1) g := by
  classical
  rw [coeff_mul, Finset.sum_eq_single (0, Finsupp.single j 1)]
  · rw [coeff_zero_eq_constantCoeff_apply]
  · rintro ⟨a, b⟩ hab hne
    have hsum : a + b = Finsupp.single j 1 := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    rcases eq_or_ne a 0 with ha | ha
    · exfalso
      apply hne
      subst ha
      rw [zero_add] at hsum
      rw [hsum]
    ·
      have hdeg : a.degree + b.degree = 1 := by
        rw [← map_add, hsum, Finsupp.degree_single]
      have ha' : a.degree ≠ 0 := fun h => ha ((Finsupp.degree_eq_zero_iff a).mp h)
      have hb : b = 0 := (Finsupp.degree_eq_zero_iff b).mp (by omega)
      rw [hb, coeff_zero_eq_constantCoeff_apply, hg, mul_zero]
  · simp [Finset.HasAntidiagonal.mem_antidiagonal]

end Degree

section Main

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

variable {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]

def expo (q : ℕ) : Fin 2 → ℕ := ![q ^ 2, 1]

@[scoped simp] theorem expo_zero : expo q 0 = q ^ 2 := rfl
@[scoped simp] theorem expo_one : expo q 1 = 1 := rfl

def expo₂ (q : ℕ) : Fin 2 ⊕ Fin 2 → ℕ := Sum.elim (expo q) (expo q)

variable (q k) in

abbrev J : Ideal (MvPowerSeries (Fin 2) k) :=
  Ideal.span (Set.range fun s : Fin 2 => (X s : MvPowerSeries (Fin 2) k) ^ expo q s)

variable (q k) in

abbrev J₂ : Ideal (MvPowerSeries (Fin 2 ⊕ Fin 2) k) :=
  Ideal.span (Set.range fun t : Fin 2 ⊕ Fin 2 => (X t : MvPowerSeries (Fin 2 ⊕ Fin 2) k) ^ expo₂ q t)

theorem span_pair_eq_J :
    Ideal.span ({X 1, X 0 ^ (q ^ 2)} : Set (MvPowerSeries (Fin 2) k)) = J q k := by
  apply congrArg Ideal.span
  ext f
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨1, by simp [expo]⟩
    · exact ⟨0, by simp [expo]⟩
  · rintro ⟨s, rfl⟩
    fin_cases s <;> simp [expo]

abbrev XL : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k := fun l => X (Sum.inl l)
abbrev XR : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) k := fun l => X (Sum.inr l)

theorem hasSubst_XL : HasSubst (XL (k := k)) := hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
theorem hasSubst_XR : HasSubst (XR (k := k)) := hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _

theorem subst_XL_mem_J₂ {u : MvPowerSeries (Fin 2) k} (hu : u ∈ J q k) : subst XL u ∈ J₂ q k := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hu
  rw [← coe_substAlgHom hasSubst_XL, map_sum]
  refine Ideal.sum_mem _ fun s _ => ?_
  rw [map_mul, map_pow, coe_substAlgHom, subst_X hasSubst_XL]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨Sum.inl s, rfl⟩)

theorem subst_XR_mem_J₂ {u : MvPowerSeries (Fin 2) k} (hu : u ∈ J q k) : subst XR u ∈ J₂ q k := by
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hu
  rw [← coe_substAlgHom hasSubst_XR, map_sum]
  refine Ideal.sum_mem _ fun s _ => ?_
  rw [map_mul, map_pow, coe_substAlgHom, subst_X hasSubst_XR]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨Sum.inr s, rfl⟩)

variable {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
  (hI : Ideal.span (Set.range X₀.varpi) = J q k)

theorem constantCoeff_varpi (i : Fin 2) : constantCoeff (X₀.varpi i) = 0 := X₀.isLawHom_varpi.1 i
theorem constantCoeff_act (a : Zp2 q) (i : Fin 2) : constantCoeff (X₀.act a i) = 0 := (X₀.isLawHom_act a).1 i
theorem hasSubst_varpi : HasSubst X₀.varpi := hasSubst_of_constantCoeff_zero (constantCoeff_varpi X₀)
theorem hasSubst_act (a : Zp2 q) : HasSubst (X₀.act a) := hasSubst_of_constantCoeff_zero (constantCoeff_act X₀ a)

abbrev I₂ : Ideal (MvPowerSeries (Fin 2 ⊕ Fin 2) k) :=
  Ideal.span (Set.range (Sum.elim (fun i => subst XL (X₀.varpi i)) (fun i => subst XR (X₀.varpi i))))

include hI in
theorem I₂_le_J₂ : I₂ X₀ ≤ J₂ q k := by
  apply Ideal.span_le.2
  rintro _ ⟨t, rfl⟩
  rcases t with i | i
  · exact subst_XL_mem_J₂ (hI ▸ Ideal.subset_span ⟨i, rfl⟩)
  · exact subst_XR_mem_J₂ (hI ▸ Ideal.subset_span ⟨i, rfl⟩)

include hI in

theorem subst_law_mem_J₂ {u : MvPowerSeries (Fin 2) k} (hu : u ∈ J q k) :
    subst X₀.F.toPowerSeries u ∈ J₂ q k := by
  rw [← hI] at hu
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hu
  have hF := X₀.F.hasSubst_toPowerSeries
  rw [← coe_substAlgHom hF, map_sum]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [map_mul, coe_substAlgHom]
  refine Ideal.mul_mem_left _ _ (I₂_le_J₂ X₀ hI ?_)
  rw [X₀.isLawHom_varpi.2 i]
  refine subst_mem_span _ (fun t => ?_) _ (X₀.F.constantCoeff_eq_zero i)
  rcases t with l | l
  · exact constantCoeff_subst_eq_zero hasSubst_XL (fun _ => constantCoeff_X _) (constantCoeff_varpi X₀ l)
  · exact constantCoeff_subst_eq_zero hasSubst_XR (fun _ => constantCoeff_X _) (constantCoeff_varpi X₀ l)

include hI in

theorem subst_act_mem_J (a : Zp2 q) {u : MvPowerSeries (Fin 2) k} (hu : u ∈ J q k) :
    subst (X₀.act a) u ∈ J q k := by
  rw [← hI] at hu ⊢
  obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp hu
  rw [← coe_substAlgHom (hasSubst_act X₀ a), map_sum]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [map_mul, coe_substAlgHom]
  refine Ideal.mul_mem_left _ _ ?_
  have h := congrFun (X₀.varpi_comp_act a) i
  change subst (X₀.act a) (X₀.varpi i) = subst X₀.varpi (X₀.act (WittVector.frobenius a) i) at h
  rw [h]
  exact subst_mem_span _ (constantCoeff_varpi X₀) _ (constantCoeff_act X₀ _ i)

abbrev cf (g : MvPowerSeries (Fin 2) k) (j : ℕ) : k := coeff (Finsupp.single 0 j) g

variable (q) in

def red (g : MvPowerSeries (Fin 2) k) : MvPowerSeries (Fin 2) k :=
  ∑ j ∈ Finset.range (q ^ 2), cf g j • (X 0 : MvPowerSeries (Fin 2) k) ^ j

theorem coeff_X0_pow (j : ℕ) (d : Fin 2 →₀ ℕ) :
    coeff d ((X 0 : MvPowerSeries (Fin 2) k) ^ j) = if d = Finsupp.single 0 j then 1 else 0 := by
  rw [X_pow_eq, coeff_monomial]

theorem coeff_red (g : MvPowerSeries (Fin 2) k) (d : Fin 2 →₀ ℕ) :
    coeff d (red q g) = if d 1 = 0 ∧ d 0 < q ^ 2 then coeff d g else 0 := by
  classical
  rw [red, map_sum]
  simp only [map_smul, coeff_X0_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases h : d 1 = 0 ∧ d 0 < q ^ 2
  · rw [if_pos h]
    have hd : d = Finsupp.single 0 (d 0) := by
      ext i; fin_cases i <;> simp [h.1]
    rw [Finset.sum_eq_single_of_mem (d 0) (Finset.mem_range.2 h.2)]
    · rw [if_pos hd]
      show coeff (Finsupp.single 0 (d 0)) g = coeff d g
      rw [← hd]
    · intro j _ hj
      rw [if_neg]
      intro h'
      exact hj (by rw [h', Finsupp.single_eq_same])
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [if_neg]
    intro h'
    apply h
    rw [h']
    exact ⟨by simp, by simpa using Finset.mem_range.1 hj⟩

theorem cf_red (g : MvPowerSeries (Fin 2) k) (j : ℕ) (hj : j < q ^ 2) : cf (red q g) j = cf g j := by
  rw [cf, coeff_red, if_pos ⟨by simp, by simpa⟩]

theorem sub_red_mem_J (g : MvPowerSeries (Fin 2) k) : g - red q g ∈ J q k := by
  classical
  refine mem_spanPow_of_coeff_eq_zero (expo q) fun d hd => ?_
  have h0 := hd 0
  have h1 := hd 1
  simp only [expo_zero, expo_one, Nat.lt_one_iff] at h0 h1
  rw [map_sub, coeff_red, if_pos ⟨h1, h0⟩, sub_self]

theorem red_add (g g' : MvPowerSeries (Fin 2) k) : red q (g + g') = red q g + red q g' := by
  simp only [red, cf, map_add, add_smul, Finset.sum_add_distrib]

theorem red_smul (c : k) (g : MvPowerSeries (Fin 2) k) : red q (c • g) = c • red q g := by
  simp only [red, cf, map_smul, smul_eq_mul, Finset.smul_sum, smul_smul]

theorem mem_J_of_red_eq_zero (g : MvPowerSeries (Fin 2) k) (h : red q g = 0) : g ∈ J q k := by
  have := sub_red_mem_J (q := q) g
  rwa [h, sub_zero] at this

theorem constantCoeff_red (g : MvPowerSeries (Fin 2) k) : constantCoeff (red q g) = constantCoeff g := by
  have hq : 0 < q ^ 2 := pow_pos (Fact.out : q.Prime).pos 2
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_red, if_pos ⟨rfl, hq⟩]

theorem red_eq_zero_of_cf (g : MvPowerSeries (Fin 2) k) (h : ∀ j < q ^ 2, cf g j = 0) : red q g = 0 := by
  rw [red]
  exact Finset.sum_eq_zero fun j hj => by rw [h j (Finset.mem_range.1 hj), zero_smul]

theorem addCoboundary_sub (F : MvFormalGroup 2 k) (g h : MvPowerSeries (Fin 2) k) :
    F.addCoboundary (g - h) = F.addCoboundary g - F.addCoboundary h := by
  show subst F.toPowerSeries (g - h) - subst XL (g - h) - subst XR (g - h)
    = (subst F.toPowerSeries g - subst XL g - subst XR g) - (subst F.toPowerSeries h - subst XL h - subst XR h)
  rw [subst_sub F.hasSubst_toPowerSeries, subst_sub hasSubst_XL, subst_sub hasSubst_XR]
  ring

theorem addCoboundary_add (F : MvFormalGroup 2 k) (g h : MvPowerSeries (Fin 2) k) :
    F.addCoboundary (g + h) = F.addCoboundary g + F.addCoboundary h := by
  show subst F.toPowerSeries (g + h) - subst XL (g + h) - subst XR (g + h)
    = (subst F.toPowerSeries g - subst XL g - subst XR g) + (subst F.toPowerSeries h - subst XL h - subst XR h)
  rw [subst_add F.hasSubst_toPowerSeries, subst_add hasSubst_XL, subst_add hasSubst_XR]
  ring

theorem addCoboundary_smul (F : MvFormalGroup 2 k) (c : k) (g : MvPowerSeries (Fin 2) k) :
    F.addCoboundary (c • g) = c • F.addCoboundary g := by
  show subst F.toPowerSeries (c • g) - subst XL (c • g) - subst XR (c • g)
    = c • (subst F.toPowerSeries g - subst XL g - subst XR g)
  rw [subst_smul F.hasSubst_toPowerSeries, subst_smul hasSubst_XL, subst_smul hasSubst_XR, smul_sub, smul_sub]

theorem smul_mem_ideal {R : Type*} [CommRing R] [Algebra k R] (I : Ideal R) (c : k) {x : R} (hx : x ∈ I) :
    c • x ∈ I := by
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ hx

include hI in

theorem transfer (ψ : Zp2 q → k) (g : MvPowerSeries (Fin 2) k) (hg0 : constantCoeff g = 0)
    (hgP : X₀.F.addCoboundary g ∈ I₂ X₀)
    (hgT : ∀ a, subst (X₀.act a) g - ψ a • g ∈ Ideal.span (Set.range X₀.varpi)) :
    cf g 0 = 0 ∧ X₀.F.addCoboundary (red q g) ∈ J₂ q k ∧
      ∀ a, subst (X₀.act a) (red q g) - ψ a • red q g ∈ J q k := by
  have hu : g - red q g ∈ J q k := sub_red_mem_J g
  have hred : red q g = g - (g - red q g) := by ring
  refine ⟨?_, ?_, ?_⟩
  · show coeff (Finsupp.single 0 0) g = 0
    rw [Finsupp.single_zero, coeff_zero_eq_constantCoeff_apply]
    exact hg0
  · rw [hred, addCoboundary_sub]
    refine Ideal.sub_mem _ (I₂_le_J₂ X₀ hI hgP) ?_
    show subst X₀.F.toPowerSeries (g - red q g) - subst XL (g - red q g) - subst XR (g - red q g) ∈ J₂ q k
    exact Ideal.sub_mem _ (Ideal.sub_mem _ (subst_law_mem_J₂ X₀ hI hu) (subst_XL_mem_J₂ hu)) (subst_XR_mem_J₂ hu)
  · intro a
    have e : subst (X₀.act a) (red q g) - ψ a • red q g
        = (subst (X₀.act a) g - ψ a • g) - (subst (X₀.act a) (g - red q g) - ψ a • (g - red q g)) := by
      rw [subst_sub (hasSubst_act X₀ a), smul_sub]
      ring
    rw [e]
    refine Ideal.sub_mem _ (hI ▸ hgT a) (Ideal.sub_mem _ (subst_act_mem_J X₀ hI a hu) (smul_mem_ideal _ _ hu))

theorem hyp_constantCoeff (c c' : k) {g g' : MvPowerSeries (Fin 2) k}
    (hg0 : constantCoeff g = 0) (hg0' : constantCoeff g' = 0) :
    constantCoeff (c • g + c' • g') = 0 := by
  rw [map_add, MvPowerSeries.constantCoeff_smul, MvPowerSeries.constantCoeff_smul, hg0, hg0', smul_zero, smul_zero,
    add_zero]

theorem hyp_prim (c c' : k) {g g' : MvPowerSeries (Fin 2) k}
    (hgP : X₀.F.addCoboundary g ∈ I₂ X₀) (hgP' : X₀.F.addCoboundary g' ∈ I₂ X₀) :
    X₀.F.addCoboundary (c • g + c' • g') ∈ I₂ X₀ := by
  rw [addCoboundary_add, addCoboundary_smul, addCoboundary_smul]
  exact Ideal.add_mem _ (smul_mem_ideal _ _ hgP) (smul_mem_ideal _ _ hgP')

theorem hyp_type (ψ : Zp2 q → k) (c c' : k) {g g' : MvPowerSeries (Fin 2) k}
    (hgT : ∀ a, subst (X₀.act a) g - ψ a • g ∈ Ideal.span (Set.range X₀.varpi))
    (hgT' : ∀ a, subst (X₀.act a) g' - ψ a • g' ∈ Ideal.span (Set.range X₀.varpi)) (a : Zp2 q) :
    subst (X₀.act a) (c • g + c' • g') - ψ a • (c • g + c' • g') ∈ Ideal.span (Set.range X₀.varpi) := by
  have e : subst (X₀.act a) (c • g + c' • g') - ψ a • (c • g + c' • g')
      = c • (subst (X₀.act a) g - ψ a • g) + c' • (subst (X₀.act a) g' - ψ a • g') := by
    rw [subst_add (hasSubst_act X₀ a), subst_smul (hasSubst_act X₀ a), subst_smul (hasSubst_act X₀ a)]
    module
  rw [e]
  exact Ideal.add_mem _ (smul_mem_ideal _ _ (hgT a)) (smul_mem_ideal _ _ (hgT' a))

end Main

section Compute

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

variable {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]

theorem one_lt_q : 1 < q := (Fact.out : q.Prime).one_lt
theorem q_lt_q_sq : q < q ^ 2 := by
  have := one_lt_q (q := q); nlinarith
theorem one_lt_q_sq : 1 < q ^ 2 := lt_trans one_lt_q q_lt_q_sq

scoped instance charP_mv2 : CharP (MvPowerSeries (Fin 2) k) q :=
  charP_of_injective_algebraMap (C_injective (σ := Fin 2) (R := k)) q
scoped instance charP_mv22 : CharP (MvPowerSeries (Fin 2 ⊕ Fin 2) k) q :=
  charP_of_injective_algebraMap (C_injective (σ := Fin 2 ⊕ Fin 2) (R := k)) q

theorem subst_red {τ : Type*} (φ : Fin 2 → MvPowerSeries τ k) (hφ : HasSubst φ)
    (g : MvPowerSeries (Fin 2) k) :
    subst φ (red q g) = ∑ j ∈ Finset.range (q ^ 2), cf g j • (φ 0) ^ j := by
  rw [red, ← coe_substAlgHom hφ, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coe_substAlgHom, subst_smul hφ, subst_pow hφ, subst_X hφ]

theorem eq_zero_or_single_of_degree_lt_two {σ : Type*} (a : σ →₀ ℕ) (ha : a.degree < 2) :
    a = 0 ∨ ∃ t, a = Finsupp.single t 1 := by
  classical
  by_cases h0 : a = 0
  · exact Or.inl h0
  · right
    obtain ⟨t, ht⟩ : ∃ t, a t ≠ 0 := by
      by_contra h
      exact h0 (Finsupp.ext fun t => by simpa using not_exists.mp h t)
    have hsplit : a.degree = a t + (a.erase t).degree := by
      conv_lhs => rw [← Finsupp.single_add_erase t a]
      rw [map_add, Finsupp.degree_single]
    have hat : a t = 1 := by omega
    have her : (a.erase t).degree = 0 := by omega
    have her0 : a.erase t = 0 := (Finsupp.degree_eq_zero_iff _).mp her
    refine ⟨t, ?_⟩
    rw [← Finsupp.single_add_erase t a, her0, add_zero, hat]

theorem coeff_eq_zero_of_degree_lt_two {σ : Type*} (f : MvPowerSeries σ k) (h0 : constantCoeff f = 0)
    (h1 : ∀ t, coeff (Finsupp.single t 1) f = 0) (a : σ →₀ ℕ) (ha : a.degree < 2) : coeff a f = 0 := by
  rcases eq_zero_or_single_of_degree_lt_two a ha with rfl | ⟨t, rfl⟩
  · rw [coeff_zero_eq_constantCoeff_apply, h0]
  · exact h1 t

theorem coeff_law_sub_eq_zero (F : MvFormalGroup 2 k) (a : Fin 2 ⊕ Fin 2 →₀ ℕ) (ha : a.degree < 2) :
    coeff a (F.toPowerSeries 0 - (X (Sum.inl 0) + X (Sum.inr 0))) = 0 := by
  classical
  refine coeff_eq_zero_of_degree_lt_two _ ?_ (fun t => ?_) a ha
  · rw [map_sub, map_add, F.constantCoeff_eq_zero, constantCoeff_X, constantCoeff_X]; ring
  · rw [map_sub, map_add, coeff_X, coeff_X]
    rcases t with j | j
    · rw [F.coeff_single_inl]
      fin_cases j <;> simp [Finsupp.single_eq_single_iff]
    · rw [F.coeff_single_inr]
      fin_cases j <;> simp [Finsupp.single_eq_single_iff]

abbrev dXY (i j : ℕ) : Fin 2 ⊕ Fin 2 →₀ ℕ :=
  Finsupp.single (Sum.inl 0) i + Finsupp.single (Sum.inr 0) j

theorem degree_dXY (i j : ℕ) : (dXY i j).degree = i + j := by
  rw [dXY, map_add, Finsupp.degree_single, Finsupp.degree_single]

theorem dXY_lt_expo₂ (i j : ℕ) (hi : i < q ^ 2) (hj : j < q ^ 2) (t : Fin 2 ⊕ Fin 2) :
    dXY i j t < expo₂ q t := by
  have hq := one_lt_q_sq (q := q)
  rcases t with l | l <;> fin_cases l <;>
    simp [dXY, expo₂, expo, hi, hj, Finsupp.single_apply]

private theorem _root_.CountSol.exists_coeff_X_add_X_pow_ne_zero (n : ℕ) (h2 : 2 ≤ n) (hn : n < q ^ 2) (hnq : n ≠ q) :
    ∃ i : ℕ, 0 < i ∧ i < n ∧
      MvPowerSeries.coeff (Finsupp.single (Sum.inl (0 : Fin 2)) i + Finsupp.single (Sum.inr (0 : Fin 2)) (n - i))
        (((MvPowerSeries.X (Sum.inl 0) : MvPowerSeries (Fin 2 ⊕ Fin 2) k) + MvPowerSeries.X (Sum.inr 0)) ^ n) ≠ 0 :=
  CountNum.exists_coeff_X_add_X_pow_ne_zero n h2 hn hnq

p2m_export "CountSol" "exists_coeff_X_add_X_pow_ne_zero"

theorem coeff_dXY_law_pow (F : MvFormalGroup 2 k) (n i : ℕ) (hi : i ≤ n) :
    coeff (dXY i (n - i)) (F.toPowerSeries 0 ^ n) =
      coeff (dXY i (n - i)) (((X (Sum.inl 0) : MvPowerSeries (Fin 2 ⊕ Fin 2) k) + X (Sum.inr 0)) ^ n) := by
  classical
  set L : MvPowerSeries (Fin 2 ⊕ Fin 2) k := X (Sum.inl 0) + X (Sum.inr 0) with hL
  set Rm : MvPowerSeries (Fin 2 ⊕ Fin 2) k := F.toPowerSeries 0 - L with hRm
  have hF : F.toPowerSeries 0 = L + Rm := by rw [hRm]; ring
  have hdeg : (dXY i (n - i)).degree = n := by rw [degree_dXY]; omega
  rw [hF, add_pow, map_sum, Finset.sum_eq_single_of_mem n (Finset.mem_range.2 (Nat.lt_succ_self n))]
  · rw [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one]
  · intro m hm hmn
    have hm' : m < n := lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)) hmn
    have hz : coeff (dXY i (n - i)) (L ^ m * Rm ^ (n - m)) = 0 := by
      refine coeff_mul_eq_zero_of_degree (L ^ m) (Rm ^ (n - m)) m (2 * (n - m)) ?_ ?_ _ (by rw [hdeg]; omega)
      · intro a ha
        exact coeff_pow_eq_zero_of_constantCoeff L
          (by rw [hL, map_add, constantCoeff_X, constantCoeff_X, add_zero]) m a ha
      · intro b hb
        exact coeff_pow_eq_zero_of_degree Rm 2 (fun a ha => by rw [hRm, hL]; exact coeff_law_sub_eq_zero F a ha)
          (n - m) b hb
    rw [show L ^ m * Rm ^ (n - m) * ((n.choose m : ℕ) : MvPowerSeries (Fin 2 ⊕ Fin 2) k) =
        (n.choose m) • (L ^ m * Rm ^ (n - m)) from by rw [nsmul_eq_mul, mul_comm], map_nsmul, hz, smul_zero]

variable {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)

theorem addCoboundary_red (g : MvPowerSeries (Fin 2) k) :
    X₀.F.addCoboundary (red q g) = ∑ j ∈ Finset.range (q ^ 2),
      cf g j • ((X₀.F.toPowerSeries 0) ^ j - (X (Sum.inl 0)) ^ j - (X (Sum.inr 0)) ^ j) := by
  rw [MvFormalGroup.addCoboundary, subst_red _ X₀.F.hasSubst_toPowerSeries, subst_red _ hasSubst_XL,
    subst_red _ hasSubst_XR, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_sub, smul_sub]

theorem cf_eq_zero_of_lowest (g : MvPowerSeries (Fin 2) k) (hP : X₀.F.addCoboundary (red q g) ∈ J₂ q k)
    (n : ℕ) (h2 : 2 ≤ n) (hn : n < q ^ 2) (hnq : n ≠ q) (hlow : ∀ j < n, cf g j = 0) : cf g n = 0 := by
  classical
  obtain ⟨i, hi0, hin, hcoef⟩ := exists_coeff_X_add_X_pow_ne_zero (k := k) n h2 hn hnq

  have hz : coeff (dXY i (n - i)) (X₀.F.addCoboundary (red q g)) = 0 :=
    coeff_eq_zero_of_mem_spanPow (expo₂ q) hP _ (dXY_lt_expo₂ i (n - i) (by omega) (by omega))

  rw [addCoboundary_red, map_sum, Finset.sum_eq_single_of_mem n (Finset.mem_range.2 hn)] at hz
  · rw [map_smul, map_sub, map_sub, coeff_dXY_law_pow _ n i hin.le, coeff_X_pow, coeff_X_pow,
      if_neg, if_neg, sub_zero, sub_zero, smul_eq_mul] at hz
    · exact (mul_eq_zero.1 hz).resolve_right hcoef
    · intro h; have := congrArg (fun d => d (Sum.inl 0)) h; simp [dXY] at this; omega
    · intro h; have := congrArg (fun d => d (Sum.inr 0)) h; simp [dXY] at this; omega
  · intro j hj hjn
    rcases lt_or_gt_of_ne hjn with hlt | hgt
    · rw [hlow j hlt, zero_smul, map_zero]
    · rw [map_smul, map_sub, map_sub, coeff_X_pow, coeff_X_pow, if_neg, if_neg, sub_zero, sub_zero,
        coeff_pow_eq_zero_of_constantCoeff _ (X₀.F.constantCoeff_eq_zero 0) j _ (by rw [degree_dXY]; omega),
        smul_zero]
      · intro h; have := congrArg (fun d => d (Sum.inl 0)) h; simp [dXY] at this; omega
      · intro h; have := congrArg (fun d => d (Sum.inr 0)) h; simp [dXY] at this; omega

theorem cf_eq_zero_below_q (g : MvPowerSeries (Fin 2) k) (hP : X₀.F.addCoboundary (red q g) ∈ J₂ q k)
    (h0 : cf g 0 = 0) (h1 : cf g 1 = 0) : ∀ j < q, cf g j = 0 := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · interval_cases j <;> assumption
    · exact cf_eq_zero_of_lowest X₀ g hP j hj2 (lt_trans hj q_lt_q_sq) (ne_of_lt hj) fun l hl => ih l hl (lt_trans hl hj)

theorem red_eq_zero_of_cf_one_q (g : MvPowerSeries (Fin 2) k) (hP : X₀.F.addCoboundary (red q g) ∈ J₂ q k)
    (h0 : cf g 0 = 0) (h1 : cf g 1 = 0) (hq : cf g q = 0) : red q g = 0 := by
  apply red_eq_zero_of_cf
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · interval_cases j <;> assumption
    · by_cases hjq : j = q
      · rw [hjq]; exact hq
      · exact cf_eq_zero_of_lowest X₀ g hP j hj2 hj hjq fun l hl => ih l hl (lt_trans hl hj)

abbrev tc (a : Zp2 q) : k := coeff (Finsupp.single 0 1) (X₀.act a 0)

theorem cf_one_subst_act (a : Zp2 q) (g : MvPowerSeries (Fin 2) k) (h0 : cf g 0 = 0) :
    coeff (Finsupp.single 0 1) (subst (X₀.act a) (red q g)) = cf g 1 * tc X₀ a := by
  classical
  rw [subst_red _ (hasSubst_act X₀ a), map_sum,
    Finset.sum_eq_single_of_mem 1 (Finset.mem_range.2 one_lt_q_sq)]
  · rw [map_smul, pow_one, smul_eq_mul]
  · intro j hj hj1
    rcases Nat.lt_or_gt_of_ne hj1 with hlt | hgt
    · have : j = 0 := by omega
      subst this
      rw [h0, zero_smul, map_zero]
    · rw [map_smul, coeff_pow_eq_zero_of_constantCoeff _ (constantCoeff_act X₀ a 0) j _
        (by rw [Finsupp.degree_single]; exact hgt), smul_zero]

theorem cf_q_subst_act (a : Zp2 q) (g : MvPowerSeries (Fin 2) k) (hlow : ∀ j < q, cf g j = 0) :
    coeff (Finsupp.single 0 q) (subst (X₀.act a) (red q g)) = cf g q * tc X₀ a ^ q := by
  classical
  rw [subst_red _ (hasSubst_act X₀ a), map_sum,
    Finset.sum_eq_single_of_mem q (Finset.mem_range.2 q_lt_q_sq)]
  · rw [map_smul, smul_eq_mul]
    congr 1

    set α := X₀.act a 0 with hα
    set b : k := coeff (Finsupp.single 1 1) α with hb
    set H := α - (tc X₀ a • (X 0 : MvPowerSeries (Fin 2) k) + b • X 1) with hH
    have hHdeg : ∀ e : Fin 2 →₀ ℕ, e.degree < 2 → coeff e H = 0 := by
      refine coeff_eq_zero_of_degree_lt_two H ?_ (fun t => ?_)
      · rw [hH]
        simp only [map_sub, map_add, smul_eq_C_mul, map_mul, constantCoeff_C, constantCoeff_X, mul_zero,
          add_zero, sub_zero]
        rw [hα]
        exact constantCoeff_act X₀ a 0
      · rw [hH, map_sub, map_add, map_smul, map_smul, coeff_X, coeff_X]
        fin_cases t <;> simp [Finsupp.single_eq_single_iff, hb, tc, hα]
    have hαeq : α = (tc X₀ a • (X 0 : MvPowerSeries (Fin 2) k) + b • X 1) + H := by rw [hH]; ring
    rw [hαeq, add_pow_char, add_pow_char, smul_pow, smul_pow, map_add, map_add, map_smul, map_smul,
      coeff_X_pow, coeff_X_pow, if_pos rfl, if_neg, smul_zero, add_zero, smul_eq_mul, mul_one,
      coeff_pow_eq_zero_of_degree H 2 hHdeg q _
        (by rw [Finsupp.degree_single]; have := one_lt_q (q := q); omega), add_zero]
    intro h
    have := (Finsupp.single_eq_single_iff _ _ _ _).1 h
    rcases this with ⟨h01, -⟩ | ⟨hq0, -⟩
    · exact absurd h01 (by decide)
    · exact absurd hq0 (Fact.out : q.Prime).ne_zero
  · intro j hj hjq
    rcases Nat.lt_or_gt_of_ne hjq with hlt | hgt
    · rw [hlow j hlt, zero_smul, map_zero]
    · rw [map_smul, coeff_pow_eq_zero_of_constantCoeff _ (constantCoeff_act X₀ a 0) j _
        (by rw [Finsupp.degree_single]; exact hgt), smul_zero]

end Compute

section Assembly

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

variable {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q]
  {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀) (ψ : Zp2 q → k)

structure RedFacts (g : MvPowerSeries (Fin 2) k) : Prop where
  c0 : cf g 0 = 0
  prim : X₀.F.addCoboundary (red q g) ∈ J₂ q k
  type : ∀ a, subst (X₀.act a) (red q g) - ψ a • red q g ∈ J q k

theorem single_zero_lt_expo (j : ℕ) (hj : j < q ^ 2) (s : Fin 2) : (Finsupp.single (0 : Fin 2) j) s < expo q s := by
  fin_cases s <;> simp [expo, hj]

theorem type_eq_tc {g : MvPowerSeries (Fin 2) k} (hg : RedFacts X₀ ψ g) (h1 : cf g 1 ≠ 0) (a : Zp2 q) :
    ψ a = tc X₀ a := by
  have hz := coeff_eq_zero_of_mem_spanPow (expo q) (hg.type a) (Finsupp.single 0 1)
    (single_zero_lt_expo 1 one_lt_q_sq)
  rw [map_sub, map_smul, cf_one_subst_act X₀ a g hg.c0, smul_eq_mul] at hz
  change cf g 1 * tc X₀ a - ψ a * cf (red q g) 1 = 0 at hz
  rw [cf_red g 1 one_lt_q_sq] at hz
  have : cf g 1 * (tc X₀ a - ψ a) = 0 := by linear_combination hz
  exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left h1)).symm

theorem type_eq_tc_pow {g : MvPowerSeries (Fin 2) k} (hg : RedFacts X₀ ψ g) (h1 : cf g 1 = 0) (hq : cf g q ≠ 0)
    (a : Zp2 q) : ψ a = tc X₀ a ^ q := by
  have hlow := cf_eq_zero_below_q X₀ g hg.prim hg.c0 h1
  have hz := coeff_eq_zero_of_mem_spanPow (expo q) (hg.type a) (Finsupp.single 0 q)
    (single_zero_lt_expo q q_lt_q_sq)
  rw [map_sub, map_smul, cf_q_subst_act X₀ a g hlow, smul_eq_mul] at hz
  change cf g q * tc X₀ a ^ q - ψ a * cf (red q g) q = 0 at hz
  rw [cf_red g q q_lt_q_sq] at hz
  have : cf g q * (tc X₀ a ^ q - ψ a) = 0 := by linear_combination hz
  exact (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hq)).symm

theorem red_eq_zero_of_facts {g : MvPowerSeries (Fin 2) k} (hg : RedFacts X₀ ψ g) (h1 : cf g 1 = 0)
    (hq : cf g q = 0) : red q g = 0 :=
  red_eq_zero_of_cf_one_q X₀ g hg.prim hg.c0 h1 hq

theorem cf_comb (c c' : k) (g g' : MvPowerSeries (Fin 2) k) (j : ℕ) :
    cf (c • g + c' • g') j = c * cf g j + c' * cf g' j := by
  simp only [cf, map_add, map_smul, smul_eq_mul]

private theorem _root_.CountSol.main (hI : Ideal.span (Set.range X₀.varpi) = J q k) (htc : ∃ a, tc X₀ a ^ q ≠ tc X₀ a)
    (g g' : MvPowerSeries (Fin 2) k)
    (hg0 : constantCoeff g = 0) (hg0' : constantCoeff g' = 0)
    (hgP : X₀.F.addCoboundary g ∈ I₂ X₀) (hgP' : X₀.F.addCoboundary g' ∈ I₂ X₀)
    (hgT : ∀ a, subst (X₀.act a) g - ψ a • g ∈ Ideal.span (Set.range X₀.varpi))
    (hgT' : ∀ a, subst (X₀.act a) g' - ψ a • g' ∈ Ideal.span (Set.range X₀.varpi)) :
    ∃ c c' : k, (c ≠ 0 ∨ c' ≠ 0) ∧ c • g + c' • g' ∈ Ideal.span (Set.range X₀.varpi) := by
  obtain ⟨a₁, ha₁⟩ := htc
  have RF : ∀ c c' : k, RedFacts X₀ ψ (c • g + c' • g') := fun c c' => by
    obtain ⟨h0, hP, hT⟩ := transfer X₀ hI ψ _ (hyp_constantCoeff c c' hg0 hg0') (hyp_prim X₀ c c' hgP hgP')
      (hyp_type X₀ ψ c c' hgT hgT')
    exact ⟨h0, hP, hT⟩
  have concl : ∀ c c' : k, (c ≠ 0 ∨ c' ≠ 0) → red q (c • g + c' • g') = 0 →
      ∃ c c' : k, (c ≠ 0 ∨ c' ≠ 0) ∧ c • g + c' • g' ∈ Ideal.span (Set.range X₀.varpi) := by
    intro c c' hcc h
    refine ⟨c, c', hcc, ?_⟩
    rw [hI]
    exact mem_J_of_red_eq_zero _ h
  by_cases hA : ∃ a₀, ψ a₀ ≠ tc X₀ a₀
  ·
    obtain ⟨a₀, ha₀⟩ := hA
    have h1 : ∀ c c' : k, cf (c • g + c' • g') 1 = 0 := fun c c' => by
      by_contra h
      exact ha₀ (type_eq_tc X₀ ψ (RF c c') h a₀)
    by_cases hq' : cf g' q = 0
    · refine concl 0 1 (Or.inr one_ne_zero) (red_eq_zero_of_facts X₀ ψ (RF 0 1) (h1 0 1) ?_)
      rw [cf_comb, zero_mul, one_mul, zero_add, hq']
    · refine concl (cf g' q) (-cf g q) (Or.inl hq') (red_eq_zero_of_facts X₀ ψ (RF _ _) (h1 _ _) ?_)
      rw [cf_comb]; ring
  ·
    simp only [not_exists, ne_eq, not_not] at hA
    have hne : ψ a₁ ≠ tc X₀ a₁ ^ q := by rw [hA a₁]; exact fun h => ha₁ h.symm
    have fin : ∀ c c' : k, cf (c • g + c' • g') 1 = 0 → red q (c • g + c' • g') = 0 := fun c c' h1' => by
      refine red_eq_zero_of_facts X₀ ψ (RF c c') h1' ?_
      by_contra hq
      exact hne (type_eq_tc_pow X₀ ψ (RF c c') h1' hq a₁)
    by_cases h1' : cf g' 1 = 0
    · refine concl 0 1 (Or.inr one_ne_zero) (fin 0 1 ?_)
      rw [cf_comb, zero_mul, one_mul, zero_add, h1']
    · refine concl (cf g' 1) (-cf g 1) (Or.inl h1') (fin _ _ ?_)
      rw [cf_comb]; ring

p2m_export "CountSol" "main"
end Assembly

end CountSol
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_span_eq.CountSol"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_span_eq.CountSol"

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
theorem solution
    {q : ℕ} [Fact q.Prime] {k : Type u} [Field k] [CharP k q] [IsAlgClosed k]
    {j₀ : Zp2 q →+* k} (X₀ : SpecialFormalODModule q j₀)
    (hsmooth : ¬ ((∀ m ∈ X₀.toFormalODModule.lieZero j₀,
        Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0) ∧
      (∀ m ∈ X₀.toFormalODModule.lieOne j₀,
        Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)))
    (hI : Ideal.span (Set.range X₀.varpi) =
      Ideal.span ({MvPowerSeries.X 1, MvPowerSeries.X 0 ^ (q ^ 2)} : Set (MvPowerSeries (Fin 2) k)))
    (ψ : Zp2 q → k) (g g' : MvPowerSeries (Fin 2) k)
    (hg0 : MvPowerSeries.constantCoeff g = 0) (hg0' : MvPowerSeries.constantCoeff g' = 0)
    (hgP : X₀.F.addCoboundary g ∈ Ideal.span (Set.range (Sum.elim
        (fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi i))
        (fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi i)))))
    (hgP' : X₀.F.addCoboundary g' ∈ Ideal.span (Set.range (Sum.elim
        (fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi i))
        (fun i => MvPowerSeries.subst
          (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) k)) (X₀.varpi i)))))
    (hgT : ∀ a : Zp2 q, MvPowerSeries.subst (X₀.act a) g - ψ a • g ∈ Ideal.span (Set.range X₀.varpi))
    (hgT' : ∀ a : Zp2 q, MvPowerSeries.subst (X₀.act a) g' - ψ a • g' ∈ Ideal.span (Set.range X₀.varpi)) :
    ∃ c c' : k, (c ≠ 0 ∨ c' ≠ 0) ∧ c • g + c' • g' ∈ Ideal.span (Set.range X₀.varpi) := by
  have hI' : Ideal.span (Set.range X₀.varpi) = CountSol.J q k := hI.trans CountSol.span_pair_eq_J
  exact CountSol.main X₀ ψ hI'
    (TChar.main X₀ hI)
    g g' hg0 hg0' hgP hgP' hgT hgT'

end S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_span_eq
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_smul_add_smul_mem_span_varpi_of_addCoboundary_mem_of_span_eq (solution)
