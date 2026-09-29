-- Prove2me | solution 1 for CuspidalType.charpoly_scalarElem_mul_unipotent_eq_cyclotomic_of_cuspidal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/7f697ba1-ee8c-51e6-b6cd-03a30dc4c95f

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_charpoly_scalarElem_mul_unipotent_eq_cyclotomic_of_cuspidal

set_option autoImplicit false

p2m_open "Polynomial CuspidalType P2MW.S_CuspidalType_charpoly_scalarElem_mul_unipotent_eq_cyclotomic_of_cuspidal.CuspidalType"

namespace CuspidalType
p2m_export "CuspidalType" "GL2 unipotent scalarElem diagElem diagElem_val unipotent_val"
namespace UnipCharpoly
p2m_open "CuspidalType"

variable {q : ℕ} [Fact q.Prime]

theorem unipotent_add (s t : ZMod q) :
    unipotent q (s + t) = unipotent q s * unipotent q t := by
  apply Units.ext
  ext i j
  simp only [Units.val_mul, unipotent_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem unipotent_zero : unipotent q 0 = 1 := by
  apply Units.ext
  ext i j
  simp only [unipotent_val, Units.val_one]
  fin_cases i <;> fin_cases j <;> simp

theorem unipotent_nsmul (n : ℕ) (t : ZMod q) :
    unipotent q (n • t) = unipotent q t ^ n := by
  induction n with
  | zero => rw [zero_smul, unipotent_zero, pow_zero]
  | succ n ih => rw [add_smul, one_smul, unipotent_add, ih, pow_succ]

theorem unipotent_pow_eq_one (t : ZMod q) : unipotent q t ^ q = 1 := by
  rw [← unipotent_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, unipotent_zero]

theorem diagElem_mul_unipotent (a : (ZMod q)ˣ) (t : ZMod q) :
    diagElem q a * unipotent q t = unipotent q ((a : ZMod q) * t) * diagElem q a := by
  apply Units.ext
  ext i j
  simp only [Units.val_mul, unipotent_val, diagElem_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem unipotent_units_mul (a : (ZMod q)ˣ) (t : ZMod q) :
    unipotent q ((a : ZMod q) * t) = diagElem q a * unipotent q t * (diagElem q a)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  exact (diagElem_mul_unipotent a t).symm

theorem aeval_conj {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    (e e' x : A) (he : e * e' = 1) (he' : e' * e = 1) (p : R[X]) :
    aeval (e * x * e') p = e * aeval x p * e' := by
  have hpow : ∀ n : ℕ, (e * x * e') ^ n = e * x ^ n * e' := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, mul_one, he]
    | succ n ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [mul_assoc]
      rw [← mul_assoc e' e, he', one_mul]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, add_mul]
  | monomial n c =>
    simp only [aeval_monomial, hpow]
    simp only [← mul_assoc]
    rw [Algebra.commutes c e]

end CuspidalType.UnipCharpoly

open CuspidalType.UnipCharpoly in

theorem solution
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K (GL2 q) V)
    (hfin : Module.finrank K V = q - 1)
    (hcusp : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0)
    (hcent : ∀ c : (ZMod q)ˣ, ρ (scalarElem q c) = LinearMap.id)
    (z : (ZMod q)ˣ) (t : ZMod q) (ht : t ≠ 0) :
    LinearMap.charpoly (ρ (scalarElem q z * unipotent q t)) = Polynomial.cyclotomic q K := by
  classical
  have hq : q.Prime := Fact.out
  haveI : NeZero q := ⟨hq.ne_zero⟩

  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (R := K) (by rw [hfin]; have := hq.two_le; omega)

  rw [map_mul, hcent, Module.End.mul_eq_comp, LinearMap.id_comp]
  set A : Module.End K V := ρ (unipotent q t) with hA

  have hAq : A ^ q = 1 := by rw [hA, ← map_pow, unipotent_pow_eq_one, map_one]

  have hfix : ∀ v : V, A v = v → v = 0 := by
    intro v hv
    apply hcusp v
    intro s
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, s = n • t :=
      ⟨(s * t⁻¹).val, by rw [nsmul_eq_mul, ZMod.natCast_zmod_val, inv_mul_cancel_right₀ ht]⟩
    rw [unipotent_nsmul, map_pow]
    induction n with
    | zero => rw [pow_zero, Module.End.one_apply]
    | succ n ih => rw [pow_succ, Module.End.mul_apply, hv, ih]

  have hΦA : aeval A (cyclotomic q K) = 0 := by
    have hmul : (X - 1 : K[X]) * cyclotomic q K = X ^ q - 1 := by
      rw [mul_comm, cyclotomic_prime_mul_X_sub_one]
    have h1 : (A - 1) * aeval A (cyclotomic q K) = 0 := by
      have := congrArg (aeval A) hmul
      rwa [map_mul, map_sub, aeval_X, map_one, map_sub, map_pow, aeval_X, map_one, hAq,
        sub_self] at this
    ext v
    have hv := congrArg (fun f : Module.End K V => f v) h1
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.zero_apply, sub_eq_zero] at hv
    rw [LinearMap.zero_apply]
    exact hfix _ hv

  have hAint : IsIntegral K A := Algebra.IsIntegral.isIntegral A
  set g : K[X] := minpoly K A with hg
  have hgΦ : g ∣ cyclotomic q K := minpoly.dvd K A hΦA
  have hgmon : g.Monic := minpoly.monic hAint

  have hexp : ∀ a : (ZMod q)ˣ, g ∣ expand K (a : ZMod q).val g := by
    intro a
    apply minpoly.dvd
    rw [expand_aeval]
    have hconj : A ^ (a : ZMod q).val = ρ (diagElem q a) * A * ρ (diagElem q a)⁻¹ := by
      rw [hA, ← map_pow, ← unipotent_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val,
        unipotent_units_mul a t, map_mul, map_mul]
    rw [hconj, aeval_conj _ _ _ (by rw [← map_mul, mul_inv_cancel, map_one])
      (by rw [← map_mul, inv_mul_cancel, map_one]), hg, minpoly.aeval, mul_zero, zero_mul]

  have hdeg : q - 1 ≤ g.natDegree := by
    let L := AlgebraicClosure K
    set g' : L[X] := g.map (algebraMap K L) with hg'
    have hg'mon : g'.Monic := hgmon.map _
    have hg'0 : g' ≠ 0 := hg'mon.ne_zero
    obtain ⟨ζ, hζ⟩ : ∃ ζ, g'.IsRoot ζ := IsAlgClosed.exists_root g' (by
      rw [hg', degree_map]; exact (minpoly.degree_pos hAint).ne')

    have hζ1 : ζ ≠ 1 := by
      rintro rfl
      have h1 : g.IsRoot 1 := by
        rw [← isRoot_map_iff (algebraMap K L).injective, map_one]
        exact hζ
      obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_of_isRoot h1).exists_hasEigenvector
      exact hv.2 (hfix v (by rw [hv.apply_eq_smul, one_smul]))

    have hζq : ζ ^ q = 1 := by
      have hX : (X ^ q - 1 : L[X]).IsRoot ζ := by
        apply hζ.dvd
        calc g' ∣ (cyclotomic q K).map (algebraMap K L) := Polynomial.map_dvd _ hgΦ
          _ ∣ (X ^ q - 1 : K[X]).map (algebraMap K L) :=
            Polynomial.map_dvd _ (cyclotomic.dvd_X_pow_sub_one q K)
          _ = X ^ q - 1 := by rw [Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one]
      have := hX.eq_zero
      rwa [eval_sub, eval_pow, eval_X, eval_one, sub_eq_zero] at this
    have hord : orderOf ζ = q := orderOf_eq_prime hζq hζ1
    have hprim : IsPrimitiveRoot ζ q := hord ▸ IsPrimitiveRoot.orderOf ζ

    let f : (ZMod q)ˣ → L := fun a => ζ ^ (a : ZMod q).val
    have hf_inj : Function.Injective f := by
      intro a b hab
      simp only [f] at hab
      exact Units.ext (ZMod.val_injective q (hprim.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hab))
    have hf_root : ∀ a, f a ∈ g'.roots.toFinset := by
      intro a
      rw [Multiset.mem_toFinset, mem_roots hg'0]
      have hd : g' ∣ expand L (a : ZMod q).val g' := by
        rw [hg', ← map_expand]; exact Polynomial.map_dvd _ (hexp a)
      have := hζ.dvd hd
      rwa [IsRoot, expand_eval] at this
    calc q - 1 = Fintype.card (ZMod q)ˣ := (ZMod.card_units q).symm
      _ = (Finset.univ.image f).card := by
        rw [Finset.card_image_of_injective _ hf_inj, Finset.card_univ]
      _ ≤ g'.roots.toFinset.card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
        exact hf_root a
      _ ≤ Multiset.card g'.roots := Multiset.toFinset_card_le _
      _ ≤ g'.natDegree := card_roots' g'
      _ = g.natDegree := by rw [hg', natDegree_map]

  have hΦdeg : (cyclotomic q K).natDegree = q - 1 := by
    rw [natDegree_cyclotomic, Nat.totient_prime hq]
  have hgeq : cyclotomic q K = g :=
    eq_of_monic_of_dvd_of_natDegree_le hgmon (cyclotomic.monic q K) hgΦ (by rw [hΦdeg]; exact hdeg)
  have hchar : g ∣ A.charpoly := minpoly.dvd K A (LinearMap.aeval_self_charpoly A)
  rw [hgeq]
  exact eq_of_monic_of_dvd_of_natDegree_le hgmon (LinearMap.charpoly_monic A) hchar
    (by rw [LinearMap.charpoly_natDegree, hfin, ← hgeq, hΦdeg])

end S_CuspidalType_charpoly_scalarElem_mul_unipotent_eq_cyclotomic_of_cuspidal
end P2MW
export P2MW.S_CuspidalType_charpoly_scalarElem_mul_unipotent_eq_cyclotomic_of_cuspidal (solution)
