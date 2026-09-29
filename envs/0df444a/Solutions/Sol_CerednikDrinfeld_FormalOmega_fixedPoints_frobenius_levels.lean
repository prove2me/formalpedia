-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.fixedPoints_frobenius_levels
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/93bb4bae-cd75-5a60-a39e-104ebb748d23

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_fixedPoints_frobenius_levels

set_option autoImplicit false

namespace CerednikDrinfeld
namespace FormalOmega
namespace TeichLevelsAux
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

open Polynomial

section Basic

variable {S : Type} [CommRing S]

theorem root_unique [IsDomain S] (I : Ideal S) (hI : I ≠ ⊤) (Q : ℕ) (hQ : (Q : S) ∈ I)
    {t t' : S} (ht : t ^ Q = t) (ht' : t' ^ Q = t') (h : t - t' ∈ I) : t = t' := by
  rcases Nat.eq_zero_or_pos Q with hQ0 | hQpos
  · subst hQ0; rw [pow_zero] at ht ht'; rw [← ht, ← ht']
  have key : (∑ i ∈ Finset.range Q, t ^ i * t' ^ (Q - 1 - i) - 1) * (t - t') = 0 := by
    rw [sub_mul, geom_sum₂_mul, one_mul, ht, ht', sub_self]
  rcases mul_eq_zero.mp key with h1 | h2
  · exfalso
    apply hI
    rw [Ideal.eq_top_iff_one]
    have hG : (∑ i ∈ Finset.range Q, t ^ i * t' ^ (Q - 1 - i)) ∈ I := by
      have hmk : Ideal.Quotient.mk I t = Ideal.Quotient.mk I t' := by
        rw [Ideal.Quotient.eq]; exact h
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum]
      simp only [map_mul, map_pow, hmk, ← pow_add]
      have : ∀ i ∈ Finset.range Q, (Ideal.Quotient.mk I t') ^ (i + (Q - 1 - i)) = (Ideal.Quotient.mk I t') ^ (Q - 1) := by
        intro i hi
        congr 1
        have := Finset.mem_range.mp hi
        omega
      rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← map_natCast (Ideal.Quotient.mk I), (Ideal.Quotient.eq_zero_iff_mem.mpr hQ), zero_mul]
    have : (1 : S) = (∑ i ∈ Finset.range Q, t ^ i * t' ^ (Q - 1 - i)) -
        (∑ i ∈ Finset.range Q, t ^ i * t' ^ (Q - 1 - i) - 1) := by ring
    rw [this, h1, sub_zero]
    exact hG
  · exact sub_eq_zero.mp h2

theorem isUnit_of_not_mem (I : Ideal S) [hmax : I.IsMaximal] (hc : IsAdicComplete I S) {x : S}
    (hx : x ∉ I) : IsUnit x := by
  letI := Ideal.Quotient.field I
  have hx' : Ideal.Quotient.mk I x ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (I := I) ((Ideal.Quotient.mk I x)⁻¹)
  have hxy : x * y - 1 ∈ I := by
    rw [← Ideal.Quotient.eq, map_mul, hy, mul_inv_cancel₀ hx', map_one]
  haveI := hc
  have hj := IsAdicComplete.le_jacobson_bot I hxy
  rw [Ideal.mem_jacobson_bot] at hj
  have := hj 1
  rw [mul_one, sub_add_cancel] at this
  exact isUnit_of_mul_isUnit_left this

theorem exists_root_X_pow_sub_X [IsDomain S] (I : Ideal S) (hc : IsAdicComplete I S)
    (Q : ℕ) (hQ2 : 2 ≤ Q) (hQ : (Q : S) ∈ I) (a₀ : S) (h₀ : a₀ ^ Q - a₀ ∈ I) :
    ∃ t : S, t ^ Q = t ∧ t - a₀ ∈ I := by
  haveI := hc
  have hmonic : (X ^ Q - X : S[X]).Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [degree_X]; exact_mod_cast (lt_of_lt_of_le one_lt_two hQ2)
  have heval : ∀ a : S, (X ^ Q - X : S[X]).eval a = a ^ Q - a := by intro a; simp
  have hder : ∀ a : S, (derivative (X ^ Q - X : S[X])).eval a = (Q : S) * a ^ (Q - 1) - 1 := by
    intro a; simp [derivative_X_pow]
  obtain ⟨t, ht, ht'⟩ := HenselianRing.is_henselian (R := S) (I := I) (X ^ Q - X) hmonic a₀
    (by rw [heval]; exact h₀)
    (by
      rw [hder, map_sub, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hQ, zero_mul, zero_sub, map_one]
      exact isUnit_one.neg)
  refine ⟨t, ?_, ht'⟩
  have := ht.eq_zero
  rw [heval] at this
  exact sub_eq_zero.mp this

theorem mk_iterate_eq_pow (I : Ideal S) (r : ℕ) (φ : S →+* S) (hφ : ∀ x : S, φ x - x ^ r ∈ I)
    (n : ℕ) (x : S) : Ideal.Quotient.mk I (φ^[n] x) = (Ideal.Quotient.mk I x) ^ (r ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ, pow_mul, ← ih, ← map_pow, Ideal.Quotient.eq]
    exact hφ _

theorem iterate_pow (φ : S →+* S) (n : ℕ) (x : S) (Q : ℕ) : φ^[n] (x ^ Q) = (φ^[n] x) ^ Q := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_pow]

theorem iterate_eq_self_of_pow_eq [IsDomain S] (I : Ideal S) (hI : I ≠ ⊤) (r : ℕ) (hr : (r : S) ∈ I)
    (φ : S →+* S) (hφ : ∀ x : S, φ x - x ^ r ∈ I) (n : ℕ) (hn : 0 < n) (t : S) (ht : t ^ (r ^ n) = t) :
    φ^[n] t = t := by
  have hQ : ((r ^ n : ℕ) : S) ∈ I := by
    obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [Nat.cast_pow, pow_succ]
    exact I.mul_mem_left _ hr
  refine root_unique I hI (r ^ n) hQ ?_ ht ?_
  · rw [← iterate_pow, ht]
  · rw [← Ideal.Quotient.eq, mk_iterate_eq_pow I r φ hφ, ← map_pow, ht]

theorem pow_pow_sub_mem (I : Ideal S) (Q : ℕ) (x : S) (h : x ^ Q - x ∈ I) (n : ℕ) :
    x ^ (Q ^ n) - x ∈ I := by
  rw [← Ideal.Quotient.eq, map_pow] at h ⊢
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_mul, ih, h]

end Basic

section Residue

variable {S : Type} [CommRing S]

theorem eval_map_apply_eq {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (p : A[X]) (z : A) :
    (p.map f).eval (f z) = f (p.eval z) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_hom]

theorem charP_quotient (I : Ideal S) [hmax : I.IsMaximal] (r : ℕ) [hr : Fact r.Prime] (hrI : (r : S) ∈ I) :
    letI := Ideal.Quotient.field I; CharP (S ⧸ I) r := by
  letI := Ideal.Quotient.field I
  apply (CharP.charP_iff_prime_eq_zero hr.out).mpr
  rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
  exact hrI

theorem exists_pow_pow_sub_mem (I : Ideal S) [hmax : I.IsMaximal] (r : ℕ) [hr : Fact r.Prime] (hrI : (r : S) ∈ I)
    (p : S[X]) (hp : p.Monic) (hcoef : ∀ i, p.coeff i ^ r - p.coeff i ∈ I) (x : S) (hx : p.eval x ∈ I) :
    ∃ d, 0 < d ∧ x ^ (r ^ d) - x ∈ I := by
  classical
  letI := Ideal.Quotient.field I
  haveI : CharP (S ⧸ I) r := charP_quotient I r hrI
  set mk := Ideal.Quotient.mk I with hmk
  set pb : (S ⧸ I)[X] := p.map mk with hpb
  have hpb0 : pb ≠ 0 := (hp.map mk).ne_zero
  have hfrob : pb.map (frobenius (S ⧸ I) r) = pb := by
    ext i
    rw [Polynomial.coeff_map, hpb, Polynomial.coeff_map, frobenius_def, ← map_pow, hmk, Ideal.Quotient.eq]
    exact hcoef i
  have hroot_pow : ∀ z : S ⧸ I, pb.eval z = 0 → pb.eval (z ^ r) = 0 := by
    intro z hz
    have := eval_map_apply_eq (frobenius (S ⧸ I) r) pb z
    rw [hz, map_zero, hfrob, frobenius_def] at this
    exact this
  set a : ℕ → S ⧸ I := fun n => mk x ^ (r ^ n) with ha
  have ha_root : ∀ n, pb.eval (a n) = 0 := by
    intro n
    induction n with
    | zero =>
      simp only [ha, pow_zero, pow_one]
      rw [hpb, eval_map_apply_eq, hmk, Ideal.Quotient.eq_zero_iff_mem]
      exact hx
    | succ n ih =>
      have := hroot_pow _ ih
      simp only [ha] at this ⊢
      rwa [pow_succ, pow_mul]
  have ha_mem : ∀ n, a n ∈ pb.roots.toFinset := by
    intro n
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hpb0]
    exact ha_root n
  obtain ⟨i, j, hij, hEq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => (⟨a n, ha_mem n⟩ : pb.roots.toFinset))
  have hEq' : a i = a j := congrArg Subtype.val hEq

  have key : ∀ i j : ℕ, i < j → a i = a j → ∃ d, 0 < d ∧ x ^ (r ^ d) - x ∈ I := by
    intro i j hlt h
    refine ⟨j - i, Nat.sub_pos_of_lt hlt, ?_⟩
    rw [← Ideal.Quotient.eq, ← hmk, map_pow]
    have hinj : Function.Injective ((frobenius (S ⧸ I) r)^[i]) := Function.Injective.iterate (frobenius_inj _ _) i
    apply hinj
    rw [iterate_frobenius, iterate_frobenius, ← pow_mul, ← pow_add, Nat.sub_add_cancel hlt.le]
    simp only [ha] at h
    exact h.symm
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact key i j hlt hEq'
  · exact key j i hgt hEq'.symm

theorem isAlgClosed_quotient (I : Ideal S) [hmax : I.IsMaximal]
    (hclosed : ∀ p : S[X], p.Monic → 0 < p.natDegree → ∃ x : S, p.eval x ∈ I) :
    letI := Ideal.Quotient.field I; IsAlgClosed (S ⧸ I) := by
  letI := Ideal.Quotient.field I
  apply IsAlgClosed.of_exists_root
  intro q hq hirr
  have hlifts : q ∈ Polynomial.lifts (Ideal.Quotient.mk I) := by
    rw [Polynomial.mem_lifts]
    exact Polynomial.map_surjective _ Ideal.Quotient.mk_surjective q
  obtain ⟨p, hpq, hdeg, hpmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic hlifts hq
  have hpos : 0 < p.natDegree := by
    have h1 := Polynomial.degree_pos_of_irreducible hirr
    rw [← hdeg] at h1
    exact Polynomial.natDegree_pos_iff_degree_pos.mpr h1
  obtain ⟨x, hx⟩ := hclosed p hpmonic hpos
  refine ⟨Ideal.Quotient.mk I x, ?_⟩
  rw [← hpq, eval_map_apply_eq, Ideal.Quotient.eq_zero_iff_mem]
  exact hx

theorem exists_exact_level (I : Ideal S) [hmax : I.IsMaximal] (r : ℕ) [hr : Fact r.Prime] (hrI : (r : S) ∈ I)
    (hclosed : ∀ p : S[X], p.Monic → 0 < p.natDegree → ∃ x : S, p.eval x ∈ I)
    (m : ℕ) (hm : 0 < m) (k : ℕ) (hk : 0 < k) :
    ∃ a : S, a ^ ((r ^ m) ^ k) - a ∈ I ∧ ∀ d, 0 < d → d < k → a ^ ((r ^ m) ^ d) - a ∉ I := by
  classical
  letI := Ideal.Quotient.field I
  haveI : CharP (S ⧸ I) r := charP_quotient I r hrI
  haveI : IsAlgClosed (S ⧸ I) := isAlgClosed_quotient I hclosed
  set q : ℕ := r ^ m with hq
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 ≤ r := hr.out.two_le
      _ = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ m := Nat.pow_le_pow_right hr.out.pos hm
  set f : (S ⧸ I)[X] := X ^ (q ^ k) - X with hf
  have hQ2 : 2 ≤ q ^ k := by
    calc 2 ≤ q := hq2
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ k := Nat.pow_le_pow_right (by omega) hk
  have hfsep : f.Separable := by
    rw [hf]
    apply galois_poly_separable r
    rw [hq, ← pow_mul]
    exact dvd_pow_self r (Nat.mul_ne_zero hm.ne' hk.ne')
  have hfdeg : f.natDegree = q ^ k := by
    rw [hf]
    exact FiniteField.X_pow_card_sub_X_natDegree_eq (S ⧸ I) (by omega)
  have hf0 : f ≠ 0 := by
    rw [hf]; exact FiniteField.X_pow_card_sub_X_ne_zero (S ⧸ I) (by omega)
  have hcard : f.roots.toFinset.card = q ^ k := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hfsep), ← hfdeg]
    exact (Polynomial.Splits.natDegree_eq_card_roots (IsAlgClosed.splits f)).symm
  set g : ℕ → (S ⧸ I)[X] := fun d => X ^ (q ^ d) - X with hg
  set bad : Finset (S ⧸ I) := (Finset.Ioo 0 k).biUnion fun d => (g d).roots.toFinset with hbad
  have hbad_card : bad.card < q ^ k := by
    calc bad.card ≤ ∑ d ∈ Finset.Ioo 0 k, ((g d).roots.toFinset).card := Finset.card_biUnion_le
      _ ≤ ∑ d ∈ Finset.Ioo 0 k, q ^ d := by
          apply Finset.sum_le_sum
          intro d hd
          have hd' := (Finset.mem_Ioo.mp hd).1
          calc ((g d).roots.toFinset).card ≤ (g d).roots.card := Multiset.toFinset_card_le _
            _ ≤ (g d).natDegree := Polynomial.card_roots' _
            _ = q ^ d := by
                simp only [hg]
                exact FiniteField.X_pow_card_sub_X_natDegree_eq (S ⧸ I)
                  (by calc 1 < 2 := one_lt_two
                         _ ≤ q := hq2
                         _ = q ^ 1 := (pow_one q).symm
                         _ ≤ q ^ d := Nat.pow_le_pow_right (by omega) hd')
      _ < q ^ k := Nat.geomSum_lt hq2 (fun d hd => (Finset.mem_Ioo.mp hd).2)
  rw [← hcard] at hbad_card
  obtain ⟨ab, hab, hab_bad⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad_card
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective ab
  refine ⟨a, ?_, ?_⟩
  · rw [Multiset.mem_toFinset, Polynomial.mem_roots hf0, Polynomial.IsRoot, hf] at hab
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X] at hab
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow]
    exact hab
  · intro d hd1 hd2 hmem
    apply hab_bad
    rw [hbad, Finset.mem_biUnion]
    refine ⟨d, Finset.mem_Ioo.mpr ⟨hd1, hd2⟩, ?_⟩
    have hg0 : g d ≠ 0 := by
      simp only [hg]
      exact FiniteField.X_pow_card_sub_X_ne_zero (S ⧸ I)
        (by calc 1 < 2 := one_lt_two
               _ ≤ q := hq2
               _ = q ^ 1 := (pow_one q).symm
               _ ≤ q ^ d := Nat.pow_le_pow_right (by omega) hd1)
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hg0, Polynomial.IsRoot]
    simp only [hg, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← map_pow, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact hmem

end Residue

section Vandermonde

variable {R T : Type} [CommRing R] [CommRing T] [Algebra R T]

theorem mulVec_injective_of_isUnit {n : Type} [Fintype n] [DecidableEq n] (V : Matrix n n T) (hV : IsUnit V) :
    Function.Injective V.mulVec := by
  obtain ⟨u, rfl⟩ := hV
  intro a b h
  have h2 := congrArg (fun x => ((u⁻¹ : (Matrix n n T)ˣ) : Matrix n n T).mulVec x) h
  simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h2
  exact h2

theorem mulVec_surjective_of_isUnit {n : Type} [Fintype n] [DecidableEq n] (V : Matrix n n T) (hV : IsUnit V) :
    Function.Surjective V.mulVec := by
  obtain ⟨u, rfl⟩ := hV
  intro y
  refine ⟨((u⁻¹ : (Matrix n n T)ˣ) : Matrix n n T).mulVec y, ?_⟩
  simp only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

theorem isUnit_vandermonde (k : ℕ) (ζ : T) (σ : T ≃ₐ[R] T)
    (hunit : ∀ i j : Fin k, i ≠ j → IsUnit ((σ ^ (i : ℕ)) ζ - (σ ^ (j : ℕ)) ζ)) :
    IsUnit (Matrix.vandermonde (fun j : Fin k => (σ ^ (j : ℕ)) ζ)) := by
  classical
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_vandermonde]
  refine IsUnit.prod_iff.mpr fun i _ => IsUnit.prod_iff.mpr fun j hj => ?_
  exact hunit j i (Finset.mem_Ioi.mp hj).ne'

theorem exists_basis_of_existsUnique {M : Type} [AddCommGroup M] [Module R M] {k : ℕ} (v : Fin k → M)
    (h : ∀ x : M, ∃! c : Fin k → R, x = ∑ i, c i • v i) :
    ∃ b : Module.Basis (Fin k) R M, ∀ i, b i = v i := by
  have hli : LinearIndependent R v := by
    refine Fintype.linearIndependent_iff.mpr fun g hg => ?_
    have : g = 0 := (h 0).unique hg.symm (by simp)
    exact fun i => congrFun this i
  have hsp : ⊤ ≤ Submodule.span R (Set.range v) := by
    intro x _
    obtain ⟨c, hc, -⟩ := h x
    rw [hc]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun i => Module.Basis.mk_apply hli hsp i⟩

theorem existsUnique_coeffs (k : ℕ) (hk : 0 < k) (ζ : T) (σ : T ≃ₐ[R] T) (hσk : σ ^ k = 1)
    (hfix : ∀ x : T, σ x = x → ∃ c : R, algebraMap R T c = x)
    (hinj : Function.Injective (algebraMap R T))
    (hunit : ∀ i j : Fin k, i ≠ j → IsUnit ((σ ^ (i : ℕ)) ζ - (σ ^ (j : ℕ)) ζ))
    (x : T) : ∃! c : Fin k → R, x = ∑ i : Fin k, c i • ζ ^ (i : ℕ) := by
  classical
  set V : Matrix (Fin k) (Fin k) T := Matrix.vandermonde (fun j : Fin k => (σ ^ (j : ℕ)) ζ) with hV
  have hVu : IsUnit V := isUnit_vandermonde k ζ σ hunit
  set vec : Fin k → T := fun j => (σ ^ (j : ℕ)) x with hvec

  have hrep : ∀ c : Fin k → R, x = ∑ i : Fin k, c i • ζ ^ (i : ℕ) →
      V.mulVec (fun i => algebraMap R T (c i)) = vec := by
    intro c hc
    funext j
    simp only [hvec, Matrix.mulVec, dotProduct, hV, Matrix.vandermonde_apply]
    rw [hc, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_pow, Algebra.smul_def, mul_comm]
  obtain ⟨u, hu⟩ := hVu
  set c' : Fin k → T := ((u⁻¹ : (Matrix (Fin k) (Fin k) T)ˣ) : Matrix (Fin k) (Fin k) T).mulVec vec with hc'
  have hVc' : V.mulVec c' = vec := by
    rw [hc', ← hu, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hpow_mod : ∀ n : ℕ, σ ^ n = σ ^ (n % k) := by
    intro n
    conv_lhs => rw [← Nat.mod_add_div n k, pow_add, pow_mul, hσk, one_pow, mul_one]
  have hrow : ∀ n : ℕ, ∑ i : Fin k, ((σ ^ n) ζ) ^ (i : ℕ) * c' i = (σ ^ n) x := by
    intro n
    have := congrFun hVc' ⟨n % k, Nat.mod_lt n hk⟩
    simp only [Matrix.mulVec, dotProduct, hV, Matrix.vandermonde_apply, hvec] at this
    rw [hpow_mod n]
    exact this
  have hσc' : ∀ i, σ (c' i) = c' i := by
    have h1 : V.mulVec (fun i => σ (c' i)) = V.mulVec c' := by
      funext j
      rw [hVc']
      simp only [Matrix.mulVec, dotProduct, hV, Matrix.vandermonde_apply, hvec]
      have h2 := congrArg σ (hrow ((j : ℕ) + (k - 1)))
      rw [map_sum] at h2
      simp only [map_mul, map_pow] at h2
      have h3 : ∀ y : T, σ ((σ ^ ((j : ℕ) + (k - 1))) y) = (σ ^ (j : ℕ)) y := by
        intro y
        rw [← AlgEquiv.mul_apply, ← pow_succ', show (j : ℕ) + (k - 1) + 1 = (j : ℕ) + k by omega,
          pow_add, hσk, mul_one]
      simp only [h3] at h2
      exact h2
    exact fun i => congrFun (mulVec_injective_of_isUnit V ⟨u, hu⟩ h1) i
  choose c hc using fun i => hfix (c' i) (hσc' i)
  have hxc : x = ∑ i : Fin k, c i • ζ ^ (i : ℕ) := by
    have := hrow 0
    rw [pow_zero, AlgEquiv.one_apply, AlgEquiv.one_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, hc, mul_comm]
  refine ⟨c, hxc, fun c₂ hc₂ => ?_⟩
  have := mulVec_injective_of_isUnit V ⟨u, hu⟩ ((hrep c₂ hc₂).trans (hrep c hxc).symm)
  funext i
  exact hinj (congrFun this i)

open TensorProduct in

theorem exists_galois_equiv (k : ℕ) (ζ : T) (σ : T ≃ₐ[R] T)
    (b : Module.Basis (Fin k) R T) (hb : ∀ i, b i = ζ ^ (i : ℕ))
    (hunit : ∀ i j : Fin k, i ≠ j → IsUnit ((σ ^ (i : ℕ)) ζ - (σ ^ (j : ℕ)) ζ)) :
    ∃ e : T ⊗[R] T ≃ₐ[R] (Fin k → T), ∀ x y : T, e (x ⊗ₜ[R] y) = fun j : Fin k => x * (σ ^ (j : ℕ)) y := by
  classical
  let e₀ : T ⊗[R] T →ₐ[R] (Fin k → T) :=
    Pi.algHom R (fun _ : Fin k => T)
      (fun j => Algebra.TensorProduct.productMap (AlgHom.id R T) ((σ ^ (j : ℕ) : T ≃ₐ[R] T) : T →ₐ[R] T))
  have he₀ : ∀ x y : T, e₀ (x ⊗ₜ[R] y) = fun j : Fin k => x * (σ ^ (j : ℕ)) y := by
    intro x y
    funext j
    simp [e₀, Algebra.TensorProduct.productMap_apply_tmul]
  set V : Matrix (Fin k) (Fin k) T := Matrix.vandermonde (fun j : Fin k => (σ ^ (j : ℕ)) ζ) with hV
  have hVu : IsUnit V := isUnit_vandermonde k ζ σ hunit
  set bB := Algebra.TensorProduct.basis T b with hbB
  have hfac : ∀ w : T ⊗[R] T, e₀ w = V.mulVec (fun i => bB.repr w i) := by
    intro w
    have hw : w = ∑ i, (bB.repr w i) ⊗ₜ[R] (ζ ^ (i : ℕ)) := by
      conv_lhs => rw [← bB.sum_repr w]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hbB, Algebra.TensorProduct.basis_apply, hb, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    conv_lhs => rw [hw]
    rw [map_sum]
    funext j
    simp only [Finset.sum_apply, he₀, Matrix.mulVec, dotProduct, hV, Matrix.vandermonde_apply, map_pow]
    refine Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hbij : Function.Bijective e₀ := by
    have h1 : (e₀ : T ⊗[R] T → (Fin k → T)) = (fun c => V.mulVec c) ∘ (fun w => (fun i => bB.repr w i)) :=
      funext hfac
    have h2 : (fun w : T ⊗[R] T => (fun i => bB.repr w i)) = ⇑bB.equivFun := by
      funext w; rw [Module.Basis.equivFun_apply]
    rw [h1, h2]
    exact Function.Bijective.comp ⟨mulVec_injective_of_isUnit V hVu, mulVec_surjective_of_isUnit V hVu⟩
      bB.equivFun.bijective
  exact ⟨AlgEquiv.ofBijective e₀ hbij, fun x y => by rw [AlgEquiv.ofBijective_apply, he₀]⟩

end Vandermonde

section Levels

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

abbrev Lev (F : S ≃ₐ[R] S) (k : ℕ) : Subalgebra R S :=
  AlgHom.equalizer ((F ^ k : S ≃ₐ[R] S) : S →ₐ[R] S) (AlgHom.id R S)

theorem mem_Lev {F : S ≃ₐ[R] S} {k : ℕ} {x : S} : x ∈ Lev F k ↔ (F ^ k) x = x := by
  simp [AlgHom.mem_equalizer]

theorem pow_mul_apply_of_fixed (F : S ≃ₐ[R] S) (k l : ℕ) (x : S) (h : (F ^ k) x = x) :
    (F ^ (k * l)) x = x := by
  induction l with
  | zero => simp
  | succ l ih => rw [Nat.mul_succ, pow_add, AlgEquiv.mul_apply, h, ih]

theorem Lev_le_of_dvd (F : S ≃ₐ[R] S) {k K : ℕ} (h : k ∣ K) : Lev F k ≤ Lev F K := by
  obtain ⟨l, rfl⟩ := h
  intro x hx
  exact mem_Lev.mpr (pow_mul_apply_of_fixed F k l x (mem_Lev.mp hx))

theorem map_mem_Lev (F : S ≃ₐ[R] S) (k : ℕ) {x : S} (hx : x ∈ Lev F k) : F x ∈ Lev F k := by
  rw [mem_Lev] at hx ⊢
  rw [← AlgEquiv.mul_apply, ← pow_succ, pow_succ', AlgEquiv.mul_apply, hx]

theorem symm_mem_Lev (F : S ≃ₐ[R] S) (k : ℕ) {x : S} (hx : x ∈ Lev F k) : F.symm x ∈ Lev F k := by
  rw [mem_Lev] at hx ⊢
  apply F.injective
  rw [AlgEquiv.apply_symm_apply, ← AlgEquiv.mul_apply, ← pow_succ', pow_succ, AlgEquiv.mul_apply,
    AlgEquiv.apply_symm_apply, hx]

noncomputable def levAut (F : S ≃ₐ[R] S) (k : ℕ) : Lev F k ≃ₐ[R] Lev F k :=
  AlgEquiv.ofBijective (((F : S →ₐ[R] S).comp (Lev F k).val).codRestrict (Lev F k)
    (fun x => map_mem_Lev F k x.2))
    (by
      constructor
      · intro x y h
        apply Subtype.ext
        apply F.injective
        have := congrArg Subtype.val h
        simpa using this
      · intro y
        refine ⟨⟨F.symm y, symm_mem_Lev F k y.2⟩, ?_⟩
        apply Subtype.ext
        simp)

theorem levAut_apply_coe (F : S ≃ₐ[R] S) (k : ℕ) (x : Lev F k) : ((levAut F k x : Lev F k) : S) = F x := by
  simp [levAut]

theorem levAut_pow_apply_coe (F : S ≃ₐ[R] S) (k : ℕ) (n : ℕ) (x : Lev F k) :
    (((levAut F k ^ n) x : Lev F k) : S) = (F ^ n) x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, ih, levAut_apply_coe, pow_succ, AlgEquiv.mul_apply]

theorem levAut_pow_eq_one (F : S ≃ₐ[R] S) (k : ℕ) : levAut F k ^ k = 1 := by
  ext x
  rw [levAut_pow_apply_coe, AlgEquiv.one_apply]
  exact mem_Lev.mp x.2

theorem isUnit_lev_of_isUnit (F : S ≃ₐ[R] S) (k : ℕ) (x : Lev F k) (hx : IsUnit (x : S)) : IsUnit x := by
  obtain ⟨u, hu⟩ := hx
  have hinv : ((u⁻¹ : Sˣ) : S) ∈ Lev F k := by
    rw [mem_Lev]
    have h1 : (F ^ k) (u : S) = u := by rw [hu]; exact mem_Lev.mp x.2
    have h2 : (F ^ k) ((u⁻¹ : Sˣ) : S) * (u : S) = 1 := by
      rw [← h1, ← map_mul, Units.inv_mul, map_one]
    calc (F ^ k) ((u⁻¹ : Sˣ) : S) = (F ^ k) ((u⁻¹ : Sˣ) : S) * ((u : S) * ((u⁻¹ : Sˣ) : S)) := by
          rw [Units.mul_inv, mul_one]
      _ = ((u⁻¹ : Sˣ) : S) := by rw [← mul_assoc, h2, one_mul]
  refine ⟨⟨x, ⟨(u⁻¹ : Sˣ), hinv⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext; change (x : S) * ((u⁻¹ : Sˣ) : S) = 1; rw [← hu, Units.mul_inv]
  · apply Subtype.ext; change ((u⁻¹ : Sˣ) : S) * (x : S) = 1; rw [← hu, Units.inv_mul]

theorem algebraMap_lev_injective (F : S ≃ₐ[R] S) (k : ℕ) (hinj : Function.Injective (algebraMap R S)) :
    Function.Injective (algebraMap R (Lev F k)) := by
  intro a b h
  apply hinj
  have := congrArg (fun t : Lev F k => (t : S)) h
  simpa using this

end Levels

section Assembly

variable {R S : Type} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]

theorem levels_part_i (π : S) [hmax : (Ideal.span {π}).IsMaximal] (hc : IsAdicComplete (Ideal.span {π}) S)
    (r : ℕ) [hr : Fact r.Prime] (hrI : (r : S) ∈ Ideal.span {π}) (m : ℕ) (hm : 0 < m)
    (φ : S →+* S) (hφ : ∀ x : S, φ x - x ^ r ∈ Ideal.span {π})
    (F : S ≃ₐ[R] S) (hFφ : ∀ (k : ℕ) (x : S), (F ^ k) x = (⇑φ)^[m * k] x)
    (hπlev : ∀ K : ℕ, π ∈ Lev F K)
    (halg : ∀ x : S, ∃ d, 0 < d ∧ x ^ (r ^ d) - x ∈ Ideal.span {π}) :
    ∀ (N : ℕ) (x : S), ∃ k : ℕ, 0 < k ∧ ∃ x' ∈ Lev F k, x - x' ∈ Ideal.span {π ^ N} := by
  have hItop : Ideal.span {π} ≠ ⊤ := hmax.ne_top
  have hrnI : ∀ n : ℕ, 0 < n → ((r ^ n : ℕ) : S) ∈ Ideal.span {π} := by
    intro n hn
    obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [Nat.cast_pow, pow_succ]
    exact Ideal.mul_mem_left _ _ hrI
  have hrn2 : ∀ n : ℕ, 0 < n → 2 ≤ r ^ n := by
    intro n hn
    calc 2 ≤ r := hr.out.two_le
      _ = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ n := Nat.pow_le_pow_right hr.out.pos hn
  have hteich : ∀ k : ℕ, 0 < k → ∀ t : S, t ^ (r ^ (m * k)) = t → t ∈ Lev F k := by
    intro k hk t ht
    rw [mem_Lev, hFφ]
    exact iterate_eq_self_of_pow_eq (Ideal.span {π}) hItop r hrI φ hφ (m * k) (Nat.mul_pos hm hk) t ht
  intro N
  induction N with
  | zero =>
    intro x
    refine ⟨1, one_pos, 0, Subalgebra.zero_mem _, ?_⟩
    simp
  | succ N ih =>
    intro x
    obtain ⟨d, hd, hxd⟩ := halg x
    have hxd' : x ^ (r ^ (m * d)) - x ∈ Ideal.span {π} := by
      rw [mul_comm, pow_mul]
      exact pow_pow_sub_mem _ _ x hxd m
    obtain ⟨t, ht, htx⟩ := exists_root_X_pow_sub_X (Ideal.span {π}) hc (r ^ (m * d))
      (hrn2 _ (Nat.mul_pos hm hd)) (hrnI _ (Nat.mul_pos hm hd)) x hxd'
    have htL : t ∈ Lev F d := hteich d hd t ht
    have hxt : x - t ∈ Ideal.span {π} := by
      have := Submodule.neg_mem _ htx
      rwa [neg_sub] at this
    obtain ⟨x₁, hx₁⟩ := Ideal.mem_span_singleton.mp hxt
    obtain ⟨k₁, hk₁, x₁', hx₁', hN⟩ := ih x₁
    obtain ⟨c, hc'⟩ := Ideal.mem_span_singleton.mp hN
    refine ⟨d * k₁, Nat.mul_pos hd hk₁, t + π * x₁', ?_, ?_⟩
    · exact Subalgebra.add_mem _ (Lev_le_of_dvd F (dvd_mul_right d k₁) htL)
        (Subalgebra.mul_mem _ (hπlev _) (Lev_le_of_dvd F (dvd_mul_left k₁ d) hx₁'))
    · rw [Ideal.mem_span_singleton]
      refine ⟨c, ?_⟩
      calc x - (t + π * x₁') = (x - t) - π * x₁' := by ring
        _ = π * (x₁ - x₁') := by rw [hx₁]; ring
        _ = π ^ (N + 1) * c := by rw [hc']; ring

open TensorProduct in

theorem levels_part_ii (I : Ideal S) [hmax : I.IsMaximal] (hc : IsAdicComplete I S)
    (r : ℕ) [hr : Fact r.Prime] (hrI : (r : S) ∈ I)
    (hclosed : ∀ p : S[X], p.Monic → 0 < p.natDegree → ∃ x : S, p.eval x ∈ I)
    (m : ℕ) (hm : 0 < m)
    (φ : S →+* S) (hφ : ∀ x : S, φ x - x ^ r ∈ I)
    (F : S ≃ₐ[R] S) (hFφ : ∀ (k : ℕ) (x : S), (F ^ k) x = (⇑φ)^[m * k] x)
    (hfixR : ∀ x : S, F x = x → ∃ c : R, algebraMap R S c = x)
    (hinjR : Function.Injective (algebraMap R S))
    (k : ℕ) (hk : 0 < k) :
    ∃ (ζ : Lev F k) (σ : Lev F k ≃ₐ[R] Lev F k),
      (∀ x : Lev F k, (σ x : S) = F (x : S)) ∧
      (∀ x : Lev F k, ∃! c : Fin k → R, x = ∑ i : Fin k, c i • ζ ^ (i : ℕ)) ∧
      (∀ i j : Fin k, i ≠ j → IsUnit ((σ ^ (i : ℕ)) ζ - (σ ^ (j : ℕ)) ζ)) ∧
      ∃ e : Lev F k ⊗[R] Lev F k ≃ₐ[R] (Fin k → Lev F k),
        ∀ x y : Lev F k, e (x ⊗ₜ[R] y) = fun j : Fin k => x * (σ ^ (j : ℕ)) y := by
  classical
  have hItop : I ≠ ⊤ := hmax.ne_top
  have hrnI : ∀ n : ℕ, 0 < n → ((r ^ n : ℕ) : S) ∈ I := by
    intro n hn
    obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [Nat.cast_pow, pow_succ]
    exact Ideal.mul_mem_left _ _ hrI
  have hrn2 : ∀ n : ℕ, 0 < n → 2 ≤ r ^ n := by
    intro n hn
    calc 2 ≤ r := hr.out.two_le
      _ = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ n := Nat.pow_le_pow_right hr.out.pos hn
  obtain ⟨a, ha, hane⟩ := exists_exact_level I r hrI hclosed m hm k hk
  obtain ⟨t, ht, hta⟩ := exists_root_X_pow_sub_X I hc (r ^ (m * k)) (hrn2 _ (Nat.mul_pos hm hk))
    (hrnI _ (Nat.mul_pos hm hk)) a (by rwa [pow_mul])
  have htL : t ∈ Lev F k := by
    rw [mem_Lev, hFφ]
    exact iterate_eq_self_of_pow_eq I hItop r hrI φ hφ (m * k) (Nat.mul_pos hm hk) t ht
  let ζ : Lev F k := ⟨t, htL⟩
  have hζ : (ζ : S) = t := rfl
  let σ : Lev F k ≃ₐ[R] Lev F k := levAut F k
  have hσ : σ = levAut F k := rfl
  let A : S ⧸ I := Ideal.Quotient.mk I a
  have hA : A = Ideal.Quotient.mk I a := rfl
  have hAq : A ^ ((r ^ m) ^ k) = A := by
    rw [hA, ← map_pow, Ideal.Quotient.eq]; exact ha
  have hconj : ∀ i : ℕ, Ideal.Quotient.mk I (((σ ^ i) ζ : Lev F k) : S) = A ^ ((r ^ m) ^ i) := by
    intro i
    rw [hσ, levAut_pow_apply_coe, hFφ, mk_iterate_eq_pow I r φ hφ (m * i), hζ, pow_mul, hA]
    congr 1
    rw [Ideal.Quotient.eq]; exact hta
  have hunit : ∀ i j : Fin k, i ≠ j → IsUnit ((σ ^ (i : ℕ)) ζ - (σ ^ (j : ℕ)) ζ) := by
    have key : ∀ i j : ℕ, i < j → j < k → A ^ ((r ^ m) ^ i) = A ^ ((r ^ m) ^ j) → False := by
      intro i j hij hjk h
      have h2 : A ^ ((r ^ m) ^ (i + (k - j))) = A ^ ((r ^ m) ^ (j + (k - j))) := by
        rw [pow_add, pow_mul, h, ← pow_mul, ← pow_add]
      rw [show j + (k - j) = k by omega, hAq] at h2
      apply hane (i + (k - j)) (by omega) (by omega)
      rw [← Ideal.Quotient.eq, map_pow, ← hA]
      exact h2
    intro i j hij
    apply isUnit_lev_of_isUnit
    apply isUnit_of_not_mem I hc
    intro hmem
    rw [Subalgebra.coe_sub, ← Ideal.Quotient.eq, hconj, hconj] at hmem
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
    · exact key i j hlt j.2 hmem
    · exact key j i hgt i.2 hmem.symm
  have hσk : σ ^ k = 1 := by rw [hσ]; exact levAut_pow_eq_one F k
  have hfix : ∀ x : Lev F k, σ x = x → ∃ c : R, algebraMap R (Lev F k) c = x := by
    intro x hx
    have h1 : F (x : S) = x := by
      rw [← levAut_apply_coe F k x, ← hσ]
      exact congrArg Subtype.val hx
    obtain ⟨c, hc'⟩ := hfixR x h1
    exact ⟨c, Subtype.ext (by rw [Subalgebra.coe_algebraMap]; exact hc')⟩
  have hcoef := existsUnique_coeffs k hk ζ σ hσk hfix (algebraMap_lev_injective F k hinjR) hunit
  obtain ⟨bT, hbT⟩ := exists_basis_of_existsUnique (fun i : Fin k => ζ ^ (i : ℕ)) hcoef
  obtain ⟨e, he⟩ := exists_galois_equiv k ζ σ bT hbT hunit
  exact ⟨ζ, σ, fun x => by rw [hσ]; exact levAut_apply_coe F k x, hcoef, hunit, e, he⟩

end Assembly

end CerednikDrinfeld.FormalOmega.TeichLevelsAux

open scoped NumberField TensorProduct
p2m_open "CategoryTheory CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_fixedPoints_frobenius_levels.CerednikDrinfeld CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_fixedPoints_frobenius_levels.CerednikDrinfeld.FormalOmega"
open CerednikDrinfeld.FormalOmega.TeichLevelsAux

theorem solution
    {r : ℕ} [Fact r.Prime]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (m : ℕ) (hm : 0 < m)
    (FrS : Onr ≃ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (hFrS : ∀ x : Onr, FrS x = (Fr ^ (m : ℤ)) x) :
    (∀ (N : ℕ) (x : Onr), ∃ k : ℕ, 0 < k ∧ ∃ x' ∈ (AlgHom.equalizer ((FrS ^ (k : ℕ) : Onr ≃ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr)),
        x - x' ∈ Ideal.span {(algebraMap 𝒪 Onr π) ^ N}) ∧
    (∀ (k : ℕ), 0 < k →
      ∃ (ζ : ↥(AlgHom.equalizer ((FrS ^ (k : ℕ) : Onr ≃ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr))) (σ : ↥(AlgHom.equalizer ((FrS ^ (k : ℕ) : Onr ≃ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr)) ≃ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] ↥(AlgHom.equalizer ((FrS ^ (k : ℕ) : Onr ≃ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr))),
        (∀ x : ↥(AlgHom.equalizer ((FrS ^ (k : ℕ) : Onr ≃ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr)), (σ x : Onr) = FrS (x : Onr)) ∧
        (∀ x : ↥(AlgHom.equalizer ((FrS ^ (k : ℕ) : Onr ≃ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr)), ∃! c : Fin k → ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)), x = ∑ i : Fin k, c i • ζ ^ (i : ℕ)) ∧
        (∀ i j : Fin k, i ≠ j → IsUnit ((σ ^ (i : ℕ)) ζ - (σ ^ (j : ℕ)) ζ)) ∧
        ∃ e : (↥(AlgHom.equalizer ((FrS ^ (k : ℕ) : Onr ≃ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr)) ⊗[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] ↥(AlgHom.equalizer ((FrS ^ (k : ℕ) : Onr ≃ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr))) ≃ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] (Fin k → ↥(AlgHom.equalizer ((FrS ^ (k : ℕ) : Onr ≃ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr))),
          ∀ x y : ↥(AlgHom.equalizer ((FrS ^ (k : ℕ) : Onr ≃ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) : Onr →ₐ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] Onr) (AlgHom.id ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr)), e (x ⊗ₜ[↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr))] y) = fun j : Fin k => x * (σ ^ (j : ℕ)) y) := by
  classical
  haveI hmaxI : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal := hOnr_max

  have hmapI : ∀ y : 𝒪, y ∈ Ideal.span {π} → algebraMap 𝒪 Onr y ∈ (Ideal.span {algebraMap 𝒪 Onr π}) := by
    intro y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  have hrI : ((r : ℕ) : Onr) ∈ (Ideal.span {algebraMap 𝒪 Onr π}) := by
    rw [← map_natCast (algebraMap 𝒪 Onr)]
    apply hmapI
    rw [← hunr]
    exact Ideal.mem_span_singleton_self _

  have hOres : ∀ a : 𝒪, a ^ r - a ∈ Ideal.span {π} := by
    haveI := hdvr.toIsPrincipalIdealRing
    haveI : (Ideal.span {π}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hπ
    letI := Ideal.Quotient.field (Ideal.span {π})
    haveI : Finite (𝒪 ⧸ Ideal.span {π}) :=
      Nat.finite_of_card_ne_zero (by rw [hres]; exact (Fact.out : r.Prime).ne_zero)
    letI := Fintype.ofFinite (𝒪 ⧸ Ideal.span {π})
    intro a
    rw [← Ideal.Quotient.eq, map_pow]
    have := FiniteField.pow_card (Ideal.Quotient.mk (Ideal.span {π}) a)
    rwa [← Nat.card_eq_fintype_card, hres] at this

  let φ : Onr →+* Onr := (Fr : Onr →ₐ[𝒪] Onr).toRingHom
  have hcoe : (⇑φ : Onr → Onr) = ⇑Fr := by funext x; rfl
  have hFrφ : ∀ x : Onr, φ x - x ^ r ∈ (Ideal.span {algebraMap 𝒪 Onr π}) := by intro x; rw [congrFun hcoe x]; exact hFr x
  have hFrS1 : ∀ x : Onr, FrS x = (⇑Fr)^[m] x := by
    intro x; rw [hFrS, zpow_natCast, AlgEquiv.coe_pow]
  have hFrSk : ∀ (k : ℕ) (x : Onr), (FrS ^ k) x = (⇑φ)^[m * k] x := by
    intro k
    rw [hcoe]
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, AlgEquiv.mul_apply, hFrS1, ih, Nat.mul_succ, Function.iterate_add_apply]

  have halg : ∀ x : Onr, ∃ d, 0 < d ∧ x ^ (r ^ d) - x ∈ (Ideal.span {algebraMap 𝒪 Onr π}) := by
    intro x
    obtain ⟨p, hp, hpx⟩ := hOnr_alg x
    refine exists_pow_pow_sub_mem (Ideal.span {algebraMap 𝒪 Onr π}) r hrI (p.map (algebraMap 𝒪 Onr)) (hp.map _) ?_ x ?_
    · intro i
      rw [Polynomial.coeff_map, ← map_pow, ← map_sub]
      exact hmapI _ (hOres (p.coeff i))
    · rwa [Polynomial.eval_map, ← Polynomial.aeval_def]

  have hπmemR : algebraMap 𝒪 Onr π ∈ AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr) := by
    rw [AlgHom.mem_equalizer]
    simp
  have hπlev : ∀ K : ℕ, algebraMap 𝒪 Onr π ∈ Lev FrS K := fun K =>
    Subalgebra.algebraMap_mem (Lev FrS K) (⟨algebraMap 𝒪 Onr π, hπmemR⟩ : ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)))
  have hfixR : ∀ x : Onr, FrS x = x → ∃ c : ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)), algebraMap ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr c = x := by
    intro x hx
    have h2 : x ∈ AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr) := by
      rw [AlgHom.mem_equalizer, AlgHom.id_apply]
      change (Fr ^ (m : ℤ)) x = x
      rw [← hFrS]; exact hx
    exact ⟨⟨x, h2⟩, rfl⟩
  have hinjR : Function.Injective (algebraMap ↥(AlgHom.equalizer ((Fr ^ (m : ℤ) : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr) (AlgHom.id 𝒪 Onr)) Onr) := fun a b h => Subtype.ext h
  exact ⟨levels_part_i (algebraMap 𝒪 Onr π) hOnr_complete r hrI m hm φ hFrφ FrS hFrSk hπlev halg,
    levels_part_ii (Ideal.span {algebraMap 𝒪 Onr π}) hOnr_complete r hrI hOnr_closed m hm φ hFrφ FrS hFrSk hfixR hinjR⟩

end S_CerednikDrinfeld_FormalOmega_fixedPoints_frobenius_levels
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_fixedPoints_frobenius_levels (solution)
