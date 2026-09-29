-- Prove2me | solution 1 for CuspidalType.charpoly_ind_torus_eq_X_pow_orderOf_sub_one_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/7db48c9d-815d-5b2d-a60a-15f5bdfd8d4e

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_charpoly_ind_torus_eq_X_pow_orderOf_sub_one_pow

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "Polynomial CuspidalType P2MW.S_CuspidalType_charpoly_ind_torus_eq_X_pow_orderOf_sub_one_pow.CuspidalType"
open scoped Matrix

namespace PermCharpoly

open Polynomial

variable {K : Type*} [Field K] {X : Type*} [Fintype X] [DecidableEq X]

noncomputable abbrev permLin (K : Type*) [Field K] (σ : Equiv.Perm X) : (X →₀ K) →ₗ[K] (X →₀ K) :=
  Finsupp.lmapDomain K K σ

theorem permLin_single (σ : Equiv.Perm X) (x : X) (c : K) :
    permLin K σ (Finsupp.single x c) = Finsupp.single (σ x) c := by
  simp [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

theorem permLin_one : permLin K (1 : Equiv.Perm X) = LinearMap.id := by
  ext x c; simp [Finsupp.lmapDomain_apply]

theorem permLin_mul (σ τ : Equiv.Perm X) : permLin K (σ * τ) = permLin K σ ∘ₗ permLin K τ := by
  ext x c; simp [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Equiv.Perm.mul_apply]

theorem permLin_pow (σ : Equiv.Perm X) (n : ℕ) : permLin K (σ ^ n) = (permLin K σ) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, permLin_one]; rfl
  | succ n ih => rw [pow_succ, permLin_mul, ih, pow_succ]; rfl

theorem charpoly_permLin_of_transitive (σ : Equiv.Perm X) (m : ℕ) (hm : 0 < m) (hσm : σ ^ m = 1)
    (x₀ : X) (hsurj : ∀ x : X, ∃ j : ℕ, j < m ∧ (σ ^ j) x₀ = x) (hcard : Fintype.card X = m) :
    (permLin K σ).charpoly = Polynomial.X ^ m - 1 := by
  classical

  have hinj : ∀ i j : ℕ, i < m → j < m → (σ ^ i) x₀ = (σ ^ j) x₀ → i = j := by

    have hs : Function.Surjective (fun j : Fin m => (σ ^ (j : ℕ)) x₀) := by
      intro x; obtain ⟨j, hj, h⟩ := hsurj x; exact ⟨⟨j, hj⟩, h⟩
    have hb : Function.Bijective (fun j : Fin m => (σ ^ (j : ℕ)) x₀) := by
      refine (Fintype.bijective_iff_surjective_and_card _).mpr ⟨hs, ?_⟩
      rw [Fintype.card_fin, hcard]
    intro i j hi hj h
    have := hb.1 (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) h
    exact congrArg Fin.val this

  set L : (X →₀ K) →ₗ[K] (X →₀ K) := permLin K σ with hL
  have hLm : L ^ m = 1 := by rw [hL, ← permLin_pow, hσm, permLin_one]; rfl
  have hann : Polynomial.aeval L (Polynomial.X ^ m - 1 : K[X]) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, map_one, hLm, sub_self]
  have hdvd : minpoly K L ∣ Polynomial.X ^ m - 1 := minpoly.dvd K L hann

  have hint : IsIntegral K L := Algebra.IsIntegral.isIntegral L
  have hdeg : m ≤ (minpoly K L).natDegree := by
    by_contra hlt
    push_neg at hlt
    have hp0 : minpoly K L ≠ 0 := (minpoly.monic hint).ne_zero
    have happly := DFunLike.congr_fun (minpoly.aeval K L) (Finsupp.single x₀ (1 : K))
    rw [LinearMap.zero_apply, Polynomial.aeval_eq_sum_range, LinearMap.sum_apply] at happly
    have hterm : ∀ j : ℕ, ((minpoly K L).coeff j • L ^ j) (Finsupp.single x₀ (1 : K)) =
        Finsupp.single ((σ ^ j) x₀) ((minpoly K L).coeff j) := by
      intro j
      rw [LinearMap.smul_apply, hL, ← permLin_pow, permLin_single, Finsupp.smul_single, smul_eq_mul, mul_one]
    simp_rw [hterm] at happly

    have hd : (minpoly K L).natDegree < m := hlt
    have key := congrArg (fun f : X →₀ K => f ((σ ^ (minpoly K L).natDegree) x₀)) happly
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_zero, Pi.zero_apply] at key
    rw [Finset.sum_eq_single (minpoly K L).natDegree] at key
    · rw [Finsupp.single_eq_same] at key
      exact (Polynomial.leadingCoeff_ne_zero.mpr hp0) key
    · intro j hj hjne
      rw [Finsupp.single_eq_of_ne]
      intro heq
      have hj' : j < m := lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hd
      exact hjne (hinj _ _ hj' hd (by first | exact heq | exact heq.symm))
    · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h

  have hXm : (Polynomial.X ^ m - 1 : K[X]).Monic := by
    rw [← Polynomial.C_1]; exact Polynomial.monic_X_pow_sub_C (1 : K) hm.ne'
  have hXmdeg : (Polynomial.X ^ m - 1 : K[X]).natDegree = m := by
    rw [← Polynomial.C_1, Polynomial.natDegree_X_pow_sub_C]
  have hmin : minpoly K L = Polynomial.X ^ m - 1 :=
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hXm hdvd (by rw [hXmdeg]; exact hdeg)).symm
  have hfin : Module.finrank K (X →₀ K) = m := by rw [Module.finrank_finsupp_self, hcard]
  rw [← hmin]
  refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) L.charpoly_monic
    (LinearMap.minpoly_dvd_charpoly L) ?_)
  rw [LinearMap.charpoly_natDegree, hfin, hmin, hXmdeg]

end PermCharpoly

namespace PermCharpoly

open Polynomial

variable {K : Type*} [Field K]

theorem permLin_subtypePerm_single {X : Type*} [Fintype X] [DecidableEq X] (σ : Equiv.Perm X) (p : X → Prop) [DecidablePred p]
    (hp : ∀ x, p (σ x) ↔ p x) (x : {x // p x}) (c : K) :
    permLin K (σ.subtypePerm hp) (Finsupp.single x c) = Finsupp.single ⟨σ x, (hp x).mpr x.2⟩ c := by
  rw [permLin_single]; rfl

theorem charpoly_permLin_of_free :
    ∀ (n : ℕ) (X : Type*) [Fintype X] [DecidableEq X], Fintype.card X = n →
    ∀ (σ : Equiv.Perm X) (m : ℕ), 0 < m → σ ^ m = 1 →
      (∀ j : ℕ, 0 < j → j < m → ∀ x : X, (σ ^ j) x ≠ x) →
      (permLin K σ).charpoly = (Polynomial.X ^ m - 1) ^ (Fintype.card X / m) ∧ m ∣ Fintype.card X := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ hn σ m hm hσm hfree
  classical
  by_cases hX : IsEmpty X
  ·
    have h0 : Fintype.card X = 0 := Fintype.card_eq_zero
    refine ⟨?_, by rw [h0]; exact dvd_zero m⟩
    rw [h0, Nat.zero_div, pow_zero]
    have hfin : Module.finrank K (X →₀ K) = 0 := by rw [Module.finrank_finsupp_self, h0]
    have hmon := (permLin K σ).charpoly_monic
    have hdeg := (permLin K σ).charpoly_natDegree
    rw [hfin] at hdeg
    exact Polynomial.eq_one_of_monic_natDegree_zero hmon hdeg
  · rw [not_isEmpty_iff] at hX
    obtain ⟨x₀⟩ := hX

    let p : X → Prop := fun x => ∃ j : ℕ, (σ ^ j) x₀ = x
    have hp : ∀ x, p x ↔ p (σ x) := by
      intro x
      constructor
      · rintro ⟨j, rfl⟩; exact ⟨j + 1, by rw [pow_succ', Equiv.Perm.mul_apply]⟩
      · rintro ⟨j, hj⟩
        refine ⟨(m - 1) + j, ?_⟩
        rw [pow_add, Equiv.Perm.mul_apply, hj, ← Equiv.Perm.mul_apply, ← pow_succ, Nat.sub_add_cancel hm, hσm]
        rfl
    have hnp : ∀ x, (¬ p x) ↔ (¬ p (σ x)) := fun x => not_congr (hp x)

    have hred : ∀ x, p x → ∃ j, j < m ∧ (σ ^ j) x₀ = x := by
      rintro x ⟨j, rfl⟩
      refine ⟨j % m, Nat.mod_lt j hm, ?_⟩
      conv_rhs => rw [← Nat.mod_add_div j m, pow_add, pow_mul, hσm, one_pow, mul_one]

    set O := {x // p x} with hO
    set C := {x // ¬ p x} with hC
    let σO : Equiv.Perm O := σ.subtypePerm (fun x => (hp x).symm)
    let σC : Equiv.Perm C := σ.subtypePerm (fun x => (hnp x).symm)
    have hσO_pow : ∀ j : ℕ, ∀ x : O, ((σO ^ j) x : X) = (σ ^ j) (x : X) := by
      intro j x
      induction j with
      | zero => rfl
      | succ j ihj => rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply, ← ihj]; rfl
    have hσC_pow : ∀ j : ℕ, ∀ x : C, ((σC ^ j) x : X) = (σ ^ j) (x : X) := by
      intro j x
      induction j with
      | zero => rfl
      | succ j ihj => rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply, ← ihj]; rfl
    have hσOm : σO ^ m = 1 := by
      ext x; exact (hσO_pow m x).trans (by rw [hσm]; rfl)
    have hσCm : σC ^ m = 1 := by
      ext x; exact (hσC_pow m x).trans (by rw [hσm]; rfl)

    have hcardO : Fintype.card O = m := by
      have hsurj : Function.Surjective (fun j : Fin m => (⟨(σ ^ (j : ℕ)) x₀, ⟨j, rfl⟩⟩ : O)) := by
        rintro ⟨x, hx⟩
        obtain ⟨j, hj, rfl⟩ := hred x hx
        exact ⟨⟨j, hj⟩, rfl⟩
      have hinj : Function.Injective (fun j : Fin m => (⟨(σ ^ (j : ℕ)) x₀, ⟨j, rfl⟩⟩ : O)) := by
        intro i j h
        have h' : (σ ^ (i : ℕ)) x₀ = (σ ^ (j : ℕ)) x₀ := congrArg Subtype.val h

        rcases le_total (i : ℕ) (j : ℕ) with hij | hij
        · by_contra hne
          have hlt : (i : ℕ) < j := lt_of_le_of_ne hij (fun e => hne (Fin.ext e))
          have hfix : (σ ^ ((j : ℕ) - i)) ((σ ^ (i : ℕ)) x₀) = (σ ^ (i : ℕ)) x₀ := by
            rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hij, ← h']
          exact hfree _ (Nat.sub_pos_of_lt hlt) (lt_of_le_of_lt (Nat.sub_le _ _) j.2) _ hfix
        · by_contra hne
          have hlt : (j : ℕ) < i := lt_of_le_of_ne hij (fun e => hne (Fin.ext e.symm))
          have hfix : (σ ^ ((i : ℕ) - j)) ((σ ^ (j : ℕ)) x₀) = (σ ^ (j : ℕ)) x₀ := by
            rw [← Equiv.Perm.mul_apply, ← pow_add, Nat.sub_add_cancel hij, h']
          exact hfree _ (Nat.sub_pos_of_lt hlt) (lt_of_le_of_lt (Nat.sub_le _ _) i.2) _ hfix
      have := Fintype.card_of_bijective ⟨hinj, hsurj⟩
      rw [Fintype.card_fin] at this
      exact this.symm

    have hO : (permLin K σO).charpoly = Polynomial.X ^ m - 1 := by
      refine charpoly_permLin_of_transitive σO m hm hσOm ⟨x₀, ⟨0, rfl⟩⟩ ?_ hcardO
      rintro ⟨x, hx⟩
      obtain ⟨j, hj, rfl⟩ := hred x hx
      exact ⟨j, hj, Subtype.ext (hσO_pow j _)⟩

    have hcardC : Fintype.card C < n := by
      rw [← hn]
      have := Fintype.card_subtype_lt (p := fun x => ¬ p x) (x := x₀) (by simp only [not_not]; exact ⟨0, rfl⟩)
      exact this
    have hfreeC : ∀ j : ℕ, 0 < j → j < m → ∀ x : C, (σC ^ j) x ≠ x := by
      intro j hj0 hjm x h
      exact hfree j hj0 hjm (x : X) ((hσC_pow j x).symm.trans (congrArg Subtype.val h))
    obtain ⟨hCpoly, hCdvd⟩ := ih (Fintype.card C) hcardC C rfl σC m hm hσCm hfreeC

    have hcardX : Fintype.card X = m + Fintype.card C := by
      have h1 : Fintype.card C = Fintype.card X - Fintype.card O := Fintype.card_subtype_compl p
      have h2 : Fintype.card O ≤ Fintype.card X := Fintype.card_subtype_le p
      omega
    refine ⟨?_, by rw [hcardX]; exact dvd_add dvd_rfl hCdvd⟩

    let e : (X →₀ K) ≃ₗ[K] (O →₀ K) × (C →₀ K) :=
      (Finsupp.domLCongr (Equiv.sumCompl p).symm).trans (Finsupp.sumFinsuppLEquivProdFinsupp K)

    have he : ∀ (y : X) (c : K), e (Finsupp.single y c) =
        if h : p y then (Finsupp.single (⟨y, h⟩ : O) c, 0) else (0, Finsupp.single (⟨y, h⟩ : C) c) := by
      intro y c
      show Finsupp.sumFinsuppLEquivProdFinsupp K (Finsupp.domLCongr (Equiv.sumCompl p).symm (Finsupp.single y c)) = _
      rw [Finsupp.domLCongr_single]
      by_cases h : p y
      · rw [Equiv.sumCompl_symm_apply_of_pos h, dif_pos h]
        refine Prod.ext ?_ ?_
        · ext a
          rw [Finsupp.fst_sumFinsuppLEquivProdFinsupp, Finsupp.single_apply, Finsupp.single_apply]
          simp only [Sum.inl.injEq]
        · ext a
          rw [Finsupp.snd_sumFinsuppLEquivProdFinsupp, Finsupp.single_apply]
          simp
      · rw [Equiv.sumCompl_symm_apply_of_neg h, dif_neg h]
        refine Prod.ext ?_ ?_
        · ext a
          rw [Finsupp.fst_sumFinsuppLEquivProdFinsupp, Finsupp.single_apply]
          simp
        · ext a
          rw [Finsupp.snd_sumFinsuppLEquivProdFinsupp, Finsupp.single_apply, Finsupp.single_apply]
          simp only [Sum.inr.injEq]
    have key : e.toLinearMap ∘ₗ permLin K σ = ((permLin K σO).prodMap (permLin K σC)) ∘ₗ e.toLinearMap := by
      apply Finsupp.lhom_ext
      intro x c
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, permLin_single]
      by_cases hx : p x
      · have hσx : p (σ x) := (hp x).mp hx
        rw [he, he, dif_pos hσx, dif_pos hx, LinearMap.prodMap_apply, map_zero, permLin_subtypePerm_single]
      · have hσx : ¬ p (σ x) := (hnp x).mp hx
        rw [he, he, dif_neg hσx, dif_neg hx, LinearMap.prodMap_apply, map_zero, permLin_subtypePerm_single]
    have hconj : e.conj (permLin K σ) = (permLin K σO).prodMap (permLin K σC) := by
      rw [LinearEquiv.conj_apply, key, LinearMap.comp_assoc, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
        LinearEquiv.refl_toLinearMap, LinearMap.comp_id]
    rw [← e.charpoly_conj (permLin K σ), hconj, LinearMap.charpoly_prodMap, hO, hCpoly, hcardX,
      Nat.add_div_of_dvd_left hCdvd, Nat.div_self hm, pow_add, pow_one]

end PermCharpoly

namespace CuspidalType
p2m_export "CuspidalType" "GL2 ProjLine card_projLine ind quadBasis torus IsCuspidalOfType"
namespace IndTorus
p2m_open "CuspidalType"

p2m_open "Polynomial CuspidalType P2MW.S_CuspidalType_charpoly_ind_torus_eq_X_pow_orderOf_sub_one_pow.CuspidalType P2MW.S_CuspidalType_charpoly_ind_torus_eq_X_pow_orderOf_sub_one_pow.PermCharpoly"
open scoped Matrix

variable (q : ℕ) [Fact q.Prime]

theorem torus_mulVec_repr (β : (GaloisField q 2)ˣ) (w : GaloisField q 2) :
    ((torus q β : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) *ᵥ ⇑((quadBasis q).repr w) =
      ⇑((quadBasis q).repr ((β : GaloisField q 2) * w)) := by
  have hmat : ((torus q β : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      LinearMap.toMatrix (quadBasis q) (quadBasis q) (Algebra.lmul (ZMod q) (GaloisField q 2) (β : GaloisField q 2)) := rfl
  rw [hmat, LinearMap.toMatrix_mulVec_repr]
  rfl

theorem torus_smul_mk (β : (GaloisField q 2)ˣ) (v : Fin 2 → ZMod q) (hv : v ≠ 0) :
    (torus q β) • Projectivization.mk (ZMod q) v hv =
      Projectivization.mk (ZMod q) (((torus q β : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) *ᵥ v)
        (by
          intro h0
          have := congrArg (fun u => ((torus q β)⁻¹ : GL2 q).val *ᵥ u) h0
          simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
          rw [show ((torus q β)⁻¹ : GL2 q).val * ((torus q β : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) = 1 from
            Units.inv_mul _, Matrix.one_mulVec] at this
          exact hv this) := by
  change (Matrix.GeneralLinearGroup.toLin (torus q β)) • Projectivization.mk (ZMod q) v hv = _
  rw [Projectivization.smul_mk]
  congr 1

theorem exists_repr_eq (v : Fin 2 → ZMod q) : ∃ w : GaloisField q 2, ⇑((quadBasis q).repr w) = v := by
  refine ⟨(quadBasis q).equivFun.symm v, ?_⟩
  ext i
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]

theorem forall_smul_eq_of_exists_smul_eq (β : (GaloisField q 2)ˣ)
    (h : ∃ x : ProjLine q, (torus q β) • x = x) : ∀ x : ProjLine q, (torus q β) • x = x := by
  obtain ⟨x, hx⟩ := h

  induction x using Projectivization.ind with
  | h v hv =>
    rw [torus_smul_mk, Projectivization.mk_eq_mk_iff] at hx
    obtain ⟨a, ha⟩ := hx
    obtain ⟨w, rfl⟩ := exists_repr_eq q v
    have hw : w ≠ 0 := by rintro rfl; apply hv; ext i; simp
    rw [torus_mulVec_repr] at ha

    have hβ : (β : GaloisField q 2) = algebraMap (ZMod q) (GaloisField q 2) (a : ZMod q) := by
      have h1 : ⇑((quadBasis q).repr ((a : ZMod q) • w)) = ⇑((quadBasis q).repr ((β : GaloisField q 2) * w)) := by
        rw [map_smul]; ext i; (have h__af := congrFun ha i; simp at h__af; exact h__af)
      have h2 : (a : ZMod q) • w = (β : GaloisField q 2) * w :=
        (quadBasis q).repr.injective (DFunLike.coe_injective h1)
      rw [Algebra.smul_def] at h2
      exact (mul_right_cancel₀ hw h2).symm

    intro y
    induction y using Projectivization.ind with
    | h u hu =>
      rw [torus_smul_mk, Projectivization.mk_eq_mk_iff]
      obtain ⟨w', rfl⟩ := exists_repr_eq q u
      refine ⟨a, ?_⟩
      rw [torus_mulVec_repr, hβ, ← Algebra.smul_def, map_smul]
      ext i; simp [Units.smul_def]

theorem free_toPermHom_torus (α : (GaloisField q 2)ˣ) :
    ∀ j : ℕ, 0 < j → j < orderOf (MulAction.toPermHom (GL2 q) (ProjLine q) (torus q α)) →
      ∀ x : ProjLine q, ((MulAction.toPermHom (GL2 q) (ProjLine q) (torus q α)) ^ j) x ≠ x := by
  set σ : Equiv.Perm (ProjLine q) := MulAction.toPermHom (GL2 q) (ProjLine q) (torus q α) with hσ
  intro j hj0 hjm x hx
  have hpow : σ ^ j = MulAction.toPermHom (GL2 q) (ProjLine q) (torus q (α ^ j)) := by
    rw [hσ, ← map_pow, ← map_pow]
  have hfix : (torus q (α ^ j)) • x = x := by
    have := hx; rw [hpow, MulAction.toPermHom_apply, MulAction.toPerm_apply] at this; exact this
  have hall := forall_smul_eq_of_exists_smul_eq q (α ^ j) ⟨x, hfix⟩
  have h1 : σ ^ j = 1 := by
    rw [hpow]; ext y; rw [MulAction.toPermHom_apply, MulAction.toPerm_apply, hall y]; rfl
  have := orderOf_dvd_of_pow_eq_one h1
  exact absurd (Nat.le_of_dvd hj0 this) (not_le.mpr hjm)

theorem orderOf_pos_and_dvd (α : (GaloisField q 2)ˣ) :
    0 < orderOf (MulAction.toPermHom (GL2 q) (ProjLine q) (torus q α)) ∧
      orderOf (MulAction.toPermHom (GL2 q) (ProjLine q) (torus q α)) ∣ q + 1 := by
  classical
  set σ : Equiv.Perm (ProjLine q) := MulAction.toPermHom (GL2 q) (ProjLine q) (torus q α) with hσ
  haveI : Fintype (ProjLine q) := Fintype.ofFinite _
  have hcard : Fintype.card (ProjLine q) = q + 1 := by rw [← Nat.card_eq_fintype_card, card_projLine]
  refine ⟨orderOf_pos σ, ?_⟩
  obtain ⟨-, hdvd⟩ := charpoly_permLin_of_free (K := ZMod q) (Fintype.card (ProjLine q)) (ProjLine q) rfl σ (orderOf σ)
    (orderOf_pos σ) (pow_orderOf_eq_one σ) (free_toPermHom_torus q α)
  rwa [hcard] at hdvd

theorem charpoly_ind_torus (K : Type*) [Field K] (α : (GaloisField q 2)ˣ) :
    LinearMap.charpoly (ind q K (torus q α)) =
      (X ^ orderOf (MulAction.toPermHom (GL2 q) (ProjLine q) (torus q α)) - 1) ^
        ((q + 1) / orderOf (MulAction.toPermHom (GL2 q) (ProjLine q) (torus q α))) := by
  classical
  set σ : Equiv.Perm (ProjLine q) := MulAction.toPermHom (GL2 q) (ProjLine q) (torus q α) with hσ
  have hind : ind q K (torus q α) = permLin K σ := by
    rw [Representation.ofMulActionFinsupp_def]; rfl
  haveI : Fintype (ProjLine q) := Fintype.ofFinite _
  have hcard : Fintype.card (ProjLine q) = q + 1 := by rw [← Nat.card_eq_fintype_card, card_projLine]
  have hm : 0 < orderOf σ := orderOf_pos σ
  have hfree := free_toPermHom_torus q α
  obtain ⟨hpoly, -⟩ := charpoly_permLin_of_free (K := K) (Fintype.card (ProjLine q)) (ProjLine q) rfl σ (orderOf σ) hm
    (pow_orderOf_eq_one σ) hfree
  rw [hind, hpoly, hcard]

end CuspidalType.IndTorus

theorem solution
    (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] (α : (GaloisField q 2)ˣ) :
    LinearMap.charpoly (ind q K (torus q α)) =
      (X ^ orderOf (MulAction.toPermHom (GL2 q) (ProjLine q) (torus q α)) - 1) ^
        ((q + 1) / orderOf (MulAction.toPermHom (GL2 q) (ProjLine q) (torus q α))) :=
  CuspidalType.IndTorus.charpoly_ind_torus q K α

end S_CuspidalType_charpoly_ind_torus_eq_X_pow_orderOf_sub_one_pow
end P2MW
export P2MW.S_CuspidalType_charpoly_ind_torus_eq_X_pow_orderOf_sub_one_pow (solution)
