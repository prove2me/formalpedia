-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_comp_frobenius_act_frobenius_varpi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/1701b647-e223-5381-829d-735a54dad402

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isODHom_map_iterateFrobenius_comp_X_pow_eq_act_pow
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_map_of_field
import Theorems.Thm_WittVector_ringHom_map_frobenius_of_finite
import Theorems.Thm_MvFormalGroup_Hom_exists_finrank_quotient_span_range_map_eq_prime_pow_of_isComm
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_map_of_bijective
import Theorems.Thm_MvPowerSeries_span_range_X_eq_ker_constantCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_comp_frobenius_act_frobenius_varpi
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

universe u

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace R4PiTranslate

open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff coeff
  subst_X map_subst constantCoeff_X constantCoeff_subst_eq_zero)

variable {p : ℕ} [Fact p.Prime]

section Zp2

theorem frobenius_frobenius (a : Zp2 p) :
    WittVector.frobenius (WittVector.frobenius a) = a := by
  ext n
  haveI : Fintype (GaloisField p 2) := Fintype.ofFinite _
  rw [WittVector.coeff_frobenius_charP, WittVector.coeff_frobenius_charP, ← pow_mul]
  have hcard : Fintype.card (GaloisField p 2) = p ^ 2 := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p 2 two_ne_zero
  have : p * p = Fintype.card (GaloisField p 2) := by rw [hcard, pow_two]
  rw [this, FiniteField.pow_card]

theorem frobenius_bijective_Zp2 :
    Function.Bijective (WittVector.frobenius : Zp2 p → Zp2 p) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨WittVector.frobenius, frobenius_frobenius, frobenius_frobenius⟩

end Zp2

section FrobTwist

variable {B : Type u} [CommRing B] {B' : Type u} [CommRing B']

private noncomputable def _root_.R4PiTranslate.frobTwist (X : FormalODModule p B) : FormalODModule p B where
  F := X.F
  isComm := X.isComm
  act a := X.act (WittVector.frobenius a)
  varpi := X.varpi
  isLawHom_act a := X.isLawHom_act _
  isLawHom_varpi := X.isLawHom_varpi
  act_one := by rw [map_one, X.act_one]
  act_mul a b := by rw [map_mul, X.act_mul]
  act_add a b := by rw [map_add, X.act_add]
  varpi_comp_varpi := by rw [X.varpi_comp_varpi, map_natCast]
  varpi_comp_act a := X.varpi_comp_act _

p2m_export "R4PiTranslate" "frobTwist"
@[scoped simp] theorem frobTwist_F (X : FormalODModule p B) : (frobTwist X).F = X.F := rfl
@[scoped simp] theorem frobTwist_act (X : FormalODModule p B) (a : Zp2 p) :
    (frobTwist X).act a = X.act (WittVector.frobenius a) := rfl
@[scoped simp] theorem frobTwist_varpi (X : FormalODModule p B) : (frobTwist X).varpi = X.varpi := rfl

theorem frobTwist_map (X : FormalODModule p B) (f : B →+* B') :
    (frobTwist X).map f = frobTwist (X.map f) :=
  FormalODModule.ext' rfl rfl rfl

theorem IsODHom.frobTwist {X Y : FormalODModule p B} {φ : Series B}
    (h : FormalODModule.IsODHom X Y φ) :
    FormalODModule.IsODHom (frobTwist X) (frobTwist Y) φ :=
  ⟨h.1, fun a => h.2.1 (WittVector.frobenius a), h.2.2⟩

theorem isODHom_varpi_frobTwist (X : FormalODModule p B) :
    FormalODModule.IsODHom X (frobTwist X) X.varpi :=
  ⟨X.isLawHom_varpi, fun a => X.varpi_comp_act a, rfl⟩

theorem lieAct_frobTwist (X : FormalODModule p B) (a : Zp2 p) :
    (frobTwist X).lieAct a = X.lieAct (WittVector.frobenius a) := rfl

theorem lieZero_frobTwist (X : FormalODModule p B) (j : Zp2 p →+* B) :
    (frobTwist X).lieZero (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) = X.lieZero j := by
  apply le_antisymm
  · refine le_iInf fun b => ?_
    obtain ⟨a, rfl⟩ := (frobenius_bijective_Zp2 (p := p)).2 b
    exact iInf_le _ a
  · refine le_iInf fun a => ?_
    exact iInf_le _ (WittVector.frobenius a)

theorem lieOne_frobTwist (X : FormalODModule p B) (j : Zp2 p →+* B) :
    (frobTwist X).lieOne (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) = X.lieOne j := by
  apply le_antisymm
  · refine le_iInf fun b => ?_
    obtain ⟨a, rfl⟩ := (frobenius_bijective_Zp2 (p := p)).2 b
    refine (iInf_le _ a).trans (le_of_eq ?_)
    simp only [lieAct_frobTwist, RingHom.comp_apply, frobenius_frobenius]
  · refine le_iInf fun a => ?_
    refine (iInf_le _ (WittVector.frobenius a)).trans (le_of_eq ?_)
    simp only [lieAct_frobTwist, RingHom.comp_apply, frobenius_frobenius]

theorem isSpecial_frobTwist_iff (X : FormalODModule p B) (j : Zp2 p →+* B) :
    (frobTwist X).IsSpecial (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) ↔ X.IsSpecial j := by
  unfold FormalODModule.IsSpecial
  rw [lieZero_frobTwist, lieOne_frobTwist]

theorem hasHeight_frobTwist_iff (X : FormalODModule p B) (h : ℕ) :
    (frobTwist X).HasHeight h ↔ X.HasHeight h := by
  unfold FormalODModule.HasHeight
  rw [frobTwist_act, map_natCast]

end FrobTwist

section Kernel

variable {B : Type u} [CommRing B]

theorem comp_mem_span (ψ φ : Series B) (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (hφ : ∀ i, constantCoeff (φ i) = 0) (i : Fin 2) :
    (ψ.comp φ) i ∈ Ideal.span (Set.range φ) := by
  have hmem : ψ i ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) B)) := by
    rw [MvPowerSeries.span_range_X_eq_ker_constantCoeff]
    exact hψ i
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  have hS : HasSubst φ := hasSubst_of_constantCoeff_zero hφ
  show subst φ (ψ i) ∈ _
  rw [← hc, ← MvPowerSeries.coe_substAlgHom hS, map_sum]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [map_mul, MvPowerSeries.coe_substAlgHom hS, subst_X hS]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

theorem span_comp_le (ψ φ : Series B) (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (hφ : ∀ i, constantCoeff (φ i) = 0) :
    Ideal.span (Set.range (ψ.comp φ)) ≤ Ideal.span (Set.range φ) := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact comp_mem_span ψ φ hψ hφ i

theorem finite_kerAlgebra_of_comp (ψ φ : Series B) (hψ : ∀ i, constantCoeff (ψ i) = 0)
    (hφ : ∀ i, constantCoeff (φ i) = 0)
    (hfin : Module.Finite B (FormalODModule.KerAlgebra (ψ.comp φ))) :
    Module.Finite B (FormalODModule.KerAlgebra φ) := by
  let g : FormalODModule.KerAlgebra (ψ.comp φ) →ₐ[B] FormalODModule.KerAlgebra φ :=
    Ideal.Quotient.factorₐ B (span_comp_le ψ φ hψ hφ)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩
  exact Module.Finite.of_surjective g.toLinearMap hg

end Kernel

section Field

variable {κ : Type u} [Field κ] [CharP κ p]

theorem hasKernelOfDegree_varpi (Φ : FormalODModule p κ) (hΦ4 : Φ.HasHeight 4) :
    FormalODModule.HasKernelOfDegree Φ.varpi (p ^ 2) := by
  have hvarpi0 : ∀ i, constantCoeff (Φ.varpi i) = 0 := Φ.isLawHom_varpi.1
  have hpp : Φ.act (p : Zp2 p) = Φ.varpi.comp Φ.varpi := Φ.varpi_comp_varpi.symm

  have hfin : Module.Finite κ (FormalODModule.KerAlgebra Φ.varpi) := by
    have h4 := hΦ4.1
    rw [hpp] at h4
    exact finite_kerAlgebra_of_comp _ _ hvarpi0 hvarpi0 h4

  obtain ⟨h, hh⟩ :=
    MvFormalGroup.Hom.exists_finrank_quotient_span_range_map_eq_prime_pow_of_isComm p κ Φ.F Φ.F
      Φ.varpiEnd hfin
  have hvarpih : FormalODModule.HasKernelOfDegree Φ.varpi (p ^ h) :=
    ⟨hfin, inferInstance, fun κ' _ f' => hh κ' f'⟩

  have hcomp := CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp_map_of_field
    (RingHom.id κ) hvarpih hvarpi0 hvarpih
  rw [Series.map_ringHom_id, ← hpp] at hcomp
  have e1 := hcomp.2.2 κ (RingHom.id κ)
  have e2 := hΦ4.2.2 κ (RingHom.id κ)
  rw [e1, ← pow_add] at e2
  have hh2 : h + h = 4 := Nat.pow_right_injective (Fact.out : p.Prime).two_le e2
  have : h = 2 := by omega
  rw [this] at hvarpih
  exact hvarpih

end Field

section Residue

variable (p)
variable {k : Type u} [Field k] [CharP k p] [PerfectRing k p] {B : Type u} [CommRing B]

omit [PerfectRing k p] in

theorem constantCoeff_frobenius (x : WittVector p k) :
    WittVector.constantCoeff (WittVector.frobenius x) = (WittVector.constantCoeff x) ^ p :=
  WittVector.coeff_frobenius_charP p x 0

theorem residueMap_comp_frobenius (ψ : WittVector p k →+* B) :
    residueMap (p := p) (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) =
      ((((residueMap (p := p) ψ).comp
          (WittVector.quotientPEquiv (p := p) (k := k)).symm.toRingHom).comp
          (iterateFrobenius k p 1)).comp
        (WittVector.quotientPEquiv (p := p) (k := k)).toRingHom) := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  have h1 : (WittVector.quotientPEquiv (p := p) (k := k))
      (Ideal.Quotient.mk (pIdeal p (WittVector p k)) x) = WittVector.constantCoeff x := rfl
  have h2 : (WittVector.quotientPEquiv (p := p) (k := k))
      (Ideal.Quotient.mk (pIdeal p (WittVector p k)) (WittVector.frobenius x)) =
        WittVector.constantCoeff (WittVector.frobenius x) := rfl
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, h1,
    iterateFrobenius_def, pow_one]
  rw [← constantCoeff_frobenius, ← h2, RingEquiv.symm_apply_apply]
  rfl

end Residue

section Main

variable (p)

theorem main (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k))) (hΦ4 : Φ.HasHeight 4)
    (B : Type u) [CommRing B] (ψ : WittVector p k →+* B) (t : Rigidified p Φ B)
    (ht : t.IsAdmissible ι ψ) :
    ∃ t' : Rigidified p Φ B,
      t'.IsAdmissible ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) ∧
      t'.X.F = t.X.F ∧ t'.X.varpi = t.X.varpi ∧ (∀ a, t'.X.act a = t.X.act (WittVector.frobenius a)) ∧
      ∃ c : ℕ,
        (t.Xbar.act ((p : Zp2 p) ^ (c + t.n))).comp
            (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal p B)) ^ p) =
          (t.Xbar.act ((p : Zp2 p) ^ (c + t'.n))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ))) := by
  classical

  let Fr : WittVector p k →+* WittVector p k := WittVector.frobenius
  let mkB : B →+* B ⧸ pIdeal p B := Ideal.Quotient.mk (pIdeal p B)
  let f : (WittVector p k ⧸ pIdeal p (WittVector p k)) →+* B ⧸ pIdeal p B := residueMap ψ
  let e₀ : (WittVector p k ⧸ pIdeal p (WittVector p k)) ≃+* k := WittVector.quotientPEquiv
  let fk : k →+* B ⧸ pIdeal p B := f.comp e₀.symm.toRingHom
  have hfk : fk.comp e₀.toRingHom = f := by
    ext x; simp [fk]
  let Φk : FormalODModule p k := Φ.map e₀.toRingHom
  have hΦk4 : Φk.HasHeight 4 :=
    CerednikDrinfeld.FormalODModule.HasKernelOfDegree.map_of_bijective e₀.toRingHom e₀.bijective hΦ4
  have hΦf : Φ.map f = Φk.map fk := by
    rw [FormalODModule.map_map, hfk]

  obtain ⟨V, hV, hVF, hVdeg⟩ :=
    CerednikDrinfeld.FormalODModule.exists_isODHom_map_iterateFrobenius_comp_X_pow_eq_act_pow Φk hΦk4 1
  have hV0 : ∀ i, constantCoeff (V i) = 0 := hV.constantCoeff
  have hvarpik0 : ∀ i, constantCoeff (Φk.varpi i) = 0 := Φk.isLawHom_varpi.1
  have hvarpideg : FormalODModule.HasKernelOfDegree Φk.varpi (p ^ 2) := hasKernelOfDegree_varpi Φk hΦk4

  have hgdeg : FormalODModule.HasKernelOfDegree (Φk.varpi.comp V) (p ^ 2 * p ^ (2 * 1)) := by
    have h := CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp_map_of_field
      (RingHom.id k) hvarpideg hV0 hVdeg
    rwa [Series.map_ringHom_id] at h
  have hg0 : ∀ i, constantCoeff ((Φk.varpi.comp V) i) = 0 := Series.constantCoeff_comp hvarpik0 hV0

  let ρ' : Series (B ⧸ pIdeal p B) := t.ρ.comp ((Φk.varpi.comp V).map fk)
  have hρ'deg : FormalODModule.HasKernelOfDegree ρ' (p ^ (4 * (t.n + 1))) := by
    have h := CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp_map_of_field fk ht.2.2.2 hg0 hgdeg
    have e : p ^ (4 * t.n) * (p ^ 2 * p ^ (2 * 1)) = p ^ (4 * (t.n + 1)) := by ring
    rwa [e] at h

  have hρ0 : ∀ i, constantCoeff (t.ρ i) = 0 := ht.constantCoeff_ρ
  have hVR0 : ∀ i, constantCoeff ((V.map fk) i) = 0 := fun i => by
    show constantCoeff (MvPowerSeries.map fk (V i)) = 0
    rw [MvPowerSeries.constantCoeff_map, hV0, map_zero]
  have hvarpiR0 : ∀ i, constantCoeff ((Φk.varpi.map fk) i) = 0 := fun i => by
    show constantCoeff (MvPowerSeries.map fk (Φk.varpi i)) = 0
    rw [MvPowerSeries.constantCoeff_map, hvarpik0, map_zero]
  have hFrob0 : ∀ i, constantCoeff
      ((fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal p B)) ^ p) i) = 0 := fun i => by
    show constantCoeff ((MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal p B)) ^ p) = 0
    rw [map_pow, constantCoeff_X, zero_pow (Fact.out : p.Prime).ne_zero]
  have hact0 : ∀ (Y : FormalODModule p (B ⧸ pIdeal p B)) (a : Zp2 p) (i : Fin 2),
      constantCoeff (Y.act a i) = 0 := fun Y a => (Y.isLawHom_act a).1
  have hgR : (Φk.varpi.comp V).map fk = (Φk.varpi.map fk).comp (V.map fk) :=
    Series.map_comp fk _ _ hV0

  have h1 : FormalODModule.IsODHom ((Φk.map (iterateFrobenius k p 1)).map fk) (Φk.map fk) (V.map fk) :=
    hV.map fk
  have h2 : FormalODModule.IsODHom (Φk.map fk) (frobTwist (Φk.map fk)) (Φk.varpi.map fk) :=
    isODHom_varpi_frobTwist (Φk.map fk)
  have h3 : FormalODModule.IsODHom (frobTwist (Φk.map fk)) (frobTwist t.Xbar) t.ρ := by
    have h : FormalODModule.IsODHom (Φ.map f) t.Xbar t.ρ := ht.2.2.1
    rw [hΦf] at h
    exact IsODHom.frobTwist h
  have h32 := h3.comp h2
  have hρ' : FormalODModule.IsODHom ((Φk.map (iterateFrobenius k p 1)).map fk) (frobTwist t.Xbar) ρ' := by
    have h := h32.comp h1
    have e : (t.ρ.comp (Φk.varpi.map fk)).comp (V.map fk) = ρ' := by
      show _ = t.ρ.comp ((Φk.varpi.comp V).map fk)
      rw [hgR, Series.comp_assoc _ _ _ hvarpiR0 hVR0]
    rw [e] at h
    exact h

  refine ⟨⟨frobTwist t.X, t.n + 1, ρ'⟩, ⟨?_, ?_, ?_⟩, rfl, rfl, fun a => rfl, 0, ?_⟩
  ·
    show (frobTwist t.X).IsSpecial ((ψ.comp Fr).comp ι)
    have hι : (ψ.comp Fr).comp ι = (ψ.comp ι).comp (WittVector.frobenius : Zp2 p →+* Zp2 p) := by
      ext a
      simp only [RingHom.comp_apply, Fr]
      rw [WittVector.ringHom_map_frobenius_of_finite p ι a]
    rw [hι, isSpecial_frobTwist_iff]
    exact ht.1
  ·
    exact (hasHeight_frobTwist_iff _ _).mpr ht.2.1
  ·
    show FormalODModule.IsIsogenyOfHeight (Φ.map (residueMap (ψ.comp Fr)))
      ((frobTwist t.X).map mkB) ρ' (4 * (t.n + 1))
    have hsrc : Φ.map (residueMap (ψ.comp Fr)) = (Φk.map (iterateFrobenius k p 1)).map fk := by
      rw [residueMap_comp_frobenius p ψ, ← FormalODModule.map_map, ← FormalODModule.map_map]
    rw [hsrc, frobTwist_map]
    exact ⟨hρ', hρ'deg⟩
  ·
    show (t.Xbar.act ((p : Zp2 p) ^ (0 + t.n))).comp
        (ρ'.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal p B)) ^ p) =
      (t.Xbar.act ((p : Zp2 p) ^ (0 + (t.n + 1)))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ)))

    have hVFR : (V.map fk).comp (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal p B)) ^ p) =
        (Φ.map f).act (p : Zp2 p) := by
      have h := congrArg (Series.map fk) hVF
      have hF0 : ∀ i, constantCoeff ((fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) k) ^ (p ^ 1)) i) = 0 :=
        fun i => by
          show constantCoeff ((MvPowerSeries.X i : MvPowerSeries (Fin 2) k) ^ (p ^ 1)) = 0
          rw [map_pow, constantCoeff_X, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]
      rw [Series.map_comp fk _ _ hF0] at h
      have hFR : Series.map fk (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) k) ^ (p ^ 1)) =
          fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal p B)) ^ p := by
        funext i
        show MvPowerSeries.map fk ((MvPowerSeries.X i) ^ (p ^ 1)) = _
        rw [map_pow, MvPowerSeries.map_X, pow_one]
      rw [hFR] at h
      rw [h, hΦf, pow_one]
      rfl
    have hvarpiR : Φ.varpi.map (residueMap ψ) = Φk.varpi.map fk := by
      show (Φ.map f).varpi = (Φk.map fk).varpi
      rw [hΦf]

    have hlin : (t.ρ.comp (Φk.varpi.map fk)).comp ((Φ.map f).act (p : Zp2 p)) =
        (t.Xbar.act (p : Zp2 p)).comp (t.ρ.comp (Φk.varpi.map fk)) := by
      have h := h32.2.1 (p : Zp2 p)
      rw [frobTwist_act, map_natCast, ← hΦf] at h
      exact h
    have hrhovarpi0 : ∀ i, constantCoeff ((t.ρ.comp (Φk.varpi.map fk)) i) = 0 :=
      Series.constantCoeff_comp hρ0 hvarpiR0

    have step : ρ'.comp (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal p B)) ^ p) =
        (t.Xbar.act (p : Zp2 p)).comp (t.ρ.comp (Φk.varpi.map fk)) := by
      show (t.ρ.comp ((Φk.varpi.comp V).map fk)).comp _ = _
      rw [hgR, ← Series.comp_assoc _ _ _ hvarpiR0 hVR0,
        Series.comp_assoc _ _ _ hVR0 hFrob0, hVFR, hlin]
    rw [step, ← Series.comp_assoc _ _ _ (hact0 _ _) hrhovarpi0, zero_add, zero_add, hvarpiR,
      FormalODModule.act_pow_add, pow_one]

end Main

end R4PiTranslate
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_comp_frobenius_act_frobenius_varpi.R4PiTranslate"

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k))) (hΦ4 : Φ.HasHeight 4)
    (B : Type u) [CommRing B] (ψ : WittVector p k →+* B) (t : Rigidified p Φ B)
    (ht : t.IsAdmissible ι ψ) :
    ∃ t' : Rigidified p Φ B,
      t'.IsAdmissible ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) ∧
      t'.X.F = t.X.F ∧ t'.X.varpi = t.X.varpi ∧ (∀ a, t'.X.act a = t.X.act (WittVector.frobenius a)) ∧
      ∃ c : ℕ,
        (t.Xbar.act ((p : Zp2 p) ^ (c + t.n))).comp
            (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal p B)) ^ p) =
          (t.Xbar.act ((p : Zp2 p) ^ (c + t'.n))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ))) :=
  R4PiTranslate.main p k ι Φ hΦ4 B ψ t ht

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_comp_frobenius_act_frobenius_varpi
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_comp_frobenius_act_frobenius_varpi (solution)
