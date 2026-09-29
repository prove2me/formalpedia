-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_lieCoordinates_mul_eq_of_isProrepresentedBy_deformations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/b7851989-6d22-50ae-b52a-a2aee93041bb

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecial_and_hasHeight_four_of_isIso_of_isArtinianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_lieCoordinates_mul_eq_of_isProrepresentedBy_deformations
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal IsLocalRing
open scoped Matrix

namespace DDF3a

section Generic
variable {q : ℕ} [Fact q.Prime]
variable {B : Type} [CommRing B] {B' : Type} [CommRing B']

open MvPowerSeries in
theorem linearPart_comp (ψ φ : Series B) (hφ : ∀ i, constantCoeff (φ i) = 0) :
    MvFormalGroup.linearPart (ψ.comp φ) = MvFormalGroup.linearPart ψ * MvFormalGroup.linearPart φ :=
  MvFormalGroup.linearPart_subst hφ ψ

theorem linearPart_map (f : B →+* B') (φ : Series B) :
    MvFormalGroup.linearPart (φ.map f) = (MvFormalGroup.linearPart φ).map f := by
  ext i j
  simp [MvFormalGroup.linearPart, Series.map, MvPowerSeries.coeff_map]

theorem linearPart_id : MvFormalGroup.linearPart (Series.id B) = 1 := by
  unfold Series.id
  exact MvFormalGroup.linearPart_X

theorem mem_lieZero_iff (j : Zp2 q →+* B) (X : FormalODModule q B) (m : X.Lie) :
    m ∈ X.lieZero j ↔ ∀ a, MvFormalGroup.linearPart (X.act a) *ᵥ m = j a • m := by
  simp only [FormalODModule.lieZero, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, FormalODModule.lieAct, Matrix.mulVecLin_apply]

theorem mem_lieOne_iff (j : Zp2 q →+* B) (X : FormalODModule q B) (m : X.Lie) :
    m ∈ X.lieOne j ↔
      ∀ a, MvFormalGroup.linearPart (X.act a) *ᵥ m = j (WittVector.frobenius a) • m := by
  simp only [FormalODModule.lieOne, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, FormalODModule.lieAct, Matrix.mulVecLin_apply]

theorem frob_frob (a : Zp2 q) : WittVector.frobenius (WittVector.frobenius a) = a := by
  letI : Fintype (GaloisField q 2) := Fintype.ofFinite _
  ext n
  simp only [WittVector.coeff_frobenius_charP]
  rw [← pow_mul, ← pow_two, ← GaloisField.card q 2 two_ne_zero, Nat.card_eq_fintype_card,
    FiniteField.pow_card]

theorem linearPart_varpi_mul_self (X : FormalODModule q B) :
    MvFormalGroup.linearPart X.varpi * MvFormalGroup.linearPart X.varpi =
      ((q : ℕ) : B) • (1 : Matrix (Fin 2) (Fin 2) B) := by
  have h := congrArg MvFormalGroup.linearPart X.varpi_comp_varpi
  rw [linearPart_comp _ _ X.isLawHom_varpi.1, FormalODModule.act_natCast, MvFormalGroup.linearPart_nthSeries] at h
  rw [h]
  ext i i'
  simp [Matrix.smul_apply, nsmul_eq_mul]

theorem linearPart_varpi_mul_act (X : FormalODModule q B) (a : Zp2 q) :
    MvFormalGroup.linearPart X.varpi * MvFormalGroup.linearPart (X.act a) =
      MvFormalGroup.linearPart (X.act (WittVector.frobenius a)) * MvFormalGroup.linearPart X.varpi := by
  have h := congrArg MvFormalGroup.linearPart (X.varpi_comp_act a)
  rwa [linearPart_comp _ _ (X.isLawHom_act a).1, linearPart_comp _ _ X.isLawHom_varpi.1] at h

theorem Hom.linearPart_mul_act {X Y : FormalODModule q B} (w : X.Hom Y) (a : Zp2 q) :
    MvFormalGroup.linearPart w.toSeries * MvFormalGroup.linearPart (X.act a) =
      MvFormalGroup.linearPart (Y.act a) * MvFormalGroup.linearPart w.toSeries := by
  have h := congrArg MvFormalGroup.linearPart (w.isODHom.2.1 a)
  rwa [linearPart_comp _ _ (X.isLawHom_act a).1, linearPart_comp _ _ w.isODHom.1.1] at h

theorem Hom.linearPart_mul_varpi {X Y : FormalODModule q B} (w : X.Hom Y) :
    MvFormalGroup.linearPart w.toSeries * MvFormalGroup.linearPart X.varpi =
      MvFormalGroup.linearPart Y.varpi * MvFormalGroup.linearPart w.toSeries := by
  have h := congrArg MvFormalGroup.linearPart w.isODHom.2.2
  rwa [linearPart_comp _ _ X.isLawHom_varpi.1, linearPart_comp _ _ w.isODHom.1.1] at h

theorem Hom.exists_mul_linearPart_eq_one {X Y : FormalODModule q B} (w : X.Hom Y) (hw : w.IsIso) :
    ∃ W' : Matrix (Fin 2) (Fin 2) B, W' * MvFormalGroup.linearPart w.toSeries = 1 := by
  obtain ⟨g, hg, -⟩ := hw
  refine ⟨MvFormalGroup.linearPart g.toSeries, ?_⟩
  have h := congrArg (fun f : X.Hom X => MvFormalGroup.linearPart f.toSeries) hg
  simp only [FormalODModule.Hom.comp] at h
  rw [linearPart_comp _ _ w.isODHom.1.1] at h
  rw [h]
  exact linearPart_id

theorem Hom.isIso_cast {X X' Y : FormalODModule q B} (h : X = X') (w : X.Hom Y) (hw : w.IsIso) :
    (h ▸ w : X'.Hom Y).IsIso := by
  subst h
  exact hw

end Generic

end DDF3a

namespace DDF3a

section Trunc
variable {q : ℕ} [Fact q.Prime]

theorem eq_zero_of_forall_mk_pow_eq_zero {R : Type} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (x : R)
    (h : ∀ n : ℕ, Ideal.Quotient.mk (maximalIdeal R ^ n) x = 0) : x = 0 := by
  refine IsHausdorff.haus (show IsHausdorff (maximalIdeal R) R from inferInstance) x fun n => ?_
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
  exact Ideal.Quotient.eq_zero_iff_mem.mp (h n)

theorem isLocalRing_quotient {R : Type} [CommRing R] [IsLocalRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    IsLocalRing (R ⧸ I) :=
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

theorem isArtinianRing_quotient_pow {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (n : ℕ) (hn : maximalIdeal R ^ n ≠ ⊤) :
    haveI := isLocalRing_quotient (maximalIdeal R ^ n) hn
    IsArtinianRing (R ⧸ maximalIdeal R ^ n) := by
  haveI := isLocalRing_quotient (maximalIdeal R ^ n) hn
  rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
  refine ⟨n, ?_⟩
  have hle : maximalIdeal (R ⧸ maximalIdeal R ^ n) ≤ (maximalIdeal R).map (Ideal.Quotient.mk _) := by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    refine Ideal.mem_map_of_mem _ ?_
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    exact fun hy => hx (hy.map _)
  rw [show (0 : Ideal (R ⧸ maximalIdeal R ^ n)) = ⊥ from rfl, eq_bot_iff]
  calc maximalIdeal (R ⧸ maximalIdeal R ^ n) ^ n
      ≤ ((maximalIdeal R).map (Ideal.Quotient.mk (maximalIdeal R ^ n))) ^ n := Ideal.pow_right_mono hle n
    _ = (maximalIdeal R ^ n).map (Ideal.Quotient.mk (maximalIdeal R ^ n)) := (Ideal.map_pow _ _ n).symm
    _ = ⊥ := Ideal.map_quotient_self _

variable (Onr : Type) [CommRing Onr] [IsLocalRing Onr]
  (ι : Zp2 q →+* Onr) (X₀ : SpecialFormalODModule q ((IsLocalRing.residue Onr).comp ι))
  (R : Type) [CommRing R] [IsLocalRing R] [Algebra Onr R]
  (resR : R →+* IsLocalRing.ResidueField Onr) (hresR : resR.comp (algebraMap Onr R) = IsLocalRing.residue Onr)
  (Xu : FormalODModule q R) (wu : (Xu.map resR).Hom X₀.toFormalODModule) (hwu : wu.IsIso)

include hresR hwu in

theorem isSpecial_map_mk (I : Ideal R) (hI : I ≤ RingHom.ker resR) (hI' : I ≠ ⊤)
    (hart : haveI := isLocalRing_quotient I hI'; IsArtinianRing (R ⧸ I)) :
    (Xu.map (Ideal.Quotient.mk I)).IsSpecial ((algebraMap Onr (R ⧸ I)).comp ι) := by
  haveI := isLocalRing_quotient I hI'
  haveI := hart

  let resI : R ⧸ I →+* ResidueField Onr := Ideal.Quotient.lift I resR (fun a ha => hI ha)
  have hcomp : resI.comp (Ideal.Quotient.mk I) = resR := RingHom.ext fun x => rfl
  have hs : Function.Surjective resI := by
    intro y
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨Ideal.Quotient.mk I (algebraMap Onr R o), by
      change resR (algebraMap Onr R o) = IsLocalRing.residue Onr o
      rw [← RingHom.comp_apply, hresR]⟩
  have hc : resI.comp (algebraMap Onr (R ⧸ I)) = IsLocalRing.residue Onr := by
    ext o
    change resR (algebraMap Onr R o) = IsLocalRing.residue Onr o
    rw [← RingHom.comp_apply, hresR]
  have hmap : Xu.map resR = (Xu.map (Ideal.Quotient.mk I)).map resI := by
    rw [FormalODModule.map_map, hcomp]
  exact (CerednikDrinfeld.FormalODModule.isSpecial_and_hasHeight_four_of_isIso_of_isArtinianRing Onr ι X₀
    (R ⧸ I) resI hs hc (Xu.map (Ideal.Quotient.mk I)) (hmap ▸ wu) (Hom.isIso_cast hmap wu hwu)).1

include hresR hwu in

theorem isSpecial_map_resR [IsNoetherianRing R] :
    (Xu.map resR).IsSpecial ((IsLocalRing.residue Onr).comp ι) := by
  have hmap : Xu.map resR = (Xu.map resR).map (RingHom.id _) := by
    rw [FormalODModule.map_map, RingHom.id_comp]
  have h := (CerednikDrinfeld.FormalODModule.isSpecial_and_hasHeight_four_of_isIso_of_isArtinianRing Onr ι X₀
    (ResidueField Onr) (RingHom.id _) Function.surjective_id (by ext; rfl) (Xu.map resR) (hmap ▸ wu)
    (Hom.isIso_cast hmap wu hwu)).1
  rwa [IsLocalRing.ResidueField.algebraMap_eq] at h

end Trunc

end DDF3a

namespace DDF3a

section MatrixLemmas
variable {R S : Type} [CommRing R] [CommRing S]

theorem map_sub_smul_one (f : R →+* S) (A : Matrix (Fin 2) (Fin 2) R) (c : R) :
    (A - c • (1 : Matrix (Fin 2) (Fin 2) R)).map f = A.map f - f c • (1 : Matrix (Fin 2) (Fin 2) S) := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

theorem sub_smul_one_mulVec (A : Matrix (Fin 2) (Fin 2) R) (c : R) (v : Fin 2 → R) :
    (A - c • (1 : Matrix (Fin 2) (Fin 2) R)) *ᵥ v = A *ᵥ v - c • v := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem eq_zero_of_forall_mulVec_eq_zero (A : Matrix (Fin 2) (Fin 2) R) (h : ∀ v, A *ᵥ v = 0) : A = 0 := by
  have : Matrix.toLin' A = 0 := LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v
  exact (LinearEquiv.map_eq_zero_iff Matrix.toLin').mp this

theorem map_mulVec_apply (f : R →+* S) (A : Matrix (Fin 2) (Fin 2) R) (v : Fin 2 → R) (i : Fin 2) :
    f ((A *ᵥ v) i) = (A.map f *ᵥ (f ∘ v)) i :=
  RingHom.map_mulVec f A v i

theorem funext_fin_two {X : Type} {f g : Fin 2 → X} (h0 : f 0 = g 0) (h1 : f 1 = g 1) : f = g := by
  funext i
  exact (Fin.forall_fin_two (p := fun i => f i = g i)).mpr ⟨h0, h1⟩ i

theorem exists_smul_of_det_eq_zero {k : Type} [Field k] (v w : Fin 2 → k) (hv : v ≠ 0)
    (h : v 0 * w 1 - v 1 * w 0 = 0) : ∃ c : k, w = c • v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1; apply hv
      exact funext_fin_two (by simp [h0]) (by simp [h1])
    have hw0 : w 0 = 0 := by
      rw [h0, zero_mul, zero_sub, neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_left h1
    refine ⟨w 1 / v 1, funext_fin_two ?_ ?_⟩
    · simp [h0, hw0]
    · simp [div_mul_cancel₀ _ h1]
  · refine ⟨w 0 / v 0, funext_fin_two ?_ ?_⟩
    · simp [div_mul_cancel₀ _ h0]
    · simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination h

theorem existsUnique_coords (e₀ e₁ : Fin 2 → R) (δinv : R)
    (hδ : δinv * (e₀ 0 * e₁ 1 - e₀ 1 * e₁ 0) = 1) (m : Fin 2 → R) :
    ∃! c : R × R, m = c.1 • e₀ + c.2 • e₁ := by
  refine ⟨(δinv * (m 0 * e₁ 1 - m 1 * e₁ 0), δinv * (e₀ 0 * m 1 - e₀ 1 * m 0)), ?_, ?_⟩
  · refine funext_fin_two ?_ ?_
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(m 0)) * hδ
    · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(m 1)) * hδ
  · rintro ⟨c₁, c₂⟩ hc
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h0 h1
    ext
    · simp only
      linear_combination (-c₁) * hδ - δinv * e₁ 1 * h0 + δinv * e₁ 0 * h1
    · simp only
      linear_combination (-c₂) * hδ + δinv * e₀ 1 * h0 - δinv * e₀ 0 * h1

end MatrixLemmas

end DDF3a

open DDF3a in
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
theorem solution
    {q : ℕ} [Fact q.Prime]
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [IsDiscreteValuationRing Onr] [CharZero Onr] [Algebra ℤ_[q] Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}) Onr)
    (hOnr_max : (Ideal.span {algebraMap ℤ_[q] Onr (q : ℤ_[q])}).IsMaximal)
    [IsAlgClosed (IsLocalRing.ResidueField Onr)]
    (ι : Zp2 q →+* Onr) (X₀ : SpecialFormalODModule q ((IsLocalRing.residue Onr).comp ι))
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra Onr R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (resR : R →+* IsLocalRing.ResidueField Onr) (hresR : resR.comp (algebraMap Onr R) = IsLocalRing.residue Onr)
    (Xu : FormalODModule q R) (wu : (Xu.map resR).Hom X₀.toFormalODModule) (hwu : wu.IsIso)
    (hPRO : (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra Onr A]
            (resA : A →+* IsLocalRing.ResidueField Onr), Function.Surjective resA →
            resA.comp (algebraMap Onr A) = IsLocalRing.residue Onr →
          ∀ (X : FormalODModule q A), X.IsSpecial ((algebraMap Onr A).comp ι) → X.HasHeight 4 →
          ∀ (w : (X.map resA).Hom X₀.toFormalODModule), w.IsIso →
            ∃! χ : R →ₐ[Onr] A, resA.comp χ.toRingHom = resR ∧
              ∃ v : (Xu.map χ.toRingHom).Hom X, v.IsIso ∧
                (w.comp (v.map resA)).toSeries = wu.toSeries))
    (hnode₀ : (∀ m ∈ X₀.toFormalODModule.lieZero ((IsLocalRing.residue Onr).comp ι), Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0))
    (hnode₁ : (∀ m ∈ X₀.toFormalODModule.lieOne ((IsLocalRing.residue Onr).comp ι), Matrix.mulVecLin (MvFormalGroup.linearPart X₀.varpi) m = 0)) :
    ∃ (e₀ e₁ : Xu.Lie) (u v : R),
      e₀ ∈ Xu.lieZero ((algebraMap Onr R).comp ι) ∧ e₁ ∈ Xu.lieOne ((algebraMap Onr R).comp ι) ∧
      (∀ m : Xu.Lie, ∃! c : R × R, m = c.1 • e₀ + c.2 • e₁) ∧
      Matrix.mulVecLin (MvFormalGroup.linearPart Xu.varpi) e₀ = u • e₁ ∧ Matrix.mulVecLin (MvFormalGroup.linearPart Xu.varpi) e₁ = v • e₀ ∧
      u * v = algebraMap Onr R ((q : ℕ) : Onr) ∧
      u ∈ IsLocalRing.maximalIdeal R ∧ v ∈ IsLocalRing.maximalIdeal R := by
  classical

  have hsurj : Function.Surjective resR := by
    intro y; obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨algebraMap Onr R o, by rw [← RingHom.comp_apply, hresR]⟩
  have hker : RingHom.ker resR = maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective resR hsurj)
  have hres_jR : ∀ a, resR (algebraMap Onr R (ι a)) = (IsLocalRing.residue Onr) (ι a) := fun a => by
    rw [← RingHom.comp_apply, hresR]

  have hα : ∃ α : Zp2 q, (IsLocalRing.residue Onr) (ι α) ≠ (IsLocalRing.residue Onr) (ι (WittVector.frobenius α)) := by
    by_contra h
    push Not at h
    have hEq : X₀.toFormalODModule.lieZero ((IsLocalRing.residue Onr).comp ι) =
        X₀.toFormalODModule.lieOne ((IsLocalRing.residue Onr).comp ι) := by
      ext m
      rw [mem_lieZero_iff, mem_lieOne_iff]
      exact forall_congr' fun a => by rw [RingHom.comp_apply, RingHom.comp_apply, h a]
    have hc := X₀.isSpecial.1
    rw [hEq] at hc
    have h1 : X₀.toFormalODModule.lieOne ((IsLocalRing.residue Onr).comp ι) = ⊥ := by simpa using hc.inf_eq_bot
    have h2 : X₀.toFormalODModule.lieOne ((IsLocalRing.residue Onr).comp ι) = ⊤ := by simpa using hc.sup_eq_top
    exact absurd (h1.symm.trans h2) bot_ne_top
  obtain ⟨α, hα⟩ := hα
  set d : R := algebraMap Onr R (ι α) - algebraMap Onr R (ι (WittVector.frobenius α)) with hd
  have hresd : resR d ≠ 0 := by
    rw [hd, map_sub, hres_jR, hres_jR]; exact sub_ne_zero.mpr hα
  have hdunit : IsUnit d := by
    by_contra hnu
    have : d ∈ maximalIdeal R := hnu
    rw [← hker, RingHom.mem_ker] at this
    exact hresd this
  obtain ⟨dinv, hdinv⟩ := hdunit.exists_left_inv

  set B₀ : Matrix (Fin 2) (Fin 2) R :=
    MvFormalGroup.linearPart (Xu.act α) - algebraMap Onr R (ι (WittVector.frobenius α)) • 1 with hB₀
  set B₁ : Matrix (Fin 2) (Fin 2) R := MvFormalGroup.linearPart (Xu.act α) - algebraMap Onr R (ι α) • 1 with hB₁
  have hB₀₁ : ∀ v : Fin 2 → R, B₀ *ᵥ v = B₁ *ᵥ v + d • v := by
    intro v
    simp only [hB₀, hB₁, hd, sub_smul_one_mulVec, sub_smul]
    abel
  have hcomm : B₀ * B₁ = B₁ * B₀ := by
    simp only [hB₀, hB₁, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_one, one_mul, smul_sub,
      smul_smul]
    rw [mul_comm (algebraMap Onr R (ι α)) (algebraMap Onr R (ι (WittVector.frobenius α)))]
    abel

  have htrunc : ∀ n : ℕ, 0 < n →
      (Xu.map (Ideal.Quotient.mk (maximalIdeal R ^ n))).IsSpecial
        ((algebraMap Onr (R ⧸ maximalIdeal R ^ n)).comp ι) := by
    intro n hn
    have hle : maximalIdeal R ^ n ≤ RingHom.ker resR := by
      rw [hker]; exact Ideal.pow_le_self hn.ne'
    have hne : maximalIdeal R ^ n ≠ ⊤ := fun h =>
      (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (h ▸ Ideal.pow_le_self hn.ne'))
    exact isSpecial_map_mk Onr ι X₀ R resR hresR Xu wu hwu _ hle hne (isArtinianRing_quotient_pow n hne)

  have hN : B₀ * B₁ = 0 := by
    apply eq_zero_of_forall_mulVec_eq_zero
    intro v
    funext i
    apply eq_zero_of_forall_mk_pow_eq_zero
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simp)
    · set πn := Ideal.Quotient.mk (maximalIdeal R ^ n) with hπn
      set Xn := Xu.map πn with hXn
      set jn : Zp2 q →+* R ⧸ maximalIdeal R ^ n := (algebraMap Onr (R ⧸ maximalIdeal R ^ n)).comp ι with hjn
      have hjn : ∀ a, πn (algebraMap Onr R (ι a)) = jn a := fun a => rfl
      obtain ⟨hcompl, -, -⟩ := htrunc n hn
      have hAn : ∀ a, (MvFormalGroup.linearPart (Xu.act a)).map πn = MvFormalGroup.linearPart (Xn.act a) :=
        fun a => by rw [hXn, FormalODModule.map_act, linearPart_map]

      have h1 : ∀ y ∈ Xn.lieZero jn, (B₁.map πn) *ᵥ y = 0 := by
        intro y hy
        rw [hB₁, map_sub_smul_one, sub_smul_one_mulVec, hAn, (mem_lieZero_iff jn Xn y).mp hy α, hjn, sub_self]
      have h2 : ∀ y ∈ Xn.lieOne jn, (B₀.map πn) *ᵥ y = 0 := by
        intro y hy
        rw [hB₀, map_sub_smul_one, sub_smul_one_mulVec, hAn, (mem_lieOne_iff jn Xn y).mp hy α, hjn, sub_self]
      have h3 : ∀ y ∈ Xn.lieOne jn, (B₁.map πn) *ᵥ y = (jn (WittVector.frobenius α) - jn α) • y := by
        intro y hy
        rw [hB₁, map_sub_smul_one, sub_smul_one_mulVec, hAn, (mem_lieOne_iff jn Xn y).mp hy α, hjn, sub_smul]
      have key : ∀ w : Fin 2 → R ⧸ maximalIdeal R ^ n, (B₀.map πn) *ᵥ ((B₁.map πn) *ᵥ w) = 0 := by
        intro w
        have hw : w ∈ Xn.lieZero jn ⊔ Xn.lieOne jn := by rw [hcompl.sup_eq_top]; trivial
        obtain ⟨y₀, hy₀, y₁, hy₁, rfl⟩ := Submodule.mem_sup.mp hw
        rw [Matrix.mulVec_add, h1 y₀ hy₀, zero_add, h3 y₁ hy₁, Matrix.mulVec_smul, h2 y₁ hy₁, smul_zero]
      have e2 : (πn : R → R ⧸ maximalIdeal R ^ n) ∘ (B₁ *ᵥ v) = B₁.map πn *ᵥ ((πn : R → _) ∘ v) :=
        funext fun j => RingHom.map_mulVec πn B₁ v j
      rw [← Matrix.mulVec_mulVec, RingHom.map_mulVec, e2]
      exact congrFun (key _) i
  have hN' : B₁ * B₀ = 0 := by rw [← hcomm, hN]

  have hXb := isSpecial_map_resR Onr ι X₀ R resR hresR Xu wu hwu
  obtain ⟨hcomplb, hinv0, hinv1⟩ := hXb
  haveI := hinv0
  haveI := hinv1
  have hAb : ∀ a, (MvFormalGroup.linearPart (Xu.act a)).map resR = MvFormalGroup.linearPart ((Xu.map resR).act a) :=
    fun a => by rw [FormalODModule.map_act, linearPart_map]
  have hMb : (MvFormalGroup.linearPart Xu.varpi).map resR = MvFormalGroup.linearPart (Xu.map resR).varpi := by
    rw [FormalODModule.map_varpi, linearPart_map]

  have hne0 : (Xu.map resR).lieZero ((IsLocalRing.residue Onr).comp ι) ≠ ⊥ := by
    intro h
    have h1 := Module.Invertible.finrank_eq_one (ResidueField Onr) ↥((Xu.map resR).lieZero ((IsLocalRing.residue Onr).comp ι))
    rw [h, finrank_bot] at h1
    exact zero_ne_one h1
  have hne1 : (Xu.map resR).lieOne ((IsLocalRing.residue Onr).comp ι) ≠ ⊥ := by
    intro h
    have h1 := Module.Invertible.finrank_eq_one (ResidueField Onr) ↥((Xu.map resR).lieOne ((IsLocalRing.residue Onr).comp ι))
    rw [h, finrank_bot] at h1
    exact zero_ne_one h1
  obtain ⟨eb₀, heb₀, heb₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne0
  obtain ⟨eb₁, heb₁, heb₁ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne1

  have hlift : ∀ w : Fin 2 → ResidueField Onr, ∃ v : Fin 2 → R, (resR : R → _) ∘ v = w := fun w =>
    ⟨fun i => (hsurj (w i)).choose, funext fun i => (hsurj (w i)).choose_spec⟩
  obtain ⟨et₀, het₀⟩ := hlift eb₀
  obtain ⟨et₁, het₁⟩ := hlift eb₁
  set e₀ : Fin 2 → R := B₀ *ᵥ et₀ with he₀
  set e₁ : Fin 2 → R := B₁ *ᵥ et₁ with he₁
  have hB₁e₀ : B₁ *ᵥ e₀ = 0 := by rw [he₀, Matrix.mulVec_mulVec, hN', Matrix.zero_mulVec]
  have hB₀e₁ : B₀ *ᵥ e₁ = 0 := by rw [he₁, Matrix.mulVec_mulVec, hN, Matrix.zero_mulVec]
  have hB₀e₀ : B₀ *ᵥ e₀ = d • e₀ := by rw [hB₀₁, hB₁e₀, zero_add]
  have hB₁e₁ : B₁ *ᵥ e₁ = -d • e₁ := by
    have := hB₀₁ e₁; rw [hB₀e₁] at this
    rw [neg_smul, eq_neg_iff_add_eq_zero, this]

  set rd : ResidueField Onr := resR d with hrd
  have hrd' : rd = (IsLocalRing.residue Onr) (ι α) - (IsLocalRing.residue Onr) (ι (WittVector.frobenius α)) := by
    rw [hrd, hd, map_sub, hres_jR, hres_jR]
  have hrdne : rd ≠ 0 := hresd
  have hred₀ : (resR : R → _) ∘ e₀ = rd • eb₀ := by
    have h := funext fun j => RingHom.map_mulVec resR B₀ et₀ j
    rw [he₀]
    refine h.trans ?_
    rw [het₀, hB₀, map_sub_smul_one, sub_smul_one_mulVec, hAb,
      (mem_lieZero_iff _ _ eb₀).mp heb₀ α, hres_jR, RingHom.comp_apply, ← sub_smul, hrd']
  have hred₁ : (resR : R → _) ∘ e₁ = -rd • eb₁ := by
    have h := funext fun j => RingHom.map_mulVec resR B₁ et₁ j
    rw [he₁]
    refine h.trans ?_
    rw [het₁, hB₁, map_sub_smul_one, sub_smul_one_mulVec, hAb,
      (mem_lieOne_iff _ _ eb₁).mp heb₁ α, hres_jR, RingHom.comp_apply, ← sub_smul, hrd', neg_sub]

  set δ : R := e₀ 0 * e₁ 1 - e₀ 1 * e₁ 0 with hδ
  have hδunit : IsUnit δ := by
    by_contra hnu
    have hδm : δ ∈ maximalIdeal R := hnu
    rw [← hker, RingHom.mem_ker, hδ, map_sub, map_mul, map_mul] at hδm

    have hr0 : ∀ i, resR (e₀ i) = rd * eb₀ i := fun i => by
      have := congrFun hred₀ i; simpa using this
    have hr1 : ∀ i, resR (e₁ i) = -rd * eb₁ i := fun i => by
      have := congrFun hred₁ i; simpa using this
    rw [hr0, hr0, hr1, hr1] at hδm
    have hdet : eb₀ 0 * eb₁ 1 - eb₀ 1 * eb₁ 0 = 0 := by
      have : rd * (-rd) * (eb₀ 0 * eb₁ 1 - eb₀ 1 * eb₁ 0) = 0 := by linear_combination hδm
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (mul_ne_zero hrdne (neg_ne_zero.mpr hrdne))
      · exact h
    obtain ⟨c, hc⟩ := exists_smul_of_det_eq_zero eb₀ eb₁ heb₀ne hdet

    have hmem : eb₁ ∈ (Xu.map resR).lieZero ((IsLocalRing.residue Onr).comp ι) := by
      rw [hc]; exact Submodule.smul_mem _ c heb₀
    have : eb₁ ∈ (Xu.map resR).lieZero ((IsLocalRing.residue Onr).comp ι) ⊓
        (Xu.map resR).lieOne ((IsLocalRing.residue Onr).comp ι) := ⟨hmem, heb₁⟩
    rw [hcomplb.inf_eq_bot, Submodule.mem_bot] at this
    exact heb₁ne this
  obtain ⟨δinv, hδinv⟩ := hδunit.exists_left_inv
  have hbasis : ∀ m : Fin 2 → R, ∃! c : R × R, m = c.1 • e₀ + c.2 • e₁ :=
    existsUnique_coords e₀ e₁ δinv (by rw [← hδ]; exact hδinv)

  have hcoord : ∀ a b : R, a • e₀ + b • e₁ = 0 → a = 0 ∧ b = 0 := by
    intro a b hab
    have h := (hbasis 0).unique (y₁ := (a, b)) (y₂ := (0, 0)) (by simpa using hab.symm) (by simp)
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

  have hE : ∀ (a : Zp2 q),
      MvFormalGroup.linearPart (Xu.act a) *ᵥ e₀ = algebraMap Onr R (ι a) • e₀ ∧
      MvFormalGroup.linearPart (Xu.act a) *ᵥ e₁ = algebraMap Onr R (ι (WittVector.frobenius a)) • e₁ := by
    intro a
    constructor
    all_goals
      refine sub_eq_zero.mp (funext fun i => eq_zero_of_forall_mk_pow_eq_zero _ fun n => ?_)
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact Ideal.Quotient.eq_zero_iff_mem.mpr (by simp)
      set πn := Ideal.Quotient.mk (maximalIdeal R ^ n) with hπn
      set Xn := Xu.map πn with hXn
      set jn : Zp2 q →+* R ⧸ maximalIdeal R ^ n := (algebraMap Onr (R ⧸ maximalIdeal R ^ n)).comp ι with hjn
      have hjn : ∀ a, πn (algebraMap Onr R (ι a)) = jn a := fun a => rfl
      obtain ⟨hcompl, -, -⟩ := htrunc n hn
      have hAn : ∀ a, (MvFormalGroup.linearPart (Xu.act a)).map πn = MvFormalGroup.linearPart (Xn.act a) :=
        fun a => by rw [hXn, FormalODModule.map_act, linearPart_map]
      have hdn : IsUnit (πn d) := hdunit.map πn

      have hker₁ : ∀ y : Fin 2 → R ⧸ maximalIdeal R ^ n, (B₁.map πn) *ᵥ y = 0 → y ∈ Xn.lieZero jn := by
        intro y hy
        have hw : y ∈ Xn.lieZero jn ⊔ Xn.lieOne jn := by rw [hcompl.sup_eq_top]; trivial
        obtain ⟨y₀, hy₀, y₁, hy₁, rfl⟩ := Submodule.mem_sup.mp hw
        have h0 : (B₁.map πn) *ᵥ y₀ = 0 := by
          rw [hB₁, map_sub_smul_one, sub_smul_one_mulVec, hAn, (mem_lieZero_iff jn Xn y₀).mp hy₀ α, hjn, sub_self]
        have h1 : (B₁.map πn) *ᵥ y₁ = -(πn d) • y₁ := by
          rw [hB₁, map_sub_smul_one, sub_smul_one_mulVec, hAn, (mem_lieOne_iff jn Xn y₁).mp hy₁ α, hjn, ← sub_smul,
            hd, map_sub, hjn, hjn, neg_sub]
        rw [Matrix.mulVec_add, h0, h1, zero_add, neg_smul, neg_eq_zero] at hy
        have : y₁ = 0 := by
          have := congrArg (fun z => hdn.unit⁻¹.val • z) hy
          simpa [smul_smul, hdn.unit_spec] using this
        rw [this, add_zero]; exact hy₀
      have hker₀ : ∀ y : Fin 2 → R ⧸ maximalIdeal R ^ n, (B₀.map πn) *ᵥ y = 0 → y ∈ Xn.lieOne jn := by
        intro y hy
        have hw : y ∈ Xn.lieZero jn ⊔ Xn.lieOne jn := by rw [hcompl.sup_eq_top]; trivial
        obtain ⟨y₀, hy₀, y₁, hy₁, rfl⟩ := Submodule.mem_sup.mp hw
        have h1 : (B₀.map πn) *ᵥ y₁ = 0 := by
          rw [hB₀, map_sub_smul_one, sub_smul_one_mulVec, hAn, (mem_lieOne_iff jn Xn y₁).mp hy₁ α, hjn, sub_self]
        have h0 : (B₀.map πn) *ᵥ y₀ = (πn d) • y₀ := by
          rw [hB₀, map_sub_smul_one, sub_smul_one_mulVec, hAn, (mem_lieZero_iff jn Xn y₀).mp hy₀ α, hjn, ← sub_smul,
            hd, map_sub, hjn, hjn]
        rw [Matrix.mulVec_add, h0, h1, add_zero] at hy
        have : y₀ = 0 := by
          have := congrArg (fun z => hdn.unit⁻¹.val • z) hy
          simpa [smul_smul, hdn.unit_spec] using this
        rw [this, zero_add]; exact hy₁
      first
      |
        have hmem : (πn : R → _) ∘ e₀ ∈ Xn.lieZero jn := by
          apply hker₁
          have h := funext fun j => RingHom.map_mulVec πn B₁ e₀ j
          rw [← h, hB₁e₀]; rfl
        have h2 := (mem_lieZero_iff jn Xn _).mp hmem a
        rw [← hAn, ← hjn] at h2
        have h3 := RingHom.map_mulVec πn (MvFormalGroup.linearPart (Xu.act a)) e₀ i
        rw [Pi.sub_apply, map_sub, h3, h2, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul,
          Function.comp_apply, sub_self]
      |
        have hmem : (πn : R → _) ∘ e₁ ∈ Xn.lieOne jn := by
          apply hker₀
          have h := funext fun j => RingHom.map_mulVec πn B₀ e₁ j
          rw [← h, hB₀e₁]; rfl
        have h2 := (mem_lieOne_iff jn Xn _).mp hmem a
        rw [← hAn, ← hjn] at h2
        have h3 := RingHom.map_mulVec πn (MvFormalGroup.linearPart (Xu.act a)) e₁ i
        rw [Pi.sub_apply, map_sub, h3, h2, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul,
          Function.comp_apply, sub_self]
  have he₀mem : e₀ ∈ Xu.lieZero ((algebraMap Onr R).comp ι) :=
    (mem_lieZero_iff _ _ _).mpr fun a => (hE a).1
  have he₁mem : e₁ ∈ Xu.lieOne ((algebraMap Onr R).comp ι) :=
    (mem_lieOne_iff _ _ _).mpr fun a => (hE a).2

  have hMA : ∀ a, MvFormalGroup.linearPart Xu.varpi * MvFormalGroup.linearPart (Xu.act a) =
      MvFormalGroup.linearPart (Xu.act (WittVector.frobenius a)) * MvFormalGroup.linearPart Xu.varpi :=
    linearPart_varpi_mul_act Xu
  have hAM : MvFormalGroup.linearPart (Xu.act α) * MvFormalGroup.linearPart Xu.varpi =
      MvFormalGroup.linearPart Xu.varpi * MvFormalGroup.linearPart (Xu.act (WittVector.frobenius α)) := by
    rw [hMA, frob_frob]
  have hd' : d * dinv = 1 := by rw [mul_comm]; exact hdinv

  have hB₀Me₀ : B₀ *ᵥ (MvFormalGroup.linearPart Xu.varpi *ᵥ e₀) = 0 := by
    rw [hB₀, sub_smul_one_mulVec, Matrix.mulVec_mulVec, hAM, ← Matrix.mulVec_mulVec, (hE _).1, Matrix.mulVec_smul,
      sub_self]
  obtain ⟨⟨u', u⟩, hu, -⟩ := hbasis (MvFormalGroup.linearPart Xu.varpi *ᵥ e₀)
  have hu'0 : u' = 0 := by
    have h := congrArg (fun z => B₀ *ᵥ z) hu
    simp only [hB₀Me₀, Matrix.mulVec_add, Matrix.mulVec_smul, hB₀e₀, hB₀e₁, smul_zero, add_zero, smul_smul] at h
    have := (hcoord (u' * d) 0 (by rw [zero_smul, add_zero]; exact h.symm)).1
    calc u' = u' * d * dinv := by rw [mul_assoc, hd', mul_one]
      _ = 0 := by rw [this, zero_mul]
  rw [hu'0, zero_smul, zero_add] at hu
  change MvFormalGroup.linearPart Xu.varpi *ᵥ e₀ = u • e₁ at hu

  have hB₁Me₁ : B₁ *ᵥ (MvFormalGroup.linearPart Xu.varpi *ᵥ e₁) = 0 := by
    rw [hB₁, sub_smul_one_mulVec, Matrix.mulVec_mulVec, hAM, ← Matrix.mulVec_mulVec, (hE _).2, frob_frob,
      Matrix.mulVec_smul, sub_self]
  obtain ⟨⟨v, v'⟩, hv, -⟩ := hbasis (MvFormalGroup.linearPart Xu.varpi *ᵥ e₁)
  have hv'0 : v' = 0 := by
    have h := congrArg (fun z => B₁ *ᵥ z) hv
    simp only [hB₁Me₁, Matrix.mulVec_add, Matrix.mulVec_smul, hB₁e₀, hB₁e₁, smul_zero, zero_add, smul_smul] at h
    have := (hcoord 0 (v' * -d) (by rw [zero_smul, zero_add]; exact h.symm)).2
    calc v' = -(v' * -d * dinv) := by rw [mul_neg, neg_mul, neg_neg, mul_assoc, hd', mul_one]
      _ = 0 := by rw [this, zero_mul, neg_zero]
  rw [hv'0, zero_smul, add_zero] at hv
  change MvFormalGroup.linearPart Xu.varpi *ᵥ e₁ = v • e₀ at hv

  have huv : u * v = algebraMap Onr R ((q : ℕ) : Onr) := by
    rw [map_natCast]
    have h1 : MvFormalGroup.linearPart Xu.varpi *ᵥ (MvFormalGroup.linearPart Xu.varpi *ᵥ e₀) = ((q : ℕ) : R) • e₀ := by
      rw [Matrix.mulVec_mulVec, linearPart_varpi_mul_self, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [hu, Matrix.mulVec_smul, hv, smul_smul] at h1
    have := (hcoord (u * v - (q : ℕ)) 0 (by rw [sub_smul, h1, zero_smul, add_zero, sub_self])).1
    exact sub_eq_zero.mp this

  obtain ⟨W', hW'⟩ := Hom.exists_mul_linearPart_eq_one wu hwu
  have hWact := Hom.linearPart_mul_act wu
  have hWvarpi := Hom.linearPart_mul_varpi wu
  have hWeb₀ : MvFormalGroup.linearPart wu.toSeries *ᵥ eb₀ ∈ X₀.toFormalODModule.lieZero ((IsLocalRing.residue Onr).comp ι) := by
    rw [mem_lieZero_iff]
    intro a
    rw [Matrix.mulVec_mulVec, ← hWact, ← Matrix.mulVec_mulVec, (mem_lieZero_iff _ _ eb₀).mp heb₀ a, Matrix.mulVec_smul]
  have hWeb₁ : MvFormalGroup.linearPart wu.toSeries *ᵥ eb₁ ∈ X₀.toFormalODModule.lieOne ((IsLocalRing.residue Onr).comp ι) := by
    rw [mem_lieOne_iff]
    intro a
    rw [Matrix.mulVec_mulVec, ← hWact, ← Matrix.mulVec_mulVec, (mem_lieOne_iff _ _ eb₁).mp heb₁ a, Matrix.mulVec_smul]
  have hr0 := hnode₀ _ hWeb₀
  have hr1 := hnode₁ _ hWeb₁
  rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← hWvarpi, ← Matrix.mulVec_mulVec] at hr0 hr1

  have hred_u : MvFormalGroup.linearPart (Xu.map resR).varpi *ᵥ (rd • eb₀) = resR u • (-rd • eb₁) := by
    rw [← hred₀, ← hred₁, ← hMb]
    funext i
    rw [← RingHom.map_mulVec, hu, Pi.smul_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, smul_eq_mul,
      map_mul]
  have hred_v : MvFormalGroup.linearPart (Xu.map resR).varpi *ᵥ (-rd • eb₁) = resR v • (rd • eb₀) := by
    rw [← hred₀, ← hred₁, ← hMb]
    funext i
    rw [← RingHom.map_mulVec, hv, Pi.smul_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, smul_eq_mul,
      map_mul]
  have hWinj : ∀ z : Fin 2 → ResidueField Onr, MvFormalGroup.linearPart wu.toSeries *ᵥ z = 0 → z = 0 := by
    intro z hz
    have h := congrArg (fun y => W' *ᵥ y) hz
    simp only [Matrix.mulVec_mulVec, hW', Matrix.one_mulVec, Matrix.mulVec_zero] at h
    exact h
  have hum : u ∈ maximalIdeal R := by
    rw [← hker, RingHom.mem_ker]
    have h1 : MvFormalGroup.linearPart wu.toSeries *ᵥ
        (MvFormalGroup.linearPart (Xu.map resR).varpi *ᵥ (rd • eb₀)) = 0 := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, hr0, smul_zero]
    rw [hred_u, smul_smul] at h1
    rw [Matrix.mulVec_smul] at h1
    have h2 := (smul_eq_zero.mp h1).resolve_right (fun h => heb₁ne (hWinj _ h))
    exact (mul_eq_zero.mp h2).resolve_right (neg_ne_zero.mpr hrdne)
  have hvm : v ∈ maximalIdeal R := by
    rw [← hker, RingHom.mem_ker]
    have h1 : MvFormalGroup.linearPart wu.toSeries *ᵥ
        (MvFormalGroup.linearPart (Xu.map resR).varpi *ᵥ (-rd • eb₁)) = 0 := by
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, hr1, smul_zero]
    rw [hred_v, smul_smul] at h1
    rw [Matrix.mulVec_smul] at h1
    have h2 := (smul_eq_zero.mp h1).resolve_right (fun h => heb₀ne (hWinj _ h))
    exact (mul_eq_zero.mp h2).resolve_right hrdne
  refine ⟨e₀, e₁, u, v, he₀mem, he₁mem, hbasis, ?_, ?_, huv, hum, hvm⟩
  · rw [Matrix.mulVecLin_apply]; exact hu
  · rw [Matrix.mulVecLin_apply]; exact hv

#print axioms solution

end S_CerednikDrinfeld_SpecialFormalODModule_exists_lieCoordinates_mul_eq_of_isProrepresentedBy_deformations
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_lieCoordinates_mul_eq_of_isProrepresentedBy_deformations (solution)
