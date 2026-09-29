-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_algHom_forall_exists_isIso_of_isAdicComplete_of_isProrepresentedBy_deformations
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/7490eb19-c91f-5dec-8039-c30da851a234

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecial_and_hasHeight_four_of_isIso_of_isArtinianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_algHom_forall_exists_isIso_of_isAdicComplete_of_isProrepresentedBy_deformations
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open IsLocalRing CerednikDrinfeld CerednikDrinfeld.SpecialFormal

namespace DDDefPt

variable {q : ℕ} [Fact q.Prime]

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

def castHom2 {A : Type} [CommRing A] {X X' Y Y' : FormalODModule q A} (hX : X = X') (hY : Y = Y')
    (w : X.Hom Y) : X'.Hom Y' :=
  ⟨w.toSeries, by subst hX; subst hY; exact w.isODHom⟩

@[scoped simp] theorem castHom2_toSeries {A : Type} [CommRing A] {X X' Y Y' : FormalODModule q A}
    (hX : X = X') (hY : Y = Y') (w : X.Hom Y) : (castHom2 hX hY w).toSeries = w.toSeries := rfl

theorem castHom2_isIso {A : Type} [CommRing A] {X X' Y Y' : FormalODModule q A} (hX : X = X') (hY : Y = Y')
    (w : X.Hom Y) (hw : w.IsIso) : (castHom2 hX hY w).IsIso := by
  subst hX; subst hY
  have : castHom2 rfl rfl w = w := FormalODModule.Hom.ext rfl
  rw [this]; exact hw

theorem isIso_map {A A' : Type} [CommRing A] [CommRing A'] (r : A →+* A') {X Y : FormalODModule q A}
    {f : X.Hom Y} (hf : f.IsIso) : (f.map r).IsIso := by
  obtain ⟨g, hg₁, hg₂⟩ := hf
  have e1 := congrArg FormalODModule.Hom.toSeries hg₁
  have e2 := congrArg FormalODModule.Hom.toSeries hg₂
  refine ⟨g.map r, FormalODModule.Hom.ext ?_, FormalODModule.Hom.ext ?_⟩
  · show (g.toSeries.map r).comp (f.toSeries.map r) = Series.id A'
    rw [← Series.map_comp _ _ _ f.isODHom.1.1]
    change (g.comp f).toSeries.map r = _
    rw [e1]; exact Series.map_id r
  · show (f.toSeries.map r).comp (g.toSeries.map r) = Series.id A'
    rw [← Series.map_comp _ _ _ g.isODHom.1.1]
    change (f.comp g).toSeries.map r = _
    rw [e2]; exact Series.map_id r

end DDDefPt
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_algHom_forall_exists_isIso_of_isAdicComplete_of_isProrepresentedBy_deformations.DDDefPt"

open DDDefPt in
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
    (B' : Type) [CommRing B'] [IsLocalRing B'] [IsNoetherianRing B'] [Algebra Onr B']
    [IsAdicComplete (IsLocalRing.maximalIdeal B') B']
    (resB : B' →+* IsLocalRing.ResidueField Onr) (hresB : Function.Surjective resB)
    (hresB' : resB.comp (algebraMap Onr B') = IsLocalRing.residue Onr)
    (X' : FormalODModule q B') (w' : (X'.map resB).Hom X₀.toFormalODModule) (hw' : w'.IsIso) :
    ∃ χ : R →ₐ[Onr] B', resB.comp χ.toRingHom = resR ∧
      ∀ n : ℕ, 0 < n →
        ∃ v : (Xu.map ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal B' ^ n)).comp χ.toRingHom)).Hom
            (X'.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B' ^ n))),
          v.IsIso ∧
          ∀ (resn : B' ⧸ IsLocalRing.maximalIdeal B' ^ n →+* IsLocalRing.ResidueField Onr),
            resn.comp (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B' ^ n)) = resB →
            (w'.toSeries).comp (v.toSeries.map resn) = wu.toSeries := by
  classical
  set I := maximalIdeal B' with hI
  have hkerB : RingHom.ker resB = I :=
    (IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective resB hresB)).trans hI.symm
  have hIn_le : ∀ n, 0 < n → I ^ n ≤ RingHom.ker resB := fun n hn => by
    rw [hkerB]; exact Ideal.pow_le_self hn.ne'
  have hIn_ne : ∀ n, 0 < n → I ^ n ≠ ⊤ := fun n hn h =>
    (maximalIdeal.isMaximal B').ne_top (top_le_iff.mp (h ▸ (hI ▸ Ideal.pow_le_self hn.ne')))

  let resn : ∀ n, 0 < n → (B' ⧸ I ^ n →+* ResidueField Onr) := fun n hn =>
    Ideal.Quotient.lift (I ^ n) resB (fun a ha => hIn_le n hn ha)
  have hresn_mk : ∀ n hn, (resn n hn).comp (Ideal.Quotient.mk (I ^ n)) = resB := fun n hn => RingHom.ext fun _ => rfl
  have hresn_surj : ∀ n hn, Function.Surjective (resn n hn) := fun n hn y => by
    obtain ⟨b, rfl⟩ := hresB y; exact ⟨Ideal.Quotient.mk _ b, rfl⟩
  have hresn_alg : ∀ n hn, (resn n hn).comp (algebraMap Onr (B' ⧸ I ^ n)) = IsLocalRing.residue Onr := fun n hn => by
    ext o; change resB (algebraMap Onr B' o) = _; rw [← RingHom.comp_apply, hresB']
  have hresn_unique : ∀ n hn (r : B' ⧸ I ^ n →+* ResidueField Onr),
      r.comp (Ideal.Quotient.mk (I ^ n)) = resB → r = resn n hn := fun n hn r hr =>
    Ideal.Quotient.ringHom_ext (hr.trans (hresn_mk n hn).symm)

  have hXn : ∀ n hn, X'.map resB = (X'.map (Ideal.Quotient.mk (I ^ n))).map (resn n hn) := fun n hn => by
    rw [FormalODModule.map_map, hresn_mk n hn]

  let P : ∀ n (hn : 0 < n), (R →ₐ[Onr] B' ⧸ I ^ n) → Prop := fun n hn ψ =>
    (resn n hn).comp ψ.toRingHom = resR ∧
      ∃ v : (Xu.map ψ.toRingHom).Hom (X'.map (Ideal.Quotient.mk (I ^ n))), v.IsIso ∧
        ((castHom2 (hXn n hn) rfl w').comp (v.map (resn n hn))).toSeries = wu.toSeries
  have key : ∀ n hn, ∃! ψ : R →ₐ[Onr] B' ⧸ I ^ n, P n hn ψ := by
    intro n hn
    haveI := isLocalRing_quotient (I ^ n) (hIn_ne n hn)
    haveI : IsArtinianRing (B' ⧸ I ^ n) := by
      have := isArtinianRing_quotient_pow (R := B') n (by rw [← hI]; exact hIn_ne n hn)
      rw [← hI] at this; exact this
    have hsh := CerednikDrinfeld.FormalODModule.isSpecial_and_hasHeight_four_of_isIso_of_isArtinianRing Onr ι X₀
      (B' ⧸ I ^ n) (resn n hn) (hresn_surj n hn) (hresn_alg n hn) (X'.map (Ideal.Quotient.mk (I ^ n)))
      (castHom2 (hXn n hn) rfl w') (castHom2_isIso _ _ w' hw')
    exact hPRO (B' ⧸ I ^ n) (resn n hn) (hresn_surj n hn) (hresn_alg n hn) (X'.map (Ideal.Quotient.mk (I ^ n)))
      hsh.1 hsh.2 (castHom2 (hXn n hn) rfl w') (castHom2_isIso _ _ w' hw')

  have hmax : ∀ n : ℕ, 0 < max n 1 := fun n => lt_max_of_lt_right one_pos
  let f : ∀ n : ℕ, R →ₐ[Onr] B' ⧸ I ^ n := fun n =>
    (Ideal.Quotient.factorₐ Onr (Ideal.pow_le_pow_right (le_max_left n 1))).comp (key (max n 1) (hmax n)).exists.choose

  have hpush : ∀ m n (hm : 0 < m) (hn : 0 < n) (hle : m ≤ n) (ψ : R →ₐ[Onr] B' ⧸ I ^ n),
      P n hn ψ → P m hm ((Ideal.Quotient.factorₐ Onr (Ideal.pow_le_pow_right hle)).comp ψ) := by
    intro m n hm hn hle ψ hψ
    obtain ⟨hres, v, hv, hc⟩ := hψ
    have hfac : (resn m hm).comp (Ideal.Quotient.factor (Ideal.pow_le_pow_right hle)) = resn n hn := by
      apply hresn_unique n hn
      rw [RingHom.comp_assoc, Ideal.Quotient.factor_comp_mk]; exact hresn_mk m hm
    refine ⟨?_, ?_⟩
    · rw [← hres, ← hfac, RingHom.comp_assoc]; rfl
    · have hsrc : (Xu.map ψ.toRingHom).map (Ideal.Quotient.factor (Ideal.pow_le_pow_right hle)) =
          Xu.map ((Ideal.Quotient.factorₐ Onr (Ideal.pow_le_pow_right hle)).comp ψ).toRingHom := by
        rw [FormalODModule.map_map]; rfl
      have htgt : (X'.map (Ideal.Quotient.mk (I ^ n))).map (Ideal.Quotient.factor (Ideal.pow_le_pow_right hle)) =
          X'.map (Ideal.Quotient.mk (I ^ m)) := by
        rw [FormalODModule.map_map, Ideal.Quotient.factor_comp_mk]
      refine ⟨castHom2 hsrc htgt (v.map _), castHom2_isIso _ _ _ (isIso_map _ hv), ?_⟩
      show w'.toSeries.comp (((v.toSeries.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right hle))).map (resn m hm))) =
        wu.toSeries
      rw [Series.map_map, hfac]
      exact hc
  have hfP : ∀ n hn, P n hn (f n) := fun n hn =>
    hpush n (max n 1) hn (hmax n) (le_max_left n 1) _ (key (max n 1) (hmax n)).exists.choose_spec

  have hcompat : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorₐ Onr (Ideal.pow_le_pow_right hle)).comp (f n) = f m := by
    intro m n hle
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · haveI : Subsingleton (B' ⧸ I ^ 0) :=
        Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
      exact AlgHom.ext fun x => Subsingleton.elim _ _
    · have hn : 0 < n := lt_of_lt_of_le hm hle
      exact (key m hm).unique (hpush m n hm hn hle (f n) (hfP n hn)) (hfP m hm)

  let Λ : R →ₐ[Onr] AdicCompletion I B' := AdicCompletion.liftAlgHom I f hcompat
  let ε : AdicCompletion I B' →ₐ[Onr] B' :=
    { toRingHom := ((AdicCompletion.ofAlgEquiv I).symm : AdicCompletion I B' ≃ₐ[B'] B').toRingEquiv.toRingHom
      commutes' := fun o => by
        show (AdicCompletion.ofAlgEquiv I).symm (algebraMap Onr (AdicCompletion I B') o) = algebraMap Onr B' o
        rw [AdicCompletion.algebraMap_apply, AdicCompletion.ofAlgEquiv_symm_of] }
  let χ : R →ₐ[Onr] B' := ε.comp Λ
  have hχn : ∀ n (x : R), Ideal.Quotient.mk (I ^ n) (χ x) = f n x := fun n x => by
    show Ideal.Quotient.mk (I ^ n) ((AdicCompletion.ofAlgEquiv I).symm (Λ x)) = f n x
    rw [AdicCompletion.mk_ofAlgEquiv_symm]
    exact AdicCompletion.evalₐ_liftAlgHom I f hcompat n x
  have hχn' : ∀ n, (Ideal.Quotient.mk (I ^ n)).comp χ.toRingHom = (f n).toRingHom := fun n =>
    RingHom.ext fun x => hχn n x
  refine ⟨χ, ?_, ?_⟩
  · rw [← hresn_mk 1 one_pos, RingHom.comp_assoc, hχn' 1]
    exact (hfP 1 one_pos).1
  · intro n hn
    rw [hχn' n]
    obtain ⟨-, v, hv, hc⟩ := hfP n hn
    refine ⟨v, hv, fun r hr => ?_⟩
    rw [hresn_unique n hn r hr]
    exact hc

#print axioms solution

end S_CerednikDrinfeld_SpecialFormalODModule_exists_algHom_forall_exists_isIso_of_isAdicComplete_of_isProrepresentedBy_deformations
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_algHom_forall_exists_isIso_of_isAdicComplete_of_isProrepresentedBy_deformations (solution)
