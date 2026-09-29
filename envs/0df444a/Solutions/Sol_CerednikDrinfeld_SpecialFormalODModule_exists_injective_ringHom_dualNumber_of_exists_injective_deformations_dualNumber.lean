-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormalODModule.exists_injective_ringHom_dualNumber_of_exists_injective_deformations_dualNumber
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/e49e5367-8965-5b45-96e2-7424325cc228

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isSpecial_and_hasHeight_four_of_isIso_of_isArtinianRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_injective_ringHom_dualNumber_of_exists_injective_deformations_dualNumber
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

namespace TTR
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

variable {q : ℕ} [Fact q.Prime] {B : Type} [CommRing B]

def castHom {X X' Y : FormalODModule q B} (h : X = X') (w : X.Hom Y) : X'.Hom Y := ⟨w.toSeries, h ▸ w.isODHom⟩

@[scoped simp] theorem castHom_toSeries {X X' Y : FormalODModule q B} (h : X = X') (w : X.Hom Y) :
    (castHom h w).toSeries = w.toSeries := rfl

theorem castHom_isIso {X X' Y : FormalODModule q B} (h : X = X') (w : X.Hom Y) (hw : w.IsIso) : (castHom h w).IsIso := by
  subst h; exact hw

theorem isIso_id (X : FormalODModule q B) : (FormalODModule.Hom.id X).IsIso :=
  ⟨FormalODModule.Hom.id X, FormalODModule.Hom.ext (Series.comp_id _), FormalODModule.Hom.ext (Series.comp_id _)⟩

theorem Series.map_id' {B' : Type} [CommRing B'] (f : B →+* B') : (Series.id B).map f = Series.id B' := by
  funext i; simp [Series.map, Series.id, MvPowerSeries.map_X]

end TTR
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_injective_ringHom_dualNumber_of_exists_injective_deformations_dualNumber.TTR"

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

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
    {r : ℕ}
    (htangent : ∃ (e : ∀ (X : FormalODModule q (DualNumber (IsLocalRing.ResidueField Onr)))
        (w : (X.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).Hom X₀.toFormalODModule),
        w.IsIso → (Fin r → (IsLocalRing.ResidueField Onr))),

      (∀ (X : FormalODModule q (DualNumber (IsLocalRing.ResidueField Onr)))
          (w : (X.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).Hom X₀.toFormalODModule) (hw : w.IsIso)
          (X' : FormalODModule q (DualNumber (IsLocalRing.ResidueField Onr)))
          (w' : (X'.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).Hom X₀.toFormalODModule)
          (hw' : w'.IsIso) (v : X.Hom X'), v.IsIso →
          w'.toSeries.comp (v.toSeries.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom) = w.toSeries →
        e X w hw = e X' w' hw') ∧

      (∀ (X : FormalODModule q (DualNumber (IsLocalRing.ResidueField Onr)))
          (w : (X.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).Hom X₀.toFormalODModule) (hw : w.IsIso)
          (X' : FormalODModule q (DualNumber (IsLocalRing.ResidueField Onr)))
          (w' : (X'.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).Hom X₀.toFormalODModule)
          (hw' : w'.IsIso),
        e X w hw = e X' w' hw' →
        ∃ v : X.Hom X', v.IsIso ∧
          w'.toSeries.comp (v.toSeries.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom) = w.toSeries) ∧

      (∀ (c : (IsLocalRing.ResidueField Onr)) (μ : DualNumber (IsLocalRing.ResidueField Onr) →+* DualNumber (IsLocalRing.ResidueField Onr)),
          (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp μ = (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom →
          (∀ t, TrivSqZeroExt.snd (μ t) = c * TrivSqZeroExt.snd t) →
        ∀ (X : FormalODModule q (DualNumber (IsLocalRing.ResidueField Onr)))
          (w : (X.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).Hom X₀.toFormalODModule) (hw : w.IsIso)
          (w' : ((X.map μ).map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).Hom X₀.toFormalODModule)
          (hw' : w'.IsIso), w'.toSeries = w.toSeries →
        e (X.map μ) w' hw' = c • e X w hw) ∧

      (∀ (B : Type) [CommRing B] (resB : B →+* (IsLocalRing.ResidueField Onr)), Function.Surjective resB → IsLocalHom resB →
        ∀ (p₁ p₂ σ : B →+* DualNumber (IsLocalRing.ResidueField Onr)),
          (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp p₁ = resB →
          (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp p₂ = resB →
          (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp σ = resB →
          (∀ b, TrivSqZeroExt.snd (σ b) = TrivSqZeroExt.snd (p₁ b) + TrivSqZeroExt.snd (p₂ b)) →
        ∀ (Y : FormalODModule q B) (u : (Y.map resB).Hom X₀.toFormalODModule), u.IsIso →
        ∀ (w₁ : ((Y.map p₁).map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).Hom X₀.toFormalODModule)
          (hw₁ : w₁.IsIso)
          (w₂ : ((Y.map p₂).map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).Hom X₀.toFormalODModule)
          (hw₂ : w₂.IsIso)
          (wσ : ((Y.map σ).map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).Hom X₀.toFormalODModule)
          (hwσ : wσ.IsIso),
          w₁.toSeries = u.toSeries → w₂.toSeries = u.toSeries → wσ.toSeries = u.toSeries →
        e (Y.map σ) wσ hwσ = e (Y.map p₁) w₁ hw₁ + e (Y.map p₂) w₂ hw₂)) :
    ∃ e' : (R →+* DualNumber (IsLocalRing.ResidueField Onr)) → (Fin r → IsLocalRing.ResidueField Onr),
      (∀ χ χ' : R →+* DualNumber (IsLocalRing.ResidueField Onr),
        ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp χ = resR ∧ χ.comp (algebraMap Onr R) = (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr)) →
        ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp χ' = resR ∧ χ'.comp (algebraMap Onr R) = (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr)) →
        e' χ = e' χ' → χ = χ') ∧
      (∀ (c : IsLocalRing.ResidueField Onr) (μ : DualNumber (IsLocalRing.ResidueField Onr) →+* DualNumber (IsLocalRing.ResidueField Onr)),
        (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp μ = (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom →
        (∀ t, TrivSqZeroExt.snd (μ t) = c * TrivSqZeroExt.snd t) →
        ∀ χ : R →+* DualNumber (IsLocalRing.ResidueField Onr), ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp χ = resR ∧ χ.comp (algebraMap Onr R) = (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr)) →
          e' (μ.comp χ) = c • e' χ) ∧
      (∀ χ₁ χ₂ χ₃ : R →+* DualNumber (IsLocalRing.ResidueField Onr),
        ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp χ₁ = resR ∧ χ₁.comp (algebraMap Onr R) = (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr)) →
        ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp χ₂ = resR ∧ χ₂.comp (algebraMap Onr R) = (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr)) →
        ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom.comp χ₃ = resR ∧ χ₃.comp (algebraMap Onr R) = (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr)) →
        (∀ x, TrivSqZeroExt.snd (χ₃ x) = TrivSqZeroExt.snd (χ₁ x) + TrivSqZeroExt.snd (χ₂ x)) →
          e' χ₃ = e' χ₁ + e' χ₂) := by
  classical
  obtain ⟨e, hconst, hinj, hhomog, hadd⟩ := htangent

  letI iAlg : Algebra Onr (DualNumber (IsLocalRing.ResidueField Onr)) := ((algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr)).toAlgebra
  haveI : Module.Finite (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr)) := inferInstanceAs (Module.Finite (IsLocalRing.ResidueField Onr) ((IsLocalRing.ResidueField Onr) × (IsLocalRing.ResidueField Onr)))
  haveI : IsArtinianRing (DualNumber (IsLocalRing.ResidueField Onr)) := IsArtinianRing.of_finite (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))
  have hfst_surj : Function.Surjective (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  have hfst_alg : ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).comp (algebraMap Onr (DualNumber (IsLocalRing.ResidueField Onr))) = IsLocalRing.residue Onr := by
    ext o; rfl

  have Eχ : ∀ χ : R →+* DualNumber (IsLocalRing.ResidueField Onr), ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).comp χ = resR → Xu.map resR = (Xu.map χ).map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom := by
    intro χ h; rw [FormalODModule.map_map, h]

  have hSH : ∀ χ : R →+* DualNumber (IsLocalRing.ResidueField Onr), ∀ h : ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).comp χ = resR,
      (Xu.map χ).IsSpecial ((algebraMap Onr (DualNumber (IsLocalRing.ResidueField Onr))).comp ι) ∧ (Xu.map χ).HasHeight 4 := fun χ h =>
    CerednikDrinfeld.FormalODModule.isSpecial_and_hasHeight_four_of_isIso_of_isArtinianRing Onr ι X₀ (DualNumber (IsLocalRing.ResidueField Onr))
      (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom hfst_surj hfst_alg (Xu.map χ) (TTR.castHom (Eχ χ h) wu) (TTR.castHom_isIso _ wu hwu)

  have mkAlg : ∀ χ : R →+* DualNumber (IsLocalRing.ResidueField Onr), χ.comp (algebraMap Onr R) = (algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr) →
      ∃ ψ : R →ₐ[Onr] DualNumber (IsLocalRing.ResidueField Onr), ψ.toRingHom = χ := fun χ h =>
    ⟨{ toRingHom := χ, commutes' := fun o => by
        change χ (algebraMap Onr R o) = ((algebraMap (IsLocalRing.ResidueField Onr) (DualNumber (IsLocalRing.ResidueField Onr))).comp (IsLocalRing.residue Onr)) o
        rw [← h]; rfl }, rfl⟩

  have ecast : ∀ {X X' : FormalODModule q (DualNumber (IsLocalRing.ResidueField Onr))} (hX : X = X')
      (w : (X.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).Hom X₀.toFormalODModule) (hw : w.IsIso)
      (w' : (X'.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).Hom X₀.toFormalODModule) (hw' : w'.IsIso),
      w.toSeries = w'.toSeries → e X w hw = e X' w' hw' := by
    intro X X' hX; subst hX; intro w hw w' hw' hs
    obtain rfl : w = w' := FormalODModule.Hom.ext hs
    rfl

  refine ⟨fun χ => if h : ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).comp χ = resR then e (Xu.map χ) (TTR.castHom (Eχ χ h) wu) (TTR.castHom_isIso _ wu hwu) else 0,
    ?_, ?_, ?_⟩
  ·
    intro χ χ' hχ hχ' hee
    dsimp only at hee
    rw [dif_pos hχ.1, dif_pos hχ'.1] at hee
    obtain ⟨v, hv, hvw⟩ := hinj _ _ _ _ _ _ hee
    obtain ⟨ψ, hψ⟩ := mkAlg χ hχ.2
    obtain ⟨ψ', hψ'⟩ := mkAlg χ' hχ'.2
    obtain ⟨ψ₀, -, huniq⟩ := hPRO (DualNumber (IsLocalRing.ResidueField Onr)) (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom hfst_surj hfst_alg (Xu.map χ') (hSH χ' hχ'.1).1 (hSH χ' hχ'.1).2
      (TTR.castHom (Eχ χ' hχ'.1) wu) (TTR.castHom_isIso _ wu hwu)
    have h1 : ψ' = ψ₀ := by
      apply huniq
      refine ⟨by rw [hψ']; exact hχ'.1, ?_⟩
      rw [hψ']
      refine ⟨FormalODModule.Hom.id _, TTR.isIso_id _, ?_⟩
      show (TTR.castHom (Eχ χ' hχ'.1) wu).toSeries.comp ((Series.id _).map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom) = wu.toSeries
      rw [TTR.Series.map_id', Series.comp_id]; rfl
    have h2 : ψ = ψ₀ := by
      apply huniq
      refine ⟨by rw [hψ]; exact hχ.1, ?_⟩
      rw [hψ]
      refine ⟨v, hv, ?_⟩
      show (TTR.castHom (Eχ χ' hχ'.1) wu).toSeries.comp (v.toSeries.map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom) = wu.toSeries
      rw [hvw]; rfl
    rw [← hψ, ← hψ', h1, h2]
  ·
    intro c μ hμ₁ hμ₂ χ hχ
    have hμχ : ((TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom).comp (μ.comp χ) = resR := by rw [← RingHom.comp_assoc, hμ₁]; exact hχ.1
    dsimp only
    rw [dif_pos hμχ, dif_pos hχ.1]
    have Eμ : (Xu.map χ).map μ = Xu.map (μ.comp χ) := FormalODModule.map_map _ _ _
    have E' : Xu.map resR = ((Xu.map χ).map μ).map (TrivSqZeroExt.fstHom (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr) (IsLocalRing.ResidueField Onr)).toRingHom := by rw [Eμ]; exact Eχ _ hμχ
    rw [← hhomog c μ hμ₁ hμ₂ (Xu.map χ) (TTR.castHom (Eχ χ hχ.1) wu) (TTR.castHom_isIso _ wu hwu)
      (TTR.castHom E' wu) (TTR.castHom_isIso _ wu hwu) rfl]
    exact ecast Eμ.symm _ _ _ _ rfl
  ·
    intro χ₁ χ₂ χ₃ hχ₁ hχ₂ hχ₃ hsum
    dsimp only
    rw [dif_pos hχ₁.1, dif_pos hχ₂.1, dif_pos hχ₃.1]
    have hres_surj : Function.Surjective resR := by
      intro y; obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective y
      exact ⟨algebraMap Onr R o, by rw [← RingHom.comp_apply, hresR]⟩
    haveI : IsLocalHom resR := by
      refine ⟨fun x hx => ?_⟩
      by_contra hxu
      have hxm : x ∈ IsLocalRing.maximalIdeal R := hxu
      have hker : RingHom.ker resR = IsLocalRing.maximalIdeal R :=
        IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective resR hres_surj)
      rw [← hker, RingHom.mem_ker] at hxm
      rw [hxm] at hx
      exact not_isUnit_zero hx
    exact hadd R resR hres_surj inferInstance χ₁ χ₂ χ₃ hχ₁.1 hχ₂.1 hχ₃.1 hsum Xu wu hwu
      (TTR.castHom (Eχ χ₁ hχ₁.1) wu) (TTR.castHom_isIso _ wu hwu)
      (TTR.castHom (Eχ χ₂ hχ₂.1) wu) (TTR.castHom_isIso _ wu hwu)
      (TTR.castHom (Eχ χ₃ hχ₃.1) wu) (TTR.castHom_isIso _ wu hwu) rfl rfl rfl

#print axioms solution

end S_CerednikDrinfeld_SpecialFormalODModule_exists_injective_ringHom_dualNumber_of_exists_injective_deformations_dualNumber
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormalODModule_exists_injective_ringHom_dualNumber_of_exists_injective_deformations_dualNumber (solution)
