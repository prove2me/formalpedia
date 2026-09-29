-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_theta_apply_eta_eq_of_rule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/15f99157-9094-5463-9c54-6f6949a0641b

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec
import Definitions.Def_CerednikDrinfeld_PeriodMap
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Theorems.Thm_CerednikDrinfeld_FormalOmega_Omega_existsUnique_glue_of_span_eq_top
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsAdmissible_map_ringHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_theta_apply_eta_eq_of_rule

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

set_option autoImplicit false

set_option linter.unusedVariables false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

noncomputable section

namespace ThetaDescentAux

section Loc

variable {B : Type} [CommRing B]

def toRight (x y : B) : Localization.Away x →ₐ[B] Localization.Away (x * y) :=
  { IsLocalization.Away.awayToAwayRight (P := Localization.Away (x * y)) x y with
    commutes' := fun b => IsLocalization.Away.awayToAwayRight_eq x y b }

def toLeft (x y : B) : Localization.Away x →ₐ[B] Localization.Away (y * x) :=
  { IsLocalization.Away.awayToAwayLeft (P := Localization.Away (y * x)) x y with
    commutes' := fun b => IsLocalization.Away.awayToAwayLeft_eq x y b }

def prodCover {n n' : ℕ} (f : Fin n → B) (g : Fin n' → B) : Fin (n * n') → B :=
  fun l => f (finProdFinEquiv.symm l).1 * g (finProdFinEquiv.symm l).2

theorem prodCover_apply {n n' : ℕ} (f : Fin n → B) (g : Fin n' → B) (i : Fin n) (j : Fin n') :
    prodCover f g (finProdFinEquiv (i, j)) = f i * g j := by
  simp [prodCover]

theorem span_prodCover_eq_top {n n' : ℕ} (f : Fin n → B) (g : Fin n' → B)
    (hf : Ideal.span (Set.range f) = ⊤) (hg : Ideal.span (Set.range g) = ⊤) :
    Ideal.span (Set.range (prodCover f g)) = ⊤ := by
  apply le_antisymm le_top
  have h : Ideal.span (Set.range f) * Ideal.span (Set.range g) ≤ Ideal.span (Set.range (prodCover f g)) := by
    rw [Ideal.span_mul_span']
    apply Ideal.span_le.mpr
    rintro _ ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨finProdFinEquiv (i, j), prodCover_apply f g i j⟩
  simpa [hf, hg] using h

theorem span_range_comp_eq_top {B' : Type} [CommRing B'] (φ : B →+* B') {n : ℕ} (f : Fin n → B)
    (hf : Ideal.span (Set.range f) = ⊤) : Ideal.span (Set.range (fun i => φ (f i))) = ⊤ := by
  have h := congrArg (Ideal.map φ) hf
  rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
  exact h

theorem nilp_away (p : ℕ) (hB : IsNilpotent (p : B)) (x : B) : IsNilpotent (p : Localization.Away x) := by
  simpa using hB.map (algebraMap B (Localization.Away x))

theorem nilp_of_algebra (p : ℕ) (hB : IsNilpotent (p : B)) (C : Type) [CommRing C] [Algebra B C] :
    IsNilpotent (p : C) := by
  simpa using hB.map (algebraMap B C)

end Loc

section Om

variable (p : ℕ) [Fact p.Prime]

abbrev Om (B : Type) [CommRing B] [Algebra ℤ_[p] B] : Type := OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B

abbrev incl {B : Type} [CommRing B] [Algebra ℤ_[p] B] (x : B) : B →ₐ[ℤ_[p]] Localization.Away x :=
  IsScalarTower.toAlgHom ℤ_[p] B (Localization.Away x)

variable {p}

theorem map_map {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B''] [Algebra ℤ_[p] B]
    [Algebra ℤ_[p] B'] [Algebra ℤ_[p] B''] (f : B →ₐ[ℤ_[p]] B') (g : B' →ₐ[ℤ_[p]] B'') (d : Om p B) :
    (d.map (p : ℤ_[p]) f).map (p : ℤ_[p]) g = d.map (p : ℤ_[p]) (g.comp f) :=
  ((Omega ℚ_[p] (p : ℤ_[p])).map_comp f g d).symm

theorem map_congr {B B' : Type} [CommRing B] [CommRing B'] [Algebra ℤ_[p] B] [Algebra ℤ_[p] B']
    {f f' : B →ₐ[ℤ_[p]] B'} (h : f = f') (d : Om p B) : d.map (p : ℤ_[p]) f = d.map (p : ℤ_[p]) f' := by
  rw [h]

theorem isBaseChange_iff {B B' : Type} [CommRing B] [CommRing B'] [Algebra ℤ_[p] B] [Algebra ℤ_[p] B']
    (f : B →ₐ[ℤ_[p]] B') (d : Om p B) (d' : Om p B') :
    DeligneDatum.IsBaseChange (K := ℚ_[p]) (π := (p : ℤ_[p])) f d d' ↔ d' = d.map (p : ℤ_[p]) f := by
  constructor
  · intro h
    exact DeligneDatum.ext' (funext h)
  · rintro rfl
    exact DeligneDatum.isBaseChange_map (K := ℚ_[p]) (p : ℤ_[p]) f d

theorem awayMapₐ_comp {B B' : Type} [CommRing B] [CommRing B'] [Algebra ℤ_[p] B] [Algebra ℤ_[p] B']
    (φ : B →ₐ[ℤ_[p]] B') (x : B) :
    (Localization.awayMapₐ φ x : Localization.Away x →+* Localization.Away (φ x)).comp
        (algebraMap B (Localization.Away x)) =
      (algebraMap B' (Localization.Away (φ x))).comp (φ : B →+* B') := by
  ext b
  show Localization.awayMapₐ φ x (algebraMap B _ b) = algebraMap B' _ (φ b)
  rw [Localization.awayMapₐ, IsLocalization.Away.mapₐ_apply]
  exact IsLocalization.map_eq _ b

theorem awayMapₐ_comp_comp {B B' : Type} [CommRing B] [CommRing B'] [Algebra ℤ_[p] B] [Algebra ℤ_[p] B']
    (φ : B →ₐ[ℤ_[p]] B') {W : Type} [CommRing W] {ψ : W →+* B} {ψ' : W →+* B'}
    (hφ : (φ : B →+* B').comp ψ = ψ') (x : B) :
    (Localization.awayMapₐ φ x : Localization.Away x →+* Localization.Away (φ x)).comp
        ((algebraMap B (Localization.Away x)).comp ψ) =
      (algebraMap B' (Localization.Away (φ x))).comp ψ' := by
  rw [← RingHom.comp_assoc, awayMapₐ_comp, RingHom.comp_assoc, hφ]

theorem incl_comp_eq_awayMapₐ_comp_incl {B B' : Type} [CommRing B] [CommRing B'] [Algebra ℤ_[p] B]
    [Algebra ℤ_[p] B'] (φ : B →ₐ[ℤ_[p]] B') (x : B) :
    (incl p (φ x)).comp φ = (Localization.awayMapₐ φ x).comp (incl p x) := by
  ext b
  show algebraMap B' _ (φ b) = Localization.awayMapₐ φ x (algebraMap B _ b)
  rw [Localization.awayMapₐ, IsLocalization.Away.mapₐ_apply]
  exact (IsLocalization.map_eq _ b).symm

theorem sep {B : Type} [CommRing B] [Algebra ℤ_[p] B] {n : ℕ} (f : Fin n → B)
    (hf : Ideal.span (Set.range f) = ⊤) (d d' : Om p B)
    (h : ∀ i, d.map (p : ℤ_[p]) (incl p (f i)) = d'.map (p : ℤ_[p]) (incl p (f i))) : d = d' := by
  have H := Omega.existsUnique_glue_of_span_eq_top (K := ℚ_[p]) (p : ℤ_[p]) B f hf
    (fun i => Localization.Away (f i)) (fun i j => Localization.Away (f i * f j))
    (fun i j => toRight (f i) (f j)) (fun i j => toLeft (f j) (f i))
    (fun i => d.map (p : ℤ_[p]) (incl p (f i))) ?_
  · obtain ⟨d₀, -, huniq⟩ := H
    exact (huniq d (fun i => rfl)).trans (huniq d' (fun i => (h i).symm)).symm
  · intro i j
    show ((d.map (p : ℤ_[p]) (incl p (f i))).map (p : ℤ_[p]) ((toRight (f i) (f j)).restrictScalars ℤ_[p])) =
      ((d.map (p : ℤ_[p]) (incl p (f j))).map (p : ℤ_[p]) ((toLeft (f j) (f i)).restrictScalars ℤ_[p]))
    have c1 : ((toRight (f i) (f j)).restrictScalars ℤ_[p]).comp (incl p (f i)) = incl p (f i * f j) := by
      ext b; exact (toRight (f i) (f j)).commutes b
    have c2 : ((toLeft (f j) (f i)).restrictScalars ℤ_[p]).comp (incl p (f j)) = incl p (f i * f j) := by
      ext b; exact (toLeft (f j) (f i)).commutes b
    rw [map_map, map_map, c1, c2]

end Om

section Frame

variable (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] (ι : Zp2 p →+* WittVector p k)
  (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
  (M : ModuliPackage.{0, 0} p (WittVector p k))
  (η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
    Rigidified p Φ B → M.obj B ψ hB)
  (ϑ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
    (hB : IsNilpotent (p : B)) (t : Rigidified p Φ B), t.IsAdmissible ι ψ → OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B)

structure Hyps : Prop where
  inj : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
    (t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
    (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')
  nat : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B']
    (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
    (hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ →
    η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)
  surj : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
    (m : M.obj B ψ hB),
    ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
      ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
        (hL : IsNilpotent (p : L)),
        ∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
          η L ((algebraMap B L).comp ψ) hL t =
            M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m
  iso : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
    (hB : IsNilpotent (p : B)) (t t' : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) (ht' : t'.IsAdmissible ι ψ),
    t.IsIsomorphic t' → ϑ B ψ hB t ht = ϑ B ψ hB t' ht'
  tnat : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B']
    [Algebra ℤ_[p] B] [Algebra ℤ_[p] B']
    (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →ₐ[ℤ_[p]] B')
    (hf : (f : B →+* B').comp ψ = ψ') (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (ht' : (t.map (f : B →+* B')).IsAdmissible ι ψ'),
    DeligneDatum.IsBaseChange (K := ℚ_[p]) (π := (p : ℤ_[p])) f (ϑ B ψ hB t ht) (ϑ B' ψ' hB' (t.map (f : B →+* B')) ht')

variable {p k ι Φ M η ϑ}

theorem Mmap_congr {B B' : Type} [CommRing B] [CommRing B'] {ψ : WittVector p k →+* B}
    {ψ' : WittVector p k →+* B'} (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B'))
    {f f' : B →+* B'} (h : f = f') (hf : f.comp ψ = ψ') (hf' : f'.comp ψ = ψ') (x : M.obj B ψ hB) :
    M.map hB hB' f hf x = M.map hB hB' f' hf' x := by
  subst h; rfl

theorem Hyps.tnat_eq (H : Hyps p k ι Φ M η ϑ) {B B' : Type} [CommRing B] [CommRing B'] [IsNoetherianRing B]
    [IsNoetherianRing B'] [Algebra ℤ_[p] B] [Algebra ℤ_[p] B']
    (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →ₐ[ℤ_[p]] B')
    (hf : (f : B →+* B').comp ψ = ψ') (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (ht' : (t.map (f : B →+* B')).IsAdmissible ι ψ') :
    ϑ B' ψ' hB' (t.map (f : B →+* B')) ht' = (ϑ B ψ hB t ht).map (p : ℤ_[p]) f :=
  (isBaseChange_iff f _ _).mp (H.tnat B B' ψ ψ' hB hB' f hf t ht ht')

theorem Hyps.theta_eq_of_eta_eq (H : Hyps p k ι Φ M η ϑ) {C : Type} [CommRing C] [IsNoetherianRing C]
    [Algebra ℤ_[p] C] (ψ : WittVector p k →+* C) (hC : IsNilpotent (p : C)) (s s' : Rigidified p Φ C)
    (hs : s.IsAdmissible ι ψ) (hs' : s'.IsAdmissible ι ψ) (h : η C ψ hC s = η C ψ hC s') :
    ϑ C ψ hC s hs = ϑ C ψ hC s' hs' :=
  H.iso C ψ hC s s' hs hs' ((H.inj C ψ hC s s' hs hs').mp h)

theorem Hyps.transfer (H : Hyps p k ι Φ M η ϑ) {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B]
    (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB) (x : B)
    (t : Rigidified p Φ (Localization.Away x))
    (ht : t.IsAdmissible ι ((algebraMap B (Localization.Away x)).comp ψ))
    (hηt : η (Localization.Away x) ((algebraMap B (Localization.Away x)).comp ψ) (nilp_away p hB x) t =
      M.map hB (nilp_away p hB x) (algebraMap B (Localization.Away x)) rfl m)
    (C : Type) [CommRing C] [IsNoetherianRing C] [Algebra B C] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] B C]
    (hC : IsNilpotent (p : C)) (g : Localization.Away x →ₐ[B] C) :
    ∃ ht' : (t.map (g : Localization.Away x →+* C)).IsAdmissible ι ((algebraMap B C).comp ψ),
    η C ((algebraMap B C).comp ψ) hC (t.map (g : Localization.Away x →+* C)) =
      M.map hB hC (algebraMap B C) rfl m ∧
    (ϑ (Localization.Away x) ((algebraMap B (Localization.Away x)).comp ψ) (nilp_away p hB x) t ht).map (p : ℤ_[p])
        (g.restrictScalars ℤ_[p]) =
      ϑ C ((algebraMap B C).comp ψ) hC (t.map (g : Localization.Away x →+* C)) ht' := by
  have hg : (g : Localization.Away x →+* C).comp (algebraMap B (Localization.Away x)) = algebraMap B C :=
    RingHom.ext fun b => g.commutes b
  have hgψ : (g : Localization.Away x →+* C).comp ((algebraMap B (Localization.Away x)).comp ψ) =
      (algebraMap B C).comp ψ := by
    rw [← RingHom.comp_assoc, hg]
  have HT : (t.map (g : Localization.Away x →+* C)).IsAdmissible ι ((algebraMap B C).comp ψ) := by
    have h := Rigidified.IsAdmissible.map_ringHom ι ((algebraMap B (Localization.Away x)).comp ψ)
      (g : Localization.Away x →+* C) t ht
    rwa [hgψ] at h
  refine ⟨HT, ?_, ?_⟩
  · rw [H.nat (Localization.Away x) C ((algebraMap B (Localization.Away x)).comp ψ) ((algebraMap B C).comp ψ)
        (nilp_away p hB x) hC (g : Localization.Away x →+* C) hgψ t ht, hηt,
      ← M.map_comp hB (nilp_away p hB x) hC (g : Localization.Away x →+* C) (algebraMap B (Localization.Away x))
        rfl hgψ m]
    exact Mmap_congr hB hC hg _ rfl m
  · have hgψ' : ((g.restrictScalars ℤ_[p] : Localization.Away x →ₐ[ℤ_[p]] C) : Localization.Away x →+* C).comp
        ((algebraMap B (Localization.Away x)).comp ψ) = (algebraMap B C).comp ψ := hgψ
    exact (H.tnat_eq _ _ (nilp_away p hB x) hC (g.restrictScalars ℤ_[p]) hgψ' t ht HT).symm

structure Pres {B : Type} [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
    (m : M.obj B ψ hB) where
  n : ℕ
  f : Fin n → B
  span_eq : Ideal.span (Set.range f) = ⊤
  t : ∀ i, Rigidified p Φ (Localization.Away (f i))
  adm : ∀ i, (t i).IsAdmissible ι ((algebraMap B (Localization.Away (f i))).comp ψ)
  eta_eq : ∀ i, η (Localization.Away (f i)) ((algebraMap B (Localization.Away (f i))).comp ψ)
      (nilp_away p hB (f i)) (t i) =
    M.map hB (nilp_away p hB (f i)) (algebraMap B (Localization.Away (f i))) rfl m

def Pres.Matches {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] {ψ : WittVector p k →+* B}
    {hB : IsNilpotent (p : B)} {m : M.obj B ψ hB} (P : Pres (ι := ι) (η := η) ψ hB m) (d : Om p B) : Prop :=
  ∀ i, d.map (p : ℤ_[p]) (incl p (P.f i)) =
    ϑ (Localization.Away (P.f i)) ((algebraMap B (Localization.Away (P.f i))).comp ψ) (nilp_away p hB (P.f i)) (P.t i)
      (P.adm i)

theorem Hyps.nonempty_pres (H : Hyps p k ι Φ M η ϑ) {B : Type} [CommRing B] [IsNoetherianRing B]
    (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB) :
    Nonempty (Pres (ι := ι) (η := η) ψ hB m) := by
  obtain ⟨n, f, hf, hloc⟩ := H.surj B ψ hB m
  choose t ht hηt using fun i => hloc i (Localization.Away (f i)) (nilp_away p hB (f i))
  exact ⟨⟨n, f, hf, t, ht, hηt⟩⟩

theorem Hyps.exists_matches (H : Hyps p k ι Φ M η ϑ) {B : Type} [CommRing B] [IsNoetherianRing B]
    [Algebra ℤ_[p] B] {ψ : WittVector p k →+* B} {hB : IsNilpotent (p : B)} {m : M.obj B ψ hB}
    (P : Pres (ι := ι) (η := η) ψ hB m) : ∃ d : Om p B, P.Matches (ϑ := ϑ) d := by
  have hcoc : ∀ i j,
      (Omega ℚ_[p] (p : ℤ_[p])).map ((toRight (P.f i) (P.f j)).restrictScalars ℤ_[p])
          (ϑ (Localization.Away (P.f i)) ((algebraMap B (Localization.Away (P.f i))).comp ψ)
            (nilp_away p hB (P.f i)) (P.t i) (P.adm i)) =
        (Omega ℚ_[p] (p : ℤ_[p])).map ((toLeft (P.f j) (P.f i)).restrictScalars ℤ_[p])
          (ϑ (Localization.Away (P.f j)) ((algebraMap B (Localization.Away (P.f j))).comp ψ)
            (nilp_away p hB (P.f j)) (P.t j) (P.adm j)) := by
    intro i j
    have hC : IsNilpotent (p : Localization.Away (P.f i * P.f j)) := nilp_away p hB _
    obtain ⟨ha₁, ha₂, ha₃⟩ := H.transfer ψ hB m (P.f i) (P.t i) (P.adm i) (P.eta_eq i)
      (Localization.Away (P.f i * P.f j)) hC (toRight (P.f i) (P.f j))
    obtain ⟨hb₁, hb₂, hb₃⟩ := H.transfer ψ hB m (P.f j) (P.t j) (P.adm j) (P.eta_eq j)
      (Localization.Away (P.f i * P.f j)) hC (toLeft (P.f j) (P.f i))
    show DeligneDatum.map (p : ℤ_[p]) _ _ = DeligneDatum.map (p : ℤ_[p]) _ _
    rw [ha₃, hb₃]
    exact H.theta_eq_of_eta_eq _ hC _ _ ha₁ hb₁ (ha₂.trans hb₂.symm)
  obtain ⟨d₀, hd₀, -⟩ := Omega.existsUnique_glue_of_span_eq_top (K := ℚ_[p]) (p : ℤ_[p]) B P.f P.span_eq
    (fun i => Localization.Away (P.f i)) (fun i j => Localization.Away (P.f i * P.f j))
    (fun i j => toRight (P.f i) (P.f j)) (fun i j => toLeft (P.f j) (P.f i))
    (fun i => ϑ (Localization.Away (P.f i)) ((algebraMap B (Localization.Away (P.f i))).comp ψ)
      (nilp_away p hB (P.f i)) (P.t i) (P.adm i)) hcoc
  exact ⟨d₀, hd₀⟩

theorem Hyps.eq_of_matches (H : Hyps p k ι Φ M η ϑ) {B : Type} [CommRing B] [IsNoetherianRing B]
    [Algebra ℤ_[p] B] {ψ : WittVector p k →+* B} {hB : IsNilpotent (p : B)} {m : M.obj B ψ hB}
    (P P' : Pres (ι := ι) (η := η) ψ hB m) {d d' : Om p B} (hd : P.Matches (ϑ := ϑ) d)
    (hd' : P'.Matches (ϑ := ϑ) d') : d = d' := by
  refine sep (prodCover P.f P'.f) (span_prodCover_eq_top P.f P'.f P.span_eq P'.span_eq) d d' fun l => ?_

  set i := (finProdFinEquiv.symm l).1 with hi
  set j := (finProdFinEquiv.symm l).2 with hj
  show d.map (p : ℤ_[p]) (incl p (P.f i * P'.f j)) = d'.map (p : ℤ_[p]) (incl p (P.f i * P'.f j))
  have hC : IsNilpotent (p : Localization.Away (P.f i * P'.f j)) := nilp_away p hB _
  obtain ⟨ha₁, ha₂, ha₃⟩ := H.transfer ψ hB m (P.f i) (P.t i) (P.adm i) (P.eta_eq i)
    (Localization.Away (P.f i * P'.f j)) hC (toRight (P.f i) (P'.f j))
  obtain ⟨hb₁, hb₂, hb₃⟩ := H.transfer ψ hB m (P'.f j) (P'.t j) (P'.adm j) (P'.eta_eq j)
    (Localization.Away (P.f i * P'.f j)) hC (toLeft (P'.f j) (P.f i))
  have c1 : ((toRight (P.f i) (P'.f j)).restrictScalars ℤ_[p]).comp (incl p (P.f i)) = incl p (P.f i * P'.f j) := by
    ext b; exact (toRight (P.f i) (P'.f j)).commutes b
  have c2 : ((toLeft (P'.f j) (P.f i)).restrictScalars ℤ_[p]).comp (incl p (P'.f j)) = incl p (P.f i * P'.f j) := by
    ext b; exact (toLeft (P'.f j) (P.f i)).commutes b
  rw [← c1, ← map_map, hd i, ha₃, map_congr (c1.trans c2.symm), ← map_map, hd' j, hb₃]
  exact H.theta_eq_of_eta_eq _ hC _ _ ha₁ hb₁ (ha₂.trans hb₂.symm)

def Hyps.pres (H : Hyps p k ι Φ M η ϑ) {B : Type} [CommRing B] [IsNoetherianRing B]
    (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB) : Pres (ι := ι) (η := η) ψ hB m :=
  Classical.choice (H.nonempty_pres ψ hB m)

def Hyps.theta (H : Hyps p k ι Φ M η ϑ) (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B]
    (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB) : Om p B :=
  Classical.choose (H.exists_matches (H.pres ψ hB m))

theorem Hyps.theta_matches (H : Hyps p k ι Φ M η ϑ) {B : Type} [CommRing B] [IsNoetherianRing B]
    [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB) :
    (H.pres ψ hB m).Matches (ϑ := ϑ) (H.theta B ψ hB m) :=
  Classical.choose_spec (H.exists_matches (H.pres ψ hB m))

theorem Hyps.eq_theta (H : Hyps p k ι Φ M η ϑ) {B : Type} [CommRing B] [IsNoetherianRing B]
    [Algebra ℤ_[p] B] {ψ : WittVector p k →+* B} {hB : IsNilpotent (p : B)} {m : M.obj B ψ hB}
    (P : Pres (ι := ι) (η := η) ψ hB m) {d : Om p B} (hd : P.Matches (ϑ := ϑ) d) : d = H.theta B ψ hB m :=
  H.eq_of_matches P (H.pres ψ hB m) hd (H.theta_matches ψ hB m)

def presEta (H : Hyps p k ι Φ M η ϑ) {B : Type} [CommRing B] [IsNoetherianRing B]
    (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) :
    Pres (ι := ι) (η := η) ψ hB (η B ψ hB t) where
  n := 1
  f := fun _ => 1
  span_eq := by
    rw [Ideal.eq_top_iff_one]
    exact Ideal.subset_span ⟨0, rfl⟩
  t := fun _ => t.map (algebraMap B (Localization.Away (1 : B)))
  adm := fun _ => Rigidified.IsAdmissible.map_ringHom ι ψ _ t ht
  eta_eq := fun _ => H.nat B _ ψ _ hB (nilp_away p hB 1) _ rfl t ht

theorem Hyps.theta_eta (H : Hyps p k ι Φ M η ϑ) {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B]
    (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) :
    H.theta B ψ hB (η B ψ hB t) = ϑ B ψ hB t ht := by
  refine (H.eq_theta (presEta H ψ hB t ht) fun i => ?_).symm
  exact (H.tnat_eq ψ _ hB (nilp_away p hB 1) (incl p (1 : B)) rfl t ht ((presEta H ψ hB t ht).adm i)).symm

def Hyps.presMap (H : Hyps p k ι Φ M η ϑ) {B B' : Type} [CommRing B] [CommRing B'] [IsNoetherianRing B]
    [IsNoetherianRing B'] [Algebra ℤ_[p] B] [Algebra ℤ_[p] B'] {ψ : WittVector p k →+* B}
    {ψ' : WittVector p k →+* B'} {hB : IsNilpotent (p : B)} (hB' : IsNilpotent (p : B')) (φ : B →ₐ[ℤ_[p]] B')
    (hφ : (φ : B →+* B').comp ψ = ψ') {m : M.obj B ψ hB} (P : Pres (ι := ι) (η := η) ψ hB m) :
    Pres (ι := ι) (η := η) ψ' hB' (M.map hB hB' (φ : B →+* B') hφ m) where
  n := P.n
  f := fun i => φ (P.f i)
  span_eq := span_range_comp_eq_top (φ : B →+* B') P.f P.span_eq
  t := fun i => (P.t i).map (Localization.awayMapₐ φ (P.f i) : Localization.Away (P.f i) →+* _)
  adm := fun i => by
    have h := Rigidified.IsAdmissible.map_ringHom ι ((algebraMap B (Localization.Away (P.f i))).comp ψ)
      (Localization.awayMapₐ φ (P.f i) : Localization.Away (P.f i) →+* Localization.Away (φ (P.f i))) (P.t i)
      (P.adm i)
    rwa [awayMapₐ_comp_comp φ hφ (P.f i)] at h
  eta_eq := fun i => by
    rw [H.nat _ _ ((algebraMap B (Localization.Away (P.f i))).comp ψ) _ (nilp_away p hB (P.f i))
        (nilp_away p hB' (φ (P.f i))) _ (awayMapₐ_comp_comp φ hφ (P.f i)) (P.t i) (P.adm i), P.eta_eq i,
      ← M.map_comp hB (nilp_away p hB (P.f i)) (nilp_away p hB' (φ (P.f i))) _ _ rfl
        (awayMapₐ_comp_comp φ hφ (P.f i)) m,
      ← M.map_comp hB hB' (nilp_away p hB' (φ (P.f i))) (algebraMap B' (Localization.Away (φ (P.f i))))
        (φ : B →+* B') hφ rfl m]
    exact Mmap_congr hB _ (awayMapₐ_comp φ (P.f i)) _ _ m

theorem Hyps.theta_map (H : Hyps p k ι Φ M η ϑ) {B B' : Type} [CommRing B] [CommRing B'] [IsNoetherianRing B]
    [IsNoetherianRing B'] [Algebra ℤ_[p] B] [Algebra ℤ_[p] B'] (ψ : WittVector p k →+* B)
    (ψ' : WittVector p k →+* B') (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (φ : B →ₐ[ℤ_[p]] B')
    (hφ : (φ : B →+* B').comp ψ = ψ') (m : M.obj B ψ hB) :
    H.theta B' ψ' hB' (M.map hB hB' (φ : B →+* B') hφ m) = (H.theta B ψ hB m).map (p : ℤ_[p]) φ := by
  have hadm : ∀ i, (((H.pres ψ hB m).t i).map
      (Localization.awayMapₐ φ ((H.pres ψ hB m).f i) :
            Localization.Away ((H.pres ψ hB m).f i) →+* Localization.Away (φ ((H.pres ψ hB m).f i)))).IsAdmissible ι
        ((algebraMap B' (Localization.Away (φ ((H.pres ψ hB m).f i)))).comp ψ') := fun i => by
    have h := Rigidified.IsAdmissible.map_ringHom ι ((algebraMap B (Localization.Away ((H.pres ψ hB m).f i))).comp ψ)
      (Localization.awayMapₐ φ ((H.pres ψ hB m).f i) :
        Localization.Away ((H.pres ψ hB m).f i) →+* Localization.Away (φ ((H.pres ψ hB m).f i)))
      ((H.pres ψ hB m).t i) ((H.pres ψ hB m).adm i)
    rwa [awayMapₐ_comp_comp φ hφ ((H.pres ψ hB m).f i)] at h
  have key : ∀ i, ((H.theta B ψ hB m).map (p : ℤ_[p]) φ).map (p : ℤ_[p]) (incl p (φ ((H.pres ψ hB m).f i))) =
      ϑ (Localization.Away (φ ((H.pres ψ hB m).f i)))
        ((algebraMap B' (Localization.Away (φ ((H.pres ψ hB m).f i)))).comp ψ')
        (nilp_away p hB' (φ ((H.pres ψ hB m).f i)))
        (((H.pres ψ hB m).t i).map
          (Localization.awayMapₐ φ ((H.pres ψ hB m).f i) :
            Localization.Away ((H.pres ψ hB m).f i) →+* Localization.Away (φ ((H.pres ψ hB m).f i))))
        (hadm i) := by
    intro i
    rw [map_map, map_congr (incl_comp_eq_awayMapₐ_comp_incl φ ((H.pres ψ hB m).f i)), ← map_map,
      H.theta_matches ψ hB m i]
    exact (H.tnat_eq _ _ (nilp_away p hB ((H.pres ψ hB m).f i)) (nilp_away p hB' (φ ((H.pres ψ hB m).f i)))
      (Localization.awayMapₐ φ ((H.pres ψ hB m).f i)) (awayMapₐ_comp_comp φ hφ ((H.pres ψ hB m).f i))
      ((H.pres ψ hB m).t i) ((H.pres ψ hB m).adm i) (hadm i)).symm
  exact (H.eq_theta (H.presMap hB' φ hφ (H.pres ψ hB m)) key).symm

end Frame

end ThetaDescentAux

end

open ThetaDescentAux in
theorem solution
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
    (h0 : ∀ m ∈ Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι), Φ.lieVarpi m = 0)
(M : ModuliPackage.{0, 0} p (WittVector p k)) (hM : M.IsZariskiSheaf)
(η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
Rigidified p Φ B → M.obj B ψ hB)
(hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
(t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
(η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
(∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
(hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
(hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ →
η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
(∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB),
∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
(hL : IsNilpotent (p : L)),
∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
η L ((algebraMap B L).comp ψ) hL t =
M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
    (d : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
        (t : Rigidified p Φ B), t.IsAdmissible ι ψ → OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B)
    (hiso : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
        (hB : IsNilpotent (p : B)) (t t' : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) (ht' : t'.IsAdmissible ι ψ),
        t.IsIsomorphic t' → d B ψ hB t ht = d B ψ hB t' ht')
    (hnat : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[p] B]
        [Algebra ℤ_[p] B'] (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B') (hB : IsNilpotent (p : B))
        (hB' : IsNilpotent (p : B')) (f : B →ₐ[ℤ_[p]] B') (hf : (f : B →+* B').comp ψ = ψ')
        (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) (ht' : (t.map (f : B →+* B')).IsAdmissible ι ψ'),
        DeligneDatum.IsBaseChange (K := ℚ_[p]) (π := (p : ℤ_[p])) f (d B ψ hB t ht) (d B' ψ' hB' (t.map (f : B →+* B')) ht')) :
    ∃ θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
        M.obj B ψ hB → OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B,
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
          (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ), θ B ψ hB (η B ψ hB t) = d B ψ hB t ht) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[p] B] [Algebra ℤ_[p] B']
    (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →ₐ[ℤ_[p]] B')
    (hf : (f : B →+* B').comp ψ = ψ') (x : M.obj B ψ hB),
    DeligneDatum.IsBaseChange (K := ℚ_[p]) (π := (p : ℤ_[p])) f (θ B ψ hB x)
      (θ B' ψ' hB' (M.map hB hB' (f : B →+* B') hf x))) := by
  have H : ThetaDescentAux.Hyps p k ι Φ M η d := ⟨hη.1, hη.2.1, hη.2.2, hiso, hnat⟩
  refine ⟨fun B _ _ _ ψ hB m => H.theta B ψ hB m, ?_, ?_⟩
  · intro B _ _ _ ψ hB t ht
    exact H.theta_eta ψ hB t ht
  · intro B B' _ _ _ _ _ _ ψ ψ' hB hB' f hf x
    exact (ThetaDescentAux.isBaseChange_iff f _ _).mpr (H.theta_map ψ ψ' hB hB' f hf x)

end S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_theta_apply_eta_eq_of_rule
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_theta_apply_eta_eq_of_rule (solution)
