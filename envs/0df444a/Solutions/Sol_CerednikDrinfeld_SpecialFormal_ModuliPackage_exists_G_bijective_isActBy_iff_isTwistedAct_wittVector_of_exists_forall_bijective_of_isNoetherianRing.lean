-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_G_bijective_isActBy_iff_isTwistedAct_wittVector_of_exists_forall_bijective_of_isNoetherianRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/86e11f37-2afb-5a1b-805a-e273962cea25

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_exists_det_eq_mul_pow_of_hasKernelOfDegree
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_exists_hasKernelOfDegree_of_generalLinearGroup_coe_eq
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_isPullback_of_isTranslate_of_isTranslate_zero
import Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isAdmissible_and_isTranslate_of_isTranslate_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_wittVector_of_exists_forall_bijective_of_isNoetherianRing
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace R4F4aEd2

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

theorem eq_map_of_isBaseChange {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    (d : DeligneDatum (K := K) π B) (d' : DeligneDatum (K := K) π B')
    (h : DeligneDatum.IsBaseChange (K := K) (π := π) f d d') :
    d' = DeligneDatum.map π f d :=
  DeligneDatum.ext' (funext fun M => h M)

section Frame

variable {r : ℕ} [Fact r.Prime] {k : Type} [Field k] [CharP k r] [IsAlgClosed k]
variable [Algebra ℤ_[r] (WittVector r k)]

theorem isNilpotent_natCast {B : Type} [CommRing B] [Algebra ℤ_[r] B]
    (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))) : IsNilpotent ((r : ℕ) : B) := by
  simpa only [map_natCast] using hB

theorem isNilpotent_algebraMap_localization {B : Type} [CommRing B] (hB : IsNilpotent ((r : ℕ) : B))
    (L : Type) [CommRing L] [Algebra B L] : IsNilpotent ((r : ℕ) : L) := by
  simpa only [map_natCast] using hB.map (algebraMap B L)

theorem comp_frobTwist_one (Fr : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k)
    (hFr : ∀ x : WittVector r k, Fr x = WittVector.frobenius x)
    {B : Type} [CommRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →ₐ[ℤ_[r]] B)
    {L : Type} [CommRing L] (φ : B →+* L) :
    (φ.comp (ψ : WittVector r k →+* B)).comp (WittVector.frobenius : WittVector r k →+* WittVector r k) =
      φ.comp ((frobTwist (WittVector r k) Fr 1 ψ : WittVector r k →ₐ[ℤ_[r]] B) : WittVector r k →+* B) := by
  refine RingHom.ext fun x => ?_
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, frobTwist, zpow_one, AlgHom.coe_comp,
    AlgEquiv.coe_algHom, hFr]

theorem frobTwist_one_toRingHom (Fr : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k)
    (hFr : ∀ x : WittVector r k, Fr x = WittVector.frobenius x)
    {B : Type} [CommRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →ₐ[ℤ_[r]] B) :
    ((frobTwist (WittVector r k) Fr 1 ψ : WittVector r k →ₐ[ℤ_[r]] B) : WittVector r k →+* B) =
      (ψ : WittVector r k →+* B).comp (WittVector.frobenius : WittVector r k →+* WittVector r k) := by
  have h := comp_frobTwist_one Fr hFr ψ (RingHom.id B)
  rw [RingHom.id_comp, RingHom.id_comp] at h
  exact h.symm

theorem sep_away (M : ModuliPackage.{0, 0} r (WittVector r k)) (hM : M.IsZariskiSheaf)
    {B : Type} [CommRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent ((r : ℕ) : B))
    {n : ℕ} (f : Fin n → B) (hf : Ideal.span (Set.range f) = ⊤)
    (m m' : M.obj B ψ hB)
    (h : ∀ i, M.map (ψ' := (algebraMap B (Localization.Away (f i))).comp ψ) hB
        (isNilpotent_algebraMap_localization hB (Localization.Away (f i))) (algebraMap B (Localization.Away (f i))) rfl m =
      M.map (ψ' := (algebraMap B (Localization.Away (f i))).comp ψ) hB
        (isNilpotent_algebraMap_localization hB (Localization.Away (f i))) (algebraMap B (Localization.Away (f i))) rfl m') :
    m = m' :=
  (hM B ψ hB n f hf (fun i => Localization.Away (f i))
      (fun i => isNilpotent_algebraMap_localization hB (Localization.Away (f i)))
      (fun i j => Localization.Away (f i * f j))
      (fun i j => isNilpotent_algebraMap_localization hB (Localization.Away (f i * f j)))
      (fun i j => IsLocalization.Away.awayToAwayRight (f i) (f j))
      (fun i j => IsLocalization.Away.awayToAwayLeft (f j) (f i))
      (fun i j b => IsLocalization.Away.awayToAwayRight_eq (f i) (f j) b)
      (fun i j b => IsLocalization.Away.awayToAwayLeft_eq (f j) (f i) b)).1 m m' h

variable (M : ModuliPackage.{0, 0} r (WittVector r k))
variable
  (θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
    M.obj B ψ hB → OmegaObj (K := ℚ_[r]) (r : ℤ_[r]) B)

theorem theta_map
    (hnat : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[r] B] [Algebra ℤ_[r] B']
      (ψ : WittVector r k →+* B) (ψ' : WittVector r k →+* B')
      (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →ₐ[ℤ_[r]] B')
      (hf : (f : B →+* B').comp ψ = ψ') (x : M.obj B ψ hB),
      DeligneDatum.IsBaseChange (K := ℚ_[r]) (π := (r : ℤ_[r])) f (θ B ψ hB x)
        (θ B' ψ' hB' (M.map hB hB' (f : B →+* B') hf x)))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent ((r : ℕ) : B))
    (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra ℤ_[r] L] [Algebra B L] [IsScalarTower ℤ_[r] B L]
    (hL : IsNilpotent ((r : ℕ) : L)) (m : M.obj B ψ hB) :
    θ L ((algebraMap B L).comp ψ) hL (M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m) =
      DeligneDatum.map ((r : ℕ) : ℤ_[r]) (IsScalarTower.toAlgHom ℤ_[r] B L) (θ B ψ hB m) :=
  eq_map_of_isBaseChange _ _ _ _
    (hnat B L ψ ((algebraMap B L).comp ψ) hB hL (IsScalarTower.toAlgHom ℤ_[r] B L) rfl m)

theorem theta_map_algHom
    (hnat : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[r] B] [Algebra ℤ_[r] B']
      (ψ : WittVector r k →+* B) (ψ' : WittVector r k →+* B')
      (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →ₐ[ℤ_[r]] B')
      (hf : (f : B →+* B').comp ψ = ψ') (x : M.obj B ψ hB),
      DeligneDatum.IsBaseChange (K := ℚ_[r]) (π := (r : ℤ_[r])) f (θ B ψ hB x)
        (θ B' ψ' hB' (M.map hB hB' (f : B →+* B') hf x)))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B]
    {B' : Type} [CommRing B'] [IsNoetherianRing B'] [Algebra ℤ_[r] B']
    (ψ : WittVector r k →+* B) (hB : IsNilpotent ((r : ℕ) : B)) (hB' : IsNilpotent ((r : ℕ) : B'))
    (φ : B →ₐ[ℤ_[r]] B') (m : M.obj B ψ hB) :
    θ B' ((φ : B →+* B').comp ψ) hB' (M.map (ψ' := (φ : B →+* B').comp ψ) hB hB' (φ : B →+* B') rfl m) =
      DeligneDatum.map ((r : ℕ) : ℤ_[r]) φ (θ B ψ hB m) :=
  eq_map_of_isBaseChange _ _ _ _ (hnat B B' ψ ((φ : B →+* B').comp ψ) hB hB' φ rfl m)

theorem theta_eta_congr {Φ : FormalODModule r (WittVector r k ⧸ pIdeal r (WittVector r k))}
    (η : ∀ (B : Type) [CommRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → M.obj B ψ hB)
    {L : Type} [CommRing L] [IsNoetherianRing L] [Algebra ℤ_[r] L] {ψ₁ ψ₂ : WittVector r k →+* L}
    (h : ψ₁ = ψ₂) (hL : IsNilpotent ((r : ℕ) : L)) (t : Rigidified r Φ L) :
    θ L ψ₁ hL (η L ψ₁ hL t) = θ L ψ₂ hL (η L ψ₂ hL t) := by
  subst h
  rfl

theorem isAdmissible_congr {Φ : FormalODModule r (WittVector r k ⧸ pIdeal r (WittVector r k))}
    (ι : Zp2 r →+* WittVector r k) {L : Type} [CommRing L] {ψ₁ ψ₂ : WittVector r k →+* L}
    (h : ψ₁ = ψ₂) (t : Rigidified r Φ L) : t.IsAdmissible ι ψ₁ ↔ t.IsAdmissible ι ψ₂ := by
  subst h
  exact Iff.rfl

def eG (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B]
    (x : ModuliPackage.GPoint ℤ_[r] M B) :
    (WittVector r k →ₐ[ℤ_[r]] B) × OmegaObj (K := ℚ_[r]) ((r : ℕ) : ℤ_[r]) B :=
  (x.ψ, θ B (x.ψ : WittVector r k →+* B) x.nilp x.pt)

@[scoped simp] theorem eG_fst (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B]
    (x : ModuliPackage.GPoint ℤ_[r] M B) : (eG M θ B x).1 = x.ψ := rfl

@[scoped simp] theorem eG_snd (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B]
    (x : ModuliPackage.GPoint ℤ_[r] M B) : (eG M θ B x).2 = θ B (x.ψ : WittVector r k →+* B) x.nilp x.pt := rfl

theorem eG_nat
    (hnat : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[r] B] [Algebra ℤ_[r] B']
      (ψ : WittVector r k →+* B) (ψ' : WittVector r k →+* B')
      (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →ₐ[ℤ_[r]] B')
      (hf : (f : B →+* B').comp ψ = ψ') (x : M.obj B ψ hB),
      DeligneDatum.IsBaseChange (K := ℚ_[r]) (π := (r : ℤ_[r])) f (θ B ψ hB x)
        (θ B' ψ' hB' (M.map hB hB' (f : B →+* B') hf x)))
    (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B]
    (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra ℤ_[r] B']
    (φ : B →ₐ[ℤ_[r]] B') (x : (ModuliPackage.G ℤ_[r] M).obj B) :
    eG M θ B' ((ModuliPackage.G ℤ_[r] M).map φ x) =
      (AlgFunctor.prod (AlgFunctor.corep (WittVector r k)) (Omega ℚ_[r] ((r : ℕ) : ℤ_[r]))).map φ (eG M θ B x) := by
  refine Prod.ext rfl ?_
  exact theta_map_algHom M θ hnat (x.ψ : WittVector r k →+* B) x.nilp (x.map φ).nilp φ x.pt

theorem eG_bijective
    (hbij : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
      Function.Bijective (θ B ψ hB))
    (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B]
    (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))) :
    Function.Bijective (eG M θ B) := by
  constructor
  · rintro ⟨ψ, n, m⟩ ⟨ψ', n', m'⟩ h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    subst h₁
    exact ModuliPackage.GPoint.ext' rfl (heq_of_eq ((hbij B _ n).1 h₂))
  · rintro ⟨ψ, P⟩
    have n : IsNilpotent ((r : ℕ) : B) := isNilpotent_natCast hB
    obtain ⟨m, hm⟩ := (hbij B (ψ : WittVector r k →+* B) n).2 P
    exact ⟨⟨ψ, n, m⟩, Prod.ext rfl hm⟩

variable {M}
variable (Fr : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k) (hFr : ∀ x : WittVector r k, Fr x = WittVector.frobenius x)
variable (ι : Zp2 r →+* WittVector r k) (Φ : FormalODModule r (WittVector r k ⧸ pIdeal r (WittVector r k)))
variable (hM : M.IsZariskiSheaf)
variable
  (η : ∀ (B : Type) [CommRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
    Rigidified r Φ B → M.obj B ψ hB)

include hFr hM in

theorem eG_Pi
    (hbij : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
      Function.Bijective (θ B ψ hB))
    (hnat : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[r] B] [Algebra ℤ_[r] B']
      (ψ : WittVector r k →+* B) (ψ' : WittVector r k →+* B')
      (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →ₐ[ℤ_[r]] B')
      (hf : (f : B →+* B').comp ψ = ψ') (x : M.obj B ψ hB),
      DeligneDatum.IsBaseChange (K := ℚ_[r]) (π := (r : ℤ_[r])) f (θ B ψ hB x)
        (θ B' ψ' hB' (M.map hB hB' (f : B →+* B') hf x)))
    (hPieq : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B))
        (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ →
          t'.IsAdmissible ι (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) →
          t'.X.F = t.X.F → t'.X.varpi = t.X.varpi → (∀ a, t'.X.act a = t.X.act (WittVector.frobenius a)) →
          (∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ r) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ)))) →
          θ B (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) hB
              (η B (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) hB t') =
            θ B ψ hB (η B ψ hB t))
    (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B]
    (x x' : (ModuliPackage.G ℤ_[r] M).obj B)
    (hx : ModuliPackage.G.IsPiTranslate ι Φ η Fr x x') :
    eG M θ B x' = (frobTwist (WittVector r k) Fr 1 (eG M θ B x).1, (eG M θ B x).2) := by
  obtain ⟨hψ, n, f, hf, hcov⟩ := hx
  refine Prod.ext hψ ?_
  show θ B (x'.ψ : WittVector r k →+* B) x'.nilp x'.pt = θ B (x.ψ : WittVector r k →+* B) x.nilp x.pt

  set P := θ B (x.ψ : WittVector r k →+* B) x.nilp x.pt with hP
  obtain ⟨m₃, hm₃⟩ := (hbij B (x'.ψ : WittVector r k →+* B) x'.nilp).2 P
  rw [← hm₃]
  congr 1

  refine sep_away M hM (x'.ψ : WittVector r k →+* B) x'.nilp f hf x'.pt m₃ fun i => ?_
  have hL : IsNilpotent ((r : ℕ) : Localization.Away (f i)) :=
    isNilpotent_algebraMap_localization x.nilp (Localization.Away (f i))
  obtain ⟨t, t', ht, ht', hηt, hηt', hrel⟩ := hcov i (Localization.Away (f i)) hL

  apply (hbij (Localization.Away (f i)) ((algebraMap B (Localization.Away (f i))).comp (x'.ψ : WittVector r k →+* B)) hL).1
  have hleg : ((algebraMap B (Localization.Away (f i))).comp (x.ψ : WittVector r k →+* B)).comp
      (WittVector.frobenius : WittVector r k →+* WittVector r k) =
      (algebraMap B (Localization.Away (f i))).comp (x'.ψ : WittVector r k →+* B) := by
    rw [hψ]; exact comp_frobTwist_one Fr hFr x.ψ _
  obtain ⟨hF, hϖ, hact, c, hc⟩ := hrel
  calc θ (Localization.Away (f i)) ((algebraMap B (Localization.Away (f i))).comp (x'.ψ : WittVector r k →+* B)) hL
          (M.map (ψ' := (algebraMap B (Localization.Away (f i))).comp (x'.ψ : WittVector r k →+* B)) x'.nilp hL
            (algebraMap B (Localization.Away (f i))) rfl x'.pt)
        = θ (Localization.Away (f i)) ((algebraMap B (Localization.Away (f i))).comp (x'.ψ : WittVector r k →+* B)) hL
            (η (Localization.Away (f i)) ((algebraMap B (Localization.Away (f i))).comp (x'.ψ : WittVector r k →+* B)) hL t') := by
          rw [hηt']
    _ = θ (Localization.Away (f i))
            (((algebraMap B (Localization.Away (f i))).comp (x.ψ : WittVector r k →+* B)).comp
              (WittVector.frobenius : WittVector r k →+* WittVector r k)) hL
            (η (Localization.Away (f i))
              (((algebraMap B (Localization.Away (f i))).comp (x.ψ : WittVector r k →+* B)).comp
                (WittVector.frobenius : WittVector r k →+* WittVector r k)) hL t') :=
          theta_eta_congr M θ η hleg.symm hL t'
    _ = θ (Localization.Away (f i)) ((algebraMap B (Localization.Away (f i))).comp (x.ψ : WittVector r k →+* B)) hL
            (η (Localization.Away (f i)) ((algebraMap B (Localization.Away (f i))).comp (x.ψ : WittVector r k →+* B)) hL t) :=
          hPieq (Localization.Away (f i)) _ hL t t' ht ((isAdmissible_congr ι hleg t').2 ht') hF hϖ hact ⟨c, hc⟩
    _ = θ (Localization.Away (f i)) ((algebraMap B (Localization.Away (f i))).comp (x.ψ : WittVector r k →+* B)) hL
            (M.map (ψ' := (algebraMap B (Localization.Away (f i))).comp (x.ψ : WittVector r k →+* B)) x.nilp hL
              (algebraMap B (Localization.Away (f i))) rfl x.pt) := by rw [hηt]
    _ = DeligneDatum.map ((r : ℕ) : ℤ_[r]) (IsScalarTower.toAlgHom ℤ_[r] B (Localization.Away (f i))) P :=
          theta_map M θ hnat _ x.nilp _ hL x.pt
    _ = DeligneDatum.map ((r : ℕ) : ℤ_[r]) (IsScalarTower.toAlgHom ℤ_[r] B (Localization.Away (f i)))
            (θ B (x'.ψ : WittVector r k →+* B) x'.nilp m₃) := by rw [hm₃]
    _ = θ (Localization.Away (f i)) ((algebraMap B (Localization.Away (f i))).comp (x'.ψ : WittVector r k →+* B)) hL
          (M.map (ψ' := (algebraMap B (Localization.Away (f i))).comp (x'.ψ : WittVector r k →+* B)) x'.nilp hL
            (algebraMap B (Localization.Away (f i))) rfl m₃) :=
          (theta_map M θ hnat _ x'.nilp _ hL m₃).symm

include hFr in

theorem G_piTotal
    (hbij : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
      Function.Bijective (θ B ψ hB))
    (hnat : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[r] B] [Algebra ℤ_[r] B']
      (ψ : WittVector r k →+* B) (ψ' : WittVector r k →+* B')
      (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →ₐ[ℤ_[r]] B')
      (hf : (f : B →+* B').comp ψ = ψ') (x : M.obj B ψ hB),
      DeligneDatum.IsBaseChange (K := ℚ_[r]) (π := (r : ℤ_[r])) f (θ B ψ hB x)
        (θ B' ψ' hB' (M.map hB hB' (f : B →+* B') hf x)))
    (hη₃ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m)
    (hPidef : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          ∃ t' : Rigidified r Φ B,
            t'.IsAdmissible ι (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) ∧
            t'.X.F = t.X.F ∧ t'.X.varpi = t.X.varpi ∧ (∀ a, t'.X.act a = t.X.act (WittVector.frobenius a)) ∧
            ∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ r) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ))))
    (hPieq : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B))
        (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ →
          t'.IsAdmissible ι (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) →
          t'.X.F = t.X.F → t'.X.varpi = t.X.varpi → (∀ a, t'.X.act a = t.X.act (WittVector.frobenius a)) →
          (∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ r) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ)))) →
          θ B (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) hB
              (η B (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) hB t') =
            θ B ψ hB (η B ψ hB t))
    (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B]
    (x : (ModuliPackage.G ℤ_[r] M).obj B) :
    ∃ x' : (ModuliPackage.G ℤ_[r] M).obj B, ModuliPackage.G.IsPiTranslate ι Φ η Fr x x' := by

  set ψ' : WittVector r k →ₐ[ℤ_[r]] B := frobTwist (WittVector r k) Fr 1 x.ψ with hψ'
  set P := θ B (x.ψ : WittVector r k →+* B) x.nilp x.pt with hP
  obtain ⟨m', hm'⟩ := (hbij B (ψ' : WittVector r k →+* B) x.nilp).2 P
  refine ⟨⟨ψ', x.nilp, m'⟩, rfl, ?_⟩

  obtain ⟨n, f, hf, hcov⟩ := hη₃ B (x.ψ : WittVector r k →+* B) x.nilp x.pt
  refine ⟨n, f, hf, fun i L _ _ _ hL => ?_⟩
  haveI : IsNoetherianRing L := IsLocalization.isNoetherianRing (Submonoid.powers (f i)) L inferInstance
  letI : Algebra ℤ_[r] L := ((algebraMap B L).comp (algebraMap ℤ_[r] B)).toAlgebra
  haveI : IsScalarTower ℤ_[r] B L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨t, ht, hηt⟩ := hcov i L hL
  obtain ⟨t', ht', hF, hϖ, hact, c, hc⟩ := hPidef L ((algebraMap B L).comp (x.ψ : WittVector r k →+* B)) t ht
  have hleg : ((algebraMap B L).comp (x.ψ : WittVector r k →+* B)).comp
      (WittVector.frobenius : WittVector r k →+* WittVector r k) =
      (algebraMap B L).comp (ψ' : WittVector r k →+* B) := comp_frobTwist_one Fr hFr x.ψ _
  refine ⟨t, t', ht, (isAdmissible_congr ι hleg t').1 ht', hηt, ?_, hF, hϖ, hact, c, hc⟩

  apply (hbij L ((algebraMap B L).comp (ψ' : WittVector r k →+* B)) hL).1
  calc θ L ((algebraMap B L).comp (ψ' : WittVector r k →+* B)) hL (η L ((algebraMap B L).comp (ψ' : WittVector r k →+* B)) hL t')
        = θ L (((algebraMap B L).comp (x.ψ : WittVector r k →+* B)).comp
              (WittVector.frobenius : WittVector r k →+* WittVector r k)) hL
            (η L (((algebraMap B L).comp (x.ψ : WittVector r k →+* B)).comp
              (WittVector.frobenius : WittVector r k →+* WittVector r k)) hL t') :=
          theta_eta_congr M θ η hleg.symm hL t'
    _ = θ L ((algebraMap B L).comp (x.ψ : WittVector r k →+* B)) hL
            (η L ((algebraMap B L).comp (x.ψ : WittVector r k →+* B)) hL t) :=
          hPieq L _ hL t t' ht ht' hF hϖ hact ⟨c, hc⟩
    _ = θ L ((algebraMap B L).comp (x.ψ : WittVector r k →+* B)) hL
            (M.map (ψ' := (algebraMap B L).comp (x.ψ : WittVector r k →+* B)) x.nilp hL (algebraMap B L) rfl x.pt) := by
          rw [hηt]
    _ = DeligneDatum.map ((r : ℕ) : ℤ_[r]) (IsScalarTower.toAlgHom ℤ_[r] B L) P := theta_map M θ hnat _ x.nilp _ hL x.pt
    _ = DeligneDatum.map ((r : ℕ) : ℤ_[r]) (IsScalarTower.toAlgHom ℤ_[r] B L) (θ B (ψ' : WittVector r k →+* B) x.nilp m') := by
          rw [hm']
    _ = θ L ((algebraMap B L).comp (ψ' : WittVector r k →+* B)) hL
          (M.map (ψ' := (algebraMap B L).comp (ψ' : WittVector r k →+* B)) x.nilp hL (algebraMap B L) rfl m') :=
          (theta_map M θ hnat _ x.nilp _ hL m').symm

theorem exists_apply_eq_pow_smul_inv
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r])
    (m : ℕ) (hm : ∀ A : Matrix (Fin 2) (Fin 2) ℤ_[r], ∃ e, E e = (r : ℚ_[r]) ^ m • A.map ((↑) : ℤ_[r] → ℚ_[r]))
    (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) :
    ∃ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (k : ℕ),
      E e = (r : ℚ_[r]) ^ k • ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) : Matrix (Fin 2) (Fin 2) ℚ_[r]) := by

  have hden : ∀ x : ℚ_[r], ∃ j : ℕ, ‖(r : ℚ_[r]) ^ j * x‖ ≤ 1 := by
    intro x
    by_cases hx : x = 0
    · exact ⟨0, by simp [hx]⟩
    have hr : (1 : ℝ) < r := by exact_mod_cast (Fact.out : r.Prime).one_lt
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt ‖x‖ hr
    refine ⟨j, ?_⟩
    rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, ← div_eq_inv_mul, div_le_one (by positivity)]
    exact hj.le
  choose j hj using hden
  set G : Matrix (Fin 2) (Fin 2) ℚ_[r] := ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) : Matrix (Fin 2) (Fin 2) ℚ_[r])
  set J : ℕ := ∑ i, ∑ i', j (G i i') with hJ
  have hle : ∀ i i', j (G i i') ≤ J := fun i i' =>
    (Finset.single_le_sum (f := fun i'' => j (G i i'')) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i')).trans
      (Finset.single_le_sum (f := fun i'' => ∑ i', j (G i'' i')) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have hint : ∀ i i', ‖(r : ℚ_[r]) ^ J * G i i'‖ ≤ 1 := by
    intro i i'
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (hle i i')
    rw [hd, add_comm, pow_add, mul_assoc, norm_mul, norm_pow, Padic.norm_p]
    calc (r : ℝ)⁻¹ ^ d * ‖(r : ℚ_[r]) ^ j (G i i') * G i i'‖ ≤ 1 ^ d * 1 := by
          gcongr
          · exact inv_le_one_of_one_le₀ (by exact_mod_cast (Fact.out : r.Prime).one_lt.le)
          · exact hj _
      _ = 1 := by rw [one_pow, one_mul]
  let A : Matrix (Fin 2) (Fin 2) ℤ_[r] := fun i i' => ⟨(r : ℚ_[r]) ^ J * G i i', hint i i'⟩
  obtain ⟨e, he⟩ := hm A
  refine ⟨e, m + J, ?_⟩
  rw [he, pow_add, mul_smul]
  congr 1

end Frame

section Scalars

open LT.LatticeTree

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (B : Type) [CommRing B] [Algebra 𝒪 B]

theorem isPullback_iff_eq_pullback (g : Matrix.GeneralLinearGroup (Fin 2) K) (d d' : DeligneDatum (K := K) π B) :
    DeligneDatum.IsPullback (K := K) (π := π) B g d d' ↔ d' = DeligneDatum.pullback π B g d :=
  ⟨fun h => DeligneDatum.ext' (funext h), fun h => h ▸ DeligneDatum.isPullback_pullback π B g d⟩

theorem pullback_scalarGL (c : Kˣ) (d : DeligneDatum (K := K) π B) :
    DeligneDatum.pullback π B (scalarGL c) d = d := by
  apply DeligneDatum.ext'
  funext M
  show (d.line (FullLattice.act (scalarGL c) M)).comap (actBaseChange B (scalarGL c) M).toLinearMap = d.line M
  rw [d.homothety c M]
  exact Submodule.comap_map_eq_of_injective (actBaseChange B (scalarGL c) M).injective _

theorem pullback_mul (g h : Matrix.GeneralLinearGroup (Fin 2) K) (d : DeligneDatum (K := K) π B) :
    DeligneDatum.pullback π B (g * h) d = DeligneDatum.pullback π B h (DeligneDatum.pullback π B g d) := by
  have := (Omega.action K π).act_mul B h⁻¹ g⁻¹ d
  change DeligneDatum.pullback π B (h⁻¹ * g⁻¹)⁻¹ d =
    DeligneDatum.pullback π B h⁻¹⁻¹ (DeligneDatum.pullback π B g⁻¹⁻¹ d) at this
  simpa only [_root_.mul_inv_rev, inv_inv] using this

theorem isPullback_scalarGL_mul_iff (c : Kˣ) (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (d d' : DeligneDatum (K := K) π B) :
    DeligneDatum.IsPullback (K := K) (π := π) B (scalarGL c * g) d d' ↔
      DeligneDatum.IsPullback (K := K) (π := π) B g d d' := by
  rw [isPullback_iff_eq_pullback, isPullback_iff_eq_pullback, pullback_mul, pullback_scalarGL]

theorem isPullback_iff_of_coe_eq_smul {c : K} (hc : c ≠ 0) (g₁ g₂ : Matrix.GeneralLinearGroup (Fin 2) K)
    (h : (g₁ : Matrix (Fin 2) (Fin 2) K) = c • (g₂ : Matrix (Fin 2) (Fin 2) K))
    (d d' : DeligneDatum (K := K) π B) :
    DeligneDatum.IsPullback (K := K) (π := π) B g₁ d d' ↔ DeligneDatum.IsPullback (K := K) (π := π) B g₂ d d' := by
  have hg : g₁ = scalarGL (Units.mk0 c hc) * g₂ := by
    apply Units.ext
    rw [h, Units.val_mul, scalarGL_coe, Units.val_mk0, Matrix.smul_mul, Matrix.one_mul]
  rw [hg, isPullback_scalarGL_mul_iff]

theorem isPullback_inv_iff_of_coe_eq_smul {c : K} (hc : c ≠ 0) (g₁ g₂ : Matrix.GeneralLinearGroup (Fin 2) K)
    (h : (g₁ : Matrix (Fin 2) (Fin 2) K) = c • (g₂ : Matrix (Fin 2) (Fin 2) K))
    (d d' : DeligneDatum (K := K) π B) :
    DeligneDatum.IsPullback (K := K) (π := π) B g₁⁻¹ d d' ↔ DeligneDatum.IsPullback (K := K) (π := π) B g₂⁻¹ d d' := by
  refine isPullback_iff_of_coe_eq_smul π B (inv_ne_zero hc) g₁⁻¹ g₂⁻¹ ?_ d d'
  have hg : g₁ = scalarGL (Units.mk0 c hc) * g₂ := by
    apply Units.ext
    rw [h, Units.val_mul, scalarGL_coe, Units.val_mk0, Matrix.smul_mul, Matrix.one_mul]
  have hinv : (scalarGL (Units.mk0 c hc))⁻¹ = scalarGL (Units.mk0 c hc)⁻¹ :=
    inv_eq_of_mul_eq_one_right (by rw [← scalarGL_mul, mul_inv_cancel, scalarGL_one])
  rw [hg, _root_.mul_inv_rev, hinv, ← scalarGL_mul_comm, Units.val_mul, scalarGL_coe, Matrix.smul_mul, Matrix.one_mul,
    Units.val_inv_eq_inv_val, Units.val_mk0]

end Scalars

section GLclause

open LT.LatticeTree

variable {r : ℕ} [Fact r.Prime] {k : Type} [Field k] [CharP k r] [IsAlgClosed k]
variable [Algebra ℤ_[r] (WittVector r k)]
variable (Fr : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k)
variable (ι : Zp2 r →+* WittVector r k) (Φ : FormalODModule r (WittVector r k ⧸ pIdeal r (WittVector r k)))
variable (M : ModuliPackage.{0, 0} r (WittVector r k))
variable
  (θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
    M.obj B ψ hB → OmegaObj (K := ℚ_[r]) (r : ℤ_[r]) B)
variable
  (η : ∀ (B : Type) [CommRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
    Rigidified r Φ B → M.obj B ψ hB)
variable (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r])

abbrev frPow (n : ℤ) : WittVector r k →+* WittVector r k :=
  (((Fr ^ n : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k) : WittVector r k →ₐ[ℤ_[r]] WittVector r k) :
    WittVector r k →+* WittVector r k)

theorem comp_frobTwist {B : Type} [CommRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →ₐ[ℤ_[r]] B)
    {L : Type} [CommRing L] (φ : B →+* L) (n : ℤ) :
    (φ.comp (ψ : WittVector r k →+* B)).comp (frPow Fr n) =
      φ.comp ((frobTwist (WittVector r k) Fr n ψ : WittVector r k →ₐ[ℤ_[r]] B) : WittVector r k →+* B) :=
  RingHom.ext fun _ => rfl

abbrev HDet : Prop :=
  ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ),
    FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) →
    ∃ u : ℤ_[r]ˣ, (E e).det = ((u : ℤ_[r]) : ℚ_[r]) * (r : ℚ_[r]) ^ m'

abbrev HIso : Prop :=
  ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]),
    (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e →
    ∃ m' : ℕ, FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m'))

abbrev HLocFwd : Prop :=
  ∀ (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra ℤ_[r] L] (ψ : WittVector r k →+* L) (hL : IsNilpotent (r : L))
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (kk m' : ℕ),
    FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) →
    ∀ (g₀ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]), (g₀ : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e →
    ∀ (t t' : Rigidified r Φ L), t.IsAdmissible ι ψ → t'.IsAdmissible ι (ψ.comp (frPow Fr ((m' : ℤ) - 2 * kk))) →
      Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries kk m' ψ t t' →
      DeligneDatum.IsPullback (K := ℚ_[r]) (π := (r : ℤ_[r])) L g₀ (θ L ψ hL (η L ψ hL t))
        (θ L (ψ.comp (frPow Fr ((m' : ℤ) - 2 * kk))) hL (η L (ψ.comp (frPow Fr ((m' : ℤ) - 2 * kk))) hL t'))

abbrev HEx : Prop :=
  ∀ (L : Type) [CommRing L] [IsNoetherianRing L] (ψ : WittVector r k →+* L) (t : Rigidified r Φ L), t.IsAdmissible ι ψ →
    ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (kk m' : ℕ),
    FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) →
    ∃ t' : Rigidified r Φ L, t'.IsAdmissible ι (ψ.comp (frPow Fr ((m' : ℤ) - 2 * kk))) ∧
      Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries kk m' ψ t t'

theorem rpow_ne_zero (kk : ℕ) : (r : ℚ_[r]) ^ kk ≠ 0 :=
  pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : r.Prime).ne_zero)

def gzero (kk : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r] :=
  scalarGL (Units.mk0 ((r : ℚ_[r]) ^ kk) (rpow_ne_zero kk)) * g⁻¹

theorem coe_gzero (kk : ℕ) (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) :
    (gzero kk g : Matrix (Fin 2) (Fin 2) ℚ_[r]) =
      (r : ℚ_[r]) ^ kk • ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) : Matrix (Fin 2) (Fin 2) ℚ_[r]) := by
  rw [gzero, Units.val_mul, scalarGL_coe, Units.val_mk0, Matrix.smul_mul, Matrix.one_mul]

theorem vdet_eq
    (vdet : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r] →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : ℤ_[r]ˣ, (Matrix.GeneralLinearGroup.det g : ℚ_[r]) = algebraMap ℤ_[r] ℚ_[r] (u : ℤ_[r]) * (algebraMap ℤ_[r] ℚ_[r] ((r : ℕ) : ℤ_[r])) ^ n)
    (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (kk m' : ℕ) (u : ℤ_[r]ˣ) (A : Matrix (Fin 2) (Fin 2) ℚ_[r])
    (hA : A = (r : ℚ_[r]) ^ kk • ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) : Matrix (Fin 2) (Fin 2) ℚ_[r]))
    (hu : A.det = ((u : ℤ_[r]) : ℚ_[r]) * (r : ℚ_[r]) ^ m') :
    vdet g = Multiplicative.ofAdd (2 * (kk : ℤ) - m') := by
  apply (hvdet g _).2
  refine ⟨u⁻¹, ?_⟩
  have hR : (algebraMap ℤ_[r] ℚ_[r] ((r : ℕ) : ℤ_[r])) = (r : ℚ_[r]) := map_natCast _ r
  have hU : algebraMap ℤ_[r] ℚ_[r] ((u⁻¹ : ℤ_[r]ˣ) : ℤ_[r]) * algebraMap ℤ_[r] ℚ_[r] (u : ℤ_[r]) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hUu : algebraMap ℤ_[r] ℚ_[r] (u : ℤ_[r]) = ((u : ℤ_[r]) : ℚ_[r]) := rfl
  rw [hR]
  rw [hA, Matrix.det_smul, Fintype.card_fin, ← Matrix.GeneralLinearGroup.val_det_apply, map_inv,
    Units.val_inv_eq_inv_val] at hu
  set d : ℚ_[r] := (Matrix.GeneralLinearGroup.det g : ℚ_[r]) with hd
  have hd0 : d ≠ 0 := (Matrix.GeneralLinearGroup.det g).ne_zero
  set U := algebraMap ℤ_[r] ℚ_[r] (u : ℤ_[r])
  set U' := algebraMap ℤ_[r] ℚ_[r] ((u⁻¹ : ℤ_[r]ˣ) : ℤ_[r])
  set R := (r : ℚ_[r]) with hRdef
  have hR0 : R ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : r.Prime).ne_zero
  have hU0 : U ≠ 0 := by rintro h0; rw [h0, mul_zero] at hU; exact zero_ne_one hU
  have hU' : U' = U⁻¹ := by field_simp; linear_combination hU
  rw [hUu] at hU0 hU'
  rw [hU', zpow_sub₀ hR0, show (2 * (kk : ℤ)) = ((2 * kk : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast,
    pow_mul]
  rw [eq_comm] at hu
  field_simp at hu ⊢
  linear_combination hu

variable {M}

theorem GL_fwd
    (vdet : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r] →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : ℤ_[r]ˣ, (Matrix.GeneralLinearGroup.det g : ℚ_[r]) = algebraMap ℤ_[r] ℚ_[r] (u : ℤ_[r]) * (algebraMap ℤ_[r] ℚ_[r] ((r : ℕ) : ℤ_[r])) ^ n)
    (hM : M.IsZariskiSheaf)
    (hbij : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
      Function.Bijective (θ B ψ hB))
    (hnat : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[r] B] [Algebra ℤ_[r] B']
      (ψ : WittVector r k →+* B) (ψ' : WittVector r k →+* B')
      (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →ₐ[ℤ_[r]] B')
      (hf : (f : B →+* B').comp ψ = ψ') (x : M.obj B ψ hB),
      DeligneDatum.IsBaseChange (K := ℚ_[r]) (π := (r : ℤ_[r])) f (θ B ψ hB x)
        (θ B' ψ' hB' (M.map hB hB' (f : B →+* B') hf x)))
    (hDet : HDet Φ E) (hLoc : HLocFwd Fr ι Φ M θ η E)
    (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B]
    (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (x x' : (ModuliPackage.G ℤ_[r] M).obj B)
    (h : ModuliPackage.G.IsActBy ι Φ η Fr E g x x') :
    OmegaNr.IsTwistedAct ((r : ℕ) : ℤ_[r]) (WittVector r k) Fr vdet B g (eG M θ B x) (eG M θ B x') := by
  obtain ⟨e, kk, m', hEe, hker, hleg, n, f, hf, hcov⟩ := h
  have hg₀ : (gzero kk g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e := by rw [coe_gzero, hEe]
  obtain ⟨u, hu⟩ := hDet e m' hker
  refine ⟨?_, ?_⟩
  ·
    show x'.ψ = frobTwist (WittVector r k) Fr (-Multiplicative.toAdd (vdet g)) x.ψ
    rw [vdet_eq vdet hvdet g kk m' u (E e) hEe hu, toAdd_ofAdd, neg_sub]
    exact hleg
  ·
    show DeligneDatum.IsPullback (K := ℚ_[r]) (π := ((r : ℕ) : ℤ_[r])) B g⁻¹
      (θ B (x.ψ : WittVector r k →+* B) x.nilp x.pt) (θ B (x'.ψ : WittVector r k →+* B) x'.nilp x'.pt)
    refine (isPullback_iff_of_coe_eq_smul ((r : ℕ) : ℤ_[r]) B (rpow_ne_zero kk) (gzero kk g) g⁻¹ (coe_gzero kk g) _ _).1 ?_
    rw [isPullback_iff_eq_pullback]
    set Q := DeligneDatum.pullback ((r : ℕ) : ℤ_[r]) B (gzero kk g) (θ B (x.ψ : WittVector r k →+* B) x.nilp x.pt) with hQ
    obtain ⟨m₃, hm₃⟩ := (hbij B (x'.ψ : WittVector r k →+* B) x'.nilp).2 Q
    rw [← hm₃]
    congr 1
    refine sep_away M hM (x'.ψ : WittVector r k →+* B) x'.nilp f hf x'.pt m₃ fun i => ?_
    have hL : IsNilpotent ((r : ℕ) : Localization.Away (f i)) :=
      isNilpotent_algebraMap_localization x.nilp (Localization.Away (f i))
    obtain ⟨t, t', ht, ht', hηt, hηt', hrel⟩ := hcov i (Localization.Away (f i)) hL
    apply (hbij (Localization.Away (f i)) ((algebraMap B (Localization.Away (f i))).comp (x'.ψ : WittVector r k →+* B)) hL).1
    have hlegL : ((algebraMap B (Localization.Away (f i))).comp (x.ψ : WittVector r k →+* B)).comp
        (frPow Fr ((m' : ℤ) - 2 * kk)) =
        (algebraMap B (Localization.Away (f i))).comp (x'.ψ : WittVector r k →+* B) := by
      rw [hleg]; exact comp_frobTwist Fr x.ψ _ _
    have hpb := hLoc (Localization.Away (f i)) ((algebraMap B (Localization.Away (f i))).comp (x.ψ : WittVector r k →+* B))
      hL e kk m' hker (gzero kk g) hg₀ t t' ht ((isAdmissible_congr ι hlegL t').2 ht') hrel
    rw [isPullback_iff_eq_pullback] at hpb
    calc θ (Localization.Away (f i)) ((algebraMap B (Localization.Away (f i))).comp (x'.ψ : WittVector r k →+* B)) hL
          (M.map (ψ' := (algebraMap B (Localization.Away (f i))).comp (x'.ψ : WittVector r k →+* B)) x'.nilp hL
            (algebraMap B (Localization.Away (f i))) rfl x'.pt)
        = θ (Localization.Away (f i)) ((algebraMap B (Localization.Away (f i))).comp (x'.ψ : WittVector r k →+* B)) hL
            (η (Localization.Away (f i)) ((algebraMap B (Localization.Away (f i))).comp (x'.ψ : WittVector r k →+* B)) hL t') := by
          rw [hηt']
      _ = θ (Localization.Away (f i))
            (((algebraMap B (Localization.Away (f i))).comp (x.ψ : WittVector r k →+* B)).comp (frPow Fr ((m' : ℤ) - 2 * kk))) hL
            (η (Localization.Away (f i))
              (((algebraMap B (Localization.Away (f i))).comp (x.ψ : WittVector r k →+* B)).comp (frPow Fr ((m' : ℤ) - 2 * kk)))
              hL t') := theta_eta_congr M θ η hlegL.symm hL t'
      _ = DeligneDatum.pullback ((r : ℕ) : ℤ_[r]) (Localization.Away (f i)) (gzero kk g)
            (θ (Localization.Away (f i)) ((algebraMap B (Localization.Away (f i))).comp (x.ψ : WittVector r k →+* B)) hL
              (η (Localization.Away (f i)) ((algebraMap B (Localization.Away (f i))).comp (x.ψ : WittVector r k →+* B)) hL t)) := hpb
      _ = DeligneDatum.pullback ((r : ℕ) : ℤ_[r]) (Localization.Away (f i)) (gzero kk g)
            (θ (Localization.Away (f i)) ((algebraMap B (Localization.Away (f i))).comp (x.ψ : WittVector r k →+* B)) hL
              (M.map (ψ' := (algebraMap B (Localization.Away (f i))).comp (x.ψ : WittVector r k →+* B)) x.nilp hL
                (algebraMap B (Localization.Away (f i))) rfl x.pt)) := by rw [hηt]
      _ = DeligneDatum.pullback ((r : ℕ) : ℤ_[r]) (Localization.Away (f i)) (gzero kk g)
            (DeligneDatum.map ((r : ℕ) : ℤ_[r]) (IsScalarTower.toAlgHom ℤ_[r] B (Localization.Away (f i)))
              (θ B (x.ψ : WittVector r k →+* B) x.nilp x.pt)) := by rw [theta_map M θ hnat _ x.nilp _ hL x.pt]
      _ = DeligneDatum.map ((r : ℕ) : ℤ_[r]) (IsScalarTower.toAlgHom ℤ_[r] B (Localization.Away (f i))) Q :=
          (DeligneDatum.map_pullback _ _ _ _).symm
      _ = DeligneDatum.map ((r : ℕ) : ℤ_[r]) (IsScalarTower.toAlgHom ℤ_[r] B (Localization.Away (f i)))
            (θ B (x'.ψ : WittVector r k →+* B) x'.nilp m₃) := by rw [hm₃]
      _ = θ (Localization.Away (f i)) ((algebraMap B (Localization.Away (f i))).comp (x'.ψ : WittVector r k →+* B)) hL
          (M.map (ψ' := (algebraMap B (Localization.Away (f i))).comp (x'.ψ : WittVector r k →+* B)) x'.nilp hL
            (algebraMap B (Localization.Away (f i))) rfl m₃) := (theta_map M θ hnat _ x'.nilp _ hL m₃).symm

theorem GL_bwd
    (vdet : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r] →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : ℤ_[r]ˣ, (Matrix.GeneralLinearGroup.det g : ℚ_[r]) = algebraMap ℤ_[r] ℚ_[r] (u : ℤ_[r]) * (algebraMap ℤ_[r] ℚ_[r] ((r : ℕ) : ℤ_[r])) ^ n)
    (hbij : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
      Function.Bijective (θ B ψ hB))
    (hnat : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[r] B] [Algebra ℤ_[r] B']
      (ψ : WittVector r k →+* B) (ψ' : WittVector r k →+* B')
      (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →ₐ[ℤ_[r]] B')
      (hf : (f : B →+* B').comp ψ = ψ') (x : M.obj B ψ hB),
      DeligneDatum.IsBaseChange (K := ℚ_[r]) (π := (r : ℤ_[r])) f (θ B ψ hB x)
        (θ B' ψ' hB' (M.map hB hB' (f : B →+* B') hf x)))
    (hη₃ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m)
    (m : ℕ) (hm : ∀ A : Matrix (Fin 2) (Fin 2) ℤ_[r], ∃ e, E e = (r : ℚ_[r]) ^ m • A.map ((↑) : ℤ_[r] → ℚ_[r]))
    (hDet : HDet Φ E) (hIso : HIso Φ E) (hLoc : HLocFwd Fr ι Φ M θ η E) (hEx : HEx Fr ι Φ)
    (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B]
    (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (x x' : (ModuliPackage.G ℤ_[r] M).obj B)
    (h : OmegaNr.IsTwistedAct ((r : ℕ) : ℤ_[r]) (WittVector r k) Fr vdet B g (eG M θ B x) (eG M θ B x')) :
    ModuliPackage.G.IsActBy ι Φ η Fr E g x x' := by
  obtain ⟨hleg', hpb⟩ := h
  change x'.ψ = frobTwist (WittVector r k) Fr (-Multiplicative.toAdd (vdet g)) x.ψ at hleg'
  change DeligneDatum.IsPullback (K := ℚ_[r]) (π := ((r : ℕ) : ℤ_[r])) B g⁻¹
    (θ B (x.ψ : WittVector r k →+* B) x.nilp x.pt) (θ B (x'.ψ : WittVector r k →+* B) x'.nilp x'.pt) at hpb

  obtain ⟨e, kk, hEe⟩ := exists_apply_eq_pow_smul_inv Φ E m hm g
  have hg₀ : (gzero kk g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e := by rw [coe_gzero, hEe]
  obtain ⟨m', hker⟩ := hIso e (gzero kk g) hg₀
  obtain ⟨u, hu⟩ := hDet e m' hker
  have hleg : x'.ψ = frobTwist (WittVector r k) Fr ((m' : ℤ) - 2 * kk) x.ψ := by
    rw [vdet_eq vdet hvdet g kk m' u (E e) hEe hu, toAdd_ofAdd, neg_sub] at hleg'
    exact hleg'
  have hpb' : θ B (x'.ψ : WittVector r k →+* B) x'.nilp x'.pt =
      DeligneDatum.pullback ((r : ℕ) : ℤ_[r]) B (gzero kk g) (θ B (x.ψ : WittVector r k →+* B) x.nilp x.pt) :=
    (isPullback_iff_eq_pullback _ B _ _ _).1
      ((isPullback_iff_of_coe_eq_smul ((r : ℕ) : ℤ_[r]) B (rpow_ne_zero kk) (gzero kk g) g⁻¹ (coe_gzero kk g) _ _).2 hpb)
  refine ⟨e, kk, m', hEe, hker, hleg, ?_⟩

  obtain ⟨n, f, hf, hcov⟩ := hη₃ B (x.ψ : WittVector r k →+* B) x.nilp x.pt
  refine ⟨n, f, hf, fun i L _ _ _ hL => ?_⟩
  haveI : IsNoetherianRing L := IsLocalization.isNoetherianRing (Submonoid.powers (f i)) L inferInstance
  letI : Algebra ℤ_[r] L := ((algebraMap B L).comp (algebraMap ℤ_[r] B)).toAlgebra
  haveI : IsScalarTower ℤ_[r] B L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨t, ht, hηt⟩ := hcov i L hL
  obtain ⟨t', ht', hrel⟩ := hEx L ((algebraMap B L).comp (x.ψ : WittVector r k →+* B)) t ht e kk m' hker
  have hlegL : ((algebraMap B L).comp (x.ψ : WittVector r k →+* B)).comp (frPow Fr ((m' : ℤ) - 2 * kk)) =
      (algebraMap B L).comp (x'.ψ : WittVector r k →+* B) := by
    rw [hleg]; exact comp_frobTwist Fr x.ψ _ _
  refine ⟨t, t', ht, (isAdmissible_congr ι hlegL t').1 ht', hηt, ?_, hrel⟩
  have hloc := hLoc L ((algebraMap B L).comp (x.ψ : WittVector r k →+* B)) hL e kk m' hker (gzero kk g) hg₀ t t' ht ht' hrel
  rw [isPullback_iff_eq_pullback] at hloc
  apply (hbij L ((algebraMap B L).comp (x'.ψ : WittVector r k →+* B)) hL).1
  calc θ L ((algebraMap B L).comp (x'.ψ : WittVector r k →+* B)) hL
          (η L ((algebraMap B L).comp (x'.ψ : WittVector r k →+* B)) hL t')
        = θ L (((algebraMap B L).comp (x.ψ : WittVector r k →+* B)).comp (frPow Fr ((m' : ℤ) - 2 * kk))) hL
            (η L (((algebraMap B L).comp (x.ψ : WittVector r k →+* B)).comp (frPow Fr ((m' : ℤ) - 2 * kk))) hL t') :=
          theta_eta_congr M θ η hlegL.symm hL t'
    _ = DeligneDatum.pullback ((r : ℕ) : ℤ_[r]) L (gzero kk g)
          (θ L ((algebraMap B L).comp (x.ψ : WittVector r k →+* B)) hL
            (η L ((algebraMap B L).comp (x.ψ : WittVector r k →+* B)) hL t)) := hloc
    _ = DeligneDatum.pullback ((r : ℕ) : ℤ_[r]) L (gzero kk g)
          (θ L ((algebraMap B L).comp (x.ψ : WittVector r k →+* B)) hL
            (M.map (ψ' := (algebraMap B L).comp (x.ψ : WittVector r k →+* B)) x.nilp hL (algebraMap B L) rfl x.pt)) := by
          rw [hηt]
    _ = DeligneDatum.pullback ((r : ℕ) : ℤ_[r]) L (gzero kk g)
          (DeligneDatum.map ((r : ℕ) : ℤ_[r]) (IsScalarTower.toAlgHom ℤ_[r] B L)
            (θ B (x.ψ : WittVector r k →+* B) x.nilp x.pt)) := by rw [theta_map M θ hnat _ x.nilp _ hL x.pt]
    _ = DeligneDatum.map ((r : ℕ) : ℤ_[r]) (IsScalarTower.toAlgHom ℤ_[r] B L)
          (DeligneDatum.pullback ((r : ℕ) : ℤ_[r]) B (gzero kk g) (θ B (x.ψ : WittVector r k →+* B) x.nilp x.pt)) :=
          (DeligneDatum.map_pullback _ _ _ _).symm
    _ = DeligneDatum.map ((r : ℕ) : ℤ_[r]) (IsScalarTower.toAlgHom ℤ_[r] B L)
          (θ B (x'.ψ : WittVector r k →+* B) x'.nilp x'.pt) := by rw [hpb']
    _ = θ L ((algebraMap B L).comp (x'.ψ : WittVector r k →+* B)) hL
          (M.map (ψ' := (algebraMap B L).comp (x'.ψ : WittVector r k →+* B)) x'.nilp hL (algebraMap B L) rfl x'.pt) :=
          (theta_map M θ hnat _ x'.nilp _ hL x'.pt).symm

theorem frobSeries_zero (L : Type) [CommRing L] : Rigidified.frobSeries (p := r) L 0 = Series.id L := by
  funext i
  simp only [Rigidified.frobSeries, pow_zero, pow_one, Series.id]

theorem frPow_natCast_sub_zero (hFr : ∀ x : WittVector r k, Fr x = WittVector.frobenius x) (m' : ℕ) :
    frPow Fr ((m' : ℤ) - 2 * (0 : ℕ)) = (WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m' := by
  have h : ((m' : ℤ) - 2 * (0 : ℕ)) = (m' : ℤ) := by simp
  rw [frPow, h, zpow_natCast]
  refine RingHom.ext fun x => ?_
  show (Fr ^ m') x = (WittVector.frobenius ^ m') x
  clear h
  induction m' generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, AlgEquiv.mul_apply, RingHom.coe_mul, Function.comp_apply, hFr, ih]

theorem isTranslate_zero_iff {L : Type} [CommRing L] (ε : Series (WittVector r k ⧸ pIdeal r (WittVector r k))) (m' : ℕ)
    (ψ : WittVector r k →+* L) (t t' : Rigidified r Φ L) :
    Rigidified.IsTranslate ε 0 m' ψ t t' ↔
      t'.X = t.X ∧
        ∃ c : ℕ,
          (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
              (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (L ⧸ pIdeal r L)) ^ (r ^ m')) =
            (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp (t.ρ.comp (Series.map (residueMap ψ) ε)) := by
  simp only [Rigidified.IsTranslate, Nat.add_zero, Nat.mul_zero, frobSeries_zero, Series.comp_id]
  exact Iff.rfl

theorem hLocFwd_zero (hFr : ∀ x : WittVector r k, Fr x = WittVector.frobenius x)
    (hGLeq : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B))
        (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ),
        FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) →
        ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]), (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e →
        ∀ (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ →
          t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) →
          t'.X = t.X →
          (∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ m')) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp
                  (t.ρ.comp (Series.map (residueMap ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries))) →
          DeligneDatum.IsPullback (K := ℚ_[r]) (π := (r : ℤ_[r])) B g (θ B ψ hB (η B ψ hB t))
            (θ B (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) hB
              (η B (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) hB t')))
    (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra ℤ_[r] L] (ψ : WittVector r k →+* L) (hL : IsNilpotent (r : L))
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ)
    (hker : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')))
    (g₀ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (hg₀ : (g₀ : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e)
    (t t' : Rigidified r Φ L) (ht : t.IsAdmissible ι ψ) (ht' : t'.IsAdmissible ι (ψ.comp (frPow Fr ((m' : ℤ) - 2 * (0 : ℕ)))))
    (hrel : Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries 0 m' ψ t t') :
    DeligneDatum.IsPullback (K := ℚ_[r]) (π := (r : ℤ_[r])) L g₀ (θ L ψ hL (η L ψ hL t))
      (θ L (ψ.comp (frPow Fr ((m' : ℤ) - 2 * (0 : ℕ)))) hL (η L (ψ.comp (frPow Fr ((m' : ℤ) - 2 * (0 : ℕ)))) hL t')) := by
  have hleg : ψ.comp (frPow Fr ((m' : ℤ) - 2 * (0 : ℕ))) =
      ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m') := by rw [frPow_natCast_sub_zero Fr hFr]
  obtain ⟨hX, hc⟩ := (isTranslate_zero_iff Φ _ m' ψ t t').1 hrel
  rw [theta_eta_congr M θ η hleg hL t']
  exact hGLeq L ψ hL e m' hker g₀ hg₀ t t' ht ((isAdmissible_congr ι hleg t').1 ht') hX hc

theorem hEx_zero (hFr : ∀ x : WittVector r k, Fr x = WittVector.frobenius x)
    (hGLdef : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
        ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ),
          FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) →
          ∃ t' : Rigidified r Φ B,
            t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) ∧
            t'.X = t.X ∧
            ∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ m')) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp
                  (t.ρ.comp (Series.map (residueMap ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries)))
    (L : Type) [CommRing L] [IsNoetherianRing L] (ψ : WittVector r k →+* L) (t : Rigidified r Φ L) (ht : t.IsAdmissible ι ψ)
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ)
    (hker : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m'))) :
    ∃ t' : Rigidified r Φ L, t'.IsAdmissible ι (ψ.comp (frPow Fr ((m' : ℤ) - 2 * (0 : ℕ)))) ∧
      Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries 0 m' ψ t t' := by
  have hleg : ψ.comp (frPow Fr ((m' : ℤ) - 2 * (0 : ℕ))) =
      ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m') := by rw [frPow_natCast_sub_zero Fr hFr]
  obtain ⟨t', ht', hX, hc⟩ := hGLdef L ψ t ht e m' hker
  exact ⟨t', (isAdmissible_congr ι hleg t').2 ht', (isTranslate_zero_iff Φ _ m' ψ t t').2 ⟨hX, hc⟩⟩

end GLclause

theorem assemble
    {r : ℕ} [Fact r.Prime] (k : Type) [Field k] [CharP k r] [IsAlgClosed k]
    [Algebra ℤ_[r] (WittVector r k)]
    (Fr : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k) (hFr : ∀ x : WittVector r k, Fr x = WittVector.frobenius x)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r] →* Multiplicative ℤ)
    (ι : Zp2 r →+* WittVector r k)
    (Φ : FormalODModule r (WittVector r k ⧸ pIdeal r (WittVector r k)))
    (M : ModuliPackage.{0, 0} r (WittVector r k)) (hM : M.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → M.obj B ψ hB)
    (hη₃ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m)
    (θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
        M.obj B ψ hB → OmegaObj (K := ℚ_[r]) (r : ℤ_[r]) B)
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r])
    (hbij : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
        Function.Bijective (θ B ψ hB))
    (hnat : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[r] B] [Algebra ℤ_[r] B']
        (ψ : WittVector r k →+* B) (ψ' : WittVector r k →+* B')
        (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →ₐ[ℤ_[r]] B')
        (hf : (f : B →+* B').comp ψ = ψ') (x : M.obj B ψ hB),
        DeligneDatum.IsBaseChange (K := ℚ_[r]) (π := (r : ℤ_[r])) f (θ B ψ hB x)
          (θ B' ψ' hB' (M.map hB hB' (f : B →+* B') hf x)))
    (hE : Function.Injective E ∧
        ∃ m : ℕ,
          (∀ A : Matrix (Fin 2) (Fin 2) ℤ_[r], ∃ e, E e = (r : ℚ_[r]) ^ m • A.map ((↑) : ℤ_[r] → ℚ_[r])) ∧
          (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[r], (r : ℚ_[r]) ^ m • E e = A.map ((↑) : ℤ_[r] → ℚ_[r])))
    (hPidef : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          ∃ t' : Rigidified r Φ B,
            t'.IsAdmissible ι (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) ∧
            t'.X.F = t.X.F ∧ t'.X.varpi = t.X.varpi ∧ (∀ a, t'.X.act a = t.X.act (WittVector.frobenius a)) ∧
            ∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ r) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ))))
    (hPieq : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B))
        (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ →
          t'.IsAdmissible ι (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) →
          t'.X.F = t.X.F → t'.X.varpi = t.X.varpi → (∀ a, t'.X.act a = t.X.act (WittVector.frobenius a)) →
          (∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ r) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ)))) →
          θ B (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) hB
              (η B (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) hB t') =
            θ B ψ hB (η B ψ hB t))

    (hGL : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B]
        (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r])))
        (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (x x' : (ModuliPackage.G ℤ_[r] M).obj B),
        ModuliPackage.G.IsActBy ι Φ η Fr E g x x' ↔
          OmegaNr.IsTwistedAct ((r : ℕ) : ℤ_[r]) (WittVector r k) Fr vdet B g
            (x.ψ, θ B (x.ψ : WittVector r k →+* B) x.nilp x.pt) (x'.ψ, θ B (x'.ψ : WittVector r k →+* B) x'.nilp x'.pt)) :
    ∃
      (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r])
      (_ : Function.Injective E₀ ∧
        ∃ m : ℕ,
          (∀ A : Matrix (Fin 2) (Fin 2) ℤ_[r], ∃ e, E₀ e = (r : ℚ_[r]) ^ m • A.map (algebraMap ℤ_[r] ℚ_[r])) ∧
          (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[r], (r : ℚ_[r]) ^ m • E₀ e = A.map (algebraMap ℤ_[r] ℚ_[r])))
      (e : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B], IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r])) → (ModuliPackage.G ℤ_[r] M).obj B → (AlgFunctor.prod (AlgFunctor.corep (WittVector r k)) (Omega ℚ_[r] ((r : ℕ) : ℤ_[r]))).obj B),

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra ℤ_[r] B'] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))) (hB' : IsNilpotent (algebraMap ℤ_[r] B' ((r : ℕ) : ℤ_[r])))
          (φ : B →ₐ[ℤ_[r]] B') (x : (ModuliPackage.G ℤ_[r] M).obj B), e B' hB' ((ModuliPackage.G ℤ_[r] M).map φ x) = (AlgFunctor.prod (AlgFunctor.corep (WittVector r k)) (Omega ℚ_[r] ((r : ℕ) : ℤ_[r]))).map φ (e B hB x)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))), Function.Bijective (e B hB)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))) (x : (ModuliPackage.G ℤ_[r] M).obj B), (e B hB x).1 = x.ψ) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))) (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (x x' : (ModuliPackage.G ℤ_[r] M).obj B),
          ModuliPackage.G.IsActBy ι Φ η Fr E₀ g x x' ↔ OmegaNr.IsTwistedAct ((r : ℕ) : ℤ_[r]) (WittVector r k) Fr vdet B g (e B hB x) (e B hB x')) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))) (x x' : (ModuliPackage.G ℤ_[r] M).obj B),
          ModuliPackage.G.IsPiTranslate ι Φ η Fr x x' → e B hB x' = (frobTwist (WittVector r k) Fr 1 (e B hB x).1, (e B hB x).2)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (x : (ModuliPackage.G ℤ_[r] M).obj B), ∃ x' : (ModuliPackage.G ℤ_[r] M).obj B, ModuliPackage.G.IsPiTranslate ι Φ η Fr x x') := by
  refine ⟨E, hE, fun B _ _ _ _ x => eG M θ B x, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro B _ _ _ B' _ _ _ hB hB' φ x
    exact eG_nat M θ hnat B B' φ x
  · intro B _ _ _ hB
    exact eG_bijective M θ hbij B hB
  · intro B _ _ _ hB x
    rfl
  · intro B _ _ _ hB g x x'
    exact hGL B hB g x x'
  · intro B _ _ _ hB x x' hx
    exact eG_Pi θ Fr hFr ι Φ hM η hbij hnat hPieq B x x' hx
  · intro B _ _ _ x
    exact G_piTotal θ Fr hFr ι Φ η hbij hnat hη₃ hPidef hPieq B x

theorem assemble_of_perLeg
    {r : ℕ} [Fact r.Prime] (k : Type) [Field k] [CharP k r] [IsAlgClosed k]
    [Algebra ℤ_[r] (WittVector r k)]
    (Fr : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k) (hFr : ∀ x : WittVector r k, Fr x = WittVector.frobenius x)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r] →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : ℤ_[r]ˣ, (Matrix.GeneralLinearGroup.det g : ℚ_[r]) = algebraMap ℤ_[r] ℚ_[r] (u : ℤ_[r]) * (algebraMap ℤ_[r] ℚ_[r] ((r : ℕ) : ℤ_[r])) ^ n)
    (ι : Zp2 r →+* WittVector r k)
    (Φ : FormalODModule r (WittVector r k ⧸ pIdeal r (WittVector r k)))
    (M : ModuliPackage.{0, 0} r (WittVector r k)) (hM : M.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → M.obj B ψ hB)
    (hη₃ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m)
    (θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
        M.obj B ψ hB → OmegaObj (K := ℚ_[r]) (r : ℤ_[r]) B)
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r])
    (hbij : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
        Function.Bijective (θ B ψ hB))
    (hnat : ∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[r] B] [Algebra ℤ_[r] B']
        (ψ : WittVector r k →+* B) (ψ' : WittVector r k →+* B')
        (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →ₐ[ℤ_[r]] B')
        (hf : (f : B →+* B').comp ψ = ψ') (x : M.obj B ψ hB),
        DeligneDatum.IsBaseChange (K := ℚ_[r]) (π := (r : ℤ_[r])) f (θ B ψ hB x)
          (θ B' ψ' hB' (M.map hB hB' (f : B →+* B') hf x)))
    (hE : Function.Injective E ∧
        ∃ m : ℕ,
          (∀ A : Matrix (Fin 2) (Fin 2) ℤ_[r], ∃ e, E e = (r : ℚ_[r]) ^ m • A.map ((↑) : ℤ_[r] → ℚ_[r])) ∧
          (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[r], (r : ℚ_[r]) ^ m • E e = A.map ((↑) : ℤ_[r] → ℚ_[r])))
    (hPidef : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          ∃ t' : Rigidified r Φ B,
            t'.IsAdmissible ι (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) ∧
            t'.X.F = t.X.F ∧ t'.X.varpi = t.X.varpi ∧ (∀ a, t'.X.act a = t.X.act (WittVector.frobenius a)) ∧
            ∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ r) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ))))
    (hPieq : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B))
        (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ →
          t'.IsAdmissible ι (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) →
          t'.X.F = t.X.F → t'.X.varpi = t.X.varpi → (∀ a, t'.X.act a = t.X.act (WittVector.frobenius a)) →
          (∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ r) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ)))) →
          θ B (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) hB
              (η B (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) hB t') =
            θ B ψ hB (η B ψ hB t))
    (hGLdef : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
        ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ),
          FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) →
          ∃ t' : Rigidified r Φ B,
            t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) ∧
            t'.X = t.X ∧
            ∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ m')) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp
                  (t.ρ.comp (Series.map (residueMap ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries)))
    (hGLeq : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B))
        (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ),
        FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) →
        ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]), (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e →
        ∀ (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ →
          t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) →
          t'.X = t.X →
          (∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ m')) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp
                  (t.ρ.comp (Series.map (residueMap ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries))) →
          DeligneDatum.IsPullback (K := ℚ_[r]) (π := (r : ℤ_[r])) B g (θ B ψ hB (η B ψ hB t))
            (θ B (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) hB
              (η B (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) hB t')))

    (hDet : HDet Φ E) (hIso : HIso Φ E) (hLoc : HLocFwd Fr ι Φ M θ η E) (hEx : HEx Fr ι Φ) :
    ∃
      (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r])
      (_ : Function.Injective E₀ ∧
        ∃ m : ℕ,
          (∀ A : Matrix (Fin 2) (Fin 2) ℤ_[r], ∃ e, E₀ e = (r : ℚ_[r]) ^ m • A.map (algebraMap ℤ_[r] ℚ_[r])) ∧
          (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[r], (r : ℚ_[r]) ^ m • E₀ e = A.map (algebraMap ℤ_[r] ℚ_[r])))
      (e : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B], IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r])) → (ModuliPackage.G ℤ_[r] M).obj B → (AlgFunctor.prod (AlgFunctor.corep (WittVector r k)) (Omega ℚ_[r] ((r : ℕ) : ℤ_[r]))).obj B),

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra ℤ_[r] B'] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))) (hB' : IsNilpotent (algebraMap ℤ_[r] B' ((r : ℕ) : ℤ_[r])))
          (φ : B →ₐ[ℤ_[r]] B') (x : (ModuliPackage.G ℤ_[r] M).obj B), e B' hB' ((ModuliPackage.G ℤ_[r] M).map φ x) = (AlgFunctor.prod (AlgFunctor.corep (WittVector r k)) (Omega ℚ_[r] ((r : ℕ) : ℤ_[r]))).map φ (e B hB x)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))), Function.Bijective (e B hB)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))) (x : (ModuliPackage.G ℤ_[r] M).obj B), (e B hB x).1 = x.ψ) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))) (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (x x' : (ModuliPackage.G ℤ_[r] M).obj B),
          ModuliPackage.G.IsActBy ι Φ η Fr E₀ g x x' ↔ OmegaNr.IsTwistedAct ((r : ℕ) : ℤ_[r]) (WittVector r k) Fr vdet B g (e B hB x) (e B hB x')) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))) (x x' : (ModuliPackage.G ℤ_[r] M).obj B),
          ModuliPackage.G.IsPiTranslate ι Φ η Fr x x' → e B hB x' = (frobTwist (WittVector r k) Fr 1 (e B hB x).1, (e B hB x).2)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (x : (ModuliPackage.G ℤ_[r] M).obj B), ∃ x' : (ModuliPackage.G ℤ_[r] M).obj B, ModuliPackage.G.IsPiTranslate ι Φ η Fr x x') := by
  obtain ⟨hEinj, m, hm, hm'⟩ := hE
  exact assemble k Fr hFr vdet ι Φ M hM η hη₃ θ E hbij hnat ⟨hEinj, m, hm, hm'⟩ hPidef hPieq
    (fun B _ _ _ hB g x x' =>
      ⟨GL_fwd Fr ι Φ θ η E vdet hvdet hM hbij hnat hDet hLoc B g x x',
       GL_bwd Fr ι Φ θ η E vdet hvdet hbij hnat hη₃ m hm hDet hIso hLoc hEx B g x x'⟩)

example
    {r : ℕ} [Fact r.Prime] (k : Type) [Field k] [CharP k r] [IsAlgClosed k]
    [Algebra ℤ_[r] (WittVector r k)]
    (Fr : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k) (hFr : ∀ x : WittVector r k, Fr x = WittVector.frobenius x)
    (ι : Zp2 r →+* WittVector r k)
    (Φ : FormalODModule r (WittVector r k ⧸ pIdeal r (WittVector r k)))
    (M : ModuliPackage.{0, 0} r (WittVector r k))
    (η : ∀ (B : Type) [CommRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → M.obj B ψ hB)
    (θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
        M.obj B ψ hB → OmegaObj (K := ℚ_[r]) (r : ℤ_[r]) B)
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r])
    (hGLdef : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
        ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ),
          FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) →
          ∃ t' : Rigidified r Φ B,
            t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) ∧
            t'.X = t.X ∧
            ∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ m')) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp
                  (t.ρ.comp (Series.map (residueMap ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries)))
    (hGLeq : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B))
        (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ),
        FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) →
        ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]), (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e →
        ∀ (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ →
          t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) →
          t'.X = t.X →
          (∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ m')) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp
                  (t.ρ.comp (Series.map (residueMap ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries))) →
          DeligneDatum.IsPullback (K := ℚ_[r]) (π := (r : ℤ_[r])) B g (θ B ψ hB (η B ψ hB t))
            (θ B (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) hB
              (η B (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) hB t'))) :
    (∀ (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra ℤ_[r] L] (ψ : WittVector r k →+* L) (hL : IsNilpotent (r : L))
      (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ),
      FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) →
      ∀ (g₀ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]), (g₀ : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e →
      ∀ (t t' : Rigidified r Φ L), t.IsAdmissible ι ψ → t'.IsAdmissible ι (ψ.comp (frPow Fr ((m' : ℤ) - 2 * (0 : ℕ)))) →
        Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries 0 m' ψ t t' →
        DeligneDatum.IsPullback (K := ℚ_[r]) (π := (r : ℤ_[r])) L g₀ (θ L ψ hL (η L ψ hL t))
          (θ L (ψ.comp (frPow Fr ((m' : ℤ) - 2 * (0 : ℕ)))) hL (η L (ψ.comp (frPow Fr ((m' : ℤ) - 2 * (0 : ℕ)))) hL t'))) ∧
    (∀ (L : Type) [CommRing L] [IsNoetherianRing L] (ψ : WittVector r k →+* L) (t : Rigidified r Φ L), t.IsAdmissible ι ψ →
      ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ),
      FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) →
      ∃ t' : Rigidified r Φ L, t'.IsAdmissible ι (ψ.comp (frPow Fr ((m' : ℤ) - 2 * (0 : ℕ)))) ∧
        Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries 0 m' ψ t t') :=
  ⟨fun L _ _ _ ψ hL e m' hker g₀ hg₀ t t' ht ht' hrel =>
      hLocFwd_zero Fr ι Φ θ η E hFr hGLeq L ψ hL e m' hker g₀ hg₀ t t' ht ht' hrel,
   fun L _ _ ψ t ht e m' hker => hEx_zero Fr ι Φ hFr hGLdef L ψ t ht e m' hker⟩

end R4F4aEd2
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_wittVector_of_exists_forall_bijective_of_isNoetherianRing.R4F4aEd2"

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega in

theorem solution
    {r : ℕ} [Fact r.Prime] (k : Type) [Field k] [CharP k r] [IsAlgClosed k]

    [Algebra ℤ_[r] (WittVector r k)]
    (Fr : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k) (hFr : ∀ x : WittVector r k, Fr x = WittVector.frobenius x)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r] →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : ℤ_[r]ˣ, (Matrix.GeneralLinearGroup.det g : ℚ_[r]) = algebraMap ℤ_[r] ℚ_[r] (u : ℤ_[r]) * (algebraMap ℤ_[r] ℚ_[r] ((r : ℕ) : ℤ_[r])) ^ n)

    (ι : Zp2 r →+* WittVector r k)
    (Φ : FormalODModule r (WittVector r k ⧸ pIdeal r (WittVector r k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r (WittVector r k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (M : ModuliPackage.{0, 0} r (WittVector r k)) (hM : M.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → M.obj B ψ hB)
    (hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B))
          (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
          (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : WittVector r k →+* B) (ψ' : WittVector r k →+* B')
          (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
          (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))

    (hmaster :
    ∃ (θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
        M.obj B ψ hB → OmegaObj (K := ℚ_[r]) (r : ℤ_[r]) B)
      (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r]),

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
        Function.Bijective (θ B ψ hB)) ∧

      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[r] B] [Algebra ℤ_[r] B']
        (ψ : WittVector r k →+* B) (ψ' : WittVector r k →+* B')
        (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →ₐ[ℤ_[r]] B')
        (hf : (f : B →+* B').comp ψ = ψ') (x : M.obj B ψ hB),
        DeligneDatum.IsBaseChange (K := ℚ_[r]) (π := (r : ℤ_[r])) f (θ B ψ hB x)
          (θ B' ψ' hB' (M.map hB hB' (f : B →+* B') hf x))) ∧

      (Function.Injective E ∧
        ∃ m : ℕ,
          (∀ A : Matrix (Fin 2) (Fin 2) ℤ_[r], ∃ e, E e = (r : ℚ_[r]) ^ m • A.map ((↑) : ℤ_[r] → ℚ_[r])) ∧
          (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[r], (r : ℚ_[r]) ^ m • E e = A.map ((↑) : ℤ_[r] → ℚ_[r]))) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
        ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ),
          FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) →
          ∃ t' : Rigidified r Φ B,
            t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) ∧
            t'.X = t.X ∧
            ∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ m')) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp
                  (t.ρ.comp (Series.map (residueMap ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries))) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B))
        (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ),
        FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) →
        ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]), (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e →
        ∀ (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ →
          t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) →
          t'.X = t.X →
          (∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ m')) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp
                  (t.ρ.comp (Series.map (residueMap ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries))) →
          DeligneDatum.IsPullback (K := ℚ_[r]) (π := (r : ℤ_[r])) B g (θ B ψ hB (η B ψ hB t))
            (θ B (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) hB
              (η B (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) hB t'))) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          ∃ t' : Rigidified r Φ B,
            t'.IsAdmissible ι (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) ∧
            t'.X.F = t.X.F ∧ t'.X.varpi = t.X.varpi ∧ (∀ a, t'.X.act a = t.X.act (WittVector.frobenius a)) ∧
            ∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ r) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ)))) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B))
        (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ →
          t'.IsAdmissible ι (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) →
          t'.X.F = t.X.F → t'.X.varpi = t.X.varpi → (∀ a, t'.X.act a = t.X.act (WittVector.frobenius a)) →
          (∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ r) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ)))) →
          θ B (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) hB
              (η B (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) hB t') =
            θ B ψ hB (η B ψ hB t)))
    :
    ∃
      (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r])
      (_ : Function.Injective E₀ ∧
        ∃ m : ℕ,
          (∀ A : Matrix (Fin 2) (Fin 2) ℤ_[r], ∃ e, E₀ e = (r : ℚ_[r]) ^ m • A.map (algebraMap ℤ_[r] ℚ_[r])) ∧
          (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[r], (r : ℚ_[r]) ^ m • E₀ e = A.map (algebraMap ℤ_[r] ℚ_[r])))
      (e : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B], IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r])) → (ModuliPackage.G ℤ_[r] M).obj B → (AlgFunctor.prod (AlgFunctor.corep (WittVector r k)) (Omega ℚ_[r] ((r : ℕ) : ℤ_[r]))).obj B),

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra ℤ_[r] B'] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))) (hB' : IsNilpotent (algebraMap ℤ_[r] B' ((r : ℕ) : ℤ_[r])))
          (φ : B →ₐ[ℤ_[r]] B') (x : (ModuliPackage.G ℤ_[r] M).obj B), e B' hB' ((ModuliPackage.G ℤ_[r] M).map φ x) = (AlgFunctor.prod (AlgFunctor.corep (WittVector r k)) (Omega ℚ_[r] ((r : ℕ) : ℤ_[r]))).map φ (e B hB x)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))), Function.Bijective (e B hB)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))) (x : (ModuliPackage.G ℤ_[r] M).obj B), (e B hB x).1 = x.ψ) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))) (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (x x' : (ModuliPackage.G ℤ_[r] M).obj B),
          ModuliPackage.G.IsActBy ι Φ η Fr E₀ g x x' ↔ OmegaNr.IsTwistedAct ((r : ℕ) : ℤ_[r]) (WittVector r k) Fr vdet B g (e B hB x) (e B hB x')) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))) (x x' : (ModuliPackage.G ℤ_[r] M).obj B),
          ModuliPackage.G.IsPiTranslate ι Φ η Fr x x' → e B hB x' = (frobTwist (WittVector r k) Fr 1 (e B hB x).1, (e B hB x).2)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (x : (ModuliPackage.G ℤ_[r] M).obj B), ∃ x' : (ModuliPackage.G ℤ_[r] M).obj B, ModuliPackage.G.IsPiTranslate ι Φ η Fr x x') := by
  obtain ⟨θ, E, hbij, hnat, hE, hGLdef, hGLeq, hPidef, hPieq⟩ := hmaster
  exact R4F4aEd2.assemble_of_perLeg k Fr hFr vdet hvdet ι Φ M hM η hη.2.2 θ E hbij hnat hE hPidef hPieq hGLdef hGLeq

    (fun e m' he =>
      CerednikDrinfeld.SpecialFormal.exists_det_eq_mul_pow_of_hasKernelOfDegree k ι Φ hΦ hΦ4 E hE e m' he)

    (fun e g hg =>
      CerednikDrinfeld.SpecialFormal.exists_hasKernelOfDegree_of_generalLinearGroup_coe_eq k ι Φ hΦ hΦ4 E hE e g hg)

    (fun L _ _ _ ψ hL e kk m' he g₀ hg₀ t t' ht ht' htt' =>
      CerednikDrinfeld.SpecialFormal.Rigidified.isPullback_of_isTranslate_of_isTranslate_zero k Fr hFr ι Φ hΦ4 M η
        hη.1 θ E hGLdef hGLeq L ψ hL e kk m' he g₀ hg₀ t t' ht ht' htt')

    (fun L _ _ ψ t ht e kk m' he =>
      CerednikDrinfeld.SpecialFormal.Rigidified.exists_isAdmissible_and_isTranslate_of_isTranslate_zero k Fr hFr ι Φ
        hGLdef L ψ t ht e kk m' he)

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_wittVector_of_exists_forall_bijective_of_isNoetherianRing.R4F4aEd2"

end S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_wittVector_of_exists_forall_bijective_of_isNoetherianRing
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_wittVector_of_exists_forall_bijective_of_isNoetherianRing (solution)
