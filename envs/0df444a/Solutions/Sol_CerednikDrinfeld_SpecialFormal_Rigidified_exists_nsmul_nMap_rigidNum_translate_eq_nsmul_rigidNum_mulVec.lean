-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_nMap_rigidNum_translate_eq_nsmul_rigidNum_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/e8342a41-2516-5507-a3c0-42976dd8e43a

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_PeriodMap
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_nMap_rigidNum_translate_eq_nsmul_rigidNum_mulVec

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace RhoMatch
open CerednikDrinfeld MvFormalGroup
variable {p : ℕ} [Fact p.Prime]
theorem nsmul_nMk {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j)
    (n : ℕ) (x y : D.M) : n • D.nMk (x, y) = D.nMk (n • x, n • y) := by
  rw [← map_nsmul]; rfl
end RhoMatch

namespace G4L
open MvPowerSeries MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [CommRing C]

noncomputable abbrev frobS (C : Type) [CommRing C] (q : ℕ) : Series C :=
  fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) C) ^ q

omit hp in
theorem constantCoeff_frobS {q : ℕ} (hq : q ≠ 0) (i : Fin 2) : constantCoeff (frobS C q i) = 0 := by
  rw [map_pow, MvPowerSeries.constantCoeff_X, zero_pow hq]

omit hp in
theorem subst_X_pow_eq_expand {σ : Type*} {q : ℕ} (hq : q ≠ 0) (g : MvPowerSeries σ C) :
    subst (fun s : σ => (MvPowerSeries.X s : MvPowerSeries σ C) ^ q) g = MvPowerSeries.expand q hq g := by
  rw [MvPowerSeries.expand, MvPowerSeries.substAlgHom_apply]

theorem subst_X_pow_map_iterateFrobenius [CharP C p] {σ : Type*} (m : ℕ) (g : MvPowerSeries σ C) :
    subst (fun s : σ => (MvPowerSeries.X s : MvPowerSeries σ C) ^ (p ^ m))
      (MvPowerSeries.map (iterateFrobenius C p m) g) = g ^ (p ^ m) := by
  haveI : ExpChar C p := ExpChar.prime hp.out
  rw [subst_X_pow_eq_expand (pow_ne_zero m hp.out.ne_zero), ← MvPowerSeries.map_expand,
    MvPowerSeries.map_iterateFrobenius_expand p hp.out.ne_zero]

theorem isLawHom_frobS [CharP C p] (F : MvFormalGroup 2 C) (m : ℕ) :
    IsLawHom F (F.map (iterateFrobenius C p m)) (frobS C (p ^ m)) := by
  refine ⟨constantCoeff_frobS (pow_ne_zero m hp.out.ne_zero), fun i => ?_⟩
  have hF : HasSubst F.toPowerSeries := F.hasSubst_toPowerSeries
  have hXL : HasSubst (fun l : Fin 2 => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) C)) :=
    hasSubst_of_constantCoeff_zero fun l => MvPowerSeries.constantCoeff_X _
  have hXR : HasSubst (fun l : Fin 2 => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) C)) :=
    hasSubst_of_constantCoeff_zero fun l => MvPowerSeries.constantCoeff_X _
  rw [MvPowerSeries.subst_pow hF, MvPowerSeries.subst_X hF]
  have hE : (Sum.elim (fun j => subst (fun l : Fin 2 => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) C))
        (frobS C (p ^ m) j))
      (fun j => subst (fun l : Fin 2 => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) C))
        (frobS C (p ^ m) j))) =
      fun s : Fin 2 ⊕ Fin 2 => (MvPowerSeries.X s : MvPowerSeries (Fin 2 ⊕ Fin 2) C) ^ (p ^ m) := by
    funext s
    rcases s with j | j
    · show subst _ ((MvPowerSeries.X j : MvPowerSeries (Fin 2) C) ^ (p ^ m)) = _
      rw [MvPowerSeries.subst_pow hXL, MvPowerSeries.subst_X hXL]
    · show subst _ ((MvPowerSeries.X j : MvPowerSeries (Fin 2) C) ^ (p ^ m)) = _
      rw [MvPowerSeries.subst_pow hXR, MvPowerSeries.subst_X hXR]
  rw [hE]
  exact (subst_X_pow_map_iterateFrobenius m (F.toPowerSeries i)).symm

omit hp in
theorem expand_congr {σ : Type*} {a b : ℕ} (h : a = b) (ha : a ≠ 0) (hb : b ≠ 0) (f : MvPowerSeries σ C) :
    MvPowerSeries.expand a ha f = MvPowerSeries.expand b hb f := by
  subst h; rfl

theorem toPowerSeries_verschiebungInt_iterate_eq_expand [CharP C p] {F : MvFormalGroup 2 C} [F.IsComm]
    (f : CartierModule p F) (m : ℕ) (j : Fin 2) :
    ((⇑(verschiebungInt (p := p) (Φ := F)))^[m] f).toPowerSeries j =
      MvPowerSeries.expand (p ^ m) (pow_ne_zero m hp.out.ne_zero) (f.toPowerSeries j) := by
  rw [toPowerSeries_verschiebungInt_iterate, WittLaw.frobPolyFam_eq_frobFam]
  induction m with
  | zero =>
    rw [Function.iterate_zero, id, expand_congr (pow_zero p) _ one_ne_zero, MvPowerSeries.expand_one_apply]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    show subst (fun n : ℕ => (MvPowerSeries.X n : MvPowerSeries ℕ C) ^ p) _ = _
    rw [subst_X_pow_eq_expand hp.out.ne_zero,
      expand_congr (pow_succ' p m) _ (Nat.mul_ne_zero hp.out.ne_zero (pow_ne_zero m hp.out.ne_zero)),
      MvPowerSeries.expand_mul p hp.out.ne_zero (p ^ m) (pow_ne_zero m hp.out.ne_zero)]

theorem map_frobHom [CharP C p] {F Ψ : MvFormalGroup 2 C} [F.IsComm] [Ψ.IsComm] (m : ℕ)
    (hΨ : F.map (iterateFrobenius C p m) = Ψ) (h : IsLawHom F Ψ (frobS C (p ^ m))) (x : CartierModule p F) :
    CartierModule.map h.toHom x =
      (⇑(verschiebungInt (p := p) (Φ := Ψ)))^[m] (baseChangeEq (iterateFrobenius C p m) hΨ x) := by
  apply CartierModule.ext
  funext i
  rw [toPowerSeries_map, toPowerSeries_verschiebungInt_iterate_eq_expand, toPowerSeries_baseChangeEq,
    ← MvPowerSeries.map_expand]
  haveI : ExpChar C p := ExpChar.prime hp.out
  rw [MvPowerSeries.map_iterateFrobenius_expand p hp.out.ne_zero]
  show subst x.toPowerSeries ((MvPowerSeries.X i : MvPowerSeries (Fin 2) C) ^ (p ^ m)) = _
  rw [MvPowerSeries.subst_pow x.hasSubst_toPowerSeries, MvPowerSeries.subst_X x.hasSubst_toPowerSeries]

end G4L

namespace G4R
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal MvFormalGroup MvFormalGroup.CartierModule

variable (p : ℕ) [hp : Fact p.Prime]
variable {k : Type} [Field k] [CharP k p] [PerfectRing k p] {B : Type} [CommRing B]

omit [PerfectRing k p] in
theorem constantCoeff_frobenius_pow (m : ℕ) (x : WittVector p k) :
    WittVector.constantCoeff (((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m) x) =
      (WittVector.constantCoeff x) ^ (p ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, pow_one, RingHom.one_def, RingHom.id_apply]
  | succ m ih =>
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply, pow_succ, pow_mul]
    show (WittVector.frobenius (((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m) x)).coeff 0 = _
    rw [WittVector.coeff_frobenius_charP, ← ih]
    rfl

theorem residueMap_comp_frobenius_pow (ψ : WittVector p k →+* B) (m : ℕ) :
    residueMap (p := p) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m)) =
      ((((residueMap (p := p) ψ).comp
          (WittVector.quotientPEquiv (p := p) (k := k)).symm.toRingHom).comp
          (iterateFrobenius k p m)).comp
        (WittVector.quotientPEquiv (p := p) (k := k)).toRingHom) := by
  apply Ideal.Quotient.ringHom_ext
  ext x
  have h1 : (WittVector.quotientPEquiv (p := p) (k := k))
      (Ideal.Quotient.mk (pIdeal p (WittVector p k)) x) = WittVector.constantCoeff x := rfl
  have h2 : (WittVector.quotientPEquiv (p := p) (k := k))
      (Ideal.Quotient.mk (pIdeal p (WittVector p k))
        (((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m) x)) =
        WittVector.constantCoeff (((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m) x) := rfl
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, h1,
    iterateFrobenius_def]
  rw [← constantCoeff_frobenius_pow, ← h2, RingEquiv.symm_apply_apply]
  rfl

theorem iterateFrobenius_comp_comp_residueMap {C : Type} [CommRing C] [CharP C p]
    (ψ : WittVector p k →+* B) (g : B ⧸ pIdeal p B →+* C) (m : ℕ) :
    (iterateFrobenius C p m).comp (g.comp (residueMap (p := p) ψ)) =
      g.comp (residueMap (p := p) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m))) := by
  rw [residueMap_comp_frobenius_pow]
  haveI : ExpChar k p := ExpChar.prime hp.out
  haveI : ExpChar C p := ExpChar.prime hp.out
  have key : (iterateFrobenius C p m).comp ((g.comp (residueMap (p := p) ψ)).comp
      (WittVector.quotientPEquiv (p := p) (k := k)).symm.toRingHom) =
      ((g.comp (residueMap (p := p) ψ)).comp (WittVector.quotientPEquiv (p := p) (k := k)).symm.toRingHom).comp
        (iterateFrobenius k p m) :=
    (RingHom.iterateFrobenius_comm _ p m).symm
  apply RingHom.ext
  intro x
  have hx : x = (WittVector.quotientPEquiv (p := p) (k := k)).symm.toRingHom
      ((WittVector.quotientPEquiv (p := p) (k := k)).toRingHom x) := by
    simp
  have := congrArg (fun φ => φ ((WittVector.quotientPEquiv (p := p) (k := k)).toRingHom x)) key
  simp only [RingHom.comp_apply] at this ⊢
  rw [hx]
  simpa using this

theorem map_actEnd_natCast_pow {C : Type} [CommRing C] (X : FormalODModule p C) (a : ℕ) (z : CartierModule p X.F) :
    CartierModule.map (X.actEnd ((p : Zp2 p) ^ a)) z = p ^ a • z := by
  have h : X.actEnd ((p : Zp2 p) ^ a) = ((p ^ a : ℕ) : MvFormalGroup.End X.F) := by
    rw [← FormalODModule.actRingHom_apply, map_pow, map_natCast, Nat.cast_pow]
  rw [← endAct_apply, h, endAct_natCast]

theorem map_verschiebungInt_iterate {C : Type} [CommRing C] {F G : MvFormalGroup 2 C} [F.IsComm] [G.IsComm]
    (φ : F.Hom G) (m : ℕ) (x : CartierModule p F) :
    CartierModule.map φ ((⇑(verschiebungInt (p := p) (Φ := F)))^[m] x) =
      (⇑(verschiebungInt (p := p) (Φ := G)))^[m] (CartierModule.map φ x) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_verschiebungInt, ih]

omit hp in
theorem frobSeries_map {C C' : Type} [CommRing C] [CommRing C'] (g : C →+* C') (j : ℕ) :
    (Rigidified.frobSeries (p := p) C j).map g = Rigidified.frobSeries (p := p) C' j := by
  funext i
  show MvPowerSeries.map g ((MvPowerSeries.X i : MvPowerSeries (Fin 2) C) ^ (p ^ j)) = _
  rw [map_pow, MvPowerSeries.map_X]
  rfl

omit hp in
theorem frobSeries_zero_comp {C : Type} [CommRing C] (φ : Series C) :
    φ.comp (Rigidified.frobSeries (p := p) C 0) = φ := by
  have : Rigidified.frobSeries (p := p) C 0 = Series.id C := by
    funext i
    show (MvPowerSeries.X i : MvPowerSeries (Fin 2) C) ^ (p ^ 0) = MvPowerSeries.X i
    rw [pow_zero, pow_one]
  rw [this, Series.comp_id]

end G4R
theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B]
    (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[p]) (m : ℕ)
    (hEinj : Function.Injective E)
    (hEord : ∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[p], (p : ℚ_[p]) ^ m • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]))
    (hEcompat : (∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (A : Matrix (Fin 2) (Fin 2) ℤ_[p]),
        (p : ℚ_[p]) ^ m • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]) →
        ∀ (Ne : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod),
          (∀ x : MvFormalGroup.CartierModule p Φ.F × (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).Sigma,
            Ne ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk x) =
              (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk
                (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) x.1,
                 (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).toSigma
                   (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F)
                     ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).ofSigma x.2)))) →
          ∀ w : Fin 2 → ℤ_[p], p ^ m • Ne (rΦ w) = rΦ (A.mulVec w)))
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ)
    (hker : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (p ^ (2 * m')))
    (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]) (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = E e)
    (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) (hA : (p : ℚ_[p]) ^ m • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) (n' : ℕ) (ρ' : Series (B ⧸ pIdeal p B))
    (ht' : ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')))
    (htr : Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries 0 m' ψ t ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B)) :
    ∃ c : ℕ, ∀ (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
      (hOD' : FormalODModule.IsODHom (({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B).Φbar (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m'))) t.Xbar ρ')
      {S : Type} [CommRing S] (f : B →+* S)
      (hcb : t.IsGradedSbar ι ψ f)
      (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ f) (hcΦf' : Rigidified.IsGradedPhiS (Φ := Φ) ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f)
      (NV : ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb).NMod →+ ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb).NMod)
      (hNV : ∀ x : MvFormalGroup.CartierModule p (t.XbarS f).F × MvFormalGroup.CartierModule p (t.XbarS f).F,
        NV (((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb).nMk x) = ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb).nMk ((MvFormalGroup.CartierModule.verschiebungInt)^[m'] x.1,
          (MvFormalGroup.CartierModule.verschiebungInt)^[m'] x.2))
      (w : Fin 2 → ℤ_[p]),
      p ^ (c + t.n + m) • NV (((Rigidified.PhibarS (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f).toGradedCartierModuleData (Rigidified.jPhiS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f) hcΦf').nMap ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb)
            (Rigidified.rhoC (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 f)
            (Rigidified.rhoC_verschiebungInt (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 f)
            (Rigidified.rhoC_endAct_varpiEnd (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD' f)
          ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f).toGradedCartierModuleData (Rigidified.jPhiS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f) hcΦf')
            (Rigidified.bcPhi (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f)
            (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f) (rΦ w))) =
        p ^ (c + n') • t.rigidNum ι hcΦ rΦ ψ hOD f hcb hcΦf (A.mulVec w) := by
  classical
  obtain ⟨_, c, hc⟩ := htr
  refine ⟨c, ?_⟩
  intro hOD hOD' S _ f hcb hcΦf hcΦf' NV hNV w

  have he_varpi : (e : MvFormalGroup.End Φ.F) * Φ.varpiEnd = Φ.varpiEnd * (e : MvFormalGroup.End Φ.F) := by
    have := Subring.mem_centralizer_iff.mp e.2 Φ.varpiEnd (Set.mem_union_right _ (Set.mem_singleton _))
    exact this.symm
  have hVe : ∀ x : MvFormalGroup.CartierModule p Φ.F,
      MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).verschiebung x) =
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).verschiebung (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) x) :=
    fun x => MvFormalGroup.CartierModule.endAct_verschiebungInt _ x
  have hPie : ∀ x : MvFormalGroup.CartierModule p Φ.F,
      MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).varpi x) =
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).varpi (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) x) := by
    intro x
    show MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) (MvFormalGroup.CartierModule.endAct Φ.varpiEnd x) =
      MvFormalGroup.CartierModule.endAct Φ.varpiEnd (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) x)
    simp only [MvFormalGroup.CartierModule.endAct_apply]
    rw [← MvFormalGroup.CartierModule.map_comp, ← MvFormalGroup.CartierModule.map_comp]
    exact congrArg (fun φ => MvFormalGroup.CartierModule.map φ x) he_varpi
  let Ne : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod :=
    (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ) (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F)) hVe hPie
  have hNe := hEcompat e A hA Ne (fun x => by
    obtain ⟨a, b⟩ := x
    rfl) w

  have star : ∀ a : MvFormalGroup.CartierModule p Φ.F,
      p ^ (c + t.n) • ((MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := (t.XbarS f).F))^[m']
        (Rigidified.rhoC (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 f (Rigidified.bcPhi (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f a))) =
      p ^ (c + n') • Rigidified.rhoC ψ t hOD.1 f
        (Rigidified.bcPhi (Φ := Φ) ψ f (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) a)) := by
    intro a
    rcases subsingleton_or_nontrivial (S ⧸ pIdeal p S) with hsub | hnon
    · haveI : Subsingleton (MvFormalGroup.CartierModule p (t.XbarS f).F) :=
        ⟨fun x y => MvFormalGroup.CartierModule.ext (funext fun i => MvPowerSeries.ext fun n => Subsingleton.elim _ _)⟩
      exact Subsingleton.elim _ _
    haveI : CharP (S ⧸ pIdeal p S) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
      rw [← map_natCast (Ideal.Quotient.mk (pIdeal p S))]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)))

    have hρ'0 : ∀ i, MvPowerSeries.constantCoeff (ρ' i) = 0 := hOD'.1.1
    have hρ0 : ∀ i, MvPowerSeries.constantCoeff (t.ρ i) = 0 := hOD.1.1
    have he0 : ∀ i, MvPowerSeries.constantCoeff ((Series.map (residueMap (p := p) ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries) i) = 0 :=
      ((IsLawHom.of_hom (e : MvFormalGroup.End Φ.F)).map (residueMap (p := p) ψ)).1
    have hFr0 : ∀ i, MvPowerSeries.constantCoeff (Rigidified.frobSeries (p := p) (B ⧸ pIdeal p B) m' i) = 0 :=
      G4L.constantCoeff_frobS (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    have hc1 : (t.Xbar.act ((p : Zp2 p) ^ (c + t.n))).comp (ρ'.comp (Rigidified.frobSeries (p := p) _ m')) =
        (t.Xbar.act ((p : Zp2 p) ^ (c + n'))).comp (t.ρ.comp (Series.map (residueMap (p := p) ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries)) := by
      have h := hc
      dsimp only at h
      rwa [add_zero, mul_zero, G4R.frobSeries_zero_comp] at h
    have hcS := congrArg (Series.map (reduceMap (p := p) f)) hc1
    rw [Series.map_comp _ _ _ (Series.constantCoeff_comp hρ'0 hFr0), Series.map_comp _ _ _ hFr0,
      Series.map_comp _ _ _ (Series.constantCoeff_comp hρ0 he0), Series.map_comp _ _ _ he0,
      G4R.frobSeries_map] at hcS

    have hF : (Rigidified.PhibarS (Φ := Φ) ψ f).F.map (iterateFrobenius (S ⧸ pIdeal p S) p m') = (Rigidified.PhibarS (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f).F := by
      show ((Φ.F.map (residueMap (p := p) ψ)).map (reduceMap (p := p) f)).map (iterateFrobenius (S ⧸ pIdeal p S) p m') =
        (Φ.F.map (residueMap (p := p) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')))).map (reduceMap (p := p) f)
      rw [MvFormalGroup.map_map_ringHom, MvFormalGroup.map_map_ringHom, MvFormalGroup.map_map_ringHom,
        RingHom.comp_assoc, G4R.iterateFrobenius_comp_comp_residueMap]
    have hFrob : IsLawHom (Rigidified.PhibarS (Φ := Φ) ψ f).F (Rigidified.PhibarS (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f).F (G4L.frobS (S ⧸ pIdeal p S) (p ^ m')) := hF ▸ G4L.isLawHom_frobS (Rigidified.PhibarS (Φ := Φ) ψ f).F m'
    have hρ'S : IsLawHom (Rigidified.PhibarS (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f).F (t.XbarS f).F (ρ'.map (reduceMap (p := p) f)) := hOD'.1.map (reduceMap (p := p) f)
    have hρS : IsLawHom (Rigidified.PhibarS (Φ := Φ) ψ f).F (t.XbarS f).F (t.ρ.map (reduceMap (p := p) f)) := hOD.1.map (reduceMap (p := p) f)
    have heS : IsLawHom (Rigidified.PhibarS (Φ := Φ) ψ f).F (Rigidified.PhibarS (Φ := Φ) ψ f).F ((Series.map (residueMap (p := p) ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries).map (reduceMap (p := p) f)) :=
      ((IsLawHom.of_hom (e : MvFormalGroup.End Φ.F)).map (residueMap (p := p) ψ)).map (reduceMap (p := p) f)
    have hLR : ((t.XbarS f).actEnd ((p : Zp2 p) ^ (c + t.n))).comp (hρ'S.toHom.comp hFrob.toHom) =
        ((t.XbarS f).actEnd ((p : Zp2 p) ^ (c + n'))).comp (hρS.toHom.comp heS.toHom) :=
      MvFormalGroup.Hom.ext hcS
    have key := congrArg (fun φ => MvFormalGroup.CartierModule.map φ (Rigidified.bcPhi (Φ := Φ) ψ f a)) hLR
    simp only [MvFormalGroup.CartierModule.map_comp, G4R.map_actEnd_natCast_pow] at key
    rw [G4L.map_frobHom m' hF hFrob, G4R.map_verschiebungInt_iterate] at key

    have E2 : MvFormalGroup.CartierModule.baseChangeEq (iterateFrobenius (S ⧸ pIdeal p S) p m') hF (Rigidified.bcPhi (Φ := Φ) ψ f a) =
        Rigidified.bcPhi (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f a := by
      apply MvFormalGroup.CartierModule.ext
      funext i
      show MvPowerSeries.map (iterateFrobenius (S ⧸ pIdeal p S) p m')
          (MvPowerSeries.map (reduceMap (p := p) f) (MvPowerSeries.map (residueMap (p := p) ψ) (a.toPowerSeries i))) =
        MvPowerSeries.map (reduceMap (p := p) f) (MvPowerSeries.map (residueMap (p := p) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m'))) (a.toPowerSeries i))
      rw [MvPowerSeries.map_map, MvPowerSeries.map_map, MvPowerSeries.map_map,
        RingHom.comp_assoc, G4R.iterateFrobenius_comp_comp_residueMap]
    have E3 : MvFormalGroup.CartierModule.map heS.toHom (Rigidified.bcPhi (Φ := Φ) ψ f a) =
        Rigidified.bcPhi (Φ := Φ) ψ f (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) a) := by
      rw [MvFormalGroup.CartierModule.endAct_apply]
      apply MvFormalGroup.CartierModule.ext
      funext i
      show MvPowerSeries.subst (fun l => MvPowerSeries.map (reduceMap (p := p) f) (MvPowerSeries.map (residueMap (p := p) ψ) (a.toPowerSeries l)))
          (MvPowerSeries.map (reduceMap (p := p) f) (MvPowerSeries.map (residueMap (p := p) ψ) ((e : MvFormalGroup.End Φ.F).toPowerSeries i))) =
        MvPowerSeries.map (reduceMap (p := p) f) (MvPowerSeries.map (residueMap (p := p) ψ)
          (MvPowerSeries.subst a.toPowerSeries ((e : MvFormalGroup.End Φ.F).toPowerSeries i)))
      rw [MvPowerSeries.map_subst a.hasSubst_toPowerSeries,
        MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero
          (MvFormalGroup.WittLaw.constantCoeff_map_family a.constantCoeff_eq_zero (residueMap (p := p) ψ)))]
    rw [E2, E3] at key
    exact key

  have key : ∀ z : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod,
      p ^ (c + t.n) • NV (((Rigidified.PhibarS (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f).toGradedCartierModuleData (Rigidified.jPhiS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f) hcΦf').nMap ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb)
            (Rigidified.rhoC (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 f)
            (Rigidified.rhoC_verschiebungInt (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 f)
            (Rigidified.rhoC_endAct_varpiEnd (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD' f)
          ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f).toGradedCartierModuleData (Rigidified.jPhiS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f) hcΦf')
            (Rigidified.bcPhi (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f)
            (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f) z)) =
      p ^ (c + n') • ((Rigidified.PhibarS (Φ := Φ) ψ f).toGradedCartierModuleData (Rigidified.jPhiS ι ψ f) hcΦf).nMap ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb) (Rigidified.rhoC ψ t hOD.1 f) (Rigidified.rhoC_verschiebungInt ψ t hOD.1 f)
          (Rigidified.rhoC_endAct_varpiEnd ψ t hOD f)
        ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) ψ f).toGradedCartierModuleData (Rigidified.jPhiS ι ψ f) hcΦf) (Rigidified.bcPhi (Φ := Φ) ψ f) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ f)
          (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ f) (Ne z)) := by
    intro z
    obtain ⟨⟨a, b⟩, rfl⟩ := (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk_surjective z
    have e1 : Ne ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (a, b)) =
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) a,
          MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) b) := rfl
    rw [e1]
    have eL : ((Rigidified.PhibarS (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f).toGradedCartierModuleData (Rigidified.jPhiS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f) hcΦf').nMap ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb)
            (Rigidified.rhoC (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 f)
            (Rigidified.rhoC_verschiebungInt (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 f)
            (Rigidified.rhoC_endAct_varpiEnd (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD' f)
          ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f).toGradedCartierModuleData (Rigidified.jPhiS ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f) hcΦf')
            (Rigidified.bcPhi (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f)
            (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f) ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (a, b))) =
        ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb).nMk (Rigidified.rhoC (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 f (Rigidified.bcPhi (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f a),
          Rigidified.rhoC (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 f (Rigidified.bcPhi (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f b)) := rfl
    have eR : ((Rigidified.PhibarS (Φ := Φ) ψ f).toGradedCartierModuleData (Rigidified.jPhiS ι ψ f) hcΦf).nMap ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb) (Rigidified.rhoC ψ t hOD.1 f) (Rigidified.rhoC_verschiebungInt ψ t hOD.1 f)
          (Rigidified.rhoC_endAct_varpiEnd ψ t hOD f)
        ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) ψ f).toGradedCartierModuleData (Rigidified.jPhiS ι ψ f) hcΦf) (Rigidified.bcPhi (Φ := Φ) ψ f) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ f)
          (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ f)
          ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) a,
            MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) b))) =
        ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb).nMk (Rigidified.rhoC ψ t hOD.1 f (Rigidified.bcPhi (Φ := Φ) ψ f (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) a)),
          Rigidified.rhoC ψ t hOD.1 f (Rigidified.bcPhi (Φ := Φ) ψ f (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) b))) := rfl
    have hL : NV (((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb).nMk ((Rigidified.rhoC (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 f (Rigidified.bcPhi (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f a)), (Rigidified.rhoC (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 f (Rigidified.bcPhi (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f b)))) =
        ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb).nMk ((MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := (t.XbarS f).F))^[m'] (Rigidified.rhoC (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 f (Rigidified.bcPhi (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f a)),
          (MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := (t.XbarS f).F))^[m'] (Rigidified.rhoC (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 f (Rigidified.bcPhi (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f b))) :=
      hNV ((Rigidified.rhoC (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 f (Rigidified.bcPhi (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f a)), (Rigidified.rhoC (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) ({ X := t.X, n := n', ρ := ρ' } : Rigidified p Φ B) hOD'.1 f (Rigidified.bcPhi (Φ := Φ) (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) f b)))
    rw [eL, eR, hL, RhoMatch.nsmul_nMk, RhoMatch.nsmul_nMk]
    congr 1
    exact Prod.ext (star a) (star b)

  have hrig : ∀ w', t.rigidNum ι hcΦ rΦ ψ hOD f hcb hcΦf w' =
      ((Rigidified.PhibarS (Φ := Φ) ψ f).toGradedCartierModuleData (Rigidified.jPhiS ι ψ f) hcΦf).nMap ((t.XbarS f).toGradedCartierModuleData (Rigidified.jSbar ι ψ f) hcb) (Rigidified.rhoC ψ t hOD.1 f) (Rigidified.rhoC_verschiebungInt ψ t hOD.1 f)
          (Rigidified.rhoC_endAct_varpiEnd ψ t hOD f)
        ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) ψ f).toGradedCartierModuleData (Rigidified.jPhiS ι ψ f) hcΦf) (Rigidified.bcPhi (Φ := Φ) ψ f) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ f)
          (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ f) (rΦ w')) := fun _ => rfl
  rw [hrig, ← hNe, map_nsmul, map_nsmul, smul_comm (p ^ (c + n')) (p ^ m), ← key (rΦ w), ← mul_smul, ← pow_add]
  congr 1
  ring

end S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_nMap_rigidNum_translate_eq_nsmul_rigidNum_mulVec
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_nMap_rigidNum_translate_eq_nsmul_rigidNum_mulVec (solution)
