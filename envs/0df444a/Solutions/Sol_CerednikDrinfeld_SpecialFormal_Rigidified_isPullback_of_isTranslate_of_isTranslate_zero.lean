-- Prove2me | solution 1 for CerednikDrinfeld.SpecialFormal.Rigidified.isPullback_of_isTranslate_of_isTranslate_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/07d3d3ce-b64e-5a05-8b17-8ca8e7943859

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isPullback_of_isTranslate_of_isTranslate_zero

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace R4TranslatePullback

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega
open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff coeff subst_X coe_substAlgHom)

universe u

section SeriesAlgebra

variable {A : Type u} [CommRing A]

def powPair (A : Type u) [CommRing A] (q : ℕ) : Series A :=
  fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) A) ^ q

theorem constantCoeff_powPair {q : ℕ} (hq : q ≠ 0) (i : Fin 2) : constantCoeff (powPair A q i) = 0 := by
  rw [powPair, map_pow, MvPowerSeries.constantCoeff_X, zero_pow hq]

theorem hasSubst_powPair {q : ℕ} (hq : q ≠ 0) : HasSubst (powPair A q) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_powPair hq)

theorem powPair_comp (q : ℕ) (φ : Series A) (hφ : ∀ i, constantCoeff (φ i) = 0) :
    (powPair A q).comp φ = fun i => φ i ^ q := by
  funext i
  show subst φ ((MvPowerSeries.X i : MvPowerSeries (Fin 2) A) ^ q) = φ i ^ q
  rw [← coe_substAlgHom (hasSubst_of_constantCoeff_zero hφ), map_pow, coe_substAlgHom,
    subst_X (hasSubst_of_constantCoeff_zero hφ)]

theorem powPair_comp_powPair {q q' : ℕ} (hq' : q' ≠ 0) :
    (powPair A q).comp (powPair A q') = powPair A (q' * q) := by
  rw [powPair_comp q _ (constantCoeff_powPair hq')]
  funext i
  rw [powPair, powPair, pow_mul]

theorem prod_powPair_pow (q : ℕ) (d : Fin 2 →₀ ℕ) :
    (d.prod fun s n => powPair A q s ^ n) = MvPowerSeries.monomial (q • d) (1 : A) := by
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  have h : ∀ i : Fin 2, powPair A q i ^ d i = MvPowerSeries.monomial (Finsupp.single i ((q • d) i)) (1 : A) := by
    intro i
    rw [powPair, ← pow_mul, MvPowerSeries.X_pow_eq, Finsupp.smul_apply, smul_eq_mul]
  simp_rw [h]
  rw [MvPowerSeries.prod_monomial, Finset.prod_const_one, Finsupp.univ_sum_single]

theorem smul_finsupp_injective {q : ℕ} (hq : q ≠ 0) {d d' : Fin 2 →₀ ℕ} (h : q • d = q • d') : d = d' := by
  ext i
  have := DFunLike.congr_fun h i
  simp only [Finsupp.smul_apply, smul_eq_mul] at this
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq) this

theorem coeff_smul_subst_powPair {q : ℕ} (hq : q ≠ 0) (f : MvPowerSeries (Fin 2) A) (m : Fin 2 →₀ ℕ) :
    coeff (q • m) (subst (powPair A q) f) = coeff m f := by
  classical
  rw [MvPowerSeries.coeff_subst (hasSubst_powPair hq)]
  have h : ∀ d : Fin 2 →₀ ℕ,
      coeff d f • coeff (q • m) (d.prod fun s n => powPair A q s ^ n) = if d = m then coeff m f else 0 := by
    intro d
    rw [prod_powPair_pow, MvPowerSeries.coeff_monomial]
    by_cases hd : d = m
    · subst hd; simp
    · have hne : q • m ≠ q • d := fun h' => hd (smul_finsupp_injective hq h').symm
      rw [if_neg hne, if_neg hd, smul_zero]
  simp_rw [h]
  rw [finsum_eq_single _ m (fun d hd => if_neg hd), if_pos rfl]

theorem comp_powPair_injective {q : ℕ} (hq : q ≠ 0) {φ ψ : Series A}
    (h : φ.comp (powPair A q) = ψ.comp (powPair A q)) : φ = ψ := by
  funext i
  ext m
  have hi := congrFun h i
  change subst (powPair A q) (φ i) = subst (powPair A q) (ψ i) at hi
  rw [← coeff_smul_subst_powPair hq (φ i) m, ← coeff_smul_subst_powPair hq (ψ i) m, hi]

variable {p : ℕ} [Fact p.Prime]

theorem frobSeries_eq_powPair (j : ℕ) : Rigidified.frobSeries (p := p) A j = powPair A (p ^ j) := rfl

theorem ppow_ne_zero (j : ℕ) : p ^ j ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero

theorem constantCoeff_frobSeries (j : ℕ) (i : Fin 2) :
    constantCoeff (Rigidified.frobSeries (p := p) A j i) = 0 :=
  constantCoeff_powPair (ppow_ne_zero j) i

theorem frobSeries_comp_frobSeries (a b : ℕ) :
    (Rigidified.frobSeries (p := p) A a).comp (Rigidified.frobSeries (p := p) A b) =
      Rigidified.frobSeries (p := p) A (a + b) := by
  rw [frobSeries_eq_powPair, frobSeries_eq_powPair, frobSeries_eq_powPair,
    powPair_comp_powPair (ppow_ne_zero b), ← pow_add, add_comm]

theorem comp_frobSeries_injective (j : ℕ) {φ ψ : Series A}
    (h : φ.comp (Rigidified.frobSeries (p := p) A j) = ψ.comp (Rigidified.frobSeries (p := p) A j)) : φ = ψ :=
  comp_powPair_injective (ppow_ne_zero j) h

theorem frobSeries_zero : Rigidified.frobSeries (p := p) A 0 = Series.id A := by
  funext i
  simp only [Rigidified.frobSeries, pow_zero, pow_one, Series.id]

end SeriesAlgebra

section ActAlgebra

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (Y : FormalODModule p A)

def sm (i : ℕ) (φ : Series A) : Series A := (Y.act ((p : Zp2 p) ^ i)).comp φ

theorem constantCoeff_act (a : Zp2 p) (i : Fin 2) : constantCoeff (Y.act a i) = 0 := (Y.isLawHom_act a).1 i

theorem constantCoeff_sm (i : ℕ) (φ : Series A) (hφ : ∀ l, constantCoeff (φ l) = 0) (l : Fin 2) :
    constantCoeff (sm Y i φ l) = 0 :=
  Series.constantCoeff_comp (constantCoeff_act Y _) hφ l

theorem sm_sm (i j : ℕ) (φ : Series A) (hφ : ∀ l, constantCoeff (φ l) = 0) :
    sm Y i (sm Y j φ) = sm Y (i + j) φ := by
  rw [sm, sm, sm, ← Series.comp_assoc _ _ _ (constantCoeff_act Y _) hφ, ← FormalODModule.act_pow_add]

theorem sm_comm (i j : ℕ) (φ : Series A) (hφ : ∀ l, constantCoeff (φ l) = 0) :
    sm Y i (sm Y j φ) = sm Y j (sm Y i φ) := by
  rw [sm_sm Y i j φ hφ, sm_sm Y j i φ hφ, add_comm]

theorem sm_comp (i : ℕ) (φ ψ : Series A) (hφ : ∀ l, constantCoeff (φ l) = 0) (hψ : ∀ l, constantCoeff (ψ l) = 0) :
    (sm Y i φ).comp ψ = sm Y i (φ.comp ψ) :=
  Series.comp_assoc _ _ _ hφ hψ

theorem sm_zero (φ : Series A) (hφ : ∀ l, constantCoeff (φ l) = 0) : sm Y 0 φ = φ := by
  rw [sm, pow_zero, Y.act_one, Series.id_comp _ hφ]

theorem sm_comp_frob_cancel (i i' : ℕ) (φ ψ : Series A) (hφ : ∀ l, constantCoeff (φ l) = 0)
    (hψ : ∀ l, constantCoeff (ψ l) = 0) (j : ℕ)
    (h : sm Y i (φ.comp (Rigidified.frobSeries (p := p) A j)) = sm Y i' (ψ.comp (Rigidified.frobSeries (p := p) A j))) :
    sm Y i φ = sm Y i' ψ := by
  rw [← sm_comp Y i φ _ hφ (constantCoeff_frobSeries j), ← sm_comp Y i' ψ _ hψ (constantCoeff_frobSeries j)] at h
  exact comp_frobSeries_injective j h

end ActAlgebra

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

theorem eq_of_isPullback_scalarGL (c : Kˣ) (d d' : DeligneDatum (K := K) π B)
    (h : DeligneDatum.IsPullback (K := K) (π := π) B (scalarGL c) d d') : d' = d := by
  rw [(isPullback_iff_eq_pullback π B _ d d').1 h, pullback_scalarGL]

end Scalars

section Frame

variable {r : ℕ} [Fact r.Prime] {k : Type} [Field k] [CharP k r] [IsAlgClosed k]
variable [Algebra ℤ_[r] (WittVector r k)]

local notation "Frob" => (WittVector.frobenius : WittVector r k →+* WittVector r k)

abbrev frPow (Fr : (WittVector r k) ≃ₐ[ℤ_[r]] (WittVector r k)) (n : ℤ) : (WittVector r k) →+* (WittVector r k) :=
  (((Fr ^ n : (WittVector r k) ≃ₐ[ℤ_[r]] (WittVector r k)) : (WittVector r k) →ₐ[ℤ_[r]] (WittVector r k)) : (WittVector r k) →+* (WittVector r k))

theorem frPow_natCast (Fr : (WittVector r k) ≃ₐ[ℤ_[r]] (WittVector r k)) (hFr : ∀ x : (WittVector r k), Fr x = WittVector.frobenius x) (n : ℕ) :
    frPow Fr (n : ℤ) = Frob ^ n := by
  rw [frPow, zpow_natCast]
  refine RingHom.ext fun x => ?_
  show (Fr ^ n) x = (WittVector.frobenius ^ n) x
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, AlgEquiv.mul_apply, RingHom.coe_mul, Function.comp_apply, hFr, ih]

theorem comp_frPow_comp_pow (Fr : (WittVector r k) ≃ₐ[ℤ_[r]] (WittVector r k)) (hFr : ∀ x : (WittVector r k), Fr x = WittVector.frobenius x)
    {L : Type} [CommRing L] (ψ : (WittVector r k) →+* L) (z : ℤ) (j : ℕ) :
    (ψ.comp (frPow Fr z)).comp (Frob ^ j) = ψ.comp (frPow Fr (z + j)) := by
  rw [RingHom.comp_assoc]
  congr 1
  rw [← frPow_natCast Fr hFr j]
  refine RingHom.ext fun x => ?_
  show (Fr ^ z) ((Fr ^ (j : ℤ)) x) = (Fr ^ (z + j)) x
  rw [zpow_add, AlgEquiv.mul_apply]

theorem comp_pow_add {L : Type} [CommRing L] (χ : (WittVector r k) →+* L) (a b : ℕ) :
    χ.comp (Frob ^ (a + b)) = (χ.comp (Frob ^ a)).comp (Frob ^ b) := by
  rw [pow_add, RingHom.comp_assoc]; rfl

theorem comp_pow_zero {L : Type} [CommRing L] (χ : (WittVector r k) →+* L) : χ.comp (Frob ^ 0) = χ := by
  rw [pow_zero]; rfl

variable (ι : Zp2 r →+* (WittVector r k)) (Φ : FormalODModule r ((WittVector r k) ⧸ pIdeal r (WittVector r k)))
variable (M : ModuliPackage.{0, 0} r (WittVector r k))
variable
  (η : ∀ (B : Type) [CommRing B] (ψ : (WittVector r k) →+* B) (hB : IsNilpotent (r : B)), Rigidified r Φ B → M.obj B ψ hB)
  (θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : (WittVector r k) →+* B) (hB : IsNilpotent (r : B)),
    M.obj B ψ hB → OmegaObj (K := ℚ_[r]) (r : ℤ_[r]) B)
  (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r])

theorem theta_eta_congr {L : Type} [CommRing L] [IsNoetherianRing L] [Algebra ℤ_[r] L] {ψ₁ ψ₂ : (WittVector r k) →+* L}
    (h : ψ₁ = ψ₂) (hL : IsNilpotent ((r : ℕ) : L)) (t : Rigidified r Φ L) :
    θ L ψ₁ hL (η L ψ₁ hL t) = θ L ψ₂ hL (η L ψ₂ hL t) := by
  subst h; rfl

theorem isAdmissible_congr {L : Type} [CommRing L] {ψ₁ ψ₂ : (WittVector r k) →+* L} (h : ψ₁ = ψ₂) (t : Rigidified r Φ L) :
    t.IsAdmissible ι ψ₁ ↔ t.IsAdmissible ι ψ₂ := by
  subst h; exact Iff.rfl

theorem eta_eq_congr {L : Type} [CommRing L] {ψ₁ ψ₂ : (WittVector r k) →+* L} (h : ψ₁ = ψ₂) (hL : IsNilpotent ((r : ℕ) : L))
    (t t' : Rigidified r Φ L) (h₁ : η L ψ₁ hL t = η L ψ₁ hL t') : η L ψ₂ hL t = η L ψ₂ hL t' := by
  subst h; exact h₁

abbrev eP : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) := (r : _)

theorem eP_toPowerSeries : ((eP Φ : Subring.centralizer _) : MvFormalGroup.End Φ.F).toPowerSeries = Φ.act (r : Zp2 r) := by
  rw [eP, SubringClass.coe_natCast, MvFormalGroup.End.toPowerSeries_natCast, FormalODModule.act_natCast]

theorem hasKernelOfDegree_eP (hΦ4 : Φ.HasHeight 4) :
    FormalODModule.HasKernelOfDegree ((eP Φ : Subring.centralizer _) : MvFormalGroup.End Φ.F).toPowerSeries
      (r ^ (2 * 2)) := by
  rw [eP_toPowerSeries]; exact hΦ4

theorem rQ_ne_zero : (r : ℚ_[r]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : r.Prime).ne_zero

def gP : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r] := LT.LatticeTree.scalarGL (Units.mk0 (r : ℚ_[r]) rQ_ne_zero)

theorem coe_gP : ((gP : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E (eP Φ) := by
  rw [gP, LT.LatticeTree.scalarGL_coe, Units.val_mk0, eP, map_natCast,
    ← map_natCast (algebraMap ℚ_[r] (Matrix (Fin 2) (Fin 2) ℚ_[r])) r, Algebra.algebraMap_eq_smul_one]

theorem map_eP_toPowerSeries {L : Type} [CommRing L] (χ : (WittVector r k) →+* L) :
    Series.map (residueMap χ) ((eP Φ : Subring.centralizer _) : MvFormalGroup.End Φ.F).toPowerSeries =
      (Φ.map (residueMap (p := r) χ)).act (r : Zp2 r) := by
  rw [eP_toPowerSeries]; rfl

end Frame

section Chain

variable {r : ℕ} [Fact r.Prime] {k : Type} [Field k] [CharP k r] [IsAlgClosed k]
variable [Algebra ℤ_[r] (WittVector r k)]

local notation "Frob" => (WittVector.frobenius : WittVector r k →+* WittVector r k)

variable (ι : Zp2 r →+* (WittVector r k)) (Φ : FormalODModule r ((WittVector r k) ⧸ pIdeal r (WittVector r k)))
variable (M : ModuliPackage.{0, 0} r (WittVector r k))
variable
  (η : ∀ (B : Type) [CommRing B] (ψ : (WittVector r k) →+* B) (hB : IsNilpotent (r : B)), Rigidified r Φ B → M.obj B ψ hB)
  (θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : (WittVector r k) →+* B) (hB : IsNilpotent (r : B)),
    M.obj B ψ hB → OmegaObj (K := ℚ_[r]) (r : ℤ_[r]) B)
  (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r])

abbrev GLdef : Prop :=
  ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : (WittVector r k) →+* B) (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
    ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ),
      FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) →
      ∃ t' : Rigidified r Φ B,
        t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) ∧
        t'.X = t.X ∧
        ∃ c : ℕ,
          (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
              (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ m')) =
            (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp
              (t.ρ.comp (Series.map (residueMap ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries))

abbrev GLeq : Prop :=
  ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : (WittVector r k) →+* B) (hB : IsNilpotent (r : B))
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
          (η B (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) hB t'))

variable {Φ}

theorem Xbar_congr {L : Type} [CommRing L] {s s' : Rigidified r Φ L} (h : s'.X = s.X) : s'.Xbar = s.Xbar := by
  show s'.X.map _ = s.X.map _; rw [h]

theorem rho_comp_act {L : Type} [CommRing L] {χ : (WittVector r k) →+* L} {s : Rigidified r Φ L} (hs : s.IsAdmissible ι χ) :
    s.ρ.comp ((Φ.map (residueMap (p := r) χ)).act (r : Zp2 r)) = sm s.Xbar 1 s.ρ := by
  rw [sm, pow_one]
  exact hs.2.2.1.2.1 (r : Zp2 r)

variable (Φ)

theorem chain (hΦ4 : Φ.HasHeight 4) (hGLdef : GLdef ι Φ) (hGLeq : GLeq ι Φ M η θ E)
    (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra ℤ_[r] L] (hL : IsNilpotent ((r : ℕ) : L))
    (χ : (WittVector r k) →+* L) (s : Rigidified r Φ L) (hs : s.IsAdmissible ι χ) :
    ∀ (j : ℕ) (ℓ : (WittVector r k) →+* L), ℓ = χ.comp (Frob ^ (2 * j)) →
      ∃ s' : Rigidified r Φ L, s'.IsAdmissible ι ℓ ∧ s'.X = s.X ∧
        (∃ c : ℕ, sm s.Xbar (c + s.n) (s'.ρ.comp (Rigidified.frobSeries (p := r) _ (2 * j))) =
          sm s.Xbar (c + s'.n + j) s.ρ) ∧
        θ L ℓ hL (η L ℓ hL s') = θ L χ hL (η L χ hL s) := by
  intro j
  induction j with
  | zero =>
      intro ℓ hℓ
      rw [Nat.mul_zero, comp_pow_zero] at hℓ
      subst hℓ
      refine ⟨s, hs, rfl, ⟨0, ?_⟩, rfl⟩
      rw [Nat.mul_zero, frobSeries_zero, Series.comp_id, Nat.add_zero]
  | succ j ih =>
      intro ℓ' hℓ'
      set ℓ : (WittVector r k) →+* L := χ.comp (Frob ^ (2 * j)) with hℓdef
      obtain ⟨sj, hsj, hXj, ⟨c, hc⟩, hθj⟩ := ih ℓ rfl
      have hℓ'eq : ℓ' = ℓ.comp (Frob ^ 2) := by
        rw [hℓ', hℓdef, show 2 * (j + 1) = 2 * j + 2 by ring, comp_pow_add]
      subst hℓ'eq

      obtain ⟨s'', hs'', hX'', d, hd⟩ := hGLdef L ℓ sj hsj (eP Φ) 2 (hasKernelOfDegree_eP Φ hΦ4)
      have hρj0 : ∀ l, constantCoeff (sj.ρ l) = 0 := hsj.constantCoeff_ρ
      have hρ''0 : ∀ l, constantCoeff (s''.ρ l) = 0 := hs''.constantCoeff_ρ
      have hρ0 : ∀ l, constantCoeff (s.ρ l) = 0 := hs.constantCoeff_ρ

      have hd' : sm s.Xbar (d + sj.n) (s''.ρ.comp (Rigidified.frobSeries (p := r) _ 2)) =
          sm s.Xbar (d + s''.n + 1) sj.ρ := by
        have h1 := hd
        rw [map_eP_toPowerSeries Φ ℓ, rho_comp_act ι hsj, Xbar_congr hXj] at h1
        change sm s.Xbar (d + sj.n) (s''.ρ.comp (Rigidified.frobSeries (p := r) _ 2)) =
          sm s.Xbar (d + s''.n) (sm s.Xbar 1 sj.ρ) at h1
        rw [sm_sm _ _ _ _ hρj0] at h1
        exact h1
      refine ⟨s'', hs'', hX''.trans hXj, ⟨c + d + sj.n, ?_⟩, ?_⟩
      ·
        have hF2 : ∀ l, constantCoeff (Rigidified.frobSeries (p := r) (L ⧸ pIdeal r L) 2 l) = 0 :=
          constantCoeff_frobSeries 2
        have hF2j : ∀ l, constantCoeff (Rigidified.frobSeries (p := r) (L ⧸ pIdeal r L) (2 * j) l) = 0 :=
          constantCoeff_frobSeries (2 * j)
        calc sm s.Xbar (c + d + sj.n + s.n) (s''.ρ.comp (Rigidified.frobSeries (p := r) _ (2 * (j + 1))))
            = sm s.Xbar (c + s.n) (sm s.Xbar (d + sj.n)
                ((s''.ρ.comp (Rigidified.frobSeries (p := r) _ 2)).comp (Rigidified.frobSeries (p := r) _ (2 * j)))) := by
              rw [sm_sm _ _ _ _ (Series.constantCoeff_comp (Series.constantCoeff_comp hρ''0 hF2) hF2j),
                Series.comp_assoc _ _ _ hF2 hF2j, frobSeries_comp_frobSeries,
                show 2 + 2 * j = 2 * (j + 1) by ring]
              congr 1; omega
          _ = sm s.Xbar (c + s.n) ((sm s.Xbar (d + sj.n) (s''.ρ.comp (Rigidified.frobSeries (p := r) _ 2))).comp
                (Rigidified.frobSeries (p := r) _ (2 * j))) := by
              rw [sm_comp _ _ _ _ (Series.constantCoeff_comp hρ''0 hF2) hF2j]
          _ = sm s.Xbar (c + s.n) ((sm s.Xbar (d + s''.n + 1) sj.ρ).comp (Rigidified.frobSeries (p := r) _ (2 * j))) := by
              rw [hd']
          _ = sm s.Xbar (d + s''.n + 1) (sm s.Xbar (c + s.n) (sj.ρ.comp (Rigidified.frobSeries (p := r) _ (2 * j)))) := by
              rw [sm_comp _ _ _ _ hρj0 hF2j, sm_comm _ _ _ _ (Series.constantCoeff_comp hρj0 hF2j)]
          _ = sm s.Xbar (d + s''.n + 1) (sm s.Xbar (c + sj.n + j) s.ρ) := by rw [hc]
          _ = sm s.Xbar (c + d + sj.n + s''.n + (j + 1)) s.ρ := by
              rw [sm_sm _ _ _ _ hρ0]; congr 1; omega
      ·
        have hpb := hGLeq L ℓ hL (eP Φ) 2 (hasKernelOfDegree_eP Φ hΦ4) gP (coe_gP Φ E) sj s'' hsj hs'' hX'' ⟨d, hd⟩
        rw [← hθj]
        exact eq_of_isPullback_scalarGL ((r : ℕ) : ℤ_[r]) L _ _ _ hpb

end Chain

section Main

variable {r : ℕ} [Fact r.Prime] {k : Type} [Field k] [CharP k r] [IsAlgClosed k]
variable [Algebra ℤ_[r] (WittVector r k)]

local notation "Frob" => (WittVector.frobenius : WittVector r k →+* WittVector r k)

theorem main
    (Fr : (WittVector r k) ≃ₐ[ℤ_[r]] (WittVector r k)) (hFr : ∀ x : (WittVector r k), Fr x = WittVector.frobenius x)
    (ι : Zp2 r →+* (WittVector r k)) (Φ : FormalODModule r ((WittVector r k) ⧸ pIdeal r (WittVector r k))) (hΦ4 : Φ.HasHeight 4)
    (M : ModuliPackage.{0, 0} r (WittVector r k))
    (η : ∀ (B : Type) [CommRing B] (ψ : (WittVector r k) →+* B) (hB : IsNilpotent (r : B)), Rigidified r Φ B → M.obj B ψ hB)
    (hη : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : (WittVector r k) →+* B) (hB : IsNilpotent (r : B))
      (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
      (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t'))
    (θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : (WittVector r k) →+* B) (hB : IsNilpotent (r : B)),
      M.obj B ψ hB → OmegaObj (K := ℚ_[r]) (r : ℤ_[r]) B)
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r])
    (hGLdef : GLdef ι Φ) (hGLeq : GLeq ι Φ M η θ E)
    (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra ℤ_[r] L] (ψ : (WittVector r k) →+* L) (hL : IsNilpotent ((r : ℕ) : L))
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (kk m' : ℕ)
    (he : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')))
    (g₀ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (hg₀ : (g₀ : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e)
    (t t' : Rigidified r Φ L) (ht : t.IsAdmissible ι ψ) (ht' : t'.IsAdmissible ι (ψ.comp (frPow Fr ((m' : ℤ) - 2 * kk))))
    (htt' : Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries kk m' ψ t t') :
    DeligneDatum.IsPullback (K := ℚ_[r]) (π := (r : ℤ_[r])) L g₀ (θ L ψ hL (η L ψ hL t))
      (θ L (ψ.comp (frPow Fr ((m' : ℤ) - 2 * kk))) hL (η L (ψ.comp (frPow Fr ((m' : ℤ) - 2 * kk))) hL t')) := by

  set ψ' : (WittVector r k) →+* L := ψ.comp (frPow Fr ((m' : ℤ) - 2 * kk)) with hψ'
  set ℓ₀ : (WittVector r k) →+* L := ψ.comp (Frob ^ m') with hℓ₀
  obtain ⟨hX', c, hc⟩ := htt'
  have hρ0 : ∀ l, constantCoeff (t.ρ l) = 0 := ht.constantCoeff_ρ
  have hρ'0 : ∀ l, constantCoeff (t'.ρ l) = 0 := ht'.constantCoeff_ρ
  set eS : Series (L ⧸ pIdeal r L) := Series.map (residueMap ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries with heS
  have heS0 : ∀ l, constantCoeff (eS l) = 0 := fun l => by
    rw [heS, Series.map, MvPowerSeries.constantCoeff_map, (e : MvFormalGroup.End Φ.F).constantCoeff_eq_zero l, map_zero]
  have hF : ∀ (j : ℕ) l, constantCoeff (Rigidified.frobSeries (p := r) (L ⧸ pIdeal r L) j l) = 0 :=
    fun j => constantCoeff_frobSeries j

  obtain ⟨t₀, ht₀, hX₀, c₀, hc₀⟩ := hGLdef L ψ t ht e m' he
  have hpb₀ : DeligneDatum.IsPullback (K := ℚ_[r]) (π := (r : ℤ_[r])) L g₀ (θ L ψ hL (η L ψ hL t))
      (θ L ℓ₀ hL (η L ℓ₀ hL t₀)) := hGLeq L ψ hL e m' he g₀ hg₀ t t₀ ht ht₀ hX₀ ⟨c₀, hc₀⟩
  have hρ₀0 : ∀ l, constantCoeff (t₀.ρ l) = 0 := ht₀.constantCoeff_ρ

  have hleg : ψ'.comp (Frob ^ (2 * kk)) = ℓ₀ := by
    rw [hψ', comp_frPow_comp_pow Fr hFr, hℓ₀, ← frPow_natCast Fr hFr]
    congr 2; push_cast; ring
  obtain ⟨s, hs, hXs, ⟨a, ha⟩, hθs⟩ := chain ι Φ M η θ E hΦ4 hGLdef hGLeq L hL ψ' t' ht' kk ℓ₀ hleg.symm
  have hρs0 : ∀ l, constantCoeff (s.ρ l) = 0 := hs.constantCoeff_ρ

  have hXbar' : t'.Xbar = t.Xbar := Xbar_congr hX'
  have hXbar₀ : t₀.Xbar = t.Xbar := Xbar_congr hX₀
  have R1 : sm t.Xbar (c + t.n + kk) (t'.ρ.comp (Rigidified.frobSeries (p := r) _ m')) =
      sm t.Xbar (c + t'.n) (t.ρ.comp (eS.comp (Rigidified.frobSeries (p := r) _ (2 * kk)))) := hc
  have R2 : sm t.Xbar (a + t'.n) (s.ρ.comp (Rigidified.frobSeries (p := r) _ (2 * kk))) =
      sm t.Xbar (a + s.n + kk) t'.ρ := by rw [← hXbar']; exact ha
  have R3 : sm t.Xbar (c₀ + t.n) (t₀.ρ.comp (Rigidified.frobSeries (p := r) _ m')) =
      sm t.Xbar (c₀ + t₀.n) (t.ρ.comp eS) := hc₀

  have key : sm t.Xbar (c₀ + t₀.n + (c + t.n + kk) + (a + t'.n)) s.ρ =
      sm t.Xbar (a + s.n + kk + (c + t'.n) + (c₀ + t.n)) t₀.ρ := by
    apply sm_comp_frob_cancel _ _ _ _ _ hρs0 hρ₀0 (2 * kk + m')
    calc sm t.Xbar (c₀ + t₀.n + (c + t.n + kk) + (a + t'.n)) (s.ρ.comp (Rigidified.frobSeries (p := r) _ (2 * kk + m')))
        = sm t.Xbar (c₀ + t₀.n) (sm t.Xbar (c + t.n + kk)
            ((sm t.Xbar (a + t'.n) (s.ρ.comp (Rigidified.frobSeries (p := r) _ (2 * kk)))).comp
              (Rigidified.frobSeries (p := r) _ m'))) := by
          rw [sm_comp _ _ _ _ (Series.constantCoeff_comp hρs0 (hF _)) (hF _),
            Series.comp_assoc _ _ _ (hF _) (hF _), frobSeries_comp_frobSeries,
            sm_sm _ _ _ _ (Series.constantCoeff_comp hρs0 (hF _)),
            sm_sm _ _ _ _ (Series.constantCoeff_comp hρs0 (hF _))]
          simp only [add_assoc]
      _ = sm t.Xbar (c₀ + t₀.n) (sm t.Xbar (c + t.n + kk)
            ((sm t.Xbar (a + s.n + kk) t'.ρ).comp (Rigidified.frobSeries (p := r) _ m'))) := by rw [R2]
      _ = sm t.Xbar (c₀ + t₀.n) (sm t.Xbar (a + s.n + kk)
            (sm t.Xbar (c + t.n + kk) (t'.ρ.comp (Rigidified.frobSeries (p := r) _ m')))) := by
          rw [sm_comp _ _ _ _ hρ'0 (hF _), sm_comm _ _ _ _ (Series.constantCoeff_comp hρ'0 (hF _))]
      _ = sm t.Xbar (c₀ + t₀.n) (sm t.Xbar (a + s.n + kk)
            (sm t.Xbar (c + t'.n) (t.ρ.comp (eS.comp (Rigidified.frobSeries (p := r) _ (2 * kk)))))) := by rw [R1]
      _ = sm t.Xbar (a + s.n + kk) (sm t.Xbar (c + t'.n)
            ((sm t.Xbar (c₀ + t₀.n) (t.ρ.comp eS)).comp (Rigidified.frobSeries (p := r) _ (2 * kk)))) := by
          rw [sm_comp _ _ _ _ (Series.constantCoeff_comp hρ0 heS0) (hF _),
            Series.comp_assoc _ _ _ heS0 (hF _),
            sm_comm _ (c₀ + t₀.n) _ _ (constantCoeff_sm _ _ _
              (Series.constantCoeff_comp hρ0 (Series.constantCoeff_comp heS0 (hF _)))),
            sm_comm _ (c₀ + t₀.n) _ _ (Series.constantCoeff_comp hρ0 (Series.constantCoeff_comp heS0 (hF _)))]
      _ = sm t.Xbar (a + s.n + kk) (sm t.Xbar (c + t'.n)
            ((sm t.Xbar (c₀ + t.n) (t₀.ρ.comp (Rigidified.frobSeries (p := r) _ m'))).comp
              (Rigidified.frobSeries (p := r) _ (2 * kk)))) := by rw [R3]
      _ = sm t.Xbar (a + s.n + kk + (c + t'.n) + (c₀ + t.n))
            (t₀.ρ.comp (Rigidified.frobSeries (p := r) _ (2 * kk + m'))) := by
          rw [sm_comp _ _ _ _ (Series.constantCoeff_comp hρ₀0 (hF _)) (hF _),
            Series.comp_assoc _ _ _ (hF _) (hF _), frobSeries_comp_frobSeries, add_comm m' (2 * kk),
            sm_sm _ _ _ _ (Series.constantCoeff_comp hρ₀0 (hF _)),
            sm_sm _ _ _ _ (Series.constantCoeff_comp hρ₀0 (hF _))]
          simp only [add_assoc]

  have hXs₀ : s.X = t₀.X := by rw [hXs, hX', hX₀]
  have hiso : s.IsIsomorphic t₀ := by
    refine ⟨Series.id L, Series.id L, c₀ + c + t.n + kk + a + t'.n, ?_, ?_, Series.comp_id _, Series.comp_id _, ?_⟩
    · rw [hXs₀]; exact FormalODModule.IsODHom.id t₀.X
    · rw [hXs₀]; exact FormalODModule.IsODHom.id t₀.X
    · rw [Series.map_id, Series.id_comp _ hρs0, hXbar₀]
      change sm t.Xbar (c₀ + c + t.n + kk + a + t'.n + t₀.n) s.ρ = sm t.Xbar (c₀ + c + t.n + kk + a + t'.n + s.n) t₀.ρ
      convert key using 2 <;> omega
  have hηeq : η L ℓ₀ hL s = η L ℓ₀ hL t₀ := (hη L ℓ₀ hL s t₀ hs ht₀).2 hiso

  rw [isPullback_iff_eq_pullback] at hpb₀ ⊢
  rw [← hθs, hηeq, hpb₀]

end Main

end R4TranslatePullback

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega in

theorem solution
    {r : ℕ} [Fact r.Prime] (k : Type) [Field k] [CharP k r] [IsAlgClosed k]
    [Algebra ℤ_[r] (WittVector r k)]
    (Fr : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k) (hFr : ∀ x : WittVector r k, Fr x = WittVector.frobenius x)
    (ι : Zp2 r →+* WittVector r k)
    (Φ : FormalODModule r (WittVector r k ⧸ pIdeal r (WittVector r k)))
    (hΦ4 : Φ.HasHeight 4)
    (M : ModuliPackage.{0, 0} r (WittVector r k))
    (η : ∀ (B : Type) [CommRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → M.obj B ψ hB)
    (hη : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B))
      (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
      (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t'))
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
            (η B (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) hB t')))

    (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra ℤ_[r] L] (ψ : WittVector r k →+* L) (hL : IsNilpotent (r : L))
    (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (kk m' : ℕ)
    (he : FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')))
    (g₀ : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (hg₀ : (g₀ : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e)
    (t t' : Rigidified r Φ L) (ht : t.IsAdmissible ι ψ)
    (ht' : t'.IsAdmissible ι
      (ψ.comp (((Fr ^ ((m' : ℤ) - 2 * kk) : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k) :
        WittVector r k →ₐ[ℤ_[r]] WittVector r k) : WittVector r k →+* WittVector r k)))
    (htt' : Rigidified.IsTranslate (e : MvFormalGroup.End Φ.F).toPowerSeries kk m' ψ t t') :
    DeligneDatum.IsPullback (K := ℚ_[r]) (π := (r : ℤ_[r])) L g₀ (θ L ψ hL (η L ψ hL t))
      (θ L (ψ.comp (((Fr ^ ((m' : ℤ) - 2 * kk) : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k) :
          WittVector r k →ₐ[ℤ_[r]] WittVector r k) : WittVector r k →+* WittVector r k)) hL
        (η L (ψ.comp (((Fr ^ ((m' : ℤ) - 2 * kk) : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k) :
          WittVector r k →ₐ[ℤ_[r]] WittVector r k) : WittVector r k →+* WittVector r k)) hL t')) :=
  R4TranslatePullback.main Fr hFr ι Φ hΦ4 M η hη θ E hGLdef hGLeq L ψ hL e kk m' he g₀ hg₀ t t' ht ht' htt'

end

end S_CerednikDrinfeld_SpecialFormal_Rigidified_isPullback_of_isTranslate_of_isTranslate_zero
end P2MW
export P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_isPullback_of_isTranslate_of_isTranslate_zero (solution)
