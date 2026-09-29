-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_and_hasStructureConstants_liftVar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c451a108-0c67-537d-a4e4-3621be6b292e

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants

import Theorems.Thm_MvFormalGroup_exists_cartierModule_vBasis_of_frobenius_expansion
import Theorems.Thm_CerednikDrinfeld_CartierLift_exists_digits_forall_smul_eq_teichmuller_smul_add_sum_verschiebungInt
import Theorems.Thm_MvFormalGroup_CartierModule_exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_smul
import Theorems.Thm_MvFormalGroup_CartierModule_exists_zp2Action_of_graded_frobenius_expansion
import Definitions.Def_MvFormalGroup_WittPointFamily
import Theorems.Thm_MvFormalGroup_CartierModule_verschiebungInt_injective_of_algebra_padicInt
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add
import Theorems.Thm_MvFormalGroup_exists_subst_eq_X_of_linearPart_eq_one
import Theorems.Thm_MvFormalGroup_exists_hom_comp_eq_id_tangent_map_eq_of_isUnit_det
import Theorems.Thm_MvFormalGroup_CartierModule_varpiTuple_rel_and_sum_eq_of_rel
import Theorems.Thm_WittVector_coeff_eq_coeff_of_forall_ghostComponent_eq
import Theorems.Thm_WittVector_exists_forall_ghostComponent_eq_of_sub_frobeniusLift_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_and_hasStructureConstants_liftVar
p2m_attr_erase "simp" "MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

universe u

open MvPowerSeries

namespace FFromPi

section W1

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R]

open MvFormalGroup MvFormalGroup.WittLaw in

theorem mulFam_verschiebung_eq (w : WittVector p R) (n : ℕ) :
    mulFam p (WittVector.verschiebung w) n =
      subst (fun k => subst (frobPolyFam p R) (mulFam p w k)) (verFam R n) := by
  have hcV : cVec p (τ := ℕ) (WittVector.verschiebung w) = WittVector.verschiebung (cVec p w) :=
    WittVector.map_verschiebung _ w
  have hL : mulFam p (WittVector.verschiebung w) n =
      (((WittVector.verschiebung (cVec p w * WittVector.frobenius (xTaut p R))).coeff n :
        MvPolynomial ℕ R) : MvPowerSeries ℕ R) := by
    rw [mulFam_apply, WittVector.verschiebung_mul_frobenius, ← hcV]
    rfl
  have hR : ∀ k, subst (frobPolyFam p R) (mulFam p w k) =
      (((cVec p w * WittVector.frobenius (xTaut p R)).coeff k : MvPolynomial ℕ R) :
        MvPowerSeries ℕ R) := by
    intro k
    have hf : frobPolyFam p R = fun m => (frobPoly p R m : MvPowerSeries ℕ R) := rfl
    rw [hf, mulFam_apply, ← WittLaw.coe_aeval, aeval_mulPoly, mk_frobPoly]
  have hS : HasSubst (fun k => subst (frobPolyFam p R) (mulFam p w k)) := by
    have h := (hasSubst_mulFam (p := p) w).comp (hasSubst_frobPolyFam (p := p) (R := R))
    simpa only [coe_substAlgHom] using h
  rw [hL]
  cases n with
  | zero =>
    rw [WittVector.verschiebung_coeff_zero, verFam_zero, MvPolynomial.coe_zero]
    rw [← coe_substAlgHom hS, map_zero]
  | succ k =>
    rw [WittVector.verschiebung_coeff_succ, verFam_succ, subst_X hS, hR]

open MvFormalGroup MvFormalGroup.CartierModule in

theorem verschiebung_smul_eq {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]
    (w : WittVector p R) (f : CartierModule p Φ) :
    WittVector.verschiebung w • f = verschiebungInt (w • frobenius f) := by
  apply CartierModule.ext
  funext j
  show subst (WittLaw.mulFam p (WittVector.verschiebung w)) (f.toPowerSeries j) =
    subst (WittLaw.frobPolyFam p R) (subst (WittLaw.mulFam p w)
      (subst (WittLaw.verFam R) (f.toPowerSeries j)))
  have hS : HasSubst (fun k => subst (WittLaw.frobPolyFam p R) (WittLaw.mulFam p w k)) := by
    have h := (WittLaw.hasSubst_mulFam (p := p) w).comp (WittLaw.hasSubst_frobPolyFam (p := p) (R := R))
    simpa only [coe_substAlgHom] using h
  rw [subst_comp_subst_apply (WittLaw.hasSubst_mulFam w) WittLaw.hasSubst_frobPolyFam,
    subst_comp_subst_apply WittLaw.hasSubst_verFam hS]
  congr 1
  funext n
  exact mulFam_verschiebung_eq w n

end W1

section W2

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R]

theorem eq_teichmuller_add_verschiebung_shift (w : WittVector p R) :
    w = WittVector.teichmuller p (w.coeff 0) + WittVector.verschiebung (w.shift 1) := by
  have h := WittVector.init_add_tail w 1
  have hi : WittVector.init 1 w = WittVector.teichmuller p (w.coeff 0) := by
    ext n
    simp only [WittVector.init, WittVector.select, WittVector.coeff_mk]
    cases n with
    | zero => simp [WittVector.teichmuller_coeff_zero]
    | succ n => simp [WittVector.teichmuller_coeff_pos p (w.coeff 0) (n + 1) (Nat.succ_pos n)]
  have ht : WittVector.tail 1 w = WittVector.verschiebung (w.shift 1) := by
    ext n
    simp only [WittVector.tail, WittVector.select, WittVector.coeff_mk]
    cases n with
    | zero => simp [WittVector.verschiebung_coeff_zero]
    | succ n => simp [WittVector.verschiebung_coeff_succ, WittVector.shift_coeff, Nat.add_comm]
  rw [hi, ht] at h
  exact h.symm

open MvFormalGroup MvFormalGroup.CartierModule in

theorem smul_eq_homothety_add {d : ℕ} {Φ : MvFormalGroup d R} [Φ.IsComm]
    (w : WittVector p R) (f : CartierModule p Φ) :
    w • f = homothety (w.coeff 0) f + verschiebungInt (w.shift 1 • frobenius f) := by
  conv_lhs => rw [eq_teichmuller_add_verschiebung_shift w]
  rw [add_smul, teichmuller_smul, verschiebung_smul_eq]

end W2

section W3

variable (p : ℕ) [hp : Fact p.Prime]

theorem ghostComponent_eq_of_coeff_eq {R : Type u} [CommRing R] (n : ℕ) (x y : WittVector p R)
    (h : ∀ i ≤ n, x.coeff i = y.coeff i) :
    WittVector.ghostComponent n x = WittVector.ghostComponent n y := by
  rw [WittVector.ghostComponent_apply, WittVector.ghostComponent_apply, aeval_wittPolynomial,
    aeval_wittPolynomial]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [h i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]

theorem exists_natCast_eq_teichmuller_add_verschiebung_unit :
    ∃ η θ : WittVector p (PadicInt p),
      (p : WittVector p (PadicInt p)) =
        WittVector.teichmuller p (p : PadicInt p) + WittVector.verschiebung η ∧ θ * η = 1 := by
  have hp0 : (p : PadicInt p) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hpnz : (p : PadicInt p) ∈ nonZeroDivisors (PadicInt p) := mem_nonZeroDivisors_of_ne_zero hp0
  set y : WittVector p (PadicInt p) :=
    (p : WittVector p (PadicInt p)) - WittVector.teichmuller p (p : PadicInt p) with hy
  set η : WittVector p (PadicInt p) := y.shift 1 with hη
  have hyV : WittVector.verschiebung η = y := by
    have := eq_teichmuller_add_verschiebung_shift (p := p) y
    have hy0 : y.coeff 0 = 0 := by
      have h1 := (WittVector.constantCoeff : WittVector p (PadicInt p) →+* PadicInt p).map_sub
        (p : WittVector p (PadicInt p)) (WittVector.teichmuller p (p : PadicInt p))
      have h2 : (WittVector.constantCoeff : WittVector p (PadicInt p) →+* PadicInt p)
          (p : WittVector p (PadicInt p)) = p := map_natCast _ p
      rw [h2] at h1
      rw [WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
        WittVector.teichmuller_coeff_zero, sub_self] at h1
      rw [hy]; exact h1
    rw [hy0, WittVector.teichmuller_zero, zero_add] at this
    rw [hη]; exact this.symm

  have hgη : ∀ k, WittVector.ghostComponent k η = 1 - (p : PadicInt p) ^ (p ^ (k + 1) - 1) := by
    intro k
    have h := congrArg (WittVector.ghostComponent (k + 1)) hyV
    rw [WittVector.ghostComponent_verschiebung, hy, map_sub, map_natCast,
      WittVector.ghostComponent_teichmuller] at h
    have hk : 1 ≤ p ^ (k + 1) := Nat.one_le_pow _ _ hp.out.pos
    have h2 : (p : PadicInt p) * WittVector.ghostComponent k η =
        p * (1 - (p : PadicInt p) ^ (p ^ (k + 1) - 1)) := by
      rw [h, mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hk]
    exact mul_left_cancel₀ hp0 h2

  have hle : ∀ k : ℕ, k + 1 ≤ p ^ (k + 1) - 1 := fun k =>
    Nat.le_sub_one_of_lt (Nat.lt_pow_self hp.out.one_lt)
  have hu : ∀ k : ℕ, IsUnit (1 - (p : PadicInt p) ^ (p ^ (k + 1) - 1)) := by
    intro k
    have hmem : (p : PadicInt p) ^ (p ^ (k + 1) - 1) ∈ nonunits (PadicInt p) := by
      rw [← IsLocalRing.mem_maximalIdeal, PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _
        (Nat.lt_of_lt_of_le (Nat.succ_pos k) (hle k))
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hmem
  set g : ℕ → PadicInt p := fun k => ((hu k).unit⁻¹ : (PadicInt p)ˣ) with hg
  have hgu : ∀ k, g k * (1 - (p : PadicInt p) ^ (p ^ (k + 1) - 1)) = 1 := by
    intro k
    have h1 := (hu k).unit.inv_mul
    rw [IsUnit.unit_spec] at h1
    exact h1

  have hσ : ∀ a : PadicInt p, (RingHom.id (PadicInt p)) a - a ^ p ∈ Ideal.span {(p : PadicInt p)} := by
    intro a
    rw [RingHom.id_apply, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod, RingHom.mem_ker,
      map_sub, map_pow, ZMod.pow_card, sub_self]
  have hpowmem : ∀ k m : ℕ, k + 1 ≤ m →
      (p : PadicInt p) ^ m ∈ Ideal.span {(p : PadicInt p) ^ (k + 1)} := fun k m hkm =>
    Ideal.mem_span_singleton.mpr (pow_dvd_pow _ hkm)
  have hgc : ∀ k : ℕ, k + 1 < 0 + (0 : ℕ) + (k + 2) →
      g (k + 1) - (RingHom.id (PadicInt p)) (g k) ∈ Ideal.span {(p : PadicInt p) ^ (k + 1)} := by
    intro k _
    rw [RingHom.id_apply]
    have key : g (k + 1) - g k = g (k + 1) * g k *
        ((p : PadicInt p) ^ (p ^ (k + 2) - 1) - (p : PadicInt p) ^ (p ^ (k + 1) - 1)) := by
      have a1 := hgu k
      have a2 := hgu (k + 1)
      linear_combination (-(g (k + 1))) * a1 + (g k) * a2
    rw [key]
    refine Ideal.mul_mem_left _ _ (Ideal.sub_mem _ ?_ ?_)
    · exact hpowmem k _ ((hle k).trans (Nat.sub_le_sub_right
        (Nat.pow_le_pow_right hp.out.pos (Nat.le_succ _)) 1))
    · exact hpowmem k _ (hle k)
  have hex : ∀ n : ℕ, ∃ x : WittVector p (PadicInt p), ∀ k < n, WittVector.ghostComponent k x = g k :=
    fun n => WittVector.exists_forall_ghostComponent_eq_of_sub_frobeniusLift_mem p (RingHom.id _) hσ n g
      (fun k _ => hgc k (by omega))
  choose xs hxs using hex
  set θ : WittVector p (PadicInt p) := WittVector.mk p fun k => (xs (k + 1)).coeff k with hθ
  have hθcoeff : ∀ n k, k < n → θ.coeff k = (xs n).coeff k := by
    intro n k hk
    have h1 := WittVector.coeff_eq_coeff_of_forall_ghostComponent_eq p hpnz (k + 1) (xs (k + 1)) (xs n)
      (fun i hi => by rw [hxs (k + 1) i hi, hxs n i (by omega)]) k (Nat.lt_succ_self k)
    rw [← h1, hθ, WittVector.coeff_mk]
  have hgθ : ∀ k, WittVector.ghostComponent k θ = g k := by
    intro k
    rw [ghostComponent_eq_of_coeff_eq p k θ (xs (k + 1)) (fun i hi => hθcoeff (k + 1) i (Nat.lt_succ_of_le hi)),
      hxs (k + 1) k (Nat.lt_succ_self k)]
  refine ⟨η, θ, ?_, ?_⟩
  · rw [hyV, hy, add_sub_cancel]
  · ext k
    exact WittVector.coeff_eq_coeff_of_forall_ghostComponent_eq p hpnz (k + 1) (θ * η) 1
      (fun i _ => by rw [map_mul, hgθ, hgη, map_one, hgu]) k (Nat.lt_succ_self k)

theorem exists_natCast_eq_teichmuller_add_verschiebung_unit_map
    {B : Type u} [CommRing B] [Algebra (PadicInt p) B] :
    ∃ η θ : WittVector p B,
      (p : WittVector p B) = WittVector.teichmuller p (p : B) + WittVector.verschiebung η ∧ θ * η = 1 := by
  obtain ⟨η, θ, h1, h2⟩ := exists_natCast_eq_teichmuller_add_verschiebung_unit p
  refine ⟨WittVector.map (algebraMap (PadicInt p) B) η, WittVector.map (algebraMap (PadicInt p) B) θ, ?_, ?_⟩
  · have h := congrArg (WittVector.map (algebraMap (PadicInt p) B)) h1
    rw [map_natCast, map_add, WittVector.map_teichmuller, WittVector.map_verschiebung, map_natCast] at h
    exact h
  · rw [← map_mul, h2, map_one]

end W3

end FFromPi

universe v

noncomputable section

namespace P2mLawPresWx

open MvPowerSeries

section Generic

open MvFormalGroup

variable {R : Type u} [CommRing R] {d : ℕ} {Φ : MvFormalGroup d R}

theorem hasSubst_constX (i : Fin d) :
    HasSubst (fun _ : Unit => (X i : MvPowerSeries (Fin d) R)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X i

def linMap (Φ : MvFormalGroup d R) [Φ.IsComm] (m : ℕ) :
    SeriesPoint Φ (Fin m) →+ Matrix (Fin d) (Fin m) R where
  toFun a := linearPart a.val
  map_zero' := by rw [SeriesPoint.val_zero]; exact linearPart_zero
  map_add' a b := by
    rw [SeriesPoint.val_add]
    exact linearPart_subst_elim Φ a.constantCoeff_eq_zero b.constantCoeff_eq_zero

@[scoped simp] theorem linMap_apply [Φ.IsComm] (m : ℕ) (a : SeriesPoint Φ (Fin m)) :
    linMap Φ m a = linearPart a.val :=
  rfl

def XPt (Φ : MvFormalGroup d R) : SeriesPoint Φ (Fin d) := ⟨fun i => X i, fun i => constantCoeff_X i⟩

def inlPt (Φ : MvFormalGroup d R) : SeriesPoint Φ (Fin d ⊕ Fin d) :=
  ⟨fun l => X (Sum.inl l), fun _ => constantCoeff_X _⟩

def inrPt (Φ : MvFormalGroup d R) : SeriesPoint Φ (Fin d ⊕ Fin d) :=
  ⟨fun l => X (Sum.inr l), fun _ => constantCoeff_X _⟩

theorem val_inlPt_add_inrPt : (inlPt Φ + inrPt Φ).val = Φ.toPowerSeries := by
  rw [SeriesPoint.val_add]
  funext j
  have hX : Sum.elim (inlPt Φ).val (inrPt Φ).val =
      fun s => (X s : MvPowerSeries (Fin d ⊕ Fin d) R) := by
    funext s
    rcases s with l | l <;> rfl
  rw [hX]
  exact congrFun subst_self _

theorem prod_X_pow_eq_monomial {σ : Type*} (e : σ →₀ ℕ) :
    (e.prod fun s k => (X s : MvPowerSeries σ R) ^ k) = monomial e 1 := by
  have h := monomial_eq e (fun _ : σ => (1 : R))
  have h1 : (e.prod fun _ n => (1 : R) ^ n) = 1 := by simp [Finsupp.prod]
  rw [h1] at h
  rw [h]
  exact Finsupp.prod_congr fun s _ => by rw [one_smul]

end Generic

section Section

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] {d d' : ℕ}
  {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} [Φ.IsComm] [Φ'.IsComm]

def cwPt (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] (d : ℕ) (i : Fin d) :
    WittLaw.seriesPoint p R (Fin d) :=
  WittLaw.substPt (b := fun _ : Unit => (X i : MvPowerSeries (Fin d) R)) (hasSubst_constX i)
    (fun _ => constantCoeff_X i) WittLaw.curveTautPt

theorem val_evalPt_cwPt (g : CartierModule p Φ) (i : Fin d) :
    (evalPt g (cwPt p R d i)).val = fun j => subst (fun _ : Unit => (X i : MvPowerSeries (Fin d) R))
      (curve g j) := by
  rw [cwPt, ← substPt_evalPt]
  rfl

theorem coeff_single_val_evalPt_cwPt (g : CartierModule p Φ) (i j j' : Fin d) :
    coeff (Finsupp.single j' 1) ((evalPt g (cwPt p R d i)).val j) =
      if j' = i then tangent g j else 0 := by
  classical
  rw [val_evalPt_cwPt]
  dsimp only
  rw [coeff_single_subst (fun _ => constantCoeff_X i), Fintype.sum_unique, coeff_X,
    ← PowerSeries.coeff_def (s := Finsupp.single (default : Unit) 1) (n := 1) (by simp), coeff_one_curve]
  by_cases hji : j' = i
  · subst hji
    rw [if_pos rfl, if_pos rfl, mul_one]
  · rw [if_neg (fun h => hji (Finsupp.single_left_injective one_ne_zero h)), if_neg hji, mul_zero]

def GPt (f : Fin d → CartierModule p Φ) : SeriesPoint Φ (Fin d) :=
  presPi f (cwPt p R d)

theorem linearPart_GPt (f : Fin d → CartierModule p Φ)
    (hf : ∀ i j, tangent (f i) j = if i = j then 1 else 0) : linearPart (GPt (p := p) f).val = 1 := by
  rw [← linMap_apply, GPt, presPi_def, map_sum]
  ext j j'
  rw [Matrix.sum_apply, Matrix.one_apply]
  simp only [linMap_apply, linearPart, Matrix.of_apply, coeff_single_val_evalPt_cwPt]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), hf]
  by_cases h : j = j'
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem presPi_substPt {ι : Type*} [Fintype ι] (F : ι → CartierModule p Φ) {τ : Type v}
    {τ' : Type*} {b : τ → MvPowerSeries τ' R} (hb : HasSubst b) (hb0 : ∀ t, (b t).constantCoeff = 0)
    (v : ι → WittLaw.seriesPoint p R τ) :
    presPi F (fun l => WittLaw.substPt hb hb0 (v l)) = SeriesPoint.substPt hb hb0 (presPi F v) := by
  simp only [presPi_def, map_sum, substPt_evalPt]

variable (f : Fin d → CartierModule p Φ) {uinv : Fin d → MvPowerSeries (Fin d) R}
  (hu0 : ∀ i, (uinv i).constantCoeff = 0) (hu : ∀ i, subst uinv ((GPt (p := p) f).val i) = X i)

def wX : Fin d → WittLaw.seriesPoint p R (Fin d) := fun l =>
  WittLaw.substPt (hasSubst_of_constantCoeff_zero hu0) hu0 (cwPt p R d l)

include hu in

theorem presPi_wX : presPi f (wX (p := p) hu0) = XPt Φ := by
  unfold wX
  rw [presPi_substPt]
  refine SeriesPoint.ext (funext fun i => ?_)
  exact hu i

def wOf {τ : Type v} (a : SeriesPoint Φ τ) : Fin d → WittLaw.seriesPoint p R τ := fun l =>
  WittLaw.substPt a.hasSubst_val a.constantCoeff_eq_zero (wX (p := p) hu0 l)

include hu in

theorem presPi_wOf {τ : Type v} (a : SeriesPoint Φ τ) : presPi f (wOf (p := p) hu0 a) = a := by
  unfold wOf
  rw [presPi_substPt, presPi_wX f hu0 hu]
  refine SeriesPoint.ext (funext fun i => ?_)
  exact subst_X a.hasSubst_val i

end Section

section HomEq

open MvFormalGroup MvFormalGroup.CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R] {d d' : ℕ}
  {Φ : MvFormalGroup d R} {Ψ : MvFormalGroup d' R} [Φ.IsComm] [Ψ.IsComm]

theorem hom_eq_of_map_basis_eq (f : Fin d → CartierModule p Φ)
    (hf : ∀ i j, tangent (f i) j = if i = j then 1 else 0)
    (φ ψ : Φ.Hom Ψ) (h : ∀ l, CartierModule.map φ (f l) = CartierModule.map ψ (f l)) : φ = ψ := by
  obtain ⟨uinv, hu0, -, hu⟩ := MvFormalGroup.exists_subst_eq_X_of_linearPart_eq_one
    (GPt (p := p) f).val (GPt (p := p) f).constantCoeff_eq_zero (linearPart_GPt f hf)
  have key : SeriesPoint.mapPt φ (XPt Φ) = SeriesPoint.mapPt ψ (XPt Φ) := by
    rw [← presPi_wX (p := p) f hu0 hu, mapPt_presPi, mapPt_presPi]
    congr 1
    funext l
    exact h l
  apply MvFormalGroup.Hom.ext
  funext j
  have hv := congrArg (fun a : SeriesPoint Ψ (Fin d) => a.val j) key
  simp only [SeriesPoint.val_mapPt, XPt] at hv
  have hX : (fun i => (X i : MvPowerSeries (Fin d) R)) = MvPowerSeries.X := rfl
  rw [hX, MvPowerSeries.subst_self] at hv
  exact hv

end HomEq

end P2mLawPresWx
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_and_hasStructureConstants_liftVar.P2mLawPresWx"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_and_hasStructureConstants_liftVar.P2mLawPresWx"

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld CerednikDrinfeld.SpecialFormal

noncomputable section

namespace RealiseODUniv

variable (p : ℕ) [Fact p.Prime]

abbrev U : Type := CartierLift.LiftRing p (Zp2 p) ((0, 0) : ℕ × Fin 2) (0, 1)

scoped instance instAlgebraPadicInt : Algebra (PadicInt p) (U p) :=
  ((algebraMap (Zp2 p) (U p)).comp
    ((WittVector.map (algebraMap (ZMod p) (GaloisField p 2))).comp
      (WittVector.equiv p).symm.toRingHom)).toAlgebra

abbrev Xv (m : ℕ) (i : Fin 2) : U p :=
  CartierLift.liftVar (p := p) (R := Zp2 p) ((0, 0) : ℕ × Fin 2) (0, 1) (m, i)

def dW (k : ℕ) (i : Fin 2) : WittVector p (U p) :=
  ∑ m ∈ Finset.range (k + 2),
    WittVector.teichmuller p (Xv p m i ^ p ^ (k + 1 - m) * Xv p (k + 1 - m) (FormalODModule.piIndex m i))

section Generic

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [Algebra (PadicInt p) R] {d d' : ℕ}

theorem eq_zero_of_forall_exists_iterate (Ψ : MvFormalGroup d' R) [Ψ.IsComm]
    (x : CartierModule p Ψ)
    (hx : ∀ N : ℕ, ∃ t : CartierModule p Ψ, x = (⇑(verschiebungInt (p := p) (Φ := Ψ)))^[N] t) :
    x = 0 := by
  obtain ⟨s, hs, huniq⟩ :=
    MvFormalGroup.CartierModule.existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add p Ψ (fun _ => 0)
  have h0 : (0 : CartierModule p Ψ) = s := huniq 0 (fun N => ⟨0, by simp [iterate_map_zero]⟩)
  have h1 : x = s := huniq x (fun N => by
    obtain ⟨t, ht⟩ := hx N
    exact ⟨t, by simpa [iterate_map_zero] using ht⟩)
  rw [h1, ← h0]

theorem map_iterate_verschiebungInt (Φ : MvFormalGroup d R) [Φ.IsComm] (Ψ : MvFormalGroup d' R) [Ψ.IsComm]
    (φ : Φ.Hom Ψ) (m : ℕ) (x : CartierModule p Φ) :
    CartierModule.map φ ((⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] x) =
      (⇑(verschiebungInt (p := p) (Φ := Ψ)))^[m] (CartierModule.map φ x) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_verschiebungInt, ih]

theorem iterate_verschiebungInt_sub (Ψ : MvFormalGroup d' R) [Ψ.IsComm] (N : ℕ) (a b : CartierModule p Ψ) :
    (⇑(verschiebungInt (p := p) (Φ := Ψ)))^[N] a - (⇑(verschiebungInt (p := p) (Φ := Ψ)))^[N] b =
      (⇑(verschiebungInt (p := p) (Φ := Ψ)))^[N] (a - b) := by
  induction N generalizing a b with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply',
      ← map_sub, ih]

theorem smul_iterate_verschiebungInt (Φ : MvFormalGroup d R) [Φ.IsComm] (m : ℕ) (w : WittVector p R)
    (x : CartierModule p Φ) :
    w • (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] x =
      (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] (((⇑(WittVector.frobenius (p := p) (R := R)))^[m] w) • x) := by
  induction m generalizing w x with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', smul_verschiebungInt, ih, Function.iterate_succ_apply]
    exact (Function.iterate_succ_apply' (⇑(verschiebungInt (p := p) (Φ := Φ))) m _).symm

end Generic
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_and_hasStructureConstants_liftVar.P2mLawPresWx"

def wt (θ : WittVector p (U p)) (m : ℕ) (i l : Fin 2) : WittVector p (U p) :=
  if l = FormalODModule.piIndex m i then
    ((⇑(WittVector.frobenius (p := p) (R := U p)))^[m] θ) * dW p m i else 0

theorem frobenius_expansion_of_rel (Φ : MvFormalGroup 2 (U p)) [Φ.IsComm]
    (η θ : WittVector p (U p))
    (hη : ((p : ℕ) : WittVector p (U p)) = WittVector.teichmuller p (p : U p) + WittVector.verschiebung η)
    (hθ : θ * η = 1)
    (t : Fin 2 → CartierModule p Φ)
    (hrel : ∀ (N : ℕ) (i : Fin 2), ∃ s : CartierModule p Φ,
      p • t i = WittVector.teichmuller p (p : U p) • t i +
        (∑ k ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[k + 1]
          (dW p k i • t (FormalODModule.piIndex k i))) +
        (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N + 1] s) :
    ∃ h' : ℕ → Fin 2 → CartierModule p Φ, ∀ (N : ℕ) (i : Fin 2), frobenius (t i) =
      (∑ m ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m]
        (∑ l : Fin 2, wt p θ m i l • t l)) +
      (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] (h' N i) := by
  classical
  have hVinj := MvFormalGroup.CartierModule.verschiebungInt_injective_of_algebra_padicInt p Φ
  choose s hs using hrel
  refine ⟨fun N i => ((⇑(WittVector.frobenius (p := p) (R := U p)))^[N] θ) • s N i, fun N i => ?_⟩

  have h1 : WittVector.verschiebung η • t i =
      (∑ k ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[k + 1]
          (dW p k i • t (FormalODModule.piIndex k i))) +
        (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N + 1] (s N i) := by
    have := hs N i
    rw [← Nat.cast_smul_eq_nsmul (WittVector p (U p)), hη, add_smul, add_assoc] at this
    exact add_left_cancel this
  have h2 : verschiebungInt (η • frobenius (t i)) =
      verschiebungInt ((∑ k ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[k]
          (dW p k i • t (FormalODModule.piIndex k i))) +
        (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] (s N i)) := by
    rw [← FFromPi.verschiebung_smul_eq, h1, map_add, map_sum]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => Function.iterate_succ_apply' _ _ _
    · exact Function.iterate_succ_apply' _ _ _
  have h3 := hVinj h2

  have h4 : frobenius (t i) = θ • (η • frobenius (t i)) := by rw [smul_smul, hθ, one_smul]
  rw [h4, h3, smul_add, Finset.smul_sum, smul_iterate_verschiebungInt]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [smul_iterate_verschiebungInt, smul_smul]
  congr 1
  simp only [wt]
  rw [Fintype.sum_eq_single (FormalODModule.piIndex m i) (fun x hx => by
      rw [if_neg hx]; exact zero_smul (WittVector p (U p)) (t x)),
    if_pos rfl]

end RealiseODUniv
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_and_hasStructureConstants_liftVar.P2mLawPresWx P2MW.S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_and_hasStructureConstants_liftVar.RealiseODUniv"

open RealiseODUniv

theorem solution (p : ℕ) [Fact p.Prime] :
    ∃ (X : CerednikDrinfeld.FormalODModule p
          (CerednikDrinfeld.CartierLift.LiftRing p (CerednikDrinfeld.Zp2 p) ((0, 0) : ℕ × Fin 2) (0, 1)))
      (γ : Fin 2 → MvFormalGroup.CartierModule p X.F),
      X.IsHomogeneousVBasis
          (algebraMap (CerednikDrinfeld.Zp2 p)
            (CerednikDrinfeld.CartierLift.LiftRing p (CerednikDrinfeld.Zp2 p) ((0, 0) : ℕ × Fin 2) (0, 1))) γ ∧
        X.HasStructureConstants γ
          (fun m i => CerednikDrinfeld.CartierLift.liftVar (p := p) (R := CerednikDrinfeld.Zp2 p)
            ((0, 0) : ℕ × Fin 2) (0, 1) (m, i)) := by
  classical

  obtain ⟨C, hCgr, hC⟩ :=
    CerednikDrinfeld.CartierLift.exists_digits_forall_smul_eq_teichmuller_smul_add_sum_verschiebungInt p

  obtain ⟨Φ₀, hΦ₀, f₀, hdet₀, hF₀⟩ :=
    MvFormalGroup.exists_cartierModule_vBasis_of_frobenius_expansion p (R := U p) 2 C

  have coord : ∃ (Φ : MvFormalGroup 2 (U p)) (_ : Φ.IsComm) (f : Fin 2 → CartierModule p Φ),
      (∀ i l, tangent (f i) l = if i = l then 1 else 0) ∧
      ∀ (i : Fin 2) (N : ℕ), ∃ h : CartierModule p Φ,
        frobenius (f i) =
          (∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[(m : ℕ)]
            (∑ k : Fin 2, homothety (C m i k) (f k))) +
          (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] h := by
    haveI := hΦ₀
    obtain ⟨Φ, hΦ, φ, ψ, -, -, hstd⟩ :=
      MvFormalGroup.exists_hom_comp_eq_id_tangent_map_eq_of_isUnit_det p Φ₀ f₀ hdet₀
    haveI := hΦ
    refine ⟨Φ, hΦ, fun i => CartierModule.map φ (f₀ i), hstd, fun i N => ?_⟩
    obtain ⟨h0, hh0⟩ := hF₀ i N
    refine ⟨CartierModule.map φ h0, ?_⟩
    rw [← map_frobenius, hh0, map_add, map_sum, map_iterate_verschiebungInt]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_iterate_verschiebungInt, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_homothety]
  obtain ⟨Φ, hΦ, f, hf, hF⟩ := coord

  have hexp : ∃ h : ℕ → Fin 2 → CartierModule p Φ, ∀ (N : ℕ) (i : Fin 2), frobenius (f i) =
      (∑ m ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin 2, homothety (C m i l) (f l))) +
        (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i) := by
    choose hh hhh using fun i N => hF i N
    refine ⟨fun N i => hh i N, fun N i => ?_⟩
    rw [hhh i N]
    congr 1
    exact Fin.sum_univ_eq_sum_range
      (fun m => (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] (∑ k : Fin 2, homothety (C m i k) (f k))) N
  obtain ⟨h, hexp⟩ := hexp

  have hrel := hC Φ f hf h hexp

  have hcompl := MvFormalGroup.CartierModule.existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add p Φ

  have hg : ∃ (g : Fin 2 → CartierModule p Φ) (r : ℕ → Fin 2 → CartierModule p Φ),
      ∀ (N : ℕ) (i : Fin 2), g i =
        (∑ m ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m]
          (homothety (Xv p m i) (f (FormalODModule.piIndex m i)))) +
        (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] (r N i) := by
    have hex : ∀ i : Fin 2, ∃ s : CartierModule p Φ, ∀ N : ℕ, ∃ t : CartierModule p Φ,
        s = (∑ m ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m]
              (homothety (Xv p m i) (f (FormalODModule.piIndex m i)))) +
            (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] t :=
      fun i => (hcompl fun m => homothety (Xv p m i) (f (FormalODModule.piIndex m i))).exists
    choose g hg0 using hex
    choose r hr using fun i N => hg0 i N
    exact ⟨g, fun N i => r i N, fun N i => hr i N⟩
  obtain ⟨g, r, hg⟩ := hg

  obtain ⟨hrel_g, hPg⟩ :=
    MvFormalGroup.CartierModule.varpiTuple_rel_and_sum_eq_of_rel p (fun m i => Xv p m i)
      (CartierLift.liftVar_mul_liftVar ((0, 0) : ℕ × Fin 2) (0, 1)) Φ f hrel g r hg

  have hW : ∃ (w : ℕ → Fin 2 → Fin 2 → WittVector p (U p))
      (hf' : ℕ → Fin 2 → CartierModule p Φ) (hg' : ℕ → Fin 2 → CartierModule p Φ),
      (∀ (N : ℕ) (i : Fin 2), frobenius (f i) =
        (∑ m ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] (∑ l : Fin 2, w m i l • f l)) +
          (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] (hf' N i)) ∧
      (∀ (N : ℕ) (i : Fin 2), frobenius (g i) =
        (∑ m ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m] (∑ l : Fin 2, w m i l • g l)) +
          (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] (hg' N i)) := by
    obtain ⟨η, θW, hη, hθW⟩ :=
      FFromPi.exists_natCast_eq_teichmuller_add_verschiebung_unit_map (p := p) (B := U p)
    obtain ⟨hf', hexpf⟩ := frobenius_expansion_of_rel p Φ η θW hη hθW f hrel
    obtain ⟨hg', hexpg⟩ := frobenius_expansion_of_rel p Φ η θW hη hθW g hrel_g
    exact ⟨wt p θW, hf', hg', hexpf, hexpg⟩
  obtain ⟨w, hf', hg', hexpWf, hexpWg⟩ := hW

  obtain ⟨ϖ, hϖ⟩ :=
    MvFormalGroup.CartierModule.exists_hom_forall_map_eq_of_forall_frobenius_eq_sum_verschiebungInt_iterate_smul
      p Φ Φ f hf w hf' hexpWf g hg' hexpWg

  obtain ⟨θ, act, hact, hθghost, hθteich, hact1, hactmul, hactadd, hactf⟩ :=
    MvFormalGroup.CartierModule.exists_zp2Action_of_graded_frobenius_expansion
      p (algebraMap (Zp2 p) (U p)) Φ f hf C hCgr h hexp

  have hσnat : ∀ n : ℕ, (⇑(WittVector.frobenius (p := p) (R := GaloisField p 2)))^[n] (p : Zp2 p) = p := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, map_natCast]
  have hactp : ∀ i : Fin 2, CartierModule.map (hact (p : Zp2 p)).toHom (f i) = p • f i := by
    intro i
    rw [hactf, hσnat, map_natCast, map_natCast, Nat.cast_smul_eq_nsmul]
  have hϖg : ∀ i : Fin 2, CartierModule.map ϖ (g i) = p • f i := by
    intro i
    have hL : ∀ N : ℕ, ∃ t : CartierModule p Φ,
        CartierModule.map ϖ (g i) - p • f i = (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] t := by
      intro N
      obtain ⟨s, hs⟩ := hPg N i
      refine ⟨CartierModule.map ϖ (r N i) - s, ?_⟩
      have e1 : CartierModule.map ϖ (g i) =
          (∑ m ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m]
            (homothety (Xv p m i) (g (FormalODModule.piIndex m i)))) +
          (⇑(verschiebungInt (p := p) (Φ := Φ)))^[N] (CartierModule.map ϖ (r N i)) := by
        conv_lhs => rw [hg N i]
        rw [map_add, map_sum, map_iterate_verschiebungInt]
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [map_iterate_verschiebungInt, map_homothety, hϖ]
      rw [e1, ← hs, add_sub_add_left_eq_sub, iterate_verschiebungInt_sub]
    exact sub_eq_zero.1 (eq_zero_of_forall_exists_iterate (p := p) Φ _ hL)
  have hPiPi : (ϖ.comp ϖ) = (hact (p : Zp2 p)).toHom :=
    P2mLawPresWx.hom_eq_of_map_basis_eq (p := p) f hf _ _ fun i => by
      rw [CartierModule.map_comp, hϖ i, hϖg i, hactp i]

  have hpZ : ((p : ℕ) : Zp2 p) ∈ nonZeroDivisors (Zp2 p) := by
    rw [mem_nonZeroDivisors_iff]
    exact ⟨fun x hx => CartierLift.zp2_natCast_mul_eq_zero x hx,
      fun x hx => CartierLift.zp2_natCast_mul_eq_zero x (by rwa [mul_comm] at hx)⟩
  have hσσ : ∀ b : Zp2 p, WittVector.frobenius (WittVector.frobenius b) = b := by
    haveI : Fintype (GaloisField p 2) := Fintype.ofFinite _
    intro b
    refine WittVector.ext fun n => ?_
    rw [WittVector.coeff_frobenius_charP, WittVector.coeff_frobenius_charP, ← pow_mul, ← pow_two,
      ← GaloisField.card p 2 two_ne_zero, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hσpar : ∀ (n : ℕ) (b : Zp2 p),
      (⇑(WittVector.frobenius (p := p) (R := GaloisField p 2)))^[n] b =
        (⇑(WittVector.frobenius (p := p) (R := GaloisField p 2)))^[n % 2] b := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro b
      rcases Nat.lt_or_ge n 2 with hn | hn
      · rw [Nat.mod_eq_of_lt hn]
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
        rw [show 2 + k = k + 1 + 1 from by omega, Function.iterate_succ_apply',
          Function.iterate_succ_apply', hσσ, ih k (by omega), show (k + 1 + 1) % 2 = k % 2 from by omega]
  have hθσ : ∀ b : Zp2 p, θ (WittVector.frobenius b) = WittVector.frobenius (θ b) := by
    intro b
    refine WittVector.ext fun n => ?_
    refine WittVector.coeff_eq_coeff_of_forall_ghostComponent_eq p hpZ (n + 1) _ _ (fun k _ => ?_) n
      (Nat.lt_succ_self n)
    rw [hθghost, WittVector.ghostComponent_frobenius, hθghost, ← Function.iterate_succ_apply,
      Function.iterate_succ_apply']
  have hθσit : ∀ (m : ℕ) (b : Zp2 p),
      θ ((⇑(WittVector.frobenius (p := p) (R := GaloisField p 2)))^[m] b) =
        (⇑(WittVector.frobenius (p := p) (R := Zp2 p)))^[m] (θ b) := by
    intro m
    induction m with
    | zero => intro b; rfl
    | succ m ih => intro b; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hθσ, ih]
  have hmapσit : ∀ (m : ℕ) (w : WittVector p (Zp2 p)),
      (⇑(WittVector.frobenius (p := p) (R := U p)))^[m] (WittVector.map (algebraMap (Zp2 p) (U p)) w) =
        WittVector.map (algebraMap (Zp2 p) (U p)) ((⇑(WittVector.frobenius (p := p) (R := Zp2 p)))^[m] w) := by
    intro m
    induction m with
    | zero => intro w; rfl
    | succ m ih =>
      intro w
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
        (WittVector.frobenius_isPoly p).map]
  have hPiAct : ∀ a : Zp2 p,
      ϖ.comp (hact a).toHom = (hact (WittVector.frobenius a)).toHom.comp ϖ := by
    intro a
    refine P2mLawPresWx.hom_eq_of_map_basis_eq (p := p) f hf _ _ fun i => ?_
    rw [CartierModule.map_comp, CartierModule.map_comp, hactf, map_smul_witt, hϖ i]

    apply eq_of_sub_eq_zero
    apply eq_zero_of_forall_exists_iterate (p := p) Φ
    intro N

    have hcoef : ∀ m : ℕ,
        (⇑(WittVector.frobenius (p := p) (R := U p)))^[m]
            (WittVector.map (algebraMap (Zp2 p) (U p))
              (θ ((⇑(WittVector.frobenius (p := p) (R := GaloisField p 2)))^[(i : ℕ)] a))) =
          WittVector.map (algebraMap (Zp2 p) (U p))
            (θ ((⇑(WittVector.frobenius (p := p) (R := GaloisField p 2)))^[((FormalODModule.piIndex m i : Fin 2) : ℕ)]
              (WittVector.frobenius a))) := by
      intro m
      have hmod : (m + (i : ℕ)) % 2 = (((FormalODModule.piIndex m i : Fin 2) : ℕ) + 1) % 2 := by
        rw [FormalODModule.piIndex_val]; omega
      rw [hmapσit, ← hθσit, ← Function.iterate_add_apply, ← Function.iterate_succ_apply,
        hσpar (m + (i : ℕ)), hσpar (((FormalODModule.piIndex m i : Fin 2) : ℕ) + 1), hmod]
    refine ⟨((⇑(WittVector.frobenius (p := p) (R := U p)))^[N]
        (WittVector.map (algebraMap (Zp2 p) (U p))
          (θ ((⇑(WittVector.frobenius (p := p) (R := GaloisField p 2)))^[(i : ℕ)] a)))) • r N i -
        CartierModule.map (hact (WittVector.frobenius a)).toHom (r N i), ?_⟩
    have hS : (WittVector.map (algebraMap (Zp2 p) (U p))
          (θ ((⇑(WittVector.frobenius (p := p) (R := GaloisField p 2)))^[(i : ℕ)] a))) •
        (∑ m ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m]
          (homothety (Xv p m i) (f (FormalODModule.piIndex m i)))) =
        CartierModule.map (hact (WittVector.frobenius a)).toHom
        (∑ m ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m]
          (homothety (Xv p m i) (f (FormalODModule.piIndex m i)))) := by
      rw [Finset.smul_sum, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [smul_iterate_verschiebungInt, map_iterate_verschiebungInt, ← homothety_smul_witt, hcoef m,
        map_homothety, hactf]
    conv_lhs => rw [hg N i]
    rw [smul_add, map_add, hS, add_sub_add_left_eq_sub, smul_iterate_verschiebungInt,
      map_iterate_verschiebungInt, iterate_verschiebungInt_sub]

  let XU : FormalODModule p (U p) :=
    { F := Φ
      isComm := hΦ
      act := act
      varpi := ϖ.toPowerSeries
      isLawHom_act := hact
      isLawHom_varpi := IsLawHom.of_hom ϖ
      act_one := hact1
      act_mul := hactmul
      act_add := hactadd
      varpi_comp_varpi := by
        have := congrArg MvFormalGroup.Hom.toPowerSeries hPiPi
        exact this
      varpi_comp_act := by
        intro a
        have := congrArg MvFormalGroup.Hom.toPowerSeries (hPiAct a)
        exact this }
  refine ⟨XU, f, ⟨?_, ?_⟩, ?_⟩
  ·
    have hft : ∀ (n : ℕ) (c : GaloisField p 2),
        (⇑(WittVector.frobenius (p := p) (R := GaloisField p 2)))^[n] (WittVector.teichmuller p c) =
          WittVector.teichmuller p (c ^ p ^ n) := by
      intro n
      induction n with
      | zero => intro c; simp
      | succ n ih =>
        intro c
        rw [Function.iterate_succ_apply', ih, WittVector.frobenius_eq_map_frobenius,
          WittVector.map_teichmuller, frobenius_def, ← pow_mul, ← pow_succ]
    intro i c
    have h1 : endAct (XU.actEnd (WittVector.teichmuller p c)) (f i) =
        CartierModule.map (hact (WittVector.teichmuller p c)).toHom (f i) := by
      rw [endAct_apply]
      rfl
    rw [h1, hactf, hft, hθteich, WittVector.map_teichmuller, teichmuller_smul, ← map_pow,
      ← map_pow]
  ·
    have hM : (Matrix.of fun i k => tangent (f i) k) = (1 : Matrix (Fin 2) (Fin 2) (U p)) := by
      ext i k
      rw [Matrix.of_apply, hf i k, Matrix.one_apply]
    rw [hM, Matrix.det_one]
    exact isUnit_one
  ·
    intro i N
    refine ⟨r N i, ?_⟩
    have h1 : endAct XU.varpiEnd (f i) = CartierModule.map ϖ (f i) := by
      rw [endAct_apply]
      rfl
    rw [h1, hϖ i, hg N i]
    congr 1
    exact (Fin.sum_univ_eq_sum_range
      (fun m => (⇑(verschiebungInt (p := p) (Φ := Φ)))^[m]
        (homothety (Xv p m i) (f (FormalODModule.piIndex m i)))) N).symm

end
end S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_and_hasStructureConstants_liftVar
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_and_hasStructureConstants_liftVar (solution)
