-- Prove2me | solution 1 for CerednikDrinfeld.QM.exists_injective_range_isTangentVector_of_isFormalCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/99fbf862-db88-5f91-a840-9611b1c19715

import Mathlib
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_exists_injective_range_isTangentVector_of_isFormalCoordinates

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_exists_injective_range_isTangentVector_of_isFormalCoordinates.CerednikDrinfeld.QM"

noncomputable section

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "tree"
namespace QM
p2m_export "CerednikDrinfeld.QM" "geomPoint tangentBase tangentZero tangentScale IsTangentVector"
namespace TangentChart
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

section Law

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

theorem eq_one_of_mul_self {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t f)
    (hx : L.mul t x x = x) : x = L.one t := by
  calc x = L.mul t (L.one t) x := (L.one_mul t x).symm
    _ = L.mul t (L.mul t (L.inv t x) x) x := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t x) (L.mul t x x) := by rw [L.mul_assoc]
    _ = L.mul t (L.inv t x) x := by rw [hx]
    _ = L.one t := L.inv_mul_cancel t x

theorem schemeHomOverComp_one {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T' ⟶ Spec (CommRingCat.of S)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    schemeHomOverComp ψ hψ (L.one t) = L.one t' :=
  eq_one_of_mul_self L t' _ (by rw [← L.mul_natural, L.mul_one])

end Law

section Poly

variable {B : Type} [CommRing B] {C : Type} [CommRing C] [Algebra B C] {σ : Type} [Fintype σ] [DecidableEq σ]

theorem prod_pow_eq_zero_of_mul_eq_zero (a : σ → C) (ha : ∀ x y, a x * a y = 0) (u : σ →₀ ℕ) (hu0 : u ≠ 0)
    (hu1 : ∀ x, u ≠ Finsupp.single x 1) : (u.prod fun i e => a i ^ e) = 0 := by
  classical
  obtain ⟨x, hx⟩ : ∃ x, u x ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (Finsupp.ext fun s => by simpa using h s)
  have hxs : x ∈ u.support := Finsupp.mem_support_iff.mpr hx
  rw [Finsupp.prod, ← Finset.mul_prod_erase _ _ hxs]
  by_cases h2 : 2 ≤ u x
  ·
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h2
    rw [hm, pow_add, pow_two, ha x x, zero_mul, zero_mul]
  ·
    have hux : u x = 1 := by omega
    obtain ⟨y, hyx, hy⟩ : ∃ y, y ≠ x ∧ u y ≠ 0 := by
      by_contra h
      push Not at h
      apply hu1 x
      ext s
      by_cases hs : s = x
      · subst hs; rw [hux, Finsupp.single_eq_same]
      · rw [h s hs, Finsupp.single_eq_of_ne hs]
    have hys : y ∈ u.support.erase x := Finset.mem_erase.mpr ⟨hyx, Finsupp.mem_support_iff.mpr hy⟩
    rw [← Finset.mul_prod_erase _ _ hys, hux, pow_one]
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hy
    set rest := ∏ z ∈ (u.support.erase x).erase y, a z ^ u z
    rw [hm, pow_succ]
    calc a x * (a y ^ m * a y * rest) = (a x * a y) * (a y ^ m * rest) := by ring
      _ = 0 := by rw [ha x y, zero_mul]

theorem aeval_eq_of_mul_eq_zero (a : σ → C) (ha : ∀ x y, a x * a y = 0) (p : MvPolynomial σ B) :
    MvPolynomial.aeval a p = algebraMap B C (p.coeff 0) + ∑ x, p.coeff (Finsupp.single x 1) • a x := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [MvPolynomial.aeval_monomial]
    simp only [MvPolynomial.coeff_monomial]
    by_cases hu0 : u = 0
    · subst hu0
      have hne : ∀ x : σ, ¬ ((0 : σ →₀ ℕ) = Finsupp.single x 1) := fun x h =>
        one_ne_zero ((Finsupp.single_eq_zero.mp h.symm))
      simp [hne]
    · rw [if_neg hu0, map_zero, zero_add]
      by_cases hu1 : ∃ x, u = Finsupp.single x 1
      · obtain ⟨x, rfl⟩ := hu1
        rw [Finset.sum_eq_single x]
        · rw [if_pos rfl, Finsupp.prod_single_index (h := fun i e => a i ^ e) (pow_zero _), pow_one,
            Algebra.smul_def]
        · intro y _ hyx
          rw [if_neg (fun h => hyx ((Finsupp.single_left_injective one_ne_zero h).symm)), zero_smul]
        · intro h; exact absurd (Finset.mem_univ x) h
      · push Not at hu1
        rw [prod_pow_eq_zero_of_mul_eq_zero a ha u hu0 hu1, mul_zero]
        symm
        refine Finset.sum_eq_zero fun x _ => ?_
        rw [if_neg (hu1 x), zero_smul]
  | add p q hp hq =>
    rw [map_add, hp, hq, MvPolynomial.coeff_add, map_add]
    simp only [MvPolynomial.coeff_add, add_smul, Finset.sum_add_distrib]
    abel

theorem nilMul_one_eq_add {g : ℕ} (F : MvFormalGroup g B) (s t : Fin g → C)
    (h : ∀ x y, Sum.elim s t x * Sum.elim s t y = 0) : F.nilMul 1 s t = s + t := by
  classical
  funext i
  show MvPolynomial.aeval (Sum.elim s t)
      (MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ => 1) (F.toPowerSeries i)) = s i + t i
  rw [aeval_eq_of_mul_eq_zero _ h]
  have h0 : (MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ : Fin g ⊕ Fin g => 1)
      (F.toPowerSeries i)).coeff 0 = 0 := by
    rw [MvPowerSeries.coeff_trunc', if_pos (Finsupp.le_def.2 fun _ => Nat.zero_le _),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, F.constantCoeff_eq_zero i]
  have h1 : ∀ x : Fin g ⊕ Fin g,
      (MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ : Fin g ⊕ Fin g => 1)
        (F.toPowerSeries i)).coeff (Finsupp.single x 1) =
        MvPowerSeries.coeff (Finsupp.single x 1) (F.toPowerSeries i) := by
    intro x
    rw [MvPowerSeries.coeff_trunc', if_pos]
    rw [Finsupp.le_def]
    intro y
    show Finsupp.single x 1 y ≤ 1
    by_cases hxy : x = y
    · subst hxy; rw [Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne (Ne.symm hxy)]; exact Nat.zero_le _
  rw [h0, map_zero, zero_add]
  simp only [h1, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, F.coeff_single_inl, F.coeff_single_inr,
    ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end Poly

section Dual

variable {B : Type} [CommRing B] (k : Type) [Field k] [Algebra B k]

def aug : DualNumber k →ₐ[B] k := (TrivSqZeroExt.fstHom k k k).restrictScalars B

theorem aug_apply (x : DualNumber k) : aug (B := B) k x = x.fst := rfl

theorem aug_surjective : Function.Surjective (aug (B := B) k) := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩

def J : Ideal (DualNumber k) := RingHom.ker (aug (B := B) k).toRingHom

theorem mem_J_iff (x : DualNumber k) : x ∈ J (B := B) k ↔ x.fst = 0 := Iff.rfl

theorem inr_mem_J (m : k) : (TrivSqZeroExt.inr m : DualNumber k) ∈ J (B := B) k := by
  rw [mem_J_iff]; rfl

theorem eq_inr_of_mem_J {x : DualNumber k} (hx : x ∈ J (B := B) k) : x = TrivSqZeroExt.inr x.snd := by
  rw [mem_J_iff] at hx
  ext <;> simp [hx]

theorem mul_eq_zero_of_mem_J {x y : DualNumber k} (hx : x ∈ J (B := B) k) (hy : y ∈ J (B := B) k) : x * y = 0 := by
  rw [eq_inr_of_mem_J k hx, eq_inr_of_mem_J k hy, TrivSqZeroExt.inr_mul_inr]

theorem J_sq : J (B := B) k ^ (1 + 1) = ⊥ := by
  rw [one_add_one_eq_two, pow_two, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  rw [mul_eq_zero_of_mem_J k hx hy]
  exact Submodule.zero_mem _

def quotJ : (DualNumber k ⧸ J (B := B) k) ≃ₐ[B] k :=
  Ideal.quotientKerAlgEquivOfSurjective (aug_surjective k)

def qJc : CommRingCat.of (DualNumber k ⧸ J (B := B) k) ⟶ CommRingCat.of k :=
  CommRingCat.ofHom (quotJ (B := B) k).toAlgHom.toRingHom

def mkc : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of (DualNumber k ⧸ J (B := B) k) :=
  CommRingCat.ofHom (Ideal.Quotient.mk (J (B := B) k))

def augc : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k :=
  CommRingCat.ofHom (aug (B := B) k).toRingHom

def algc : CommRingCat.of B ⟶ CommRingCat.of (DualNumber k ⧸ J (B := B) k) :=
  CommRingCat.ofHom (algebraMap B (DualNumber k ⧸ J (B := B) k))

theorem specOver_quot_eq : Scheme.specOver (𝒪 := B) (DualNumber k ⧸ J (B := B) k) = Spec.map (algc (B := B) k) :=
  rfl

theorem specMap_qJc_comp_specOver :
    Spec.map (qJc (B := B) k) ≫ Scheme.specOver (𝒪 := B) (DualNumber k ⧸ J (B := B) k) =
      Scheme.specOver (𝒪 := B) k := by
  show Spec.map (qJc (B := B) k) ≫ Spec.map (algc (B := B) k) = Spec.map (CommRingCat.ofHom (algebraMap B k))
  rw [← Spec.map_comp]
  congr 1

scoped instance isIso_specMap_qJc : IsIso (Spec.map (qJc (B := B) k)) := by
  have h : qJc (B := B) k = (quotJ (B := B) k).toRingEquiv.toCommRingCatIso.hom := by
    rw [RingEquiv.toCommRingCatIso_hom]; rfl
  rw [h]
  infer_instance

theorem specMap_augc : Spec.map (augc (B := B) k) = Spec.map (qJc (B := B) k) ≫ Spec.map (mkc (B := B) k) := by
  rw [← Spec.map_comp]
  congr 1

theorem tangentZero_eq : tangentZero k = Spec.map (augc (B := B) k) := rfl

theorem geomPoint_eq : geomPoint k (algebraMap B k) = Scheme.specOver (𝒪 := B) k := rfl

def scale (c : k) : DualNumber k →ₐ[B] DualNumber k :=
  (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).restrictScalars B

theorem scale_inr (c m : k) : scale (B := B) k c (TrivSqZeroExt.inr m) = TrivSqZeroExt.inr (c * m) := by
  show TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k)) (TrivSqZeroExt.inr m) = _
  rw [TrivSqZeroExt.map_inr]
  rfl

theorem tangentScale_eq (c : k) : tangentScale k c = Spec.map (CommRingCat.ofHom (scale (B := B) k c).toRingHom) := rfl

end Dual

section Main

variable {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} {g : ℕ}

theorem isInfinitesimal_iff_isTangentVector (L : RelativeGroupLaw B f) (k : Type) [Field k] [Algebra B k]
    (P : SchemeHomOver (Scheme.specOver (𝒪 := B) (DualNumber k)) f) :
    L.IsInfinitesimal (J (B := B) k) P ↔ IsTangentVector L k (algebraMap B k) P := by
  have hone : (L.one (Scheme.specOver (𝒪 := B) k)).1 =
      Spec.map (qJc (B := B) k) ≫ (L.one (Scheme.specOver (𝒪 := B) (DualNumber k ⧸ J (B := B) k))).1 :=
    (congrArg Subtype.val (schemeHomOverComp_one L _ _ (Spec.map (qJc (B := B) k))
      (specMap_qJc_comp_specOver k))).symm
  have e1 : L.IsInfinitesimal (J (B := B) k) P ↔
      Spec.map (mkc (B := B) k) ≫ P.1 = (L.one (Scheme.specOver (𝒪 := B) (DualNumber k ⧸ J (B := B) k))).1 := by
    unfold RelativeGroupLaw.IsInfinitesimal
    rw [Subtype.ext_iff, schemeHomOverComp_coe]
    exact Iff.rfl
  have e2 : IsTangentVector L k (algebraMap B k) P ↔
      Spec.map (qJc (B := B) k) ≫ (Spec.map (mkc (B := B) k) ≫ P.1) =
        Spec.map (qJc (B := B) k) ≫ (L.one (Scheme.specOver (𝒪 := B) (DualNumber k ⧸ J (B := B) k))).1 := by
    unfold IsTangentVector
    rw [tangentZero_eq (B := B) k, specMap_augc k, Category.assoc, geomPoint_eq, hone]
  rw [e1, e2]
  constructor
  · intro h
    rw [h]
  · intro h
    exact (cancel_epi _).mp h

theorem main (L : RelativeGroupLaw B f) (F : MvFormalGroup g B) (θ : RelativeGroupLaw.FormalCoordinates f g)
    (hθ : L.IsFormalCoordinates F θ) (k : Type) [Field k] [Algebra B k] :
    ∃ τ : (Fin g → k) → SchemeHomOver (tangentBase k (algebraMap B k)) f,
      (∀ v, (τ v).1 = (θ (DualNumber k) (fun i => TrivSqZeroExt.inr (v i))).1) ∧
      Function.Injective τ ∧
      (∀ P, P ∈ Set.range τ ↔ IsTangentVector L k (algebraMap B k) P) ∧
      (∀ v w, τ (v + w) = L.mul (tangentBase k (algebraMap B k)) (τ v) (τ w)) ∧
      (∀ (c : k) (v : Fin g → k), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) := by
  classical
  let ev : (Fin g → k) → (Fin g → DualNumber k) := fun v i => TrivSqZeroExt.inr (v i)
  have hev_mem : ∀ v i, ev v i ∈ J (B := B) k := fun v i => inr_mem_J k (v i)
  have hev_inj : Function.Injective ev := by
    intro v w h
    funext i
    have := congrFun h i
    simpa [ev] using congrArg TrivSqZeroExt.snd this

  obtain ⟨hinto, hinj, honto, hhom⟩ := hθ.2 (DualNumber k) (J (B := B) k) 1 (J_sq k)
  let τ : (Fin g → k) → SchemeHomOver (tangentBase k (algebraMap B k)) f := fun v => θ (DualNumber k) (ev v)
  refine ⟨τ, fun v => rfl, ?_, ?_, ?_, ?_⟩
  ·
    intro v w h
    exact hev_inj (hinj _ _ (hev_mem v) (hev_mem w) h)
  ·
    intro P
    constructor
    · rintro ⟨v, rfl⟩
      exact (isInfinitesimal_iff_isTangentVector L k _).mp (hinto _ (hev_mem v))
    · intro hP
      obtain ⟨s, hs, hsP⟩ := honto P ((isInfinitesimal_iff_isTangentVector L k P).mpr hP)
      refine ⟨fun i => (s i).snd, ?_⟩
      show θ (DualNumber k) (fun i => TrivSqZeroExt.inr (s i).snd) = P
      have hs' : (fun i => TrivSqZeroExt.inr (s i).snd) = s := funext fun i => (eq_inr_of_mem_J k (hs i)).symm
      rw [hs', hsP]
  ·
    intro v w
    have hprod : ∀ x y, Sum.elim (ev v) (ev w) x * Sum.elim (ev v) (ev w) y = 0 := by
      have hmem : ∀ x, Sum.elim (ev v) (ev w) x ∈ J (B := B) k := by
        rintro (x | x)
        exacts [hev_mem v x, hev_mem w x]
      exact fun x y => mul_eq_zero_of_mem_J k (hmem x) (hmem y)
    have hsum : F.nilMul 1 (ev v) (ev w) = ev (v + w) := by
      rw [nilMul_one_eq_add F _ _ hprod]
      funext i
      show (TrivSqZeroExt.inr (v i) : DualNumber k) + TrivSqZeroExt.inr (w i) = TrivSqZeroExt.inr (v i + w i)
      exact (TrivSqZeroExt.inr_add k (v i) (w i)).symm
    show θ (DualNumber k) (ev (v + w)) = L.mul _ (θ (DualNumber k) (ev v)) (θ (DualNumber k) (ev w))
    rw [← hsum]
    exact hhom _ _ (hev_mem v) (hev_mem w)
  ·
    intro c v
    have hnil : ∀ i, IsNilpotent (ev v i) := fun i =>
      ⟨2, by rw [pow_two]; exact mul_eq_zero_of_mem_J k (hev_mem v i) (hev_mem v i)⟩
    have hcomp : (scale (B := B) k c) ∘ ev v = ev (c • v) := by
      funext i
      show scale (B := B) k c (TrivSqZeroExt.inr (v i)) = TrivSqZeroExt.inr ((c • v) i)
      rw [scale_inr, Pi.smul_apply, smul_eq_mul]
    show (θ (DualNumber k) (ev (c • v))).1 = tangentScale k c ≫ (θ (DualNumber k) (ev v)).1
    rw [← hcomp, hθ.1 (DualNumber k) (DualNumber k) (scale (B := B) k c) (ev v) hnil, schemeHomOverComp_coe,
      tangentScale_eq (B := B) k]

end Main

end CerednikDrinfeld.QM.TangentChart
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_injective_range_isTangentVector_of_isFormalCoordinates.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_exists_injective_range_isTangentVector_of_isFormalCoordinates.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_exists_injective_range_isTangentVector_of_isFormalCoordinates.CerednikDrinfeld.QM.TangentChart"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_injective_range_isTangentVector_of_isFormalCoordinates.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_exists_injective_range_isTangentVector_of_isFormalCoordinates.CerednikDrinfeld.QM"
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_injective_range_isTangentVector_of_isFormalCoordinates.CerednikDrinfeld"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_exists_injective_range_isTangentVector_of_isFormalCoordinates.CerednikDrinfeld P2MW.S_CerednikDrinfeld_QM_exists_injective_range_isTangentVector_of_isFormalCoordinates.CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_exists_injective_range_isTangentVector_of_isFormalCoordinates.CerednikDrinfeld.QM.TangentChart"

theorem solution
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} {g : ℕ}
    (L : RelativeGroupLaw B f) (F : MvFormalGroup g B) (θ : RelativeGroupLaw.FormalCoordinates f g)
    (hθ : L.IsFormalCoordinates F θ) (k : Type) [Field k] [Algebra B k] :
    ∃ τ : (Fin g → k) → SchemeHomOver (tangentBase k (algebraMap B k)) f,
      (∀ v, (τ v).1 = (θ (DualNumber k) (fun i => TrivSqZeroExt.inr (v i))).1) ∧
      Function.Injective τ ∧
      (∀ P, P ∈ Set.range τ ↔ IsTangentVector L k (algebraMap B k) P) ∧
      (∀ v w, τ (v + w) = L.mul (tangentBase k (algebraMap B k)) (τ v) (τ w)) ∧
      (∀ (c : k) (v : Fin g → k), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) :=
  CerednikDrinfeld.QM.TangentChart.main L F θ hθ k

end S_CerednikDrinfeld_QM_exists_injective_range_isTangentVector_of_isFormalCoordinates
end P2MW
export P2MW.S_CerednikDrinfeld_QM_exists_injective_range_isTangentVector_of_isFormalCoordinates (solution)
