-- Prove2me | solution 1 for CerednikDrinfeld.QM.trace_eq_of_smooth_of_isCommutative_of_forall_injective_trace_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/7fc1a3c9-c99d-52dd-b0ab-bc0899a1dfe7

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_mvFormalGroup_kernelOfReduction_of_smooth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_trace_eq_of_smooth_of_isCommutative_of_forall_injective_trace_eq

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM
open MvPowerSeries
open scoped Quaternion

universe u

noncomputable section

namespace TraceClosedBody

section NilEval

variable {R : Type u} [CommRing R] {C : Type u} [CommRing C] [Algebra R C]

theorem isAdicComplete_of_isNilpotent (J : Ideal C) (hJ : IsNilpotent J) : IsAdicComplete J C := by
  obtain ⟨n, hn⟩ := hJ
  haveI : IsHausdorff J C := ⟨fun x hx => by
    have := hx n
    rw [hn] at this
    simpa [SModEq.zero] using this⟩
  haveI : IsPrecomplete J C := ⟨fun {f} hf => ⟨f n, fun m => by
    by_cases hm : m ≤ n
    · exact hf hm
    · push Not at hm
      have h1 : f n ≡ f m [SMOD (J ^ n • ⊤ : Submodule C C)] := hf hm.le
      have h2 : (J ^ m • ⊤ : Submodule C C) = ⊥ := by
        rw [show m = n + (m - n) by omega, pow_add, hn, zero_mul]; simp
      have h3 : (J ^ n • ⊤ : Submodule C C) = ⊥ := by rw [hn]; simp
      rw [h2]; rw [h3] at h1
      exact h1.symm⟩⟩
  exact ⟨⟩

theorem prod_pow_eq_zero_of_le_degree {σ : Type} (J₀ : Ideal C) {N : ℕ} (hN : J₀ ^ N = ⊥) {x : σ → C}
    (hx : ∀ s, x s ∈ J₀) (d : σ →₀ ℕ) (hd : N ≤ d.degree) :
    (d.prod fun s e => x s ^ e) = 0 := by
  have hmem : (d.prod fun s e => x s ^ e) ∈ J₀ ^ d.degree := by
    rw [Finsupp.prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun s _ => Ideal.pow_mem_pow (hx s) _
  have hle : J₀ ^ d.degree ≤ J₀ ^ N := Ideal.pow_le_pow_right hd
  have := hle hmem
  rwa [hN, Submodule.mem_bot] at this

theorem adicEval_eq_sum {σ : Type} [Finite σ] (J : Ideal C) {N : ℕ} (hN : J ^ N = ⊥)
    {x : σ → C} (hx : ∀ s, x s ∈ J) (f : MvPowerSeries σ R) (D : Finset (σ →₀ ℕ))
    (hD : ∀ d, d ∉ D → N ≤ d.degree) :
    MvFormalGroup.adicEval J x f = ∑ d ∈ D, algebraMap R C (coeff d f) * d.prod fun s e => x s ^ e := by
  letI : UniformSpace R := ⊥
  letI : WithIdeal C := ⟨J⟩
  haveI hc : IsAdicComplete J C := isAdicComplete_of_isNilpotent J ⟨N, hN⟩
  haveI : CompleteSpace C := ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp hc).1
  haveI : T2Space C := ((IsAdic.isAdicComplete_iff (show IsAdic J from rfl)).mp hc).2
  have hφ : Continuous (algebraMap R C) := continuous_of_discreteTopology
  have ha : MvPowerSeries.HasEval x := by
    refine ⟨fun s => ?_, ?_⟩
    · apply tendsto_atTop_of_eventually_const (i₀ := N)
      intro n hn
      have h0 : x s ^ n = 0 := by
        have hmem : x s ^ n ∈ J ^ n := Ideal.pow_mem_pow (hx s) n
        have := (Ideal.pow_le_pow_right hn) hmem
        rwa [hN, Submodule.mem_bot] at this
      exact h0
    · rw [Filter.cofinite_eq_bot]
      exact Filter.tendsto_bot
  have h1 := MvPowerSeries.hasSum_eval₂ hφ ha f
  have h2 : HasSum (fun d : σ →₀ ℕ => algebraMap R C (coeff d f) * d.prod fun s e => x s ^ e)
      (∑ d ∈ D, algebraMap R C (coeff d f) * d.prod fun s e => x s ^ e) := by
    apply hasSum_sum_of_ne_finset_zero
    intro d hd'
    rw [prod_pow_eq_zero_of_le_degree J hN hx d (hD d hd'), mul_zero]
  exact h1.unique h2

theorem prod_pow_eq_zero_of_mul_eq_zero {σ : Type} [DecidableEq σ] (a : σ → C) (ha : ∀ x y, a x * a y = 0)
    (u : σ →₀ ℕ) (hu0 : u ≠ 0) (hu1 : ∀ x, u ≠ Finsupp.single x 1) : (u.prod fun i e => a i ^ e) = 0 := by
  classical
  obtain ⟨x, hx⟩ : ∃ x, u x ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (Finsupp.ext fun s => by simpa using h s)
  have hxs : x ∈ u.support := Finsupp.mem_support_iff.mpr hx
  rw [Finsupp.prod, ← Finset.mul_prod_erase _ _ hxs]
  by_cases h2 : 2 ≤ u x
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h2
    rw [hm, pow_add, pow_two, ha x x, zero_mul, zero_mul]
  · have hux : u x = 1 := by omega
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

theorem adicEval_sqZero {σ : Type} [Fintype σ] [DecidableEq σ] (J : Ideal C) (hJ : J ^ 2 = ⊥)
    {x : σ → C} (hx : ∀ s, x s ∈ J) (f : MvPowerSeries σ R) :
    MvFormalGroup.adicEval J x f =
      algebraMap R C (constantCoeff f) + ∑ s, algebraMap R C (coeff (Finsupp.single s 1) f) * x s := by
  classical

  have hxx : ∀ s t, x s * x t = 0 := by
    intro s t
    have : x s * x t ∈ J ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul (hx s) (hx t)
    rwa [hJ, Submodule.mem_bot] at this
  let D : Finset (σ →₀ ℕ) := Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ : σ => 2)
  have hD : ∀ d, d ∉ D → 2 ≤ d.degree := by
    intro d hd
    rw [Finset.mem_Iic] at hd
    have : ∃ s, 2 < d s := by
      by_contra h
      push Not at h
      exact hd fun s => by simpa using h s
    obtain ⟨s, hs⟩ := this
    calc 2 ≤ d s := hs.le
      _ ≤ d.degree := by
          rw [Finsupp.degree_apply]
          by_cases hs0 : s ∈ d.support
          · exact Finset.single_le_sum (fun i _ => Nat.zero_le _) hs0
          · rw [Finsupp.notMem_support_iff.mp hs0]; exact Nat.zero_le _
  rw [adicEval_eq_sum J hJ hx f D hD]

  let D' : Finset (σ →₀ ℕ) := insert 0 (Finset.univ.image fun s : σ => Finsupp.single s 1)
  have hD'D : D' ⊆ D := by
    intro d hd
    rw [Finset.mem_Iic]
    rcases Finset.mem_insert.mp hd with rfl | hd
    · exact bot_le
    · obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hd
      intro t
      show Finsupp.single s 1 t ≤ 2
      by_cases hst : s = t
      · subst hst; rw [Finsupp.single_eq_same]; omega
      · rw [Finsupp.single_eq_of_ne (Ne.symm hst)]; exact Nat.zero_le _
  rw [← Finset.sum_subset hD'D]
  · have h0 : (0 : σ →₀ ℕ) ∉ Finset.univ.image fun s : σ => Finsupp.single s 1 := by
      intro h
      obtain ⟨s, -, hs⟩ := Finset.mem_image.mp h
      exact one_ne_zero (Finsupp.single_eq_zero.mp hs)
    rw [Finset.sum_insert h0, Finset.sum_image fun s _ t _ h => Finsupp.single_left_injective one_ne_zero h]
    congr 1
    · rw [Finsupp.prod_zero_index, mul_one]; rfl
    · refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finsupp.prod_single_index (h := fun i e => x i ^ e) (pow_zero _), pow_one]
  · intro d _ hd
    have hd0 : d ≠ 0 := fun h => hd (h ▸ Finset.mem_insert_self _ _)
    have hd1 : ∀ s, d ≠ Finsupp.single s 1 := fun s h =>
      hd (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, h.symm⟩))
    rw [prod_pow_eq_zero_of_mul_eq_zero x hxx d hd0 hd1, mul_zero]

end NilEval

section Cast

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)}

def castPt {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t') (P : SchemeHomOver t f) :
    SchemeHomOver t' f :=
  ⟨P.1, h ▸ P.2⟩

@[scoped simp] theorem castPt_coe {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t')
    (P : SchemeHomOver t f) : (castPt h P).1 = P.1 := rfl

theorem castPt_injective {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t') :
    Function.Injective (castPt (f := f) h) := by
  intro P Q hPQ
  have h1 : (castPt h P).1 = (castPt h Q).1 := congrArg Subtype.val hPQ
  exact Subtype.ext h1

theorem castPt_mul (L : RelativeGroupLaw S f) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of S)}
    (h : t = t') (P Q : SchemeHomOver t f) :
    castPt h (L.mul t P Q) = L.mul t' (castPt h P) (castPt h Q) := by
  subst h; rfl

theorem castPt_symm_castPt {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t')
    (P : SchemeHomOver t f) : castPt h.symm (castPt h P) = P := rfl

theorem pushPt_castPt (φ : A ⟶ A) (hφ : φ ≫ f = f) {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of S)}
    (h : t = t') (P : SchemeHomOver t f) : pushPt φ hφ (castPt h P) = castPt h (pushPt φ hφ P) := rfl

end Cast

section Dual

variable (k : Type u) [Field k]

def Jε : Ideal (DualNumber k) := RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom

theorem mem_Jε_iff (x : DualNumber k) : x ∈ Jε k ↔ x.fst = 0 := Iff.rfl

theorem inr_mem_Jε (c : k) : (TrivSqZeroExt.inr c : DualNumber k) ∈ Jε k := by
  rw [mem_Jε_iff]; rfl

theorem eq_inr_of_mem_Jε {x : DualNumber k} (hx : x ∈ Jε k) : x = TrivSqZeroExt.inr x.snd := by
  rw [mem_Jε_iff] at hx
  ext <;> simp [hx]

theorem mul_eq_zero_of_mem_Jε {x y : DualNumber k} (hx : x ∈ Jε k) (hy : y ∈ Jε k) : x * y = 0 := by
  rw [eq_inr_of_mem_Jε k hx, eq_inr_of_mem_Jε k hy, TrivSqZeroExt.inr_mul_inr]

theorem Jε_sq : Jε k ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  rw [mul_eq_zero_of_mem_Jε k hx hy]
  exact Submodule.zero_mem _

theorem isNilpotent_Jε : IsNilpotent (Jε k) := ⟨2, Jε_sq k⟩

scoped instance isAdicComplete_Jε : IsAdicComplete (Jε k) (DualNumber k) :=
  isAdicComplete_of_isNilpotent _ (isNilpotent_Jε k)

theorem aug_surjective : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom :=
  fun x => ⟨TrivSqZeroExt.inl x, rfl⟩

def quotJ : (DualNumber k ⧸ Jε k) ≃+* k :=
  RingHom.quotientKerEquivOfSurjective (aug_surjective k)

theorem quotJ_mk (x : DualNumber k) : quotJ k (Ideal.Quotient.mk (Jε k) x) = x.fst := rfl

def qJc : CommRingCat.of (DualNumber k ⧸ Jε k) ⟶ CommRingCat.of k := CommRingCat.ofHom (quotJ k).toRingHom

def mkc : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of (DualNumber k ⧸ Jε k) :=
  CommRingCat.ofHom (Ideal.Quotient.mk (Jε k))

scoped instance isIso_specMap_qJc : IsIso (Spec.map (qJc k)) := by
  have h : qJc k = (quotJ k).toCommRingCatIso.hom := by rw [RingEquiv.toCommRingCatIso_hom]; rfl
  rw [h]
  infer_instance

abbrev mkS (C : Type u) [CommRing C] (J : Ideal C) : Spec (CommRingCat.of (C ⧸ J)) ⟶ Spec (CommRingCat.of C) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))

theorem tangentZero_eq : tangentZero k = Spec.map (qJc k) ≫ mkS (DualNumber k) (Jε k) := by
  rw [mkS, ← Spec.map_comp]
  rfl

end Dual

section Chart

variable {R : Type u} [CommRing R] {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
variable {Rᵢ : Type u} [CommRing Rᵢ] [Algebra R Rᵢ] {g : ℕ} {F : MvFormalGroup g Rᵢ}

abbrev tθ (C : Type u) [CommRing C] [Algebra Rᵢ C] : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))

abbrev tmod (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C) :
    Spec (CommRingCat.of (C ⧸ J)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ))))

def Clauses
    (θ : ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C) [IsAdicComplete J C],
      F.Points C J → SchemeHomOver (tθ (R := R) (Rᵢ := Rᵢ) C) f) : Prop :=
  ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C) [IsAdicComplete J C], IsNilpotent J →
    Function.Injective (θ C J) ∧
    (∀ x : F.Points C J,
      (∀ j, x.val j ∈ J) ↔
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ (θ C J x).1 =
          (L.one (Spec.map (CommRingCat.ofHom
            ((Ideal.Quotient.mk J).comp ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))))).1) ∧
    (∀ P : SchemeHomOver (Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))) f,
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ P.1 =
          (L.one (Spec.map (CommRingCat.ofHom
            ((Ideal.Quotient.mk J).comp ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ)))))).1 →
        P ∈ Set.range (θ C J)) ∧
    (∀ x y : F.Points C J,
      θ C J (x + y) =
        L.mul (Spec.map (CommRingCat.ofHom ((algebraMap Rᵢ C).comp (algebraMap R Rᵢ))))
          (θ C J x) (θ C J y)) ∧
    (∀ (C' : Type u) [CommRing C'] [Algebra Rᵢ C'] (J' : Ideal C') [IsAdicComplete J' C'],
      IsNilpotent J' →
        ∀ (φ : C →ₐ[Rᵢ] C') (x : F.Points C J) (x' : F.Points C' J'),
          (∀ j, x'.val j = φ (x.val j)) →
            (θ C' J' x').1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (θ C J x).1)

variable (θ : ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C) [IsAdicComplete J C],
  F.Points C J → SchemeHomOver (tθ (R := R) (Rᵢ := Rᵢ) C) f)

variable (k : Type u) [Field k] [Algebra Rᵢ k]

def εpt (v : Fin g → k) : F.Points (DualNumber k) (Jε k) :=
  ⟨fun i => TrivSqZeroExt.inr (v i), fun i => Ideal.le_radical (inr_mem_Jε k (v i))⟩

@[scoped simp] theorem εpt_val (v : Fin g → k) (i : Fin g) : (εpt (F := F) k v).val i = TrivSqZeroExt.inr (v i) := rfl

theorem εpt_injective : Function.Injective (εpt (F := F) k) := by
  intro v w h
  funext i
  have := congrArg (fun x : F.Points (DualNumber k) (Jε k) => (x.val i).snd) h
  simpa using this

theorem εpt_mem (v : Fin g → k) (i : Fin g) : (εpt (F := F) k v).val i ∈ Jε k := inr_mem_Jε k (v i)

theorem εpt_snd_eq (x : F.Points (DualNumber k) (Jε k)) (hx : ∀ j, x.val j ∈ Jε k) :
    εpt k (fun j => (x.val j).snd) = x := by
  apply MvFormalGroup.Points.ext
  funext j
  exact (eq_inr_of_mem_Jε k (hx j)).symm

theorem algebraMap_mul_inr (r : Rᵢ) (c : k) :
    algebraMap Rᵢ (DualNumber k) r * TrivSqZeroExt.inr c = TrivSqZeroExt.inr (algebraMap Rᵢ k r * c) := by
  rw [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.inl_mul_inr, smul_eq_mul]

theorem εpt_add (v w : Fin g → k) : εpt (F := F) k v + εpt k w = εpt k (v + w) := by
  classical
  apply MvFormalGroup.Points.ext
  funext i
  rw [MvFormalGroup.Points.val_add]
  have hx : ∀ s, Sum.elim (εpt (F := F) k v).val (εpt (F := F) k w).val s ∈ Jε k := by
    rintro (s | s) <;> exact inr_mem_Jε k _
  rw [adicEval_sqZero (Jε k) (Jε_sq k) hx, F.constantCoeff_eq_zero, map_zero, zero_add]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, F.coeff_single_inl, F.coeff_single_inr, εpt_val]
  simp only [apply_ite (algebraMap Rᵢ (DualNumber k)), map_one, map_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact (TrivSqZeroExt.inr_add k (v i) (w i)).symm

theorem evalPoints_εpt (ρ : MvFormalGroup.Hom F F) (w : Fin g → k) :
    ρ.evalPoints (εpt k w) =
      εpt k (((MvFormalGroup.linearPart ρ.toPowerSeries).map (algebraMap Rᵢ k)).mulVec w) := by
  classical
  apply MvFormalGroup.Points.ext
  funext i
  rw [MvFormalGroup.Hom.val_evalPoints, adicEval_sqZero (Jε k) (Jε_sq k) (εpt_mem k w),
    ρ.constantCoeff_eq_zero, map_zero, zero_add, εpt_val, Matrix.mulVec, dotProduct]
  simp only [εpt_val, algebraMap_mul_inr, Matrix.map_apply, MvFormalGroup.linearPart, Matrix.of_apply]
  induction (Finset.univ : Finset (Fin g)) using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, ih, TrivSqZeroExt.inr_add]

variable {k}
variable (sk : R →+* k) (hsk : (algebraMap Rᵢ k).comp (algebraMap R Rᵢ) = sk)

include hsk in

theorem tθ_dual_eq : tθ (R := R) (Rᵢ := Rᵢ) (DualNumber k) = tangentBase k sk := by
  rw [tangentBase, ← hsk]

include hsk in

theorem qJc_comp : Spec.map (qJc k) ≫ tmod (R := R) (Rᵢ := Rᵢ) (DualNumber k) (Jε k) = geomPoint k sk := by
  rw [tmod, geomPoint, ← Spec.map_comp, ← hsk]
  congr 1

include hsk in

theorem mod_iff_isTangent (P₁ : Spec (CommRingCat.of (DualNumber k)) ⟶ 𝒜) :
    mkS (DualNumber k) (Jε k) ≫ P₁ = (L.one (tmod (R := R) (Rᵢ := Rᵢ) (DualNumber k) (Jε k))).1 ↔
      tangentZero k ≫ P₁ = (L.one (geomPoint k sk)).1 := by
  have hone : (L.one (geomPoint k sk)).1 =
      Spec.map (qJc k) ≫ (L.one (tmod (R := R) (Rᵢ := Rᵢ) (DualNumber k) (Jε k))).1 :=
    (congrArg Subtype.val (L.one_natural _ _ (Spec.map (qJc k)) (qJc_comp sk hsk))).symm
  rw [tangentZero_eq, Category.assoc, hone]
  constructor
  · intro h
    rw [h]
  · intro h
    exact (cancel_epi (Spec.map (qJc k))).mp h

def scale (c : k) : DualNumber k →ₐ[Rᵢ] DualNumber k :=
  (TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k))).restrictScalars Rᵢ

theorem scale_inr (c m : k) : scale (Rᵢ := Rᵢ) c (TrivSqZeroExt.inr m) = TrivSqZeroExt.inr (c * m) := by
  show TrivSqZeroExt.map (R' := k) (c • (LinearMap.id : k →ₗ[k] k)) (TrivSqZeroExt.inr m) = _
  rw [TrivSqZeroExt.map_inr]
  rfl

theorem tangentScale_eq (c : k) :
    tangentScale k c = Spec.map (CommRingCat.ofHom (scale (Rᵢ := Rᵢ) c).toRingHom) := rfl

def τ₀ (v : Fin g → k) : SchemeHomOver (tangentBase k sk) f :=
  castPt (tθ_dual_eq sk hsk) (θ (DualNumber k) (Jε k) (εpt k v))

theorem τ₀_coe (v : Fin g → k) : (τ₀ θ sk hsk v).1 = (θ (DualNumber k) (Jε k) (εpt k v)).1 := rfl

variable {θ} (hcl : Clauses L θ)
include hcl

theorem τ₀_injective : Function.Injective (τ₀ θ sk hsk) := by
  intro v w h
  obtain ⟨hinj, -, -, -, -⟩ := hcl (DualNumber k) (Jε k) (isNilpotent_Jε k)
  exact εpt_injective k (hinj (castPt_injective _ h))

theorem mem_range_τ₀_iff (P : SchemeHomOver (tangentBase k sk) f) :
    P ∈ Set.range (τ₀ θ sk hsk) ↔ IsTangentVector L k sk P := by
  obtain ⟨-, hmod, honto, -, -⟩ := hcl (DualNumber k) (Jε k) (isNilpotent_Jε k)
  constructor
  · rintro ⟨v, rfl⟩
    exact (mod_iff_isTangent L sk hsk _).mp ((hmod (εpt k v)).mp (εpt_mem k v))
  · intro hP
    have hP' := (mod_iff_isTangent L sk hsk P.1).mpr hP
    obtain ⟨x, hx⟩ := honto (castPt (tθ_dual_eq sk hsk).symm P) hP'
    have hxJ : ∀ j, x.val j ∈ Jε k := (hmod x).mpr (by rw [hx]; exact hP')
    refine ⟨fun j => (x.val j).snd, ?_⟩
    apply Subtype.ext
    rw [τ₀_coe, εpt_snd_eq k x hxJ, hx]
    rfl

theorem τ₀_add (v w : Fin g → k) : τ₀ θ sk hsk (v + w) = L.mul (tangentBase k sk) (τ₀ θ sk hsk v) (τ₀ θ sk hsk w) := by
  obtain ⟨-, -, -, hadd, -⟩ := hcl (DualNumber k) (Jε k) (isNilpotent_Jε k)
  rw [τ₀, τ₀, τ₀, ← castPt_mul, ← hadd, εpt_add]

theorem τ₀_smul (c : k) (v : Fin g → k) : (τ₀ θ sk hsk (c • v)).1 = tangentScale k c ≫ (τ₀ θ sk hsk v).1 := by
  obtain ⟨-, -, -, -, hnat⟩ := hcl (DualNumber k) (Jε k) (isNilpotent_Jε k)
  rw [τ₀_coe, τ₀_coe, tangentScale_eq (Rᵢ := Rᵢ)]
  refine hnat (DualNumber k) (Jε k) (isNilpotent_Jε k) (scale c) (εpt k v) (εpt k (c • v)) fun j => ?_
  rw [εpt_val, εpt_val, scale_inr, Pi.smul_apply, smul_eq_mul]

omit hcl in

theorem τ₀_mulVec (u : 𝒜 ⟶ 𝒜) (hu : u ≫ f = f) (ρ : MvFormalGroup.Hom F F)
    (hρ : ∀ (C : Type u) [CommRing C] [Algebra Rᵢ C] (J : Ideal C) [IsAdicComplete J C], IsNilpotent J →
      ∀ x : F.Points C J, θ C J (ρ.evalPoints x) = pushPt u hu (θ C J x))
    (w : Fin g → k) :
    τ₀ θ sk hsk (((MvFormalGroup.linearPart ρ.toPowerSeries).map (algebraMap Rᵢ k)).mulVec w) =
      pushPt u hu (τ₀ θ sk hsk w) := by
  rw [τ₀, τ₀, pushPt_castPt, ← hρ _ _ (isNilpotent_Jε k), evalPoints_εpt]

end Chart

section TwoCharts

variable {S : Type u} [CommRing S] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)
variable (k : Type u) [Field k] (sk : S →+* k)
variable {V : Type u} [AddCommGroup V] [Module k V] (τ : V → SchemeHomOver (tangentBase k sk) f)
  (hinj : Function.Injective τ)
  (hrange : ∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P)
  (hadd : ∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w))
  (hsmul : ∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1)
variable {W : Type u} [AddCommGroup W] [Module k W] (τ' : W → SchemeHomOver (tangentBase k sk) f)
  (hinj' : Function.Injective τ')
  (hrange' : ∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ' ↔ IsTangentVector L k sk P)
  (hadd' : ∀ v w : W, τ' (v + w) = L.mul (tangentBase k sk) (τ' v) (τ' w))
  (hsmul' : ∀ (c : k) (v : W), (τ' (c • v)).1 = tangentScale k c ≫ (τ' v).1)

include hinj hrange hadd hsmul hinj' hrange' hadd' hsmul' in

theorem exists_linearEquiv : ∃ e : V ≃ₗ[k] W, ∀ v, τ' (e v) = τ v := by
  have hex : ∀ v : V, ∃ w : W, τ' w = τ v := fun v =>
    (hrange' (τ v)).mpr ((hrange (τ v)).mp ⟨v, rfl⟩)
  have hex' : ∀ w : W, ∃ v : V, τ v = τ' w := fun w =>
    (hrange (τ' w)).mpr ((hrange' (τ' w)).mp ⟨w, rfl⟩)
  choose e he using hex
  choose e' he' using hex'
  refine ⟨{ toFun := e,
             map_add' := fun v w => hinj' ?_,
             map_smul' := fun c v => hinj' (Subtype.ext ?_),
             invFun := e',
             left_inv := fun v => hinj ?_,
             right_inv := fun w => hinj' ?_ }, he⟩
  · rw [he, hadd, hadd', he, he]
  · rw [he, hsmul, RingHom.id_apply, hsmul', he]
  · rw [he', he]
  · rw [he, he']

include hinj' in

theorem trace_eq_of_intertwine
    (e : V ≃ₗ[k] W) (he : ∀ v, τ' (e v) = τ v)
    (u : A ⟶ A) (hu : u ≫ f = f) (Φ : V →ₗ[k] V) (hΦ : ∀ v, τ (Φ v) = pushPt u hu (τ v))
    (Φ' : W →ₗ[k] W) (hΦ' : ∀ w, τ' (Φ' w) = pushPt u hu (τ' w)) :
    LinearMap.trace k V Φ = LinearMap.trace k W Φ' := by
  have hconj : e.conj Φ = Φ' := by
    refine LinearMap.ext fun w => hinj' ?_
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, hΦ']
    show τ' (e (Φ (e.symm w))) = _
    rw [he, hΦ, ← he, LinearEquiv.apply_symm_apply]
  rw [← hconj, LinearMap.trace_conj']

end TwoCharts

section Main

variable {a b : ℚ} {Λ : Submodule ℤ (ℍ[ℚ, a, b])}
    {R : Type u} [CommRing R] [IsDomain R]
    {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of R)}

theorem main (L : RelativeGroupLaw R f) (hL : L.IsCommutative) (hf : Smooth f)
    (act : ↥Λ → (𝒜 ⟶ 𝒜)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
    (act_hom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
    (hgen : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k), Function.Injective sk →
      ∀ (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P) →
        (∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w)) →
        (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
        ∀ (m : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (act m) (act_over m) (τ v)) →
        ∀ n : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) =
            ((n : ℚ) : ℍ[ℚ, a, b]) →
          LinearMap.trace k V Φ = (n : k))
    (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k)
    (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f)
    (hinj : Function.Injective τ)
    (hrange : ∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P)
    (hadd : ∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w))
    (hsmul : ∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1)
    (m : ↥Λ) (Φ : V →ₗ[k] V) (hΦ : ∀ v : V, τ (Φ v) = pushPt (act m) (act_over m) (τ v))
    (n : ℤ) (hn : (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) =
      ((n : ℚ) : ℍ[ℚ, a, b])) :
    LinearMap.trace k V Φ = (n : k) := by
  classical

  obtain ⟨N, c, hspan, hloc⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_mvFormalGroup_kernelOfReduction_of_smooth L hL hf

  obtain ⟨i, hi⟩ : ∃ i, sk (c i) ≠ 0 := by
    by_contra h
    push Not at h
    have hle : Ideal.span (Set.range c) ≤ RingHom.ker sk := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact h j
    rw [hspan] at hle
    have h1 : sk 1 = 0 := hle Submodule.mem_top
    exact one_ne_zero (by rwa [map_one] at h1)
  have hci : c i ≠ 0 := fun h0 => hi (by rw [h0, map_zero])

  let Rᵢ : Type u := Localization.Away (c i)
  have hpow : Submonoid.powers (c i) ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hci
  haveI : IsDomain Rᵢ := IsLocalization.isDomain_localization hpow
  have hRinj : Function.Injective (algebraMap R Rᵢ) := IsLocalization.injective Rᵢ hpow
  letI : Algebra Rᵢ k := (IsLocalization.Away.lift (c i) (g := sk) (isUnit_iff_ne_zero.mpr hi)).toAlgebra
  have hsk : (algebraMap Rᵢ k).comp (algebraMap R Rᵢ) = sk := IsLocalization.Away.lift_comp (c i) _
  obtain ⟨g, F, θ, -, hcl, hact, -⟩ := hloc i Rᵢ

  obtain ⟨ρ, hρ⟩ := hact (act m) (act_over m) (act_hom m)
  let M : Matrix (Fin g) (Fin g) Rᵢ := MvFormalGroup.linearPart (MvFormalGroup.Hom.toPowerSeries (F := F) (G := F) ρ)

  have key : ∀ (k' : Type u) [Field k'] [Algebra Rᵢ k'] (sk' : R →+* k')
      (hsk' : (algebraMap Rᵢ k').comp (algebraMap R Rᵢ) = sk')
      (V' : Type u) [AddCommGroup V'] [Module k' V'] (τ' : V' → SchemeHomOver (tangentBase k' sk') f),
      Function.Injective τ' →
      (∀ P : SchemeHomOver (tangentBase k' sk') f, P ∈ Set.range τ' ↔ IsTangentVector L k' sk' P) →
      (∀ v w : V', τ' (v + w) = L.mul (tangentBase k' sk') (τ' v) (τ' w)) →
      (∀ (c : k') (v : V'), (τ' (c • v)).1 = tangentScale k' c ≫ (τ' v).1) →
      ∀ Φ' : V' →ₗ[k'] V', (∀ v, τ' (Φ' v) = pushPt (act m) (act_over m) (τ' v)) →
        LinearMap.trace k' V' Φ' = algebraMap Rᵢ k' M.trace := by
    intro k' _ _ sk' hsk' V' _ _ τ' hinj' hrange' hadd' hsmul' Φ' hΦ'
    have hclL : Clauses L θ := hcl
    obtain ⟨e, he⟩ := exists_linearEquiv L k' sk' τ' hinj' hrange' hadd' hsmul'
      (τ₀ θ sk' hsk') (τ₀_injective L sk' hsk' hclL) (mem_range_τ₀_iff L sk' hsk' hclL)
      (τ₀_add L sk' hsk' hclL) (τ₀_smul L sk' hsk' hclL)
    rw [trace_eq_of_intertwine k' sk' τ' (τ₀ θ sk' hsk') (τ₀_injective L sk' hsk' hclL) e he
      (act m) (act_over m) Φ' hΦ' (Matrix.toLin' (M.map (algebraMap Rᵢ k')))
      (fun w => by rw [Matrix.toLin'_apply]; exact τ₀_mulVec (θ := θ) sk' hsk' (act m) (act_over m) ρ hρ w),
      Matrix.trace_toLin'_eq, ← AddMonoidHom.map_trace]

  let K : Type u := AlgebraicClosure (FractionRing Rᵢ)
  have hKinj : Function.Injective (algebraMap Rᵢ K) := by
    rw [IsScalarTower.algebraMap_eq Rᵢ (FractionRing Rᵢ) K, RingHom.coe_comp]
    exact (algebraMap (FractionRing Rᵢ) K).injective.comp (IsFractionRing.injective Rᵢ (FractionRing Rᵢ))
  let sK : R →+* K := (algebraMap Rᵢ K).comp (algebraMap R Rᵢ)
  have hsKinj : Function.Injective sK := hKinj.comp hRinj
  have hM : algebraMap Rᵢ K M.trace = (n : K) := by
    have hclL : Clauses L θ := hcl
    rw [← key K sK rfl (Fin g → K) (τ₀ θ sK rfl) (τ₀_injective L sK rfl hclL) (mem_range_τ₀_iff L sK rfl hclL)
      (τ₀_add L sK rfl hclL) (τ₀_smul L sK rfl hclL) (Matrix.toLin' (M.map (algebraMap Rᵢ K)))
      (fun w => by rw [Matrix.toLin'_apply]; exact τ₀_mulVec (θ := θ) sK rfl (act m) (act_over m) ρ hρ w)]
    exact hgen K sK hsKinj (Fin g → K) (τ₀ θ sK rfl) (τ₀_injective L sK rfl hclL) (mem_range_τ₀_iff L sK rfl hclL)
      (τ₀_add L sK rfl hclL) (τ₀_smul L sK rfl hclL) m _
      (fun w => by rw [Matrix.toLin'_apply]; exact τ₀_mulVec (θ := θ) sK rfl (act m) (act_over m) ρ hρ w) n hn
  have hMn : M.trace = (n : Rᵢ) := hKinj (by rw [hM, map_intCast])

  rw [key k sk hsk V τ hinj hrange hadd hsmul Φ hΦ, hMn, map_intCast]

end Main

end TraceClosedBody
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_trace_eq_of_smooth_of_isCommutative_of_forall_injective_trace_eq.TraceClosedBody"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_QM_trace_eq_of_smooth_of_isCommutative_of_forall_injective_trace_eq.TraceClosedBody"

open TraceClosedBody in
theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    {R : Type u} [CommRing R] [IsDomain R]
    {𝒜 : Scheme.{u}} {f : 𝒜 ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (hL : L.IsCommutative) (hf : Smooth f)
    (act : ↥Λ → (𝒜 ⟶ 𝒜)) (act_over : ∀ x : ↥Λ, act x ≫ f = f)
    (act_hom : ∀ (x : ↥Λ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f),
      pushPt (act x) (act_over x) (L.mul t P Q) = L.mul t (pushPt (act x) (act_over x) P) (pushPt (act x) (act_over x) Q))
    (hgen : ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k), Function.Injective sk →
      ∀ (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P) →
        (∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w)) →
        (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
        ∀ (m : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (act m) (act_over m) (τ v)) →
        ∀ n : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          LinearMap.trace k V Φ = (n : k)
    ) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (sk : R →+* k),
      ∀ (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f),
        Function.Injective τ →
        (∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P) →
        (∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w)) →
        (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
        ∀ (m : ↥Λ) (Φ : V →ₗ[k] V), (∀ v : V, τ (Φ v) = pushPt (act m) (act_over m) (τ v)) →
        ∀ n : ℤ, (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((n : ℚ) : ℍ[ℚ, a, b]) →
          LinearMap.trace k V Φ = (n : k) := by
  intro k _ _ sk V _ _ _ τ hinj hrange hadd hsmul m Φ hΦ n hn
  exact main L hL hf act act_over act_hom hgen k sk V τ hinj hrange hadd hsmul m Φ hΦ n hn

end S_CerednikDrinfeld_QM_trace_eq_of_smooth_of_isCommutative_of_forall_injective_trace_eq
end P2MW
export P2MW.S_CerednikDrinfeld_QM_trace_eq_of_smooth_of_isCommutative_of_forall_injective_trace_eq (solution)
