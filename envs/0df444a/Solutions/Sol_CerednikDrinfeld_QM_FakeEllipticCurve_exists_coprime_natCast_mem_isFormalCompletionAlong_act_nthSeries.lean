-- Prove2me | solution 1 for CerednikDrinfeld.QM.FakeEllipticCurve.exists_coprime_natCast_mem_isFormalCompletionAlong_act_nthSeries
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/6e3d8684-0739-5b92-9007-7b6cfa24229c

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_QMFormalCompletionAlong
import Definitions.Def_MvFormalGroup_NegV2
import Theorems.Thm_CerednikDrinfeld_QM_exists_injective_range_isTangentVector_of_isFormalCoordinates
import Theorems.Thm_CerednikDrinfeld_QM_existsUnique_hom_isFormalCompletionAlong_of_isFormalCoordinates
import Theorems.Thm_CerednikDrinfeld_QM_IsFormalCompletionAlong_of_forall_mapPt_eq_mul_of_isFormalCoordinates
import Theorems.Thm_CerednikDrinfeld_QM_IsFormalCompletionAlong_id_and_comp
import Theorems.Thm_CerednikDrinfeld_QM_IsOrderCoord_exists_eq_pow_smul_and_exists_nsmul_mem_and_exists_coprime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_coprime_natCast_mem_isFormalCompletionAlong_act_nthSeries
p2m_attr_erase "instance" "MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal

open scoped Quaternion

noncomputable section

namespace D2aUnital

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

theorem nilEval_one_eq_sum {g : ℕ} (φ : MvPowerSeries (Fin g) B) (hφ : MvPowerSeries.constantCoeff φ = 0)
    (a : Fin g → C) (ha : ∀ x y, a x * a y = 0) :
    MvFormalGroup.nilEval 1 φ a = ∑ x, MvPowerSeries.coeff (Finsupp.single x 1) φ • a x := by
  classical
  unfold MvFormalGroup.nilEval
  rw [aeval_eq_of_mul_eq_zero a ha]
  have h0 : (MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ : Fin g => 1) φ).coeff 0 = 0 := by
    rw [MvPowerSeries.coeff_trunc', if_pos (Finsupp.le_def.2 fun _ => Nat.zero_le _),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ]
  have h1 : ∀ x : Fin g, (MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ : Fin g => 1) φ).coeff
      (Finsupp.single x 1) = MvPowerSeries.coeff (Finsupp.single x 1) φ := by
    intro x
    rw [MvPowerSeries.coeff_trunc', if_pos]
    rw [Finsupp.le_def]
    intro y
    show Finsupp.single x 1 y ≤ 1
    by_cases hxy : x = y
    · subst hxy; rw [Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne (Ne.symm hxy)]; exact Nat.zero_le _
  rw [h0, map_zero, zero_add]
  convert rfl using 2
  rw [h1]

end Poly

section Dual

variable {B : Type} [CommRing B] (k : Type) [Field k] [Algebra B k]

def Jε : Ideal (DualNumber k) := RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom

theorem mem_Jε_iff (x : DualNumber k) : x ∈ Jε k ↔ x.fst = 0 := Iff.rfl

theorem eq_inr_of_mem_Jε {x : DualNumber k} (hx : x ∈ Jε k) : x = TrivSqZeroExt.inr x.snd := by
  rw [mem_Jε_iff] at hx
  ext <;> simp [hx]

theorem mul_eq_zero_of_mem_Jε {x y : DualNumber k} (hx : x ∈ Jε k) (hy : y ∈ Jε k) : x * y = 0 := by
  rw [eq_inr_of_mem_Jε k hx, eq_inr_of_mem_Jε k hy, TrivSqZeroExt.inr_mul_inr]

theorem Jε_sq : Jε k ^ (1 + 1) = ⊥ := by
  rw [one_add_one_eq_two, pow_two, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  rw [mul_eq_zero_of_mem_Jε k hx hy]
  exact Submodule.zero_mem _

def epsV {g : ℕ} (v : Fin g → k) : Fin g → DualNumber k := fun i => TrivSqZeroExt.inr (v i)

theorem epsV_mem {g : ℕ} (v : Fin g → k) (i : Fin g) : epsV k v i ∈ Jε k := by
  rw [mem_Jε_iff]; rfl

theorem epsV_mul {g : ℕ} (v : Fin g → k) (x y : Fin g) : epsV k v x * epsV k v y = 0 :=
  TrivSqZeroExt.inr_mul_inr k _ _

theorem nilEval_one_epsV {g : ℕ} (φ : Fin g → MvPowerSeries (Fin g) B)
    (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (v : Fin g → k) (i : Fin g) :
    MvFormalGroup.nilEval 1 (φ i) (epsV k v) =
      TrivSqZeroExt.inr (((MvFormalGroup.linearPart φ).map (algebraMap B k)).mulVec v i) := by
  classical
  rw [nilEval_one_eq_sum (φ i) (hφ i) (epsV k v) (epsV_mul k v)]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  have hterm : ∀ x : Fin g, MvPowerSeries.coeff (Finsupp.single x 1) (φ i) • epsV k v x =
      TrivSqZeroExt.inr (algebraMap B k (MvFormalGroup.linearPart φ i x) * v x) := by
    intro x
    rw [epsV, ← Algebra.smul_def, TrivSqZeroExt.inr_smul]
    rfl
  simp only [hterm]
  induction (Finset.univ : Finset (Fin g)) using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, ih, TrivSqZeroExt.inr_add]

end Dual

section Read

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}

theorem trace_mulVecLin (k : Type) [Field k] (A : Matrix (Fin 2) (Fin 2) k) :
    LinearMap.trace k (Fin 2 → k) (Matrix.mulVecLin A) = A.trace := by
  rw [← Matrix.toLin'_apply', LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin 2)),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

theorem apply_trace_linearPart_eq {B : Type} [CommRing B] (E : FakeEllipticCurve Λ N B) (F : MvFormalGroup 2 B)
    (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hθ : E.L.IsFormalCoordinates F θ) (m : ↥Λ)
    (φ : Fin 2 → MvPowerSeries (Fin 2) B) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφ : IsFormalCompletionAlong θ θ (E.act m) (E.act_over m) φ)
    (k : Type) [Field k] [IsAlgClosed k] (sk : B →+* k)
    (t : ℤ) (hm : (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((t : ℚ) : ℍ[ℚ, a, b])) :
    sk (Matrix.trace (MvFormalGroup.linearPart φ)) = (t : k) := by
  classical
  letI : Algebra B k := sk.toAlgebra
  have hsk : algebraMap B k = sk := rfl
  obtain ⟨τ, hτθ, hinj, hrange, hadd, hsmul⟩ :=
    CerednikDrinfeld.QM.exists_injective_range_isTangentVector_of_isFormalCoordinates E.L F θ hθ k
  set M : Matrix (Fin 2) (Fin 2) B := MvFormalGroup.linearPart φ with hMdef
  let Φ : (Fin 2 → k) →ₗ[k] (Fin 2 → k) := Matrix.mulVecLin (M.map sk)
  have hΦ : ∀ v, τ (Φ v) = pushPt (E.act m) (E.act_over m) (τ v) := by
    intro v
    apply Subtype.ext
    rw [hτθ (Φ v), mapPt_coe, hτθ v]
    have key := hφ (DualNumber k) (Jε k) 1 (Jε_sq k) (epsV k v) (epsV_mem k v)
    have hε : (fun i => MvFormalGroup.nilEval 1 (φ i) (epsV k v)) = fun i => TrivSqZeroExt.inr (Φ v i) := by
      funext i
      rw [nilEval_one_epsV k φ hφ0 v i, Matrix.mulVecLin_apply, hsk]
    have key' := congrArg Subtype.val key
    rw [mapPt_coe, hε] at key'
    exact key'
  have htr := E.act_trace k sk (Fin 2 → k) τ hinj hrange hadd hsmul m Φ hΦ t hm
  rw [trace_mulVecLin] at htr
  rw [AddMonoidHom.map_trace]
  exact htr

end Read

section Completions

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {B : Type} [CommRing B]
variable (E : FakeEllipticCurve Λ N B) (F : MvFormalGroup 2 B) [F.IsComm]
variable (θ : RelativeGroupLaw.FormalCoordinates E.f 2) (hθ : E.L.IsFormalCoordinates F θ)

theorem isFormalCompletionAlong_congr {A A' : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of B)} {f' : A' ⟶ Spec (CommRingCat.of B)} {g g' : ℕ}
    {θ : RelativeGroupLaw.FormalCoordinates f g} {θ' : RelativeGroupLaw.FormalCoordinates f' g'}
    {h h' : A ⟶ A'} {hh : h ≫ f' = f} {hh' : h' ≫ f' = f} {φ : Fin g' → MvPowerSeries (Fin g) B}
    (e : h = h') (H : IsFormalCompletionAlong θ θ' h' hh' φ) : IsFormalCompletionAlong θ θ' h hh φ := by
  subst e
  exact H

include hθ in

theorem exists_completion :
    ∃ R : ↥Λ → MvFormalGroup.End F,
      (∀ m, IsFormalCompletionAlong θ θ (E.act m) (E.act_over m) (R m).toPowerSeries) ∧
      (∀ m (φ : MvFormalGroup.End F), IsFormalCompletionAlong θ θ (E.act m) (E.act_over m) φ.toPowerSeries → φ = R m) ∧
      (∀ m m', R (m + m') = R m + R m') ∧
      (∀ (m m' : ↥Λ) (h : (m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) ∈ Λ),
        R ⟨(m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]), h⟩ = R m * R m') ∧
      (∀ (n : ℕ) (m : ↥Λ), R (n • m) = n • R m) := by
  classical
  have hC : ∀ m : ↥Λ, ∃! φ : MvFormalGroup.End F,
      IsFormalCompletionAlong θ θ (E.act m) (E.act_over m) φ.toPowerSeries := fun m =>
    CerednikDrinfeld.QM.existsUnique_hom_isFormalCompletionAlong_of_isFormalCoordinates E.L E.L F F θ θ hθ hθ
      (E.act m) (E.act_over m) (fun B' _ _ P Q => E.act_hom m _ P Q)
  let R : ↥Λ → MvFormalGroup.End F := fun m => Classical.choose (hC m).exists
  have hR : ∀ m, IsFormalCompletionAlong θ θ (E.act m) (E.act_over m) (R m).toPowerSeries := fun m =>
    Classical.choose_spec (hC m).exists
  have hRu : ∀ (m : ↥Λ) (φ : MvFormalGroup.End F),
      IsFormalCompletionAlong θ θ (E.act m) (E.act_over m) φ.toPowerSeries → φ = R m :=
    fun m φ h => (hC m).unique h (hR m)
  have hadd : ∀ m m' : ↥Λ, R (m + m') = R m + R m' := by
    intro m m'
    symm
    apply hRu
    exact CerednikDrinfeld.QM.IsFormalCompletionAlong.of_forall_mapPt_eq_mul_of_isFormalCoordinates θ θ E.L F hθ
      (E.act m) (E.act m') (E.act (m + m')) (E.act_over m) (E.act_over m') (E.act_over _)
      (fun B' _ _ P => E.act_add m m' _ P) (R m).toPowerSeries (R m').toPowerSeries
      (R m).constantCoeff_eq_zero (R m').constantCoeff_eq_zero (hR m) (hR m')
  have hmul : ∀ (m m' : ↥Λ) (h : (m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]) ∈ Λ),
      R ⟨(m : ℍ[ℚ, a, b]) * (m' : ℍ[ℚ, a, b]), h⟩ = R m * R m' := by
    intro m m' h
    symm
    apply hRu
    have hc := (CerednikDrinfeld.QM.IsFormalCompletionAlong.id_and_comp θ θ θ).2 (E.act m') (E.act_over m')
      (E.act m) (E.act_over m) (by rw [Category.assoc, E.act_over, E.act_over]) (R m').toPowerSeries
      (R m).toPowerSeries (R m').constantCoeff_eq_zero (hR m') (hR m)
    exact isFormalCompletionAlong_congr (E.act_mul m m' h) hc
  have h0 : R 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    exact add_eq_left.1 h.symm
  have hnsmul : ∀ (n : ℕ) (m : ↥Λ), R (n • m) = n • R m := by
    intro n m
    induction n with
    | zero => rw [zero_smul, zero_smul, h0]
    | succ n ih => rw [succ_nsmul, hadd, ih, succ_nsmul]
  exact ⟨R, hR, hRu, hadd, hmul, hnsmul⟩

end Completions

section TwoByTwo

variable {B : Type} [CommRing B]

theorem mul_self_eq_trace_smul_sub (M : Matrix (Fin 2) (Fin 2) B) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) B) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.trace_fin_two,
    Matrix.det_fin_two, Matrix.one_apply, smul_eq_mul, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem exists_eq_smul_one_of_idem_of_trace {k : Type} [Field k] (e : Matrix (Fin 2) (Fin 2) k) (he : e * e = e)
    (htr : e.trace = 2) : ∃ c : k, e = c • (1 : Matrix (Fin 2) (Fin 2) k) ∧ c * c = c ∧ 2 * (c - 1) = 0 := by
  have h := mul_self_eq_trace_smul_sub e
  rw [he, htr, two_smul] at h
  have hec : e = e.det • (1 : Matrix (Fin 2) (Fin 2) k) := by
    have h' := congrArg (fun A => A - e) h
    simp only [sub_self] at h'

    have : e - e.det • (1 : Matrix (Fin 2) (Fin 2) k) = 0 := by
      rw [h']; abel
    exact sub_eq_zero.1 this
  refine ⟨e.det, hec, ?_, ?_⟩
  · have h2 := congrFun (congrFun he 0) 0
    rw [hec] at h2
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.one_apply] using h2
  · have h3 := congrArg Matrix.trace hec
    rw [htr, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, Fintype.card_fin] at h3
    push_cast at h3
    linear_combination -h3

end TwoByTwo

section Subst

variable {B : Type} [CommRing B] {g : ℕ}

open MvPowerSeries

theorem eq_zero_of_subst_eq_zero_of_isUnit (c : Fin g → MvPowerSeries (Fin g) B)
    (hc0 : ∀ j, constantCoeff (c j) = 0) (u : Bˣ)
    (hc1 : ∀ j j', coeff (Finsupp.single j' 1) (c j) = if j = j' then (u : B) else 0)
    {p : MvPowerSeries (Fin g) B} (hp : subst c p = 0) : p = 0 := by
  classical

  set c₁ : Fin g → MvPowerSeries (Fin g) B := fun j => ((u⁻¹ : Bˣ) : B) • c j with hc₁
  have hc₁0 : ∀ j, constantCoeff (c₁ j) = 0 := fun j => by
    show constantCoeff (((u⁻¹ : Bˣ) : B) • c j) = 0
    rw [smul_eq_C_mul, map_mul, hc0 j, mul_zero]
  have hc₁1 : ∀ j j', coeff (Finsupp.single j' 1) (c₁ j) = if j = j' then 1 else 0 := fun j j' => by
    show coeff (Finsupp.single j' 1) (((u⁻¹ : Bˣ) : B) • c j) = _
    rw [coeff_smul, hc1 j j']
    split_ifs
    · exact Units.inv_mul u
    · exact mul_zero _

  set s : Fin g → MvPowerSeries (Fin g) B := fun j => (u : B) • X j with hs
  set s' : Fin g → MvPowerSeries (Fin g) B := fun j => ((u⁻¹ : Bˣ) : B) • X j with hs'
  have hs0 : ∀ j, constantCoeff (s j) = 0 := fun j => by
    show constantCoeff ((u : B) • (X j : MvPowerSeries (Fin g) B)) = 0
    rw [smul_eq_C_mul, map_mul, constantCoeff_X, mul_zero]
  have hs'0 : ∀ j, constantCoeff (s' j) = 0 := fun j => by
    show constantCoeff (((u⁻¹ : Bˣ) : B) • (X j : MvPowerSeries (Fin g) B)) = 0
    rw [smul_eq_C_mul, map_mul, constantCoeff_X, mul_zero]
  have hss : HasSubst s := hasSubst_of_constantCoeff_zero hs0
  have hss' : HasSubst s' := hasSubst_of_constantCoeff_zero hs'0
  have hsc₁ : HasSubst c₁ := hasSubst_of_constantCoeff_zero hc₁0

  have h1 : subst c₁ (subst s p) = subst c p := by
    rw [subst_comp_subst_apply hss hsc₁]
    congr 1
    funext j
    show subst c₁ ((u : B) • X j) = c j
    rw [← coe_substAlgHom hsc₁, map_smul, coe_substAlgHom hsc₁, subst_X hsc₁]
    show (u : B) • (((u⁻¹ : Bˣ) : B) • c j) = c j
    rw [smul_smul, Units.mul_inv, one_smul]
  have h2 : subst s p = 0 := MvFormalGroup.eq_zero_of_subst_eq_zero hc₁0 hc₁1 (by rw [h1, hp])

  have h3 : subst s' (subst s p) = p := by
    rw [subst_comp_subst_apply hss hss']
    have : (fun j => subst s' (s j)) = fun j => (X j : MvPowerSeries (Fin g) B) := by
      funext j
      show subst s' ((u : B) • X j) = X j
      rw [← coe_substAlgHom hss', map_smul, coe_substAlgHom hss', subst_X hss']
      show (u : B) • (((u⁻¹ : Bˣ) : B) • X j) = X j
      rw [smul_smul, Units.mul_inv, one_smul]
    rw [this]
    exact congrFun subst_self p
  rw [← h3, h2, ← coe_substAlgHom hss', map_zero]

end Subst

section Main

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]

theorem coe_nsmul (n : ℕ) (m : ↥Λ) : ((n • m : ↥Λ) : ℍ[ℚ, a, b]) = (n : ℚ) • (m : ℍ[ℚ, a, b]) := by
  rw [Submodule.coe_smul_of_tower, Nat.cast_smul_eq_nsmul]

theorem exists_add_sq_eq_one : ∃ ω : GaloisField 2 2, ω + ω ^ 2 = 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 2) = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 two_ne_zero]
    norm_num

  have hex : ∃ ω : GaloisField 2 2, ω ^ 2 ≠ ω := by
    by_contra hall
    push Not at hall

    have hsub : ∀ ω : GaloisField 2 2, ω = 0 ∨ ω = 1 := by
      intro ω
      have h : ω * (ω - 1) = 0 := by rw [mul_sub, mul_one, ← pow_two, hall ω, sub_self]
      rcases mul_eq_zero.1 h with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.1 h)
    have hle : Fintype.card (GaloisField 2 2) ≤ 2 := by
      have : (Finset.univ : Finset (GaloisField 2 2)) ⊆ ({0, 1} : Finset (GaloisField 2 2)) := by
        intro ω _
        rcases hsub ω with h | h <;> simp [h]
      have h := Finset.card_le_card this
      rw [Finset.card_univ] at h
      exact h.trans (Finset.card_le_two)
    omega
  obtain ⟨ω, hω⟩ := hex
  refine ⟨ω, ?_⟩
  have h2 : (2 : GaloisField 2 2) = 0 := by
    have : ringChar (GaloisField 2 2) = 2 := ringChar.eq (GaloisField 2 2) 2
    exact (ringChar.spec _ 2).2 (by rw [this])

  have hω4 : ω ^ 4 = ω := by
    have := FiniteField.pow_card ω
    rwa [hcard] at this
  have hy : (ω + ω ^ 2) * (ω + ω ^ 2 - 1) = 0 := by
    have e : (ω + ω ^ 2) * (ω + ω ^ 2 - 1) = ω ^ 4 - ω + 2 * ω ^ 3 := by ring
    rw [e, hω4, h2]; ring
  rcases mul_eq_zero.1 hy with h | h
  · exfalso
    apply hω
    have : ω ^ 2 = -ω := eq_neg_of_add_eq_zero_right h
    rw [this]
    have : -ω = ω - 2 * ω := by ring
    rw [this, h2]; ring
  · exact sub_eq_zero.1 h

theorem solution'
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (B : Type) [CommRing B] (hq : IsNilpotent ((q : ℕ) : B)) (E : FakeEllipticCurve Λ N B)
    (F : MvFormalGroup 2 B) (hF : F.IsComm) (θ : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hθ : E.L.IsFormalCoordinates F θ) :
    ∃ n : ℕ, n.Coprime q ∧ ∃ h : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      coord ⟨((n : ℚ) : ℍ[ℚ, a, b]), h⟩ = ((n : Zp2 q), 0) ∧
        IsFormalCompletionAlong θ θ (E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), h⟩) (E.act_over _) (F.nthSeries n) := by
  classical
  haveI := hF
  obtain ⟨-, -, -, n, hn, h1, hc1⟩ :=
    CerednikDrinfeld.QM.IsOrderCoord.exists_eq_pow_smul_and_exists_nsmul_mem_and_exists_coprime coord hcoord
  refine ⟨n, hn, h1, hc1, ?_⟩
  obtain ⟨K₀, hK₀⟩ := hq
  set x : ↥Λ := ⟨((n : ℚ) : ℍ[ℚ, a, b]), h1⟩ with hx

  have hnu : IsUnit (n : B) := by
    have hcop : (n ^ 1).Coprime (q ^ K₀) := Nat.Coprime.pow 1 K₀ hn
    rw [pow_one] at hcop
    obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
    have : (u : B) * n = 1 := by
      have h := congrArg (fun z : ℤ => (z : B)) huv
      push_cast at h
      rw [hK₀, mul_zero, add_zero] at h
      exact h
    exact IsUnit.of_mul_eq_one_right _ this

  obtain ⟨R, hR, hRu, hRadd, hRmul, hRnsmul⟩ := exists_completion E F θ hθ
  set r := R x with hr

  have hxm : ∀ m : ↥Λ, ∃ h : ((x : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b])) ∈ Λ,
      (⟨(x : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]), h⟩ : ↥Λ) = n • m := by
    intro m
    have e : (x : ℍ[ℚ, a, b]) * (m : ℍ[ℚ, a, b]) = ((n • m : ↥Λ) : ℍ[ℚ, a, b]) := by
      rw [coe_nsmul, hx, QuaternionAlgebra.coe_mul_eq_smul]
    exact ⟨by rw [e]; exact Submodule.coe_mem _, Subtype.ext e⟩
  have hrRm : ∀ m, r * R m = n • R m := by
    intro m
    obtain ⟨h, he⟩ := hxm m
    rw [← hRmul x m h, he, hRnsmul]
  have hrr : r * r = n • r := hrRm x

  set M : Matrix (Fin 2) (Fin 2) B := MvFormalGroup.linearPart r.toPowerSeries with hM
  have hlp : ∀ φ ψ : MvFormalGroup.End F, MvFormalGroup.linearPart (φ * ψ).toPowerSeries =
      MvFormalGroup.linearPart φ.toPowerSeries * MvFormalGroup.linearPart ψ.toPowerSeries :=
    fun φ ψ => (MvFormalGroup.linearPartHom F).map_mul φ ψ
  have hlpn : ∀ (k : ℕ) (φ : MvFormalGroup.End F), MvFormalGroup.linearPart (k • φ).toPowerSeries =
      k • MvFormalGroup.linearPart φ.toPowerSeries :=
    fun k φ => map_nsmul (MvFormalGroup.linearPartHom F) k φ
  have hMM : M * M = n • M := by rw [hM, ← hlp, hrr, hlpn]
  have hMm : ∀ m, M * MvFormalGroup.linearPart (R m).toPowerSeries = n • MvFormalGroup.linearPart (R m).toPowerSeries :=
    fun m => by rw [hM, ← hlp, hrRm, hlpn]

  have htrx : (x : ℍ[ℚ, a, b]) + star (x : ℍ[ℚ, a, b]) = ((((2 * (n : ℤ) : ℤ)) : ℚ) : ℍ[ℚ, a, b]) := by
    rw [hx]
    change ((n : ℚ) : ℍ[ℚ, a, b]) + star ((n : ℚ) : ℍ[ℚ, a, b]) = _
    rw [QuaternionAlgebra.star_coe, ← QuaternionAlgebra.coe_add]
    congr 1
    push_cast
    ring
  have hgeo : ∀ (P : Ideal B), P.IsPrime → ∀ i j, (M - n • (1 : Matrix (Fin 2) (Fin 2) B)) i j ∈ P := by
    intro P hP
    haveI := hP
    let k : Type := AlgebraicClosure (FractionRing (B ⧸ P))
    let sk : B →+* k := ((algebraMap (FractionRing (B ⧸ P)) k).comp
      (algebraMap (B ⧸ P) (FractionRing (B ⧸ P)))).comp (Ideal.Quotient.mk P)
    have hker : ∀ z : B, sk z = 0 ↔ z ∈ P := by
      intro z
      show (algebraMap (FractionRing (B ⧸ P)) k) (algebraMap (B ⧸ P) (FractionRing (B ⧸ P))
        (Ideal.Quotient.mk P z)) = 0 ↔ _
      rw [map_eq_zero_iff _ (algebraMap (FractionRing (B ⧸ P)) k).injective,
        map_eq_zero_iff _ (IsFractionRing.injective (B ⧸ P) (FractionRing (B ⧸ P))), Ideal.Quotient.eq_zero_iff_mem]

    have hqk : ((q : ℕ) : k) = 0 := by
      have : IsNilpotent ((q : ℕ) : k) := ⟨K₀, by rw [← map_natCast sk, ← map_pow, hK₀, map_zero]⟩
      exact this.eq_zero
    haveI : CharP k q := (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).2 hqk
    have hnk : (n : k) ≠ 0 := by
      rw [← map_natCast sk]
      exact (hnu.map sk).ne_zero

    set Mb : Matrix (Fin 2) (Fin 2) k := M.map sk with hMb
    have hMbMb : Mb * Mb = (n : k) • Mb := by
      rw [hMb, ← Matrix.map_mul, hMM]
      ext i j
      rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, nsmul_eq_mul, map_mul,
        map_natCast, smul_eq_mul]
    have htrMb : Mb.trace = 2 * (n : k) := by
      rw [hMb, ← AddMonoidHom.map_trace]
      change sk (Matrix.trace M) = _
      have h := apply_trace_linearPart_eq E F θ hθ x r.toPowerSeries r.constantCoeff_eq_zero (hR x) k sk (2 * (n : ℤ)) htrx
      rw [h]
      rw [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]

    set e : Matrix (Fin 2) (Fin 2) k := (n : k)⁻¹ • Mb with he
    have hee : e * e = e := by
      rw [he, smul_mul_smul_comm, hMbMb, smul_smul]
      congr 1
      rw [mul_assoc, inv_mul_cancel₀ hnk, mul_one]
    have htre : e.trace = 2 := by
      rw [he, Matrix.trace_smul, htrMb, smul_eq_mul, mul_comm, mul_assoc, mul_inv_cancel₀ hnk, mul_one]
    obtain ⟨c, hec, hcc, h2c⟩ := exists_eq_smul_one_of_idem_of_trace e hee htre

    have hc : c = 1 := by
      by_cases h2 : (2 : k) = 0
      ·
        rcases mul_eq_zero.1 (show c * (c - 1) = 0 by rw [mul_sub, hcc, mul_one, sub_self]) with hc0 | hc1'
        · exfalso

          have hMb0 : Mb = 0 := by
            have : Mb = (n : k) • e := by rw [he, smul_smul, mul_inv_cancel₀ hnk, one_smul]
            rw [this, hec, hc0, zero_smul, smul_zero]
          have hRm0 : ∀ m, (MvFormalGroup.linearPart (R m).toPowerSeries).map sk = 0 := by
            intro m
            have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) B => A.map sk) (hMm m)
            simp only [Matrix.map_mul] at h
            change Mb * _ = _ at h
            rw [hMb0, zero_mul] at h
            have h' : (n : k) • (MvFormalGroup.linearPart (R m).toPowerSeries).map sk = 0 := by
              rw [h]
              ext i j
              rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, nsmul_eq_mul, map_mul,
                map_natCast, smul_eq_mul]
            exact (smul_eq_zero.1 h').resolve_left hnk

          have htr0 : ∀ (m : ↥Λ) (t : ℤ), (m : ℍ[ℚ, a, b]) + star (m : ℍ[ℚ, a, b]) = ((t : ℚ) : ℍ[ℚ, a, b]) →
              (t : k) = 0 := by
            intro m t hmt
            rw [← apply_trace_linearPart_eq E F θ hθ m (R m).toPowerSeries (R m).constantCoeff_eq_zero (hR m) k sk t
              hmt, AddMonoidHom.map_trace]
            change Matrix.trace ((MvFormalGroup.linearPart (R m).toPowerSeries).map sk) = 0
            rw [hRm0 m, Matrix.trace_zero]

          have hq2 : q = 2 := by
            have h2' : ((2 : ℕ) : k) = 0 := by exact_mod_cast h2
            rw [CharP.cast_eq_zero_iff k q] at h2'
            exact (Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) Nat.prime_two).1 h2'
          subst hq2

          obtain ⟨ω, hω⟩ := exists_add_sq_eq_one
          obtain ⟨m₀, hαm, -⟩ := hcoord.dense 1 (WittVector.teichmuller 2 ω) 0
          rw [pow_one, WittVector.mem_span_p_iff_coeff_zero_eq_zero, ← WittVector.constantCoeff_apply, map_sub,
            WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero,
            sub_eq_zero] at hαm

          obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℚ, (m₀ : ℍ[ℚ, a, b]) + star (m₀ : ℍ[ℚ, a, b]) = (c₀ : ℍ[ℚ, a, b]) :=
            ⟨_, QuaternionAlgebra.self_add_star' _⟩
          set s₀ : ℕ := c₀.den with hs₀
          set r₀ : ℤ := c₀.num with hr₀
          set m₁ : ↥Λ := s₀ • m₀ with hm₁
          have hm₁tr : (m₁ : ℍ[ℚ, a, b]) + star (m₁ : ℍ[ℚ, a, b]) = ((r₀ : ℚ) : ℍ[ℚ, a, b]) := by
            rw [hm₁, Submodule.coe_smul_of_tower, star_nsmul, ← nsmul_add, hc₀, nsmul_eq_mul,
              ← QuaternionAlgebra.coe_natCast, ← QuaternionAlgebra.coe_mul, mul_comm, Rat.mul_den_eq_num]
          have hcm₁ : coord m₁ = s₀ • coord m₀ := by
            rw [hm₁]
            clear hm₁tr hm₁
            induction s₀ with
            | zero =>
              rw [zero_smul, zero_smul]
              have h := hcoord.map_add 0 0
              rw [add_zero] at h
              exact add_eq_left.1 h.symm
            | succ s ih => rw [succ_nsmul, hcoord.map_add, ih, succ_nsmul]

          have htrW := hcoord.trace m₁ r₀ hm₁tr
          rw [hcm₁, Prod.smul_fst, nsmul_eq_mul, map_mul, map_natCast, ← mul_add] at htrW
          have hcc := congrArg WittVector.constantCoeff htrW
          rw [map_mul, map_natCast, map_add, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
            WittVector.coeff_frobenius_charP, hαm, hω, mul_one, map_intCast] at hcc

          have hr₀k : ((r₀ : ℤ) : k) = 0 := htr0 m₁ r₀ hm₁tr
          haveI : CharP k 2 := inferInstance
          have h2r : (2 : ℤ) ∣ r₀ := (CharP.intCast_eq_zero_iff k 2 r₀).1 hr₀k

          have hs₀ : (2 : ℕ) ∣ s₀ := by
            have : ((r₀ : ℤ) : GaloisField 2 2) = 0 := (CharP.intCast_eq_zero_iff (GaloisField 2 2) 2 r₀).2 h2r
            rw [this] at hcc
            exact (CharP.cast_eq_zero_iff (GaloisField 2 2) 2 s₀).1 hcc
          have h2r' : (2 : ℕ) ∣ r₀.natAbs := Int.natCast_dvd.1 (by exact_mod_cast h2r)
          have := Nat.eq_one_of_dvd_coprimes (Rat.reduced c₀) h2r' hs₀
          omega
        · exact sub_eq_zero.1 hc1'
      · have := mul_eq_zero.1 h2c
        rcases this with h | h
        · exact absurd h h2
        · exact sub_eq_zero.1 h

    have hMbn : Mb = (n : k) • (1 : Matrix (Fin 2) (Fin 2) k) := by
      have : Mb = (n : k) • e := by rw [he, smul_smul, mul_inv_cancel₀ hnk, one_smul]
      rw [this, hec, hc, one_smul]
    intro i j
    rw [← hker, Matrix.sub_apply, map_sub]
    have h1 := congrFun (congrFun hMbn i) j
    rw [hMb, Matrix.map_apply] at h1
    rw [h1, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp [nsmul_eq_mul]

  set Nm : Matrix (Fin 2) (Fin 2) B := M - n • (1 : Matrix (Fin 2) (Fin 2) B) with hNm
  have hnil : ∀ i j, IsNilpotent (Nm i j) := fun i j => nilpotent_iff_mem_prime.2 fun P hP => hgeo P hP i j
  have hMeq : M = Nm + n • (1 : Matrix (Fin 2) (Fin 2) B) := by rw [hNm, sub_add_cancel]
  have hNM : Nm * M = 0 := by
    rw [hNm, sub_mul, hMM, smul_mul_assoc, one_mul, sub_self]
  have hdet : IsUnit M.det := by
    have hM00 : M 0 0 = Nm 0 0 + n := by
      rw [hNm, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, nsmul_eq_mul, mul_one, sub_add_cancel]
    have hM11 : M 1 1 = Nm 1 1 + n := by
      rw [hNm, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, nsmul_eq_mul, mul_one, sub_add_cancel]
    have hM01 : M 0 1 = Nm 0 1 := by
      rw [hNm, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne (by decide), smul_zero, sub_zero]
    have hM10 : M 1 0 = Nm 1 0 := by
      rw [hNm, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne (by decide), smul_zero, sub_zero]
    rw [Matrix.det_fin_two, hM00, hM11, hM01, hM10]
    have hν : IsNilpotent (Nm 0 0 * (n : B) + (n : B) * Nm 1 1 + Nm 0 0 * Nm 1 1 - Nm 0 1 * Nm 1 0) := by
      have h : ∀ i j, Nm i j ∈ nilradical B := fun i j => mem_nilradical.2 (hnil i j)
      apply mem_nilradical.1
      refine Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_right _ _ (h 0 0))
        (Ideal.mul_mem_left _ _ (h 1 1))) (Ideal.mul_mem_left _ _ (h 1 1))) (Ideal.mul_mem_left _ _ (h 1 0))
    have hn2 : IsUnit ((n : B) * n) := hnu.mul hnu
    have e : (Nm 0 0 + (n : B)) * (Nm 1 1 + (n : B)) - Nm 0 1 * Nm 1 0 =
        (n : B) * n + (Nm 0 0 * (n : B) + (n : B) * Nm 1 1 + Nm 0 0 * Nm 1 1 - Nm 0 1 * Nm 1 0) := by ring
    rw [e]
    obtain ⟨w, hw⟩ := hn2
    rw [← hw, show (w : B) + _ = w * (1 + (w⁻¹ : Bˣ) * (Nm 0 0 * (n : B) + (n : B) * Nm 1 1 + Nm 0 0 * Nm 1 1 -
      Nm 0 1 * Nm 1 0)) by rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]]
    exact (Units.isUnit w).mul ((Commute.all _ _).isNilpotent_mul_left hν).isUnit_one_add
  have hNm0 : Nm = 0 := by
    have h := congrArg (fun A => A * M⁻¹) hNM
    simp only [zero_mul] at h
    rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv M hdet, Matrix.mul_one] at h
  have hMn : M = n • (1 : Matrix (Fin 2) (Fin 2) B) := by rw [hMeq, hNm0, zero_add]

  have hrn : r = (n : MvFormalGroup.End F) := by
    have hd : (r - n) * r = 0 := by rw [sub_mul, hrr, nsmul_eq_mul, sub_self]
    have hz : ∀ i, MvPowerSeries.subst r.toPowerSeries ((r - (n : MvFormalGroup.End F)).toPowerSeries i) = 0 := by
      intro i
      have := congrFun (congrArg MvFormalGroup.Hom.toPowerSeries hd) i
      exact this
    have hc1 : ∀ j j', MvPowerSeries.coeff (Finsupp.single j' 1) (r.toPowerSeries j) =
        if j = j' then ((hnu.unit : Bˣ) : B) else 0 := by
      intro j j'
      have := congrFun (congrFun hMn j) j'
      rw [hM] at this
      simp only [MvFormalGroup.linearPart, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply] at this
      rw [this, IsUnit.unit_spec]
      split_ifs <;> simp
    have h0 : r - (n : MvFormalGroup.End F) = 0 := by
      apply MvFormalGroup.Hom.ext
      funext i
      exact eq_zero_of_subst_eq_zero_of_isUnit r.toPowerSeries r.constantCoeff_eq_zero hnu.unit hc1 (hz i)
    exact sub_eq_zero.1 h0
  have := hR x
  rw [← hr, hrn, MvFormalGroup.End.toPowerSeries_natCast] at this
  exact this

end Main

end D2aUnital

end

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {q : ℕ} [Fact q.Prime]
    (coord : ↥Λ → Zp2 q × Zp2 q) (hcoord : IsOrderCoord Λ q coord)
    (B : Type) [CommRing B] (hq : IsNilpotent ((q : ℕ) : B)) (E : FakeEllipticCurve Λ N B)
    (F : MvFormalGroup 2 B) (hF : F.IsComm) (θ : RelativeGroupLaw.FormalCoordinates E.f 2)
    (hθ : E.L.IsFormalCoordinates F θ) :
    ∃ n : ℕ, n.Coprime q ∧ ∃ h : ((n : ℚ) : ℍ[ℚ, a, b]) ∈ Λ,
      coord ⟨((n : ℚ) : ℍ[ℚ, a, b]), h⟩ = ((n : Zp2 q), 0) ∧
        IsFormalCompletionAlong θ θ (E.act ⟨((n : ℚ) : ℍ[ℚ, a, b]), h⟩) (E.act_over _) (F.nthSeries n) :=
  D2aUnital.solution' coord hcoord B hq E F hF θ hθ

end S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_coprime_natCast_mem_isFormalCompletionAlong_act_nthSeries
end P2MW
export P2MW.S_CerednikDrinfeld_QM_FakeEllipticCurve_exists_coprime_natCast_mem_isFormalCompletionAlong_act_nthSeries (solution)
