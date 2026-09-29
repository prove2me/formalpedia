-- Prove2me | solution 1 for CerednikDrinfeld.QM.forall_trace_eq_apply_trace_linearPart_of_isFormalCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.141142+00:00
-- url     : https://prove2.me/submissions/65cace05-82bf-525d-ad48-f315f6b8c374

import Mathlib
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_CerednikDrinfeld_QM_exists_injective_range_isTangentVector_of_isFormalCoordinates
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_QM_forall_trace_eq_apply_trace_linearPart_of_isFormalCoordinates

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM P2MW.S_CerednikDrinfeld_QM_forall_trace_eq_apply_trace_linearPart_of_isFormalCoordinates.CerednikDrinfeld.QM"

noncomputable section

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "QM.exists_injective_range_isTangentVector_of_isFormalCoordinates"
namespace QM
p2m_export "CerednikDrinfeld.QM" "mapPt_coe pushPt tangentBase tangentScale IsTangentVector exists_injective_range_isTangentVector_of_isFormalCoordinates"
namespace TraceLinPartAux
p2m_open "CerednikDrinfeld.QM CerednikDrinfeld"

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

def J : Ideal (DualNumber k) := RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom

theorem mem_J_iff (x : DualNumber k) : x ∈ J k ↔ x.fst = 0 := Iff.rfl

theorem inr_mem_J (m : k) : (TrivSqZeroExt.inr m : DualNumber k) ∈ J k := by
  rw [mem_J_iff]; rfl

theorem eq_inr_of_mem_J {x : DualNumber k} (hx : x ∈ J k) : x = TrivSqZeroExt.inr x.snd := by
  rw [mem_J_iff] at hx
  ext <;> simp [hx]

theorem mul_eq_zero_of_mem_J {x y : DualNumber k} (hx : x ∈ J k) (hy : y ∈ J k) : x * y = 0 := by
  rw [eq_inr_of_mem_J k hx, eq_inr_of_mem_J k hy, TrivSqZeroExt.inr_mul_inr]

theorem J_sq : J k ^ (1 + 1) = ⊥ := by
  rw [one_add_one_eq_two, pow_two, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  rw [mul_eq_zero_of_mem_J k hx hy]
  exact Submodule.zero_mem _

def epsV {g : ℕ} (v : Fin g → k) : Fin g → DualNumber k := fun i => TrivSqZeroExt.inr (v i)

theorem epsV_mem {g : ℕ} (v : Fin g → k) (i : Fin g) : epsV k v i ∈ J k := inr_mem_J k (v i)

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

section LinAlg

theorem trace_mulVecLin {g : ℕ} (k : Type) [Field k] (A : Matrix (Fin g) (Fin g) k) :
    LinearMap.trace k (Fin g → k) (Matrix.mulVecLin A) = A.trace := by
  rw [← Matrix.toLin'_apply', LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin g)),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

end LinAlg

end CerednikDrinfeld.QM.TraceLinPartAux

end

open CerednikDrinfeld.QM.TraceLinPartAux in
theorem solution
    {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} {g : ℕ}
    (L : RelativeGroupLaw B f) (F : MvFormalGroup g B) (θ : RelativeGroupLaw.FormalCoordinates f g)
    (hθ : L.IsFormalCoordinates F θ)
    (a : A ⟶ A) (ha : a ≫ f = f)

    (φ : Fin g → MvPowerSeries (Fin g) B) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφ : ∀ (B' : Type) [CommRing B'] [Algebra B B'] (J : Ideal B') (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ s : Fin g → B', (∀ i, s i ∈ J) →
        θ B' (fun i => MvFormalGroup.nilEval n (φ i) s) = pushPt a ha (θ B' s)) :
    ∀ (k : Type) [Field k] (sk : B →+* k)
      (V : Type) [AddCommGroup V] [Module k V] [Module.Finite k V] (τ : V → SchemeHomOver (tangentBase k sk) f),
      Function.Injective τ →
      (∀ P : SchemeHomOver (tangentBase k sk) f, P ∈ Set.range τ ↔ IsTangentVector L k sk P) →
      (∀ v w : V, τ (v + w) = L.mul (tangentBase k sk) (τ v) (τ w)) →
      (∀ (c : k) (v : V), (τ (c • v)).1 = tangentScale k c ≫ (τ v).1) →
      ∀ Φ : V →ₗ[k] V, (∀ v : V, τ (Φ v) = pushPt a ha (τ v)) →
        LinearMap.trace k V Φ = sk (Matrix.trace (MvFormalGroup.linearPart φ)) := by
  intro k _ sk V _ _ _ τ hinj hrange hadd hsmul Φ hΦ
  classical
  letI : Algebra B k := sk.toAlgebra
  have hsk : algebraMap B k = sk := rfl
  obtain ⟨τ₀, hτθ, hinj₀, hrange₀, hadd₀, hsmul₀⟩ :=
    CerednikDrinfeld.QM.exists_injective_range_isTangentVector_of_isFormalCoordinates L F θ hθ k
  set M : Matrix (Fin g) (Fin g) B := MvFormalGroup.linearPart φ with hMdef
  let Φ₀ : (Fin g → k) →ₗ[k] (Fin g → k) := Matrix.mulVecLin (M.map sk)

  have hΦ₀ : ∀ w, τ₀ (Φ₀ w) = pushPt a ha (τ₀ w) := by
    intro w
    apply Subtype.ext
    rw [hτθ (Φ₀ w), mapPt_coe, hτθ w]
    have key := hφ (DualNumber k) (J k) 1 (J_sq k) (epsV k w) (epsV_mem k w)
    have hε : (fun i => MvFormalGroup.nilEval 1 (φ i) (epsV k w)) = fun i => TrivSqZeroExt.inr (Φ₀ w i) := by
      funext i
      rw [nilEval_one_epsV k φ hφ0 w i, Matrix.mulVecLin_apply, hsk]
    have key' := congrArg Subtype.val key
    rw [mapPt_coe, hε] at key'
    exact key'

  have hex : ∀ v, ∃ w, τ₀ w = τ v := fun v => (hrange₀ (τ v)).mpr ((hrange (τ v)).mp ⟨v, rfl⟩)
  choose e he using hex
  have he_add : ∀ v w, e (v + w) = e v + e w := by
    intro v w
    apply hinj₀
    rw [he, hadd, hadd₀, he, he]
    rfl
  have he_smul : ∀ (c : k) (v : V), e (c • v) = c • e v := by
    intro c v
    apply hinj₀
    apply Subtype.ext
    rw [hsmul₀, he, he, hsmul]
  let eL : V →ₗ[k] (Fin g → k) :=
    { toFun := e, map_add' := he_add, map_smul' := he_smul }
  have he_inj : Function.Injective e := by
    intro v w hvw
    apply hinj
    rw [← he v, ← he w, hvw]
  have he_surj : Function.Surjective e := by
    intro w
    obtain ⟨v, hv⟩ := (hrange (τ₀ w)).mpr ((hrange₀ (τ₀ w)).mp ⟨w, rfl⟩)
    refine ⟨v, hinj₀ ?_⟩
    rw [he, hv]
  let eE : V ≃ₗ[k] (Fin g → k) := LinearEquiv.ofBijective eL ⟨he_inj, he_surj⟩
  have heE : ∀ v, eE v = e v := fun _ => rfl

  have hconj : ∀ v, e (Φ v) = Φ₀ (e v) := by
    intro v
    apply hinj₀
    rw [he, hΦ, hΦ₀, he]
  have hΦeq : Φ = eE.symm.toLinearMap ∘ₗ Φ₀ ∘ₗ eE.toLinearMap := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
    apply eE.injective
    rw [LinearEquiv.apply_symm_apply, heE, heE, hconj]

  have htr : LinearMap.trace k V Φ = LinearMap.trace k (Fin g → k) Φ₀ := by
    rw [hΦeq, LinearMap.trace_comp_comm', LinearMap.comp_assoc, ← LinearEquiv.coe_trans,
      LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap, LinearMap.comp_id]
  rw [htr, trace_mulVecLin, AddMonoidHom.map_trace]

end S_CerednikDrinfeld_QM_forall_trace_eq_apply_trace_linearPart_of_isFormalCoordinates
end P2MW
export P2MW.S_CerednikDrinfeld_QM_forall_trace_eq_apply_trace_linearPart_of_isFormalCoordinates (solution)
