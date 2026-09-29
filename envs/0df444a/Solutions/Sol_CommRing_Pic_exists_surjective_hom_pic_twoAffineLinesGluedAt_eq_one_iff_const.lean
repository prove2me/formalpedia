-- Prove2me | solution 1 for CommRing.Pic.exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/37bb581d-d369-5cea-a71a-628d9752c838

import Mathlib
import Theorems.Thm_CommRing_Pic_exists_boundaryHom_conductorSquare_exact
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CommRing_Pic_exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const

open Polynomial TensorProduct

universe u v

namespace ProdPic

variable {R₁ R₂ : Type u} [CommRing R₁] [CommRing R₂]

theorem CommRing.Pic.eq_one_of_mapRingHom_fst_snd (P : CommRing.Pic (R₁ × R₂))
    (h₁ : CommRing.Pic.mapRingHom (RingHom.fst R₁ R₂) P = 1)
    (h₂ : CommRing.Pic.mapRingHom (RingHom.snd R₁ R₂) P = 1) : P = 1 := by
  letI alg₁ : Algebra (R₁ × R₂) R₁ := (RingHom.fst R₁ R₂).toAlgebra
  letI alg₂ : Algebra (R₁ × R₂) R₂ := (RingHom.snd R₁ R₂).toAlgebra
  set R := R₁ × R₂
  set M := (P : Type u)
  have h₁' : CommRing.Pic.mapAlgebra R R₁ P = 1 := by
    rw [← CommRing.Pic.mapRingHom_algebraMap]; exact h₁
  have h₂' : CommRing.Pic.mapAlgebra R R₂ P = 1 := by
    rw [← CommRing.Pic.mapRingHom_algebraMap]; exact h₂
  rw [CommRing.Pic.mapAlgebra_apply, CommRing.Pic.mk_eq_one_iff] at h₁' h₂'
  obtain ⟨e₁⟩ := h₁'
  obtain ⟨e₂⟩ := h₂'
  have hsm₁ : ∀ (r : R) (x : R₁), r • x = r.1 * x := fun r x => rfl
  have hsm₂ : ∀ (r : R) (x : R₂), r • x = r.2 * x := fun r x => rfl

  let F : M →ₗ[R] R :=
    { toFun := fun m => (e₁ (1 ⊗ₜ m), e₂ (1 ⊗ₜ m))
      map_add' := fun m m' => by simp only [tmul_add, map_add, Prod.mk_add_mk]; rfl
      map_smul' := fun r m => by
        rw [RingHom.id_apply]
        have t₁ : (1 : R₁) ⊗ₜ[R] (r • m) = r • ((1 : R₁) ⊗ₜ[R] m) := by rw [smul_tmul', smul_tmul]
        have t₂ : (1 : R₂) ⊗ₜ[R] (r • m) = r • ((1 : R₂) ⊗ₜ[R] m) := by rw [smul_tmul', smul_tmul]
        rw [t₁, t₂, ← algebraMap_smul R₁ r ((1 : R₁) ⊗ₜ[R] m), ← algebraMap_smul R₂ r ((1 : R₂) ⊗ₜ[R] m),
          map_smul, map_smul]
        change (r.1 • e₁ (1 ⊗ₜ m), r.2 • e₂ (1 ⊗ₜ m)) = r * (e₁ (1 ⊗ₜ m), e₂ (1 ⊗ₜ m))
        rfl }

  let ψ₁ : R₁ ⊗[R] M →ₗ[R] M := TensorProduct.lift
    { toFun := fun x => ((x, 0) : R) • LinearMap.id
      map_add' := fun x y => by
        rw [← add_smul]; congr 1; change _ = ((x + y, 0 + 0) : R); rw [add_zero]
      map_smul' := fun r x => by
        rw [RingHom.id_apply, hsm₁, ← smul_assoc]
        congr 1
        change ((r.1 * x, 0) : R) = r * (x, 0)
        rw [Prod.mk_mul_mk, mul_zero] }
  let ψ₂ : R₂ ⊗[R] M →ₗ[R] M := TensorProduct.lift
    { toFun := fun y => ((0, y) : R) • LinearMap.id
      map_add' := fun x y => by
        rw [← add_smul]; congr 1; change _ = ((0 + 0, x + y) : R); rw [add_zero]
      map_smul' := fun r y => by
        rw [RingHom.id_apply, hsm₂, ← smul_assoc]
        congr 1
        change ((0, r.2 * y) : R) = r * (0, y)
        rw [Prod.mk_mul_mk, mul_zero] }
  have hψ₁ : ∀ m : M, ψ₁ (1 ⊗ₜ m) = ((1, 0) : R) • m := fun m => by
    simp only [ψ₁, TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
      LinearMap.id_apply]
  have hψ₂ : ∀ m : M, ψ₂ (1 ⊗ₜ m) = ((0, 1) : R) • m := fun m => by
    simp only [ψ₂, TensorProduct.lift.tmul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
      LinearMap.id_apply]

  have hsurj₁ : ∀ z : R₁ ⊗[R] M, ∃ m : M, z = 1 ⊗ₜ m := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [tmul_zero]⟩
    | tmul x m => exact ⟨((x, 0) : R) • m, by rw [← smul_tmul, hsm₁, mul_one]⟩
    | add z z' hz hz' =>
      obtain ⟨m, rfl⟩ := hz; obtain ⟨m', rfl⟩ := hz'
      exact ⟨m + m', by rw [tmul_add]⟩
  have hsurj₂ : ∀ z : R₂ ⊗[R] M, ∃ m : M, z = 1 ⊗ₜ m := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [tmul_zero]⟩
    | tmul y m => exact ⟨((0, y) : R) • m, by rw [← smul_tmul, hsm₂, mul_one]⟩
    | add z z' hz hz' =>
      obtain ⟨m, rfl⟩ := hz; obtain ⟨m', rfl⟩ := hz'
      exact ⟨m + m', by rw [tmul_add]⟩
  have hF : Function.Bijective F := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro m hm
      have hm₁ : e₁ (1 ⊗ₜ m) = 0 := congrArg Prod.fst hm
      have hm₂ : e₂ (1 ⊗ₜ m) = 0 := congrArg Prod.snd hm
      rw [map_eq_zero_iff _ e₁.injective] at hm₁
      rw [map_eq_zero_iff _ e₂.injective] at hm₂
      have k₁ := hψ₁ m
      have k₂ := hψ₂ m
      rw [hm₁, map_zero] at k₁
      rw [hm₂, map_zero] at k₂
      calc m = ((1, 0) : R) • m + ((0, 1) : R) • m := by
              rw [← add_smul]; change m = ((1 + 0, 0 + 1) : R) • m
              rw [add_zero, zero_add]; exact (one_smul R m).symm
        _ = 0 := by rw [← k₁, ← k₂, add_zero]
    · rintro ⟨x, y⟩
      obtain ⟨n₁, hn₁⟩ := hsurj₁ (e₁.symm 1)
      obtain ⟨n₂, hn₂⟩ := hsurj₂ (e₂.symm 1)
      refine ⟨((x, 0) : R) • n₁ + ((0, y) : R) • n₂, ?_⟩
      have a₁ : ∀ r : R, algebraMap R R₁ r = r.1 := fun r => rfl
      have a₂ : ∀ r : R, algebraMap R R₂ r = r.2 := fun r => rfl
      refine Prod.ext ?_ ?_
      · change e₁ (1 ⊗ₜ _) = x
        rw [tmul_add, tmul_smul, tmul_smul, ← hn₁, ← algebraMap_smul R₁ ((x, 0) : R),
          ← algebraMap_smul R₁ ((0, y) : R), a₁, a₁]
        change e₁ (x • e₁.symm 1 + (0 : R₁) • (1 ⊗ₜ n₂)) = x
        rw [zero_smul, add_zero, map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
      · change e₂ (1 ⊗ₜ _) = y
        rw [tmul_add, tmul_smul, tmul_smul, ← hn₂, ← algebraMap_smul R₂ ((x, 0) : R),
          ← algebraMap_smul R₂ ((0, y) : R), a₂, a₂]
        change e₂ ((0 : R₂) • (1 ⊗ₜ n₁) + y • e₂.symm 1) = y
        rw [zero_smul, zero_add, map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  rw [← CommRing.Pic.mk_eq_self (M := P), CommRing.Pic.mk_eq_one_iff]
  exact ⟨LinearEquiv.ofBijective F hF⟩

end ProdPic

namespace TwoGluedLines

variable {k : Type u} [Field k] {ι : Type v} (a b : ι → k)

noncomputable def evA : (k[X] × k[X]) →ₐ[k] (ι → k) :=
  Pi.algHom k (fun _ : ι => k) fun i => (Polynomial.aeval (a i)).comp (AlgHom.fst k k[X] k[X])

noncomputable def evB : (k[X] × k[X]) →ₐ[k] (ι → k) :=
  Pi.algHom k (fun _ : ι => k) fun i => (Polynomial.aeval (b i)).comp (AlgHom.snd k k[X] k[X])

@[scoped simp] theorem evA_apply (p : k[X] × k[X]) (i : ι) : evA a p i = (p.1).eval (a i) := by
  simp [evA, Polynomial.coe_aeval_eq_eval]

@[scoped simp] theorem evB_apply (p : k[X] × k[X]) (i : ι) : evB b p i = (p.2).eval (b i) := by
  simp [evB, Polynomial.coe_aeval_eq_eval]

noncomputable abbrev R : Subalgebra k (k[X] × k[X]) := AlgHom.equalizer (evA a) (evB b)

theorem mem_R {p : k[X] × k[X]} : p ∈ R a b ↔ ∀ i, (p.1).eval (a i) = (p.2).eval (b i) := by
  rw [AlgHom.mem_equalizer, funext_iff]
  simp only [evA_apply, evB_apply]

noncomputable def cond : Ideal (k[X] × k[X]) := RingHom.ker (evA a) ⊓ RingHom.ker (evB b)

theorem mem_cond {p : k[X] × k[X]} :
    p ∈ cond a b ↔ (∀ i, (p.1).eval (a i) = 0) ∧ ∀ i, (p.2).eval (b i) = 0 := by
  rw [cond, Ideal.mem_inf, RingHom.mem_ker, RingHom.mem_ker, funext_iff, funext_iff]
  simp only [evA_apply, evB_apply, Pi.zero_apply]

theorem mem_R_of_mem_cond {p : k[X] × k[X]} (hp : p ∈ cond a b) : p ∈ R a b := by
  rw [mem_cond] at hp; rw [mem_R]; intro i; rw [hp.1 i, hp.2 i]

theorem mk_eq_mk_iff {p q : k[X] × k[X]} :
    Ideal.Quotient.mk (cond a b) p = Ideal.Quotient.mk (cond a b) q ↔
      (∀ i, (p.1).eval (a i) = (q.1).eval (a i)) ∧ ∀ i, (p.2).eval (b i) = (q.2).eval (b i) := by
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, mem_cond]
  simp only [Prod.fst_sub, Prod.snd_sub, eval_sub, sub_eq_zero]

section interp

variable [Fintype ι] [DecidableEq ι]

noncomputable def LA (v : ι → k) : k[X] := Lagrange.interpolate Finset.univ a v

noncomputable def LB (v : ι → k) : k[X] := Lagrange.interpolate Finset.univ b v

variable {a b}

theorem eval_LA (ha : Function.Injective a) (v : ι → k) (i : ι) : (LA a v).eval (a i) = v i :=
  Lagrange.eval_interpolate_at_node v ha.injOn (Finset.mem_univ i)

theorem eval_LB (hb : Function.Injective b) (v : ι → k) (i : ι) : (LB b v).eval (b i) = v i :=
  Lagrange.eval_interpolate_at_node v hb.injOn (Finset.mem_univ i)

theorem LA_LB_mem_R (ha : Function.Injective a) (hb : Function.Injective b) (v : ι → k) :
    (LA a v, LB b v) ∈ R a b := by
  rw [mem_R]; intro i; simp only [eval_LA ha, eval_LB hb]

end interp

end TwoGluedLines
p2m_reactivate "P2MW.S_CommRing_Pic_exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const.TwoGluedLines"

namespace TwoGluedLines

variable {k : Type u} [Field k] {ι : Type v} (a b : ι → k)

local notation "B" => (k[X] × k[X])

theorem algebraMap_R_apply (r : ↥(R a b)) : algebraMap (↥(R a b)) B r = (r : B) := rfl

theorem cond_subset_range : ∀ p ∈ cond a b, p ∈ Set.range (algebraMap (↥(R a b)) B) :=
  fun p hp => ⟨⟨p, mem_R_of_mem_cond a b hp⟩, rfl⟩

noncomputable abbrev condA : Ideal ↥(R a b) := (cond a b).comap (algebraMap (↥(R a b)) B)

section theta

variable [Fintype ι] [DecidableEq ι]
variable {b} (hb : Function.Injective b)
include hb

noncomputable def theta : (ι → kˣ) →* (B ⧸ cond a b)ˣ where
  toFun w :=
    { val := Ideal.Quotient.mk (cond a b) (1, LB b fun i => (w i : k))
      inv := Ideal.Quotient.mk (cond a b) (1, LB b fun i => ((w i)⁻¹ : kˣ))
      val_inv := by
        rw [← map_mul, ← map_one (Ideal.Quotient.mk (cond a b)), mk_eq_mk_iff]
        refine ⟨fun i => by simp, fun i => ?_⟩
        simp only [Prod.snd_mul, eval_mul, eval_LB hb, Prod.snd_one, eval_one, Units.mul_inv]
      inv_val := by
        rw [← map_mul, ← map_one (Ideal.Quotient.mk (cond a b)), mk_eq_mk_iff]
        refine ⟨fun i => by simp, fun i => ?_⟩
        simp only [Prod.snd_mul, eval_mul, eval_LB hb, Prod.snd_one, eval_one, Units.inv_mul] }
  map_one' := by
    apply Units.ext
    change Ideal.Quotient.mk (cond a b) (1, LB b fun i => ((1 : ι → kˣ) i : k)) = 1
    rw [← map_one (Ideal.Quotient.mk (cond a b)), mk_eq_mk_iff]
    refine ⟨fun i => by simp, fun i => ?_⟩
    simp only [eval_LB hb, Pi.one_apply, Units.val_one, Prod.snd_one, eval_one]
  map_mul' w w' := by
    apply Units.ext
    change Ideal.Quotient.mk (cond a b) (1, LB b fun i => ((w * w') i : k)) =
      Ideal.Quotient.mk (cond a b) (1, LB b fun i => (w i : k)) *
        Ideal.Quotient.mk (cond a b) (1, LB b fun i => (w' i : k))
    rw [← map_mul, mk_eq_mk_iff]
    refine ⟨fun i => by simp, fun i => ?_⟩
    simp only [eval_LB hb, Pi.mul_apply, Units.val_mul, Prod.snd_mul, eval_mul]

theorem coe_theta (w : ι → kˣ) :
    (theta a hb w : B ⧸ cond a b) = Ideal.Quotient.mk (cond a b) (1, LB b fun i => (w i : k)) := rfl

variable (ha : Function.Injective a)
include ha

theorem exists_theta_mul_mk_eq_iff (w : ι → kˣ) (x : B) :
    (∃ r : ↥(R a b), (theta a hb w : B ⧸ cond a b) * Ideal.Quotient.mk (cond a b) x =
        Ideal.Quotient.mk (cond a b) (algebraMap (↥(R a b)) B r)) ↔
      ∀ i, (x.1).eval (a i) = (w i : k) * (x.2).eval (b i) := by
  constructor
  · rintro ⟨r, hr⟩
    rw [coe_theta, ← map_mul, algebraMap_R_apply, mk_eq_mk_iff] at hr
    obtain ⟨h1, h2⟩ := hr
    have hR := (mem_R a b).mp r.2
    intro i
    have e1 := h1 i
    have e2 := h2 i
    simp only [Prod.fst_mul, Prod.fst_one, one_mul] at e1
    simp only [Prod.snd_mul, eval_mul, eval_LB hb] at e2
    rw [e1, hR i, e2]
  · intro h
    refine ⟨⟨(LA a fun i => (x.1).eval (a i), LB b fun i => (x.1).eval (a i)), LA_LB_mem_R ha hb _⟩, ?_⟩
    rw [coe_theta, ← map_mul, algebraMap_R_apply, mk_eq_mk_iff]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simp only [Prod.fst_mul, Prod.fst_one, one_mul, eval_LA ha]
    · simp only [Prod.snd_mul, eval_mul, eval_LB hb, h i]

end theta
p2m_reactivate "P2MW.S_CommRing_Pic_exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const.TwoGluedLines"

section kernel

variable [Fintype ι] [DecidableEq ι]
variable {b} (hb : Function.Injective b)
include hb

omit [Fintype ι] [DecidableEq ι] hb in

theorem exists_eq_C_of_isUnit (t : Bˣ) :
    ∃ c₁ c₂ : k, c₁ ≠ 0 ∧ c₂ ≠ 0 ∧ (t : B) = (C c₁, C c₂) := by
  have h1 : IsUnit (t : B).1 := (Units.map (RingHom.fst k[X] k[X]).toMonoidHom t).isUnit
  have h2 : IsUnit (t : B).2 := (Units.map (RingHom.snd k[X] k[X]).toMonoidHom t).isUnit
  rw [Polynomial.isUnit_iff] at h1 h2
  obtain ⟨c₁, hc₁, e₁⟩ := h1
  obtain ⟨c₂, hc₂, e₂⟩ := h2
  exact ⟨c₁, c₂, hc₁.ne_zero, hc₂.ne_zero, Prod.ext e₁.symm e₂.symm⟩

theorem theta_eq_iff_const (w : ι → kˣ) :
    (∃ (t : Bˣ) (α : ((↥(R a b)) ⧸ condA a b)ˣ),
        (theta a hb w : B ⧸ cond a b) =
          Ideal.quotientMap (cond a b) (algebraMap (↥(R a b)) B) le_rfl (α : (↥(R a b)) ⧸ condA a b) *
            Ideal.Quotient.mk (cond a b) (t : B)) ↔
      ∃ c : kˣ, w = Function.const ι c := by
  constructor
  · rintro ⟨t, α, h⟩
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (α : (↥(R a b)) ⧸ condA a b)
    obtain ⟨c₁, c₂, hc₁, hc₂, ht⟩ := exists_eq_C_of_isUnit t
    rw [← hr, Ideal.quotientMap_mk, algebraMap_R_apply, ← map_mul, coe_theta, mk_eq_mk_iff, ht] at h
    obtain ⟨h1, h2⟩ := h
    have hR := (mem_R a b).mp r.2
    refine ⟨Units.mk0 (c₁⁻¹ * c₂) (mul_ne_zero (inv_ne_zero hc₁) hc₂), funext fun i => Units.ext ?_⟩
    have e1 := h1 i
    have e2 := h2 i
    simp only [Prod.fst_one, eval_one, Prod.fst_mul, eval_mul, eval_C] at e1
    simp only [eval_LB hb, Prod.snd_mul, eval_mul, eval_C] at e2
    rw [Function.const_apply, Units.val_mk0, e2, ← hR i, eq_inv_mul_iff_mul_eq₀ hc₁, mul_comm,
      mul_right_comm, ← e1, one_mul]
  · rintro ⟨c, rfl⟩
    refine ⟨⟨(1, C (c : k)), (1, C ((c⁻¹ : kˣ) : k)), ?_, ?_⟩, 1, ?_⟩
    · rw [Prod.mk_mul_mk, one_mul, ← map_mul, Units.mul_inv, map_one]; rfl
    · rw [Prod.mk_mul_mk, one_mul, ← map_mul, Units.inv_mul, map_one]; rfl
    · rw [Units.val_one, map_one, one_mul, coe_theta, mk_eq_mk_iff]
      exact ⟨fun i => rfl, fun i => by simp only [eval_LB hb, Function.const_apply, eval_C]⟩

end kernel
p2m_reactivate "P2MW.S_CommRing_Pic_exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const.TwoGluedLines"

section finiteness

variable [Finite ι]

set_option synthInstance.maxHeartbeats 1600000

theorem subsingleton_pic_quotient : Subsingleton (CommRing.Pic ((↥(R a b)) ⧸ condA a b)) := by
  let φ : (↥(R a b)) →ₐ[k] (ι → k) := (evA a).comp (R a b).val
  have hφ : ∀ r : ↥(R a b), r ∈ condA a b → φ r = 0 := fun r hr => by
    rw [Ideal.mem_comap, algebraMap_R_apply, cond, Ideal.mem_inf, RingHom.mem_ker] at hr
    exact hr.1
  let φ' : ((↥(R a b)) ⧸ condA a b) →ₐ[k] (ι → k) := Ideal.Quotient.liftₐ (condA a b) φ hφ
  have hinj : Function.Injective φ' := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change φ r = 0 at hx
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap, algebraMap_R_apply, cond, Ideal.mem_inf,
      RingHom.mem_ker, RingHom.mem_ker]
    have hr : evA a (r : B) = evB b (r : B) := (AlgHom.mem_equalizer _ _ _).mp r.2
    exact ⟨hx, hr ▸ hx⟩
  cases nonempty_fintype ι
  haveI : FiniteDimensional k ((↥(R a b)) ⧸ condA a b) := FiniteDimensional.of_injective φ'.toLinearMap hinj
  haveI : IsArtinianRing k := inferInstance
  haveI : IsArtinianRing ((↥(R a b)) ⧸ condA a b) := IsArtinianRing.of_finite k ((↥(R a b)) ⧸ condA a b)
  haveI : Finite (MaximalSpectrum ((↥(R a b)) ⧸ condA a b)) := inferInstance
  exact CommRing.Pic.instSubsingletonOfFiniteMaximalSpectrum ((↥(R a b)) ⧸ condA a b)

omit [Finite ι] in

theorem pic_prod_eq_one (Q : CommRing.Pic (k[X] × k[X])) : Q = 1 :=
  ProdPic.CommRing.Pic.eq_one_of_mapRingHom_fst_snd Q (Subsingleton.elim _ _) (Subsingleton.elim _ _)

end finiteness
p2m_reactivate "P2MW.S_CommRing_Pic_exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const.TwoGluedLines"

section main

variable {a b}

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in

theorem exists_surjective_hom_pic [Finite ι] (ha : Function.Injective a) (hb : Function.Injective b) :
    ∃ δ : (ι → kˣ) →* CommRing.Pic ↥(R a b),
      Function.Surjective δ ∧
      (∀ w : ι → kˣ, δ w = 1 ↔ ∃ c : kˣ, w = Function.const ι c) ∧
      ∀ w : ι → kˣ, ∃ N : Submodule ↥(R a b) (k[X] × k[X]),
        (∀ p : k[X] × k[X], p ∈ N ↔ ∀ i, (p.1).eval (a i) = (w i : k) * (p.2).eval (b i)) ∧
        Nonempty ((δ w : CommRing.Pic ↥(R a b)) ≃ₗ[↥(R a b)] ↥N) := by
  cases nonempty_fintype ι
  classical
  obtain ⟨δ₁, hval, hker, hrange, -⟩ :=
    CommRing.Pic.exists_boundaryHom_conductorSquare_exact (A := ↥(R a b)) (cond a b)
      (cond_subset_range a b)
  refine ⟨δ₁.comp (theta a hb), ?_, ?_, ?_⟩
  ·
    intro P
    haveI := subsingleton_pic_quotient a b
    obtain ⟨u, hu⟩ := (hrange P).mpr ⟨pic_prod_eq_one _, Subsingleton.elim _ _⟩
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (u : B ⧸ cond a b)
    obtain ⟨p', hp'⟩ := Ideal.Quotient.mk_surjective (↑u⁻¹ : B ⧸ cond a b)
    have hpp' : Ideal.Quotient.mk (cond a b) (p * p') = Ideal.Quotient.mk (cond a b) 1 := by
      rw [map_mul, hp, hp', Units.mul_inv, map_one]
    rw [mk_eq_mk_iff] at hpp'
    obtain ⟨h1, h2⟩ := hpp'
    have hp1 : ∀ i, (p.1).eval (a i) * (p'.1).eval (a i) = 1 := fun i => by
      simpa only [Prod.fst_mul, eval_mul, Prod.fst_one, eval_one] using h1 i
    have hp2 : ∀ i, (p.2).eval (b i) * (p'.2).eval (b i) = 1 := fun i => by
      simpa only [Prod.snd_mul, eval_mul, Prod.snd_one, eval_one] using h2 i
    let w : ι → kˣ := fun i => Units.mk0 ((p'.1).eval (a i) * (p.2).eval (b i))
      (mul_ne_zero (right_ne_zero_of_mul_eq_one (hp1 i)) (left_ne_zero_of_mul_eq_one (hp2 i)))
    refine ⟨w, ?_⟩
    have key : δ₁ (u⁻¹ * theta a hb w) = 1 := by
      rw [hker]
      let v : ι → k := fun i => (p'.1).eval (a i)
      let r : ↥(R a b) := ⟨(LA a v, LB b v), LA_LB_mem_R ha hb v⟩
      let r' : ↥(R a b) :=
        ⟨(LA a fun i => (p.1).eval (a i), LB b fun i => (p.1).eval (a i)), LA_LB_mem_R ha hb _⟩
      have hrr' : Ideal.Quotient.mk (condA a b) r * Ideal.Quotient.mk (condA a b) r' = 1 := by
        rw [← map_mul, ← map_one (Ideal.Quotient.mk (condA a b)),
          Ideal.Quotient.mk_eq_mk_iff_sub_mem, Ideal.mem_comap, map_sub, map_one, map_mul,
          algebraMap_R_apply, algebraMap_R_apply, ← Ideal.Quotient.mk_eq_mk_iff_sub_mem, mk_eq_mk_iff]
        refine ⟨fun i => ?_, fun i => ?_⟩
        · simp only [r, r', v, Prod.fst_mul, eval_mul, eval_LA ha, Prod.fst_one, eval_one]
          rw [mul_comm]; exact hp1 i
        · simp only [r, r', v, Prod.snd_mul, eval_mul, eval_LB hb, Prod.snd_one, eval_one]
          rw [mul_comm]; exact hp1 i
      have hr'r : Ideal.Quotient.mk (condA a b) r' * Ideal.Quotient.mk (condA a b) r = 1 := by
        rw [← map_mul, mul_comm, map_mul]; exact hrr'
      let α : ((↥(R a b)) ⧸ condA a b)ˣ :=
        ⟨Ideal.Quotient.mk (condA a b) r, Ideal.Quotient.mk (condA a b) r', hrr', hr'r⟩
      have hα : (α : (↥(R a b)) ⧸ condA a b) = Ideal.Quotient.mk (condA a b) r := rfl
      refine ⟨1, α, ?_⟩
      rw [Units.val_mul, coe_theta, ← hp', ← map_mul, Units.val_one, map_one, mul_one, hα,
        Ideal.quotientMap_mk, algebraMap_R_apply, mk_eq_mk_iff]
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simp only [Prod.fst_mul, Prod.fst_one, mul_one, eval_LA ha, r, v]
      · simp only [Prod.snd_mul, eval_mul, eval_LB hb, r, v, w, Units.val_mk0]
        rw [mul_left_comm, mul_comm ((p'.2).eval (b i)), hp2 i, mul_one]
    calc δ₁ (theta a hb w) = δ₁ (u * (u⁻¹ * theta a hb w)) := by rw [mul_inv_cancel_left]
      _ = P := by rw [map_mul, key, mul_one, hu]
  · intro w
    rw [MonoidHom.comp_apply, hker]
    exact theta_eq_iff_const a hb w
  · intro w
    obtain ⟨I, hI, hIso⟩ := hval (theta a hb w)
    refine ⟨I, fun p => ?_, hIso⟩
    rw [hI]
    exact exists_theta_mul_mk_eq_iff a hb ha w p

end main
p2m_reactivate "P2MW.S_CommRing_Pic_exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const.TwoGluedLines"

end TwoGluedLines
p2m_reactivate "P2MW.S_CommRing_Pic_exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const.TwoGluedLines"

theorem solution
    {k : Type u} [Field k] {ι : Type v} [Finite ι] (a b : ι → k)
    (ha : Function.Injective a) (hb : Function.Injective b) :
    let R : Subalgebra k (k[X] × k[X]) :=
      AlgHom.equalizer
        (Pi.algHom k (fun _ : ι => k) fun i => (Polynomial.aeval (a i)).comp (AlgHom.fst k k[X] k[X]))
        (Pi.algHom k (fun _ : ι => k) fun i => (Polynomial.aeval (b i)).comp (AlgHom.snd k k[X] k[X]))
    ∃ δ : (ι → kˣ) →* CommRing.Pic ↥R,
      Function.Surjective δ ∧
      (∀ w : ι → kˣ, δ w = 1 ↔ ∃ c : kˣ, w = Function.const ι c) ∧
      ∀ w : ι → kˣ, ∃ N : Submodule ↥R (k[X] × k[X]),
        (∀ p : k[X] × k[X], p ∈ N ↔ ∀ i, (p.1).eval (a i) = (w i : k) * (p.2).eval (b i)) ∧
        Nonempty ((δ w : CommRing.Pic ↥R) ≃ₗ[↥R] ↥N) := by
  intro R
  exact TwoGluedLines.exists_surjective_hom_pic ha hb

end S_CommRing_Pic_exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const
end P2MW
export P2MW.S_CommRing_Pic_exists_surjective_hom_pic_twoAffineLinesGluedAt_eq_one_iff_const (solution)
