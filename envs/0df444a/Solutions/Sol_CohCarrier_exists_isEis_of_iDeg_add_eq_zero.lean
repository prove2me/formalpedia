-- Prove2me | solution 1 for CohCarrier.exists_isEis_of_iDeg_add_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/96f54a21-802e-5269-bdae-4e181a268ce1

import Definitions.Def_CohCarrier_Tower
import Definitions.Def_SchurMultiplierTrivial
import Theorems.Thm_CohCarrier_coresAdd_comp_subtype
import Theorems.Thm_CohCarrier_index_GammaHUpper_of_prime
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.Group.Commutator
import Mathlib.Tactic.Group
import Mathlib.Data.ZMod.Units
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero

set_option autoImplicit false

namespace IharaSolH25
namespace SchurBridge

universe u

def IsPerfectGroup (Q : Type u) [Group Q] : Prop := commutator Q = ⊤

section LemmaA

open scoped commutatorElement

variable {E : Type u} [Group E]

theorem commutatorElement_mul_left_of_mem_center {a z : E} (hz : z ∈ Subgroup.center E) (g : E) :
    ⁅a * z, g⁆ = ⁅a, g⁆ := by
  have h1 : z * g * z⁻¹ = g := by
    rw [← Subgroup.mem_center_iff.mp hz g, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * g * (a * z)⁻¹ * g⁻¹ = a * (z * g * z⁻¹) * a⁻¹ * g⁻¹ := by group
    _ = a * g * a⁻¹ * g⁻¹ := by rw [h1]

theorem commutatorElement_mul_right_of_mem_center {b z : E} (hz : z ∈ Subgroup.center E) (a : E) :
    ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have h2 : z * a⁻¹ * z⁻¹ = a⁻¹ := by
    rw [← Subgroup.mem_center_iff.mp hz a⁻¹, mul_inv_cancel_right]
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹ * z⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h2]

variable {Q : Type u} [Group Q]

theorem exists_retraction_of_central (π : E →* Q) (hπ : Function.Surjective π)
    (hZ : π.ker ≤ Subgroup.center E) (hperf : IsPerfectGroup Q) (hstem : Ihara.HasTrivialSchurMultiplier Q) :
    ∃ p : E →* ↥π.ker, ∀ z : ↥π.ker, p z = z := by
  classical
  set E' : Subgroup E := commutator E with hE'def

  have hmap : E'.map π = ⊤ := by
    rw [hE'def, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective π hπ,
      ← commutator_def]
    exact hperf

  have hsup : E' ⊔ π.ker = ⊤ := by
    rw [eq_top_iff]
    intro e _
    have he : π e ∈ E'.map π := by rw [hmap]; exact Subgroup.mem_top _
    obtain ⟨e', he', h⟩ := Subgroup.mem_map.mp he
    have hk : e'⁻¹ * e ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    rw [← mul_inv_cancel_left e' e]
    exact Subgroup.mul_mem_sup he' hk

  have hperfE' : ⁅E', E'⁆ = E' := by
    refine le_antisymm (Subgroup.commutator_le_self E') ?_
    conv_lhs => rw [hE'def, commutator_def]
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    have hg₁ : g₁ ∈ E' ⊔ π.ker := by rw [hsup]; exact Subgroup.mem_top _
    have hg₂ : g₂ ∈ E' ⊔ π.ker := by rw [hsup]; exact Subgroup.mem_top _
    obtain ⟨a, ha, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg₁
    obtain ⟨b, hb, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg₂
    rw [commutatorElement_mul_left_of_mem_center (hZ hz₁),
      commutatorElement_mul_right_of_mem_center (hZ hz₂)]
    exact Subgroup.commutator_mem_commutator ha hb

  have hcommE' : commutator ↥E' = ⊤ := by
    apply Subgroup.map_injective E'.subtype_injective
    rw [Subgroup.map_subtype_commutator, hperfE', ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hsurj' : Function.Surjective (π.comp E'.subtype) := by
    intro q
    have hq : q ∈ E'.map π := by rw [hmap]; exact Subgroup.mem_top _
    obtain ⟨e', he', h⟩ := Subgroup.mem_map.mp hq
    exact ⟨⟨e', he'⟩, h⟩
  have hcen' : (π.comp E'.subtype).ker ≤ Subgroup.center ↥E' := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
    have hxc : (x : E) ∈ Subgroup.center E := hZ (by rw [MonoidHom.mem_ker]; exact hx)
    rw [Subgroup.mem_center_iff] at hxc ⊢
    intro y
    exact Subtype.ext (hxc y)
  have hker' : (π.comp E'.subtype).ker = ⊥ :=
    hstem (↥E') (π.comp E'.subtype) hsurj' hcen' (by rw [hcommE']; exact le_top)

  have hdisj : ∀ z : E, z ∈ π.ker → z ∈ E' → z = 1 := by
    intro z hz hzE'
    have : (⟨z, hzE'⟩ : ↥E') ∈ (π.comp E'.subtype).ker := by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply]; exact hz
    rw [hker'] at this
    exact congrArg Subtype.val (Subgroup.mem_bot.mp this)
  let f : ↥π.ker →* E ⧸ E' := (QuotientGroup.mk' E').comp π.ker.subtype
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have hz' : (z : E) ∈ E' := (QuotientGroup.eq_one_iff _).mp hz
    exact Subtype.ext (hdisj z z.2 hz')
  have hfsurj : Function.Surjective f := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H e =>
      have he : e ∈ E' ⊔ π.ker := by rw [hsup]; exact Subgroup.mem_top _
      obtain ⟨a, ha, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp he
      refine ⟨⟨z, hz⟩, ?_⟩
      change ((z : E) : E ⧸ E') = ((a * z : E) : E ⧸ E')
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff a).mpr ha, one_mul]
  let φ : ↥π.ker ≃* E ⧸ E' := MulEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  refine ⟨φ.symm.toMonoidHom.comp (QuotientGroup.mk' E'), fun z => ?_⟩
  show φ.symm (f z) = z
  exact φ.symm_apply_apply z

end LemmaA

section Pushout

variable {G : Type u} [Group G] (K : Subgroup G) [hK : K.Normal] {M : Type u} [CommGroup M]
  (w : ↥K →* M)

def antidiag : ↥K →* M × G where
  toFun k := ((w k)⁻¹, (k : G))
  map_one' := by simp
  map_mul' a b := by
    ext
    · simp only [map_mul, mul_inv_rev, Prod.fst_mul, mul_comm]
    · simp

def Delta : Subgroup (M × G) := (antidiag K w).range

omit hK in
theorem mem_Delta_iff (x : M × G) : x ∈ Delta K w ↔ ∃ k : ↥K, ((w k)⁻¹, (k : G)) = x := Iff.rfl

variable (hw : ∀ (g : G) (k : ↥K), w ⟨g * k * g⁻¹, hK.conj_mem _ k.2 g⟩ = w k)
include hw

theorem Delta_normal : (Delta K w).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨k, rfl⟩ ⟨m, g⟩
  refine ⟨⟨g * k * g⁻¹, hK.conj_mem _ k.2 g⟩, ?_⟩
  ext
  · simp only [antidiag, MonoidHom.coe_mk, OneHom.coe_mk, hw, Prod.fst_mul, Prod.fst_inv,
      mul_inv_cancel_comm]
  · simp [antidiag]

end Pushout

section Bridge

variable {G : Type u} [Group G] (K : Subgroup G) [hK : K.Normal] {M : Type u} [CommGroup M]
  (w : ↥K →* M) (hw : ∀ (g : G) (k : ↥K), w ⟨g * k * g⁻¹, hK.conj_mem _ k.2 g⟩ = w k)
include hw

theorem invariantChar_extends_mul (hperf : IsPerfectGroup (G ⧸ K)) (hstem : Ihara.HasTrivialSchurMultiplier (G ⧸ K)) :
    ∃ x : G →* M, ∀ k : ↥K, x (k : G) = w k := by
  haveI : (Delta K w).Normal := Delta_normal K w hw

  let π₀ : M × G →* G ⧸ K := (QuotientGroup.mk' K).comp (MonoidHom.snd M G)
  have hπ₀ : Delta K w ≤ π₀.ker := by
    rintro _ ⟨k, rfl⟩
    rw [MonoidHom.mem_ker]
    show ((k : G) : G ⧸ K) = 1
    exact (QuotientGroup.eq_one_iff _).mpr k.2
  let π : (M × G) ⧸ Delta K w →* G ⧸ K := QuotientGroup.lift (Delta K w) π₀ hπ₀
  have hπmk : ∀ (m : M) (g : G), π ((m, g) : M × G) = (g : G ⧸ K) := fun m g =>
    QuotientGroup.lift_mk (Delta K w) hπ₀ (m, g)
  have hπsurj : Function.Surjective π := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g => exact ⟨(((1 : M), g) : M × G), hπmk 1 g⟩
  have hker : ∀ (m : M) (g : G), (((m, g) : M × G) : (M × G) ⧸ Delta K w) ∈ π.ker ↔ g ∈ K := by
    intro m g
    rw [MonoidHom.mem_ker, hπmk, QuotientGroup.eq_one_iff]

  have hslide : ∀ (m : M) (k : ↥K),
      (((m, (k : G)) : M × G) : (M × G) ⧸ Delta K w) = ((m * w k, (1 : G)) : M × G) := by
    intro m k
    rw [QuotientGroup.eq, mem_Delta_iff]
    refine ⟨k⁻¹, ?_⟩
    ext
    · simp
    · simp
  have hcen : π.ker ≤ Subgroup.center ((M × G) ⧸ Delta K w) := by
    intro z hz
    induction z using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨m, g⟩ := x
      have hg : g ∈ K := (hker m g).mp hz
      rw [hslide m ⟨g, hg⟩, Subgroup.mem_center_iff]
      intro y
      induction y using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        ext
        · simp [mul_comm]
        · simp

  obtain ⟨p, hp⟩ := exists_retraction_of_central π hπsurj hcen hperf hstem

  let θ : M →* ↥π.ker :=
    ((QuotientGroup.mk' (Delta K w)).comp (MonoidHom.inl M G)).codRestrict π.ker
      (fun m => (hker m 1).mpr K.one_mem)
  have hθ : ∀ m : M, ((θ m : ↥π.ker) : (M × G) ⧸ Delta K w) = (((m, (1 : G)) : M × G) : _) :=
    fun m => rfl
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have hm' : (((m, (1 : G)) : M × G) : (M × G) ⧸ Delta K w) = 1 := by
      rw [← hθ, hm]; rfl
    rw [QuotientGroup.eq_one_iff, mem_Delta_iff] at hm'
    obtain ⟨k, hk⟩ := hm'
    have hk1 : (k : G) = 1 := congrArg Prod.snd hk
    have hk1' : k = 1 := Subtype.ext hk1
    have := congrArg Prod.fst hk
    simp only [hk1', map_one, inv_one] at this
    exact this.symm
  have hθsurj : Function.Surjective θ := by
    rintro ⟨z, hz⟩
    induction z using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨m, g⟩ := x
      have hg : g ∈ K := (hker m g).mp hz
      refine ⟨m * w ⟨g, hg⟩, Subtype.ext ?_⟩
      rw [hθ]
      exact (hslide m ⟨g, hg⟩).symm
  let ψ : M ≃* ↥π.ker := MulEquiv.ofBijective θ ⟨hθinj, hθsurj⟩

  refine ⟨ψ.symm.toMonoidHom.comp (p.comp ((QuotientGroup.mk' (Delta K w)).comp (MonoidHom.inr M G))),
    fun k => ?_⟩
  show ψ.symm (p ((((1 : M), (k : G)) : M × G) : (M × G) ⧸ Delta K w)) = w k
  rw [hslide 1 k, one_mul, show ((((w k), (1 : G)) : M × G) : (M × G) ⧸ Delta K w) = (θ (w k) : ↥π.ker)
    from (hθ (w k)).symm, hp]
  exact ψ.symm_apply_apply (w k)

omit hw in

theorem invariantChar_extends (hperf : IsPerfectGroup (G ⧸ K)) (hstem : Ihara.HasTrivialSchurMultiplier (G ⧸ K))
    {A : Type u} [AddCommGroup A] (u : Additive ↥K →+ A)
    (hu : ∀ (g : G) (k : ↥K), u (Additive.ofMul ⟨g * k * g⁻¹, hK.conj_mem _ k.2 g⟩) =
      u (Additive.ofMul k)) :
    ∃ x : Additive G →+ A, ∀ k : ↥K, x (Additive.ofMul (k : G)) = u (Additive.ofMul k) := by
  obtain ⟨x, hx⟩ := invariantChar_extends_mul K (AddMonoidHom.toMultiplicativeRight u)
    (fun g k => by
      apply Multiplicative.toAdd.injective
      simpa [AddMonoidHom.toMultiplicativeRight] using hu g k) hperf hstem
  refine ⟨MonoidHom.toAdditiveLeft x, fun k => ?_⟩
  have := congrArg Multiplicative.toAdd (hx k)
  simpa [AddMonoidHom.toMultiplicativeRight, MonoidHom.toAdditiveLeft] using this

end Bridge

end IharaSolH25.SchurBridge

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

namespace IharaSolH25
namespace Q2Step

private def _root_.IharaSolH25.Q2Step.Gamma0Upper (q : ℕ) : Subgroup SL(2, ℤ) where
  carrier := { g | (g 0 1 : ZMod q) = 0 }
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    have h := (Matrix.two_mul_expl a.1 b.1).2.1
    simp only [Matrix.SpecialLinearGroup.coe_mul] at *
    rw [h]
    simp [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl a]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_neg, neg_eq_zero] at *
    exact ha

p2m_export "IharaSolH25.Q2Step" "Gamma0Upper"
variable (N q : ℕ)

abbrev GLow : Subgroup ↥(Gamma0 N) := (Gamma0 (N * q)).subgroupOf (Gamma0 N)

abbrev GUp : Subgroup ↥(Gamma0 N) := (Gamma0Upper q).subgroupOf (Gamma0 N)

abbrev GPrin : Subgroup ↥(Gamma0 N) := (Gamma q).subgroupOf (Gamma0 N)

theorem GPrin_le_GLow (hNq : Nat.Coprime N q) : GPrin N q ≤ GLow N q := by
  intro A hA
  rw [Subgroup.mem_subgroupOf] at hA ⊢
  rw [Gamma0_mem]
  have hA0 : (((A : SL(2, ℤ)) 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp A.2
  have hq : (((A : SL(2, ℤ)) 1 0 : ℤ) : ZMod q) = 0 := (Gamma_mem.mp hA).2.2.1
  have hdN : (N : ℤ) ∣ (A : SL(2, ℤ)) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hA0
  have hdq : (q : ℤ) ∣ (A : SL(2, ℤ)) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hq
  have hcop : IsCoprime (N : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr hNq
  have hd : ((N * q : ℕ) : ℤ) ∣ (A : SL(2, ℤ)) 1 0 := by
    push_cast
    exact hcop.mul_dvd hdN hdq
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd

theorem GPrin_le_GUp : GPrin N q ≤ GUp N q := by
  intro A hA
  rw [Subgroup.mem_subgroupOf] at hA ⊢
  exact (Gamma_mem.mp hA).2.1

scoped instance GPrin_normal : (GPrin N q).Normal :=
  haveI : (Gamma q).Normal := Gamma_normal q
  Subgroup.normal_subgroupOf

variable (A : Type*) [AddCommGroup A]

def IsUnitsChar (M : ℕ) {K : Subgroup ↥(Gamma0 N)} (φ : Additive ↥K →+ A) : Prop :=
  ∀ γ δ : ↥K,
    ((((γ : ↥(Gamma0 N)) : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ((((δ : ↥(Gamma0 N)) : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) →
    φ (Additive.ofMul γ) = φ (Additive.ofMul δ)

def IsUnitsChar0 (φ : Additive ↥(Gamma0 N) →+ A) : Prop :=
  ∀ γ δ : ↥(Gamma0 N), Gamma0Map N γ = Gamma0Map N δ → φ (Additive.ofMul γ) = φ (Additive.ofMul δ)

def InvariantCharExtends : Prop :=
  ∀ u : Additive ↥(GPrin N q) →+ A,
    (∀ (g : ↥(Gamma0 N)) (k : ↥(GPrin N q)),
        u (Additive.ofMul ⟨g * k * g⁻¹, (GPrin_normal N q).conj_mem _ k.2 g⟩) = u (Additive.ofMul k)) →
    ∃ x : Additive ↥(Gamma0 N) →+ A, ∀ k : ↥(GPrin N q),
      x (Additive.ofMul (k : ↥(Gamma0 N))) = u (Additive.ofMul k)

theorem GLow_sup_GUp (hq : q.Prime) (hqN : ¬ q ∣ N) : GLow N q ⊔ GUp N q = ⊤ := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hcop : IsCoprime (N : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqN).symm

  have key : ∀ γ : ↥(Gamma0 N), ¬ (q : ℤ) ∣ (γ : SL(2, ℤ)) 0 0 → γ ∈ GLow N q ⊔ GUp N q := by
    intro γ ha
    have hN' : ((N : ℕ) : ZMod q) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact hqN
    have ha' : (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod q) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact ha
    have hNa : ((N : ℕ) : ZMod q) * (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod q) ≠ 0 := mul_ne_zero hN' ha'
    set tbar : ZMod q := -(((γ : SL(2, ℤ)) 1 0 : ℤ) : ZMod q) *
      (((N : ℕ) : ZMod q) * (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod q))⁻¹ with htbar
    set t : ℤ := (tbar.val : ℤ) with ht
    have htq : (q : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 + t * ((N : ℤ) * (γ : SL(2, ℤ)) 0 0) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [ht]
      push_cast
      rw [ZMod.natCast_zmod_val, htbar, neg_mul, neg_mul, inv_mul_cancel_right₀ hNa, add_neg_cancel]

    let Lsl : SL(2, ℤ) := ⟨!![1, 0; t * N, 1], by rw [Matrix.det_fin_two_of]; ring⟩
    have hL0 : Lsl ∈ Gamma0 N := by
      rw [Gamma0_mem]
      show (((!![(1 : ℤ), 0; t * N, 1] 1 0 : ℤ)) : ZMod N) = 0
      simp
    let L : ↥(Gamma0 N) := ⟨Lsl, hL0⟩
    have hLUp : L ∈ GUp N q := by
      rw [Subgroup.mem_subgroupOf]
      show (((!![(1 : ℤ), 0; t * N, 1] 0 1 : ℤ)) : ZMod q) = 0
      simp
    have hLγ : L * γ ∈ GLow N q := by
      rw [Subgroup.mem_subgroupOf, Gamma0_mem]
      have hent : ((L * γ : ↥(Gamma0 N)) : SL(2, ℤ)) 1 0 = t * N * (γ : SL(2, ℤ)) 0 0 + (γ : SL(2, ℤ)) 1 0 := by
        show (Lsl * (γ : SL(2, ℤ))) 1 0 = _
        rw [Matrix.SpecialLinearGroup.coe_mul]
        simp [Lsl, Matrix.mul_apply, Fin.sum_univ_two]
      rw [hent, ZMod.intCast_zmod_eq_zero_iff_dvd]
      have hNc : (N : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp γ.2)
      have hN : (N : ℤ) ∣ t * N * (γ : SL(2, ℤ)) 0 0 + (γ : SL(2, ℤ)) 1 0 :=
        dvd_add (Dvd.intro_left (t * (γ : SL(2, ℤ)) 0 0) (by ring)) hNc
      have hq' : (q : ℤ) ∣ t * N * (γ : SL(2, ℤ)) 0 0 + (γ : SL(2, ℤ)) 1 0 := by
        rw [add_comm, mul_assoc]
        exact htq
      push_cast
      exact hcop.mul_dvd hN hq'
    rw [← inv_mul_cancel_left L γ]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.inv_mem _ hLUp)) (Subgroup.mem_sup_left hLγ)
  rw [eq_top_iff]
  rintro γ -
  by_cases ha : (q : ℤ) ∣ (γ : SL(2, ℤ)) 0 0
  ·
    have hc : ¬ (q : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := by
      intro hc
      have h1 : (γ : SL(2, ℤ)) 0 0 * (γ : SL(2, ℤ)) 1 1 - (γ : SL(2, ℤ)) 0 1 * (γ : SL(2, ℤ)) 1 0 = 1 := by
        rw [← Matrix.det_fin_two]
        exact (γ : SL(2, ℤ)).2
      have hq1 : (q : ℤ) ∣ 1 := h1 ▸ dvd_sub (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right hc _)
      have : q ∣ 1 := by exact_mod_cast hq1
      exact hq.ne_one (Nat.dvd_one.mp this)
    let Tg : ↥(Gamma0 N) := ⟨ModularGroup.T, by rw [Gamma0_mem, ModularGroup.coe_T]; simp⟩
    have hT : Tg ∈ GLow N q := by
      rw [Subgroup.mem_subgroupOf, Gamma0_mem]
      show (((!![(1 : ℤ), 1; 0, 1] 1 0 : ℤ)) : ZMod (N * q)) = 0
      simp
    have hTγ : ¬ (q : ℤ) ∣ ((Tg * γ : ↥(Gamma0 N)) : SL(2, ℤ)) 0 0 := by
      have hent : ((Tg * γ : ↥(Gamma0 N)) : SL(2, ℤ)) 0 0 = (γ : SL(2, ℤ)) 0 0 + (γ : SL(2, ℤ)) 1 0 := by
        show (ModularGroup.T * (γ : SL(2, ℤ))) 0 0 = _
        rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T]
        simp [Matrix.mul_apply, Fin.sum_univ_two]
      rw [hent]
      intro h
      exact hc ((dvd_add_right ha).mp h)
    rw [← inv_mul_cancel_left Tg γ]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.inv_mem _ hT)) (key (Tg * γ) hTγ)
  · exact key γ ha

section Unipotent

variable {F : Type*} [CommRing F]

theorem coe_pow_of_unipotent (P : Matrix.SpecialLinearGroup (Fin 2) F) (h10 : P.1 1 0 = 0) (h00 : P.1 0 0 = 1)
    (h11 : P.1 1 1 = 1) (n : ℕ) : (P ^ n).1 = !![1, (n : F) * P.1 0 1; 0, 1] := by
  induction n with
  | zero =>
    rw [pow_zero, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
    simp
  | succ n ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, Matrix.eta_fin_two P.1, h10, h00, h11,
      Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    ring

theorem pow_eq_one_of_unipotent {q : ℕ} (P : Matrix.SpecialLinearGroup (Fin 2) (ZMod q))
    (h10 : P.1 1 0 = 0) (h00 : P.1 0 0 = 1) (h11 : P.1 1 1 = 1) : P ^ q = 1 := by
  apply Subtype.ext
  rw [coe_pow_of_unipotent P h10 h00 h11 q, ZMod.natCast_self, zero_mul,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]

end Unipotent

abbrev redq (q : ℕ) : SL(2, ℤ) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod q) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))

theorem redq_apply (γ : SL(2, ℤ)) (i j : Fin 2) : (redq q γ).1 i j = ((γ i j : ℤ) : ZMod q) := rfl

theorem isUnitsChar_of_vanish_GPrin (hq : q.Prime) (hqN : ¬ q ∣ N) (hA : ∀ a : A, q • a = 0 → a = 0)
    (φ : Additive ↥(GLow N q) →+ A)
    (hφ : ∀ k : ↥(GPrin N q), φ (Additive.ofMul (Subgroup.inclusion
      (GPrin_le_GLow N q ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqN).symm) k)) = 0) :
    IsUnitsChar N A (N * q) φ := by
  intro γ δ hd

  have hc : ∀ ε : ↥(GLow N q), (redq q ((ε : ↥(Gamma0 N)) : SL(2, ℤ))).1 1 0 = 0 := by
    intro ε
    have hε : ((ε : ↥(Gamma0 N)) : SL(2, ℤ)) ∈ Gamma0 (N * q) := Subgroup.mem_subgroupOf.mp ε.2
    rw [Gamma0_mem] at hε
    have hdvd : ((N * q : ℕ) : ℤ) ∣ ((ε : ↥(Gamma0 N)) : SL(2, ℤ)) 1 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hε
    rw [redq_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (by push_cast; exact dvd_mul_left _ _) hdvd
  have hdet : ∀ ε : ↥(GLow N q),
      (redq q ((ε : ↥(Gamma0 N)) : SL(2, ℤ))).1 0 0 * (redq q ((ε : ↥(Gamma0 N)) : SL(2, ℤ))).1 1 1 = 1 := by
    intro ε
    have h := (redq q ((ε : ↥(Gamma0 N)) : SL(2, ℤ))).2
    rw [Matrix.det_fin_two, hc ε, mul_zero, sub_zero] at h
    exact h
  have hd' : (redq q ((γ : ↥(Gamma0 N)) : SL(2, ℤ))).1 1 1 = (redq q ((δ : ↥(Gamma0 N)) : SL(2, ℤ))).1 1 1 := by
    have h := congrArg (ZMod.castHom (dvd_mul_left q N) (ZMod q)) hd
    rwa [map_intCast, map_intCast] at h
  set g := redq q ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) with hg
  set h := redq q ((δ : ↥(Gamma0 N)) : SL(2, ℤ)) with hh
  have ha' : g.1 0 0 = h.1 0 0 := by
    have e1 := hdet γ
    have e2 := hdet δ
    rw [← hg] at e1
    rw [← hh] at e2
    calc g.1 0 0 = g.1 0 0 * (h.1 0 0 * h.1 1 1) := by rw [e2, mul_one]
      _ = (g.1 0 0 * g.1 1 1) * h.1 0 0 := by rw [hd']; ring
      _ = h.1 0 0 := by rw [e1, one_mul]

  set η : ↥(GLow N q) := γ * δ⁻¹ with hη
  have hP : redq q ((η : ↥(Gamma0 N)) : SL(2, ℤ)) = g * h⁻¹ := by
    rw [hη, hg, hh, ← map_inv, ← map_mul]
    rfl
  have hP10 : (g * h⁻¹).1 1 0 = 0 := by
    have hg10 : g.1 1 0 = 0 := hc γ
    have hh10 : h.1 1 0 = 0 := hc δ
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]
    simp [hg10, hh10]
  have hP00 : (g * h⁻¹).1 0 0 = 1 := by
    have hh10 : h.1 1 0 = 0 := hc δ
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]
    simp [hh10]
    rw [← hd']
    have e1 := hdet γ
    rwa [← hg] at e1
  have hP11 : (g * h⁻¹).1 1 1 = 1 := by
    have hg10 : g.1 1 0 = 0 := hc γ
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]
    simp [hg10]
    rw [← ha', mul_comm]
    have e1 := hdet γ
    rwa [← hg] at e1

  have hηq : (((η ^ q : ↥(GLow N q)) : ↥(Gamma0 N)) : SL(2, ℤ)) ∈ Gamma q := by
    rw [Gamma_mem']
    show redq q _ = 1
    have : (((η ^ q : ↥(GLow N q)) : ↥(Gamma0 N)) : SL(2, ℤ)) = (((η : ↥(GLow N q)) : ↥(Gamma0 N)) : SL(2, ℤ)) ^ q := by
      simp
    rw [this, map_pow, hP]
    exact pow_eq_one_of_unipotent _ hP10 hP00 hP11

  have hk : φ (Additive.ofMul (η ^ q)) = 0 := by
    have := hφ ⟨((η ^ q : ↥(GLow N q)) : ↥(Gamma0 N)), Subgroup.mem_subgroupOf.mpr hηq⟩
    exact this
  have hφη : φ (Additive.ofMul η) = 0 := by
    apply hA
    rw [← map_nsmul, ← ofMul_pow]
    exact hk
  rw [← sub_eq_zero, ← map_sub, ← ofMul_div, div_eq_mul_inv]
  exact hφη

def invStab (u : Additive ↥(GPrin N q) →+ A) : Subgroup ↥(Gamma0 N) where
  carrier := { g | ∀ k : ↥(GPrin N q), u (Additive.ofMul (MulAut.conjNormal g k)) = u (Additive.ofMul k) }
  one_mem' := by
    intro k
    simp
  mul_mem' := by
    intro a b ha hb k
    rw [map_mul, MulAut.mul_apply, ha, hb]
  inv_mem' := by
    intro a ha k
    have h := ha ((MulAut.conjNormal a)⁻¹ k)
    rw [← map_inv] at h
    rw [← h, map_inv, MulAut.apply_inv_self]

theorem mem_invStab_iff (u : Additive ↥(GPrin N q) →+ A) (g : ↥(Gamma0 N)) :
    g ∈ invStab N q A u ↔
      ∀ k : ↥(GPrin N q), u (Additive.ofMul (MulAut.conjNormal g k)) = u (Additive.ofMul k) :=
  Iff.rfl

theorem conj_invariant_of_mem {K : Subgroup ↥(Gamma0 N)} (hPK : GPrin N q ≤ K)
    (z : Additive ↥K →+ A) (g : ↥(Gamma0 N)) (hg : g ∈ K) (k : ↥(GPrin N q)) :
    z (Additive.ofMul (Subgroup.inclusion hPK (MulAut.conjNormal g k))) =
      z (Additive.ofMul (Subgroup.inclusion hPK k)) := by
  have hmul : Subgroup.inclusion hPK (MulAut.conjNormal g k) =
      ⟨g, hg⟩ * Subgroup.inclusion hPK k * ⟨g, hg⟩⁻¹ := by
    ext
    simp [MulAut.conjNormal_apply, Subgroup.coe_inclusion]
  rw [hmul, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
  abel

theorem glue_mod_unitsChar (hq : q.Prime) (hqN : ¬ q ∣ N)
    (hA : ∀ a : A, q • a = 0 → a = 0)
    (hext : InvariantCharExtends N q A)
    (x : Additive ↥(GLow N q) →+ A) (y : Additive ↥(GUp N q) →+ A)
    (hagree : ∀ k : ↥(GPrin N q),
      x (Additive.ofMul (Subgroup.inclusion
        (GPrin_le_GLow N q ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqN).symm) k)) =
        y (Additive.ofMul (Subgroup.inclusion (GPrin_le_GUp N q) k))) :
    ∃ x' : Additive ↥(Gamma0 N) →+ A,
      IsUnitsChar N A (N * q) (x - x'.comp (GLow N q).subtype.toAdditive) ∧
      (∀ k : ↥(GPrin N q),
        (y - x'.comp (GUp N q).subtype.toAdditive)
          (Additive.ofMul (Subgroup.inclusion (GPrin_le_GUp N q) k)) = 0) := by
  set hLow := GPrin_le_GLow N q ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqN).symm with hLow_def

  let u : Additive ↥(GPrin N q) →+ A := x.comp (Subgroup.inclusion hLow).toAdditive
  have hu : ∀ k, u (Additive.ofMul k) = x (Additive.ofMul (Subgroup.inclusion hLow k)) := fun k => rfl

  have hLowStab : GLow N q ≤ invStab N q A u := by
    intro g hg
    rw [mem_invStab_iff]
    intro k
    rw [hu, hu]
    exact conj_invariant_of_mem N q A hLow x g hg k
  have hUpStab : GUp N q ≤ invStab N q A u := by
    intro g hg
    rw [mem_invStab_iff]
    intro k
    rw [hu, hu, hagree, hagree]
    exact conj_invariant_of_mem N q A (GPrin_le_GUp N q) y g hg k
  have hStab : invStab N q A u = ⊤ := by
    rw [eq_top_iff, ← GLow_sup_GUp N q hq hqN]
    exact sup_le hLowStab hUpStab
  have hinv : ∀ (g : ↥(Gamma0 N)) (k : ↥(GPrin N q)),
      u (Additive.ofMul ⟨g * k * g⁻¹, (GPrin_normal N q).conj_mem _ k.2 g⟩) = u (Additive.ofMul k) := by
    intro g k
    have hg : g ∈ invStab N q A u := by rw [hStab]; exact Subgroup.mem_top g
    have hk : (⟨g * k * g⁻¹, (GPrin_normal N q).conj_mem _ k.2 g⟩ : ↥(GPrin N q)) = MulAut.conjNormal g k :=
      Subtype.ext (MulAut.conjNormal_apply g k).symm
    rw [hk]
    exact (mem_invStab_iff N q A u g).mp hg k

  obtain ⟨x', hx'⟩ := hext u hinv
  refine ⟨x', ?_, ?_⟩
  ·
    apply isUnitsChar_of_vanish_GPrin N q A hq hqN hA
    intro k
    rw [AddMonoidHom.sub_apply, sub_eq_zero, ← hu, ← hx' k]
    rfl
  · intro k
    rw [AddMonoidHom.sub_apply, sub_eq_zero, ← hagree, ← hu, ← hx' k]
    rfl

abbrev GLow2 : Subgroup ↥(Gamma0 N) := (Gamma0 (N * q ^ 2)).subgroupOf (Gamma0 N)

theorem GLow2_le_GLow : GLow2 N q ≤ GLow N q := by
  intro γ hγ
  rw [Subgroup.mem_subgroupOf, Gamma0_mem] at hγ ⊢
  have h := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hγ
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (dvd_trans ?_ h)
  push_cast
  rw [pow_two, ← mul_assoc]
  exact Dvd.intro _ rfl

def IsConjDown (cq : ↥(GUp N q) →* ↥(GLow N q)) : Prop :=
  ∀ δ : ↥(GUp N q),
    (((cq δ : ↥(Gamma0 N)) : SL(2, ℤ)) 0 0 = ((δ : ↥(Gamma0 N)) : SL(2, ℤ)) 0 0) ∧
    ((q : ℤ) * ((cq δ : ↥(Gamma0 N)) : SL(2, ℤ)) 0 1 = ((δ : ↥(Gamma0 N)) : SL(2, ℤ)) 0 1) ∧
    (((cq δ : ↥(Gamma0 N)) : SL(2, ℤ)) 1 0 = (q : ℤ) * ((δ : ↥(Gamma0 N)) : SL(2, ℤ)) 1 0) ∧
    (((cq δ : ↥(Gamma0 N)) : SL(2, ℤ)) 1 1 = ((δ : ↥(Gamma0 N)) : SL(2, ℤ)) 1 1)

def IsConjUp (j₁ : ↥(GLow2 N q) →* ↥(GLow N q)) : Prop :=
  ∀ γ : ↥(GLow2 N q),
    (((j₁ γ : ↥(Gamma0 N)) : SL(2, ℤ)) 0 0 = ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) 0 0) ∧
    (((j₁ γ : ↥(Gamma0 N)) : SL(2, ℤ)) 0 1 = (q : ℤ) * ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) 0 1) ∧
    ((q : ℤ) * ((j₁ γ : ↥(Gamma0 N)) : SL(2, ℤ)) 1 0 = ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) 1 0) ∧
    (((j₁ γ : ↥(Gamma0 N)) : SL(2, ℤ)) 1 1 = ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) 1 1)

theorem cq_GPrin_mem_GLow2 (hq : q.Prime) (hqN : ¬ q ∣ N) (cq : ↥(GUp N q) →* ↥(GLow N q))
    (hcq : IsConjDown N q cq) (k : ↥(GPrin N q)) :
    (cq (Subgroup.inclusion (GPrin_le_GUp N q) k) : ↥(Gamma0 N)) ∈ GLow2 N q := by
  rw [Subgroup.mem_subgroupOf, Gamma0_mem, (hcq _).2.2.1]
  have hk : ((Subgroup.inclusion (GPrin_le_GUp N q) k : ↥(Gamma0 N)) : SL(2, ℤ)) =
      ((k : ↥(Gamma0 N)) : SL(2, ℤ)) := rfl
  rw [hk]
  have hkLow : (k : ↥(Gamma0 N)) ∈ GLow N q :=
    GPrin_le_GLow N q ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqN).symm k.2
  rw [Subgroup.mem_subgroupOf, Gamma0_mem] at hkLow
  obtain ⟨e, he⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hkLow
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ⟨e, ?_⟩
  rw [he]
  push_cast
  ring

theorem lemma25_gamma0 (hq : q.Prime) (hqN : ¬ q ∣ N)
    (hA : ∀ a : A, q • a = 0 → a = 0) (hext : InvariantCharExtends N q A)
    (cq : ↥(GUp N q) →* ↥(GLow N q)) (hcq : IsConjDown N q cq)
    (j₁ : ↥(GLow2 N q) →* ↥(GLow N q)) (hj₁ : IsConjUp N q j₁)
    (x z' : Additive ↥(GLow N q) →+ A)
    (hker : ∀ γ : ↥(GLow2 N q),
      x (Additive.ofMul (Subgroup.inclusion (GLow2_le_GLow N q) γ)) + z' (Additive.ofMul (j₁ γ)) = 0) :
    ∃ w : Additive ↥(Gamma0 N) →+ A,
      IsUnitsChar N A (N * q) (z' - w.comp (GLow N q).subtype.toAdditive) ∧
      (∀ k : ↥(GPrin N q),
        x (Additive.ofMul (cq (Subgroup.inclusion (GPrin_le_GUp N q) k))) + w (Additive.ofMul (k : ↥(Gamma0 N))) = 0) := by
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero

  let y : Additive ↥(GUp N q) →+ A := -(x.comp (MonoidHom.toAdditive cq))
  have hy : ∀ δ : ↥(GUp N q), y (Additive.ofMul δ) = -x (Additive.ofMul (cq δ)) := fun δ => rfl

  have hagree : ∀ k : ↥(GPrin N q),
      z' (Additive.ofMul (Subgroup.inclusion
        (GPrin_le_GLow N q ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqN).symm) k)) =
        y (Additive.ofMul (Subgroup.inclusion (GPrin_le_GUp N q) k)) := by
    intro k
    set δ : ↥(GUp N q) := Subgroup.inclusion (GPrin_le_GUp N q) k with hδ
    let γ : ↥(GLow2 N q) := ⟨(cq δ : ↥(Gamma0 N)), cq_GPrin_mem_GLow2 N q hq hqN cq hcq k⟩
    have hj0 : Subgroup.inclusion (GLow2_le_GLow N q) γ = cq δ := Subtype.ext rfl
    have hj1 : j₁ γ = Subgroup.inclusion
        (GPrin_le_GLow N q ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqN).symm) k := by
      apply Subtype.ext
      apply Subtype.ext
      apply Matrix.SpecialLinearGroup.ext
      obtain ⟨a1, b1, c1, d1⟩ := hj₁ γ
      obtain ⟨a2, b2, c2, d2⟩ := hcq δ
      have hγ : ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) = ((cq δ : ↥(Gamma0 N)) : SL(2, ℤ)) := rfl
      rw [hγ] at a1 b1 c1 d1
      have hkδ : ((δ : ↥(Gamma0 N)) : SL(2, ℤ)) = ((k : ↥(Gamma0 N)) : SL(2, ℤ)) := rfl
      intro i j
      show ((j₁ γ : ↥(Gamma0 N)) : SL(2, ℤ)) i j = ((k : ↥(Gamma0 N)) : SL(2, ℤ)) i j
      rw [← hkδ]
      fin_cases i <;> fin_cases j
      · exact a1.trans a2
      · simp only [Fin.zero_eta, Fin.mk_one]
        rw [b1, b2]
      · simp only [Fin.mk_one, Fin.zero_eta]
        apply mul_left_cancel₀ hq0
        rw [c1, c2]
      · exact d1.trans d2
    have h := hker γ
    rw [hj0, hj1] at h
    rw [hy, eq_neg_iff_add_eq_zero, add_comm]
    exact h
  obtain ⟨w, h1, h2⟩ := glue_mod_unitsChar N q A hq hqN hA hext z' y hagree
  refine ⟨w, h1, fun k => ?_⟩
  have h := h2 k
  rw [AddMonoidHom.sub_apply, sub_eq_zero, hy] at h

  rw [neg_eq_iff_eq_neg] at h
  rw [h, neg_add_eq_zero]
  rfl

end IharaSolH25.Q2Step
p2m_reactivate "P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25 P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25.Q2Step"
p2m_reactivate "P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25"

namespace IharaSolH25
namespace Q2Step

open CongruenceSubgroup
open scoped MatrixGroups

section SL2Gen

variable {F : Type*} [Field F]

def E12 (x : F) : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two_of]⟩
def E21 (y : F) : Matrix.SpecialLinearGroup (Fin 2) F := ⟨!![1, 0; y, 1], by simp [Matrix.det_fin_two_of]⟩

theorem SL2_decomp_of_ne (M : Matrix.SpecialLinearGroup (Fin 2) F) (hc : M.1 1 0 ≠ 0) :
    M = E12 ((M.1 0 0 - 1) / M.1 1 0) * E21 (M.1 1 0) * E12 ((M.1 1 1 - 1) / M.1 1 0) := by
  have hdet : M.1 0 0 * M.1 1 1 - M.1 0 1 * M.1 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact M.2
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [E12, E21, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp
  · ring
  · linear_combination (-1 : F) * hdet
  · ring

theorem subgroup_eq_top_of_elementary (H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    (h12 : ∀ x, E12 x ∈ H) (h21 : ∀ y, E21 y ∈ H) : H = ⊤ := by
  rw [eq_top_iff]
  rintro M -
  by_cases hc : M.1 1 0 = 0
  · have hdet : M.1 0 0 * M.1 1 1 - M.1 0 1 * M.1 1 0 = 1 := by
      rw [← Matrix.det_fin_two]; exact M.2
    have ha : M.1 0 0 ≠ 0 := by
      intro ha; rw [ha, hc] at hdet; simp at hdet
    set M' := E21 (1 : F) * M with hM'
    have hc' : M'.1 1 0 ≠ 0 := by
      have : M'.1 1 0 = M.1 0 0 + M.1 1 0 := by
        rw [hM', Matrix.SpecialLinearGroup.coe_mul]
        simp [E21, Matrix.mul_apply, Fin.sum_univ_two]
      rw [this, hc, add_zero]; exact ha
    have hmem : M' ∈ H := by
      rw [SL2_decomp_of_ne M' hc']
      exact H.mul_mem (H.mul_mem (h12 _) (h21 _)) (h12 _)
    rw [← inv_mul_cancel_left (E21 (1 : F)) M]
    exact H.mul_mem (H.inv_mem (h21 1)) hmem
  · rw [SL2_decomp_of_ne M hc]
    exact H.mul_mem (H.mul_mem (h12 _) (h21 _)) (h12 _)

end SL2Gen
p2m_reactivate "P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25 P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25.Q2Step"

variable (N q : ℕ)

theorem redq_Gamma0_surjective (hq : q.Prime) (hqN : ¬ q ∣ N) :
    Function.Surjective ((redq q).comp (Gamma0 N).subtype) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hN' : ((N : ℕ) : ZMod q) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hqN
  rw [← MonoidHom.range_eq_top]
  apply subgroup_eq_top_of_elementary
  · intro x
    let γsl : SL(2, ℤ) := ⟨!![1, (x.val : ℤ); 0, 1], by simp [Matrix.det_fin_two_of]⟩
    have hγ : γsl ∈ Gamma0 N := by
      rw [Gamma0_mem]
      show (((!![(1 : ℤ), (x.val : ℤ); 0, 1] 1 0 : ℤ)) : ZMod N) = 0
      simp
    refine ⟨⟨γsl, hγ⟩, ?_⟩
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    show (redq q γsl).1 i j = (E12 x).1 i j
    rw [redq_apply]
    fin_cases i <;> fin_cases j <;> simp [γsl, E12]
  · intro y
    let c : ℤ := (N : ℤ) * (((((N : ℕ) : ZMod q))⁻¹ * y).val : ℤ)
    let γsl : SL(2, ℤ) := ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two_of]⟩
    have hγ : γsl ∈ Gamma0 N := by
      rw [Gamma0_mem]
      show (((!![(1 : ℤ), 0; c, 1] 1 0 : ℤ)) : ZMod N) = 0
      simp [c]
    refine ⟨⟨γsl, hγ⟩, ?_⟩
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    show (redq q γsl).1 i j = (E21 y).1 i j
    rw [redq_apply]
    fin_cases i <;> fin_cases j <;> simp [γsl, E21, c, mul_inv_cancel_left₀ hN']

theorem ker_redq_Gamma0 : ((redq q).comp (Gamma0 N).subtype).ker = GPrin N q :=
  Subgroup.ext fun _ => Iff.rfl

noncomputable def quotientGPrinEquiv (hq : q.Prime) (hqN : ¬ q ∣ N) :
    ↥(Gamma0 N) ⧸ GPrin N q ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod q) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_redq_Gamma0 N q).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (redq_Gamma0_surjective N q hq hqN))

end IharaSolH25.Q2Step
p2m_reactivate "P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25 P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25.Q2Step"
p2m_reactivate "P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25 P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25.Q2Step"

namespace IharaSolH25
namespace SchurBridge

universe u

theorem isPerfectGroup_of_mulEquiv {Q Q' : Type u} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : IsPerfectGroup Q') : IsPerfectGroup Q := by
  unfold IsPerfectGroup at *
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ e.surjective,
    ← commutator_def, h]

theorem stemExtensionsTrivial_of_mulEquiv {Q Q' : Type u} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : Ihara.HasTrivialSchurMultiplier Q') : Ihara.HasTrivialSchurMultiplier Q := by
  intro E _ π hπ hcen hcomm
  have hker : (e.toMonoidHom.comp π).ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  have h' := h E (e.toMonoidHom.comp π) (e.surjective.comp hπ) (hker ▸ hcen) (hker ▸ hcomm)
  rwa [hker] at h'

end IharaSolH25.SchurBridge
p2m_reactivate "P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25 P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25.Q2Step"
p2m_reactivate "P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25 P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25.Q2Step"

namespace IharaSolH25
namespace Q2Step

open CongruenceSubgroup
open scoped MatrixGroups

theorem invariantCharExtends_of_SL2 (N q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N) (A : Type) [AddCommGroup A]
    (hperf : IharaSolH25.SchurBridge.IsPerfectGroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod q)))
    (hstem : Ihara.HasTrivialSchurMultiplier (Matrix.SpecialLinearGroup (Fin 2) (ZMod q))) :
    InvariantCharExtends N q A := by
  intro u hu
  have e := quotientGPrinEquiv N q hq hqN
  exact IharaSolH25.SchurBridge.invariantChar_extends (GPrin N q)
    (IharaSolH25.SchurBridge.isPerfectGroup_of_mulEquiv e hperf)
    (IharaSolH25.SchurBridge.stemExtensionsTrivial_of_mulEquiv e hstem) u hu

theorem glue_mod_unitsChar_of_SL2 (N q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N) (A : Type) [AddCommGroup A]
    (hA : ∀ a : A, q • a = 0 → a = 0)
    (hperf : IharaSolH25.SchurBridge.IsPerfectGroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod q)))
    (hstem : Ihara.HasTrivialSchurMultiplier (Matrix.SpecialLinearGroup (Fin 2) (ZMod q)))
    (x : Additive ↥(GLow N q) →+ A) (y : Additive ↥(GUp N q) →+ A)
    (hagree : ∀ k : ↥(GPrin N q),
      x (Additive.ofMul (Subgroup.inclusion
        (GPrin_le_GLow N q ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqN).symm) k)) =
        y (Additive.ofMul (Subgroup.inclusion (GPrin_le_GUp N q) k))) :
    ∃ x' : Additive ↥(Gamma0 N) →+ A,
      IsUnitsChar N A (N * q) (x - x'.comp (GLow N q).subtype.toAdditive) ∧
      (∀ k : ↥(GPrin N q),
        (y - x'.comp (GUp N q).subtype.toAdditive)
          (Additive.ofMul (Subgroup.inclusion (GPrin_le_GUp N q) k)) = 0) :=
  glue_mod_unitsChar N q A hq hqN hA (invariantCharExtends_of_SL2 N q hq hqN A hperf hstem) x y hagree

end IharaSolH25.Q2Step
p2m_reactivate "P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25 P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25.Q2Step"
p2m_reactivate "P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25 P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25.Q2Step"

namespace IharaSolH25
namespace Q2Step

open CongruenceSubgroup
open scoped MatrixGroups

variable (N q : ℕ)

theorem dvd_b_of_GUp (δ : ↥(GUp N q)) : (q : ℤ) ∣ ((δ : ↥(Gamma0 N)) : SL(2, ℤ)) 0 1 := by
  have h := δ.2
  rw [Subgroup.mem_subgroupOf] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

theorem dvd_c_of_Gamma0 (γ : ↥(Gamma0 N)) : (N : ℤ) ∣ ((γ : SL(2, ℤ)) 1 0) :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp γ.2)

def cqMat (δ : ↥(GUp N q)) : SL(2, ℤ) :=
  CohCarrier.conjUpperMat q ((δ : ↥(Gamma0 N)) : SL(2, ℤ)) (dvd_b_of_GUp N q δ)

theorem cqMat_apply_10 (δ : ↥(GUp N q)) :
    (cqMat N q δ) 1 0 = ((δ : ↥(Gamma0 N)) : SL(2, ℤ)) 1 0 * q := rfl

theorem cqMat_mem_Gamma0 (δ : ↥(GUp N q)) : cqMat N q δ ∈ Gamma0 N := by
  rw [Gamma0_mem, cqMat_apply_10]
  obtain ⟨e, he⟩ := dvd_c_of_Gamma0 N (δ : ↥(Gamma0 N))
  rw [he, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Dvd.intro (e * q) (by ring)

theorem cqMat_mem_GLow (δ : ↥(GUp N q)) :
    (⟨cqMat N q δ, cqMat_mem_Gamma0 N q δ⟩ : ↥(Gamma0 N)) ∈ GLow N q := by
  rw [Subgroup.mem_subgroupOf, Gamma0_mem]
  show (((cqMat N q δ) 1 0 : ℤ) : ZMod (N * q)) = 0
  rw [cqMat_apply_10]
  obtain ⟨e, he⟩ := dvd_c_of_Gamma0 N (δ : ↥(Gamma0 N))
  rw [he, ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  exact Dvd.intro e (by ring)

def cqHom : ↥(GUp N q) →* ↥(GLow N q) where
  toFun δ := ⟨⟨cqMat N q δ, cqMat_mem_Gamma0 N q δ⟩, cqMat_mem_GLow N q δ⟩
  map_one' := by
    apply Subtype.ext; apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    show (cqMat N q 1) i j = (1 : SL(2, ℤ)) i j
    fin_cases i <;> fin_cases j <;> simp [cqMat, CohCarrier.conjUpperMat]
  map_mul' a b := by
    apply Subtype.ext; apply Subtype.ext
    exact CohCarrier.conjUpperMat_mul q _ _ (dvd_b_of_GUp N q a) (dvd_b_of_GUp N q b)
      (dvd_b_of_GUp N q (a * b))

theorem cqHom_isConjDown : IsConjDown N q (cqHom N q) := by
  intro δ
  refine ⟨rfl, ?_, ?_, rfl⟩
  · show (q : ℤ) * (((δ : ↥(Gamma0 N)) : SL(2, ℤ)) 0 1 / q) = _
    exact Int.mul_ediv_cancel' (dvd_b_of_GUp N q δ)
  · show ((δ : ↥(Gamma0 N)) : SL(2, ℤ)) 1 0 * q = _
    exact mul_comm _ _

theorem dvd_c_of_GLow2 (γ : ↥(GLow2 N q)) : ((N * q ^ 2 : ℕ) : ℤ) ∣ ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) 1 0 := by
  have h := γ.2
  rw [Subgroup.mem_subgroupOf, Gamma0_mem] at h
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

theorem q_dvd_c_of_GLow2 (γ : ↥(GLow2 N q)) : (q : ℤ) ∣ ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) 1 0 :=
  dvd_trans (Dvd.intro (N * q) (by push_cast; ring)) (dvd_c_of_GLow2 N q γ)

def j1Mat (γ : ↥(GLow2 N q)) : SL(2, ℤ) :=
  CohCarrier.conjLowerMat q ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) (q_dvd_c_of_GLow2 N q γ)

theorem j1Mat_apply_10 (γ : ↥(GLow2 N q)) :
    (j1Mat N q γ) 1 0 = ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) 1 0 / q := rfl

theorem j1Mat_apply_10_eq (hq0 : (q : ℤ) ≠ 0) (γ : ↥(GLow2 N q)) :
    ∃ e : ℤ, (j1Mat N q γ) 1 0 = N * q * e := by
  obtain ⟨e, he⟩ := dvd_c_of_GLow2 N q γ
  refine ⟨e, ?_⟩
  rw [j1Mat_apply_10, he]
  push_cast
  rw [show (N : ℤ) * (q : ℤ) ^ 2 * e = (q : ℤ) * (N * q * e) by ring]
  exact Int.mul_ediv_cancel_left _ hq0

theorem j1Mat_mem_Gamma0 (hq0 : (q : ℤ) ≠ 0) (γ : ↥(GLow2 N q)) : j1Mat N q γ ∈ Gamma0 N := by
  rw [Gamma0_mem]
  obtain ⟨e, he⟩ := j1Mat_apply_10_eq N q hq0 γ
  rw [he, ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Dvd.intro (q * e) (by ring)

theorem j1Mat_mem_GLow (hq0 : (q : ℤ) ≠ 0) (γ : ↥(GLow2 N q)) :
    (⟨j1Mat N q γ, j1Mat_mem_Gamma0 N q hq0 γ⟩ : ↥(Gamma0 N)) ∈ GLow N q := by
  rw [Subgroup.mem_subgroupOf, Gamma0_mem]
  show (((j1Mat N q γ) 1 0 : ℤ) : ZMod (N * q)) = 0
  obtain ⟨e, he⟩ := j1Mat_apply_10_eq N q hq0 γ
  rw [he, ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  exact Dvd.intro e rfl

def j1Hom (hq0 : (q : ℤ) ≠ 0) : ↥(GLow2 N q) →* ↥(GLow N q) where
  toFun γ := ⟨⟨j1Mat N q γ, j1Mat_mem_Gamma0 N q hq0 γ⟩, j1Mat_mem_GLow N q hq0 γ⟩
  map_one' := by
    apply Subtype.ext; apply Subtype.ext
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    show (j1Mat N q 1) i j = (1 : SL(2, ℤ)) i j
    fin_cases i <;> fin_cases j <;> simp [j1Mat, CohCarrier.conjLowerMat]
  map_mul' a b := by
    apply Subtype.ext; apply Subtype.ext
    exact CohCarrier.conjLowerMat_mul q _ _ (q_dvd_c_of_GLow2 N q a) (q_dvd_c_of_GLow2 N q b)
      (q_dvd_c_of_GLow2 N q (a * b))

theorem j1Hom_isConjUp (hq0 : (q : ℤ) ≠ 0) : IsConjUp N q (j1Hom N q hq0) := by
  intro γ
  refine ⟨rfl, ?_, ?_, rfl⟩
  · show ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) 0 1 * q = _
    exact mul_comm _ _
  · show (q : ℤ) * (((γ : ↥(Gamma0 N)) : SL(2, ℤ)) 1 0 / q) = _
    exact Int.mul_ediv_cancel' (q_dvd_c_of_GLow2 N q γ)

theorem lemma25_gamma0_concrete (hq : q.Prime) (hqN : ¬ q ∣ N) (A : Type) [AddCommGroup A]
    (hA : ∀ a : A, q • a = 0 → a = 0)
    (hperf : IharaSolH25.SchurBridge.IsPerfectGroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod q)))
    (hstem : Ihara.HasTrivialSchurMultiplier (Matrix.SpecialLinearGroup (Fin 2) (ZMod q)))
    (x z' : Additive ↥(GLow N q) →+ A)
    (hker : ∀ γ : ↥(GLow2 N q),
      x (Additive.ofMul (Subgroup.inclusion (GLow2_le_GLow N q) γ)) +
        z' (Additive.ofMul (j1Hom N q (Int.natCast_ne_zero.mpr hq.ne_zero) γ)) = 0) :
    ∃ w : Additive ↥(Gamma0 N) →+ A,
      IsUnitsChar N A (N * q) (z' - w.comp (GLow N q).subtype.toAdditive) ∧
      (∀ k : ↥(GPrin N q),
        x (Additive.ofMul (cqHom N q (Subgroup.inclusion (GPrin_le_GUp N q) k))) +
          w (Additive.ofMul (k : ↥(Gamma0 N))) = 0) :=
  lemma25_gamma0 N q A hq hqN hA (invariantCharExtends_of_SL2 N q hq hqN A hperf hstem) (cqHom N q)
    (cqHom_isConjDown N q) (j1Hom N q _) (j1Hom_isConjUp N q _) x z' hker

end IharaSolH25.Q2Step
p2m_reactivate "P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25 P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25.Q2Step"
p2m_reactivate "P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25 P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25.Q2Step"

namespace IharaSolH25
namespace Dock
open CongruenceSubgroup IharaSolH25.Q2Step
open scoped MatrixGroups

variable (N q : ℕ)

theorem Gamma0_mul_le : Gamma0 (N * q) ≤ Gamma0 N := by
  intro A hA
  rw [Gamma0_mem] at hA ⊢
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hA ⊢
  exact dvd_trans (Int.natCast_dvd_natCast.mpr (dvd_mul_right N q)) hA

noncomputable def gLowEquiv : ↥(GLow N q) ≃* ↥(Gamma0 (N * q)) :=
  Subgroup.subgroupOfEquivOfLe (Gamma0_mul_le N q)

theorem gLowEquiv_coe (γ : ↥(GLow N q)) :
    ((gLowEquiv N q γ : ↥(Gamma0 (N * q))) : SL(2, ℤ)) = ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) := rfl

def gamma0EquivGammaHTop (M : ℕ) : ↥(Gamma0 M) ≃* ↥(CohCarrier.GammaH M ⊤) :=
  MulEquiv.subgroupCongr (CohCarrier.GammaH_top (M := M)).symm

theorem gamma0EquivGammaHTop_coe (M : ℕ) (γ : ↥(Gamma0 M)) :
    ((gamma0EquivGammaHTop M γ : ↥(CohCarrier.GammaH M ⊤)) : SL(2, ℤ)) = (γ : SL(2, ℤ)) := rfl

theorem mem_Gamma0Upper_iff (A : SL(2, ℤ)) :
    A ∈ IharaSolH25.Q2Step.Gamma0Upper q ↔ A ∈ CohCarrier.Gamma0Upper q := by
  rw [CohCarrier.mem_Gamma0Upper]; rfl

def gUpEquiv : ↥(GUp N q) ≃* ↥(CohCarrier.GammaHUpper N ⊤ q) where
  toFun δ := ⟨gamma0EquivGammaHTop N (δ : ↥(Gamma0 N)),
    Subgroup.mem_subgroupOf.mpr ((mem_Gamma0Upper_iff q _).mp (Subgroup.mem_subgroupOf.mp δ.2))⟩
  invFun γ := ⟨(gamma0EquivGammaHTop N).symm (γ : ↥(CohCarrier.GammaH N ⊤)),
    Subgroup.mem_subgroupOf.mpr ((mem_Gamma0Upper_iff q _).mpr (Subgroup.mem_subgroupOf.mp γ.2))⟩
  left_inv δ := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv γ := by apply Subtype.ext; apply Subtype.ext; rfl
  map_mul' a b := by apply Subtype.ext; apply Subtype.ext; rfl

theorem gUpEquiv_coe (δ : ↥(GUp N q)) :
    (((gUpEquiv N q δ : ↥(CohCarrier.GammaHUpper N ⊤ q)) : ↥(CohCarrier.GammaH N ⊤)) : SL(2, ℤ)) =
      ((δ : ↥(Gamma0 N)) : SL(2, ℤ)) := rfl

theorem dvd_c_of_GLow (γ : ↥(GLow N q)) : (q : ℤ) ∣ ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) 1 0 := by
  have h : ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) ∈ Gamma0 (N * q) := Subgroup.mem_subgroupOf.mp γ.2
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  exact dvd_trans (Int.natCast_dvd_natCast.mpr (dvd_mul_left q N)) h

def upMat (γ : ↥(GLow N q)) : SL(2, ℤ) :=
  CohCarrier.conjLowerMat q ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) (dvd_c_of_GLow N q γ)

theorem upMat_mem_Gamma0 (γ : ↥(GLow N q)) : upMat N q γ ∈ Gamma0 N := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]
  show (N : ℤ) ∣ ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) 1 0 / q
  have h : ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) ∈ Gamma0 (N * q) := Subgroup.mem_subgroupOf.mp γ.2
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  obtain ⟨e, he⟩ := h
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq; simp
  · refine ⟨e, ?_⟩
    rw [he]; push_cast
    rw [show (N : ℤ) * q * e = (N * e) * q by ring, Int.mul_ediv_cancel _ (by exact_mod_cast hq.ne')]

theorem upMat_mem_GUp (γ : ↥(GLow N q)) :
    (⟨upMat N q γ, upMat_mem_Gamma0 N q γ⟩ : ↥(Gamma0 N)) ∈ GUp N q := by
  rw [Subgroup.mem_subgroupOf]
  show (((upMat N q γ) 0 1 : ℤ) : ZMod q) = 0
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact Dvd.intro_left _ rfl

theorem upMat_apply_01 (γ : ↥(GLow N q)) :
    (upMat N q γ) 0 1 = ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) 0 1 * q := rfl

theorem upMat_apply_10 (γ : ↥(GLow N q)) :
    (upMat N q γ) 1 0 = ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) 1 0 / q := rfl

theorem conjLowerMat_cqMat (hq : 0 < q) (δ : ↥(GUp N q)) (h : (q : ℤ) ∣ (cqMat N q δ) 1 0) :
    CohCarrier.conjLowerMat q (cqMat N q δ) h = ((δ : ↥(Gamma0 N)) : SL(2, ℤ)) := by
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hb := dvd_b_of_GUp N q δ
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [CohCarrier.conjLowerMat, cqMat, CohCarrier.conjUpperMat, Matrix.of_apply,
      Int.ediv_mul_cancel hb, Int.mul_ediv_cancel _ hq0]

theorem conjUpperMat_upMat (hq : 0 < q) (γ : ↥(GLow N q)) (h : (q : ℤ) ∣ (upMat N q γ) 0 1) :
    CohCarrier.conjUpperMat q (upMat N q γ) h = ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) := by
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hc := dvd_c_of_GLow N q γ
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [CohCarrier.conjUpperMat, upMat, CohCarrier.conjLowerMat, Matrix.of_apply,
      Int.ediv_mul_cancel hc, Int.mul_ediv_cancel _ hq0]

noncomputable def cqEquiv (hq : 0 < q) : ↥(GUp N q) ≃* ↥(GLow N q) :=
  { cqHom N q with
    invFun := fun γ => ⟨⟨upMat N q γ, upMat_mem_Gamma0 N q γ⟩, upMat_mem_GUp N q γ⟩
    left_inv := fun δ => by
      apply Subtype.ext; apply Subtype.ext
      show upMat N q (cqHom N q δ) = _
      exact conjLowerMat_cqMat N q hq δ (dvd_c_of_GLow N q (cqHom N q δ))
    right_inv := fun γ => by
      apply Subtype.ext; apply Subtype.ext
      show cqMat N q ⟨⟨upMat N q γ, upMat_mem_Gamma0 N q γ⟩, upMat_mem_GUp N q γ⟩ = _
      exact conjUpperMat_upMat N q hq γ
        (dvd_b_of_GUp N q ⟨⟨upMat N q γ, upMat_mem_Gamma0 N q γ⟩, upMat_mem_GUp N q γ⟩) }

theorem cqEquiv_apply (hq : 0 < q) (δ : ↥(GUp N q)) : cqEquiv N q hq δ = cqHom N q δ := rfl

end IharaSolH25.Dock
p2m_reactivate "P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25 P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25.Q2Step"
p2m_reactivate "P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25 P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25.Q2Step"

namespace IharaSolH25
namespace Dock
open CongruenceSubgroup IharaSolH25.Q2Step
open scoped MatrixGroups

theorem conjLowerMat_one (A : SL(2, ℤ)) (h : ((1 : ℕ) : ℤ) ∣ A 1 0) :
    CohCarrier.conjLowerMat 1 A h = A := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [CohCarrier.conjLowerMat, Matrix.of_apply]

theorem coe_iotaDeg_one {M M' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ}
    (h : CohCarrier.LevelLE M M' H H' 1) (γ : ↥(CohCarrier.GammaH M' H')) :
    ((CohCarrier.iotaDeg M M' H H' 1 h γ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) = (γ : SL(2, ℤ)) :=
  conjLowerMat_one _ (h.dvd_entry γ)

theorem coe_iotaDeg_eq {M M' : ℕ} {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ} (q : ℕ)
    [NeZero q] (h : CohCarrier.LevelLE M M' H H' q) (γ : ↥(CohCarrier.GammaH M' H')) :
    ((CohCarrier.iotaDeg M M' H H' q h γ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) =
      CohCarrier.conjLowerMat q (γ : SL(2, ℤ)) (h.dvd_entry γ) := rfl

theorem coe_j1Hom (N q : ℕ) (hq0 : (q : ℤ) ≠ 0) (γ : ↥(GLow2 N q)) :
    (((j1Hom N q hq0 γ : ↥(GLow N q)) : ↥(Gamma0 N)) : SL(2, ℤ)) =
      CohCarrier.conjLowerMat q ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) (q_dvd_c_of_GLow2 N q γ) := rfl

theorem coe_cqHom_eq_conjL (N q : ℕ) (δ : ↥(GUp N q)) :
    (((cqHom N q δ : ↥(GLow N q)) : ↥(Gamma0 N)) : SL(2, ℤ)) =
      ((CohCarrier.conjL N ⊤ q (gUpEquiv N q δ) : ↥(CohCarrier.GammaH N ⊤)) : SL(2, ℤ)) := rfl

theorem coe_gUpEquiv_subtype (N q : ℕ) (δ : ↥(GUp N q)) :
    (((gUpEquiv N q δ : ↥(CohCarrier.GammaHUpper N ⊤ q)) : ↥(CohCarrier.GammaH N ⊤)) : SL(2, ℤ)) =
      ((δ : ↥(Gamma0 N)) : SL(2, ℤ)) := rfl

end IharaSolH25.Dock
p2m_reactivate "P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25 P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25.Q2Step"
p2m_reactivate "P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25 P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25.Q2Step"

namespace IharaSolH25
namespace Q2Step

open CongruenceSubgroup
open scoped MatrixGroups

theorem coe_pow_of_unipotent_lower {F : Type*} [CommRing F] (P : Matrix.SpecialLinearGroup (Fin 2) F)
    (h01 : P.1 0 1 = 0) (h00 : P.1 0 0 = 1) (h11 : P.1 1 1 = 1) (n : ℕ) :
    (P ^ n).1 = !![1, 0; (n : F) * P.1 1 0, 1] := by
  induction n with
  | zero =>
    rw [pow_zero, Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
    simp
  | succ n ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, Matrix.eta_fin_two P.1, h01, h00, h11,
      Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    ring

theorem pow_eq_one_of_unipotent_lower {q : ℕ} (P : Matrix.SpecialLinearGroup (Fin 2) (ZMod q))
    (h01 : P.1 0 1 = 0) (h00 : P.1 0 0 = 1) (h11 : P.1 1 1 = 1) : P ^ q = 1 := by
  apply Subtype.ext
  rw [coe_pow_of_unipotent_lower P h01 h00 h11 q, ZMod.natCast_self, zero_mul,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]

theorem isUnitsChar_of_vanish_GPrin_up (N q : ℕ) (A : Type*) [AddCommGroup A]
    (hA : ∀ a : A, q • a = 0 → a = 0) (φ : Additive ↥(GUp N q) →+ A)
    (hφ : ∀ k : ↥(GPrin N q), φ (Additive.ofMul (Subgroup.inclusion (GPrin_le_GUp N q) k)) = 0) :
    IsUnitsChar N A q φ := by
  intro γ δ hd
  have hb : ∀ ε : ↥(GUp N q), (redq q ((ε : ↥(Gamma0 N)) : SL(2, ℤ))).1 0 1 = 0 := by
    intro ε
    rw [redq_apply]
    exact Subgroup.mem_subgroupOf.mp ε.2
  have hdet : ∀ ε : ↥(GUp N q),
      (redq q ((ε : ↥(Gamma0 N)) : SL(2, ℤ))).1 0 0 * (redq q ((ε : ↥(Gamma0 N)) : SL(2, ℤ))).1 1 1 = 1 := by
    intro ε
    have h := (redq q ((ε : ↥(Gamma0 N)) : SL(2, ℤ))).2
    rw [Matrix.det_fin_two, hb ε, zero_mul, sub_zero] at h
    exact h
  have hd' : (redq q ((γ : ↥(Gamma0 N)) : SL(2, ℤ))).1 1 1 = (redq q ((δ : ↥(Gamma0 N)) : SL(2, ℤ))).1 1 1 := by
    rw [redq_apply, redq_apply]
    exact hd
  set g := redq q ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) with hg
  set h := redq q ((δ : ↥(Gamma0 N)) : SL(2, ℤ)) with hh
  have ha' : g.1 0 0 = h.1 0 0 := by
    have e1 := hdet γ
    have e2 := hdet δ
    rw [← hg] at e1
    rw [← hh] at e2
    calc g.1 0 0 = g.1 0 0 * (h.1 0 0 * h.1 1 1) := by rw [e2, mul_one]
      _ = (g.1 0 0 * g.1 1 1) * h.1 0 0 := by rw [hd']; ring
      _ = h.1 0 0 := by rw [e1, one_mul]

  set η : ↥(GUp N q) := γ * δ⁻¹ with hη
  have hP : redq q ((η : ↥(Gamma0 N)) : SL(2, ℤ)) = g * h⁻¹ := by
    rw [hη, hg, hh, ← map_inv, ← map_mul]
    rfl
  have hg01 : g.1 0 1 = 0 := hb γ
  have hh01 : h.1 0 1 = 0 := hb δ
  have hP01 : (g * h⁻¹).1 0 1 = 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]
    simp [hg01, hh01]
  have hP00 : (g * h⁻¹).1 0 0 = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]
    simp [hg01]
    rw [ha']
    have e2 := hdet δ
    rwa [← hh] at e2
  have hP11 : (g * h⁻¹).1 1 1 = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]
    simp [hh01]
    rw [hd', mul_comm]
    have e2 := hdet δ
    rwa [← hh] at e2

  have hηq : (((η ^ q : ↥(GUp N q)) : ↥(Gamma0 N)) : SL(2, ℤ)) ∈ Gamma q := by
    rw [Gamma_mem']
    show redq q _ = 1
    have : (((η ^ q : ↥(GUp N q)) : ↥(Gamma0 N)) : SL(2, ℤ)) =
        (((η : ↥(GUp N q)) : ↥(Gamma0 N)) : SL(2, ℤ)) ^ q := by
      simp
    rw [this, map_pow, hP]
    exact pow_eq_one_of_unipotent_lower _ hP01 hP00 hP11
  have hk : φ (Additive.ofMul (η ^ q)) = 0 :=
    hφ ⟨((η ^ q : ↥(GUp N q)) : ↥(Gamma0 N)), Subgroup.mem_subgroupOf.mpr hηq⟩
  have hφη : φ (Additive.ofMul η) = 0 := by
    apply hA
    rw [← map_nsmul, ← ofMul_pow]
    exact hk
  rw [← sub_eq_zero, ← map_sub, ← ofMul_div, div_eq_mul_inv]
  exact hφη

end IharaSolH25.Q2Step
p2m_reactivate "P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25 P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25.Q2Step"
p2m_reactivate "P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25 P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25.Q2Step"

namespace IharaSolH25
namespace D3Inst

open scoped MatrixGroups
open Polynomial CohCarrier CongruenceSubgroup IharaSolH25.Dock IharaSolH25.Q2Step

section EisT
variable (R : Type*) [CommRing R] (A : Type) [AddCommGroup A] [Module R A] (ℓ₀ : ℕ) [NeZero ℓ₀]

theorem heckeT_eq_coresAdd (M : ℕ) (H : Subgroup (ZMod M)ˣ) (F : H1 M H A) :
    heckeT M H ℓ₀ A F = coresAdd (GammaHUpper M H ℓ₀) (F.comp (MonoidHom.toAdditive (conjL M H ℓ₀))) := rfl

theorem heckeT_of_conjL_invariant' (M : ℕ) (H : Subgroup (ZMod M)ˣ) (F : H1 M H A)
    (hF : ∀ s : ↥(GammaHUpper M H ℓ₀),
      F (Additive.ofMul (conjL M H ℓ₀ s)) = F (Additive.ofMul (s : ↥(GammaH M H)))) :
    heckeT M H ℓ₀ A F = (GammaHUpper M H ℓ₀).index • F := by
  have hψ : F.comp (MonoidHom.toAdditive (conjL M H ℓ₀)) =
      F.comp (Subgroup.subtype (GammaHUpper M H ℓ₀)).toAdditive :=
    AddMonoidHom.ext fun s => hF (Additive.toMul s)
  rw [heckeT_eq_coresAdd, hψ, coresAdd_comp_subtype]

omit [NeZero ℓ₀] in

theorem conjL_apply_11 (M : ℕ) (H : Subgroup (ZMod M)ˣ) (s : ↥(GammaHUpper M H ℓ₀)) :
    ((conjL M H ℓ₀ s : ↥(GammaH M H)) : SL(2, ℤ)) 1 1 = ((s : ↥(GammaH M H)) : SL(2, ℤ)) 1 1 := rfl

theorem isEis_of_entry (M m : ℕ) (F : H1 M ⊤ A) (hℓ : ℓ₀.Prime) (hℓM : ¬ ℓ₀ ∣ M)
    (hF : ∀ γ δ : ↥(GammaH M ⊤),
      (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod m) = (((δ : SL(2, ℤ)) 1 1 : ℤ) : ZMod m) →
        F (Additive.ofMul γ) = F (Additive.ofMul δ)) :
    IsEis R A M ⊤ ℓ₀ F := by
  unfold IsEis
  rw [heckeT_of_conjL_invariant' A ℓ₀ M ⊤ F (fun s => hF _ _ (by rw [conjL_apply_11])),
    index_GammaHUpper_of_prime M ⊤ ℓ₀ hℓ hℓM, ← Nat.cast_smul_eq_nsmul R]
  push_cast
  rfl

end EisT
p2m_reactivate "P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25 P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25.Q2Step"

section Transport
variable (N q : ℕ)

def toTop (M : ℕ) (g : SL(2, ℤ)) (h : g ∈ Gamma0 M) : ↥(GammaH M ⊤) := ⟨g, by rw [GammaH_top]; exact h⟩

def lowTop : ↥(GLow N q) →* ↥(GammaH (N * q) ⊤) where
  toFun γ := toTop (N * q) ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) (Subgroup.mem_subgroupOf.mp γ.2)
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

theorem coe_lowTop (γ : ↥(GLow N q)) :
    ((lowTop N q γ : ↥(GammaH (N * q) ⊤)) : SL(2, ℤ)) = ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) := rfl

theorem lowTop_surjective : Function.Surjective (lowTop N q) := by
  intro δ
  have hδ : (δ : SL(2, ℤ)) ∈ Gamma0 (N * q) := GammaH_le_Gamma0 _ δ.2
  exact ⟨⟨⟨δ, Gamma0_mul_le N q hδ⟩, Subgroup.mem_subgroupOf.mpr hδ⟩, Subtype.ext rfl⟩

def low2Top : ↥(GLow2 N q) →* ↥(GammaH (N * q * q) ⊤) where
  toFun γ := toTop (N * q * q) ((γ : ↥(Gamma0 N)) : SL(2, ℤ)) (by
    have h := Subgroup.mem_subgroupOf.mp γ.2
    rw [show N * q * q = N * q ^ 2 by ring]
    exact h)
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl

variable (h₁ : LevelLE N (N * q) ⊤ ⊤ 1) (hq : LevelLE N (N * q) ⊤ ⊤ q)
variable (h₁' : LevelLE (N * q) (N * q * q) ⊤ ⊤ 1) (hq' : LevelLE (N * q) (N * q * q) ⊤ ⊤ q)

theorem iotaDeg_one_low2Top (γ : ↥(GLow2 N q)) :
    iotaDeg (N * q) (N * q * q) ⊤ ⊤ 1 h₁' (low2Top N q γ) =
      lowTop N q (Subgroup.inclusion (GLow2_le_GLow N q) γ) :=
  Subtype.ext (IharaSolH25.Dock.conjLowerMat_one _ (h₁'.dvd_entry (low2Top N q γ)))

theorem iotaDeg_q_low2Top [NeZero q] (hq0 : (q : ℤ) ≠ 0) (γ : ↥(GLow2 N q)) :
    iotaDeg (N * q) (N * q * q) ⊤ ⊤ q hq' (low2Top N q γ) = lowTop N q (j1Hom N q hq0 γ) :=
  Subtype.ext rfl

theorem symm_iotaDeg_one_lowTop (γ₀ : ↥(GLow N q)) :
    (gamma0EquivGammaHTop N).symm (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ (lowTop N q γ₀)) = (γ₀ : ↥(Gamma0 N)) :=
  Subtype.ext (IharaSolH25.Dock.conjLowerMat_one _ (h₁.dvd_entry (lowTop N q γ₀)))

theorem symm_iotaDeg_q_lowTop [NeZero q] (hq0 : 0 < q) (γ₀ : ↥(GLow N q)) :
    (gamma0EquivGammaHTop N).symm (iotaDeg N (N * q) ⊤ ⊤ q hq (lowTop N q γ₀)) =
      (((cqEquiv N q hq0).symm γ₀ : ↥(GUp N q)) : ↥(Gamma0 N)) :=
  Subtype.ext rfl

theorem coe_cqEquiv_symm_11 (hq0 : 0 < q) (γ₀ : ↥(GLow N q)) :
    ((((cqEquiv N q hq0).symm γ₀ : ↥(GUp N q)) : ↥(Gamma0 N)) : SL(2, ℤ)) 1 1 =
      ((γ₀ : ↥(Gamma0 N)) : SL(2, ℤ)) 1 1 := rfl

end Transport
p2m_reactivate "P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25 P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25.Q2Step"

end IharaSolH25.D3Inst
p2m_reactivate "P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25 P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25.Q2Step"
p2m_reactivate "P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25 P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero.IharaSolH25.Q2Step"

open scoped MatrixGroups in
open CohCarrier IharaSolH25.D3Inst IharaSolH25.Dock IharaSolH25.Q2Step CongruenceSubgroup in
theorem solution
    (R : Type*) [CommRing R] (A : Type) [AddCommGroup A] [Module R A] (ℓ₀ : ℕ) [NeZero ℓ₀]
    (N q : ℕ) [NeZero q]
    (h₁ : LevelLE N (N * q) ⊤ ⊤ 1) (hq : LevelLE N (N * q) ⊤ ⊤ q)
    (h₁' : LevelLE (N * q) (N * q * q) ⊤ ⊤ 1) (hq' : LevelLE (N * q) (N * q * q) ⊤ ⊤ q)
    (hqp : q.Prime) (hqN : ¬ q ∣ N) (hA : ∀ a : A, q • a = 0 → a = 0)
    (hperf : commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) = ⊤)
    (hstem : Ihara.HasTrivialSchurMultiplier (Matrix.SpecialLinearGroup (Fin 2) (ZMod q)))
    (hℓ : ℓ₀.Prime) (hℓNq : ¬ ℓ₀ ∣ N * q) (x z' : H1 (N * q) ⊤ A)
    (hxz : iDeg' (N * q) (N * q * q) ⊤ ⊤ 1 A h₁' x + iDeg' (N * q) (N * q * q) ⊤ ⊤ q A hq' z' = 0) :
    ∃ w : H1 N ⊤ A, IsEis R A (N * q) ⊤ ℓ₀ (z' - iDeg' N (N * q) ⊤ ⊤ 1 A h₁ w) ∧
      IsEis R A (N * q) ⊤ ℓ₀ (x + iDeg' N (N * q) ⊤ ⊤ q A hq w) := by
  have hsum := hxz
  have hq0 : (q : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hqp.ne_zero
  have hqpos : 0 < q := hqp.pos

  set X : Additive ↥(GLow N q) →+ A := x.comp (MonoidHom.toAdditive (lowTop N q)) with hX
  set Z' : Additive ↥(GLow N q) →+ A := z'.comp (MonoidHom.toAdditive (lowTop N q)) with hZ'
  have hker : ∀ γ : ↥(GLow2 N q),
      X (Additive.ofMul (Subgroup.inclusion (GLow2_le_GLow N q) γ)) +
        Z' (Additive.ofMul (j1Hom N q (Int.natCast_ne_zero.mpr hqp.ne_zero) γ)) = 0 := by
    intro γ
    have e := DFunLike.congr_fun hsum (Additive.ofMul (low2Top N q γ))
    rw [AddMonoidHom.add_apply, AddMonoidHom.zero_apply] at e
    change x (Additive.ofMul (iotaDeg (N * q) (N * q * q) ⊤ ⊤ 1 h₁' (low2Top N q γ))) +
      z' (Additive.ofMul (iotaDeg (N * q) (N * q * q) ⊤ ⊤ q hq' (low2Top N q γ))) = 0 at e
    rw [iotaDeg_one_low2Top, iotaDeg_q_low2Top N q hq' (Int.natCast_ne_zero.mpr hqp.ne_zero)] at e
    exact e
  obtain ⟨w, hU, hP⟩ := lemma25_gamma0_concrete N q hqp hqN A hA hperf hstem X Z' hker

  let W : H1 N ⊤ A := w.comp (MonoidHom.toAdditive (gamma0EquivGammaHTop N).symm.toMonoidHom)
  refine ⟨W, ?_, ?_⟩
  ·
    have key : ∀ γ₀ : ↥(GLow N q),
        (z' - iDeg' N (N * q) ⊤ ⊤ 1 A h₁ W) (Additive.ofMul (lowTop N q γ₀)) =
          (Z' - w.comp (GLow N q).subtype.toAdditive) (Additive.ofMul γ₀) := by
      intro γ₀
      rw [AddMonoidHom.sub_apply, AddMonoidHom.sub_apply]
      change z' (Additive.ofMul (lowTop N q γ₀)) -
        w (Additive.ofMul ((gamma0EquivGammaHTop N).symm
          (iotaDeg N (N * q) ⊤ ⊤ 1 h₁ (lowTop N q γ₀)))) = _
      rw [symm_iotaDeg_one_lowTop]
      rfl
    refine isEis_of_entry R A ℓ₀ (N * q) (N * q) _ hℓ hℓNq fun γ δ hγδ => ?_
    obtain ⟨γ₀, rfl⟩ := lowTop_surjective N q γ
    obtain ⟨δ₀, rfl⟩ := lowTop_surjective N q δ
    rw [key, key]
    exact hU γ₀ δ₀ hγδ
  ·
    let ψ : Additive ↥(GUp N q) →+ A :=
      X.comp (MonoidHom.toAdditive (cqHom N q)) + w.comp (GUp N q).subtype.toAdditive
    have hψ0 : ∀ k : ↥(GPrin N q), ψ (Additive.ofMul (Subgroup.inclusion (GPrin_le_GUp N q) k)) = 0 :=
      fun k => hP k
    have hψ : IsUnitsChar N A q ψ := isUnitsChar_of_vanish_GPrin_up N q A hA ψ hψ0
    have key : ∀ γ₀ : ↥(GLow N q),
        (x + iDeg' N (N * q) ⊤ ⊤ q A hq W) (Additive.ofMul (lowTop N q γ₀)) =
          ψ (Additive.ofMul ((cqEquiv N q hqpos).symm γ₀)) := by
      intro γ₀
      rw [AddMonoidHom.add_apply]
      change x (Additive.ofMul (lowTop N q γ₀)) +
        w (Additive.ofMul ((gamma0EquivGammaHTop N).symm
          (iotaDeg N (N * q) ⊤ ⊤ q hq (lowTop N q γ₀)))) =
        x (Additive.ofMul (lowTop N q (cqHom N q ((cqEquiv N q hqpos).symm γ₀)))) +
          w (Additive.ofMul (((cqEquiv N q hqpos).symm γ₀ : ↥(GUp N q)) : ↥(Gamma0 N)))
      rw [symm_iotaDeg_q_lowTop N q hq hqpos, ← cqEquiv_apply N q hqpos, MulEquiv.apply_symm_apply]
    refine isEis_of_entry R A ℓ₀ (N * q) q _ hℓ hℓNq fun γ δ hγδ => ?_
    obtain ⟨γ₀, rfl⟩ := lowTop_surjective N q γ
    obtain ⟨δ₀, rfl⟩ := lowTop_surjective N q δ
    rw [key, key]
    exact hψ _ _ (by rw [coe_cqEquiv_symm_11, coe_cqEquiv_symm_11]; exact hγδ)

#print axioms solution

end S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero
end P2MW
export P2MW.S_CohCarrier_exists_isEis_of_iDeg_add_eq_zero (solution)
