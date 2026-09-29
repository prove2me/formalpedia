-- Prove2me | solution 1 for CerednikDrinfeld.Omega.theta_eq_prod_theta_comp_subtype_and_thetaMer_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/5e147f63-e0c3-5f31-a3d1-c8f13ad39171

import Mathlib
import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_pmoebius
import Theorems.Thm_CerednikDrinfeld_Omega_thetaMultipliable_of_isDiscrete_of_isExhausted
import Theorems.Thm_CerednikDrinfeld_Omega_exists_isThetaPair_thetaMer_eq_mk
import Theorems.Thm_CerednikDrinfeld_Omega_thetaMer_mul_algebraMap_eq_of_isThetaPair
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_theta_eq_prod_theta_comp_subtype_and_thetaMer_eq_prod

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

namespace NatOmega

section Reindex

variable {α : Type*} [CommMonoid α] [TopologicalSpace α] [T3Space α] [ContinuousMul α]

theorem tprod_eq_prod_tprod_of_equiv {ι β γ : Type*} [Fintype ι] (e : ι × β ≃ γ) (f : γ → α)
    (hf : Multipliable f) (hfib : ∀ i, Multipliable fun b => f (e (i, b))) :
    ∏' c, f c = ∏ i, ∏' b, f (e (i, b)) := by
  have h1 : Multipliable (fun p : ι × β => f (e p)) := (Equiv.multipliable_iff e).mpr hf
  rw [← Equiv.tprod_eq e f, Multipliable.tprod_prod' h1 hfib, tprod_fintype]

theorem tprod_eq_prod_tprod_of_bijective {ι β γ : Type*} [Fintype ι] (φ : ι → β → γ)
    (hφ : Function.Bijective fun p : ι × β => φ p.1 p.2) (f : γ → α)
    (hf : Multipliable f) (hfib : ∀ i, Multipliable fun b => f (φ i b)) :
    ∏' c, f c = ∏ i, ∏' b, f (φ i b) :=
  tprod_eq_prod_tprod_of_equiv (Equiv.ofBijective _ hφ) f hf hfib

omit [T3Space α] [ContinuousMul α] in
theorem multipliable_comp_of_bijective {ι β γ : Type*} (φ : ι → β → γ)
    (hφ : Function.Bijective fun p : ι × β => φ p.1 p.2) (f : γ → α) (hf : Multipliable f) :
    Multipliable fun p : ι × β => f (φ p.1 p.2) :=
  (Equiv.multipliable_iff (Equiv.ofBijective _ hφ)).mpr hf

end Reindex

section Cosets

variable {G : Type*} [Group G] (Γ' : Subgroup G)

theorem bijective_mul_inv_of_section (s : G ⧸ Γ' → G) (hs : ∀ q, (QuotientGroup.mk (s q) : G ⧸ Γ') = q) :
    Function.Bijective fun p : (G ⧸ Γ') × Γ' => (p.2 : G) * (s p.1)⁻¹ := by
  constructor
  · rintro ⟨q₁, γ₁⟩ ⟨q₂, γ₂⟩ h
    simp only at h
    have hq : q₁ = q₂ := by
      rw [← hs q₁, ← hs q₂, QuotientGroup.eq]
      have h1 : (s q₁)⁻¹ = (γ₁ : G)⁻¹ * ((γ₂ : G) * (s q₂)⁻¹) := by rw [← h, inv_mul_cancel_left]
      have : (s q₁)⁻¹ * s q₂ = (γ₁ : G)⁻¹ * γ₂ := by rw [h1]; group
      rw [this]
      exact Γ'.mul_mem (Γ'.inv_mem γ₁.2) γ₂.2
    subst hq
    have : (γ₁ : G) = γ₂ := mul_right_cancel h
    exact Prod.ext rfl (Subtype.ext this)
  · intro g
    have hrel : (s (QuotientGroup.mk g⁻¹))⁻¹ * g⁻¹ ∈ Γ' := by
      rw [← QuotientGroup.eq]; exact hs _
    refine ⟨(QuotientGroup.mk g⁻¹, ⟨g * s (QuotientGroup.mk g⁻¹), ?_⟩), ?_⟩
    · have := Γ'.inv_mem hrel; simpa using this
    · simp

theorem bijective_mul_of_section (s : G ⧸ Γ' → G) (hs : ∀ q, (QuotientGroup.mk (s q) : G ⧸ Γ') = q) :
    Function.Bijective fun p : (G ⧸ Γ') × Γ' => s p.1 * (p.2 : G) := by
  constructor
  · rintro ⟨q₁, γ₁⟩ ⟨q₂, γ₂⟩ h
    simp only at h
    have hq : q₁ = q₂ := by
      rw [← hs q₁, ← hs q₂, QuotientGroup.eq]
      have h1 : s q₂ = s q₁ * (γ₁ : G) * (γ₂ : G)⁻¹ := by rw [h, mul_inv_cancel_right]
      have : (s q₁)⁻¹ * s q₂ = (γ₁ : G) * (γ₂ : G)⁻¹ := by rw [h1]; group
      rw [this]
      exact Γ'.mul_mem γ₁.2 (Γ'.inv_mem γ₂.2)
    subst hq
    have : (γ₁ : G) = γ₂ := mul_left_cancel h
    exact Prod.ext rfl (Subtype.ext this)
  · intro g
    have hrel : (s (QuotientGroup.mk g))⁻¹ * g ∈ Γ' := by
      rw [← QuotientGroup.eq]; exact hs _
    exact ⟨(QuotientGroup.mk g, ⟨_, hrel⟩), by simp⟩

theorem mk_out_eq (q : G ⧸ Γ') : (QuotientGroup.mk (Quotient.out q) : G ⧸ Γ') = q := Quotient.out_eq q

theorem bijective_out_mul : Function.Bijective fun p : (G ⧸ Γ') × Γ' => p.1.out * (p.2 : G) :=
  bijective_mul_of_section Γ' Quotient.out (mk_out_eq Γ')

theorem bijective_mul_out_inv : Function.Bijective fun p : (G ⧸ Γ') × Γ' => (p.2 : G) * (p.1.out)⁻¹ :=
  bijective_mul_inv_of_section Γ' Quotient.out (mk_out_eq Γ')

variable {α : Type*} [CommMonoid α] [TopologicalSpace α] [T3Space α] [ContinuousMul α]

theorem tprod_eq_prod_tprod_rightCoset {ι : Type*} [Fintype ι] (t : ι → G)
    (ht : Function.Bijective fun p : ι × Γ' => (p.2 : G) * t p.1) (f : G → α)
    (hf : Multipliable f) (hfib : ∀ i, Multipliable fun γ' : Γ' => f (γ' * t i)) :
    ∏' g, f g = ∏ i, ∏' γ' : Γ', f (γ' * t i) :=
  tprod_eq_prod_tprod_of_bijective (fun i (γ' : Γ') => (γ' : G) * t i) ht f hf hfib

theorem tprod_eq_prod_tprod_leftCoset {ι : Type*} [Fintype ι] (t : ι → G)
    (ht : Function.Bijective fun p : ι × Γ' => t p.1 * (p.2 : G)) (f : G → α)
    (hf : Multipliable f) (hfib : ∀ i, Multipliable fun γ' : Γ' => f (t i * γ')) :
    ∏' g, f g = ∏ i, ∏' γ' : Γ', f (t i * γ') :=
  tprod_eq_prod_tprod_of_bijective (fun i (γ' : Γ') => t i * (γ' : G)) ht f hf hfib

end Cosets

section Moebius

variable (K₀ : Type*) [Field K₀] {K : Type*} [Field K] [Algebra K₀ K]

theorem moebius_sub_moebius (g : GL (Fin 2) K₀) (z w : K)
    (hz : algebraMap K₀ K (g 1 0) * z + algebraMap K₀ K (g 1 1) ≠ 0)
    (hw : algebraMap K₀ K (g 1 0) * w + algebraMap K₀ K (g 1 1) ≠ 0) :
    moebius K₀ K g z - moebius K₀ K g w =
      algebraMap K₀ K (Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀)) * (z - w) /
        ((algebraMap K₀ K (g 1 0) * z + algebraMap K₀ K (g 1 1)) *
          (algebraMap K₀ K (g 1 0) * w + algebraMap K₀ K (g 1 1))) := by
  rw [Matrix.det_fin_two, moebius, moebius, div_sub_div _ _ hz hw]
  congr 1
  simp only [map_sub, map_mul]
  ring

theorem pmoebius_sub_pmoebius [DecidableEq K] (g : GL (Fin 2) K₀) {z w : K}
    (hz : z ∈ upperHalfPlane K₀ K) (hw : w ∈ upperHalfPlane K₀ K) :
    pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) z - pmoebius K₀ (Matrix.ProjGenLinGroup.mk g) w =
      algebraMap K₀ K (Matrix.det (g : Matrix (Fin 2) (Fin 2) K₀)) * (z - w) /
        ((algebraMap K₀ K (g 1 0) * z + algebraMap K₀ K (g 1 1)) *
          (algebraMap K₀ K (g 1 0) * w + algebraMap K₀ K (g 1 1))) := by
  have hz' := moebius_denom_ne_zero_of_mem K₀ hz g
  have hw' := moebius_denom_ne_zero_of_mem K₀ hw g
  rw [pmoebius_mk K₀ g z hz', pmoebius_mk K₀ g w hw', moebius_sub_moebius K₀ g z w hz' hw']

end Moebius

section Theta

variable {K₀ : Type*} [Field K₀] {K : Type*} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {G : Type*} [Group G] (ρ : G →* PGL(2, K₀)) (Γ' : Subgroup G)

theorem thetaFactor_coe_mul {a b : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (z₀ z : K) (γ' : Γ') (g : G) :
    thetaFactor ρ a b z₀ z ((γ' : G) * g) =
      thetaFactor (ρ.comp Γ'.subtype) (pmoebius K₀ (ρ g) a) (pmoebius K₀ (ρ g) b) z₀ z γ' := by
  simp only [thetaFactor, MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, pmoebius_mul K₀ ha,
    pmoebius_mul K₀ hb]

theorem thetaFactor_mul_coe {a b z₀ z : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hz : z ∈ upperHalfPlane K₀ K) (g : G) (γ' : Γ') :
    thetaFactor ρ a b z₀ z (g * (γ' : G)) =
      thetaFactor (ρ.comp Γ'.subtype) a b (pmoebius K₀ (ρ g)⁻¹ z₀) (pmoebius K₀ (ρ g)⁻¹ z) γ' := by
  simp only [thetaFactor, MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul]
  have ha' := pmoebius_mem_upperHalfPlane K₀ ha (ρ (γ' : G))
  have hb' := pmoebius_mem_upperHalfPlane K₀ hb (ρ (γ' : G))
  have ez : z = pmoebius K₀ (ρ g) (pmoebius K₀ (ρ g)⁻¹ z) := by
    rw [← pmoebius_mul K₀ hz, mul_inv_cancel, pmoebius_one]
  have ez₀ : z₀ = pmoebius K₀ (ρ g) (pmoebius K₀ (ρ g)⁻¹ z₀) := by
    rw [← pmoebius_mul K₀ hz₀, mul_inv_cancel, pmoebius_one]
  rw [pmoebius_mul K₀ ha, pmoebius_mul K₀ hb]
  conv_lhs => rw [ez, ez₀]
  exact crossRatio_pmoebius (ρ g) (pmoebius_mem_upperHalfPlane K₀ hz _)
    (pmoebius_mem_upperHalfPlane K₀ hz₀ _) ha' hb'

variable [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]

theorem theta_eq_prod_theta_comp_subtype_right {ι : Type*} [Fintype ι] (t : ι → G)
    (ht : Function.Bijective fun p : ι × Γ' => (p.2 : G) * t p.1)
    {a b : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (z₀ z : K)
    (hΘ : ThetaMultipliable ρ a b z₀ z)
    (hΘ' : ∀ i, ThetaMultipliable (ρ.comp Γ'.subtype) (pmoebius K₀ (ρ (t i)) a) (pmoebius K₀ (ρ (t i)) b) z₀ z) :
    theta ρ a b z₀ z = ∏ i, theta (ρ.comp Γ'.subtype) (pmoebius K₀ (ρ (t i)) a) (pmoebius K₀ (ρ (t i)) b) z₀ z := by
  unfold theta
  have hfib : ∀ i, Multipliable fun γ' : Γ' => thetaFactor ρ a b z₀ z ((γ' : G) * t i) := by
    intro i
    have h := hΘ' i
    unfold ThetaMultipliable at h
    refine h.congr ?_
    intro γ'; exact (thetaFactor_coe_mul ρ Γ' ha hb z₀ z γ' (t i)).symm
  rw [tprod_eq_prod_tprod_rightCoset Γ' t ht _ hΘ hfib]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact tprod_congr fun γ' => thetaFactor_coe_mul ρ Γ' ha hb z₀ z γ' (t i)

theorem theta_eq_prod_theta_comp_subtype_left {ι : Type*} [Fintype ι] (t : ι → G)
    (ht : Function.Bijective fun p : ι × Γ' => t p.1 * (p.2 : G))
    {a b z₀ z : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hz : z ∈ upperHalfPlane K₀ K)
    (hΘ : ThetaMultipliable ρ a b z₀ z)
    (hΘ' : ∀ i, ThetaMultipliable (ρ.comp Γ'.subtype) a b (pmoebius K₀ (ρ (t i))⁻¹ z₀) (pmoebius K₀ (ρ (t i))⁻¹ z)) :
    theta ρ a b z₀ z = ∏ i, theta (ρ.comp Γ'.subtype) a b (pmoebius K₀ (ρ (t i))⁻¹ z₀) (pmoebius K₀ (ρ (t i))⁻¹ z) := by
  unfold theta
  have hfib : ∀ i, Multipliable fun γ' : Γ' => thetaFactor ρ a b z₀ z (t i * (γ' : G)) := by
    intro i
    have h := hΘ' i
    unfold ThetaMultipliable at h
    refine h.congr ?_
    intro γ'; exact (thetaFactor_mul_coe ρ Γ' ha hb hz₀ hz (t i) γ').symm
  rw [tprod_eq_prod_tprod_leftCoset Γ' t ht _ hΘ hfib]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact tprod_congr fun γ' => thetaFactor_mul_coe ρ Γ' ha hb hz₀ hz (t i) γ'

theorem theta_eq_prod_quotient_theta_comp_subtype [Fintype (G ⧸ Γ')] (s : G ⧸ Γ' → G)
    (hs : ∀ q, (QuotientGroup.mk (s q) : G ⧸ Γ') = q)
    {a b : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (z₀ z : K)
    (hΘ : ThetaMultipliable ρ a b z₀ z)
    (hΘ' : ∀ q, ThetaMultipliable (ρ.comp Γ'.subtype) (pmoebius K₀ (ρ (s q))⁻¹ a) (pmoebius K₀ (ρ (s q))⁻¹ b) z₀ z) :
    theta ρ a b z₀ z =
      ∏ q : G ⧸ Γ', theta (ρ.comp Γ'.subtype) (pmoebius K₀ (ρ (s q))⁻¹ a) (pmoebius K₀ (ρ (s q))⁻¹ b) z₀ z := by
  have key := theta_eq_prod_theta_comp_subtype_right ρ Γ' (fun q => (s q)⁻¹)
    (bijective_mul_inv_of_section Γ' s hs) ha hb z₀ z hΘ (by simpa only [map_inv] using hΘ')
  simpa only [map_inv] using key

theorem theta_eq_prod_quotient_theta_comp_subtype_left [Fintype (G ⧸ Γ')] (s : G ⧸ Γ' → G)
    (hs : ∀ q, (QuotientGroup.mk (s q) : G ⧸ Γ') = q)
    {a b z₀ z : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K)
    (hz₀ : z₀ ∈ upperHalfPlane K₀ K) (hz : z ∈ upperHalfPlane K₀ K)
    (hΘ : ThetaMultipliable ρ a b z₀ z)
    (hΘ' : ∀ q, ThetaMultipliable (ρ.comp Γ'.subtype) a b (pmoebius K₀ (ρ (s q))⁻¹ z₀) (pmoebius K₀ (ρ (s q))⁻¹ z)) :
    theta ρ a b z₀ z =
      ∏ q : G ⧸ Γ', theta (ρ.comp Γ'.subtype) a b (pmoebius K₀ (ρ (s q))⁻¹ z₀) (pmoebius K₀ (ρ (s q))⁻¹ z) :=
  theta_eq_prod_theta_comp_subtype_left ρ Γ' s (bijective_mul_of_section Γ' s hs) ha hb hz₀ hz hΘ hΘ'

end Theta

end NatOmega

namespace NatOmega

section Discrete

theorem isDiscrete_comp_subtype {K₀ : Type*} [Field K₀] (K : Type*) [Field K] [Algebra K₀ K]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {G : Type*} [Group G] {ρ : G →* PGL(2, K₀)} (hρ : IsDiscrete K ρ) (Γ' : Subgroup G) :
    IsDiscrete K (ρ.comp Γ'.subtype) := by
  intro ε hε
  have hfin := (hρ ε hε).preimage (Subtype.val_injective (p := fun x => x ∈ Γ')).injOn
  refine hfin.subset ?_
  intro γ hγ
  simpa only [Set.mem_preimage, Set.mem_setOf_eq, MonoidHom.comp_apply, Subgroup.coe_subtype] using hγ

end Discrete

section Eval

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

def evalHol (ϖ : PseudoUniformizer K₀ K) (w : ↥(upperHalfPlane K₀ K)) : ↥(holRing ϖ) →+* K :=
  (Pi.evalRingHom (fun _ : ↥(upperHalfPlane K₀ K) => K) w).comp (holRing ϖ).subtype

@[scoped simp] theorem evalHol_apply (ϖ : PseudoUniformizer K₀ K) (w : ↥(upperHalfPlane K₀ K)) (f : ↥(holRing ϖ)) :
    evalHol ϖ w f = (f : ↥(upperHalfPlane K₀ K) → K) w := rfl

theorem holRing_ext (ϖ : PseudoUniformizer K₀ K) {f g : ↥(holRing ϖ)}
    (h : ∀ w : ↥(upperHalfPlane K₀ K), evalHol ϖ w f = evalHol ϖ w g) : f = g :=
  Subtype.ext (funext h)

end Eval

end NatOmega
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_theta_eq_prod_theta_comp_subtype_and_thetaMer_eq_prod.NatOmega"

open NatOmega in
theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) [IsDomain ↥(holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (Γ' : Subgroup G) [Fintype (G ⧸ Γ')] (s : G ⧸ Γ' → G) (hs : ∀ q : G ⧸ Γ', (QuotientGroup.mk (s q) : G ⧸ Γ') = q)
    {a b z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀) :
    (∀ z ∈ upperHalfPlane K₀ K,
        theta ρ a b z₀ z =
          ∏ q : G ⧸ Γ', theta (ρ.comp Γ'.subtype) (pmoebius K₀ (ρ (s q))⁻¹ a) (pmoebius K₀ (ρ (s q))⁻¹ b) z₀ z) ∧
      thetaMer ϖ ρ a b z₀ =
        ∏ q : G ⧸ Γ', thetaMer ϖ (ρ.comp Γ'.subtype) (pmoebius K₀ (ρ (s q))⁻¹ a) (pmoebius K₀ (ρ (s q))⁻¹ b) z₀ := by

  have hρ' : IsDiscrete K (ρ.comp Γ'.subtype) := isDiscrete_comp_subtype K hρ Γ'
  have haq : ∀ q : G ⧸ Γ', pmoebius K₀ (ρ (s q))⁻¹ a ∈ upperHalfPlane K₀ K :=
    fun q => pmoebius_mem_upperHalfPlane K₀ ha _
  have hbq : ∀ q : G ⧸ Γ', pmoebius K₀ (ρ (s q))⁻¹ b ∈ upperHalfPlane K₀ K :=
    fun q => pmoebius_mem_upperHalfPlane K₀ hb _

  have shift : ∀ (q : G ⧸ Γ') (γ : ↥Γ') (x : K), x ∈ upperHalfPlane K₀ K →
      pmoebius K₀ ((ρ.comp Γ'.subtype) γ) (pmoebius K₀ (ρ (s q))⁻¹ x) = pmoebius K₀ (ρ ((γ : G) * (s q)⁻¹)) x := by
    intro q γ x hx
    rw [MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, map_inv, pmoebius_mul K₀ hx]
  have hz₀aq : ∀ (q : G ⧸ Γ') (γ : ↥Γ'),
      pmoebius K₀ ((ρ.comp Γ'.subtype) γ) (pmoebius K₀ (ρ (s q))⁻¹ a) ≠ z₀ := by
    intro q γ; rw [shift q γ a ha]; exact hz₀a _
  have hz₀bq : ∀ (q : G ⧸ Γ') (γ : ↥Γ'),
      pmoebius K₀ ((ρ.comp Γ'.subtype) γ) (pmoebius K₀ (ρ (s q))⁻¹ b) ≠ z₀ := by
    intro q γ; rw [shift q γ b hb]; exact hz₀b _

  have hpt : ∀ z ∈ upperHalfPlane K₀ K, theta ρ a b z₀ z =
      ∏ q : G ⧸ Γ', theta (ρ.comp Γ'.subtype) (pmoebius K₀ (ρ (s q))⁻¹ a) (pmoebius K₀ (ρ (s q))⁻¹ b) z₀ z := by
    intro z hz
    exact theta_eq_prod_quotient_theta_comp_subtype ρ Γ' s hs ha hb z₀ z
      (thetaMultipliable_of_isDiscrete_of_isExhausted ϖ hex ρ hρ ha hb hz₀ hz)
      (fun q => thetaMultipliable_of_isDiscrete_of_isExhausted ϖ hex (ρ.comp Γ'.subtype) hρ' (haq q) (hbq q) hz₀ hz)
  refine ⟨hpt, ?_⟩

  obtain ⟨F, H, hFH, hmer⟩ := exists_isThetaPair_thetaMer_eq_mk K₀ K ϖ hex ρ hρ ha hb hz₀ hz₀a hz₀b
  choose Fq Hq hFHq hmerq using fun q : G ⧸ Γ' =>
    exists_isThetaPair_thetaMer_eq_mk K₀ K ϖ hex (ρ.comp Γ'.subtype) hρ' (haq q) (hbq q) hz₀ (hz₀aq q) (hz₀bq q)

  have key : F * ∏ q, Hq q = H * ∏ q, Fq q := by
    apply holRing_ext ϖ
    intro w
    simp only [map_mul, map_prod, evalHol_apply]
    by_cases hw : ∃ γ : G, pmoebius K₀ (ρ γ) b = (w : K)
    ·
      have hH : (H : ↥(upperHalfPlane K₀ K) → K) w = 0 := (hFH.2.1 w).mpr hw
      obtain ⟨γ, hγ⟩ := hw
      obtain ⟨⟨q, γ'⟩, hqγ⟩ := (bijective_mul_inv_of_section Γ' s hs).2 γ
      have hHq : (Hq q : ↥(upperHalfPlane K₀ K) → K) w = 0 := by
        refine ((hFHq q).2.1 w).mpr ⟨γ', ?_⟩
        rw [shift q γ' b hb]
        simpa only using (congrArg (fun g => pmoebius K₀ (ρ g) b) hqγ).trans hγ
      rw [hH, zero_mul, Finset.prod_eq_zero (Finset.mem_univ q) hHq, mul_zero]
    ·
      have hH : (H : ↥(upperHalfPlane K₀ K) → K) w ≠ 0 := fun h0 => hw ((hFH.2.1 w).mp h0)
      have hwq : ∀ q : G ⧸ Γ', ¬ ∃ γ' : ↥Γ',
          pmoebius K₀ ((ρ.comp Γ'.subtype) γ') (pmoebius K₀ (ρ (s q))⁻¹ b) = (w : K) := by
        intro q ⟨γ', h'⟩
        exact hw ⟨(γ' : G) * (s q)⁻¹, by rw [← shift q γ' b hb]; exact h'⟩
      have hHq : ∀ q : G ⧸ Γ', (Hq q : ↥(upperHalfPlane K₀ K) → K) w ≠ 0 :=
        fun q h0 => hwq q (((hFHq q).2.1 w).mp h0)
      have hF : (F : ↥(upperHalfPlane K₀ K) → K) w =
          theta ρ a b z₀ w * (H : ↥(upperHalfPlane K₀ K) → K) w := by
        rw [← hFH.2.2.2 w hw, div_mul_cancel₀ _ hH]
      have hFq : ∀ q : G ⧸ Γ', (Fq q : ↥(upperHalfPlane K₀ K) → K) w =
          theta (ρ.comp Γ'.subtype) (pmoebius K₀ (ρ (s q))⁻¹ a) (pmoebius K₀ (ρ (s q))⁻¹ b) z₀ w *
            (Hq q : ↥(upperHalfPlane K₀ K) → K) w := by
        intro q; rw [← (hFHq q).2.2.2 w (hwq q), div_mul_cancel₀ _ (hHq q)]
      rw [hF, Finset.prod_congr rfl (fun q _ => hFq q), Finset.prod_mul_distrib, hpt w w.2]
      ring

  have hHne : H ≠ 0 := (mem_nonZeroDivisors_iff_ne_zero.mp hFH.1)
  have hHqne : ∀ q, Hq q ≠ 0 := fun q => mem_nonZeroDivisors_iff_ne_zero.mp (hFHq q).1
  have hX : algebraMap ↥(holRing ϖ) (merField ϖ) (H * ∏ q, Hq q) ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective ↥(holRing ϖ) (merField ϖ))]
    exact mul_ne_zero hHne (Finset.prod_ne_zero_iff.mpr fun q _ => hHqne q)
  apply mul_right_cancel₀ hX
  have e1 : thetaMer ϖ ρ a b z₀ * algebraMap ↥(holRing ϖ) (merField ϖ) (H * ∏ q, Hq q) =
      algebraMap ↥(holRing ϖ) (merField ϖ) (F * ∏ q, Hq q) := by
    rw [map_mul, map_mul, ← mul_assoc, thetaMer_mul_algebraMap_eq_of_isThetaPair ϖ ρ a b z₀ F H hFH]
  have e2 : (∏ q : G ⧸ Γ', thetaMer ϖ (ρ.comp Γ'.subtype) (pmoebius K₀ (ρ (s q))⁻¹ a) (pmoebius K₀ (ρ (s q))⁻¹ b) z₀) *
        algebraMap ↥(holRing ϖ) (merField ϖ) (H * ∏ q, Hq q) =
      algebraMap ↥(holRing ϖ) (merField ϖ) (H * ∏ q, Fq q) := by
    rw [map_mul, map_mul, map_prod, map_prod, mul_left_comm, ← Finset.prod_mul_distrib]
    congr 1
    exact Finset.prod_congr rfl fun q _ =>
      thetaMer_mul_algebraMap_eq_of_isThetaPair ϖ (ρ.comp Γ'.subtype) _ _ z₀ (Fq q) (Hq q) (hFHq q)
  rw [e1, e2, key]

end S_CerednikDrinfeld_Omega_theta_eq_prod_theta_comp_subtype_and_thetaMer_eq_prod
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_theta_eq_prod_theta_comp_subtype_and_thetaMer_eq_prod (solution)
