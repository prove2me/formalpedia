-- Prove2me | solution 1 for CerednikDrinfeld.Omega.prod_theta_comp_subtype_pmoebius_eq_mul_theta_and_prod_fracAct_thetaMer_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/98841200-839e-51ca-befd-0addf12490dc

import Mathlib
import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Theorems.Thm_CerednikDrinfeld_Omega_crossRatio_pmoebius
import Theorems.Thm_CerednikDrinfeld_Omega_thetaMultipliable_of_isDiscrete_of_isExhausted
import Theorems.Thm_CerednikDrinfeld_Omega_exists_isThetaPair_thetaMer_eq_mk
import Theorems.Thm_CerednikDrinfeld_Omega_thetaMer_mul_algebraMap_eq_of_isThetaPair
import Theorems.Thm_CerednikDrinfeld_Omega_theta_mul_theta_basePoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_prod_theta_comp_subtype_pmoebius_eq_mul_theta_and_prod_fracAct_thetaMer_eq

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
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_prod_theta_comp_subtype_pmoebius_eq_mul_theta_and_prod_fracAct_thetaMer_eq.NatOmega"

namespace NatOmega

section EvalConst
variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

omit [DecidableEq K] in
theorem coe_algebraMap_holRing_apply (ϖ : PseudoUniformizer K₀ K) (w : ↥(upperHalfPlane K₀ K)) (c : K) :
    ((algebraMap K ↥(holRing ϖ) c : ↥(holRing ϖ)) : ↥(upperHalfPlane K₀ K) → K) w = c := rfl

end EvalConst
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_prod_theta_comp_subtype_pmoebius_eq_mul_theta_and_prod_fracAct_thetaMer_eq.NatOmega"

theorem norm_pointwise
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) [IsDomain ↥(holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (Γ' : Subgroup G) [Fintype (G ⧸ Γ')] (s : G ⧸ Γ' → G) (hs : ∀ q : G ⧸ Γ', (QuotientGroup.mk (s q) : G ⧸ Γ') = q)
    {a' b' z₀ : K} (ha' : a' ∈ upperHalfPlane K₀ K) (hb' : b' ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a' ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b' ≠ z₀) :
    ∀ z ∈ upperHalfPlane K₀ K,
      ∏ q : G ⧸ Γ', theta (ρ.comp Γ'.subtype) a' b' z₀ (pmoebius K₀ (ρ (s q))⁻¹ z) =
        (∏ q : G ⧸ Γ', theta (ρ.comp Γ'.subtype) a' b' z₀ (pmoebius K₀ (ρ (s q))⁻¹ z₀)) * theta ρ a' b' z₀ z := by
  have hρ' : IsDiscrete K (ρ.comp Γ'.subtype) := isDiscrete_comp_subtype K hρ Γ'
  have hΩt : ∀ (q : G ⧸ Γ') {x : K}, x ∈ upperHalfPlane K₀ K →
      pmoebius K₀ (ρ (s q))⁻¹ x ∈ upperHalfPlane K₀ K :=
    fun q _ hx => pmoebius_mem_upperHalfPlane K₀ hx _
  have unshift : ∀ (q : G ⧸ Γ') {x : K}, x ∈ upperHalfPlane K₀ K →
      pmoebius K₀ (ρ (s q)) (pmoebius K₀ (ρ (s q))⁻¹ x) = x := by
    intro q x hx; rw [← pmoebius_mul K₀ hx, mul_inv_cancel, pmoebius_one]

  have hta : ∀ (q : G ⧸ Γ') (γ : ↥Γ'),
      pmoebius K₀ ((ρ.comp Γ'.subtype) γ) a' ≠ pmoebius K₀ (ρ (s q))⁻¹ z₀ := by
    intro q γ h
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at h
    apply hz₀a (s q * (γ : G))
    rw [map_mul, pmoebius_mul K₀ ha', h]
    exact unshift q hz₀
  have htb : ∀ (q : G ⧸ Γ') (γ : ↥Γ'),
      pmoebius K₀ ((ρ.comp Γ'.subtype) γ) b' ≠ pmoebius K₀ (ρ (s q))⁻¹ z₀ := by
    intro q γ h
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at h
    apply hz₀b (s q * (γ : G))
    rw [map_mul, pmoebius_mul K₀ hb', h]
    exact unshift q hz₀
  intro z hz
  have split : ∀ q : G ⧸ Γ',
      theta (ρ.comp Γ'.subtype) a' b' z₀ (pmoebius K₀ (ρ (s q))⁻¹ z) =
        theta (ρ.comp Γ'.subtype) a' b' z₀ (pmoebius K₀ (ρ (s q))⁻¹ z₀) *
          theta (ρ.comp Γ'.subtype) a' b' (pmoebius K₀ (ρ (s q))⁻¹ z₀) (pmoebius K₀ (ρ (s q))⁻¹ z) := by
    intro q
    exact (theta_mul_theta_basePoint (ρ.comp Γ'.subtype) (hta q) (htb q)
      (thetaMultipliable_of_isDiscrete_of_isExhausted ϖ hex _ hρ' ha' hb' hz₀ (hΩt q hz₀))
      (thetaMultipliable_of_isDiscrete_of_isExhausted ϖ hex _ hρ' ha' hb' (hΩt q hz₀) (hΩt q hz))).symm
  rw [Finset.prod_congr rfl (fun q _ => split q), Finset.prod_mul_distrib]
  congr 1
  exact (theta_eq_prod_quotient_theta_comp_subtype_left ρ Γ' s hs ha' hb' hz₀ hz
    (thetaMultipliable_of_isDiscrete_of_isExhausted ϖ hex ρ hρ ha' hb' hz₀ hz)
    (fun q => thetaMultipliable_of_isDiscrete_of_isExhausted ϖ hex _ hρ' ha' hb' (hΩt q hz₀) (hΩt q hz))).symm

theorem norm_key
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) [IsDomain ↥(holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (Γ' : Subgroup G) [Fintype (G ⧸ Γ')] (s : G ⧸ Γ' → G) (hs : ∀ q : G ⧸ Γ', (QuotientGroup.mk (s q) : G ⧸ Γ') = q)
    {a' b' z₀ : K} (ha' : a' ∈ upperHalfPlane K₀ K) (hb' : b' ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a' ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b' ≠ z₀)
    (F H : ↥(holRing ϖ)) (hFH : IsThetaPair ϖ ρ a' b' z₀ F H)
    (F' H' : ↥(holRing ϖ)) (hFH' : IsThetaPair ϖ (ρ.comp Γ'.subtype) a' b' z₀ F' H') :
    (∏ q : G ⧸ Γ', ρ (s q) • F') * H =
      algebraMap K ↥(holRing ϖ) (∏ q : G ⧸ Γ', theta (ρ.comp Γ'.subtype) a' b' z₀ (pmoebius K₀ (ρ (s q))⁻¹ z₀)) *
        F * ∏ q : G ⧸ Γ', ρ (s q) • H' := by
  have hρ' : IsDiscrete K (ρ.comp Γ'.subtype) := isDiscrete_comp_subtype K hρ Γ'
  have hΩt : ∀ (q : G ⧸ Γ') {x : K}, x ∈ upperHalfPlane K₀ K →
      pmoebius K₀ (ρ (s q))⁻¹ x ∈ upperHalfPlane K₀ K :=
    fun q _ hx => pmoebius_mem_upperHalfPlane K₀ hx _
  have unshift : ∀ (q : G ⧸ Γ') {x : K}, x ∈ upperHalfPlane K₀ K →
      pmoebius K₀ (ρ (s q)) (pmoebius K₀ (ρ (s q))⁻¹ x) = x := by
    intro q x hx; rw [← pmoebius_mul K₀ hx, mul_inv_cancel, pmoebius_one]
  have hpt := norm_pointwise K₀ K ϖ hex ρ hρ Γ' s hs ha' hb' hz₀ hz₀a hz₀b
  apply holRing_ext ϖ
  intro w
  simp only [map_mul, map_prod, evalHol_apply, coe_smul_holRing_apply, coe_algebraMap_holRing_apply]
  have cw : ∀ q : G ⧸ Γ', (((ρ (s q))⁻¹ • w : ↥(upperHalfPlane K₀ K)) : K) = pmoebius K₀ (ρ (s q))⁻¹ (w : K) :=
    fun q => coe_smul_upperHalfPlane _ w
  by_cases hw : ∃ γ : G, pmoebius K₀ (ρ γ) b' = (w : K)
  · have hH : (H : ↥(upperHalfPlane K₀ K) → K) w = 0 := (hFH.2.1 w).mpr hw
    obtain ⟨γ, hγ⟩ := hw
    obtain ⟨⟨q, γ'⟩, hqγ⟩ := (bijective_mul_of_section Γ' s hs).2 γ
    have hH' : (H' : ↥(upperHalfPlane K₀ K) → K) ((ρ (s q))⁻¹ • w) = 0 := by
      refine ((hFH'.2.1 _).mpr ⟨γ', ?_⟩)
      rw [cw q, MonoidHom.comp_apply, Subgroup.coe_subtype]
      have : pmoebius K₀ (ρ (s q * (γ' : G))) b' = (w : K) := by
        simpa only using (congrArg (fun g => pmoebius K₀ (ρ g) b') hqγ).trans hγ
      rw [← this, map_mul, pmoebius_mul K₀ hb', ← pmoebius_mul K₀ (pmoebius_mem_upperHalfPlane K₀ hb' (ρ (γ' : G))),
        inv_mul_cancel, pmoebius_one]
    have hprod : ∏ x : G ⧸ Γ', (H' : ↥(upperHalfPlane K₀ K) → K) ((ρ (s x))⁻¹ • w) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ q) hH'
    rw [hH, mul_zero, hprod, mul_zero]
  · have hH : (H : ↥(upperHalfPlane K₀ K) → K) w ≠ 0 := fun h0 => hw ((hFH.2.1 w).mp h0)
    have hwq : ∀ q : G ⧸ Γ', ¬ ∃ γ' : ↥Γ',
        pmoebius K₀ ((ρ.comp Γ'.subtype) γ') b' = (((ρ (s q))⁻¹ • w : ↥(upperHalfPlane K₀ K)) : K) := by
      intro q ⟨γ', h'⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at h'
      apply hw
      refine ⟨s q * (γ' : G), ?_⟩
      rw [map_mul, pmoebius_mul K₀ hb', h', cw q]
      exact unshift q w.2
    have hH' : ∀ q : G ⧸ Γ', (H' : ↥(upperHalfPlane K₀ K) → K) ((ρ (s q))⁻¹ • w) ≠ 0 :=
      fun q h0 => hwq q (((hFH'.2.1 _).mp h0))
    have hF : (F : ↥(upperHalfPlane K₀ K) → K) w = theta ρ a' b' z₀ w * (H : ↥(upperHalfPlane K₀ K) → K) w := by
      rw [← hFH.2.2.2 w hw, div_mul_cancel₀ _ hH]
    have hF' : ∀ q : G ⧸ Γ', (F' : ↥(upperHalfPlane K₀ K) → K) ((ρ (s q))⁻¹ • w) =
        theta (ρ.comp Γ'.subtype) a' b' z₀ (pmoebius K₀ (ρ (s q))⁻¹ (w : K)) *
          (H' : ↥(upperHalfPlane K₀ K) → K) ((ρ (s q))⁻¹ • w) := by
      intro q; rw [← cw q, ← hFH'.2.2.2 _ (hwq q), div_mul_cancel₀ _ (hH' q)]
    rw [hF, Finset.prod_congr rfl (fun q _ => hF' q), Finset.prod_mul_distrib, hpt w w.2]
    ring

theorem norm_frac {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) [IsDomain ↥(holRing ϖ)] {ι : Type} [Fintype ι]
    (T : ι → merField ϖ) (TG : merField ϖ) (C : K) (F H : ↥(holRing ϖ)) (gF gH : ι → ↥(holRing ϖ))
    (hT : ∀ i, T i * algebraMap ↥(holRing ϖ) (merField ϖ) (gH i) = algebraMap ↥(holRing ϖ) (merField ϖ) (gF i))
    (hTG : TG * algebraMap ↥(holRing ϖ) (merField ϖ) H = algebraMap ↥(holRing ϖ) (merField ϖ) F)
    (hH : H ≠ 0) (hgH : ∀ i, gH i ≠ 0)
    (key : (∏ i, gF i) * H = algebraMap K ↥(holRing ϖ) C * F * ∏ i, gH i) :
    ∏ i, T i = algebraMap K (merField ϖ) C * TG := by
  have hX : algebraMap ↥(holRing ϖ) (merField ϖ) (H * ∏ i, gH i) ≠ 0 := by
    rw [map_ne_zero_iff _ (IsFractionRing.injective ↥(holRing ϖ) (merField ϖ))]
    exact mul_ne_zero hH (Finset.prod_ne_zero_iff.mpr fun i _ => hgH i)
  apply mul_right_cancel₀ hX
  have e1 : (∏ i, T i) * algebraMap ↥(holRing ϖ) (merField ϖ) (H * ∏ i, gH i) =
      algebraMap ↥(holRing ϖ) (merField ϖ) ((∏ i, gF i) * H) := by
    rw [map_mul, map_mul, map_prod, map_prod, mul_comm (algebraMap ↥(holRing ϖ) (merField ϖ) H), ← mul_assoc,
      ← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun i _ => hT i)]
  have e2 : algebraMap K (merField ϖ) C * TG * algebraMap ↥(holRing ϖ) (merField ϖ) (H * ∏ i, gH i) =
      algebraMap ↥(holRing ϖ) (merField ϖ) (algebraMap K ↥(holRing ϖ) C * F * ∏ i, gH i) := by
    rw [map_mul, map_mul, map_mul, ← IsScalarTower.algebraMap_apply K ↥(holRing ϖ) (merField ϖ) C, ← hTG]
    simp only [mul_assoc]
  rw [e1, e2, key]

end NatOmega
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_prod_theta_comp_subtype_pmoebius_eq_mul_theta_and_prod_fracAct_thetaMer_eq.NatOmega"

open NatOmega in
theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) [IsDomain ↥(holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (Γ' : Subgroup G) [Fintype (G ⧸ Γ')] (s : G ⧸ Γ' → G) (hs : ∀ q : G ⧸ Γ', (QuotientGroup.mk (s q) : G ⧸ Γ') = q)
    {a' b' z₀ : K} (ha' : a' ∈ upperHalfPlane K₀ K) (hb' : b' ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a' ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b' ≠ z₀) :
    (∀ z ∈ upperHalfPlane K₀ K,
        ∏ q : G ⧸ Γ', theta (ρ.comp Γ'.subtype) a' b' z₀ (pmoebius K₀ (ρ (s q))⁻¹ z) =
          (∏ q : G ⧸ Γ', theta (ρ.comp Γ'.subtype) a' b' z₀ (pmoebius K₀ (ρ (s q))⁻¹ z₀)) * theta ρ a' b' z₀ z) ∧
      ∏ q : G ⧸ Γ', Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ (s q)) (thetaMer ϖ (ρ.comp Γ'.subtype) a' b' z₀) =
        algebraMap K (merField ϖ) (∏ q : G ⧸ Γ', theta (ρ.comp Γ'.subtype) a' b' z₀ (pmoebius K₀ (ρ (s q))⁻¹ z₀)) *
          thetaMer ϖ ρ a' b' z₀ := by
  refine ⟨norm_pointwise K₀ K ϖ hex ρ hρ Γ' s hs ha' hb' hz₀ hz₀a hz₀b, ?_⟩
  have hρ' : IsDiscrete K (ρ.comp Γ'.subtype) := isDiscrete_comp_subtype K hρ Γ'
  have hz₀a' : ∀ γ : ↥Γ', pmoebius K₀ ((ρ.comp Γ'.subtype) γ) a' ≠ z₀ := fun γ => hz₀a γ
  have hz₀b' : ∀ γ : ↥Γ', pmoebius K₀ ((ρ.comp Γ'.subtype) γ) b' ≠ z₀ := fun γ => hz₀b γ
  obtain ⟨F, H, hFH, -⟩ := exists_isThetaPair_thetaMer_eq_mk K₀ K ϖ hex ρ hρ ha' hb' hz₀ hz₀a hz₀b
  obtain ⟨F', H', hFH', -⟩ :=
    exists_isThetaPair_thetaMer_eq_mk K₀ K ϖ hex (ρ.comp Γ'.subtype) hρ' ha' hb' hz₀ hz₀a' hz₀b'
  have hHne : H ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hFH.1
  have hH'ne : H' ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hFH'.1
  have hgH'ne : ∀ q : G ⧸ Γ', ρ (s q) • H' ≠ 0 := by
    intro q h0
    apply hH'ne
    have := congrArg (fun f => (ρ (s q))⁻¹ • f) h0
    simpa only [smul_zero, inv_smul_smul] using this
  have eq' : ∀ q : G ⧸ Γ',
      Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ (s q)) (thetaMer ϖ (ρ.comp Γ'.subtype) a' b' z₀) *
          algebraMap ↥(holRing ϖ) (merField ϖ) (ρ (s q) • H') =
        algebraMap ↥(holRing ϖ) (merField ϖ) (ρ (s q) • F') := by
    intro q
    have h := congrArg (Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ (s q)))
      (thetaMer_mul_algebraMap_eq_of_isThetaPair ϖ (ρ.comp Γ'.subtype) a' b' z₀ F' H' hFH')
    rw [map_mul, Mumford.fracAct_algebraMap, Mumford.fracAct_algebraMap] at h
    exact h
  exact norm_frac ϖ (fun q => Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ (s q)) (thetaMer ϖ (ρ.comp Γ'.subtype) a' b' z₀))
    (thetaMer ϖ ρ a' b' z₀) _ F H (fun q => ρ (s q) • F') (fun q => ρ (s q) • H') eq'
    (thetaMer_mul_algebraMap_eq_of_isThetaPair ϖ ρ a' b' z₀ F H hFH) hHne hgH'ne
    (norm_key K₀ K ϖ hex ρ hρ Γ' s hs ha' hb' hz₀ hz₀a hz₀b F H hFH F' H' hFH')

end S_CerednikDrinfeld_Omega_prod_theta_comp_subtype_pmoebius_eq_mul_theta_and_prod_fracAct_thetaMer_eq
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_prod_theta_comp_subtype_pmoebius_eq_mul_theta_and_prod_fracAct_thetaMer_eq (solution)
