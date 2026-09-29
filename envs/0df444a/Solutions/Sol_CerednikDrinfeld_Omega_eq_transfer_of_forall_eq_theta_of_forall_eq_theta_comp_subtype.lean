-- Prove2me | solution 1 for CerednikDrinfeld.Omega.eq_transfer_of_forall_eq_theta_of_forall_eq_theta_comp_subtype
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/9c03266d-7881-5d4c-ac31-51c7cbac4c6c

import Mathlib
import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Theorems.Thm_CerednikDrinfeld_Omega_exists_isThetaPair_thetaMer_eq_mk
import Theorems.Thm_CerednikDrinfeld_Omega_thetaMer_mul_algebraMap_eq_of_isThetaPair
import Theorems.Thm_CerednikDrinfeld_Omega_exists_monoidHom_fracAct_thetaMer_eq
import Theorems.Thm_CerednikDrinfeld_Omega_fracAct_prod_fracAct_eq_transfer_inv_mul
import Theorems.Thm_CerednikDrinfeld_Omega_prod_theta_comp_subtype_pmoebius_eq_mul_theta_and_prod_fracAct_thetaMer_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_eq_transfer_of_forall_eq_theta_of_forall_eq_theta_comp_subtype

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

namespace NatOmegaTM

theorem isDiscrete_comp_subtype {K₀ : Type*} [Field K₀] (K : Type*) [Field K] [Algebra K₀ K]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    {G : Type*} [Group G] {ρ : G →* PGL(2, K₀)} (hρ : IsDiscrete K ρ) (Γ' : Subgroup G) :
    IsDiscrete K (ρ.comp Γ'.subtype) := by
  intro ε hε
  have hfin := (hρ ε hε).preimage (Subtype.val_injective (p := fun x => x ∈ Γ')).injOn
  refine hfin.subset ?_
  intro γ hγ
  simpa only [Set.mem_preimage, Set.mem_setOf_eq, MonoidHom.comp_apply, Subgroup.coe_subtype] using hγ

theorem thetaMer_ne_zero
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) [IsDomain ↥(holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    {a b z₀ : K} (ha : a ∈ upperHalfPlane K₀ K) (hb : b ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b ≠ z₀) :
    thetaMer ϖ ρ a b z₀ ≠ 0 := by
  obtain ⟨F, H, hFH, -⟩ := exists_isThetaPair_thetaMer_eq_mk K₀ K ϖ hex ρ hρ ha hb hz₀ hz₀a hz₀b
  intro h0
  have hF : algebraMap ↥(holRing ϖ) (merField ϖ) F = 0 := by
    rw [← thetaMer_mul_algebraMap_eq_of_isThetaPair ϖ ρ a b z₀ F H hFH, h0, zero_mul]
  have hF0 : F = 0 := (map_eq_zero_iff _ (IsFractionRing.injective ↥(holRing ϖ) (merField ϖ))).mp hF
  have hval : (F : ↥(upperHalfPlane K₀ K) → K) ⟨z₀, hz₀⟩ ≠ 0 := by
    intro h
    obtain ⟨γ, hγ⟩ := (hFH.2.2.1 ⟨z₀, hz₀⟩).mp h
    exact hz₀a γ hγ
  apply hval
  rw [hF0]
  rfl

theorem prod_theta_shift_ne_zero
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) [IsDomain ↥(holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (Γ' : Subgroup G) [Fintype (G ⧸ Γ')] (s : G ⧸ Γ' → G)
    {a' b' z₀ : K} (ha' : a' ∈ upperHalfPlane K₀ K) (hb' : b' ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a' ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b' ≠ z₀) :
    ∏ q : G ⧸ Γ', theta (ρ.comp Γ'.subtype) a' b' z₀ (pmoebius K₀ (ρ (s q))⁻¹ z₀) ≠ 0 := by
  have hρ' : IsDiscrete K (ρ.comp Γ'.subtype) := isDiscrete_comp_subtype K hρ Γ'
  have hz₀a' : ∀ γ : ↥Γ', pmoebius K₀ ((ρ.comp Γ'.subtype) γ) a' ≠ z₀ := fun γ => hz₀a γ
  have hz₀b' : ∀ γ : ↥Γ', pmoebius K₀ ((ρ.comp Γ'.subtype) γ) b' ≠ z₀ := fun γ => hz₀b γ
  obtain ⟨F', H', hFH', -⟩ :=
    exists_isThetaPair_thetaMer_eq_mk K₀ K ϖ hex (ρ.comp Γ'.subtype) hρ' ha' hb' hz₀ hz₀a' hz₀b'
  have unshift : ∀ (q : G ⧸ Γ') {x : K}, x ∈ upperHalfPlane K₀ K →
      pmoebius K₀ (ρ (s q)) (pmoebius K₀ (ρ (s q))⁻¹ x) = x := by
    intro q x hx; rw [← pmoebius_mul K₀ hx, mul_inv_cancel, pmoebius_one]
  refine Finset.prod_ne_zero_iff.mpr fun q _ => ?_
  let w : ↥(upperHalfPlane K₀ K) := ⟨pmoebius K₀ (ρ (s q))⁻¹ z₀, pmoebius_mem_upperHalfPlane K₀ hz₀ _⟩
  have hwa : ¬ ∃ γ' : ↥Γ', pmoebius K₀ ((ρ.comp Γ'.subtype) γ') a' = (w : K) := by
    rintro ⟨γ', h'⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at h'
    apply hz₀a (s q * (γ' : G))
    rw [map_mul, pmoebius_mul K₀ ha', h']
    exact unshift q hz₀
  have hwb : ¬ ∃ γ' : ↥Γ', pmoebius K₀ ((ρ.comp Γ'.subtype) γ') b' = (w : K) := by
    rintro ⟨γ', h'⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at h'
    apply hz₀b (s q * (γ' : G))
    rw [map_mul, pmoebius_mul K₀ hb', h']
    exact unshift q hz₀
  change theta (ρ.comp Γ'.subtype) a' b' z₀ (w : K) ≠ 0
  rw [← hFH'.2.2.2 w hwb]
  exact div_ne_zero (fun h => hwa ((hFH'.2.2.1 w).mp h)) (fun h => hwb ((hFH'.2.1 w).mp h))

end NatOmegaTM

open NatOmegaTM in
theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [CompleteSpace K]
    (ϖ : PseudoUniformizer K₀ K) (hex : IsExhausted ϖ) [IsDomain ↥(holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀)) (hρ : IsDiscrete K ρ)
    (Γ' : Subgroup G) [Γ'.FiniteIndex]
    {a' b' z₀ : K} (ha' : a' ∈ upperHalfPlane K₀ K) (hb' : b' ∈ upperHalfPlane K₀ K) (hz₀ : z₀ ∈ upperHalfPlane K₀ K)
    (hz₀a : ∀ γ : G, pmoebius K₀ (ρ γ) a' ≠ z₀) (hz₀b : ∀ γ : G, pmoebius K₀ (ρ γ) b' ≠ z₀)
    (c' : ↥Γ' →* Kˣ) (hc' : ∀ β : ↥Γ', ((c' β : Kˣ) : K) = theta (ρ.comp Γ'.subtype) a' b' z₀ (pmoebius K₀ (ρ β) z₀))
    (c : G →* Kˣ) (hc : ∀ β : G, ((c β : Kˣ) : K) = theta ρ a' b' z₀ (pmoebius K₀ (ρ β) z₀)) :
    c = MonoidHom.transfer c' := by
  classical
  haveI : Fintype (G ⧸ Γ') := Fintype.ofFinite _
  let s : G ⧸ Γ' → G := Quotient.out
  have hs : ∀ q : G ⧸ Γ', (QuotientGroup.mk (s q) : G ⧸ Γ') = q := fun q => Quotient.out_eq q
  have hρ' : IsDiscrete K (ρ.comp Γ'.subtype) := isDiscrete_comp_subtype K hρ Γ'
  have hz₀a' : ∀ γ : ↥Γ', pmoebius K₀ ((ρ.comp Γ'.subtype) γ) a' ≠ z₀ := fun γ => hz₀a γ
  have hz₀b' : ∀ γ : ↥Γ', pmoebius K₀ ((ρ.comp Γ'.subtype) γ) b' ≠ z₀ := fun γ => hz₀b γ

  obtain ⟨d', hd'v, hd'act⟩ :=
    exists_monoidHom_fracAct_thetaMer_eq K₀ K ϖ hex (ρ.comp Γ'.subtype) hρ' ha' hb' hz₀ hz₀a' hz₀b'
  obtain ⟨d, hdv, hdact⟩ := exists_monoidHom_fracAct_thetaMer_eq K₀ K ϖ hex ρ hρ ha' hb' hz₀ hz₀a hz₀b
  have hd' : d' = c' := MonoidHom.ext fun β => Units.ext (by rw [hd'v, hc']; rfl)
  have hd : d = c := MonoidHom.ext fun β => Units.ext (by rw [hdv, hc])
  subst hd' hd

  have hT := fracAct_prod_fracAct_eq_transfer_inv_mul K₀ K ϖ ρ Γ' s hs
    (thetaMer ϖ (ρ.comp Γ'.subtype) a' b' z₀) d' (fun γ => hd'act γ)

  have hN := (prod_theta_comp_subtype_pmoebius_eq_mul_theta_and_prod_fracAct_thetaMer_eq K₀ K ϖ hex ρ hρ Γ' s hs
    ha' hb' hz₀ hz₀a hz₀b).2

  have hC := prod_theta_shift_ne_zero K₀ K ϖ hex ρ hρ Γ' s ha' hb' hz₀ hz₀a hz₀b
  have hΘ := thetaMer_ne_zero K₀ K ϖ hex ρ hρ ha' hb' hz₀ hz₀a hz₀b
  have hNne : ∏ q : G ⧸ Γ', Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ (s q))
      (thetaMer ϖ (ρ.comp Γ'.subtype) a' b' z₀) ≠ 0 := by
    rw [hN]
    exact mul_ne_zero ((map_ne_zero_iff _ (algebraMap K (merField ϖ)).injective).mpr hC) hΘ

  refine MonoidHom.ext fun γ => ?_
  have h1 := hT γ
  have h2 : Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ γ)
      (∏ q : G ⧸ Γ', Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ (s q)) (thetaMer ϖ (ρ.comp Γ'.subtype) a' b' z₀)) =
      algebraMap K (merField ϖ) (((d γ)⁻¹ : Kˣ) : K) *
        ∏ q : G ⧸ Γ', Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ (s q)) (thetaMer ϖ (ρ.comp Γ'.subtype) a' b' z₀) := by
    rw [hN, map_mul, hdact γ, ← Mumford.frac_smul_def, Mumford.smul_algebraMap_const]
    ring
  have h3 : algebraMap K (merField ϖ) (((MonoidHom.transfer d' γ)⁻¹ : Kˣ) : K) =
      algebraMap K (merField ϖ) (((d γ)⁻¹ : Kˣ) : K) :=
    mul_right_cancel₀ hNne (h1.symm.trans h2)
  have h4 : ((MonoidHom.transfer d' γ)⁻¹ : Kˣ) = (d γ)⁻¹ :=
    Units.ext ((algebraMap K (merField ϖ)).injective h3)
  exact (inv_inj.mp h4).symm

end S_CerednikDrinfeld_Omega_eq_transfer_of_forall_eq_theta_of_forall_eq_theta_comp_subtype
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_eq_transfer_of_forall_eq_theta_of_forall_eq_theta_comp_subtype (solution)
