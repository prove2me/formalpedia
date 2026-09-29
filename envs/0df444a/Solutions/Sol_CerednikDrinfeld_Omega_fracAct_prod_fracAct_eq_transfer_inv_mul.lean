-- Prove2me | solution 1 for CerednikDrinfeld.Omega.fracAct_prod_fracAct_eq_transfer_inv_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0abb1d80-25d4-5a0f-a11d-874680f59c2e

import Definitions.Def_CerednikDrinfeld_ThetaMer
import Definitions.Def_CerednikDrinfeld_DiscreteProjectiveAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotient
import Mathlib.GroupTheory.Transfer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_fracAct_prod_fracAct_eq_transfer_inv_mul

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

namespace NatOmegaTA

open CerednikDrinfeld

variable {G : Type} [Group G]

theorem transfer_eq_prod_section {A : Type} [CommGroup A] (Γ' : Subgroup G) [Γ'.FiniteIndex]
    [Fintype (G ⧸ Γ')] (s : G ⧸ Γ' → G) (hs : ∀ q : G ⧸ Γ', (QuotientGroup.mk (s q) : G ⧸ Γ') = q)
    (χ : ↥Γ' →* A) (γ : G)
    (hmem : ∀ q : G ⧸ Γ', (s (γ • q))⁻¹ * (γ * s q) ∈ Γ') :
    MonoidHom.transfer χ γ = ∏ q : G ⧸ Γ', χ ⟨(s (γ • q))⁻¹ * (γ * s q), hmem q⟩ := by
  classical

  obtain rfl : ‹Fintype (G ⧸ Γ')› = Γ'.fintypeQuotientOfFiniteIndex := Subsingleton.elim _ _
  letI : Fintype (G ⧸ Γ') := Γ'.fintypeQuotientOfFiniteIndex
  let T : Γ'.LeftTransversal := ⟨Set.range s, Subgroup.isComplement_range_left hs⟩
  have hT : ∀ q : G ⧸ Γ', ((T.2.leftQuotientEquiv q : G)) = s q :=
    fun q => Subgroup.IsComplement.leftQuotientEquiv_apply hs q
  rw [MonoidHom.transfer_def χ T γ, Subgroup.leftTransversals.diff]

  refine (Fintype.prod_equiv (MulAction.toPerm γ) _ _ fun q => ?_).symm
  congr 1
  apply Subtype.ext
  simp only [MulAction.toPerm_apply]
  rw [Subgroup.smul_apply_eq_smul_apply_inv_smul γ T (γ • q), inv_smul_smul, hT, hT, smul_eq_mul]

end NatOmegaTA

open NatOmegaTA CerednikDrinfeld in

theorem solution
    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (ϖ : PseudoUniformizer K₀ K) [IsDomain ↥(holRing ϖ)]
    {G : Type} [Group G] (ρ : G →* PGL(2, K₀))
    (Γ' : Subgroup G) [Γ'.FiniteIndex] [Fintype (G ⧸ Γ')] (s : G ⧸ Γ' → G) (hs : ∀ q : G ⧸ Γ', (QuotientGroup.mk (s q) : G ⧸ Γ') = q)
    (f : merField ϖ) (χ : ↥Γ' →* Kˣ)
    (hf : ∀ γ : ↥Γ', Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ γ) f =
      algebraMap K (merField ϖ) (((χ γ)⁻¹ : Kˣ) : K) * f) :
    ∀ γ : G, Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ γ)
        (∏ q : G ⧸ Γ', Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ (s q)) f) =
      algebraMap K (merField ϖ) (((MonoidHom.transfer χ γ)⁻¹ : Kˣ) : K) *
        ∏ q : G ⧸ Γ', Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) (ρ (s q)) f := by
  classical
  intro γ

  set Φ : PGL(2, K₀) → (merField ϖ ≃+* merField ϖ) := fun g => Mumford.fracAct PGL(2, K₀) ↥(holRing ϖ) g with hΦ
  have hcomp : ∀ (g h : G) (x : merField ϖ), Φ (ρ g) (Φ (ρ h) x) = Φ (ρ (g * h)) x := by
    intro g h x
    simp only [hΦ, map_mul, Mumford.fracAct_mul]
    rfl
  have hconst : ∀ (g : G) (c : K), Φ (ρ g) (algebraMap K (merField ϖ) c) = algebraMap K (merField ϖ) c := by
    intro g c
    have := Mumford.smul_algebraMap_const K PGL(2, K₀) ↥(holRing ϖ) (ρ g) c
    rwa [Mumford.frac_smul_def] at this

  have hmem : ∀ q : G ⧸ Γ', (s (γ • q))⁻¹ * (γ * s q) ∈ Γ' := by
    intro q
    rw [← QuotientGroup.eq, hs]
    conv_rhs => rw [← smul_eq_mul, ← MulAction.Quotient.smul_coe, hs]
  have hterm : ∀ q : G ⧸ Γ', Φ (ρ γ) (Φ (ρ (s q)) f) =
      algebraMap K (merField ϖ) (((χ ⟨_, hmem q⟩)⁻¹ : Kˣ) : K) * Φ (ρ (s (γ • q))) f := by
    intro q
    rw [hcomp]
    have hdec : γ * s q = s (γ • q) * ((s (γ • q))⁻¹ * (γ * s q)) := by group
    conv_lhs => rw [hdec]
    rw [← hcomp]
    have := hf ⟨_, hmem q⟩
    rw [show (ρ ((s (γ • q))⁻¹ * (γ * s q))) = ρ (↑(⟨(s (γ • q))⁻¹ * (γ * s q), hmem q⟩ : ↥Γ')) from rfl, this,
      map_mul, hconst]

  calc Φ (ρ γ) (∏ q : G ⧸ Γ', Φ (ρ (s q)) f)
      = ∏ q : G ⧸ Γ', Φ (ρ γ) (Φ (ρ (s q)) f) := map_prod (Φ (ρ γ)) _ _
    _ = ∏ q : G ⧸ Γ', (algebraMap K (merField ϖ) (((χ ⟨_, hmem q⟩)⁻¹ : Kˣ) : K) * Φ (ρ (s (γ • q))) f) :=
        Finset.prod_congr rfl fun q _ => hterm q
    _ = (∏ q : G ⧸ Γ', algebraMap K (merField ϖ) (((χ ⟨_, hmem q⟩)⁻¹ : Kˣ) : K)) *
          ∏ q : G ⧸ Γ', Φ (ρ (s (γ • q))) f := Finset.prod_mul_distrib
    _ = algebraMap K (merField ϖ) (((MonoidHom.transfer χ γ)⁻¹ : Kˣ) : K) *
          ∏ q : G ⧸ Γ', Φ (ρ (s q)) f := by
        congr 1
        · rw [← map_prod (algebraMap K (merField ϖ)), ← Units.coe_prod, Finset.prod_inv_distrib,
            transfer_eq_prod_section Γ' s hs χ γ hmem]
        · exact (Fintype.prod_equiv (MulAction.toPerm γ) _ _ fun q => rfl)

end S_CerednikDrinfeld_Omega_fracAct_prod_fracAct_eq_transfer_inv_mul
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_fracAct_prod_fracAct_eq_transfer_inv_mul (solution)
