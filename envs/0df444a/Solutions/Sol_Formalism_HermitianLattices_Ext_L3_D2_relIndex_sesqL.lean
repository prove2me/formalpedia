-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.D2.relIndex_sesqL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:05:57.929639+00:00
-- url     : https://prove2.me/submissions/96fbb92a-8e06-49e3-8b9d-e6f9f0ec0d08

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulSpanIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MulMemPrimePower
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqMapMulKer
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_J_mul_mem_pK_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_J_nO_prod
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_J_nO_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_J_form_rel
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_J_gram_rel
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_algebraMap_mem_pK
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_exists_smith
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mem_sesqL_iff
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_nO_gram
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_nO_mul
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_nO_ne_zero
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_nO_star
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_relIndex_matL
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_star_mem_pK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.D2
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {B₀ : Submodule (𝓞 K) V}
    (hB₀ : Submodule.IsLattice K B₀) (hB₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {k c : ℕ}
    (hle : sesqL (locF 𝔭 B₀) 𝔭 (k + c) ≤ sesqL (locF 𝔭 A₀) 𝔭 k) :
    (sesqL (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (sesqL (locF 𝔭 A₀) 𝔭 k) *
        Ideal.absNorm 𝔭 ^ (2 * (finrank K V * vd h (locF 𝔭 B₀) 𝔭)) =
      Ideal.absNorm 𝔭 ^ (2 * (finrank K V ^ 2 * c + finrank K V * vd h (locF 𝔭 A₀) 𝔭)) := by
  classical
  obtain ⟨a, b, e, γ, hγ, he, hA, hB, hab⟩ := exists_smith hA₀ hB₀ h𝔭
  have habK : ∀ i, (γ : K) • b i = (e i : K) • a i := fun i => by
    rw [algebraMap_smul, algebraMap_smul]
    exact hab i
  have hγK : (γ : K) ≠ 0 := fun h0 =>
    hγ (RingOfIntegers.ext (h0.trans (map_zero (algebraMap (𝓞 K) K)).symm))
  have heK : ∀ i, (e i : K) ≠ 0 := fun i h0 =>
    he i (RingOfIntegers.ext (h0.trans (map_zero (algebraMap (𝓞 K) K)).symm))
  have hγm : (γ : K) ∈ pK K 𝔭 0 := algebraMap_mem_pK 𝔭 γ
  have hem : ∀ i, (e i : K) ∈ pK K 𝔭 0 := fun i => algebraMap_mem_pK 𝔭 (e i)
  have hγγ : star (γ : K) * γ ∈ pK K 𝔭 0 ∧ star (γ : K) * γ ≠ 0 :=
    ⟨J.mul_mem_pK_zero h𝔭 (star_mem_pK hF h𝔭 hγm) hγm, mul_ne_zero (star_ne_zero.2 hγK) hγK⟩
  let Φ : (V →ₗ⋆[K] V →ₗ[K] K) →+ Matrix (Fin (finrank K V)) (Fin (finrank K V)) K :=
    (LinearMap.toMatrix₂ a a).toLinearMap.toAddMonoidHom
  have hΦ : ∀ s i j, Φ s i j = s (a i) (a j) := fun s i j => LinearMap.toMatrix₂_apply a a s i j
  have hΦs : Function.Surjective Φ := (LinearMap.toMatrix₂ a a).surjective
  let f : Fin (finrank K V) → Fin (finrank K V) → K := fun i j => star (e i : K) * (e j : K)
  let g : Fin (finrank K V) → Fin (finrank K V) → K := fun _ _ => star (γ : K) * γ
  have hSA : sesqL (locF 𝔭 A₀) 𝔭 k = (matL 𝔭 k (fun _ _ => 1) (fun _ _ => 1)).comap Φ := by
    ext s
    rw [← hA, mem_sesqL_iff hF a h𝔭]
    constructor
    · intro H i j
      exact ⟨_, H i j, by rw [hΦ]⟩
    · intro H i j
      obtain ⟨w, hw, e⟩ := H i j
      rw [one_mul, one_mul, hΦ] at e
      rwa [e]
  have hSB : sesqL (locF 𝔭 B₀) 𝔭 (k + c) = (matL 𝔭 (k + c) f g).comap Φ := by
    ext s
    rw [← hB, mem_sesqL_iff hF b h𝔭]
    constructor
    · intro H i j
      exact ⟨_, H i j, by rw [hΦ]; exact (J.form_rel s (habK i) (habK j)).symm⟩
    · intro H i j
      obtain ⟨w, hw, e⟩ := H i j
      rw [hΦ] at e
      have e2 : star (γ : K) * γ * s (b i) (b j) = star (γ : K) * γ * w :=
        (J.form_rel s (habK i) (habK j)).trans e
      rwa [mul_left_cancel₀ hγγ.2 e2]
  have hle' : matL 𝔭 (k + c) f g ≤ matL 𝔭 k (fun _ _ => 1) (fun _ _ => 1) := by
    rw [hSA, hSB] at hle
    exact (AddSubgroup.comap_le_comap_of_surjective hΦs).1 hle
  have hf : ∀ i j, f i j ∈ pK K 𝔭 0 ∧ f i j ≠ 0 := fun i j =>
    ⟨J.mul_mem_pK_zero h𝔭 (star_mem_pK hF h𝔭 (hem i)) (hem j),
      mul_ne_zero (star_ne_zero.2 (heK i)) (heK j)⟩
  have H1 := relIndex_matL hK hF h𝔭 f g hf (fun _ _ => hγγ) k c hle'
  have hidx : (sesqL (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (sesqL (locF 𝔭 A₀) 𝔭 k) =
      (matL 𝔭 (k + c) f g).relIndex (matL 𝔭 k (fun _ _ => 1) (fun _ _ => 1)) := by
    rw [hSA, hSB, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hΦs]
  rw [← hidx] at H1
  obtain ⟨hDa, hDa0, hDan⟩ := nO_gram hK hF hs hd hA₀ hA₀i h𝔭 a hA
  obtain ⟨hDb, hDb0, hDbn⟩ := nO_gram hK hF hs hd hB₀ hB₀i h𝔭 b hB
  have hnf : ∀ i j, nO 𝔭 (f i j) = nO 𝔭 (e i : K) * nO 𝔭 (e j : K) := fun i j => by
    rw [nO_mul h𝔭 (star_mem_pK hF h𝔭 (hem i)) (star_ne_zero.2 (heK i)) (hem j), nO_star hF h𝔭]
  have hng : nO 𝔭 (star (γ : K) * γ) = nO 𝔭 (γ : K) * nO 𝔭 (γ : K) := by
    rw [nO_mul h𝔭 (star_mem_pK hF h𝔭 hγm) (star_ne_zero.2 hγK) hγm, nO_star hF h𝔭]
  have H2 := congrArg (nO 𝔭) (J.gram_rel h a b (fun i => (e i : K)) γ habK)
  have hp1 := J.nO_prod h𝔭 Finset.univ (fun i => star (e i : K))
    (fun i => ⟨star_mem_pK hF h𝔭 (hem i), star_ne_zero.2 (heK i)⟩)
  have hp2 := J.nO_prod h𝔭 Finset.univ (fun i => (e i : K)) (fun i => ⟨hem i, heK i⟩)
  have hp3 := J.nO_pow h𝔭 hγγ.1 hγγ.2 (finrank K V)
  rw [nO_mul h𝔭 hp3.1 (pow_ne_zero _ hγγ.2) hDb, hp3.2, hng, hDbn,
    nO_mul h𝔭 (J.mul_mem_pK_zero h𝔭 hp1.1 hp2.1)
      (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => star_ne_zero.2 (heK i))
        (Finset.prod_ne_zero_iff.2 fun i _ => heK i)) hDa,
    nO_mul h𝔭 hp1.1 (Finset.prod_ne_zero_iff.2 fun i _ => star_ne_zero.2 (heK i)) hp2.1,
    hp1.2, hp2.2, hDan] at H2
  simp only [nO_star hF h𝔭] at H2
  simp only [hnf, g, hng, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.prod_pow] at H1
  have hE0 : (∏ i, nO 𝔭 (e i : K)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => nO_ne_zero hK hF h𝔭 (hem i) (heK i)
  generalize (∏ i, nO 𝔭 (e i : K)) = E at H1 H2 hE0
  generalize nO 𝔭 (γ : K) = G at H1 H2
  generalize (sesqL (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (sesqL (locF 𝔭 A₀) 𝔭 k) = X at H1 ⊢
  generalize Ideal.absNorm 𝔭 = q at H1 H2 ⊢
  generalize vd h (locF 𝔭 A₀) 𝔭 = vA at H2 ⊢
  generalize vd h (locF 𝔭 B₀) 𝔭 = vB at H2 ⊢
  generalize finrank K V = m at H1 H2 ⊢
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (mul_ne_zero (pow_ne_zero m hE0) (pow_ne_zero m hE0)))
  calc X * q ^ (2 * (m * vB)) * (E ^ m * E ^ m) = (X * (E ^ m * E ^ m)) * q ^ (2 * (m * vB)) := by ring
    _ = (G ^ m) ^ m * (G ^ m) ^ m * q ^ (2 * m ^ 2 * c) * q ^ (2 * (m * vB)) := by rw [H1]
    _ = ((G * G) ^ m * q ^ (2 * vB)) ^ m * q ^ (2 * m ^ 2 * c) := by ring
    _ = (E * E * q ^ (2 * vA)) ^ m * q ^ (2 * m ^ 2 * c) := by rw [H2]
    _ = q ^ (2 * (m ^ 2 * c + m * vA)) * (E ^ m * E ^ m) := by ring
end Formalism.HermitianLattices.Ext.L3.D2
