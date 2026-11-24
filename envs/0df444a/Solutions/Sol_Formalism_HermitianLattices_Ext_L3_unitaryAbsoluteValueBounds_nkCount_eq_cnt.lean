-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds.nkCount_eq_cnt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:59:37.741302+00:00
-- url     : https://prove2.me/submissions/75cdf5a5-5a33-4737-bd0c-f5455c78dae7

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldBis
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityFieldTer
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_form_lin
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_mk_lin_eq_iff
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MeanB_card_quot_extP
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormLifting_conjQ_mk
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_conjO_mem_pow
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_integralBasisSpans_congrP_int
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_unitaryAbsoluteValueBounds_exists_frame
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vectorCountBounds_card_vec
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_vectorCountBounds_finite_vec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


section
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
private theorem exists_mem_ideal_form_eq_of_mem_ideal_smul {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (I : Ideal (𝓞 K)) (w x : ↥L)
    (hx : x ∈ (I • ⊤ : Submodule (𝓞 K) ↥L)) :
    ∃ y ∈ I, h (w : V) (x : V) = algebraMap (𝓞 K) K y := by
  refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)
  · obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hLi (w : V) w.2 (m : V) m.2)
    refine ⟨r * o, Ideal.mul_mem_right _ _ hr, ?_⟩
    rw [Submodule.coe_smul, ← algebraMap_smul K r (m : V), map_smul, smul_eq_mul, map_mul, ho]
  · obtain ⟨u, hu, hu'⟩ := hx
    obtain ⟨v, hv, hv'⟩ := hy
    exact ⟨u + v, Ideal.add_mem _ hu hv, by rw [Submodule.coe_add, map_add, hu', hv', map_add]⟩
private theorem exists_mem_extP_pow_form_eq_of_mem_extP_pow_smul (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (w x : ↥L)
    (hx : x ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :
    ∃ y ∈ extP K 𝔭 ^ k, h (x : V) (w : V) = algebraMap (𝓞 K) K y := by
  refine Submodule.smul_induction_on hx (fun r hr m _ => ?_) (fun x y hx hy => ?_)
  · obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hLi (m : V) m.2 (w : V) w.2)
    refine ⟨conjO K r * o, Ideal.mul_mem_right _ _ (idealPowerSpanBounds.conjO_mem_pow hF 𝔭 k r hr), ?_⟩
    rw [Submodule.coe_smul, ← algebraMap_smul K r (m : V), LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, map_mul, ho]
    congr 1 <;> simp [conjO]
  · obtain ⟨u, hu, hu'⟩ := hx
    obtain ⟨v, hv, hv'⟩ := hy
    exact ⟨u + v, Ideal.add_mem _ hu hv, by
      rw [Submodule.coe_add, map_add, LinearMap.add_apply, hu', hv', map_add]⟩
section Frame
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V} {m : ℕ} (z : Fin m → ↥L) (g : Fin m → 𝓞 K)
variable {z g}
end Frame
private theorem quotient_norm_congr_of_quotient_eq (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (𝔭 : Ideal (𝓞 F)) (k : ℕ) (y y₀ : ↥L)
    (hy : (Submodule.Quotient.mk y : ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
      Submodule.Quotient.mk y₀)
    (o o₀ : 𝓞 K) (ho : h (y : V) (y : V) = algebraMap (𝓞 K) K o)
    (ho₀ : h (y₀ : V) (y₀ : V) = algebraMap (𝓞 K) K o₀) :
    Ideal.Quotient.mk (extP K 𝔭 ^ k) o = Ideal.Quotient.mk (extP K 𝔭 ^ k) o₀ := by
  rw [Submodule.Quotient.eq] at hy
  obtain ⟨u1, hu1, he1⟩ := exists_mem_ideal_form_eq_of_mem_ideal_smul hLi (extP K 𝔭 ^ k) y₀ (y - y₀) hy
  obtain ⟨u2, hu2, he2⟩ := exists_mem_extP_pow_form_eq_of_mem_extP_pow_smul hF hLi 𝔭 k y₀ (y - y₀) hy
  obtain ⟨u3, hu3, he3⟩ := exists_mem_ideal_form_eq_of_mem_ideal_smul hLi (extP K 𝔭 ^ k) (y - y₀) (y - y₀) hy
  have hyx : y = y₀ + (y - y₀) := by abel
  have hsum : o = o₀ + u1 + u2 + u3 := by
    apply IsFractionRing.injective (𝓞 K) K
    rw [← ho, hyx]
    simp only [Submodule.coe_add, map_add, LinearMap.add_apply]
    rw [he1, he2, he3, ← ho₀]
    ring
  rw [Ideal.Quotient.eq, hsum, show o₀ + u1 + u2 + u3 - o₀ = u1 + u2 + u3 by ring]
  exact Ideal.add_mem _ (Ideal.add_mem _ hu1 hu2) hu3
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
end
end

set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) {k : ℕ} (hk : 1 ≤ k) (n : 𝓞 F) :
    nkCount h L 𝔭 k n = cnt hF 𝔭 k (finrank K V) (ι n) := by
  obtain ⟨z, g, hzo, hzg, hg1⟩ := exists_frame hK hF hs hd hL hLi h𝔭 hv hk
  have hint : ∀ y : ↥L, ∃ o : 𝓞 K, h (y : V) (y : V) = algebraMap (𝓞 K) K o := fun y =>
    let ⟨o, ho⟩ := Submodule.mem_one.mp (hLi (y : V) y.2 (y : V) y.2)
    ⟨o, ho.symm⟩
  have hn : algebraMap F K (n : F) = algebraMap (𝓞 K) K (ι n) := rfl
  let lift : (Fin (finrank K V) → AQ K 𝔭 k) → Fin (finrank K V) → 𝓞 K :=
    fun x i => (Ideal.Quotient.mk_surjective (x i)).choose
  have hlift : ∀ x i, Ideal.Quotient.mk (extP K 𝔭 ^ k) (lift x i) = x i :=
    fun x i => (Ideal.Quotient.mk_surjective (x i)).choose_spec
  let Φ : (Fin (finrank K V) → AQ K 𝔭 k) → ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) :=
    fun x => Submodule.Quotient.mk (lin z (lift x))
  have hinj : Function.Injective Φ := by
    intro x x' hxx
    have hd := (mk_lin_eq_iff hLi 𝔭 k hzo hzg hg1 (lift x) (lift x')).mp hxx
    funext i
    rw [← hlift x i, ← hlift x' i, Ideal.Quotient.eq]
    exact hd i
  haveI : Fact (IsFixF K F) := ⟨hF⟩
  haveI : Finite (Fin (finrank K V) → AQ K 𝔭 k) := vectorCountBounds.finite_vec h𝔭 k
  have hcard : Nat.card (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) =
      Nat.card (Fin (finrank K V) → AQ K 𝔭 k) := by
    rw [MeanB.card_quot_extP hK hF hL h𝔭 k, vectorCountBounds.card_vec hK h𝔭 k, Fintype.card_fin]
    ring_nf
  haveI : Finite (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Nat.card_pos.ne')
  have hbij : Function.Bijective Φ := hinj.bijective_of_nat_card_le hcard.le
  have hsum : ∀ x, Ideal.Quotient.mk (extP K 𝔭 ^ k) (∑ i, conjO K (lift x i) * lift x i * g i) =
      ∑ i, sg hF 𝔭 k (x i) * x i := by
    intro x
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hg : Ideal.Quotient.mk (extP K 𝔭 ^ k) (g i) = 1 := by
      rw [← map_one (Ideal.Quotient.mk (extP K 𝔭 ^ k)), Ideal.Quotient.eq]
      exact hg1 i
    rw [map_mul, map_mul, hg, mul_one]
    conv_rhs => rw [← hlift x i]
    unfold sg
    rw [NormLifting.conjQ_mk]
  unfold nkCount cnt
  refine (Nat.card_congr ((Equiv.ofBijective Φ hbij).subtypeEquiv (fun x => ?_))).symm
  show _ ↔ ∃ y : ↥L, Submodule.Quotient.mk y = Φ x ∧ _
  constructor
  · intro hx
    refine ⟨lin z (lift x), rfl, ?_⟩
    rw [form_lin hzo hzg, hn, integralBasisSpans.congrP_int h𝔭, hsum x, hx]
  · rintro ⟨y, hy, hc⟩
    obtain ⟨o, ho⟩ := hint y
    have hcg := quotient_norm_congr_of_quotient_eq hF hLi 𝔭 k y (lin z (lift x)) hy o _ ho (form_lin hzo hzg (lift x))
    rw [ho, hn, integralBasisSpans.congrP_int h𝔭, hcg, hsum x] at hc
    exact hc
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
