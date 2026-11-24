-- Prove2me | solution 1 for Formalism.G0.AllButLESmithP.up
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:44.204895+00:00
-- url     : https://prove2.me/submissions/40ae0a52-5322-4a97-8e17-8ab8164ec332

import Definitions.Def_Formalism_SubspaceCounting_StatementD
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_AllButLESmith
import Theorems.Thm_Formalism_G0_AllButLESmithP_pow_succ_dvd_of_not_dvd
import Theorems.Thm_Formalism_G0_LengthLayersP_layer
import Theorems.Thm_Formalism_G0_LengthLayersP_length_residue


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open Formalism Formalism.G0
open Formalism.G0.AllButLESmithP
variable {O M ι : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [AddCommGroup M] [Module O M] [Fintype ι]
variable {P : Submodule O M} {n : ℕ}
namespace Formalism.G0.AllButLESmithP
theorem _root_.solution (snf : Basis.SmithNormalForm P ι n) (π : O) (hπ : Irreducible π) (g E : ℕ)
    (S : Finset ι) (hS : ∀ i, snf.f i ∈ S → ¬ snf.a i ∣ π ^ E)
    (h : AllButLE π ⊤ P g E) : S.card ≤ g := by
  classical
  obtain ⟨C, -, hCg, hC⟩ := h
  let K : Ideal O := Ideal.span {π ^ (E + 1)}
  let φ : M →ₗ[O] (↥S → O ⧸ K) :=
    LinearMap.pi (fun j : ↥S => K.mkQ ∘ₗ snf.bM.coord (j : ι))
  have hφb : ∀ i, φ (snf.bN i : M) = 0 := by
    intro i
    funext j
    simp only [φ, LinearMap.pi_apply, LinearMap.comp_apply, Basis.coord_apply, snf.snf i,
      map_smul, Basis.repr_self, Pi.zero_apply]
    rw [Finsupp.single_apply]
    split_ifs with hij
    · rw [← map_smul, smul_eq_mul, mul_one, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        Ideal.mem_span_singleton]
      have hmem : snf.f i ∈ S := by rw [hij]; exact j.2
      exact pow_succ_dvd_of_not_dvd hπ (hS i hmem)
    · simp
  have hφP : ∀ p ∈ P, φ p = 0 := by
    intro p hp
    have hsum := snf.bN.sum_repr ⟨p, hp⟩
    have hp' : p = ∑ i, snf.bN.repr ⟨p, hp⟩ i • (snf.bN i : M) := by
      have := congrArg Subtype.val hsum
      rw [Submodule.coe_sum] at this
      simpa using this.symm
    rw [hp', map_sum]
    simp only [map_smul, hφb, smul_zero, Finset.sum_const_zero]
  have hsurj : Function.Surjective φ := by
    intro t
    choose r hr using fun j => K.mkQ_surjective (t j)
    refine ⟨snf.bM.equivFun.symm (fun k => if hk : k ∈ S then r ⟨k, hk⟩ else 0), ?_⟩
    funext j
    have hrep : snf.bM.repr (snf.bM.equivFun.symm
        (fun k => if hk : k ∈ S then r ⟨k, hk⟩ else 0)) (j : ι) = r j := by
      rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
      simp
    simp only [φ, LinearMap.pi_apply, LinearMap.comp_apply, Basis.coord_apply, hrep, hr]
  have hmemC : ∀ x : M, π ^ E • φ x ∈ Submodule.span O ((C.image φ : Finset _) : Set _) := by
    intro x
    obtain ⟨p, hp, w, hw, hpw⟩ := Submodule.mem_sup.mp (hC x Submodule.mem_top)
    rw [← map_smul, ← hpw, map_add, hφP p hp, zero_add, Finset.coe_image, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem hw
  have hkill : ∀ w : ↥S → O ⧸ K, π ^ (E + 1) • w = 0 := by
    intro w
    funext j
    obtain ⟨r, hr⟩ := K.mkQ_surjective (w j)
    rw [Pi.smul_apply, Pi.zero_apply, ← hr, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      smul_eq_mul, Ideal.mem_span_singleton]
    exact dvd_mul_right _ _

  have hker : Ideal.span {π} ≤ LinearMap.ker ((π ^ E) • K.mkQ) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show (π ^ E) • K.mkQ π = 0
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
      ← pow_succ]
    exact Ideal.mem_span_singleton_self _
  let g0 : (O ⧸ Ideal.span {π}) →ₗ[O] (O ⧸ K) := (Ideal.span {π}).liftQ ((π ^ E) • K.mkQ) hker
  have hg0 : Function.Injective g0 := by
    rw [← LinearMap.ker_eq_bot]
    apply Submodule.ker_liftQ_eq_bot
    intro r hr
    rw [LinearMap.mem_ker, LinearMap.smul_apply, ← map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, smul_eq_mul, Ideal.mem_span_singleton, pow_succ] at hr
    rw [Ideal.mem_span_singleton]
    exact (mul_dvd_mul_iff_left (pow_ne_zero E hπ.ne_zero)).mp hr
  let ι' : (↥S → O ⧸ Ideal.span {π}) →ₗ[O] (↥S → O ⧸ K) :=
    LinearMap.pi (fun j : ↥S => g0 ∘ₗ LinearMap.proj j)
  have hinj : Function.Injective ι' := by
    intro u v huv
    funext j
    exact hg0 (congrFun huv j)
  have hV : LinearMap.range ι' ≤ Submodule.span O ((C.image φ : Finset _) : Set _) := by
    rintro _ ⟨u, rfl⟩
    choose r hr using fun j => (Ideal.span {π} : Submodule O O).mkQ_surjective (u j)
    obtain ⟨x, hx⟩ := hsurj (fun j => K.mkQ (r j))
    have : ι' u = π ^ E • φ x := by
      funext j
      rw [hx]
      simp only [ι', LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, ← hr,
        Pi.smul_apply, g0]
      rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.smul_apply]
    rw [this]
    exact hmemC x
  have hs : ∀ v ∈ LinearMap.range ι', π ^ 1 • v ∈ (⊥ : Submodule O (↥S → O ⧸ K)) := by
    rintro _ ⟨u, rfl⟩
    rw [Submodule.mem_bot]
    obtain ⟨r, hr⟩ : ∃ w, ι' u = π ^ E • w := by
      choose r hr using fun j => (Ideal.span {π} : Submodule O O).mkQ_surjective (u j)
      refine ⟨fun j => K.mkQ (r j), ?_⟩
      funext j
      simp only [ι', LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, ← hr,
        Pi.smul_apply, g0]
      rw [Submodule.mkQ_apply, Submodule.liftQ_apply, LinearMap.smul_apply]
    rw [hr, smul_smul, ← pow_add, add_comm]
    exact hkill r
  have hlay := LengthLayersP.layer π hπ (⊥ : Submodule O (↥S → O ⧸ K)) (LinearMap.range ι')
    bot_le (C.image φ) g 1 (Finset.card_image_le.trans hCg) hV hs
  rw [Module.length_bot, zero_add, ← (LinearEquiv.ofInjective ι' hinj).length_eq,
    Module.length_pi_of_fintype] at hlay
  simp only [LengthLayersP.length_residue π hπ, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, nsmul_eq_mul, mul_one] at hlay
  exact_mod_cast hlay
end Formalism.G0.AllButLESmithP
