-- Prove2me | solution 1 for CompanionTheory.L3H.key_M0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:59:28.623702+00:00
-- url     : https://prove2.me/submissions/9214d59e-5e3c-4226-b3de-0deee6491499

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_IntegralOfModule
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_InvMemRl
import Theorems.Thm_CompanionTheory_L3H_inv_mem_Rl
import Theorems.Thm_CompanionTheory_Split_ALint_eq
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_UG_P_csGlob_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.UG Formalism.L2 CompanionTheory.Split CompanionTheory.HeckeA
noncomputable section
open CompanionTheory CompanionTheory.L3H
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
local notation3 "L⁺" => maximalRealSubfield L
variable {ρ : Representation ℂ (GQ L n) W} {J : Subgroup (Formalism.AUTREP.GAf L n)} {χ : J →* ℂˣ}
  {B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {s : SplitPlace L}
namespace CompanionTheory.L3H
theorem _root_.solution {l : ℕ} [Fact l.Prime] {c : ℕ} (hc : c ≠ 0) (x : L)
    (hx : ∃ m : ℕ, ¬ l ∣ m ∧ ((m * c ^ 2 : ℕ) : AL L) * (x ⊗ₜ[maximalRealSubfield L] (1 : AFplus L)) ∈ ALint L)
    (τ : L →+* ℂ) : τ x ∈ M0 L l c := by
  obtain ⟨m, hm, h⟩ := hx
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 fun e => hm (e ▸ dvd_zero l)
  have hc' : (c : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hc
  have hint : IsIntegral ℤ (((m * c ^ 2 : ℕ) : L) * x) := by
    refine Formalism.UG.P.csGlob_int (F := maximalRealSubfield L) (E := L) _ ?_
    rw [← ALint_eq]
    convert h using 1
    show (((m * c ^ 2 : ℕ) : L) * x) ⊗ₜ[maximalRealSubfield L] (1 : AFplus L) = _
    rw [← one_mul (1 : AFplus L), ← Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
  set y : 𝓞 L := ⟨_, hint⟩
  have hy := (RingOfIntegers.basis L).sum_repr y
  have hτ : τ (((m * c ^ 2 : ℕ) : L) * x) =
      ∑ r, ((RingOfIntegers.basis L).repr y r : ℂ) * τ (RingOfIntegers.basis L r : L) := by
    have := congrArg (τ.comp (algebraMap (𝓞 L) L)) hy
    rw [show τ (((m * c ^ 2 : ℕ) : L) * x) = (τ.comp (algebraMap (𝓞 L) L)) y from rfl, ← this, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, zsmul_eq_mul]
    rfl
  obtain ⟨r, hr⟩ := inv_mem_Rl hm
  have hx' : τ x = algebraMap (Rl l) ℂ r *
      ∑ i, ((RingOfIntegers.basis L).repr y i : ℂ) * (τ (RingOfIntegers.basis L i : L) / (c : ℂ) ^ 2) := by
    have e : ∑ i, ((RingOfIntegers.basis L).repr y i : ℂ) * (τ (RingOfIntegers.basis L i : L) / (c : ℂ) ^ 2) =
        (∑ i, ((RingOfIntegers.basis L).repr y i : ℂ) * τ (RingOfIntegers.basis L i : L)) / (c : ℂ) ^ 2 := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [hr, e, ← hτ, map_mul, map_natCast]
    push_cast
    field_simp
  rw [hx', ← Algebra.smul_def]
  refine Submodule.smul_mem _ r (Submodule.sum_mem _ fun i _ => ?_)
  rw [← zsmul_eq_mul]
  exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨(τ, i), rfl⟩)
end CompanionTheory.L3H
