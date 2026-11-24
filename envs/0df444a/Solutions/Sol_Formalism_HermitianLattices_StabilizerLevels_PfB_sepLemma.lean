-- Prove2me | solution 1 for Formalism.HermitianLattices.StabilizerLevels.PfB.sepLemma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:16:07.502701+00:00
-- url     : https://prove2.me/submissions/232fcff7-025e-409c-9708-b4dc61b483c4

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.StabilizerLevels
open Formalism.HermitianLattices.StabilizerLevels.PfB
open NumberField IsDedekindDomain
open scoped TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable (w : HeightOneSpectrum (𝓞 F))
local notation "O" => (HeightOneSpectrum.adicCompletionIntegers F w)
namespace Formalism.HermitianLattices.StabilizerLevels.PfB
theorem _root_.solution (g : ℕ) (hgw : (g : 𝓞 F) ∈ w.asIdeal) :
    ∃ (A : Subring (E ⊗[F] w.adicCompletion F)),
      Formalism.UG.tensInt (F := F) (w.adicCompletion F) (Formalism.UG.intOE E)
        (w.adicCompletionIntegers F).toSubring ≤ A ∧
      (⨅ m : ℕ, (Ideal.span {(g : A)}) ^ m) = ⊥ := by
  classical
  let _ : Algebra (w.adicCompletionIntegers F) (E ⊗[F] w.adicCompletion F) := (owHom (E := E) w).toAlgebra
  let ι : 𝓞 E →+* E ⊗[F] w.adicCompletion F := (Formalism.UG.inclE (F := F) (E := E) (w.adicCompletion F)).comp (algebraMap (𝓞 E) E)
  let bs := NumberField.RingOfIntegers.basis E
  let s : Set (E ⊗[F] w.adicCompletion F) := Set.range (fun i => ι (bs i))
  have hsfin : s.Finite := Set.finite_range _
  have hint : ∀ x ∈ s, IsIntegral O x := by
    rintro _ ⟨i, rfl⟩
    have h1 : IsIntegral ℤ (bs i) := Algebra.IsIntegral.isIntegral _
    exact h1.map_of_comp_eq (Int.castRingHom O) ι (RingHom.ext_int _ _)
  have hfg := fg_adjoin_of_finite hsfin hint
  let A := Algebra.adjoin O s
  have : Module.Finite O A := Module.Finite.iff_fg.2 hfg
  have hιA : ∀ x : 𝓞 E, ι x ∈ A := by
    intro x
    rw [← bs.sum_repr x, map_sum]
    refine Subalgebra.sum_mem _ fun i _ => ?_
    rw [zsmul_eq_mul, map_mul, map_intCast]
    exact A.mul_mem (intCast_mem A _) (Algebra.subset_adjoin ⟨i, rfl⟩)
  refine ⟨A.toSubring, ?_, ?_⟩
  · unfold Formalism.UG.tensInt
    rw [Subring.closure_le]
    rintro _ (⟨⟨_, ⟨x, rfl⟩⟩, rfl⟩ | ⟨y, rfl⟩)
    · exact hιA x
    · exact A.algebraMap_mem (⟨y.1, y.2⟩ : O)
  · have hg : (g : O) ∈ IsLocalRing.maximalIdeal O := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨u, hu⟩ := hu.exists_right_inv
      have h1 : Valued.v ((g : w.adicCompletion F)) * Valued.v (u : w.adicCompletion F) = 1 := by
        rw [← map_mul]
        have := congrArg (fun z : O => (z : w.adicCompletion F)) hu
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
        have e : (((g : O)) : w.adicCompletion F) = (g : w.adicCompletion F) := by simp
        rw [e] at this
        rw [this, map_one]
      have h2 : Valued.v ((g : w.adicCompletion F)) < 1 := by
        have e : (g : w.adicCompletion F) = ((algebraMap (𝓞 F) F (g : 𝓞 F) : F) : w.adicCompletion F) := by
          rw [map_natCast]
          exact (map_natCast (algebraMap F (w.adicCompletion F)) g).symm
        rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_lt_one_iff_mem]
        exact hgw
      have h3 : Valued.v (u : w.adicCompletion F) ≤ 1 :=
        (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 u.2
      have h4 : Valued.v ((g : w.adicCompletion F)) * Valued.v (u : w.adicCompletion F) < 1 :=
        lt_of_le_of_lt (mul_le_of_le_one_right' h3) h2
      rw [h1] at h4
      exact lt_irrefl _ h4
    have hne : Ideal.span {(g : O)} ≠ ⊤ := by
      intro h
      have : Ideal.span {(g : O)} ≤ IsLocalRing.maximalIdeal O := by
        rw [Ideal.span_le, Set.singleton_subset_iff]; exact hg
      rw [h] at this
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top (top_le_iff.1 this)
    have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := A) (Ideal.span {(g : O)}) hne
    rw [eq_bot_iff]
    intro x hx
    rw [Ideal.mem_iInf] at hx
    have : (⟨x.1, x.2⟩ : A) ∈ (⨅ i : ℕ, (Ideal.span {(g : O)}) ^ i • (⊤ : Submodule O A)) := by
      rw [Submodule.mem_iInf]
      intro m
      have h1 := hx m
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h1
      obtain ⟨a, ha⟩ := h1
      have : (⟨x.1, x.2⟩ : A) = ((g : O) ^ m) • (⟨a.1, a.2⟩ : A) := by
        apply Subtype.ext
        have e := congrArg Subtype.val ha
        show x.1 = ((g : O) ^ m) • a.1
        rw [Algebra.smul_def]
        show x.1 = owHom (E := E) w ((g : O) ^ m) * a.1
        rw [map_pow, map_natCast, ← e]
        push_cast
        ring
      rw [this]
      exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) m) trivial
    rw [hK] at this
    simpa using this
end Formalism.HermitianLattices.StabilizerLevels.PfB
