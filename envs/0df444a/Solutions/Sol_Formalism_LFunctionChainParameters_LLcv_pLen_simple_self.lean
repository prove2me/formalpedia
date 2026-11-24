-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.pLen_simple_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:29:32.828577+00:00
-- url     : https://prove2.me/submissions/981ee571-f2a0-4a7c-b510-54742adc2950

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_kill_of_equiv
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_le_locS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LLcv
open Formalism.HN Formalism.HermitianLatticesTheory Formalism.LFunctionChainParameters.slopeLatticeData
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]
namespace Formalism.LFunctionChainParameters.LLcv
theorem _root_.solution (m : Ideal R) [hm : m.IsMaximal] {A C : Submodule R W}
    (e : (A ⧸ C.comap A.subtype) ≃ₗ[R] (R ⧸ m)) : pLen m A C = 1 := by
  have hkill := kill_of_equiv m e
  have hinv : ∀ s ∉ m, ∃ t, t * s - 1 ∈ m := by
    intro s hs
    obtain ⟨t, ht⟩ := Ideal.Quotient.exists_inv (I := m)
      (a := Ideal.Quotient.mk m s) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
    refine ⟨t, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, mul_comm, ht, sub_self]
  have hAP : A ≤ localization₂ m A := locBasic_le_locS _ A
  let ψ : A →ₗ[R] (localization₂ m A) ⧸ (localization₂ m C).comap (localization₂ m A).subtype :=
    ((localization₂ m C).comap (localization₂ m A).subtype).mkQ ∘ₗ Submodule.inclusion hAP
  have hsurj : Function.Surjective ψ := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨s, hs, hsx⟩ := x.2
      obtain ⟨t, ht⟩ := hinv s hs
      refine ⟨⟨t • s • (x : W), A.smul_mem t hsx⟩, ?_⟩
      show Submodule.mkQ _ _ = Submodule.Quotient.mk x
      rw [Submodule.mkQ_apply, Submodule.Quotient.eq]
      show (t • s • (x : W) - x) ∈ localization₂ m C
      refine ⟨s, hs, ?_⟩
      have e1 : s • (t • s • (x : W) - x) = (t * s - 1) • (s • (x : W)) := by module
      rw [e1]
      exact hkill _ ht _ hsx
  have hker : LinearMap.ker ψ = C.comap A.subtype := by
    ext x
    rw [LinearMap.mem_ker]
    show Submodule.mkQ _ _ = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    show (x : W) ∈ localization₂ m C ↔ (x : W) ∈ C
    constructor
    · rintro ⟨s, hs, hsx⟩
      obtain ⟨t, ht⟩ := hinv s hs
      have e1 : (x : W) = t • (s • (x : W)) - (t * s - 1) • (x : W) := by module
      rw [e1]
      exact C.sub_mem (C.smul_mem t hsx) (hkill _ ht _ x.2)
    · intro hx
      exact locBasic_le_locS _ C hx
  have e2 : (A ⧸ C.comap A.subtype) ≃ₗ[R] (localization₂ m A) ⧸ (localization₂ m C).comap (localization₂ m A).subtype :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (ψ.quotKerEquivOfSurjective hsurj)
  have hs : IsSimpleModule R (R ⧸ m) := isSimpleModule_iff_isCoatom.2 hm.out
  unfold pLen
  rw [(e2.symm.trans e).length_eq]
  exact Module.length_eq_one_iff.2 hs
end Formalism.LFunctionChainParameters.LLcv
