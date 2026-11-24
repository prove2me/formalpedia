-- Prove2me | solution 1 for Formalism.HermitianLattices.RamifiedHeckeModels.lemma_c_twist_ramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:27:28.411477+00:00
-- url     : https://prove2.me/submissions/1fbafad4-9926-48c5-9aa0-39f2f00af6ae

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RationalMatrixPrimeOrderBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LengthQuotientBoundGeneral
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LemmaCTwistRamified
import Theorems.Thm_Formalism_HermitianLattices_RamifiedHeckeModels_lemma_c_under_twist


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.RamifiedHeckeModels
namespace Formalism.HermitianLattices.RamifiedHeckeModels
theorem _root_.solution : LemmaC_twist_ram := by
  unfold LemmaC_twist_ram
  intro R _ _ _ ϖ hϖ M _ _ P S B U D e b hSB hBU hSD hPU hPD hsat hUD hfree hfin
  have hpow : ∀ n : ℕ, ∀ x : M, ϖ ^ n • x ∈ P → x ∈ P := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      apply hsat
      apply ih
      rwa [← mul_smul, ← pow_succ]
  have h1 : (S ⊓ P).map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M)) ≤ B ⊓ P := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨hSB ⟨s, hs.1, rfl⟩, by simpa using P.smul_mem (ϖ ^ b) hs.2⟩
  have h2 : (B ⊓ P).map U ≤ S ⊓ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hBU ⟨x, hx.1, rfl⟩, hPU ⟨x, hx.2, rfl⟩⟩
  have h3 : (S ⊓ P).map D ≤ B ⊓ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨hSD ⟨x, hx.1, rfl⟩, hPD ⟨x, hx.2, rfl⟩⟩
  let ι : (S ⊓ P : Submodule R M) →ₗ[R] S := Submodule.inclusion inf_le_left
  have hι : Function.Injective ι := Submodule.inclusion_injective _
  obtain ⟨n, bN⟩ := Submodule.basisOfPid (Module.Free.chooseBasis R S)
    ((S ⊓ P).comap S.subtype)
  let eN : ((S ⊓ P).comap S.subtype) ≃ₗ[R] (S ⊓ P : Submodule R M) :=
    Submodule.comapSubtypeEquivOfLe inf_le_left
  haveI : Module.Free R (S ⊓ P : Submodule R M) := Module.Free.of_basis (bN.map eN)
  haveI : Module.Finite R (S ⊓ P : Submodule R M) := Module.Finite.of_basis (bN.map eN)
  have key := lemma_c_under_twist
  unfold LemmaC_twist at key
  have key' := key R ϖ hϖ M (S ⊓ P) (B ⊓ P) U D e b h1 h2 h3 hUD inferInstance inferInstance
  have hrank : Module.finrank R (S ⊓ P : Submodule R M) ≤ Module.finrank R S :=
    LinearMap.finrank_le_finrank_of_injective hι
  have hlen : Module.length R ((B ⊓ P : Submodule R M) ⧸
      ((S ⊓ P).map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap (B ⊓ P).subtype) ≤
      Module.length R (B ⧸ (S.map ((ϖ ^ b) • (LinearMap.id : M →ₗ[R] M))).comap B.subtype) := by
    refine Module.length_le_of_injective
      (Submodule.mapQ _ _ (Submodule.inclusion (inf_le_left : B ⊓ P ≤ B)) ?_) ?_
    · intro x hx
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx ⊢
      exact Submodule.map_mono inf_le_left hx
    · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro q hq
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [LinearMap.mem_ker, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hq
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hq ⊢
      obtain ⟨s, hs, hsx⟩ := hq
      refine ⟨s, ⟨hs, ?_⟩, hsx⟩
      apply hpow b
      have hx' : (ϖ ^ b • s : M) = x := by simpa using hsx
      rw [hx']
      exact x.2.2
  refine key'.trans (add_le_add hlen ?_)
  exact_mod_cast Nat.mul_le_mul_left e hrank
end Formalism.HermitianLattices.RamifiedHeckeModels
