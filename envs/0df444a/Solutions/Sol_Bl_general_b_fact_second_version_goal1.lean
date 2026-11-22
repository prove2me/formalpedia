-- Prove2me | solution 1 for Bl.general_b_fact_second_version.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:21:01.083677+00:00
-- url     : https://prove2.me/submissions/4ad3185c-6267-49ae-9e44-b90a192bba76

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactSecondVersion_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_second_version
namespace Bl.general_b_fact_second_version
theorem _root_.solution :
  ∀ {k A : Type} [inst : Field.{0} k] [inst_1 : Ring.{0} A] [inst_2 : Algebra.{0, 0} k A] {W S : Type}
  [inst_3 : AddCommGroup.{0} W] [inst_4 : Module.{0, 0} k W] [inst_5 : Module.{0, 0} A W]
  [IsScalarTower.{0, 0, 0} k A W] [inst_7 : AddCommGroup.{0} S] [inst_8 : Module.{0, 0} A S]
  [FiniteDimensional.{0, 0} k W] [IsSemisimpleModule.{0, 0} A W] [IsSimpleModule.{0, 0} A S],
  (∀ (a : A), (∀ (w : W), Eq.{1} (HSMul.hSMul.{0, 0, 0} a w) 0) → ∀ (s : S), Eq.{1} (HSMul.hSMul.{0, 0, 0} a s) 0) →
    Exists.{1} fun (f : LinearMap.{0, 0, 0, 0} (RingHom.id.{0} A) W S) ↦ Ne.{1} f 0 := by
  intro k A _ _ _ W S _ _ _ _ _ _ _ _ _ h
  classical
  have : Nontrivial S := IsSimpleModule.nontrivial A S
  obtain ⟨s, hs⟩ := exists_ne (0 : S)
  let b := Module.finBasis k W
  let φ : A →ₗ[A] (Fin (Module.finrank k W) → W) :=
    LinearMap.pi (fun i => LinearMap.toSpanSingleton A W (b i))
  let σ : A →ₗ[A] S := LinearMap.toSpanSingleton A S s
  have hker : LinearMap.ker φ ≤ LinearMap.ker σ := by
    intro a ha
    simp only [LinearMap.mem_ker] at ha ⊢
    have hb : ∀ i, a • b i = 0 := fun i => by
      simpa [φ] using congr_fun ha i
    have hw : ∀ w : W, a • w = 0 := by
      intro w
      have e : (DistribSMul.toLinearMap k W a) = 0 :=
        b.ext (fun i => hb i)
      exact LinearMap.congr_fun e w
    simpa [σ] using h a hw s
  let ψ₀ : LinearMap.range φ →ₗ[A] S :=
    (LinearMap.ker φ).liftQ σ hker ∘ₗ φ.quotKerEquivRange.symm.toLinearMap
  have hsm : IsSemisimpleModule A (Fin (Module.finrank k W) → W) := inferInstance
  obtain ⟨C, hC⟩ := ComplementedLattice.exists_isCompl (LinearMap.range φ)
  let Ψ : (Fin (Module.finrank k W) → W) →ₗ[A] S :=
    ψ₀ ∘ₗ Submodule.linearProjOfIsCompl _ _ hC
  have hΨ : Ψ (φ 1) = s := by
    have h1 : Submodule.linearProjOfIsCompl _ _ hC (φ 1) = ⟨φ 1, LinearMap.mem_range_self φ 1⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨φ 1, LinearMap.mem_range_self φ 1⟩
    simp only [Ψ, ψ₀, LinearMap.comp_apply, h1, LinearEquiv.coe_toLinearMap,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
    simp [σ]
  by_contra hne
  push_neg at hne
  have hz : Ψ = 0 := by
    apply LinearMap.pi_ext'
    intro i
    exact hne _
  rw [hz] at hΨ
  exact hs hΨ.symm
end Bl.general_b_fact_second_version
