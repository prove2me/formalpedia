-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.dual_capacity_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:58:15.18062+00:00
-- url     : https://prove2.me/submissions/aeafcab1-2a81-4b6b-a404-2df642919055

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_unram_uniq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_unram_trace
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : DualCap := by
  intro o O abelian₂ _ _ _ _ _ _ _ _ _ _ h hU hSD S hS φ
  classical
  obtain ⟨T, hT⟩ := unram_trace hU
  have hUq := unram_uniq hU
  have := hU.free
  have : Module.Finite o O := Module.finite_of_finrank_pos (by rw [hU.rank2]; norm_num)
  let : Module o abelian₂ := Module.compHom abelian₂ (algebraMap o O)
  have : IsScalarTower o O abelian₂ := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Finite o abelian₂ := Module.Finite.trans O abelian₂
  let S' : Submodule o abelian₂ := S.restrictScalars o
  have : Module.IsTorsionFree o (abelian₂ ⧸ S') := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro r m hrm
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      obtain ⟨v, rfl⟩ := S'.mkQ_surjective m
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hrm
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hS r v hr hrm
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property S'.mkQ LinearMap.id S'.mkQ_surjective
  let ρ : abelian₂ →ₗ[o] abelian₂ := LinearMap.id - σ ∘ₗ S'.mkQ
  have hρmem : ∀ v, ρ v ∈ S := by
    intro v
    have : S'.mkQ (ρ v) = 0 := by
      have h1 := LinearMap.congr_fun hσ (S'.mkQ v)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
      simp only [ρ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h1, sub_self]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    exact this
  have hρfix : ∀ v ∈ S, ρ v = v := by
    intro v hv
    have : S'.mkQ v = 0 := by rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hv
    simp only [ρ, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, this, map_zero, sub_zero]
  let Λ : abelian₂ →ₗ[o] o :=
    { toFun := fun v => T (φ ⟨ρ v, hρmem v⟩)
      map_add' := fun v w => by
        have : (⟨ρ (v + w), hρmem (v + w)⟩ : S) = ⟨ρ v, hρmem v⟩ + ⟨ρ w, hρmem w⟩ :=
          Subtype.ext (map_add ρ v w)
        rw [this, map_add, map_add]
      map_smul' := fun c v => by
        have : (⟨ρ (c • v), hρmem (c • v)⟩ : S) = algebraMap o O c • ⟨ρ v, hρmem v⟩ :=
          Subtype.ext (map_smul ρ c v)
        rw [this, map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul, RingHom.id_apply] }
  have hΛ : ∀ v, Λ v = T (φ ⟨ρ v, hρmem v⟩) := fun v => rfl
  have hex : ∀ v : abelian₂, ∃ c : O, ∀ a : O, algebraMap o O (Λ (a • v)) = a * c + star (a * c) := by
    intro v
    obtain ⟨bv, hbv⟩ := hU.tr_perfect (Λ ∘ₗ (LinearMap.toSpanSingleton O abelian₂ v).restrictScalars o)
    exact ⟨star bv, fun a => hbv a⟩
  choose Φ hΦ using hex
  let Φl : abelian₂ →ₗ[O] O :=
    { toFun := Φ
      map_add' := fun v w => by
        rw [← sub_eq_zero]
        apply hUq
        intro a
        have h1 := hΦ (v + w) a
        rw [smul_add, map_add, map_add, hΦ v a, hΦ w a] at h1
        simp only [mul_sub, mul_add, star_sub, star_add]
        linear_combination -h1
      map_smul' := fun r v => by
        rw [← sub_eq_zero]
        apply hUq
        intro a
        have h1 := hΦ (r • v) a
        rw [smul_smul, hΦ v (a * r)] at h1
        simp only [RingHom.id_apply, smul_eq_mul, mul_sub, star_sub, ← mul_assoc]
        linear_combination -h1 }
  obtain ⟨w, hw⟩ := hSD.2 Φl
  refine ⟨w, fun v => ?_⟩
  rw [← hw]
  change φ v = Φ v
  symm
  rw [← sub_eq_zero]
  apply hUq
  intro a
  have h1 := hΦ v a
  have h2 : (⟨ρ (a • (v : abelian₂)), hρmem _⟩ : S) = a • v := Subtype.ext (hρfix _ (S.smul_mem a v.2))
  rw [hΛ, h2, map_smul, smul_eq_mul, hT] at h1
  simp only [mul_sub, star_sub]
  linear_combination -h1
end Formalism.HermitianLatticeCounting.P.S4aux
