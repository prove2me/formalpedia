-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.relIndex_hermitian_dual_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:27.671594+00:00
-- url     : https://prove2.me/submissions/b9cd08cc-1732-473c-8e1b-7edb97139cac

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_relIndex_ideal_smul
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_zdual_relIndex
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_exists_codiff
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_exists_smul_mem_of_span
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_exists_int_smul_mem
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_exists_smul_le
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_trForm_nondeg
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_dual_key
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_DualLatticeIndexBis_fg_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open NumberField
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
variable {E U : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup U] [Module E U]
  [Module (𝓞 E) U] [IsScalarTower (𝓞 E) E U] [Module ℚ U] [IsScalarTower ℚ E U]
namespace Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
theorem _root_.solution [FiniteDimensional ℚ U] (h : U →ₗ[E] U →ₗ⋆[E] E) (M N : Submodule (𝓞 E) U)
    (hnd : ∀ x : U, (∀ y : U, h x y = 0) → x = 0) (hNM : N ≤ M) (hM : M.FG)
    (hN : Submodule.span E (N : Set U) = ⊤) :
    (hdual h (algebraMap (𝓞 E) E).range M.toAddSubgroup).relIndex
          (hdual h (algebraMap (𝓞 E) E).range N.toAddSubgroup) =
        N.toAddSubgroup.relIndex M.toAddSubgroup := by
  obtain ⟨δ, K, hδ, hK, hcod⟩ := exists_codiff E
  have hδE : (δ : E) ≠ 0 := by
    intro h0
    exact hδ (RingOfIntegers.ext (by simpa using h0))
  have hsm : ∀ (a : 𝓞 E) (x : U), a • x = (a : E) • x := fun a x => (algebraMap_smul E a x).symm
  have htf : ∀ a : 𝓞 E, a ≠ 0 → ∀ x : U, a • x = 0 → x = 0 := by
    intro a ha x hx
    rw [hsm] at hx
    rcases smul_eq_zero.mp hx with h0 | h0
    · exact absurd (RingOfIntegers.ext (by simpa using h0)) ha
    · exact h0
  obtain ⟨d, hd, hdM⟩ := exists_smul_le N M hN hM
  obtain ⟨k, hkK, hk0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
  let mδ : U →+ U := (LinearMap.lsmul E U (δ : E)).toAddMonoidHom
  have hmδ : Function.Surjective mδ := by
    intro x
    refine ⟨(δ : E)⁻¹ • x, ?_⟩
    change (δ : E) • ((δ : E)⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hδE, one_smul]
  have hfgZ : ((K • M).restrictScalars ℤ).FG :=
    fg_int _ (Submodule.FG.of_le hM Submodule.smul_le_right)
  have hle : (K • N).restrictScalars ℤ ≤ (K • M).restrictScalars ℤ := by
    intro x hx
    exact Submodule.smul_mono (le_refl K) hNM hx
  have hfull : ∀ x : U, ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ (K • N).restrictScalars ℤ := by
    intro x
    obtain ⟨e, he, hex⟩ := exists_smul_mem_of_span N hN x
    refine exists_int_smul_mem (K • N) x (k * e) (mul_ne_zero hk0 he) ?_
    rw [mul_smul]
    exact Submodule.smul_mem_smul hkK hex
  have hZ := zdual_relIndex (trForm h) (trForm_nondeg h hnd) ((K • N).restrictScalars ℤ)
    ((K • M).restrictScalars ℤ) hle hfgZ hfull
    ((hdual h (algebraMap (𝓞 E) E).range N.toAddSubgroup).comap mδ)
    ((hdual h (algebraMap (𝓞 E) E).range M.toAddSubgroup).comap mδ)
    (fun x => dual_key h δ K hcod N x) (fun x => dual_key h δ K hcod M x)
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective hmδ] at hZ
  rw [hZ]
  refine relIndex_ideal_smul htf M N hNM (Ideal.span {d}) K ?_ hK ?_
  · rw [Ne, Ideal.span_singleton_eq_bot]; exact hd
  · rw [Submodule.smul_le]
    intro r hr x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    rw [mul_smul]
    exact N.smul_mem c (hdM x hx)
end Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
