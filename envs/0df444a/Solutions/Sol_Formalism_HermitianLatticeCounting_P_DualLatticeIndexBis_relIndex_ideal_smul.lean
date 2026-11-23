-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis.relIndex_ideal_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:10.316891+00:00
-- url     : https://prove2.me/submissions/19d96adc-8431-4bdd-a37b-d726860a7954

import Definitions.Def_Formalism_FlagUnipotentLattices_IdealCountLeW
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Lemmata_GeneralBFactSecondMore_Imports
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ColonCountWeighted

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
namespace Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
theorem _root_.solution {R U : Type*} [CommRing R] [IsDedekindDomain R] [AddCommGroup U] [Module R U]
    (htf : ∀ a : R, a ≠ 0 → ∀ x : U, a • x = 0 → x = 0) (M N : Submodule R U) (hNM : N ≤ M)
    (A J : Ideal R) (hA : A ≠ ⊥) (hJ : J ≠ ⊥) (hAM : A • M ≤ N) :
    (J • N).toAddSubgroup.relIndex (J • M).toAddSubgroup =
      N.toAddSubgroup.relIndex M.toAddSubgroup := by
  by_cases hMN : M ≤ N
  · have : N = M := le_antisymm hNM hMN
    rw [this, AddSubgroup.relIndex_self, AddSubgroup.relIndex_self]
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (I := A * J) (J := J) Ideal.mul_le_right
    (mul_ne_zero hA hJ)
  have haJ : Ideal.span {a} ≤ J := ha ▸ le_sup_right
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hMN
    have h1 : A * J = 1 * J := by
      rw [one_mul]
      simpa using ha
    have h2 : A = 1 := mul_right_cancel₀ hJ h1
    rw [h2, Ideal.one_eq_top, Submodule.top_smul] at hAM
    exact hAM
  obtain ⟨J', hJ'⟩ := Ideal.dvd_iff_le.mpr haJ
  have hcop : A ⊔ J' = ⊤ := by
    have h1 : J * (A ⊔ J') = J * 1 := by
      rw [Ideal.mul_sup, ← hJ', mul_comm J A, ha, mul_one]
    rw [← Ideal.one_eq_top]
    exact mul_left_cancel₀ hJ h1
  let φ : U →ₗ[R] U := LinearMap.lsmul R U a
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 : a • (x - y) = 0 := by
      rw [smul_sub]; exact sub_eq_zero.mpr hxy
    exact sub_eq_zero.mp (htf a ha0 _ h1)
  have hmap : ∀ L : Submodule R U, L.map φ = Ideal.span {a} • L := by
    intro L
    rw [Submodule.ideal_span_singleton_smul]
    ext x
    simp [φ, Submodule.mem_smul_pointwise_iff_exists]
  have h1 : J • M = M.map φ ⊔ J • N := by
    apply le_antisymm
    · conv_lhs => rw [← ha]
      rw [Submodule.sup_smul, hmap M]
      refine sup_le ?_ le_sup_left
      rw [mul_comm, Submodule.mul_smul]
      exact (Submodule.smul_mono le_rfl hAM).trans le_sup_right
    · rw [hmap M]
      exact sup_le (Submodule.smul_mono_left haJ) (Submodule.smul_mono le_rfl hNM)
  have h2 : J • N ⊓ M.map φ = N.map φ := by
    apply le_antisymm
    · rintro x ⟨hx1, y, hy, rfl⟩
      refine ⟨y, ?_, rfl⟩
      have h1 : (1 : R) ∈ A ⊔ J' := by rw [hcop]; trivial
      obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp h1
      have hsy : s • y ∈ N := hAM (Submodule.smul_mem_smul hs hy)
      have hty : t • y ∈ N := by
        have h3 : t • φ y ∈ J' • (J • N) := Submodule.smul_mem_smul ht hx1
        rw [← Submodule.mul_smul, mul_comm J' J, ← hJ', ← hmap N] at h3
        obtain ⟨n, hn, hn'⟩ := h3
        have h4 : φ n = φ (t • y) := by rw [hn', map_smul]
        rw [← hφ h4]
        exact hn
      have : y = s • y + t • y := by rw [← add_smul, hst, one_smul]
      rw [this]
      exact N.add_mem hsy hty
    · refine le_inf ?_ (Submodule.map_mono hNM)
      rw [hmap N]
      exact Submodule.smul_mono_left haJ
  have h2' : (J • N).toAddSubgroup ⊓ (M.map φ).toAddSubgroup = (N.map φ).toAddSubgroup := by
    rw [← h2]; rfl
  rw [h1, Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right,
    h2', Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ hφ
end Formalism.HermitianLatticeCounting.P.DualLatticeIndexBis
